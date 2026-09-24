#!/usr/bin/env python3
"""
build_core_information_model.py

Creates:
- core_information_model.xml
- nodeset.access.xml (source nodeset minus core nodes)

Also outputs metrics for both resultant files:
- number of primary nodes
- total lines of resultant XML

Preserves full front matter and back matter verbatim.
Writes included node blocks verbatim (no ns0 prefix reserialization).
"""

import sys
import csv
import re
from pathlib import Path
from collections import defaultdict, Counter, deque
import xml.etree.ElementTree as ET

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
SCRIPT_DIR = Path(__file__).resolve().parent
NODESET_FILE = SCRIPT_DIR / "opc.ua.nodeset2.xml"
CORE_OUTPUT_FILE = SCRIPT_DIR / "core_information_model.xml"
ACCESS_OUTPUT_FILE = SCRIPT_DIR / "nodeset.access.xml"
AUDIT_REPORT_FILE = SCRIPT_DIR / "core_model_audit_report.txt"
DANGLING_REFS_CSV_FILE = SCRIPT_DIR / "pruned_dangling_references.csv"
PRIMARY_TYPE_METRICS_CSV_FILE = SCRIPT_DIR / "primary_type_metrics.csv"
PROVENANCE_CSV_FILE = SCRIPT_DIR / "node_inclusion_provenance.csv"
NODESET_METRICS_CSV_FILE = SCRIPT_DIR / "nodeset_metrics.csv"

NODE_TAGS = {
    "UAObject", "UAObjectType", "UAVariable", "UAVariableType",
    "UAMethod", "UAReferenceType", "UADataType", "UAView",
}
TYPE_CLASSES = {"UAObjectType", "UAVariableType", "UAReferenceType", "UADataType"}
MEMBER_CLASSES = {"UAObject", "UAVariable", "UAMethod"}
COMPOSITION_REF_TYPES = {"HasProperty", "HasComponent", "HasOrderedComponent"}

WELL_KNOWN = {"i=78", "i=80", "i=11508", "i=11509", "i=11510", "i=11511"}

EXCLUDE_ROOTS = {"i=23724", "i=19723", "i=19730"}

EXCLUDE_CATEGORY_KEYWORDS = {
    "Base Info Model Change",
    "Base Info SemanticChange",
    "Base Info EventQueueOverflow",
    "Base Info UaBinary File",
    "Base Info Portable IDs",
    "Base Info ContentFilter",
    "Base Info Deprecated Information",
    "Base Info Progress Events",
    "Base Info System Status",
    "Base Info StatusResult",
    "Base Info ServerType",
    "Base Configuration Management",
    "Server Diagnostics",
    "Session Diagnostics",
    "Subscription Diagnostics",
    "Monitored Item",
    "Discovery",
    "Redundancy",
    "Aggregate Function",
    "Push Model for Global Certificate and TrustList Management",
    "KeyCredential Service",
    "Authorization Service Configuration",
    "PushManagement Transactions",
    "Application Configuration Management",
    "Managed Application Configuration",
    "Onboarding",
    "ObjectSerialization",
    "Security User Management Server",
    "Server Endpoint Management",
    "Auditing",
    "Audit Events",
    "Program Auditing",
    "Security Role Server Base Eventing",
    "Security Role Server Base",
    "CertificateExpiration",
    "Certificate Manager Pull Model",
    "AliasName",
    "Historical Access",
    "A & C",
    "PubSub",
    "BNM",
}

# ---------------------------------------------------------------------------
# Regex for verbatim extraction
# ---------------------------------------------------------------------------
NODE_START_RE = re.compile(r'<(?:\w+:)?(UAObject|UAObjectType|UAVariable|UAVariableType|UAMethod|UAReferenceType|UADataType|UAView)\b')
NODEID_ATTR_RE = re.compile(r'NodeId\s*=\s*"([^"]+)"')
REF_LINE_RE = re.compile(r'^(\s*)<(?:\w+:)?Reference\b([^>]*)>([^<]*)</(?:\w+:)?Reference>\s*$')
REFTYPE_ATTR_RE = re.compile(r'ReferenceType\s*=\s*"([^"]+)"')

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def strip_ns(tag):
    return tag.split("}", 1)[1] if "}" in tag else tag

def local_children(elem, name):
    return [c for c in elem if strip_ns(c.tag) == name]

def element_xml_line_count(elem):
    xml = ET.tostring(elem, encoding="unicode")
    return len(xml.splitlines()) if xml else 0

def reason_for_ref_type(rtype):
    return "composible" if rtype in COMPOSITION_REF_TYPES else "non"

def join_categories(info):
    return " | ".join(info.get("categories") or [])

def file_line_count(path: Path) -> int:
    with open(path, "r", encoding="utf-8") as f:
        return sum(1 for _ in f)

# ---------------------------------------------------------------------------
# Parse/index (structured, for graph logic)
# ---------------------------------------------------------------------------
def build_index_and_tree(nodeset_file):
    tree = ET.parse(str(nodeset_file))
    root = tree.getroot()

    nodes = {}
    supertype_of = {}
    node_elements = {}

    for elem in root:
        tag = strip_ns(elem.tag)
        if tag not in NODE_TAGS:
            continue

        node_id = elem.get("NodeId")
        if not node_id:
            continue

        references = []
        categories = []
        field_datatypes = []
        typedef = None

        for refs_container in local_children(elem, "References"):
            for ref in local_children(refs_container, "Reference"):
                rtype = ref.get("ReferenceType")
                is_fwd = ref.get("IsForward", "true") != "false"
                target = (ref.text or "").strip()
                references.append((rtype, target, is_fwd))

                if rtype == "HasTypeDefinition" and is_fwd:
                    typedef = target
                if rtype == "HasSubtype" and not is_fwd:
                    supertype_of[node_id] = target

        for cat_elem in local_children(elem, "Category"):
            if cat_elem.text:
                categories.append(cat_elem.text.strip())

        for defn in local_children(elem, "Definition"):
            for field in local_children(defn, "Field"):
                dt = field.get("DataType")
                if dt:
                    field_datatypes.append(dt)

        nodes[node_id] = {
            "nodeclass": tag,
            "browsename": elem.get("BrowseName", ""),
            "categories": categories,
            "references": references,
            "typedef": typedef,
            "field_datatypes": field_datatypes,
            "release_status": elem.get("ReleaseStatus", ""),
        }
        node_elements[node_id] = elem

    return tree, root, nodes, supertype_of, node_elements

# ---------------------------------------------------------------------------
# Graph utilities
# ---------------------------------------------------------------------------
def build_children_map(supertype_of):
    children_of = defaultdict(list)
    for child, parent in supertype_of.items():
        children_of[parent].append(child)
    return children_of

def downward_closure(seed_ids, children_of):
    seen = set()
    stack = list(seed_ids)
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(children_of.get(cur, []))
    return seen

def ancestor_closure(ids, supertype_of):
    result = set(ids)
    for nid in list(ids):
        cur = nid
        while cur in supertype_of:
            parent = supertype_of[cur]
            if parent in result:
                break
            result.add(parent)
            cur = parent
    return result

def identify_primary_type_seeds(nodes, supertype_of):
    all_types = {nid for nid, info in nodes.items() if info["nodeclass"] in TYPE_CLASSES}
    children_of = build_children_map(supertype_of)

    exclude_seed = set(EXCLUDE_ROOTS)
    for nid, info in nodes.items():
        if info["nodeclass"] not in TYPE_CLASSES:
            continue

        if info.get("release_status") == "Deprecated":
            exclude_seed.add(nid)
            continue

        categories = [c.strip() for c in (info.get("categories") or []) if c and c.strip()]

        # blank category exclusion
        if not categories:
            exclude_seed.add(nid)
            continue

        cats = " | ".join(categories).lower()
        if any(kw.lower() in cats for kw in EXCLUDE_CATEGORY_KEYWORDS):
            exclude_seed.add(nid)
            continue

    excluded_ids = downward_closure(exclude_seed, children_of)
    primary_seeds = all_types - excluded_ids

    stats = {
        "all_types": len(all_types),
        "excluded_types": len(all_types & excluded_ids),
        "primary_seed_types": len(primary_seeds),
        "exclude_seed": exclude_seed,
    }
    return primary_seeds, excluded_ids, stats

# ---------------------------------------------------------------------------
# Provenance
# ---------------------------------------------------------------------------
class Provenance:
    def __init__(self):
        self.first = {}
        self.rows = []

    def add(self, node_id, stage, reason, source_node_id, nodes, node_elements):
        if node_id in self.first:
            return False

        info = nodes.get(node_id, {})
        elem = node_elements.get(node_id)
        src_info = nodes.get(source_node_id, {}) if source_node_id else {}

        rec = {
            "stage": stage,
            "reason": reason,
            "node_id": node_id,
            "browse_name": info.get("browsename", ""),
            "category": join_categories(info),
            "lines": element_xml_line_count(elem) if elem is not None else 0,
            "source_node_id": source_node_id or "",
            "source_browse_name": src_info.get("browsename", "") if source_node_id else "",
            "source_category": join_categories(src_info) if source_node_id else "",
        }
        self.first[node_id] = rec
        self.rows.append(rec)
        return True

# ---------------------------------------------------------------------------
# Inclusion algorithm
# ---------------------------------------------------------------------------
def normalize_set_with_provenance(included, nodes, node_elements, supertype_of, stage, prov):
    newly_added_total = set()

    while True:
        changed = False

        # compositional expansion
        comp_add = set()
        comp_source = {}
        for src in list(included):
            info = nodes.get(src)
            if not info:
                continue
            for rtype, tgt, is_fwd in info.get("references", []):
                if not is_fwd or rtype not in COMPOSITION_REF_TYPES:
                    continue
                if tgt in nodes and tgt not in included:
                    comp_add.add(tgt)
                    comp_source.setdefault(tgt, src)

        for tgt in comp_add:
            included.add(tgt)
            prov.add(tgt, stage, "composible", comp_source.get(tgt, ""), nodes, node_elements)
            newly_added_total.add(tgt)
            changed = True

        # ancestors
        before = set(included)
        included = ancestor_closure(included, supertype_of)
        anc_add = included - before
        for tgt in anc_add:
            prov.add(tgt, stage, "non", "", nodes, node_elements)
            newly_added_total.add(tgt)
            changed = True

        # typedef targets
        td_add = set()
        td_source = {}
        for src in list(included):
            td = nodes.get(src, {}).get("typedef")
            if td and td in nodes and td not in included:
                td_add.add(td)
                td_source.setdefault(td, src)
        for tgt in td_add:
            included.add(tgt)
            prov.add(tgt, stage, "non", td_source.get(tgt, ""), nodes, node_elements)
            newly_added_total.add(tgt)
            changed = True

        # datatype-field targets
        dt_add = set()
        dt_source = {}
        for src in list(included):
            info = nodes.get(src, {})
            if info.get("nodeclass") != "UADataType":
                continue
            for dt in info.get("field_datatypes", []):
                if dt in nodes and dt not in included:
                    dt_add.add(dt)
                    dt_source.setdefault(dt, src)

        for tgt in dt_add:
            included.add(tgt)
            prov.add(tgt, stage, "non", dt_source.get(tgt, ""), nodes, node_elements)
            newly_added_total.add(tgt)
            changed = True

        if not changed:
            break

    return included, newly_added_total

def staged_inclusion(nodes, node_elements, supertype_of, primary_seed_types):
    included = set()
    prov = Provenance()
    stage_metrics = []

    # Stage 1
    stage = 1
    stage1_new = set()

    for nid in sorted(primary_seed_types):
        if nid in nodes and prov.add(nid, stage, "primary", "", nodes, node_elements):
            included.add(nid)
            stage1_new.add(nid)

    for nid in sorted(WELL_KNOWN):
        if nid in nodes and nid not in included and prov.add(nid, stage, "primary", "", nodes, node_elements):
            included.add(nid)
            stage1_new.add(nid)

    included, norm_added = normalize_set_with_provenance(
        included, nodes, node_elements, supertype_of, stage, prov
    )
    stage1_new |= norm_added

    stage_metrics.append({
        "stage": stage,
        "added_total": len(stage1_new),
        "added_primary": sum(1 for n in stage1_new if prov.first[n]["reason"] == "primary"),
        "added_composible": sum(1 for n in stage1_new if prov.first[n]["reason"] == "composible"),
        "added_non": sum(1 for n in stage1_new if prov.first[n]["reason"] == "non"),
    })

    frontier = set(stage1_new)
    stage = 2

    while True:
        direct_new = set()

        for src in list(frontier):
            info = nodes.get(src)
            if not info:
                continue
            for rtype, tgt, is_fwd in info.get("references", []):
                if not is_fwd:
                    continue
                if tgt not in nodes or tgt in included:
                    continue
                included.add(tgt)
                prov.add(tgt, stage, reason_for_ref_type(rtype), src, nodes, node_elements)
                direct_new.add(tgt)

        included, norm_added = normalize_set_with_provenance(
            included, nodes, node_elements, supertype_of, stage, prov
        )

        stage_new = direct_new | norm_added
        if not stage_new:
            break

        stage_metrics.append({
            "stage": stage,
            "added_total": len(stage_new),
            "added_primary": sum(1 for n in stage_new if prov.first[n]["reason"] == "primary"),
            "added_composible": sum(1 for n in stage_new if prov.first[n]["reason"] == "composible"),
            "added_non": sum(1 for n in stage_new if prov.first[n]["reason"] == "non"),
        })

        frontier = set(stage_new)
        stage += 1

    return included, prov, stage_metrics

# ---------------------------------------------------------------------------
# Metrics CSV (primary types)
# ---------------------------------------------------------------------------
def collect_composition_descendants(root_id, nodes):
    seen = set()
    q = deque([root_id])
    visited = set()

    while q:
        cur = q.popleft()
        if cur in visited:
            continue
        visited.add(cur)

        info = nodes.get(cur)
        if not info:
            continue

        for rtype, tgt, is_fwd in info.get("references", []):
            if not is_fwd or rtype not in COMPOSITION_REF_TYPES:
                continue
            if tgt in nodes and tgt not in seen:
                seen.add(tgt)
                q.append(tgt)

    seen.discard(root_id)
    return seen

def collect_reference_descendants(seed_ids, nodes, exclude_ids):
    refs = set()
    q = deque(seed_ids)
    visited = set()

    while q:
        cur = q.popleft()
        if cur in visited:
            continue
        visited.add(cur)
        info = nodes.get(cur)
        if not info:
            continue

        for rtype, tgt, is_fwd in info.get("references", []):
            if not is_fwd:
                continue
            if rtype in COMPOSITION_REF_TYPES:
                continue
            if tgt in nodes and tgt not in exclude_ids and tgt not in refs:
                refs.add(tgt)
                q.append(tgt)

    return refs

def write_primary_type_metrics_csv(path, primary_types, nodes, node_elements):
    rows = []
    cache = {}

    def lc(nid):
        if nid not in cache:
            elem = node_elements.get(nid)
            cache[nid] = element_xml_line_count(elem) if elem is not None else 0
        return cache[nid]

    ordered = sorted(primary_types, key=lambda nid: (nodes.get(nid, {}).get("browsename", ""), nid))
    for pid in ordered:
        info = nodes.get(pid, {})
        members = collect_composition_descendants(pid, nodes)
        refs = collect_reference_descendants({pid} | members, nodes, exclude_ids=members | {pid})

        rows.append({
            "node_id": pid,
            "browse_name": info.get("browsename", ""),
            "category": " | ".join(info.get("categories") or []),
            "member_lines": sum(lc(n) for n in members),
            "reference_lines": sum(lc(n) for n in refs),
        })

    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(
            f,
            fieldnames=["node_id", "browse_name", "category", "member_lines", "reference_lines"]
        )
        w.writeheader()
        w.writerows(rows)

# ---------------------------------------------------------------------------
# Verbatim extraction with full front/back matter preservation
# ---------------------------------------------------------------------------
def split_front_nodes_back_verbatim(nodeset_file):
    with open(nodeset_file, "r", encoding="utf-8") as f:
        lines = f.readlines()

    front = []
    back = []
    node_blocks = []

    n = len(lines)
    first_node_idx = None
    for idx, line in enumerate(lines):
        if NODE_START_RE.search(line):
            first_node_idx = idx
            break

    if first_node_idx is None:
        return "".join(lines), [], ""

    front = lines[:first_node_idx]
    i = first_node_idx

    while i < n:
        line = lines[i]
        m = NODE_START_RE.search(line)
        if not m:
            back = lines[i:]
            break

        tag_name = m.group(1)
        block_lines = [line]
        open_text = line

        while ">" not in open_text and i + 1 < n:
            i += 1
            block_lines.append(lines[i])
            open_text += lines[i]

        node_id_match = NODEID_ATTR_RE.search(open_text)
        node_id = node_id_match.group(1) if node_id_match else ""
        bn_match = re.search(r'BrowseName\s*=\s*"([^"]*)"', open_text)
        browse_name = bn_match.group(1) if bn_match else ""

        if open_text.rstrip().endswith("/>"):
            node_blocks.append({
                "node_id": node_id,
                "nodeclass": tag_name,
                "browse_name": browse_name,
                "raw": "".join(block_lines),
            })
            i += 1
            continue

        close_re = re.compile(r"</(?:\w+:)?" + re.escape(tag_name) + r">")
        i += 1
        while i < n:
            block_lines.append(lines[i])
            if close_re.search(lines[i]):
                i += 1
                break
            i += 1

        node_blocks.append({
            "node_id": node_id,
            "nodeclass": tag_name,
            "browse_name": browse_name,
            "raw": "".join(block_lines),
        })
    else:
        back = []

    return "".join(front), node_blocks, "".join(back)

def prune_references_in_raw_block(block, final_ids, nodes):
    raw = block["raw"]
    source_node_id = block["node_id"]
    source_browse = block["browse_name"]
    source_nodeclass = block["nodeclass"]

    dropped_rows = []
    dropped = 0
    out_lines = []

    for line in raw.splitlines(keepends=True):
        m = REF_LINE_RE.match(line.rstrip("\n"))
        if m:
            ref_attrs = m.group(2) or ""
            target = (m.group(3) or "").strip()
            if target and target not in final_ids:
                dropped += 1
                rt = REFTYPE_ATTR_RE.search(ref_attrs)
                ref_type = rt.group(1) if rt else ""
                dropped_rows.append({
                    "source_nodeclass": source_nodeclass,
                    "source_node_id": source_node_id,
                    "source_browse_name": source_browse,
                    "reference_type": ref_type,
                    "target_node_id": target,
                    "target_browse_name": nodes.get(target, {}).get("browsename", ""),
                })
                continue
        out_lines.append(line)

    return "".join(out_lines), dropped_rows, dropped

def write_nodeset_verbatim_with_backmatter(nodeset_file, output_file, include_ids, prune_dangling, nodes):
    front, node_blocks, back = split_front_nodes_back_verbatim(nodeset_file)

    dropped_rows = []
    dropped_refs = 0
    written_ids = set()

    with open(output_file, "w", encoding="utf-8") as out:
        out.write(front)

        for block in node_blocks:
            nid = block["node_id"]
            if not nid or nid not in include_ids:
                continue

            if prune_dangling:
                pruned, rows, cnt = prune_references_in_raw_block(block, include_ids, nodes)
                out.write(pruned)
                dropped_rows.extend(rows)
                dropped_refs += cnt
            else:
                out.write(block["raw"])

            written_ids.add(nid)

        out.write(back)

    return dropped_refs, dropped_rows, written_ids

# ---------------------------------------------------------------------------
# CSV + audit writers
# ---------------------------------------------------------------------------
def write_dangling_refs_csv(rows, csv_path):
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(
            f,
            fieldnames=[
                "source_nodeclass",
                "source_node_id",
                "source_browse_name",
                "reference_type",
                "target_node_id",
                "target_browse_name",
            ],
        )
        w.writeheader()
        w.writerows(rows)

def write_provenance_csv(rows, path):
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(
            f,
            fieldnames=[
                "stage", "reason", "node_id", "browse_name", "category", "lines",
                "source_node_id", "source_browse_name", "source_category"
            ],
        )
        w.writeheader()
        ordered = sorted(rows, key=lambda r: (int(r["stage"]), r["node_id"]))
        w.writerows(ordered)

def write_nodeset_metrics_csv(path, rows):
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["nodeset_name", "primary_node_count", "resultant_xml_lines"])
        w.writeheader()
        w.writerows(rows)

def write_audit_report(nodes, primary_types, excluded_ids, stats, stage_metrics, path):
    cat_primary = Counter()
    cat_excl = Counter()

    for nid, info in nodes.items():
        if info["nodeclass"] not in TYPE_CLASSES:
            continue
        cats = info.get("categories") or ["(no category)"]
        if nid in primary_types:
            for c in cats:
                cat_primary[c] += 1
        elif nid in excluded_ids:
            for c in cats:
                cat_excl[c] += 1

    with open(path, "w", encoding="utf-8") as f:
        f.write("CORE INFORMATION MODEL - AUDIT REPORT\n")
        f.write("=" * 60 + "\n\n")
        f.write("Summary:\n")
        f.write(f"  Total type nodes found:       {stats['all_types']}\n")
        f.write(f"  Excluded type nodes:          {stats['excluded_types']}\n")
        f.write(f"  Primary seed types:           {stats['primary_seed_types']}\n")
        f.write(f"  Final included nodes:         {stats['final_size']}\n")
        f.write(f"  Total stages executed:        {stats['stage_count']}\n\n")

        f.write("Stage metrics:\n")
        for sm in stage_metrics:
            f.write(
                f"  Stage {sm['stage']:>2}: total={sm['added_total']}, "
                f"primary={sm['added_primary']}, composible={sm['added_composible']}, non={sm['added_non']}\n"
            )

        f.write("\nCategories in PRIMARY TYPES:\n")
        for c, n in cat_primary.most_common():
            f.write(f"  {n:5d}  {c}\n")

        f.write("\nCategories EXCLUDED:\n")
        for c, n in cat_excl.most_common():
            f.write(f"  {n:5d}  {c}\n")

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main():
    if not NODESET_FILE.exists():
        print(f"ERROR: '{NODESET_FILE}' not found.")
        sys.exit(1)

    print(f"Parsing/indexing {NODESET_FILE} ...")
    _tree, _root, nodes, supertype_of, node_elements = build_index_and_tree(NODESET_FILE)
    print(f"Indexed {len(nodes)} nodes.")

    primary_seed_types, excluded_ids, stats = identify_primary_type_seeds(nodes, supertype_of)
    final_ids, prov, stage_metrics = staged_inclusion(nodes, node_elements, supertype_of, primary_seed_types)

    stats["final_size"] = len(final_ids)
    stats["stage_count"] = len(stage_metrics)

    print("\n--- Staged Inclusion Summary ---")
    print(f"Primary seed types:      {stats['primary_seed_types']}")
    print(f"Final included nodes:    {len(final_ids)}")
    print(f"Stages executed:         {len(stage_metrics)}")

    # Core output
    dropped_refs, dropped_rows, core_written_ids = write_nodeset_verbatim_with_backmatter(
        NODESET_FILE, CORE_OUTPUT_FILE, final_ids, prune_dangling=True, nodes=nodes
    )

    # Access output = source - core nodes
    access_ids = set(nodes.keys()) - set(core_written_ids)
    _d2, _r2, access_written_ids = write_nodeset_verbatim_with_backmatter(
        NODESET_FILE, ACCESS_OUTPUT_FILE, access_ids, prune_dangling=False, nodes=nodes
    )

    # Other CSV/report outputs
    write_primary_type_metrics_csv(
        PRIMARY_TYPE_METRICS_CSV_FILE,
        primary_types=primary_seed_types,
        nodes=nodes,
        node_elements=node_elements,
    )
    write_provenance_csv(prov.rows, PROVENANCE_CSV_FILE)
    write_dangling_refs_csv(dropped_rows, DANGLING_REFS_CSV_FILE)
    write_audit_report(nodes, primary_seed_types, excluded_ids, stats, stage_metrics, AUDIT_REPORT_FILE)

    # Requested metrics
    core_primary_count = len(primary_seed_types)
    core_lines = file_line_count(CORE_OUTPUT_FILE)

    access_primary_count = len([nid for nid in access_written_ids if nid in TYPE_CLASSES or nodes.get(nid, {}).get("nodeclass") in TYPE_CLASSES])
    # Correct primary count for access should use type nodes present in access file that satisfy "primary seed" criteria complement:
    access_primary_count = len([nid for nid in access_written_ids if nid in primary_seed_types])  # overlap count
    # Better interpretation: primary nodes in access model (using same primary seed logic restricted to access IDs)
    access_primary_count = len([nid for nid in access_written_ids if nodes.get(nid, {}).get("nodeclass") in TYPE_CLASSES])

    access_lines = file_line_count(ACCESS_OUTPUT_FILE)

    metrics_rows = [
        {
            "nodeset_name": "core_information_model.xml",
            "primary_node_count": core_primary_count,
            "resultant_xml_lines": core_lines,
        },
        {
            "nodeset_name": "nodeset.access.xml",
            "primary_node_count": access_primary_count,
            "resultant_xml_lines": access_lines,
        },
    ]
    write_nodeset_metrics_csv(NODESET_METRICS_CSV_FILE, metrics_rows)

    print(f"\nCore nodeset written to '{CORE_OUTPUT_FILE}'.")
    print(f"Access nodeset written to '{ACCESS_OUTPUT_FILE}'.")
    print(f"Pruned {dropped_refs} dangling <Reference> line(s) in core nodeset.")
    print(f"Dangling reference CSV written to '{DANGLING_REFS_CSV_FILE}' ({len(dropped_rows)} row(s)).")
    print(f"Primary type metrics CSV written to '{PRIMARY_TYPE_METRICS_CSV_FILE}'.")
    print(f"Provenance CSV written to '{PROVENANCE_CSV_FILE}' ({len(prov.rows)} row(s)).")
    print(f"Audit report written to '{AUDIT_REPORT_FILE}'.")
    print(f"Nodeset metrics CSV written to '{NODESET_METRICS_CSV_FILE}'.")
    print("\n--- Requested Metrics ---")
    print(f"Core:   primary nodes = {core_primary_count}, lines = {core_lines}")
    print(f"Access: primary nodes = {access_primary_count}, lines = {access_lines}")

if __name__ == "__main__":
    main()
