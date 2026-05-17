#!/usr/bin/env python3
"""Parse criterion JSON output and produce a markdown summary table.

Run benchmarks first with: cargo bench --features ipnet
Then run this script to generate the results table.
"""

import json
import os
import sys

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CRITERION_DIR = os.path.join(PROJECT_ROOT, "target", "criterion")

# Benchmark sections: (section_header, [(row_label, group_id_ipv4, group_id_ipv6)])
SECTIONS = [
    ("Lookup", [
        ("Random access", "bgp-lookup-random-ipv4", "bgp-lookup-random-ipv6"),
        ("RIS updates",   "bgp-lookup-ris-ipv4",    "bgp-lookup-ris-ipv6"),
    ]),
    ("Insert & Remove", [
        ("Random access", "bgp-mods-random-ipv4", "bgp-mods-random-ipv6"),
        ("RIS updates",   "bgp-mods-ris-ipv4",    "bgp-mods-ris-ipv6"),
    ]),
    ("Create", [
        ("Random order",    "bgp-create-random-ipv4",    "bgp-create-random-ipv6"),
        ("Sorted order",    "bgp-create-ordered-ipv4",   "bgp-create-ordered-ipv6"),
        ("Scattered order", "bgp-create-scattered-ipv4", "bgp-create-scattered-ipv6"),
    ]),
]

FUNCTIONS = ["HashMap", "PrefixMap", "TreeBitMap", "BTreeMap"]


def read_json(path):
    try:
        with open(path) as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return None


def load_throughput(group_id, function_name):
    """Load throughput (elements/s) for a group/function pair, or None."""
    base = os.path.join(CRITERION_DIR, group_id, function_name, "new")
    benchmark = read_json(os.path.join(base, "benchmark.json"))
    estimates = read_json(os.path.join(base, "estimates.json"))
    if benchmark is None or estimates is None:
        return None
    throughput_spec = benchmark.get("throughput")
    if not throughput_spec or "Elements" not in throughput_spec:
        return None
    elements = throughput_spec["Elements"]
    mean_ns = estimates["mean"]["point_estimate"]
    return elements / (mean_ns / 1e9)


def format_throughput(throughput):
    if throughput >= 1e9:
        return f"{throughput / 1e9:.1f} Gops"
    elif throughput >= 1e6:
        return f"{throughput / 1e6:.1f} Mops"
    elif throughput >= 1e3:
        return f"{throughput / 1e3:.1f} Kops"
    else:
        return f"{throughput:.0f} ops"


def format_cell(throughput, baseline, is_best):
    if throughput is None:
        return "  —"
    ratio = throughput / baseline
    text = f"{ratio:.2f}x ({format_throughput(throughput)})"
    if is_best:
        return f"**{text}**"
    else:
        return f"  {text}"


def build_row(label, group_id):
    """Build one table row. Returns (label, [cell_strings])."""
    throughputs = {}
    for fn in FUNCTIONS:
        throughputs[fn] = load_throughput(group_id, fn)

    baseline = throughputs.get("HashMap")
    if baseline is None:
        return label, ["  —"] * len(FUNCTIONS)

    valid = {fn: t for fn, t in throughputs.items() if t is not None}
    best_fn = max(valid, key=lambda fn: valid[fn]) if valid else None

    cells = []
    for fn in FUNCTIONS:
        cells.append(format_cell(throughputs[fn], baseline, fn == best_fn))
    return label, cells


def align_table(rows):
    """Given list of row tuples (col0, col1, ...), pad all columns to equal width.

    A None entry in rows produces a separator line (dashes).
    """
    num_cols = max(len(r) for r in rows if r is not None)
    widths = [0] * num_cols
    for row in rows:
        if row is None:
            continue
        for i, cell in enumerate(row):
            widths[i] = max(widths[i], len(cell))

    lines = []
    for row in rows:
        if row is None:
            parts = ["-" * (w + 2) for w in widths]
            lines.append("|" + "|".join(parts) + "|")
        else:
            parts = []
            for i, cell in enumerate(row):
                parts.append(f" {cell:<{widths[i]}} ")
            lines.append("|" + "|".join(parts) + "|")
    return "\n".join(lines)


def generate_table(results):
    """Generate aligned markdown table. results[group_id][fn] = throughput."""
    header = ("Benchmark", "`HashMap`", "`PrefixMap`", "`TreeBitMap`", "`BTreeMap`")

    table_rows = [header, None]  # None is a placeholder for the separator

    for section_name, benchmarks in SECTIONS:
        table_rows.append((f"*{section_name}*", "", "", "", ""))
        for row_label, group_ipv4, group_ipv6 in benchmarks:
            table_rows.append((f"-> {row_label}", "", "", "", ""))
            _, cells4 = build_row("", group_ipv4)
            table_rows.append((f"---> IPv4", *cells4))
            _, cells6 = build_row("", group_ipv6)
            table_rows.append((f"---> IPv6", *cells6))

    return align_table(table_rows)


def main():
    if not os.path.isdir(CRITERION_DIR):
        print(f"No criterion output found at {CRITERION_DIR}", file=sys.stderr)
        print("Run benchmarks first: cargo bench --features ipnet", file=sys.stderr)
        sys.exit(1)

    print("Collecting results from criterion JSON output...\n")

    table = generate_table(None)

    output_path = os.path.join(PROJECT_ROOT, "benches", "results.md")
    with open(output_path, "w") as f:
        f.write("# Benchmark Results\n\n")
        f.write("Throughput is reported relative to `HashMap` (1.00x = HashMap speed), "
                "with absolute throughput in parentheses.\n\n")
        f.write(table)
        f.write("\n")

    print(table)
    print(f"\nResults written to {output_path}")


if __name__ == "__main__":
    main()
