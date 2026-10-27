#!/usr/bin/env python3
"""Parse criterion JSON output and produce a markdown summary.

Run benchmarks first with: cargo bench --features ipnet
Then run this script to generate the results tables.

Each measurement kind gets its own section: a description of the experiment
above the table, and remarks (footnotes) below it. The output is complete
markdown that can be copy-pasted into the README.
"""

from __future__ import annotations

import json
import os
import sys
from dataclasses import dataclass, field

PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CRITERION_DIR = os.path.join(PROJECT_ROOT, "target", "criterion")

FOOTNOTE_MARKS = ["†", "‡", "§", "¶", "††", "‡‡", "§§", "¶¶"]


@dataclass
class Section:
    """One measurement kind, rendered as description, table, and remarks.

    rows:       (row label, criterion group for IPv4, criterion group for IPv6)
    columns:    function names as they appear in the criterion output
    baseline:   column that ratios are reported against, or None for absolute
                numbers only
    unit:       "elements" for throughput (elements/s from criterion) or
                "seconds" for the mean wall time of one operation
    footnotes:  (row label or None for any row, column) -> remark text
    """

    title: str
    description: str
    rows: list
    columns: list
    baseline: str | None
    unit: str
    footnotes: dict = field(default_factory=dict)
    throughput_label: str = "ops/s"


SECTIONS = [
    Section(
        title="Lookup",
        description=(
            "Exact lookup of a prefix, i.e. retrieving the value stored for a whole\n"
            "prefix. Throughput is reported relative to `HashMap` (1.00x = HashMap\n"
            "speed), with absolute throughput in parentheses. Benchmarked with two\n"
            "workloads: prefixes drawn at random from the RIS initial state, and\n"
            "prefixes observed in RIS routing-table updates."
        ),
        rows=[
            ("Random access", "bgp-lookup-random-ipv4", "bgp-lookup-random-ipv6"),
            ("RIS updates", "bgp-lookup-ris-ipv4", "bgp-lookup-ris-ipv6"),
        ],
        columns=["HashMap", "PrefixMap", "TreeBitMap", "BTreeMap"],
        baseline="HashMap",
        unit="elements",
    ),
    Section(
        title="Insert & Remove",
        description=(
            "Applying a stream of insertions and removals to a pre-filled table.\n"
            "Throughput is reported relative to `HashMap` (1.00x = HashMap speed),\n"
            "with absolute throughput in parentheses. Benchmarked with two\n"
            "workloads: random insert/remove pairs on prefixes drawn from the RIS\n"
            "initial state, and the mutation stream observed from a RIS peer."
        ),
        rows=[
            ("Random access", "bgp-mods-random-ipv4", "bgp-mods-random-ipv6"),
            ("RIS updates", "bgp-mods-ris-ipv4", "bgp-mods-ris-ipv6"),
        ],
        columns=["HashMap", "PrefixMap", "TreeBitMap", "BTreeMap"],
        baseline="HashMap",
        unit="elements",
    ),
    Section(
        title="Create",
        description=(
            "Building a table from scratch from the prefixes of the RIS initial\n"
            "state. Throughput is reported relative to `HashMap` (1.00x = HashMap\n"
            "speed), with absolute throughput in parentheses. Benchmarked with three\n"
            "insertion orders: random, sorted (lexicographic), and scattered\n"
            "(reversed-bit)."
        ),
        rows=[
            ("Random order", "bgp-create-random-ipv4", "bgp-create-random-ipv6"),
            ("Sorted order", "bgp-create-ordered-ipv4", "bgp-create-ordered-ipv6"),
            ("Scattered order", "bgp-create-scattered-ipv4", "bgp-create-scattered-ipv6"),
        ],
        columns=["HashMap", "PrefixMap", "TreeBitMap", "BTreeMap"],
        baseline="HashMap",
        unit="elements",
    ),
    Section(
        title="Longest-prefix match",
        description=(
            "Lookup of the longest matching prefix for random host addresses, each\n"
            "drawn inside one of the prefixes of the RIS initial state, so that every\n"
            "lookup has a match at some depth. `HashMap` and `BTreeMap` are omitted,\n"
            "since they do not support longest-prefix match; throughput is reported\n"
            "relative to `TreeBitMap` (1.00x = TreeBitMap speed), with absolute\n"
            "throughput in parentheses."
        ),
        rows=[
            ("Random hosts", "bgp-lpm-random-ipv4", "bgp-lpm-random-ipv6"),
        ],
        columns=["PrefixMap", "TreeBitMap"],
        baseline="TreeBitMap",
        unit="elements",
    ),
    Section(
        title="Clone",
        description=(
            "Copying an entire routing table built from the RIS initial state.\n"
            "TrivialClone uses `u32` values; NonTrivialClone uses a wrapper whose\n"
            "clone passes the value through `black_box`. `PrefixMap` uses its bulk\n"
            "clone specialization for `u32` only with the `nightly` feature.\n"
            "Throughput is measured in elements per second relative to `HashMap`\n"
            "(1.00x = HashMap speed), with absolute throughput in parentheses.\n"
            "elem/s is the number of elements in the table divided by the time to\n"
            "copy it, not the number of whole-table copies per second."
        ),
        throughput_label="elem/s",
        rows=[
            ("TrivialClone", "bgp-clone-ipv4", "bgp-clone-ipv6"),
            ("NonTrivialClone", "bgp-clone-nontrivial-ipv4", "bgp-clone-nontrivial-ipv6"),
        ],
        columns=["HashMap", "PrefixMap", "TreeBitMap", "BTreeMap"],
        baseline="HashMap",
        unit="elements",
        footnotes={
            (None, "TreeBitMap"):
                "`TreeBitMap` does not implement `Clone`; it is copied by iterating "
                "the source table and rebuilding the copy.",
            ("TrivialClone", "PrefixMap"):
                "Measurements were done with the `nightly` feature enabled. Without "
                "it, the performance is similar to `NonTrivialClone`. In stable rust, "
                "use `clone_memcpy`.",
        },
    ),
    Section(
        title="Iteration",
        description=(
            "Traversing and consuming all elements of a table built from the RIS\n"
            "initial state, without sorting the output of the unordered maps.\n"
            "Throughput is measured in elements per second and reported relative to\n"
            "`HashMap` (1.00x = HashMap speed), with absolute throughput in parentheses."
        ),
        throughput_label="elem/s",
        rows=[
            ("Whole table", "bgp-iter-ipv4", "bgp-iter-ipv6"),
        ],
        columns=["HashMap", "PrefixMap", "TreeBitMap", "BTreeMap"],
        baseline="HashMap",
        unit="elements",
        footnotes={
            (None, "PrefixMap"): "`PrefixMap` yields entries in lexicographic prefix order.",
            (None, "BTreeMap"): "`BTreeMap` yields entries in key order (the prefix type's `Ord` ordering).",
        },
    ),
    Section(
        title="Aggregation",
        description=(
            "Aggregating the whole table built from the RIS initial state with\n"
            "optimal routing table construction: `set` is the bitmap-only\n"
            "`PrefixSet::aggregate` (drop + merge), `map` the value-aware\n"
            "`PrefixMap::aggregate`, and `ortc` `PrefixMap::aggregate_fill_default`.\n"
            "Each prefix is assigned a next hop from 1..=32 (emulating 32\n"
            "interfaces), so the ORTC actually merges. Reported as absolute time per\n"
            "full-table aggregation; the three variants perform different operations\n"
            "and are not directly comparable."
        ),
        rows=[
            ("Whole table", "aggregate-ipv4", "aggregate-ipv6"),
        ],
        columns=["set", "map", "ortc"],
        baseline=None,
        unit="seconds",
    ),
]


@dataclass
class Sample:
    """One measurement from the criterion output."""

    elements: int | None  # elements per iteration, or None if not declared
    mean_ns: float  # mean iteration time in nanoseconds


def read_json(path):
    try:
        with open(path) as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return None


def load_sample(group_id, function_name):
    """Load the newest measurement for a group/function pair, or None."""
    base = os.path.join(CRITERION_DIR, group_id, function_name, "new")
    benchmark = read_json(os.path.join(base, "benchmark.json"))
    estimates = read_json(os.path.join(base, "estimates.json"))
    if benchmark is None or estimates is None:
        return None
    throughput = benchmark.get("throughput") or {}
    return Sample(
        elements=throughput.get("Elements"),
        mean_ns=estimates["mean"]["point_estimate"],
    )


def sample_throughput(sample):
    """Elements per second, or None if the sample is missing or has no throughput."""
    if sample is None or sample.elements is None:
        return None
    return sample.elements / (sample.mean_ns / 1e9)


def format_throughput(throughput, label):
    if throughput >= 1e9:
        return f"{throughput / 1e9:.1f} G{label}"
    elif throughput >= 1e6:
        return f"{throughput / 1e6:.1f} M{label}"
    elif throughput >= 1e3:
        return f"{throughput / 1e3:.1f} K{label}"
    else:
        return f"{throughput:.0f} {label}"


def format_time(ns):
    if ns >= 1e9:
        return f"{ns / 1e9:.1f} s"
    elif ns >= 1e6:
        return f"{ns / 1e6:.0f} ms"
    elif ns >= 1e3:
        return f"{ns / 1e3:.0f} µs"
    else:
        return f"{ns:.0f} ns"


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


def render_section(section):
    """Render one section as markdown: title, description, table, remarks."""
    marks = {}  # remark text -> footnote mark, in order of first appearance

    def mark_for(text):
        if text not in marks:
            marks[text] = FOOTNOTE_MARKS[len(marks)]
        return marks[text]

    def remark_for(row_label, column):
        # An exact row match wins over a column-wide remark.
        text = section.footnotes.get((row_label, column))
        if text is None:
            text = section.footnotes.get((None, column))
        return text

    def build_cells(group_id, row_label):
        samples = {col: load_sample(group_id, col) for col in section.columns}
        if section.baseline is not None:
            baseline_value = sample_throughput(samples.get(section.baseline))
        else:
            baseline_value = None
        values = {col: sample_throughput(s) for col, s in samples.items()}
        valid = {col: v for col, v in values.items() if v is not None}
        best = max(valid, key=valid.get) if valid else None

        cells = []
        for col in section.columns:
            sample, value = samples[col], values[col]
            if section.unit == "seconds":
                text = format_time(sample.mean_ns) if sample else "—"
            elif value is None:
                text = "—"
            elif baseline_value:
                text = f"{value / baseline_value:.2f}x ({format_throughput(value, section.throughput_label)})"
            else:
                text = format_throughput(value, section.throughput_label)
            if section.baseline is not None and col == best:
                text = f"**{text}**"
            else:
                text = f"  {text}"
            remark = remark_for(row_label, col)
            if remark:
                text = f"{text} {mark_for(remark)}"
            cells.append(text)
        return cells

    table_rows = [("Benchmark", *(f"`{c}`" for c in section.columns)), None]
    if len(section.rows) == 1:
        # Single benchmark: only the IPv4/IPv6 rows, no workload label column.
        row_label, group_ipv4, group_ipv6 = section.rows[0]
        table_rows.append(("IPv4", *build_cells(group_ipv4, row_label)))
        table_rows.append(("IPv6", *build_cells(group_ipv6, row_label)))
    else:
        for row_label, group_ipv4, group_ipv6 in section.rows:
            table_rows.append((f"*{row_label}*", *[""] * len(section.columns)))
            table_rows.append((f"--> IPv4", *build_cells(group_ipv4, row_label)))
            table_rows.append((f"--> IPv6", *build_cells(group_ipv6, row_label)))
    table = align_table(table_rows)

    lines = [f"### {section.title}", "", section.description, "", table]
    if marks:
        lines.append("")
        for text, mark in sorted(marks.items(), key=lambda item: FOOTNOTE_MARKS.index(item[1])):
            lines.append(f"{mark} {text}")
    return "\n".join(lines)


def main():
    if not os.path.isdir(CRITERION_DIR):
        print(f"No criterion output found at {CRITERION_DIR}", file=sys.stderr)
        print("Run benchmarks first: cargo bench --features ipnet", file=sys.stderr)
        sys.exit(1)

    print("Collecting results from criterion JSON output...\n")

    sections = [render_section(section) for section in SECTIONS]
    document = "\n\n".join(sections) + "\n"

    output_path = os.path.join(PROJECT_ROOT, "benches", "results.md")
    with open(output_path, "w") as f:
        f.write(document)

    print(document)
    print(f"\nResults written to {output_path}")


if __name__ == "__main__":
    main()
