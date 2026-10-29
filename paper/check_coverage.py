#!/usr/bin/env python3
"""Check module coverage without starting Lean or Lake.

Run `python3 bsp/note/check_coverage.py` for the group counts.
Add `--write-report` to update groups-report.md beside this script.
Add `--module BstLean.Part293FinalAudit` to inspect a module assignment.
All input paths default to paths relative to this script, not the current directory.
"""

import argparse
from collections import Counter
from fnmatch import fnmatchcase, translate
import hashlib
import json
import re
from pathlib import Path
import runpy
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def read_inputs(closure_path, depmap_path):
    modules = closure_path.read_text().splitlines()
    if not modules or any(not m or m != m.strip() for m in modules):
        raise ValueError("The closure contains an empty or whitespace-padded module name.")
    duplicates = [m for m, n in Counter(modules).items() if n != 1]
    if duplicates:
        raise ValueError("Duplicate closure modules: " + ", ".join(duplicates))
    counts = {}
    for line_number, line in enumerate(depmap_path.read_text().splitlines(), 1):
        fields = line.split("\t")
        if len(fields) != 2:
            raise ValueError(f"Invalid dependency row {line_number}: expected two TSV fields.")
        module, count_text = fields
        count = int(count_text)
        if count < 0 or module in counts:
            raise ValueError(f"Invalid or duplicate dependency row {line_number}: {module}")
        counts[module] = count
    outside = set(counts) - set(modules)
    if outside:
        raise ValueError("Dependency modules outside the closure: " + ", ".join(sorted(outside)))
    return modules, {m for m, count in counts.items() if count > 0}


def classify(modules, used, groups, steps):
    """Return first-match assignments, group rows, and validation errors."""
    errors = []
    ids = [g["id"] for g in groups]
    if len(ids) != len(set(ids)):
        errors.append("Group IDs are not unique.")
    for g in groups:
        if g["step"] not in steps:
            errors.append(f"{g['id']}: unknown step {g['step']}.")
        if not g["patterns"] or not all(isinstance(p, str) and p for p in g["patterns"]):
            errors.append(f"{g['id']}: empty or invalid patterns.")
        if not g["description"]:
            errors.append(f"{g['id']}: empty description.")
    assignments = {}
    members = {g["id"]: [] for g in groups}
    # Compile one union per group. This avoids millions of Python-level glob
    # calls while the independent Lean build uses the same machine.
    matchers = [(g, re.compile("|".join(translate(p) for p in g["patterns"])).match)
                for g in groups if g["patterns"]]
    for module in modules:
        for g, matches in matchers:
            if matches(module):
                assignments[module] = g["id"]
                members[g["id"]].append(module)
                break
        else:
            errors.append(f"UNMATCHED: {module}")
    rows = []
    for g in groups:
        names = members[g["id"]]
        used_names = sorted(set(names) & used)
        flags = []
        if not names:
            flags.append("EMPTY_GROUP")
        if g["step"] != "S11" and not used_names:
            flags.append("NO_USED_FILES")
        if g["step"] == "S11" and used_names:
            flags.append("S11_CONTAINS_USED")
            errors.extend(f"S11_CONTAINS_USED: {m}" for m in used_names)
        # This map places every compiled-only module in S11. Enforce that
        # stronger invariant as well as the two requested group-level flags.
        misplaced = sorted(set(names) - used) if g["step"] != "S11" else []
        if misplaced:
            flags.append("UNUSED_OUTSIDE_S11")
            errors.extend(f"UNUSED_OUTSIDE_S11: {m}" for m in misplaced)
        if flags:
            errors.append(f"{g['id']}: {', '.join(flags)}")
        rows.append(dict(g, files=len(names), used=len(used_names), flags=flags))
    return assignments, rows, errors


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def report_text(modules, used, rows, errors, config, paths):
    verdict = "PASS" if not errors else "FAIL"
    text = [
        f"Verdict: {verdict} for module coverage and dependency-status separation; the semantic map has the qualifications below.",
        "",
        "This report uses Simplified Technical English for Agents (STEA), "
        "Skill(stea:use-simplified-technical-english-for-agents).",
        "",
        f"The map assigns {len(modules):,} project modules to {len(rows)} groups. "
        f"The final theorem dependencies use {len(used):,} modules. "
        f"The other {len(modules) - len(used):,} modules belong to S11. "
        "A used file contains at least one declaration with a positive count in `depmap.tsv`; "
        "this does not mean that its headline theorem or every declaration is used. "
        "Mathlib modules are outside this closure list.",
        "",
        "The checker uses the first matching group in `groups.py`. "
        "The fixed S11 patterns take precedence over the numbered-part patterns. "
        "Specific analytic groups then take precedence over broad dimension groups. "
        "All names in the table are module globs, with the prefix `BstLean.` omitted. "
        "The named S11 pattern set is expanded after the table. "
        "The suffix `[!0-9]*` prevents a part such as Part29 from matching Part290.",
        "",
        "The source review covers the final theorem joins, the principal analytic interfaces, "
        "representative module headers, and the supplied records. Generated families are "
        "classified by their shared interfaces and representative files. "
        "The grouping is a file-level proof map. "
        "It is not a new proof audit, a declaration-level dependency map, or a build result. "
        "No Lean or Lake command forms part of this check.",
        "",
        "| Step | Group | Pattern | Files | Used | Description |",
        "|---|---|---|---:|---:|---|",
    ]
    for row in sorted(rows, key=lambda r: (int(r["step"][1:]), rows.index(r))):
        if row["id"] == "G00-unused":
            pattern = "`UNUSED_PATTERNS` (fixed globs below)"
        else:
            pattern = ", ".join("`" + p.removeprefix("BstLean.") + "`" for p in row["patterns"])
        text.append(f"| {row['step']} | {row['id']} | {pattern} | {row['files']} | {row['used']} | {row['description']} |")
    text += ["", "Step totals:", "", "| Step | Meaning | Files | Used |", "|---|---|---:|---:|"]
    for step, meaning in config["STEPS"].items():
        same = [r for r in rows if r["step"] == step]
        text.append(f"| {step} | {meaning} | {sum(r['files'] for r in same)} | {sum(r['used'] for r in same)} |")
    text += [
        "", "Assignments with limited confidence:", "",
        "These modules have a broad placement, but their exact declaration-level role "
        "remains unresolved from the supplied module counts. They are not unassigned modules.", "",
    ]
    for pattern, step, reason in config.get("PLACEMENT_NOTES", []):
        names = [m for m in modules if m in used and fnmatchcase(m, pattern)]
        text.append(f"- `{pattern}` ({step}; {len(names)} used file(s)): {reason}")
    text += [
        "",
        "Range joins: `Part278Stated16200` supplies S6; `Part287All` joins S7 to S6; "
        "`Part281Family` supplies S8; `Part293Assembly` and `Part293FinalAudit` supply S9. "
        "`Part293High` and `Part293FinalAudit` join all four ranges. "
        "`Part289Cost.progOut_run2` is the separate final cost theorem. "
        "The low-band frame proof uses internal interval covers; S9 remains one theorem band.",
        "",
        "Cross-step files: the Gaussian regression in S2 also supports Agent replacement; "
        "the centre and covariance bounds in S3 also support the roots in S4; "
        "the interval arithmetic in S5 also supports every dimension range. "
        "The broad dimension groups contain reusable analytic lemmas as well as range-specific certificates. "
        "A group assignment does not assert an exclusive mathematical use.",
        "",
        "The `evidence` field of each group names source anchors. "
        "The Lean source is the authority for each group's role.",
        "",
        "Coverage flags: " + ("none." if not errors else "see the following failures."),
    ]
    if errors:
        text += ["", *["- " + error for error in errors]]
    text += [
        "", "Reproduce the file check with `python3 bsp/note/check_coverage.py --write-report`.",
        "", "Input SHA-256 values:", "",
    ]
    for label, path in paths.items():
        text.append(f"- `{label}`: `{digest(path)}`")
    text += [
        "", "<details>", "<summary>Fixed S11 module patterns</summary>", "",
        "These patterns describe the compiled-only modules in the inspected snapshot. "
        "They do not read or filter the dependency report when `groups.py` is imported.",
        "", "```text", *config["UNUSED_PATTERNS"], "```", "", "</details>", "",
    ]
    return "\n".join(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--closure", type=Path, default=HERE.parent / "lean/closure.txt")
    parser.add_argument("--depmap", type=Path, default=HERE.parent / "lean/reports/depmap.tsv")
    parser.add_argument("--groups", type=Path, default=HERE / "groups.py")
    parser.add_argument("--write-report", action="store_true")
    parser.add_argument("--module", help="Show the group of this module.")
    parser.add_argument("--json", action="store_true", help="Print machine-readable results.")
    args = parser.parse_args()
    try:
        modules, used = read_inputs(args.closure, args.depmap)
        config = runpy.run_path(str(args.groups))
        assignments, rows, errors = classify(modules, used, config["GROUPS"], config["STEPS"])
        if args.module and args.module not in assignments:
            errors.append(f"Requested module has no assignment: {args.module}")
        if args.write_report:
            paths = {"closure.txt": args.closure, "depmap.tsv": args.depmap, "groups.py": args.groups}
            (HERE / "groups-report.md").write_text(report_text(modules, used, rows, errors, config, paths))
        if args.json:
            print(json.dumps(dict(total=len(modules), used=len(used), groups=rows,
                                  errors=errors, assignments=assignments), ensure_ascii=False, indent=2))
        elif args.module:
            identifier = assignments.get(args.module)
            row = next((r for r in rows if r["id"] == identifier), None)
            if row:
                print(f"{args.module}\t{row['step']}\t{identifier}\tused={args.module in used}")
                print(row["description"])
        else:
            print("group\tstep\tfiles\tused\tflags")
            for row in rows:
                print(f"{row['id']}\t{row['step']}\t{row['files']}\t{row['used']}\t{','.join(row['flags'])}")
            print(f"TOTAL\t\t{len(modules)}\t{len(used)}")
        for error in errors:
            print(error, file=sys.stderr)
        print("FAIL" if errors else "PASS", file=sys.stderr)
        return 1 if errors else 0
    except (OSError, ValueError, KeyError, TypeError, SyntaxError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
