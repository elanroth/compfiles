#!/usr/bin/env python3
"""
autoprove.py — deterministic bookkeeping for the Compfiles overnight proving loop.

This helper owns the three things the autonomous agent must NOT eyeball:
  1. the metric        — open proof obligations (sorry / admit / proof_wanted)
  2. target selection  — which file to attack next (cheapest first)
  3. the run log        — append-only proofs.tsv + a human-needed queue

It is intentionally dependency-free (stdlib only) and does not call Rambam,
Lean, or the network. The agent (driven by program.md) calls Rambam + git;
this script just measures and records. Authoritative obligation discovery is
`rambam preflight`; this is the fast, scriptable cross-check + metric.

Usage:
  autoprove.py count   [PATH ...]        [--json]      # obligations in file(s)/repo
  autoprove.py targets [--root DIR] [--with-notes] [--limit N] [--json]
  autoprove.py log     --target F --prover P --before N --after M \
                       --status keep|revert|crash|human [--commit SHA] [--note "..."]
  autoprove.py queue   add  --target F --decl NAME --reason "..."
  autoprove.py queue   list [--json]
  autoprove.py queue   done --decl NAME
  autoprove.py status  [--root DIR]

Exit code of `count` is 0 always; the obligation total is on stdout.
"""

from __future__ import annotations
import argparse
import json
import os
import re
import sys
import datetime as _dt

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------
LEAN_EXT = ".lean"
SKIP_DIRS = {".git", ".lake", "lake-packages", ".cache", "build", "node_modules",
             ".venv", "venv", "__pycache__", "aristotle", "ACM Old", ".rambam"}
PROOFS_TSV = "proofs.tsv"
QUEUE_MD = "human-needed.md"
TSV_HEADER = ["timestamp", "commit", "target", "prover",
              "before", "after", "delta", "status", "note"]

# Obligation tokens. proof_wanted is Compfiles' marker for an unformalized
# problem statement (declared but unproved); sorry/admit are in-proof holes.
TOKENS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "proof_wanted": re.compile(r"\bproof_wanted\b"),
}


# ---------------------------------------------------------------------------
# Comment / string stripping (Lean 4 aware: block comments NEST)
# ---------------------------------------------------------------------------
def strip_noncode(src: str) -> str:
    """Replace Lean comments and string literals with spaces of equal-ish length
    so token matching never fires inside a comment or a "sorry" string literal.
    Handles nested /- -/ block comments, -- line comments, and "..." strings
    with backslash escapes. Newlines are preserved so line numbers are stable."""
    out = []
    i, n = 0, len(src)
    depth = 0          # block-comment nesting depth
    in_line = False    # inside a -- line comment
    in_str = False     # inside a "..." string
    while i < n:
        c = src[i]
        two = src[i:i + 2]
        if in_line:
            if c == "\n":
                in_line = False
                out.append(c)
            else:
                out.append(" ")
            i += 1
            continue
        if depth > 0:
            if two == "/-":
                depth += 1
                out.append("  ")
                i += 2
                continue
            if two == "-/":
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if in_str:
            if c == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
                continue
            if c == '"':
                in_str = False
                out.append(" ")
                i += 1
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        # normal code
        if two == "/-":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if two == "--":
            in_line = True
            out.append("  ")
            i += 2
            continue
        if c == '"':
            in_str = True
            out.append(" ")
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def count_text(src: str) -> dict:
    code = strip_noncode(src)
    counts = {k: len(rx.findall(code)) for k, rx in TOKENS.items()}
    counts["total"] = sum(counts.values())
    return counts


def count_file(path: str) -> dict:
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            return count_text(f.read())
    except (OSError, UnicodeError) as e:
        return {"sorry": 0, "admit": 0, "proof_wanted": 0, "total": 0,
                "error": str(e)}


# ---------------------------------------------------------------------------
# Repo walk
# ---------------------------------------------------------------------------
def iter_lean_files(root: str):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for fn in filenames:
            if fn.endswith(LEAN_EXT):
                yield os.path.join(dirpath, fn)


def has_notes(path: str, root: str) -> bool:
    """Rambam surfaces English notes from imo_solutions/<Stem>.md matching a
    theorem file's stem. Detect a sibling note anywhere under root/imo_solutions."""
    stem = os.path.splitext(os.path.basename(path))[0]
    notes_dir = os.path.join(root, "imo_solutions")
    if not os.path.isdir(notes_dir):
        return False
    return os.path.isfile(os.path.join(notes_dir, stem + ".md"))


def scan_repo(root: str) -> list[dict]:
    rows = []
    for p in iter_lean_files(root):
        c = count_file(p)
        if c["total"] > 0:
            rows.append({
                "path": os.path.relpath(p, root),
                "notes": has_notes(p, root),
                **{k: c[k] for k in ("sorry", "admit", "proof_wanted", "total")},
            })
    return rows


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------
def cmd_count(args):
    paths = args.paths or ["."]
    files = []
    for p in paths:
        if os.path.isdir(p):
            files.extend(iter_lean_files(p))
        else:
            files.append(p)
    agg = {"sorry": 0, "admit": 0, "proof_wanted": 0, "total": 0}
    per_file = []
    for f in files:
        c = count_file(f)
        per_file.append({"path": f, **{k: c[k] for k in agg}})
        for k in agg:
            agg[k] += c[k]
    if args.json:
        print(json.dumps({"total": agg["total"], "by_token": agg,
                          "files": per_file}, indent=2))
    else:
        for pf in per_file:
            print(f"{pf['total']:>4}  {pf['path']}")
        print(f"---- {agg['total']} obligations "
              f"(sorry={agg['sorry']} admit={agg['admit']} "
              f"proof_wanted={agg['proof_wanted']})")
    return 0


def cmd_targets(args):
    root = args.root
    rows = scan_repo(root)
    # cheapest first; among ties, files WITH English notes rank first
    rows.sort(key=lambda r: (r["total"], not r["notes"], r["path"]))
    if args.with_notes:
        rows = [r for r in rows if r["notes"]]
    if args.limit:
        rows = rows[: args.limit]
    if args.json:
        print(json.dumps(rows, indent=2))
    else:
        if not rows:
            print("No open obligations found under", root)
            return 0
        print(f"{'OBL':>4}  {'NOTES':<5}  FILE")
        for r in rows:
            print(f"{r['total']:>4}  {'yes' if r['notes'] else '  -':<5}  "
                  f"{r['path']}")
    return 0


def _tsv_path(root):
    return os.path.join(root, PROOFS_TSV)


def cmd_log(args):
    path = _tsv_path(args.root)
    new = not os.path.exists(path)
    delta = args.after - args.before
    row = [
        _dt.datetime.now().isoformat(timespec="seconds"),
        args.commit or "-",
        args.target,
        args.prover,
        str(args.before),
        str(args.after),
        f"{delta:+d}",
        args.status,
        (args.note or "").replace("\t", " ").replace("\n", " "),
    ]
    with open(path, "a", encoding="utf-8") as f:
        if new:
            f.write("\t".join(TSV_HEADER) + "\n")
        f.write("\t".join(row) + "\n")
    print(f"logged: {args.status} {args.target} ({args.before}->{args.after}, "
          f"{delta:+d}) via {args.prover}")
    return 0


def _queue_path(root):
    return os.path.join(root, QUEUE_MD)


def cmd_queue(args):
    path = _queue_path(args.root)
    if args.queue_cmd == "add":
        new = not os.path.exists(path)
        ts = _dt.datetime.now().isoformat(timespec="seconds")
        line = (f"- [ ] `{args.decl}` in `{args.target}` — {args.reason} "
                f"_(queued {ts})_\n")
        with open(path, "a", encoding="utf-8") as f:
            if new:
                f.write("# Human-needed obligations\n\n"
                        "The loop parks declarations here when the provers have "
                        "no idea. These are where the *mathematics* lives — drop a "
                        "Kaplansky-style scaffold comment next to the decl and the "
                        "next overnight run will pick it up.\n\n")
            f.write(line)
        print(f"queued: {args.decl} ({args.target})")
        return 0
    if args.queue_cmd == "list":
        if not os.path.exists(path):
            print("[]" if args.json else "(queue empty)")
            return 0
        items = []
        with open(path, encoding="utf-8") as f:
            for ln in f:
                m = re.match(r"- \[( |x)\] `([^`]+)` in `([^`]+)` — (.*)", ln)
                if m:
                    items.append({"done": m.group(1) == "x",
                                  "decl": m.group(2), "target": m.group(3),
                                  "reason": m.group(4)})
        open_items = [i for i in items if not i["done"]]
        if args.json:
            print(json.dumps(open_items, indent=2))
        else:
            if not open_items:
                print("(no open human-needed items)")
            for i in open_items:
                print(f"  [ ] {i['decl']}  ({i['target']})  — {i['reason']}")
        return 0
    if args.queue_cmd == "done":
        if not os.path.exists(path):
            print("queue file does not exist", file=sys.stderr)
            return 1
        with open(path, encoding="utf-8") as f:
            txt = f.read()
        new_txt = re.sub(
            r"- \[ \] (`" + re.escape(args.decl) + r"`.*)",
            r"- [x] \1", txt)
        with open(path, "w", encoding="utf-8") as f:
            f.write(new_txt)
        print(f"marked done: {args.decl}")
        return 0
    return 1


def cmd_status(args):
    root = args.root
    rows = scan_repo(root)
    rows.sort(key=lambda r: (r["total"], not r["notes"], r["path"]))
    total = sum(r["total"] for r in rows)
    with_notes = sum(1 for r in rows if r["notes"])
    print(f"repo: {os.path.abspath(root)}")
    print(f"open obligations: {total} across {len(rows)} files "
          f"({with_notes} files have English notes)")
    print("cheapest targets:")
    for r in rows[:8]:
        print(f"  {r['total']:>3}  {'notes' if r['notes'] else '     '}  "
              f"{r['path']}")
    qp = _queue_path(root)
    if os.path.exists(qp):
        with open(qp, encoding="utf-8") as f:
            n_open = sum(1 for ln in f if ln.startswith("- [ ]"))
        print(f"human-needed queue: {n_open} open")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def build_parser():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    c = sub.add_parser("count", help="count obligations in file(s) or a dir")
    c.add_argument("paths", nargs="*")
    c.add_argument("--json", action="store_true")
    c.set_defaults(func=cmd_count)

    t = sub.add_parser("targets", help="rank target files cheapest-first")
    t.add_argument("--root", default=".")
    t.add_argument("--with-notes", action="store_true",
                   help="only files that have an imo_solutions note")
    t.add_argument("--limit", type=int, default=0)
    t.add_argument("--json", action="store_true")
    t.set_defaults(func=cmd_targets)

    g = sub.add_parser("log", help="append a row to proofs.tsv")
    g.add_argument("--root", default=".")
    g.add_argument("--target", required=True)
    g.add_argument("--prover", required=True,
                   help="aristotle | mistral | claude | combined")
    g.add_argument("--before", type=int, required=True)
    g.add_argument("--after", type=int, required=True)
    g.add_argument("--status", required=True,
                   choices=["keep", "revert", "crash", "human"])
    g.add_argument("--commit", default=None)
    g.add_argument("--note", default=None)
    g.set_defaults(func=cmd_log)

    q = sub.add_parser("queue", help="manage the human-needed queue")
    q.add_argument("--root", default=".")
    qsub = q.add_subparsers(dest="queue_cmd", required=True)
    qa = qsub.add_parser("add")
    qa.add_argument("--target", required=True)
    qa.add_argument("--decl", required=True)
    qa.add_argument("--reason", required=True)
    ql = qsub.add_parser("list")
    ql.add_argument("--json", action="store_true")
    qd = qsub.add_parser("done")
    qd.add_argument("--decl", required=True)
    q.set_defaults(func=cmd_queue)

    s = sub.add_parser("status", help="one-glance repo + queue summary")
    s.add_argument("--root", default=".")
    s.set_defaults(func=cmd_status)
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
