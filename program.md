# program.md — Compfiles autoprove loop

This is the agent constitution for an **autonomous overnight Lean-proving loop** over
[Compfiles](https://github.com/dwrensha/compfiles). It is the proving analog of Karpathy's
`autoresearch` (research-acm): a fixed-discipline loop where the agent picks an open proof
obligation, throws the provers at it, and **keeps the change iff Lean verifies a strict
reduction in open obligations — otherwise reverts via git.** You run it by pointing a coding
agent (Claude Code) at this file and letting it go.

The engine is **Rambam** (`rambam ...`), your Claude + Aristotle + Mistral pipeline.
The bookkeeping is **`autoprove.py`** (the metric, target selection, logging, human queue).
This file is the *only* thing the agent needs to read to run the loop.

---

## Prime directive

**The Lean kernel is the only judge.** A change counts as progress **only** when:
1. `rambam verify <file>` (or `lake build` of the target) succeeds, **and**
2. the open-obligation metric **strictly decreases** (`autoprove.py count <file>`), **and**
3. no new `sorry` / `admit` / `axiom` / `native_decide`-style hole was introduced, **and**
4. the theorem **statement was not weakened** (signatures, hypotheses, and `proof_wanted`
   targets are immutable — you fill proofs, you do not edit what is being proved).

Gaming the metric is the only real failure mode of a formal loop. Deleting an obligation,
weakening a statement, or `sorry`-ing something out to lower the count is a **hard violation**.
When in doubt, revert.

---

## Monorepo / branch discipline

- Compfiles may live inside a larger workspace (`~/Desktop/Lean/`). **Stage only the paths you
  changed.** Never `git add -A`.
- Each run lives on its own branch: `autoprove/<tag>` (e.g. `autoprove/jun5`). The branch must
  not already exist — this is a fresh run. Create it from the current tip of `main`/`master`.
- The branch advances by one commit per *kept* obligation. Reverts are `git reset --hard` back
  to the last green commit; the discarded hash is still recorded in `proofs.tsv`.

---

## Setup (do once, with the human, before the loop)

1. **Agree a run tag** with the user (propose today's date, e.g. `jun5`). Create the branch:
   `git checkout -b autoprove/<tag>`.
2. **Confirm the engine is live:** `rambam --version`; check `ANTHROPIC_API_KEY`,
   `ARISTOTLE_API_KEY`, `MISTRAL_API_KEY` are set. Confirm `rambam.toml` is present in the
   Compfiles root (model overrides).
3. **Establish a clean baseline build:** `rambam -p . verify` (or `lake build`). If the
   repo does not build *before* you start, stop and tell the human — never start a loop on a
   red baseline.
4. **Establish the baseline metric:** `python3 autoprove.py status --root .`. This is your
   starting obligation count. Cross-check against `rambam -p . preflight` (authoritative
   obligation discovery). Initialize `proofs.tsv` by logging the baseline if it doesn't exist.
5. **Confirm and go.** After this point, do not ask the human whether to continue (see NEVER
   STOP).

---

## The metric

- **Primary:** `rambam preflight` is the authoritative list of open obligations.
- **Scriptable cross-check + per-file metric:** `autoprove.py count <file> --json` →
  `total` (sum of `sorry` + `admit` + `proof_wanted`). Lower is better. Comment- and
  string-safe, nested-block-comment aware.
- A kept commit must reduce `total` on the target file with the file still building. The repo
  total is the headline number the human watches.

---

## The loop

```
LOOP FOREVER:
  1. SELECT a target.
     python3 autoprove.py targets --root . --limit 5
     Take the cheapest file (fewest obligations). Prefer files with NOTES=yes
     (Rambam surfaces the matching imo_solutions/<Stem>.md English solution to the
     prover). Record before = autoprove.py count <target>.

  2. PLAN. rambam -p . preflight, then for ONE obligation in the target:
     - If the file has an English note, the prover already gets it. If not, and you (the
       agent) can see the intended argument, drop a 3-6 line scaffold comment ABOVE the decl
       stating the mathematical strategy (do NOT write the Lean proof yet — give the prover
       the idea, not the syntax).

  3. GENERATE — run the two provers in PARALLEL (documented Rambam pattern):
     - rambam -p . run-once --file <target>      # Claude plans -> submits to Aristotle
     - rambam -p . mistral-prove <target> --theorem <decl> -o <decl>.mistral.lean
     Aristotle is async: it returns a project_id. Do NOT block your context waiting.
     Note the id and move on to bookkeeping; poll later with `rambam -p . poll <id>`
     or `rambam -p . jobs`.

  4. INTEGRATE the first prover that returns a candidate:
     rambam -p . integrate <result>.lean --into <target>

  5. VERIFY — the kernel decides:
     rambam -p . verify <target>
     after = python3 autoprove.py count <target>

  6. SELECT (keep or revert):
     KEEP iff verify passed AND after < before AND no new holes AND statement unchanged:
        git add <target> && git commit -m "autoprove: close <decl> in <target> (<before>-><after>)"
        python3 autoprove.py log --target <target> --prover <which> \
            --before <before> --after <after> --status keep --commit $(git rev-parse --short HEAD) \
            --note "<one line>"
     ELSE:
        git reset --hard <last-green>
        python3 autoprove.py log --target <target> --prover <which> \
            --before <before> --after <after> --status revert --note "<why>"

  7. STUCK HANDLING:
     - If neither prover closes it, DECOMPOSE: rambam -p . split <target> --theorem <decl>
       then loop back over the generated sub-lemmas (they are cheaper obligations).
     - If still stuck after ~3-4 distinct attempts (different scaffolds / splits), PARK it:
        python3 autoprove.py queue add --target <target> --decl <decl> \
            --reason "<what's missing mathematically>"
        python3 autoprove.py log --target <target> --prover combined \
            --before <before> --after <before> --status human --note "parked: <reason>"
       Then move to the NEXT obligation. Parking is normal and good — it routes the few
       genuinely-hard steps to the human.
```

---

## What you CAN do
- Edit proof bodies, add helper lemmas, add imports, restructure tactic blocks, call `split`.
- Add scaffold **comments** describing intended mathematics above an obligation.
- Reorder which obligation you attack; rewind sparingly if a branch gets wedged.

## What you CANNOT do
- Change theorem **statements**, hypotheses, or `proof_wanted` targets to make them provable.
- Introduce `sorry`, `admit`, `axiom`, or decision-procedure escape hatches to fake closure.
- Delete obligations/files to lower the count.
- Block your context on a long Aristotle job — submit, record the id, keep moving, poll later.
- `git add -A` (the repo may be a monorepo; stage only your target paths).

---

## Crashes, timeouts, async jobs
- Build error after integrate → it's a bad candidate: `git reset --hard`, log `revert`, move on.
- Aristotle job exceeds your patience → leave it; `rambam -p . jobs` + `poll <id>` later.
  Treat an unfinished job as "no candidate yet," not a failure.
- Tooling/auth error (missing key, network) → stop and tell the human; do not thrash.

---

## NEVER STOP

Once the loop has begun, do **not** pause to ask "should I keep going?" The human may be
asleep and expects to wake up to a longer `proofs.tsv` and a triaged `human-needed.md`. If you
run out of cheap targets, attack the next-cheapest; if you run out of ideas on a decl, split
it; if a split stalls, park it and move on. The loop ends only when the human interrupts you,
or when `autoprove.py status` shows zero open obligations (in which case: stop, summarize the
run, and celebrate).

## Morning handoff (what the human reads)
- `proofs.tsv` — every attempt, what closed, what reverted, what was parked.
- `human-needed.md` — the short queue of obligations that need a real mathematical idea. This
  is Elan's worklist: drop a Kaplansky-style argument into a scaffold comment by the decl, and
  the next overnight run picks it up.
