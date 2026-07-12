# Provenance bundle — AI-assisted formalization of integer interval bound propagation

This directory is the **experimental record** for the machine-checked proofs of *soundness* and
*optimality* of the floored-division interval propagator (`z <> 0 /\ x = y / z` over integer
intervals), produced with Claude (Claude Code / Opus) driving the Rocq/Coq proof assistant.

It is meant as a reproducibility + methodology artifact for a paper on **autoformalization of
integer interval bound propagation**. It keeps not only the final proofs but the *process*: the
independent proof attempts, the conjecture-validation checks (including the ones that **failed**
and reshaped the decomposition), the abandoned first approach, and the multi-agent orchestration
scripts and logs.

All proofs were checked with **The Rocq Prover, version 9.1.1** (Coq 9 / Stdlib).

## What was proved

| Theorem | File | Meaning | `Print Assumptions` |
|---|---|---|---|
| `fdiv_propagator_sound` | `final/fdiv.v` | the propagator over-approximates (loses no solution) | Closed under the global context |
| `propagator_optimal` | `final/optimal.v` | `feasible s -> forall t, contains_sols s t -> sle (propagator s) t` — the output is contained in *every* store that contains the solutions, i.e. it is the **best abstract transformer** α∘f∘γ | Closed under the global context |

"Closed under the global context" = **no `admit`, no `Admitted`, no injected `Axiom`**: the proofs
rely only on the definitions in `fdiv.v` and the Rocq standard library. Because the propagator is
sound and reductive, optimality makes it a **closure operator**, so idempotence is a corollary.

See `final/ASSUMPTIONS.txt` for the captured audit output (also covers the two leaf lemmas
`branch_attain` and `y_attain`), and `METRICS.md` for the quantitative report.

## Directory map

```
final/                    the deliverable — 4 files, admit-free, axiom-free
  fdiv.v                  definitions + SOUNDNESS (fdiv_propagator_sound)
  optbase.v               order (ile/sle), Cx, corner attainment, discrete IVT (div_1d),
                          Ylo/Yhi attainment, fden z-optimality (fden_opt)
  optbase2.v              reductivity chain -> propagator_reductive
  optimal.v               branch_attain, branch_opt, BLU_branch, y_attain, propagator_optimal
  _CoqProject             -R . LalaInterval  +  the 4 files in dependency order
  ASSUMPTIONS.txt         captured `Print Assumptions` for the 4 key results

attempts/                 raw outputs of INDEPENDENT proof agents (best-of-N proof search)
  branch_attain/          ba_a, ba_b, ba_c        (3 independent proofs; all compiled; ba_b kept)
  y_attain/               yfin_{mono,free,fdenopt,casesplit} (round 2, 3/4 succeeded; mono kept)
                          ya_a, ya_b, ya_scratch, explore_y (round 1, partial: isolated the crux)
  fden_opt/               fdenopt_{pos,neg}_{a,b} (z-table optimality; integrated into optbase.v)

grid-checks/              CONJECTURE-BEFORE-PROOF: vm_compute over a finite grid of small intervals
  opt.v, opt4.v           optimality holds on the grid (and infeasibility is detected)
  bluchk.v                BLU_grid: the branch "band" conditions hold (the y_attain crux)
  yopt.v                  y1d_grid: a z-corner divides each output y-bound into the x-interval
  branchopt.v, branchopt3.v, fdenopt.v   branch/fden attainment checks
  failed/                 checks that FAILED and reshaped the proof:
    branchopt2.v, branchopt4.v   x-bound is NOT always a box corner -> motivated the
                                 discrete 1-D IVT lemma `div_1d`

abandoned-idempotency/    the FIRST approach (prove idempotence directly) that got stuck in a
                          case explosion; kept as a dead-end record.
  idem.v                  still carries 2 admits (Jexp_x / Jexp_z — the combinatorial crux)
  zbase, zrec_*, zrows_*, row_*, nrow_*, diag_*, probe_*, nsearch, dev, ...  (grind attempts)

workflow-logs/            the multi-agent ORCHESTRATION record
  scripts/                the 6 Workflow scripts actually run (the reproducible recipe)
  transcripts/wf_*/       journal.jsonl per workflow (each agent's return value + timing/keys)
```

## How to re-verify the final proofs

`final/` is a self-contained copy. With a Rocq 9.1 environment that exposes the standard library
(e.g. the project's opam/dune setup), from inside `final/`:

```sh
coq_makefile -f _CoqProject -o Makefile && make      # or: dune build
# then, to reproduce the trust audit:
echo 'From LalaInterval Require Import optimal. Print Assumptions propagator_optimal.' | coqtop -R . LalaInterval
```

(The bare `coqc -R . LalaInterval` invocation needs the Stdlib logical path bound, which the
project's build environment provides; these files were checked through that environment.)

## Caveats for archival

- The proof files (`optbase.v`, `optbase2.v`, `optimal.v`) were **untracked** in the source repo
  and absent from the repo's `_CoqProject` at capture time — they live here and should be committed.
- `workflow-logs/transcripts/` contains the compact `journal.jsonl` per workflow. The **full**
  per-agent conversation transcripts (~14 MB total) were left in `~/.claude/.../subagents/workflows/`
  and are **ephemeral** (subject to session GC/compaction). Copy them out if you need them.
- File provenance/timestamps come from the working tree; the authoritative per-agent record
  (prompts, returns, timing) is in the `journal.jsonl` files.
