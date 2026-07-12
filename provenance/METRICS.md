# METRICS — AI-assisted formalization of the floored-division interval propagator

Prover: **The Rocq Prover 9.1.1** (Coq 9 / Stdlib). Assistant: Claude (Opus, via Claude Code),
using an interactive Rocq MCP server (`rocq_check`, `rocq_compile_file`, `rocq_assumptions`, …) and
a multi-agent **Workflow** orchestrator (parallel best-of-N sub-agents with kernel-checked verification).

## 1. Result

Two theorems, both **admit-free and axiom-free** (`Print Assumptions` = *Closed under the global context*):

- **Soundness** `fdiv_propagator_sound` — the propagator loses no solution.
- **Optimality** `propagator_optimal : forall s, feasible s -> forall t, contains_sols s t -> sle (propagator s) t`
  — the output is below every store containing the solutions: the **best abstract transformer** α∘f∘γ.
  (⇒ idempotence, since a sound + reductive best transformer is a closure operator.)

The acceptance oracle for every AI-produced proof was the Rocq kernel: *compiles* **and**
*Print Assumptions is closed*. No proof was accepted on the model's say-so.

## 2. Final artifacts (lines of Rocq)

| File | Lines | Role |
|---|---:|---|
| `fdiv.v` | 822 | definitions + soundness |
| `optbase.v` | 633 | order, corner attainment, discrete IVT, `fden_opt` |
| `optbase2.v` | 63 | reductivity → `propagator_reductive` |
| `optimal.v` | 763 | branch attainment + optimality assembly |
| **total** | **2281** | soundness + optimality |

## 3. Optimality decomposition (dependency graph)

```
propagator_optimal            (99 lines)   -- assembles the branches (join = lub) + y
├─ branch_opt                 (17)         -- attained bounds land in any sound t
│  └─ branch_attain           (127)        -- x,z output bounds are attained by real solutions
│     ├─ fden_opt  [optbase]               -- fden z-completeness (z-corner solutions exist)
│     ├─ div_1d    [optbase]               -- discrete 1-D IVT for floor(./z)
│     └─ X{lo,hi}_corner [optbase]         -- quotient extremes realised at box corners
├─ y_attain                   (46)         -- y output bounds are attained by real solutions
│  ├─ BLU_branch              (65)   <-- THE CRUX (per-branch fden "band" completeness)
│  ├─ pick_lo / pick_hi                     -- corner selection from the band conditions
│  ├─ corner_Ylo / corner_Yhi               -- extreme-case corner (no fden needed)
│  └─ propagator_reductive [optbase2]       -- places witnesses back into the input box
└─ prop_sound  [= soundness]                -- feasible input ⇒ non-empty output (unlocks attainment)
```

## 4. Multi-agent proof search — per hard lemma

Each hard lemma was delegated to a **Workflow** running independent sub-agents (diverse strategies),
each writing a standalone `.v` file and self-verifying with `rocq_compile_file`. Raw outputs in
`attempts/`.

| Lemma | Workflow(s) | Independent attempts | Compiled admit-free | Integrated | Notes |
|---|---|---:|---:|---|---|
| `fden_opt` (z-table) | `prove-zpos-rows`, `prove-zneg-rows`, `prove-fden-opt` | 4 (`fdenopt_{pos,neg}_{a,b}`) | ≥2 | into `optbase.v` | per-sign row analysis |
| `branch_attain` | `prove-branch-attain` | 3 (`ba_a/b/c`) | **3 / 3** | `ba_b` | 3 independent proofs agree ⇒ cross-validation |
| `y_attain` — round 1 | `prove-y-attain` (#1) | 4 (`ya_a/ya_b/ya_scratch/explore_y`) | 0 (partial) | — | **isolated the crux** `y_coverage`/`BLU`; proved `pick_lo/hi`, corner lemmas |
| `y_attain` — round 2 | `prove-y-attain` (#2) | 4 (`yfin_{mono,free,fdenopt,casesplit}`) | **3 / 4** | `yfin_mono` | diverse `BLU_branch` strategies; `casesplit` reached only helpers |

Independent-proof size variance (same statement, `y_attain`): 24–29 KB across the compiling
`yfin_*` files — evidence of genuinely different proof strategies converging on the same kernel-checked fact.

## 5. Conjecture-before-proof (finite-grid `vm_compute` validation)

Before investing in a proof, a lemma was first *tested* on a finite grid of small integer intervals.
This confirmed truth, pinned the exact statement, and — crucially — surfaced **counterexamples that
reshaped the decomposition**.

| Check | File | Verdict | Role |
|---|---|---|---|
| optimality on grid | `opt.v`, `opt4.v` | pass | the target is true; infeasibility detected |
| branch band conditions | `bluchk.v` (`BLU_grid`) | pass | de-risked the `y_attain` crux before proving it |
| output y-bound ⇒ corner | `yopt.v` (`y1d_grid`) | pass | validated the corner-selection idea |
| branch x,z attainment | `branchopt.v`, `branchopt3.v` | pass | validated `branch_attain` |
| fden z-optimality (tight ix) | `fdenopt.v` | pass | validated `fden_opt` shape |
| **x-bound = a box corner?** | `branchopt2.v`, `branchopt4.v` | **FAIL** | showed x-bound is *not* always a corner ⇒ **motivated the discrete IVT `div_1d`** |

## 6. Human-in-the-loop steering (the decisive interventions)

The human contribution was mainly **strategic**, not tactical:

1. *"Prove idempotency; prove the hard combination-of-cases lemmas one by one."* → first approach
   (`abandoned-idempotency/`): got stuck on a large case explosion (`idem.v` keeps admits `Jexp_x/Jexp_z`).
2. *"Prove **optimality** instead — α∘f∘γ; because it is a closure operator it also gives idempotence,
   and it should need far fewer nested cases; prove it by case analysis."* → the reformulation that
   made the proof tractable (this whole bundle).
3. *"Grind it, like for soundness."* → sanctioned the mechanical case-bashing / grid-guided style used
   throughout `optbase.v` / `optimal.v`.

## 7. Reportable methodology findings

- **Goal reformulation for tractability.** An equivalent but proof-theoretically easier target
  (optimality instead of idempotence) turned an intractable case explosion into a clean decomposition.
  The abandoned route is preserved as the counterfactual (`abandoned-idempotency/`, ~32 files).
- **Test-first formalization.** `vm_compute` grid checks acted as a cheap conjecture oracle; the
  **failed** checks were as valuable as the passing ones (they forced the discrete-IVT lemma).
- **Parallel best-of-N with a kernel oracle.** Independent agents + `rocq_compile_file` +
  `Print Assumptions` as ground truth; multiple independent admit-free proofs of one statement give
  redundancy/cross-validation, not just a single fragile witness.
- **Auditability is the acceptance criterion.** "Closed under the global context" is the objective,
  reviewer-checkable guarantee that the LLM did not smuggle in `admit`/`Axiom` — the crux of trusting
  machine-generated proofs.
