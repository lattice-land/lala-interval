export const meta = {
  name: 'prove-y-attain',
  description: 'Prove y_attain (fden y-completeness crux) admit-free for the floor-div propagator',
  phases: [
    { title: 'Prove', detail: 'best-of-4 diverse provers, each writes+compiles a standalone y_attain file' },
    { title: 'Verify', detail: 'adversarially confirm each compiled candidate is admit-free & statement-correct' },
  ],
}

const DIR = '/home/ptalbot/repositories/lattice-land/lala-interval/rocq'

const BRIEF = `
# TASK: prove \`y_attain\` ADMIT-FREE, in a standalone Rocq file (Coq 9 / Stdlib).

Workspace: ${DIR}  (a _CoqProject maps logical name \`LalaInterval\` to this dir; .vo files for
fdiv, optbase, optbase2 are BUILT). Interactive Rocq MCP tools are available (rocq_start,
rocq_check, rocq_step_multi, rocq_compile_file, rocq_query, ...). Use them heavily.

## Hard constraints
- File header EXACTLY these imports (and ONLY these library imports):
  \`\`\`
  From LalaInterval Require Import fdiv.
  From LalaInterval Require Import optbase.
  From LalaInterval Require Import optbase2.
  From Stdlib Require Import ZArith Lia.
  Open Scope Z_scope.
  \`\`\`
- FORBIDDEN: \`Require\`-ing \`idem\` or \`optdev\` (they contain the very lemma admitted; importing
  them would be circular). Do NOT use \`allstores\`, \`vm_compute\`, or any reflection/grid tactic to
  "prove" y_attain — it must be a genuine forall-s proof.
- No \`Admitted\`, \`admit\`, \`Abort\`, \`Axiom\`, \`Parameter\`, \`Conjecture\` anywhere in the final file.
- The lemma MUST have EXACTLY this statement and name:
  \`\`\`
  Lemma y_attain : forall s, consistent (propagator s) ->
    (exists x z, in_store s x (lo (sy (propagator s))) z /\\ sol x (lo (sy (propagator s))) z) /\\
    (exists x z, in_store s x (hi (sy (propagator s))) z /\\ sol x (hi (sy (propagator s))) z).
  \`\`\`
- FINAL STEP: run \`rocq_compile_file\` on your file and confirm \`success:true\`. Only report success
  if it compiled clean. Return the COMPLETE file contents in your \`file\` field.

## Definitions (all in fdiv.v / optbase / optbase2 — READ them, do not re-Require idem/optdev)
- \`consistent p := lo(sx p)<=hi(sx p) /\\ lo(sy p)<=hi(sy p) /\\ lo(sz p)<=hi(sz p)\`  (optbase)
- \`in_store s a b c := mem(sx s)a /\\ mem(sy s)b /\\ mem(sz s)c\`; \`mem i v := lo i<=v<=hi i\`;
  \`sol x y z := z<>0 /\\ x = Z.div y z\`  (fdiv)
- \`propagator s = refine_y (sqcupbot (fdivxz_neg (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)))\`
  \`refine_y u = St (sx u) (inter (sy u) (Itv (Ylo (lo(sx u))(hi(sx u))(lo(sz u))(hi(sz u)))
                                              (Yhi (lo(sx u))(hi(sx u))(lo(sz u))(hi(sz u))))) (sz u)\`
  \`restrict_z_pos s\` keeps sx,sy, sets sz := sz s ∩ [1, hi]; \`restrict_z_neg\` sz := sz s ∩ [lo,-1].
  \`fdivxz_neg = fdivxz_pos\` DEFINITIONALLY (bodies identical) — prove \`forall w, fdivxz_neg w = fdivxz_pos w\`
  by \`reflexivity\`. \`fdivxz_pos s\`: ix1:=sx s ∩ Cx(sy s,sz s); iz:=sz s ∩ fden ix1 (sy s)(sz s)=sz(F s);
  ix2:=ix1 ∩ Cx(sy s,iz)=sx(F s); sy(F s)=sy s.
- \`Ylo xl xu zl zu = Z.min (Z.min (xl*zl)(xl*zu)) (Z.min ((xu+1)*zl+1)((xu+1)*zu+1))\`
  \`Yhi xl xu zl zu = Z.max (Z.max (xl*zl)(xl*zu)) (Z.max ((xu+1)*zl-1)((xu+1)*zu-1))\`  (fdiv)
- AVAILABLE proven: \`fden_opt\` (optbase; z-completeness of fden), \`fnum_sound\` (fdiv; any solution's y
  is in [Ylo,Yhi]), \`fdiv_lb_neg\`/\`fdiv_lt_neg\` (fdiv; neg-divisor bounds), \`Z.div_le_lower_bound\`,
  \`Z.div_lt_upper_bound\`, \`div_le_mono_num_neg\` (fdiv), \`ile\`/\`Cx\`/\`inter\`/\`ijoin\`,
  \`propagator_reductive : forall s, sle (propagator s) s\` (optbase2; sle a b = ile componentwise;
  ile i j = lo j<=lo i /\\ hi i<=hi j). Use propagator_reductive to place x,y,z into \`sx/sy/sz s\`.

## STRONGLY RECOMMENDED: reuse the near-complete prior work (READ these files with the Read tool)
Two prior agents produced ALMOST-complete pieces — COPY the proven lemmas verbatim (adapting imports):
- \`${DIR}/ya_a.v\`  — PROVEN admit-free: \`num_in_band_pos\`, \`num_in_band_neg\`, and the CORNER SELECTORS
  \`pick_lo\` and \`pick_hi\`:
    \`pick_lo a b zl zu Y : a<=b -> zl<=zu -> zl<>0 -> zu<>0 -> Ylo a b zl zu <= Y ->
        (0<zu -> Y<=(b+1)*zu-1) -> (0<zl -> Y<=(b+1)*zl-1) -> (zl<0 -> Y<=a*zl) -> (zu<0 -> Y<=a*zu) ->
        exists z, zl<=z<=zu /\\ z<>0 /\\ a <= Y/z <= b\`
    \`pick_hi\` symmetric with \`Y <= Yhi a b zl zu\` and the dual band side-conditions
        (0<zu -> a*zu<=Y), (0<zl -> a*zl<=Y), (zl<0 -> (b+1)*zl+1<=Y), (zu<0 -> (b+1)*zu+1<=Y).
  These two are the heart of the corner selection — copy them EXACTLY (they only need fdiv+ZArith).
- \`${DIR}/ya_b.v\` — has PROVEN \`band_pos\`,\`band_neg\`,\`corner_Ylo\`,\`corner_Yhi\`,\`prop_z_nonzero\`, and a
  COMPLETE \`y_attain\` assembly — BUT it depends on \`idem.J\`/\`idem.propagator_J\`/\`idem.J_sy\` (FORBIDDEN)
  and on an ADMITTED \`y_coverage\`. You must (a) re-derive its structural facts inline WITHOUT idem
  (see the pattern below), and (b) REPLACE the admitted \`y_coverage\` with a real proof (see CRUX).
- \`${DIR}/explore_y.v\` and \`${DIR}/bluchk.v\` — define \`BLU\` (the branch band conditions) and
  \`BLU_grid : forallb BLU allstores = true\` is PROVEN, so the band facts below ARE TRUE (grid-checked).
- \`${DIR}/optdev.v\` — READ ONLY (do NOT import). Its \`propagator_optimal\` proof shows the exact
  inline structural-rewrite pattern (EPS/ESX/ESZ) for \`propagator s = refine_y (sqcupbot (fdivxz_pos
  (restrict_z_neg s)) (fdivxz_pos (restrict_z_pos s)))\`, \`sx/sz(propagator s) = sx/sz(sqcupbot ...)\`,
  and \`sy(J s)=sy s\`. Mirror it (it uses fdivxz_neg_eq_pos + unfold refine_y + cbn).

## THE CRUX you must prove: \`BLU_branch\` (branch-level band conditions), then LIFT + ASSEMBLE
### (1) BLU_branch  [the only genuinely hard lemma; grid-validated true as BLU_grid]
\`\`\`
Lemma BLU_branch : forall w,
  (0 < lo (sz w) \\/ hi (sz w) < 0) ->
  lo (sx (fdivxz_pos w)) <= hi (sx (fdivxz_pos w)) ->
  lo (sy w) <= hi (sy w) ->
  lo (sz (fdivxz_pos w)) <= hi (sz (fdivxz_pos w)) ->
  let a := lo (sx (fdivxz_pos w)) in let b := hi (sx (fdivxz_pos w)) in
  let zl := lo (sz (fdivxz_pos w)) in let zu := hi (sz (fdivxz_pos w)) in
  let c := lo (sy w) in let d := hi (sy w) in
  (0 < zu -> a*zu <= d) /\\ (0 < zl -> a*zl <= d) /\\
  (zl < 0 -> (b+1)*zl+1 <= d) /\\ (zu < 0 -> (b+1)*zu+1 <= d) /\\
  (0 < zu -> c <= (b+1)*zu-1) /\\ (0 < zl -> c <= (b+1)*zl-1) /\\
  (zl < 0 -> c <= a*zl) /\\ (zu < 0 -> c <= a*zu).
\`\`\`
Proof idea: set ix1, iz, ix2 as in fdivxz_pos (\`unfold fdivxz_pos; cbv zeta; cbn[sx sy sz]; set ...\`).
Because the branch is sign-definite, [zl,zu]=iz all have one sign. a=lo ix2, b=hi ix2 with
ix2=ix1 ∩ Cx(sy w,iz); so a>=Xlo(c,d,zl,zu) and b<=Xhi(c,d,zl,zu) AND a<=b (nonempty hyp). Recall
Xlo/Xhi are the min/max of the 4 quotient-corners {c/zl,c/zu,(d)/zl,(d)/zu} shifted appropriately —
READ their defs in fdiv.v. Each band inequality is then a Z.div fact:
e.g. pos z: a<=Xhi ... use the NONEMPTINESS a<=b together with b<=Xhi=d/zl and a>=Xlo=c/zu to get
a<=d/zu (⇒ a*zu<=d, that's the BL1 form) and b>=c/zu (⇒ c<=(b+1)*zu-1, that's BU1) etc.
The cleanest fully-mechanical route: MIRROR \`fden_sound\`/\`fdiv_sound_pos\` in fdiv.v — i.e. do the
same fden guard case-split (\`unfold fden in *; repeat (match goal with |- context[if ?b then _ else _]
=> destruct b eqn:? end)\`) so iz's lo/hi become explicit \`Z.div\`/\`cdiv\` of the corners; then each of the
8 inequalities is discharged by \`Z.div_le_lower_bound\`/\`Z.div_lt_upper_bound\`/\`div_le_mono_num_neg\`/
\`Z.mul_div_le\`/\`cdiv\` lemmas + \`nia\`. ALTERNATIVELY derive them from \`fden_opt\` (z-corner solutions)
+ \`fnum_sound\`. Either works; pick whichever you can push through.

### (2) LIFT to the joined output corners
Let p = propagator s = refine_y (sqcupbot N P), N=fdivxz_pos(restrict_z_neg s), P=fdivxz_pos(restrict_z_pos s).
sx p = sx(sqcupbot N P), sz p = sz(sqcupbot N P), and sy p = inter (sy s) (Itv (Ylo A B ZL ZU)(Yhi A B ZL ZU))
with A=lo(sx p),B=hi(sx p),ZL=lo(sz p),ZU=hi(sz p) (since sy(sqcupbot N P)=sy s). So
lo(sy p)=Z.max(lo(sy s))(Ylo A B ZL ZU), hi(sy p)=Z.min(hi(sy s))(Yhi A B ZL ZU).
On a CONSISTENT p, at least one branch is nonempty; the NEG branch (if present) supplies the negative
corner ZL=lo(sz p) (its z<=-1) and the POS branch the positive corner ZU=hi(sz p) (z>=1); when only one
branch is active both corners come from it (same sign). Prove \`prop_z_nonzero : consistent(propagator s)
-> lo(sz p)<>0 /\\ hi(sz p)<>0\` (see ya_b.v — reprove WITHOUT idem, using the sqcupbot cases like
optdev's propagator_optimal Hone/EX/EZ). Then the joined band conditions needed by pick_lo/pick_hi
(with the joined A,B and Y=lo(sy s) resp hi(sy s)) follow from the ACTIVE branch's BLU_branch by
MONOTONICITY: e.g. positive corner ZU=hi(sz P): from P's BU1 \`c<=(hi(sx P)+1)*ZU-1\` and B=hi(sx p)>=hi(sx P),
ZU>0 ⇒ c<=(B+1)*ZU-1; negative corner ZL=lo(sz N): from N's BU3 \`c<=(lo(sx N))*ZL\` and A=lo(sx p)<=lo(sx N),
ZL<0 ⇒ c<=A*ZL. (Careful sqcupbot algebra: sx/sz of sjoin are ijoin = [min lo, max hi]; when only one
branch active, sx/sz p equal that branch's.)

### (3) ASSEMBLE y_attain
For Y = lo(sy p): lo(sy p)=max(lo(sy s),Ylo A B ZL ZU). Case-split (\`Z.max_spec\`):
  - if = Ylo: use \`corner_Ylo\` (copy from ya_b: gives a corner zc, zc<>0, A<=Ylo/zc<=B) — needs
    prop_z_nonzero + A<=B.
  - if = lo(sy s) (so Ylo<=lo(sy s)): apply \`pick_lo A B ZL ZU (lo(sy s))\` with the joined band conds
    from step (2). It returns a corner z with A<=(lo sy s)/z<=B.
For Y = hi(sy p): symmetric with \`Z.min_spec\`, \`corner_Yhi\`, \`pick_hi\`.
Given such a corner zc (zc<>0, A<=Y/zc<=B), build the witness (Y/zc, Y, zc):
  \`sol (Y/zc) Y zc\` = (zc<>0, Y/zc=Y/zc) trivially; \`in_store s (Y/zc) Y zc\`: use propagator_reductive
  (x=Y/zc∈[A,B]=sx p ⊆ sx s; Y=lo/hi(sy p)∈sy p ⊆ sy s; zc∈{ZL,ZU}=corners of sz p ⊆ sz s). See ya_b's
  \`Hcore\` for the exact plumbing (copy, dropping idem/fold p indirection).

## CAUTION
- \`lia\`/\`nia\` DIVERGE with fden/Xlo/Ylo/div atoms in context. Introduce div facts EXPLICITLY via
  \`Z.div_le_lower_bound\`,\`Z.div_lt_upper_bound\`,\`Z.mul_div_le\`,\`Z.div_mul\`,\`div_le_mono_num_neg\`,
  \`fdiv_lb_neg\`,\`fdiv_lt_neg\`,\`Z.le_min_l/r\`,\`Z.le_max_l/r\`,\`Z.min_spec\`,\`Z.max_spec\`; \`clear\` heavy
  hyps before calling \`nia\`.
- READ the actual current statements (\`rocq_query\` "Check <name>." or \`Print\`) before relying on them.
- Work incrementally in an interactive session (\`rocq_start\` then \`rocq_check\`), then write the whole
  file and \`rocq_compile_file\`.
`

phase('Prove')
const STRATS = [
  { tag: 'casesplit',
    hint: 'Prove BLU_branch by the DIRECT fden guard case-split, mirroring fden_sound / fdiv_sound_pos in fdiv.v (unfold fden; repeat destruct the if-guards; each leaf gives explicit Z.div/cdiv corners; discharge each of the 8 inequalities with explicit div lemmas + nia). This is the most reliable route — invest here.' },
  { tag: 'fdenopt',
    hint: 'Prove BLU_branch by REUSING the already-proven fden_opt (z-corner solutions) together with fnum_sound and the Cx bounds on ix2, WITHOUT reopening the fden case-split. Derive each band inequality from an attained corner solution.' },
  { tag: 'mono',
    hint: 'Prove BLU_branch via the quotient-window characterization: a=lo ix2>=Xlo(c,d,zl,zu), b=hi ix2<=Xhi(c,d,zl,zu), plus nonemptiness a<=b; convert Xlo/Xhi (min/max of the 4 corner quotients) into the 8 band inequalities by case-analysis on which corner realizes the extreme (Z.min_spec/Z.max_spec) + div lemmas.' },
  { tag: 'free',
    hint: 'Prove y_attain end-to-end in whatever decomposition you find most tractable. You may prove BLU_branch or bypass it with a different sufficient lemma, as long as the file compiles admit-free with the exact y_attain statement.' },
]

const results = await parallel(STRATS.map(st => () =>
  agent(
    `You are proving the Rocq lemma \`y_attain\` admit-free.\n\n` +
    `Write your file to \`${DIR}/yfin_${st.tag}.v\`.\n\n` +
    `STRATEGY FOR THIS ATTEMPT: ${st.hint}\n\n` +
    BRIEF,
    { label: `prove:${st.tag}`, phase: 'Prove', effort: 'high',
      schema: {
        type: 'object', additionalProperties: false,
        required: ['tag','compiled','filename','blu_branch_done','y_attain_done','notes'],
        properties: {
          tag: { type: 'string' },
          compiled: { type: 'boolean', description: 'rocq_compile_file returned success:true on the final file' },
          filename: { type: 'string' },
          blu_branch_done: { type: 'boolean' },
          y_attain_done: { type: 'boolean', description: 'y_attain proven admit-free' },
          notes: { type: 'string', description: 'what worked / what is still open / any admits left' },
          file: { type: 'string', description: 'COMPLETE final file contents' },
        },
      } })
    .then(r => ({ ...r, strat: st.tag }))
))

const ok = results.filter(Boolean).filter(r => r.compiled && r.y_attain_done)
log(`Prove phase: ${results.filter(Boolean).length}/4 returned; ${ok.length} claim compiled+admit-free y_attain`)

phase('Verify')
// Adversarially verify each claimed-good candidate by recompiling + checking admit-freeness.
const verified = await parallel(ok.map(r => () =>
  agent(
    `Adversarially VERIFY the Rocq proof of \`y_attain\` in \`${DIR}/${r.filename}\`.\n` +
    `Do ALL of:\n` +
    `1. Run rocq_compile_file on \`${DIR}/${r.filename}\`; confirm success:true.\n` +
    `2. Grep/read the file: confirm NO occurrence of Admitted, admit, Abort, Axiom, Parameter, Conjecture,\n` +
    `   and that it does NOT Require idem or optdev, and uses no vm_compute/reflection to close y_attain.\n` +
    `3. Confirm the lemma named \`y_attain\` has EXACTLY the required statement (forall s, consistent\n` +
    `   (propagator s) -> (exists x z, in_store s x (lo (sy (propagator s))) z /\\ sol ...) /\\ (... hi ...)).\n` +
    `4. Run rocq_assumptions (or 'Print Assumptions y_attain' via rocq_query) and report the axiom list;\n` +
    `   it must be closed under the global context (only fdiv/optbase library content, no new axioms).\n` +
    `Report verdict. If anything fails, set ok=false and explain precisely.`,
    { label: `verify:${r.strat}`, phase: 'Verify', effort: 'high',
      schema: {
        type: 'object', additionalProperties: false,
        required: ['ok','filename','recompiled','admit_free','statement_correct','assumptions'],
        properties: {
          ok: { type: 'boolean' },
          filename: { type: 'string' },
          recompiled: { type: 'boolean' },
          admit_free: { type: 'boolean' },
          statement_correct: { type: 'boolean' },
          assumptions: { type: 'string', description: 'the Print Assumptions output' },
          detail: { type: 'string' },
        },
      } })
    .then(v => ({ ...v, strat: r.strat }))
))

const good = verified.filter(Boolean).filter(v => v.ok)
log(`Verify phase: ${good.length}/${ok.length} candidates fully verified admit-free`)

return {
  proveResults: results.filter(Boolean).map(r => ({ strat: r.strat, compiled: r.compiled, y_attain_done: r.y_attain_done, blu_branch_done: r.blu_branch_done, filename: r.filename, notes: r.notes })),
  verified: verified.filter(Boolean),
  winners: good.map(v => v.filename),
}
