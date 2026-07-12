export const meta = {
  name: 'prove-zneg-rows',
  description: 'Prove the 13 fden z-recovery row lemmas for the NEGATIVE-z branch in parallel',
  phases: [{ title: 'Prove neg rows' }],
}

const PREFIX =
  "forall ix1 iy iz0 iz ix2 iy2, hi iz0 < 0 -> ile ix1 (Cx iy iz0) -> " +
  "iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> " +
  "lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> "
const M0F = "((lo ix2 <=? 0) && (0 <=? hi ix2) && (lo iy2 <=? 0) && (0 <=? hi iy2))%bool = false"

const rows = [
  { name: 'nrow_2a', lemma: 'zneg_2a', tag: 'P1 x P (x>0,y>0) under z<0',
    guards: "0 < lo ix2 -> 0 <= lo iy2 -> 0 < hi iy2",
    concl: "Z.max 1 (lo iy2) / (hi ix2 + 1) + 1 <= lo iz /\\ hi iz <= hi iy2 / lo ix2" },
  { name: 'nrow_2b', lemma: 'zneg_2b', tag: 'P1 x N (x>0,y<0) under z<0',
    guards: "0 < lo ix2 -> hi iy2 < 0 -> lo iy2 <= 0",
    concl: "cdiv (lo iy2) (lo ix2) <= lo iz /\\ hi iz <= cdiv (Z.min (-1) (hi iy2)) (hi ix2 + 1) - 1" },
  { name: 'nrow_2c', lemma: 'zneg_2c', tag: 'P1 x M/Z under z<0',
    guards: "0 < lo ix2 -> ((0 <=? lo iy2) && (0 <? hi iy2))%bool = false -> ((hi iy2 <? 0) && (lo iy2 <=? 0))%bool = false",
    concl: "cdiv (lo iy2) (lo ix2) <= lo iz /\\ hi iz <= hi iy2 / lo ix2" },
  { name: 'nrow_3a', lemma: 'zneg_3a', tag: "N'1 x P (x<-1,y>0) under z<0",
    guards: "lo ix2 <= 0 -> hi ix2 < -1 -> 0 <= lo iy2 -> 0 < hi iy2",
    concl: "hi iy2 / (hi ix2 + 1) + 1 <= lo iz /\\ hi iz <= lo iy2 / lo ix2" },
  { name: 'nrow_3b', lemma: 'zneg_3b', tag: "N'1 x N (x<-1,y<0) under z<0",
    guards: "lo ix2 <= 0 -> hi ix2 < -1 -> lo iy2 < 0 -> hi iy2 <= 0",
    concl: "cdiv (hi iy2) (lo ix2) <= lo iz /\\ hi iz <= cdiv (lo iy2) (hi ix2 + 1) - 1" },
  { name: 'nrow_3c', lemma: 'zneg_3c', tag: "N'1 x M/Z under z<0",
    guards: "lo ix2 <= 0 -> hi ix2 < -1 -> ((0 <=? lo iy2) && (0 <? hi iy2))%bool = false -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false",
    concl: "hi iy2 / (hi ix2 + 1) + 1 <= lo iz /\\ hi iz <= cdiv (lo iy2) (hi ix2 + 1) - 1" },
  { name: 'nrow_4a', lemma: 'zneg_4a', tag: 'Z (x=[0,0]), y<0 under z<0',
    guards: `${M0F} -> lo ix2 = 0 -> hi ix2 = 0 -> hi iy2 < 0`,
    concl: "hi iz <= hi iy2 - 1" },
  { name: 'nrow_4b', lemma: 'zneg_4b', tag: 'Z (x=[0,0]), y>=0 under z<0 (likely vacuous)',
    guards: `${M0F} -> lo ix2 = 0 -> hi ix2 = 0 -> 0 <= hi iy2`,
    concl: "lo iy2 + 1 <= lo iz" },
  { name: 'nrow_5a', lemma: 'zneg_5a', tag: "N'0O (x=[a,-1]) x N under z<0",
    guards: "lo ix2 <= -1 -> hi ix2 = -1 -> lo iy2 < 0 -> hi iy2 <= 0",
    concl: "cdiv (Z.min (-1) (hi iy2)) (lo ix2) <= lo iz" },
  { name: 'nrow_5b', lemma: 'zneg_5b', tag: "N'0O (x=[a,-1]) x P under z<0",
    guards: "lo ix2 <= -1 -> hi ix2 = -1 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> 0 < hi iy2 -> 0 <= lo iy2",
    concl: "hi iz <= Z.max 1 (lo iy2) / lo ix2" },
  { name: 'nrow_5c', lemma: 'zneg_5c', tag: "N'0O x Z (y=[0,0]) under z<0 : CONTRADICTORY, derive False",
    guards: "lo ix2 <= -1 -> hi ix2 = -1 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> ((0 <? hi iy2) && (0 <=? lo iy2))%bool = false -> lo iy2 = 0 -> hi iy2 = 0",
    concl: "1 <= lo iz /\\ hi iz <= 0" },
  { name: 'nrow_6a', lemma: 'zneg_6a', tag: 'P0 (x=[0,b]) x N under z<0',
    guards: `${M0F} -> lo ix2 = 0 -> 0 < hi ix2 -> lo iy2 < 0 -> hi iy2 <= 0`,
    concl: "hi iz <= cdiv (Z.min (-1) (hi iy2)) (hi ix2 + 1) - 1" },
  { name: 'nrow_6b', lemma: 'zneg_6b', tag: 'P0 (x=[0,b]) x P under z<0 (likely vacuous)',
    guards: `${M0F} -> lo ix2 = 0 -> 0 < hi ix2 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> 0 < hi iy2 -> 0 <= lo iy2`,
    concl: "Z.max 1 (lo iy2) / (hi ix2 + 1) + 1 <= lo iz" },
]

const SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    name: { type: 'string' }, compiled: { type: 'boolean' },
    aux: { type: 'string' }, proof: { type: 'string' }, notes: { type: 'string' },
  },
  required: ['name', 'compiled', 'proof'],
}

phase('Prove neg rows')
const results = await parallel(rows.map(r => () => {
  const stmt = `Lemma ${r.lemma} : ${PREFIX}${r.guards} ->\n  ${r.concl}.`
  const prompt =
`Read the brief at /tmp/claude-1000/-home-ptalbot-repositories-lattice-land-lala-core/47acb528-3937-49c8-b403-258bc9817989/scratchpad/zpos_brief.md FIRST (Read tool).

IMPORTANT DIFFERENCE FROM THE BRIEF: this is the NEGATIVE-z branch. The base hypothesis is
"hi iz0 < 0" (NOT 0 < lo iz0). Consequently zsetup gives Hizpos-analog as a NEGATIVE fact:
after zsetup you will have hypotheses including that lo iz / hi iz are < 0 territory. Precisely,
derive "hi iz < 0" yourself early: "assert (Hizneg : hi iz < 0) by (rewrite Eizhi; lia)."
(Eizhi : hi iz = Z.min (hi iz0) (hi (fden ix1 iy iz0)), and hi iz0 < 0.) Also note lo iz <= hi iz < 0.
The pass-1 helpers fden_ub_mul_pos / fden_lb_mul_pos / fden_loiy_pos in the brief are for
POSITIVE x-intervals and are z-sign-agnostic in their statement but their hypotheses (0<lo ix)
may or may not apply. For negative-z rows you will typically need NEGATIVE-divisor reasoning:
prove auxiliary pass-1 fden helpers (model on fden_ub_mul_pos's proof shape) using the fdiv
lemmas cdiv_ub/cdiv_lb/cdiv_ub_neg/cdiv_lb_neg/fdiv_ub_neg/fdiv_lb_neg/fdiv_lt_neg/div_le_mono_num_neg
(all listed in the brief). Several of these rows are VACUOUS under z<0 (the guards are
inconsistent with hi iz<0 and the tightness/nonemptiness) — prove those by deriving a
contradiction (exfalso), exactly as the brief describes for contradiction rows. Row ${r.tag}.

Prove this ONE Rocq lemma. Create /home/ptalbot/repositories/lattice-land/lala-interval/rocq/${r.name}.v with header:
From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
then (optional) auxiliary lemmas, then:
${stmt}
Proof.
  (* your proof; start: intros ix1 iy iz0 iz ix2 iy2 Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2 <guards>. zsetup Hz0 Ht Diz Dx2 Dy2 Nz Nx2 Ny2. *)
Qed.

Develop with the rocq MCP tools (ToolSearch select:mcp__rocq-mcp__rocq_start,mcp__rocq-mcp__rocq_check,mcp__rocq-mcp__rocq_step_multi,mcp__rocq-mcp__rocq_compile_file),
VERIFY with rocq_compile_file(file="${r.name}.v", workspace="/home/ptalbot/repositories/lattice-land/lala-interval/rocq")
returning success:true, NO admit/Admitted. The statement is GRID-VALIDATED true, so persist.
Remember the lia/nia TIMEOUT caution: clear heavy hyps (Diz Eizlo Eizhi He1 He2 Ht Htp Htq Eix2lo Eix2hi Eiy2lo Eiy2hi)
before nia; prove div-corner facts with explicit Z.le_min_l/r, Z.le_max_l/r, Z.le_trans.

Return: name="${r.lemma}", compiled, aux (verbatim aux lemmas or ""), proof (tactics between Proof. and Qed.), notes.`
  return agent(prompt, { label: r.name, phase: 'Prove neg rows', schema: SCHEMA, effort: 'high' })
    .then(res => ({ ...res, lemma: r.lemma }))
}))

const ok = results.filter(Boolean).filter(r => r.compiled)
const bad = results.filter(Boolean).filter(r => !r.compiled)
log(`compiled ${ok.length}/${rows.length}; failed: ${bad.map(b=>b.lemma).join(', ') || 'none'}`)
return { results }
