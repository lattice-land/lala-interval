export const meta = {
  name: 'prove-zpos-rows',
  description: 'Prove the 12 remaining fden z-recovery row lemmas (positive branch) in parallel',
  phases: [{ title: 'Prove rows' }],
}

const PREFIX =
  "forall ix1 iy iz0 iz ix2 iy2, 0 < lo iz0 -> ile ix1 (Cx iy iz0) -> " +
  "iz = inter iz0 (fden ix1 iy iz0) -> ix2 = inter ix1 (Cx iy iz) -> iy2 = inter iy (Cy ix2 iz) -> " +
  "lo iz <= hi iz -> lo ix2 <= hi ix2 -> lo iy2 <= hi iy2 -> "

const rows = [
  { name: 'row_2b', lemma: 'zpos_2b', tag: 'P1 x N (x>0, y<0)',
    guards: "0 < lo ix2 -> hi iy2 < 0 -> lo iy2 <= 0",
    concl: "cdiv (lo iy2) (lo ix2) <= lo iz /\\ hi iz <= cdiv (Z.min (-1) (hi iy2)) (hi ix2 + 1) - 1" },
  { name: 'row_2c', lemma: 'zpos_2c', tag: 'P1 x M/Z (x>0, y mixed)',
    guards: "0 < lo ix2 -> ((0 <=? lo iy2) && (0 <? hi iy2))%bool = false -> ((hi iy2 <? 0) && (lo iy2 <=? 0))%bool = false",
    concl: "cdiv (lo iy2) (lo ix2) <= lo iz /\\ hi iz <= hi iy2 / lo ix2" },
  { name: 'row_3a', lemma: 'zpos_3a', tag: "N'1 x P (x<-1, y>0)",
    guards: "lo ix2 <= 0 -> hi ix2 < -1 -> 0 <= lo iy2 -> 0 < hi iy2",
    concl: "hi iy2 / (hi ix2 + 1) + 1 <= lo iz /\\ hi iz <= lo iy2 / lo ix2" },
  { name: 'row_3b', lemma: 'zpos_3b', tag: "N'1 x N (x<-1, y<0)",
    guards: "lo ix2 <= 0 -> hi ix2 < -1 -> lo iy2 < 0 -> hi iy2 <= 0",
    concl: "cdiv (hi iy2) (lo ix2) <= lo iz /\\ hi iz <= cdiv (lo iy2) (hi ix2 + 1) - 1" },
  { name: 'row_3c', lemma: 'zpos_3c', tag: "N'1 x M/Z (x<-1, y mixed)",
    guards: "lo ix2 <= 0 -> hi ix2 < -1 -> ((0 <=? lo iy2) && (0 <? hi iy2))%bool = false -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false",
    concl: "hi iy2 / (hi ix2 + 1) + 1 <= lo iz /\\ hi iz <= cdiv (lo iy2) (hi ix2 + 1) - 1" },
  { name: 'row_4a', lemma: 'zpos_4a', tag: 'Z (x=[0,0]), y<0',
    guards: "lo ix2 = 0 -> hi ix2 = 0 -> hi iy2 < 0",
    concl: "hi iz <= hi iy2 - 1" },
  { name: 'row_4b', lemma: 'zpos_4b', tag: 'Z (x=[0,0]), y>=0',
    guards: "lo ix2 = 0 -> hi ix2 = 0 -> 0 <= hi iy2",
    concl: "lo iy2 + 1 <= lo iz" },
  { name: 'row_5a', lemma: 'zpos_5a', tag: "N'0O (x=[a,-1]) x N",
    guards: "lo ix2 <= -1 -> hi ix2 = -1 -> lo iy2 < 0 -> hi iy2 <= 0",
    concl: "cdiv (Z.min (-1) (hi iy2)) (lo ix2) <= lo iz" },
  { name: 'row_5b', lemma: 'zpos_5b', tag: "N'0O (x=[a,-1]) x P",
    guards: "lo ix2 <= -1 -> hi ix2 = -1 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> 0 < hi iy2 -> 0 <= lo iy2",
    concl: "hi iz <= Z.max 1 (lo iy2) / lo ix2" },
  { name: 'row_5c', lemma: 'zpos_5c', tag: "N'0O x Z (y=[0,0]) : CONTRADICTORY hyps, derive False",
    guards: "lo ix2 <= -1 -> hi ix2 = -1 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> ((0 <? hi iy2) && (0 <=? lo iy2))%bool = false -> lo iy2 = 0 -> hi iy2 = 0",
    concl: "1 <= lo iz /\\ hi iz <= 0" },
  { name: 'row_6a', lemma: 'zpos_6a', tag: 'P0 (x=[0,b]) x N',
    guards: "lo ix2 = 0 -> 0 < hi ix2 -> lo iy2 < 0 -> hi iy2 <= 0",
    concl: "hi iz <= cdiv (Z.min (-1) (hi iy2)) (hi ix2 + 1) - 1" },
  { name: 'row_6b', lemma: 'zpos_6b', tag: 'P0 (x=[0,b]) x P',
    guards: "lo ix2 = 0 -> 0 < hi ix2 -> ((lo iy2 <? 0) && (hi iy2 <=? 0))%bool = false -> 0 < hi iy2 -> 0 <= lo iy2",
    concl: "Z.max 1 (lo iy2) / (hi ix2 + 1) + 1 <= lo iz" },
]

const SCHEMA = {
  type: 'object',
  additionalProperties: false,
  properties: {
    name: { type: 'string' },
    compiled: { type: 'boolean' },
    aux: { type: 'string', description: 'auxiliary Lemma...Qed. blocks added before the main lemma (empty string if none)' },
    proof: { type: 'string', description: 'the full proof body between Proof. and Qed. of the main lemma' },
    notes: { type: 'string', description: 'brief notes: what worked, any caveat' },
  },
  required: ['name', 'compiled', 'proof'],
}

phase('Prove rows')
const results = await parallel(rows.map(r => () => {
  const stmt = `Lemma ${r.lemma} : ${PREFIX}${r.guards} ->\n  ${r.concl}.`
  const prompt =
`Read the brief at /tmp/claude-1000/-home-ptalbot-repositories-lattice-land-lala-core/47acb528-3937-49c8-b403-258bc9817989/scratchpad/zpos_brief.md FIRST (use the Read tool).

Then prove this ONE Rocq lemma (row: ${r.tag}). Create the file at
/home/ptalbot/repositories/lattice-land/lala-interval/rocq/${r.name}.v with EXACTLY this scaffold header, then your (optional) auxiliary lemmas, then the main lemma with your proof:

--- file header (verbatim) ---
From LalaInterval Require Import fdiv.
From LalaInterval Require Import zbase.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
--- then (optional aux lemmas) then: ---
${stmt}
Proof.
  (* your proof *)
Qed.

Develop the proof using the rocq MCP tools (ToolSearch for
select:mcp__rocq-mcp__rocq_start,mcp__rocq-mcp__rocq_check,mcp__rocq-mcp__rocq_step_multi,mcp__rocq-mcp__rocq_compile_file),
then VERIFY the whole file compiles with rocq_compile_file (file="${r.name}.v",
workspace="/home/ptalbot/repositories/lattice-land/lala-interval/rocq"). It MUST return success:true
with NO admit/Admitted. The statement is grid-validated TRUE, so keep iterating until it compiles.

This row involves ${r.tag}. If it needs a negative-divisor / ceiling (cdiv) pass-1 helper,
PROVE that helper as an auxiliary Lemma in your file first (model it on fden_ub_mul_pos;
the brief lists the negative arithmetic lemmas available). Remember the lia/nia timeout
caution in the brief: clear heavy hypotheses before nia and prove corner facts with explicit
min/max lemmas.

Return: name="${r.lemma}", compiled=(did rocq_compile_file succeed), aux=(your aux lemmas verbatim, or ""),
proof=(the exact tactics between Proof. and Qed. of the main lemma), notes=(short).`
  return agent(prompt, { label: r.name, phase: 'Prove rows', schema: SCHEMA, effort: 'high' })
    .then(res => ({ ...res, lemma: r.lemma }))
}))

const ok = results.filter(Boolean).filter(r => r.compiled)
const bad = results.filter(Boolean).filter(r => !r.compiled)
log(`compiled ${ok.length}/${rows.length}; failed: ${bad.map(b=>b.lemma).join(', ') || 'none'}`)
return { results }
