export const meta = {
  name: 'prove-fden-opt',
  description: 'Prove fden z-optimality (completeness): table z-bounds are attained by solutions',
  phases: [{ title: 'Prove fden_opt' }],
}

const DEFS =
  "Definition ileD (i j : itv) : Prop := lo j <= lo i /\\ hi i <= hi j.\n" +
  "Definition CxD (iy iz : itv) : itv :=\n" +
  "  Itv (Xlo (lo iy) (hi iy) (lo iz) (hi iz)) (Xhi (lo iy) (hi iy) (lo iz) (hi iz))."

const CONCL =
  "  (exists x y, mem ix x /\\ mem iy y /\\ sol x y (lo (fden ix iy iz)))\n" +
  "  /\\ (exists x y, mem ix x /\\ mem iy y /\\ sol x y (hi (fden ix iy iz)))."

const tasks = [
  { name: 'fdenopt_pos_a', lemma: 'fden_opt_pos', hyp: '0 < lo iz' },
  { name: 'fdenopt_pos_b', lemma: 'fden_opt_pos', hyp: '0 < lo iz' },
  { name: 'fdenopt_neg_a', lemma: 'fden_opt_neg', hyp: 'hi iz < 0' },
  { name: 'fdenopt_neg_b', lemma: 'fden_opt_neg', hyp: 'hi iz < 0' },
]

const SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: {
    name: { type: 'string' }, compiled: { type: 'boolean' },
    file: { type: 'string', description: 'the COMPLETE verified .v file content (imports, defs, lemma, proof)' },
    notes: { type: 'string' },
  },
  required: ['name', 'compiled', 'file'],
}

phase('Prove fden_opt')
const results = await parallel(tasks.map(tk => () => {
  const stmt =
`Lemma ${tk.lemma} : forall ix iy iz,\n  ${tk.hyp} ->\n  ileD ix (CxD iy iz) ->\n  lo (fden ix iy iz) <= hi (fden ix iy iz) ->\n${CONCL}`
  const prompt =
`Read /tmp/claude-1000/-home-ptalbot-repositories-lattice-land-lala-core/47acb528-3937-49c8-b403-258bc9817989/scratchpad/zopt_brief.md FIRST (Read tool), and READ the fden definition + fden_sound proof in /home/ptalbot/repositories/lattice-land/lala-interval/rocq/fdiv.v (Read tool, around lines 460-680) — your proof mirrors fden_sound's case structure.

Prove this lemma (the ${tk.hyp.includes('lo') ? 'POSITIVE' : 'NEGATIVE'}-z half of fden z-optimality):

--- file to create at /home/ptalbot/repositories/lattice-land/lala-interval/rocq/${tk.name}.v ---
From LalaInterval Require Import fdiv.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
${DEFS}

${stmt}
Proof.
  (* your proof *)
Qed.
---

Develop with the rocq MCP tools (ToolSearch select:mcp__rocq-mcp__rocq_start,mcp__rocq-mcp__rocq_check,mcp__rocq-mcp__rocq_step_multi,mcp__rocq-mcp__rocq_compile_file).
VERIFY the file compiles with rocq_compile_file(file="${tk.name}.v", workspace="/home/ptalbot/repositories/lattice-land/lala-interval/rocq"), success:true, NO admit/Admitted.
The statement is grid-validated TRUE. This is the completeness dual of fden_sound: after
"intros ix iy iz Hsign Htight Hne", unfold fden; cbv zeta; destruct every table guard with
eqn; decode the booleans; for each surviving row build the witness solution for BOTH the lo and
hi returned bound (split the conjunction, destruct Z.max_spec/Z.min_spec on the bound to know
input-side vs table-side, exhibit x,y). Use the tightness hyp Htight to place the witness y in iy.
Persist until it compiles.

Return name="${tk.lemma}", compiled=(rocq_compile_file success), file=(the COMPLETE final file content verbatim), notes.`
  return agent(prompt, { label: tk.name, phase: 'Prove fden_opt', schema: SCHEMA, effort: 'high' })
    .then(res => ({ ...res, lemma: tk.lemma }))
}))

const ok = results.filter(Boolean).filter(r => r.compiled)
log(`fden_opt: ${ok.length}/${tasks.length} compiled — pos:${ok.filter(r=>r.lemma==='fden_opt_pos').length} neg:${ok.filter(r=>r.lemma==='fden_opt_neg').length}`)
return { results }
