export const meta = {
  name: 'prove-y-attain',
  description: 'Prove y_attain: the y-bounds of the propagator output are attained by solutions',
  phases: [{ title: 'Prove y_attain' }],
}
const SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: { name:{type:'string'}, compiled:{type:'boolean'}, file:{type:'string'}, notes:{type:'string'} },
  required: ['name','compiled','file'],
}
phase('Prove y_attain')
const attempts = ['ya_a','ya_b','ya_c']
const results = await parallel(attempts.map(nm => () => {
  const prompt =
`Read /tmp/claude-1000/-home-ptalbot-repositories-lattice-land-lala-core/47acb528-3937-49c8-b403-258bc9817989/scratchpad/yattain_brief.md FIRST (Read tool). Also READ fdiv.v (propagator, refine_y, fdivxz_pos, Ylo/Yhi, div_bracket_pos/neg) with the Read tool.

Prove the lemma 'y_attain' EXACTLY as stated in the brief, in file
/home/ptalbot/repositories/lattice-land/lala-interval/rocq/${nm}.v (header from brief).
Develop with the rocq MCP tools (ToolSearch: select:mcp__rocq-mcp__rocq_start,mcp__rocq-mcp__rocq_check,mcp__rocq-mcp__rocq_step_multi,mcp__rocq-mcp__rocq_compile_file).
VERIFY with rocq_compile_file(file="${nm}.v", workspace="/home/ptalbot/repositories/lattice-land/lala-interval/rocq"): success:true, NO admit/Admitted.
The witness for a y-bound Y is (Y/zc, Y, zc) for the z-corner zc of (sz (propagator s)) whose numerator
band contains Y; use propagator_reductive (from optbase2) for the in_store s memberships. It is
grid-validated true. Persist.
Return name="y_attain", compiled=(rocq_compile_file success), file=(the COMPLETE final file), notes.`
  return agent(prompt, { label: nm, phase: 'Prove y_attain', schema: SCHEMA, effort: 'high' })
}))
const ok = results.filter(Boolean).filter(r=>r.compiled)
log(`y_attain: ${ok.length}/${attempts.length} compiled`)
return { results }
