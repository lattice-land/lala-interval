export const meta = {
  name: 'prove-branch-attain',
  description: 'Prove branch_attain: fdivxz_pos x,z bounds are attained by solutions (branch optimality)',
  phases: [{ title: 'Prove branch_attain' }],
}
const SCHEMA = {
  type: 'object', additionalProperties: false,
  properties: { name:{type:'string'}, compiled:{type:'boolean'}, file:{type:'string'}, notes:{type:'string'} },
  required: ['name','compiled','file'],
}
phase('Prove branch_attain')
const attempts = ['ba_a','ba_b','ba_c']
const results = await parallel(attempts.map(nm => () => {
  const prompt =
`Read /tmp/claude-1000/-home-ptalbot-repositories-lattice-land-lala-core/47acb528-3937-49c8-b403-258bc9817989/scratchpad/branch_brief.md FIRST (Read tool). Also READ fdiv.v (the fdivxz_pos definition ~line 685 and fden_sound ~line 499) with the Read tool.

Prove the lemma 'branch_attain' EXACTLY as stated in the brief, in file
/home/ptalbot/repositories/lattice-land/lala-interval/rocq/${nm}.v (header from brief).
Develop with the rocq MCP tools (ToolSearch: select:mcp__rocq-mcp__rocq_start,mcp__rocq-mcp__rocq_check,mcp__rocq-mcp__rocq_step_multi,mcp__rocq-mcp__rocq_compile_file).
VERIFY with rocq_compile_file(file="${nm}.v", workspace="/home/ptalbot/repositories/lattice-land/lala-interval/rocq"): must be success:true with NO admit/Admitted.
The z-bounds come straight from optbase's fden_opt; the x-bounds use div_1d after locating the
right z-corner of iz. It is grid-validated true. Persist.
Return name="branch_attain", compiled=(rocq_compile_file success), file=(the COMPLETE final file), notes.`
  return agent(prompt, { label: nm, phase: 'Prove branch_attain', schema: SCHEMA, effort: 'high' })
}))
const ok = results.filter(Boolean).filter(r=>r.compiled)
log(`branch_attain: ${ok.length}/${attempts.length} compiled`)
return { results }
