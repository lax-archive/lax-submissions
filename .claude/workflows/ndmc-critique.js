// The ND-MC critique harness. Re-runnable by name:  Workflow({name: 'ndmc-critique'})
//
// Standing goal from Jan, 2026-08-17: get `plans/nowhere-dense-model-checking/
// algorithm-v2.md` to a state where this harness comes back CLEAN -- no finding
// that survives its adversarial verifier at severity major or fatal.
//
// It is written against Rev 3's open surface. Re-point the four group prompts
// at whatever is unaudited in the current revision before re-running: auditing
// what a previous round already fixed wastes the pass. The GKS source it needs
// is now checked in at references/gks/ (fetched 2026-08-17), so the scratch
// path below can be replaced by that.

export const meta = {
  name: 'ndmc-critique',
  description: 'Attack the unaudited material of algorithm-v2 Rev 3: cover time, cover space (validating the contract change), the two new inventions, and the seams between twenty patches',
  phases: [
    { title: 'Attack', detail: 'four refutation attempts on Rev 3 material nobody has read' },
    { title: 'Verify', detail: 'adversarial second opinion' },
    { title: 'Synthesize', detail: 'is the plan safe to spend a week on' },
  ],
}

const REPO = '/home/user/lax-submissions'
const GKS = REPO + '/references/gks/nowheredense.tex'

const CONTEXT = [
'Repository ' + REPO + '. Lean 4 formalization of Grohe-Kreutzer-Siebertz: first-order',
'model checking is FPT in almost linear time on nowhere dense graph classes,',
'realized on a word RAM.',
'',
'READ FIRST, in full:',
'  ' + REPO + '/plans/nowhere-dense-model-checking/algorithm-v2.md          (Rev 3)',
'  ' + REPO + '/plans/nowhere-dense-model-checking/pruned-algorithmic-layer.md',
'',
'HISTORY YOU NEED. On 2026-08-17 a 103k-line word-RAM implementation was deleted',
'and the algorithm redesigned. Rev 1 of algorithm-v2.md was written in one pass;',
'two adversarial audits (20 agents) then found roughly twenty defects in it, two',
'of them unsound rather than merely imprecise. Rev 3 repaired them. THE REPAIRS',
'THEMSELVES HAVE NOT BEEN AUDITED, and they include the document two newest and',
'most load-bearing ideas. That is what you are attacking. Do not re-audit what',
'Rev 3 already marks as fixed with an <A> tag unless you think the fix is wrong.',
'',
'SOURCES.',
'  ' + GKS,
'     -- Grohe-Kreutzer-Siebertz, arXiv:1311.3899, the LaTeX source. NEWLY',
'        AVAILABLE: both earlier audits ran WITHOUT it, so every claim traced to',
'        "GKS section 6" or "GKS section 8" in the design has been checked',
'        against absence, not against text. Section 6 "Sparse Neighbourhood',
'        Covers" begins at line 1227; "The Main Algorithm" at line 2470;',
'        "Independent Sets" at 917; the game characterisation at 758. This file',
'        is a scratch copy under arXiv non-exclusive licence -- read it, cite it',
'        by line number, do NOT copy it into the repository.',
'  ' + REPO + '/references/rploc/proofs_new.tex   -- Dreier-Toruncyzk locality note',
'  ' + REPO + '/nowhere-dense-model-checking/concepts/Lax3/*.lean     -- endorsed surface',
'  ' + REPO + '/nowhere-dense-model-checking/proofs/Lax3Proofs/*.lean -- surviving math layer',
'  ' + REPO + '/word-ram/  and  ' + REPO + '/sparsity-lectures/  -- pinned dependencies',
'     (Lax13 the machine plus its Refine tower, Lax12 sparsity)',
'  Deleted code, read-only evidence about the OLD design only:',
'     cd ' + REPO + ' && git show 816e5cc:nowhere-dense-model-checking/proofs/Lax3Proofs/<Path>.lean',
'',
'RULES.',
'- You are trying to REFUTE. Cite file:line, or tex line number, or carry out',
'  the arithmetic in full. Do not accept the design own reasoning.',
'- "Unclear" beats a guess. Say what would settle it.',
'- Read only. Scratch files under /tmp are fine. Never edit a tracked file and',
'  never add anything to references/.',
].join('\n')

const FINDINGS = {
  type: 'object', additionalProperties: false, required: ['findings', 'summary'],
  properties: {
    summary: { type: 'string' },
    findings: {
      type: 'array', maxItems: 10,
      items: {
        type: 'object', additionalProperties: false,
        required: ['id', 'claim', 'verdict', 'severity', 'evidence'],
        properties: {
          id: { type: 'string' },
          claim: { type: 'string', description: 'The Rev 3 claim under test, with its section, quoted tightly.' },
          verdict: { type: 'string', enum: ['holds', 'broken', 'overstated', 'unclear'] },
          severity: { type: 'string', enum: ['fatal', 'major', 'minor', 'none'] },
          evidence: { type: 'string' },
          fix: { type: 'string' },
        },
      },
    },
  },
}

const VERDICT = {
  type: 'object', additionalProperties: false, required: ['id', 'upheld', 'reasoning'],
  properties: {
    id: { type: 'string' }, upheld: { type: 'boolean' },
    corrected_verdict: { type: 'string', enum: ['holds', 'broken', 'overstated', 'unclear'] },
    corrected_severity: { type: 'string', enum: ['fatal', 'major', 'minor', 'none'] },
    reasoning: { type: 'string' },
  },
}

const GROUPS = [
  {
    key: 'cover-time',
    prompt: [
'GROUP A: the cover TIME bound, against the GKS text that is finally available.',
'',
'algorithm-v2 section 4 charges "cover A r" at O(||A||^(1+delta)) and section',
'6.2 concedes this is "a claim rather than an inspection". It is the sole',
'superlinear routine, the sole source of D(N), and therefore the sole reason',
'section 7 needs delta at all. Nobody has checked it against the source, because',
'the source was not in the repository until now.',
'',
'(a) Read GKS section 6 (Sparse Neighbourhood Covers, from line 1227) and the',
'    Main Algorithm (from line 2470). What running time do THEY claim for',
'    computing a sparse neighbourhood cover, under what hypotheses, and by what',
'    construction? Quote the theorem/lemma statements by line number.',
'',
'(b) Does their construction match section 6.2 of the design -- transitive-',
'    fraternal augmentation chain, ordering pi, X_u := {w : u in',
'    wreach_pi(A,2R,w)}, ctr v := pi-min(wreach_pi(A,R,v))? Where it differs,',
'    say how, and say whether the difference costs or saves.',
'',
'(c) The design applies the cover AT EVERY NODE of the recursion, to arenas that',
'    are induced subgraphs of members of the class carrying extra colours and',
'    accumulated isolated vertices. GKS apply it too -- check at what',
'    granularity, and check whether the wcol/degree bound they use is uniform',
'    over such arenas. The design asserts uniformity "over subgraphs"; verify',
'    against both GKS and CoverDegree.lean.',
'',
'(d) THE DECISIVE QUESTION: is O(N^(1+delta)) TIME for the cover actually true,',
'    and is it true for the augmentation chain that produces the ordering, not',
'    only for reading the clusters off the ordering? Count the rounds and the',
'    per-round cost from GKS own statement. If their bound is O(N^(1+delta))',
'    only for FIXED delta with the constant depending on delta, say so',
'    precisely -- the design needs delta = eps/(l+1) with l forced by the class,',
'    so a constant that blows up as delta shrinks is still fine but must be a',
'    constant of (C, phi, eps) and not of n.',
'',
'(e) Check the design claim (section 1, and the starred bound in section 7) that',
'    Sigma_X n_X <= n^(1+delta) is what the whole running-time proof rests on,',
'    against GKS own accounting in the Main Algorithm section. Is the design',
'    charging the same things they charge?',
].join('\n'),
  },
  {
    key: 'cover-space',
    prompt: [
'GROUP B: does the contract change actually suffice? This validates a decision',
'already taken, so be adversarial about it.',
'',
'On 2026-08-17 the endorsed axiom word-length side condition in',
'concepts/Lax3/ModelChecking.lean was changed from',
'  c * (x.length + v + 1) <= 2^w    to    c * (x.length + v + 1)^2 <= 2^w,',
'on the argument that the algorithm needs Theta(n^(1+delta)) addressable cells',
'and squaring buys n^2, which covers every delta <= 1.',
'',
'The reasoning behind that change verified the CLUSTER FAMILY size. It did NOT',
'verify the intermediate objects of the augmentation chain that produces the',
'ordering. Your job is to find out whether n^2 is enough for the WHOLE cover',
'pipeline, and for the rest of the algorithm.',
'',
'(a) Enumerate every object the algorithm holds live, with its size, at peak.',
'    At minimum: the l+1 live arenas; each node colour array (N x L_j, and L_j',
'    may be a TOWER of height l -- see open question O3); each node table',
'    (N x |F_j|); each node cover output (Sigma_u |X_u| <= D*N); the',
'    augmentation chain per-round fraternity graphs; the wreach fibres at radius',
'    R and 2R; the greedy-scatter marking; the recorded ancestor paths.',
'',
'(b) THE ONE THAT MATTERS: the augmentation chain. Read CoverDegree.lean,',
'    AugmentedDensity.lean and Augmentation.lean, and GKS section 6. The',
'    in-degree budget in CoverDegree is of the form (d0 + D1 + 2)^(16^R) with',
'    D1 = ceil(c0 * m^(delta / (2 * 16^R))). Work out the size of each round',
'    fraternity graph and of the chain largest intermediate. Is it O(n^2)? Is it',
'    O(n^(1+delta))? Or is it larger -- e.g. does any round square an object,',
'    giving a tower in n rather than in the constants?',
'',
'(c) Are the enormous CONSTANTS (R = 9^(q(q+1)); l and m from the class at',
'    radius 2R; L_l possibly a tower) really absorbable into c, as section 3',
'    standing remark claims? Check against ModelChecking.lean actual statement:',
'    c appears BOTH in the time bound and in the admissible-input side',
'    condition, so enlarging it does two things at once. Confirm or refute that',
'    enlarging c is always safe.',
'',
'(d) VERDICT: is exponent 2 right, too small, or unnecessarily large? If too',
'    small, what is the smallest exponent that works, and does it depend on the',
'    class or on eps (which would be a problem -- the design argues the side',
'    condition must be a property of the encoding alone)? If n^(1+delta) can be',
'    achieved with a streaming cover, say what specifically would have to be',
'    true of wreach fibres for that to work.',
'',
'(e) Sanity-check the claim that the change touches nothing else: grep the whole',
'    repository for other consumers of that side condition or of',
'    exists_almostLinearTime_program_modelChecking.',
].join('\n'),
  },
  {
    key: 'new-inventions',
    prompt: [
'GROUP C: attack the two ideas Rev 3 invented, which nobody has checked.',
'',
'INVENTION 1 -- the path-closure batch (section 5 lines 17-23 and the prose',
'under "The repair, and it is free"). The claim is:',
'',
'  With X_u = {w | u in wreach_pi(A, 2R, w)}, take w in X_u and a witnessing',
'  walk p : A.Walk w u of length <= 2R all of whose support is pi-above u. For',
'  any z in p.support, p.dropUntil z is a walk z -> u with support contained in',
'  p.support and length <= p.length <= 2R, so its pi-minimality clause holds',
'  verbatim and z in X_u. Hence p.support is contained in X_u, so p is a walk of',
'  A[X_u], so dist over A[X_u] from u to w is <= 2R for every w in X_u.',
'',
'  Consequence claimed: ONE parent-recording BFS from u inside A[X_u], cost',
'  O(||A[X_u]||), supplies a walk of length <= 2R from u to every vertex of',
'  every descendant carrier, in the arena of u own round -- which is what',
'  SplitterWinRec.ReachedR.step hwalk needs.',
'',
'Attack it. Specifically:',
' (i)   Check mem_wreach_iff and the wreach definition in CoverConstruction.lean',
'       and OrderedCovers.lean. Is the pi-minimality clause really "all of',
'       p.support is pi-above u", or is it something subtly different (e.g.',
'       about the ENDPOINT being minimum, or about w own position, or a strict',
'       inequality) that dropUntil does not preserve? Does Mathlib Walk.dropUntil',
'       have the support and length properties claimed? Does it need DecidableEq',
'       or membership hypotheses?',
' (ii)  Even granting path-closure inside X_u: hwalk asks for a walk in',
'       e.arena, the earlier round arena. The arena of u round is the PARENT',
'       arena A, not A[X_u]. A[X_u] is a subgraph of A, so a walk in A[X_u] is a',
'       walk in A -- check that this direction is the one needed and that the',
'       types line up, since arenas in the design are RENUMBERED (decision D1)',
'       while ReachedR arenas are on a fixed carrier.',
' (iii) The batch is W := pad_m({u} union (union over h in A.hist of h cap X_u)).',
'       Is |W| <= m? m is the splitter batch bound from the class. The recorded',
'       paths have <= 2R vertices each and there are <= l of them, so the union',
'       can have up to l*2R + 1 elements. Is l*2R+1 <= m? Check what m actually',
'       is -- UqwInstantiation.lean and SplitterWin.lean give the strategy batch',
'       size. If l*2R+1 > m the batch is illegal and the game is not being',
'       played.',
' (iv)  Does intersecting a recorded ancestor path with a descendant carrier',
'       preserve the property that the isolated set cuts what it must cut? A',
'       path can leave and re-enter the carrier.',
'',
'INVENTION 2 -- the compaction lemma (section 5 step 3-prime, section 8 step',
'4a). Rev 3 asserts an order-preserving Sat-transport lemma between the',
'carrier-kept arena (deleteVerts on Fin n) and the renumbered arena (Fin N),',
'with a "dead-vertex correction" for the greedy scatter choice, and puts it on',
'the critical path.',
'',
'Attack it: state the lemma precisely yourself, then find the obstruction.',
' (i)   What exactly must be assumed about the formula for it to hold? Rev 3',
'       gestures at "every quantifier guarded by the marker colour". Is that',
'       preserved by iso? Check iso_exU and iso_exL in Isolate.lean -- iso turns',
'       a guarded quantifier into a DISJUNCTION containing an UNGUARDED exU',
'       (that is decision D2 "guards degrade"). If the transported formula has',
'       an unguarded quantifier, the transport is false, because the unguarded',
'       quantifier ranges over the dead vertices on one side and not the other.',
'       This is the crux -- settle it.',
' (ii)  The dead vertices are isolated AND colourless in the carrier-kept arena.',
'       Work out what the greedy maximal scattered set does over them, and',
'       whether the "dead-vertex correction" Rev 3 hand-waves at can exist.',
' (iii) If the lemma is false as stated, is there a repair? Options to weigh:',
'       apply locality at the carrier-kept arena and compact only the TABLE; pad',
'       the child arena back to Fin n (which would violate P1); or restrict the',
'       formula class.',
].join('\n'),
  },
  {
    key: 'rev3-seams',
    prompt: [
'GROUP D: read algorithm-v2 Rev 3 as ONE document and find where the twenty',
'separate patches contradict each other or leave a hole.',
'',
'Rev 3 was produced by applying twenty individually-verified findings to Rev 1.',
'Each fix was made in isolation. Your job is the interactions -- the defects',
'that exist only because two fixes met.',
'',
'Known interaction surfaces to start from, but do not stop there:',
'',
'(a) D2 was unfused into restrict / recordProfiles / isolate. Section 5 lines',
'    16-21 were reordered. Does every later reference to "induce" or to the',
'    fused operation still exist somewhere in the document? Does section 4',
'    operations table match section 5 pseudocode and section 6 routines,',
'    operation for operation and charge for charge? Is isolate in the table? Is',
'    bfsParents?',
'',
'(b) The new batch (section 5 lines 17-19) requires restrict to MAINTAIN the',
'    recorded paths (decision D6, the hist field in section 4, "restrict hist"',
'    in section 6.1). Is the cost of that accounted anywhere? Is the semantics',
'    of "h cap X_u" for a path well defined -- a path intersected with a vertex',
'    set is not a path?',
'',
'(c) The compaction lemma (step 3-prime) moved where locality is applied.',
'    Section 5 chain now applies it at B. But section 3 L0 rank argument, D4',
'    fixed-point argument, and D5 schedule are all stated about applying it at',
'    the carrier-kept arena. Do they still hold at B? Does the formula schedule',
'    F_j depend on which arena locality is applied at?',
'',
'(d) Section 7 middle term is now c * Sigma_u N_u, and section 4 says restrict',
'    costs Sigma over s in S of deg_A(s), which is NOT N_u. Does section 7',
'    arithmetic actually use the right quantity? Redo the absorption with the',
'    correct term.',
'',
'(e) P1 was split into P1a and P1b. Check every routine in section 6 and every',
'    line of section 5 against BOTH, and report any that still violate either.',
'',
'(f) Section 8 step numbering was rewritten. Are all cross-references correct',
'    (sections 5 and 2 refer to step 4a, step 6, step 0)? Does any step depend',
'    on a later one?',
'',
'(g) The leaf case: section 5 line 10 stops at "j = l or A has no edges", but',
'    the precondition is now ReachedR rather than SplitterWins, and the depth',
'    bound comes from reachedR_length_lt. Does the recursion actually terminate',
'    at depth l under the new precondition, and is j still meaningful as an',
'    index into the formula schedule F_j if the play can stop earlier?',
'',
'(h) Anything the document still says that the two prior audits refuted but Rev',
'    3 failed to delete.',
].join('\n'),
  },
]

phase('Attack')

const results = await pipeline(
  GROUPS,
  g => agent(CONTEXT + '\n\n' + g.prompt, { label: 'attack:' + g.key, phase: 'Attack', schema: FINDINGS, effort: 'high' }),
  (report, g) => {
    if (!report || !report.findings) return { key: g.key, summary: report ? report.summary : 'no result', verdicts: [] }
    const interesting = report.findings.filter(f => f.verdict !== 'holds')
    if (!interesting.length) return { key: g.key, summary: report.summary, verdicts: [], allHold: report.findings }
    return agent(
      CONTEXT +
      '\n\nYou are the ADVERSARIAL VERIFIER for group "' + g.key + '". Another auditor\n' +
      'produced the findings below about algorithm-v2 Rev 3. Refute THE AUDITOR.\n' +
      'Open every citation yourself; do not take it on trust. Search the whole\n' +
      'document before agreeing that something is missing -- Rev 3 is long and the\n' +
      'answer is often in another section. Default to upheld=false unless convinced.\n\n' +
      JSON.stringify(interesting, null, 2),
      { label: 'verify:' + g.key, phase: 'Verify', schema: { type: 'object', additionalProperties: false, required: ['verdicts'], properties: { verdicts: { type: 'array', items: VERDICT } } }, effort: 'high' }
    ).then(v => ({ key: g.key, summary: report.summary, findings: interesting, verdicts: (v && v.verdicts) || [], allHold: report.findings.filter(f => f.verdict === 'holds') }))
  }
)

const clean = results.filter(Boolean)

phase('Synthesize')

const verdict = await agent(
  CONTEXT +
  '\n\nYou are the SYNTHESIZER. Four auditors and their verifiers attacked the\n' +
  'unaudited material of algorithm-v2 Rev 3:\n\n' + JSON.stringify(clean, null, 2) +
  '\n\nThe reader is about to spend a week of proving effort against this plan and\n' +
  'has asked whether it is safe to do so. Answer these, each with the evidence:\n' +
  '1. Is the cover O(N^(1+delta)) TIME bound true? Cite GKS.\n' +
  '2. Is the squared word-length side condition sufficient? If not, what is?\n' +
  '   (A contract change was already made on the assumption that it is.)\n' +
  '3. Do the two Rev 3 inventions -- the path-closure batch and the compaction\n' +
  '   lemma -- survive? If either fails, what is the repair, and does its failure\n' +
  '   change the algorithm or only the proof?\n' +
  '4. Is Rev 3 internally consistent enough to be built from?\n' +
  '5. If you had to name the ONE thing most likely to cost the reader a week,\n' +
  '   what is it?\n' +
  'Report as findings with ids q1..q5 plus anything else worth carrying. Be\n' +
  'blunt and rank by what changes the plan.',
  { label: 'synthesize:verdict', phase: 'Synthesize', schema: FINDINGS, effort: 'high' }
)

return { groups: clean, verdict }
