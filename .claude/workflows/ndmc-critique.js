// The ND-MC critique harness. Re-runnable by name:  Workflow({name: 'ndmc-critique'})
//
// Standing goal from Jan, 2026-08-17: get `plans/nowhere-dense-model-checking/
// algorithm-v2.md` to a state where this harness comes back CLEAN -- no finding
// that survives its adversarial verifier at severity major or fatal.
//
// ROUND 4, re-pointed at Rev 4's unaudited surface. Rounds 1-3 (7, 13, 9 agents)
// attacked the prune evidence, Rev 1, and Rev 3. Rev 4 is the repair of round 3
// and is marked <B> throughout the document; THAT is what this round attacks.
// Re-point these four prompts again before any round 5: auditing what a previous
// round already fixed wastes the pass.

export const meta = {
  name: 'ndmc-critique',
  description: 'Attack the unaudited <B> material of algorithm-v2 Rev 4: the cost constants, the rebuilt downward channel, the cover routine as GKS actually gives it, and the seams Rev 4 left',
  phases: [
    { title: 'Attack', detail: 'four refutation attempts on Rev 4 material nobody has read' },
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
'  ' + REPO + '/plans/nowhere-dense-model-checking/algorithm-v2.md          (Rev 4)',
'  ' + REPO + '/plans/nowhere-dense-model-checking/pruned-algorithmic-layer.md',
'',
'HISTORY YOU NEED. On 2026-08-17 a 103k-line word-RAM implementation was deleted',
'and the algorithm redesigned. Rev 1 was written in one pass. THREE adversarial',
'audits have run since -- 29 agents in total. Rev 3 repaired audit 2 (twenty',
'findings, two unsound). Rev 4 repairs audit 3 (nine findings surviving at major,',
'none of them in the algorithm; what broke was the seams between Rev 3 patches,',
'the constants, and the work order).',
'',
'WHAT YOU ARE ATTACKING. The document tags every repair with its revision:',
'  <A> = a Rev 3 repair. Audited in round 3 and it survived. Do NOT re-audit an',
'        <A> claim unless you have concrete evidence the fix is wrong.',
'  <B> = a Rev 4 repair, written in response to round 3 and NEVER AUDITED BY',
'        ANYONE. This is your target. Every <B> paragraph is a claim written in',
'        a hurry by an author who had just been shown he was wrong about the',
'        neighbouring paragraph.',
'Untagged prose predates both and has been read three times; treat it as',
'background unless a <B> patch changed what it depends on.',
'',
'SOURCES.',
'  ' + GKS,
'     -- Grohe-Kreutzer-Siebertz, arXiv:1311.3899, the LaTeX source. Rev 4 is the',
'        first revision written WITH it, so its GKS line citations are new and',
'        unchecked. Section 6 "Sparse Neighbourhood Covers" begins at line 1227;',
'        thm:alg-covers at 1255; thm:computingorientation at 1342; the cover',
'        algorithm and its accounting at 1459-1520; the f_X Remark at 1522-1538;',
'        "The Main Algorithm" at 2470; "Independent Sets" at 917; the game',
'        characterisation at 758. This file is a scratch copy under arXiv',
'        non-exclusive licence -- read it, cite it by line number, do NOT copy',
'        it into the repository.',
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
'- THE RULE THIS CAMPAIGN EARNED FOUR TIMES: read the theorem, not the docstring',
'  and not the file framing prose. Every defect found so far was a place where',
'  the document asserted something its own cited object does not say. Open every',
'  citation Rev 4 makes and check the statement, not the name.',
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
          claim: { type: 'string', description: 'The Rev 4 claim under test, with its section, quoted tightly.' },
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
    key: 'constants',
    prompt: [
'GROUP A: the constants and the cost arithmetic, all of it rewritten in Rev 4.',
'',
'Section 7 was rewritten twice in two revisions. Round 3 found that Rev 3 stated',
'inequality "dropped one c and the +1 from the recursion coefficient ... the same',
'failure mode as the counterexample the previous audit gave, one revision later,',
'in the paragraph written to repair it." Rev 4 rewrote it AGAIN, in a hurry, and',
'nobody has checked the rewrite. Section 3 constants were re-sourced at the same',
'time. Do the arithmetic yourself, on paper, from scratch. Do not read section 7',
'proof and agree with it; derive the condition independently and compare.',
'',
'(a) THE ONE MOST LIKELY TO BE WRONG. Section 4 charges cover at',
'    O(||A||^(1+delta)) and section 7 leading term is a*N^(1+delta). But Rev 4',
'    own section 6.2 transcribes GKS accounting for that same algorithm as',
'    "Sigma_v(|X_v|*n^delta + Sigma_{w in N_>(v)} d_<(w)) <= 2n^delta*Sigma_v|X_v|',
'    <= 2n^(1+2delta)" -- exponent 1+2*delta, not 1+delta. Check that against the',
'    tex (the display ends at line 1517 or so, and GKS set delta := epsilon/2 at',
'    the start of the proof, line 1459ff, precisely so that 2delta = epsilon).',
'    If the cover really costs N^(1+2delta) in the design own delta, then',
'    section 7 leading term, the (star) bound, section 3 delta := eps/(l+1), and',
'    the headline n^(1+eps) all shift. Work out what delta must be, and whether',
'    the tightened split section 7 defends (eps/(l+1) rather than GKS eps/(2l))',
'    survives at all. This is the single highest-value question in the round.',
'',
'(b) Redo the induction of section 7 yourself. T_j(N) <= a*N^(1+delta) +',
'    c*Sigma_u N_u + Sigma_u T_{j+1}(N_u), claim T_j(N) <= (2c)^(l-j+1) *',
'    N^(1+(l-j+1)delta). Derive the constant inequality, find where it is',
'    tightest, and solve it. Rev 4 says c >= 6, tight at c = 6 (144 <= 144),',
'    with c_D = c and a = 3c. Check: is c_D = c really the worst case (c is',
'    defined as max(..., c_D, 6), so c_D <= c -- is the LHS monotone in c_D?);',
'    is L = 1 really tightest; does the base case at j = l actually hold; is',
'    N >= 1 enough or is N >= 2 needed anywhere.',
'',
'(c) THE TERM THAT MAY NOT FIT IN a. Rev 4 sets a := c + 2c_D, glossed as',
'    "(cover, plus the restrict/hist aggregate of section 4/section 6.1)". But',
'    section 6.1 states that aggregate as O((1 + l*R)*c_D*||A||^(1+delta)) --',
'    with an l*R factor from the new hist channel (D6). 2c_D does not cover',
'    (1+l*R)c_D. Is the l*R factor absorbed by c (i.e. is "every routine',
'    constant" in section 3 large enough), and if so does that break the c >= 6',
'    solution, since c now appears on both sides? Restate a correctly and re-solve.',
'',
'(d) Section 3 re-sourced l and m. Open every citation and check the STATEMENT:',
'    UqwInstantiation.exists_roundBudget (:96-100) -- does it really conclude',
'    "exists N s l, l = N(2s+2) and ...", and is Rev 4 parenthetical right that',
'    "exists_roundBudget instantiates the UQW at 2*cap, so cap := R is the game',
'    radius 2R"? SplitterWinRec.reachedR_length_lt (:561-567) -- does it conclude',
'    rounds.length < N(2s+2) under hypotheses the design can supply?',
'    SplitterWinRec.splitterWins_of_reachedR (:459-465) -- does it conclude',
'    SplitterWins (N(2s+2)*(r+1)) r b A, and with r = 2R does that give',
'    m = l(2R+1) or m = l(4R+1)? Get the r-versus-2R bookkeeping exactly right;',
'    the document uses R for the radius cap and 2R for the game radius and the',
'    two are one character apart everywhere.',
'',
'(e) The genSet legality chain (section 3, "Consequence"). SplitterWin.genSet',
'    (:192-194) and genSet_ncard_le (:217-218): check the statements. Rev 4',
'    argues |W| <= 1 + (l-1)(2R+1) <= l(2R+1) = m "at depth j <= l-1". Is',
'    rounds.length <= j at depth j, or can it exceed j? Is the batch at line 19',
'    of section 5 literally genSet, given that the design intersects recorded',
'    supports with the child carrier (see group B) and pads to exactly m?',
'',
'(f) Section 3 new paragraph on R versus the augmentation chain depth. Check',
'    CoverDegree.exists_cover_degree (:366-378) signature and side conditions',
'    (3t <= R, 2*rc <= 2^t) and the returned constant. Is Rev 4 proposed chain',
'    depth "approx 3*ceil(log2(4*rc))" actually admissible under those side',
'    conditions, and does GKS aside at tex:1369-1372 say what Rev 4 says it says?',
    ].join('\n'),
  },
  {
    key: 'channel',
    prompt: [
'GROUP B: the downward channel, rebuilt from nothing in Rev 4. Wholly unaudited,',
'and it is the largest new object in the revision.',
'',
'Round 3 killed Rev 3 channel ("a recorded parent-pointer path of <= 2R vertices',
'per round suffices") with three arguments: hwalk is quantified over every',
'earlier round and demands a walk to a connector unknown when the round was',
'played; concatenation exceeds 2R; and a parent array cannot be carried because',
'restriction destroys parent chains, while reachedR_descend hbatch (:533-538)',
'proves batchR = W EXACTLY, so a missing element means the program arena is not',
'the game arena. Rev 4 replaces it with:',
'',
'  hist : Fin N -> Fin l -> List (Fin N)   -- per vertex AND per ancestor round,',
'  the <= 2R+1 support names of that round walk to this vertex (section 4),',
'  produced by a new routine bfsSupports (section 4 table, section 5 line 17),',
'  maintained by restrict, which "for each s in S and each ancestor round,',
'  intersect(s) the stored support list with S" (section 6.1), justified by:',
'  "Filtering at restrict is sound because carriers are nested: (S cap X1) cap X2',
'  = S cap X2 for X2 subset of X1, so a support list filtered to the child',
'  carrier is still the support of a walk of the ancestor arena." (D6)',
'',
'(a) THE CRUX. That justification is a non sequitur on its face: the set identity',
'    says filtering twice equals filtering once, which is about REPRESENTATION',
'    CONSISTENCY, and the conclusion drawn is that the filtered list is still a',
'    WALK SUPPORT. Dropping vertices from a walk support does not leave a walk',
'    support. Settle it: is the filtered list still what the game needs, and if',
'    so by what argument? Note the design own killer argument against parent',
'    arrays applies verbatim here unless something rescues it -- hbatch demands',
'    batchR = W exactly, and filtering removes elements. Consider the possible',
'    rescue that vertices outside the child carrier do not exist in the child',
'    arena at all (D1 renumbers), so isolating them is vacuous THERE while the',
'    game keeps the carrier Fin n -- does that make filtering exactly right, or',
'    does it just relocate the problem into the carrier-transport lemma that',
'    section 9 books as still open? Say precisely which lemma statement would',
'    close it.',
'',
'(b) bfsSupports. Section 4 charges it O(d*||ball_d(v)||) and section 5 line 17',
'    runs it once per child at d = 2R. Can one BFS actually materialise, at every',
'    reached vertex w, the support names of a u->w walk of length <= 2R, in that',
'    time and in O(R) space per vertex? Check the interaction with the <A>',
'    path-closure lemma (section 5): it guarantees dist inside A[X_u] from u to',
'    every w in X_u is <= 2R, so BFS reaches all of X_u -- verify that claim is',
'    what makes line 17 total, and that a BFS-tree path (not the witnessing walk',
'    of the wreach definition) also has support inside X_u.',
'',
'(c) THE WALK THE GAME ACTUALLY WANTS. ReachedR.step hwalk',
'    (SplitterWinRec.lean:195-198) asks for a walk in e.arena. Line 23 stores',
'    S[w] = support of a walk from u to w computed inside B_0 = A[X_u], and',
'    e.arena for that round is A, the parent arena. A[X_u] is a subgraph of A --',
'    check the direction is the one needed AND that the types line up given D1',
'    renumbering (section 9 <B> note says RoundR fixes arena : SimpleGraph',
'    (Fin n) and ReachedR types A : SimpleGraph (Fin n), so section 5 "# pre:"',
'    line does not typecheck; and nextArenaR restricts to ball e.arena r e.vtx',
'    while the design restricts to X_u). Is the design storing a walk in the',
'    right graph at the right time for EVERY later descendant, or only for the',
'    immediate child?',
'',
'(d) SIZE AND SPACE. hist is Theta(l*R*N) words per arena and is copied at every',
'    restrict. Check it against P1a and P1b (section 1), against section 11 peak',
'    accounting (Rev 4 says the peak grows by Theta(l*R*n), "affordable under the',
'    squared side condition" -- verify against the unconditional N^2 argument in',
'    section 11, which was proved about cover output only), and against the l*R',
'    factor group A part (c) is chasing in section 7.',
'',
'(e) Line 19 builds W from B_0.hist[u][e] -- the support at the NEW connector u.',
'    Check that is the right index (genSet is a union of pathSet e.2 r e.1 v over',
'    rounds, at the new connector v), that pad_m to exactly m is compatible with',
'    hbatch batchR = W exactly, and that the "<B> = genSet" claim in the line 19',
'    comment is defensible after filtering and padding.',
'',
'(f) Line 23 writes B.hist for the current round as S[w] and keeps B_0.hist[w][e]',
'    otherwise, indexed by "e = now". Is the round index well defined -- does the',
'    program know its depth j equals the number of recorded rounds? Section 5',
'    line 8 precondition names "rounds" but no line maintains a rounds list.',
    ].join('\n'),
  },
  {
    key: 'cover-gks',
    prompt: [
'GROUP C: the cover routine, as Rev 4 rewrote it FROM the GKS source, and its',
'seam with the rest of the design.',
'',
'Rev 4 section 6.2 adds a paragraph that did not exist before: "What this section',
'describes is the ordering, not the cover algorithm", followed by a transcription',
'of GKS actual algorithm (tex:1459-1520) -- ascending pi order, 2r BFS levels in',
'the peeled graph G minus S(v), then DELETE v; correctness X_{2r}[G,<,v] =',
'N_{2r}^{G\\S(v)}(v) (tex:1468-1471); accounting <= 2n^(1+2delta). Section 4 adds',
'a matching rewrite of ctr, attributing pi-min(wreach) to the GKS Remark',
'(tex:1522-1538) rather than to the design. Section 11 uses the same Claim to',
'refute Rev 3 stated obstacle to streaming. None of this has been checked.',
'',
'(a) Open tex:1443-1540 and check every one of those transcriptions against the',
'    text, including that GKS delta := epsilon/2 and what that does to the',
'    exponent (coordinate with group A -- if the honest cover cost is',
'    N^(1+2delta) in the design delta, say so here too and price it).',
'',
'(b) THE MUTATION. Rev 4 concedes "the peeling sweep MUTATES the arena, which',
'    section 4 operation table does not model", and then does nothing about it.',
'    Work out what it actually costs and whether it is legal: the design calls',
'    restrict(A, X_u) at line 16 using A EDGES, after cover has peeled A down to',
'    nothing. Does the design need a copy of A (space, section 11), or an undo,',
'    or is the peeling only conceptual? Is the O(n^(1+delta)) representation GKS',
'    require (edges split into N_< / N_> lists with d_<(v) <= n^delta) compatible',
'    with the CSR of section 4, and is BUILDING it inside the design cost budget',
'    at every node?',
'',
'(c) IS IT THE SAME OBJECT? The design cluster is the wreach FIBRE',
'    X_u := {w : u in wreach_pi(A,2R,w)} (OrderedCovers.lean:106), and GKS write',
'    X_{2r}[G,<,v]. Check in the Lean source (ColoringNumbers.lean,',
'    OrderedCovers.lean, CoverConstruction.lean) that the fibre and GKS set are',
'    the same set and not transposes of each other, and that',
'    isNeighborhoodCover_wreach (OrderedCovers.lean:111) is stated about the one',
'    the design uses. A silent transpose here would break both the path-closure',
'    lemma and ctr.',
'',
'(d) Does the <A> path-closure lemma survive the peeled-graph construction? Its',
'    proof takes a witnessing walk in A with all support pi-above u and applies',
'    dropUntil. If clusters are actually computed as balls in the peeled graph,',
'    check the two descriptions agree AS SETS at every u, not just for the',
'    minimal one -- the peeling deletes v after processing, so later clusters are',
'    computed in a smaller graph than A.',
'',
'(e) The ctr identity. Rev 4 claims pi-min(ball_R(v)) = pi-min(wreach_pi(A,R,v))',
'    in "roughly six lines" and that ball_R(v) subset X_{ctr v} is tex:1443',
'    transcribed. Write both proofs out in full and say whether six lines is',
'    honest, whether they need mem_wreach_iff to be stated in the direction the',
'    design uses, and whether ctr really "falls out of the same sweep for free".',
'',
'(f) THE THRESHOLD. Rev 4 states the side condition n >= f(r,epsilon)',
'    (tex:1255-1263) and disposes of it in one sentence: "absorbable -- below',
'    threshold the arena is of constant size". Attack that. The design applies',
'    cover at EVERY node; below threshold what does the program actually DO, what',
'    does it cost, and -- the part the sentence skips -- does the cover DEGREE',
'    bound D(N) and hence (star) still hold for those nodes, since (star) is what',
'    the whole recursion rests on? Check whether exists_cover_degree threshold',
'    freedom (Rev 4 says it is quantified over every subgraph copy on its own',
'    carrier, with m = 0 discharged separately) really covers the small-arena',
'    case, or whether the recursion needs a bound that only the thresholded time',
'    theorem supplies.',
'',
'(g) O7 / section 8 step 0b says the time bound is an import of Nesetril-Ossona',
'    de Mendez 2005 and is BLOCKED. Confirm or refute that this is really',
'    unobtainable from what is here: is there any route to the cover time bound',
'    that does not need NOdM 2005 -- e.g. accepting a weaker exponent, or a',
'    different ordering algorithm, or is the wcol ordering itself (Corollary',
'    thm:order, and Lax12 exists_augChain_subpolynomial) also deferred to the',
'    same paper? Say exactly which statement must be imported and with what',
'    hypotheses. If the honest answer is that TWO things must be imported, say so.',
    ].join('\n'),
  },
  {
    key: 'rev4-seams',
    prompt: [
'GROUP D: read algorithm-v2 Rev 4 as ONE document and find where the Rev 4',
'patches contradict each other, contradict what they left behind, or leave a hole.',
'',
'Rev 4 was produced by applying nine verified findings plus their consequences to',
'Rev 3, in one pass, in a hurry. Each fix was made in isolation. Round 3 found',
'that exactly this process is what produced the defects it reported. Your job is',
'the interactions.',
'',
'Known surfaces to start from, but do not stop there:',
'',
'(a) THE LEAF, and it may be the best one. Section 0 <B> strikes the inference',
'    "Splitter wins in l rounds, so at depth l the arena is edgeless" as',
'    "verbatim the inference section 9 records as underivable", replacing it with',
'    reachedR_length_lt, "which bounds the play length without naming a batch".',
'    But section 5 line 10 still returns BotTables when "j = l or A has no',
'    edges", and section 6.4 BotTables is correct ONLY on an edgeless arena --',
'    and section 3 <B> warns in as many words that a wrong l "would have called',
'    BotTables on an arena with edges and section 6.4 premise would fail',
'    SILENTLY". So: what makes the arena edgeless at depth l under the ReachedR',
'    precondition? Is it derivable (a play that could continue would contradict',
'    reachedR_length_lt -- but that needs "arena has an edge implies a legal round',
'    can be recorded", i.e. reachedR_descend applied in the contrapositive), or',
'    has Rev 4 struck the justification while keeping the line that needs it?',
'    Read reachedR_descend and reachedR_length_lt statements before answering.',
'',
'(b) D3 <B> deletes the order-preservation clause and the dead-vertex correction',
'    from the compaction lemma, on the argument that step 3-prime comes BEFORE',
'    locality, transports DistFO.Sat which "has no order-sensitive constructor",',
'    and that "no greedy value ever crosses the compaction boundary". Check every',
'    step of that: DistFO constructors and Sat (DistFO.lean), ScatterSentence.Sat',
'    (:180-184) and greedySet (:126-133), Locality.lean:104-110. Then check',
'    nothing else in the document still depends on the deleted clauses -- section',
'    4 keeps up monotone "for the CSR build", section 6.1 keeps "S given sorted".',
'    If the clauses really are phantom, is section 8 step 4a now correctly priced,',
'    and does the section 5 chain step 3-prime still typecheck as stated',
'    (a bijection Fin N <-> X, in which direction, and against which of',
'    B_full/B_full-prime/B)?',
'',
'(c) Section 4 operation table is the document inventory of charged operations',
'    and Rev 4 rewrote it. Check it against section 5 pseudocode and section 6',
'    line by line, operation for operation and charge for charge. Is every',
'    operation section 5 performs in the table (pad_m? eval? the cover peeling',
'    sweep? the per-node scratch array of section 6.1? the table allocation of',
'    line 14?), and is every table row used? Does any charge in the table',
'    disagree with the same routine section 6 heading?',
'',
'(d) The l*R channel factor propagates into: section 4 restrict charge, section',
'    6.1 aggregate, section 7 a, section 11 peak, and P1b. Follow it through all',
'    five and report every place it is dropped or silently renamed.',
'',
'(e) Section 8 was renumbered again (step 0 split into 0a/0b). Check every',
'    cross-reference in the document (sections 2, 3, 4, 5, 6, 7, 9, 11 all point',
'    into section 8) and check no step depends on a later one. In particular',
'    step 1 says it "is not independent of step 0b" while step 0b is BLOCKED on an',
'    external paper -- is the whole plan therefore blocked, or is there a',
'    parameterised form of step 1 that can proceed? Rev 4 does not say.',
'',
'(f) Section 9: O6 is declared closed and O7 opened. Is the O6 closure argument',
'    (section 11 <B>: cover degree <= carrier size, so Sigma_u |X_u| <= N^2',
'    unconditionally) actually complete now that the channel adds Theta(l*R*n)',
'    and the peeling sweep may need a second copy of A? Re-derive the peak with',
'    every live object Rev 4 introduced and check it is still <= c*(|x|+1)^2.',
'',
'(g) Anything Rev 4 still says that any of the three prior audits refuted but',
'    Rev 4 failed to delete, and anything Rev 4 asserts about what a previous',
'    audit found that the record does not support (section 12 is a summary of',
'    round 3 -- check it against the findings it claims to record, where you can).',
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
      'produced the findings below about algorithm-v2 Rev 4. Refute THE AUDITOR.\n' +
      'Open every citation yourself; do not take it on trust. Search the whole\n' +
      'document before agreeing that something is missing -- Rev 4 is long and the\n' +
      'answer is often in another section, or in a <B> paragraph the auditor did\n' +
      'not read. Default to upheld=false unless convinced. Where the auditor did\n' +
      'arithmetic, redo it independently rather than checking his.\n\n' +
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
  'unaudited <B> material of algorithm-v2 Rev 4:\n\n' + JSON.stringify(clean, null, 2) +
  '\n\nThis is the fourth round. Rounds 2 and 3 found 20 and 9 findings; the trend\n' +
  'is the signal the reader cares about. The reader is about to spend a week of\n' +
  'proving effort against this plan and has asked whether it is safe to do so.\n' +
  'Answer these, each with the evidence:\n' +
  '1. Is section 7 arithmetic right THIS time, and is delta = eps/(l+1) the\n' +
  '   correct split given what the cover actually costs? State the corrected\n' +
  '   recurrence and constant condition in full if they moved.\n' +
  '2. Does the Rev 4 downward channel (per-vertex support lists) work, or is it\n' +
  '   the second failed channel design in two revisions? If it fails, is there a\n' +
  '   third design, and does its failure change the algorithm or only the proof?\n' +
  '3. Is the cover section (6.2, 4, 11) now an honest account of what GKS do?\n' +
  '   Name every statement that must be imported from outside this repository.\n' +
  '4. Is Rev 4 internally consistent enough to be built from? Is the leaf case\n' +
  '   sound?\n' +
  '5. Given rounds 2, 3 and 4, is the audit converging? Say plainly whether a\n' +
  '   fifth round is worth running or whether the remaining risk is now in the\n' +
  '   proving rather than in the design.\n' +
  '6. If you had to name the ONE thing most likely to cost the reader a week,\n' +
  '   what is it?\n' +
  'Report as findings with ids q1..q6 plus anything else worth carrying. Be\n' +
  'blunt and rank by what changes the plan.',
  { label: 'synthesize:verdict', phase: 'Synthesize', schema: FINDINGS, effort: 'high' }
)

return { groups: clean, verdict }
