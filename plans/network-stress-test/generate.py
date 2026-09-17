#!/usr/bin/env python3
"""Generate the Lean sources of the network-stress-test submission (lax-771644).

Run it from anywhere; it rewrites `network-stress-test/concepts` and
`network-stress-test/proofs` from the tables below.
"""
import os

ROOT = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "network-stress-test")
ID = "Lax771644"
P = ID + "Proofs"

concepts = []   # dicts: name, title, type, desc, notes, imports(extra), statements
proofs = []     # dicts: module, thm, conclusion, assumptions[(fullname,a,b)], A,B, desc, strategy

def concept(name, title, ctype, desc, notes, statements=(), extra_imports=(), raw=None):
    concepts.append(dict(name=name, title=title, type=ctype, desc=desc, notes=notes,
                         statements=list(statements), extra=list(extra_imports), raw=raw))

def proof(module, thm, conclusion, assumptions, A, B, desc, strategy, attribution=None):
    proofs.append(dict(module=module, thm=thm, conclusion=conclusion,
                       assumptions=list(assumptions), A=A, B=B, desc=desc,
                       strategy=strategy, attribution=attribution))

def full(concept_name, local):
    return f"{ID}.{concept_name}.{local}"

ATTR = ("Synthetic: written for this benchmark. The mathematics is a one-line\n"
        "divisibility weakening; only the shape of the dependency edges is the point.")

# --------------------------------------------------------------- Foundations
concept("Foundations", "The benchmark ladder", "definition",
  """Every claim in this submission is a rung of one ladder: for natural numbers
$a$ and $b$, the assertion that divisibility by $2^a$ implies divisibility by
$2^b$. The mathematics is deliberately trivial. It exists only so that this
submission's *dependency graph* can be wired into any shape at all while every
proof still genuinely applies the statements it declares as assumptions.""",
  """`Stage k n` is plain divisibility, `2 ^ k ∣ n`, and `Descent a b` is the
statement shape every axiom of this submission uses. Because `Descent a b`
holds whenever `b ≤ a`, a proof of one rung can be assembled from *any*
descending sequence of other rungs. That is what lets the proof network of this
submission take on arbitrary shapes — long chains, cycles, wide fans — without
any statement being false or any proof pretending to use an assumption it does
not.""")

# --------------------------------------------------------------- IsolatedIsland
concept("IsolatedIsland", "Isolated island (no statements, no uses)", "definition",
  """A definition-concept that declares no statement, imports no other concept of
this submission, and is imported by none. It is here to check that the drawing
places a concept with no incident edge at all.""",
  """The marker predicate is never used anywhere. Its only purpose is to give
this module a declaration so that it is a concept rather than an empty file.""",
  extra_imports=(), raw="""/-- A marker predicate that nothing in this submission ever mentions. -/
def marker : Prop := ∀ n : ℕ, n = n
""")

# ------------------------------------------------- 1. sibling, conclusion right
concept("SiblingConclusionRight", "Sibling proof with the conclusion on the right", "theorem",
  """Three numbered statements, where statement 3 is proved from statements 1 and 2
of the same concept. This is the plain sibling-proof shape: the turnstile sits
below the rightmost dock and both of its assumption arrows come from docks to
its left.""",
  """The three rungs are chosen so that the composite really is the composite:
$12 \\to 11$ followed by $11 \\to 10$ gives $12 \\to 10$.""",
  [("s1", 12, 11, "Descent from stage 12 to stage 11."),
   ("s2", 11, 10, "Descent from stage 11 to stage 10."),
   ("s3", 12, 10, "Descent from stage 12 to stage 10, the composite of the two rungs above.")])
proof("SiblingConclusionRight", "s1", full("SiblingConclusionRight","s1"), [], 12, 11,
      "Statement 1 holds outright, by weakening the ladder.", "One application of the ladder's weakening lemma.")
proof("SiblingConclusionRight", "s2", full("SiblingConclusionRight","s2"), [], 11, 10,
      "Statement 2 holds outright, by weakening the ladder.", "One application of the ladder's weakening lemma.")
proof("SiblingConclusionRight", "s3", full("SiblingConclusionRight","s3"),
      [(full("SiblingConclusionRight","s1"),12,11), (full("SiblingConclusionRight","s2"),11,10)], 12, 10,
      "Statement 3 is the composite of its two siblings.",
      "Apply statement 1 to descend to stage 11, then statement 2 to descend to stage 10.")

# -------------------------------------------------- 2. sibling, conclusion left
concept("SiblingConclusionLeft", "Sibling proof with the conclusion on the left", "theorem",
  """The mirror image of the previous concept: statement 1 is proved from statements
2 and 3. The turnstile therefore sits below the *leftmost* dock while both of
its assumption arrows arrive from docks to its right.""",
  """Same ladder, different band of rungs, so that the two concepts cannot be
confused when both are on screen.""",
  [("s1", 22, 20, "Descent from stage 22 to stage 20, the composite of the two rungs below."),
   ("s2", 22, 21, "Descent from stage 22 to stage 21."),
   ("s3", 21, 20, "Descent from stage 21 to stage 20.")])
proof("SiblingConclusionLeft", "s1", full("SiblingConclusionLeft","s1"),
      [(full("SiblingConclusionLeft","s2"),22,21), (full("SiblingConclusionLeft","s3"),21,20)], 22, 20,
      "Statement 1 is the composite of its two siblings to the right.",
      "Apply statement 2, then statement 3.")
proof("SiblingConclusionLeft", "s2", full("SiblingConclusionLeft","s2"), [], 22, 21,
      "Statement 2 holds outright.", "One application of the ladder's weakening lemma.")
proof("SiblingConclusionLeft", "s3", full("SiblingConclusionLeft","s3"), [], 21, 20,
      "Statement 3 holds outright.", "One application of the ladder's weakening lemma.")

# ------------------------------------------------ 3. sibling, conclusion middle
concept("SiblingConclusionMiddle", "Sibling proof with the conclusion in the middle", "theorem",
  """Statement 2 is proved from statements 1 and 3, so the turnstile sits below the
middle dock with one assumption arriving from the left and one from the right.""",
  """Again the same ladder in a fresh band of rungs.""",
  [("s1", 32, 31, "Descent from stage 32 to stage 31."),
   ("s2", 32, 30, "Descent from stage 32 to stage 30, the composite of its two neighbours."),
   ("s3", 31, 30, "Descent from stage 31 to stage 30.")])
proof("SiblingConclusionMiddle", "s1", full("SiblingConclusionMiddle","s1"), [], 32, 31,
      "Statement 1 holds outright.", "One application of the ladder's weakening lemma.")
proof("SiblingConclusionMiddle", "s2", full("SiblingConclusionMiddle","s2"),
      [(full("SiblingConclusionMiddle","s1"),32,31), (full("SiblingConclusionMiddle","s3"),31,30)], 32, 30,
      "Statement 2 is the composite of the statements on either side of it.",
      "Apply statement 1, then statement 3.")
proof("SiblingConclusionMiddle", "s3", full("SiblingConclusionMiddle","s3"), [], 31, 30,
      "Statement 3 holds outright.", "One application of the ladder's weakening lemma.")

# -------------------------------------------------------- 4. mixed proof
concept("MixedSiblingAndForeign", "Mixed proof: one sibling and one foreign assumption", "theorem",
  """Statement 2 is proved from statement 1 of this concept *and* from statement 3
of `SiblingConclusionRight`. One assumption arrow is local, the other crosses to
another concept box, so the drawing has to place a turnstile that is a sibling
proof on one side and a cross-concept proof on the other.""",
  """The foreign rung $12 \\to 10$ picks up exactly where the local rung
$42 \\to 40$ leaves off, after a free weakening from stage 40 to stage 12.""",
  [("s1", 42, 40, "Descent from stage 42 to stage 40."),
   ("s2", 42, 10, "Descent from stage 42 all the way down to stage 10.")])
proof("MixedSiblingAndForeign", "s1", full("MixedSiblingAndForeign","s1"), [], 42, 40,
      "Statement 1 holds outright.", "One application of the ladder's weakening lemma.")
proof("MixedSiblingAndForeign", "s2", full("MixedSiblingAndForeign","s2"),
      [(full("MixedSiblingAndForeign","s1"),42,40), (full("SiblingConclusionRight","s3"),12,10)], 42, 10,
      "Statement 2 chains a sibling statement into a statement of another concept.",
      "Descend with the sibling statement to stage 40, weaken to stage 12, and finish with the foreign statement.")

# ------------------------------------------------------ 5a. chain of two siblings
concept("SiblingChain", "Two sibling proofs forming a chain", "theorem",
  """Statement 2 is proved from statement 1 and statement 3 from statement 2, both
inside this one concept. The two turnstiles must be stacked so that the second
sits below the output of the first without colliding with the dock row.""",
  """Each step weakens the lower rung by one, so the chain is genuine rather than
three unrelated claims.""",
  [("s1", 52, 51, "Descent from stage 52 to stage 51."),
   ("s2", 52, 50, "Descent from stage 52 to stage 50."),
   ("s3", 52, 49, "Descent from stage 52 to stage 49.")])
proof("SiblingChain", "s1", full("SiblingChain","s1"), [], 52, 51,
      "Statement 1 holds outright.", "One application of the ladder's weakening lemma.")
proof("SiblingChain", "s2", full("SiblingChain","s2"), [(full("SiblingChain","s1"),52,51)], 52, 50,
      "Statement 2 follows from statement 1.", "Apply statement 1, then weaken one further rung.")
proof("SiblingChain", "s3", full("SiblingChain","s3"), [(full("SiblingChain","s2"),52,50)], 52, 49,
      "Statement 3 follows from statement 2.", "Apply statement 2, then weaken one further rung.")

# ------------------------------------------- 5b. two proofs of the same statement
concept("TwoProofsOneStatement", "Two sibling proofs of the same statement", "theorem",
  """Statement 3 carries two independent proofs, one from statement 1 and one from
statement 2. Two turnstiles point at the same dock.""",
  """The two routes descend through different intermediate rungs, so they really
are two different proofs and not the same term twice.""",
  [("s1", 62, 61, "Descent from stage 62 to stage 61."),
   ("s2", 62, 60, "Descent from stage 62 to stage 60."),
   ("s3", 62, 55, "Descent from stage 62 to stage 55, reachable through either route.")])
proof("TwoProofsOneStatement", "s1", full("TwoProofsOneStatement","s1"), [], 62, 61,
      "Statement 1 holds outright.", "One application of the ladder's weakening lemma.")
proof("TwoProofsOneStatement", "s2", full("TwoProofsOneStatement","s2"), [], 62, 60,
      "Statement 2 holds outright.", "One application of the ladder's weakening lemma.")
proof("TwoProofsOneStatement", "s3_via_s1", full("TwoProofsOneStatement","s3"),
      [(full("TwoProofsOneStatement","s1"),62,61)], 62, 55,
      "First proof of statement 3, routed through statement 1.", "Descend to stage 61 and weaken.")
proof("TwoProofsOneStatement", "s3_via_s2", full("TwoProofsOneStatement","s3"),
      [(full("TwoProofsOneStatement","s2"),62,60)], 62, 55,
      "Second proof of statement 3, routed through statement 2.", "Descend to stage 60 and weaken.")

# ---------------------------------- 6. three proofs, one sibling and two foreign
concept("ThreeProofsOneStatement", "One statement with three proofs", "theorem",
  """Statement 2 is the conclusion of three different proofs: one sibling proof from
statement 1 of this concept, and two proofs whose assumptions live in other
concepts. Three turnstiles have to fan into a single dock.""",
  """Statement 2 descends far enough that any of the three routes reaches it.""",
  [("s1", 72, 71, "Descent from stage 72 to stage 71."),
   ("s2", 72, 5, "Descent from stage 72 down to stage 5.")])
proof("ThreeProofsOneStatement", "s1", full("ThreeProofsOneStatement","s1"), [], 72, 71,
      "Statement 1 holds outright.", "One application of the ladder's weakening lemma.")
proof("ThreeProofsOneStatement", "s2_via_sibling", full("ThreeProofsOneStatement","s2"),
      [(full("ThreeProofsOneStatement","s1"),72,71)], 72, 5,
      "First proof of statement 2: the sibling route.", "Descend with statement 1 and weaken to stage 5.")
proof("ThreeProofsOneStatement", "s2_via_sibling_chain", full("ThreeProofsOneStatement","s2"),
      [(full("SiblingChain","s3"),52,49)], 72, 5,
      "Second proof of statement 2, through a statement of `SiblingChain`.",
      "Weaken to stage 52, descend with the foreign statement, weaken to stage 5.")
proof("ThreeProofsOneStatement", "s2_via_middle", full("ThreeProofsOneStatement","s2"),
      [(full("SiblingConclusionMiddle","s2"),32,30)], 72, 5,
      "Third proof of statement 2, through a statement of `SiblingConclusionMiddle`.",
      "Weaken to stage 32, descend with the foreign statement, weaken to stage 5.")

# ------------------------------------------------------------- 9. wide dock row
wide = []
for k in range(1, 12):
    wide.append((f"s{k:02d}", 100 + k, 99 + k, f"Descent from stage {100+k} to stage {99+k}."))
wide.append(("s12", 111, 100, "Descent from stage 111 to stage 100, the composite of all eleven rungs above."))
concept("WideDockRow", "A very wide dock row with a wide assumption rail", "theorem",
  """Twelve numbered statements, every one of them proved, so the dock row is as
wide as this benchmark gets. Statement 12 is a sibling proof that uses eleven of
its siblings at once, which gives the widest assumption rail in the submission.""",
  """The eleven single-step rungs compose to the twelfth statement exactly, so the
eleven assumptions of the last proof are all genuinely used.""",
  wide)
for k in range(1, 12):
    proof("WideDockRow", f"s{k:02d}", full("WideDockRow", f"s{k:02d}"), [], 100 + k, 99 + k,
          f"Statement {k} holds outright.", "One application of the ladder's weakening lemma.")
proof("WideDockRow", "s12", full("WideDockRow","s12"),
      [(full("WideDockRow", f"s{k:02d}"), 100 + k, 99 + k) for k in range(11, 0, -1)], 111, 100,
      "Statement 12 composes all eleven of its siblings.",
      "Descend one rung at a time, from stage 111 to stage 100.")

# --------------------------------------------- 10-ish. many foreign assumptions
foreign = [(full("WideDockRow","s12"),111,100),
           (full("ThreeProofsOneStatement","s1"),72,71),
           (full("TwoProofsOneStatement","s3"),62,55),
           (full("SiblingChain","s3"),52,49),
           (full("MixedSiblingAndForeign","s1"),42,40),
           (full("SiblingConclusionMiddle","s2"),32,30),
           (full("SiblingConclusionLeft","s1"),22,20),
           (full("SiblingConclusionRight","s3"),12,10)]
concept("ManyForeignAssumptions", "One proof assuming eight other concepts", "theorem",
  """A single-statement concept whose proof assumes one statement from each of eight
different concepts of this submission. Every one of those uses is coarsened by
the drawing to a single port on the assumed concept's box, so this is the test
for a wide rail of *cross-concept* assumption arrows.""",
  """The eight foreign rungs are chosen to descend, so the composite from stage 200
down to stage 10 uses each of them.""",
  [("descends_far", 200, 10, "Descent from stage 200 to stage 10, assembled from eight other concepts.")])
proof("ManyForeignAssumptions", "descends_far", full("ManyForeignAssumptions","descends_far"),
      foreign, 200, 10,
      "The long descent, assembled from one statement of each of eight concepts.",
      "Weaken into each assumed rung in turn and apply it.")

# ------------------------------------------------------ 7. cross-concept cycle
concept("CycleAlpha", "Cycle, first half", "theorem",
  """Half of a genuine cross-concept cycle: this statement is proved from the
statement of `CycleBeta`, which is in turn proved from this one. Neither becomes
proven — the archive's notion of provenness is a least fixed point — so both
should be drawn open and inside the grey display-cycle envelope.""",
  """The two statements are given the same type, which is the only way two proofs
can genuinely stand in for one another; each proof really is the other statement
and nothing else.""",
  [("alpha", 300, 290, "Descent from stage 300 to stage 290.")])
concept("CycleBeta", "Cycle, second half", "theorem",
  """The other half of the cycle with `CycleAlpha`. Its proof assumes
`CycleAlpha.alpha`, whose proof assumes this statement.""",
  """See `CycleAlpha` for why the two statements share a type.""",
  [("beta", 300, 290, "Descent from stage 300 to stage 290.")])
proof("CycleAlpha", "alpha", full("CycleAlpha","alpha"), [(full("CycleBeta","beta"),300,290)], 300, 290,
      "This statement holds if the statement of `CycleBeta` does.",
      "Apply `CycleBeta.beta` verbatim. Circular by design: the converse proof assumes this statement.")
proof("CycleBeta", "beta", full("CycleBeta","beta"), [(full("CycleAlpha","alpha"),300,290)], 300, 290,
      "This statement holds if the statement of `CycleAlpha` does.",
      "Apply `CycleAlpha.alpha` verbatim. Circular by design: the converse proof assumes this statement.")

# ---------------------------------------------------- 8. self-referential proof
concept("SelfReferentialProof", "A statement proved from itself", "theorem",
  """A one-element cycle: the only proof of this statement assumes the statement
itself. It stays unproven, and the drawing has to cope with a turnstile whose
assumption and conclusion are the same node.""",
  """Nothing subtle happens on the Lean side: an axiom may be used to prove a
theorem of its own type, and the archive then records the statement in its own
assumption set.""",
  [("selfRung", 310, 300, "Descent from stage 310 to stage 300.")])
proof("SelfReferentialProof", "selfRung", full("SelfReferentialProof","selfRung"),
      [(full("SelfReferentialProof","selfRung"),310,300)], 310, 300,
      "The statement, proved from itself.",
      "Apply the statement to its own goal. Circular by design; the archive's least fixed point leaves it unproven.")

# ------------------------------------- 10. statement whose name is its concept's
concepts.append(dict(name="WholeConceptAssumption",
  title="A statement whose name is its concept's name", type="theorem",
  desc="""This concept declares one statement named exactly like the concept module
itself, alongside an ordinary numbered sibling. It is the closest the format
comes to a *whole-concept* assumption: a proof assuming it names the concept id
rather than a name below it.""",
  notes="""Lean is happy to have a constant `Lax771644.WholeConceptAssumption` and a
constant `Lax771644.WholeConceptAssumption.s2` at the same time, exactly as it
has `Nat` and `Nat.succ`. The archive treats the first as an ordinary statement
of the module it originates in, so its identifier collides with the concept's
own identifier — which is the edge case this module exists to pin down.""",
  statements=[("s2", 320, 318, "Descent from stage 320 to stage 318.")], extra=[], raw=None,
  bare=("WholeConceptAssumption", 320, 319, "Descent from stage 320 to stage 319, declared with the concept's own name.")))
proof("WholeConceptAssumption", "bare", f"{ID}.WholeConceptAssumption", [], 320, 319,
      "The concept-named statement holds outright.", "One application of the ladder's weakening lemma.")
proof("WholeConceptAssumption", "s2", full("WholeConceptAssumption","s2"),
      [(f"{ID}.WholeConceptAssumption",320,319)], 320, 318,
      "The numbered sibling follows from the concept-named statement.",
      "Apply the concept-named statement and weaken one rung.")

# ---------------------------------------------- 11. open root and an open chain
concept("OpenRoot", "An open statement nothing proves", "theorem",
  """A single-statement concept with no proof at all. Everything downstream of it
stays unproven, which is what the next two concepts are for.""",
  """No proof module mentions this statement as a conclusion.""",
  [("openRung", 400, 390, "Descent from stage 400 to stage 390. Deliberately left unproven.")])
concept("OpenMiddle", "Middle of an open chain", "theorem",
  """Proved from `OpenRoot`, which is unproven, so this statement is unproven too
although it has a proof. The drawing should show a complete turnstile above an
open dock.""",
  """Proven *relative to* `OpenRoot.openRung`, in the spec's terminology.""",
  [("middleRung", 400, 380, "Descent from stage 400 to stage 380.")])
concept("OpenLeaf", "End of an open chain", "theorem",
  """Proved from `OpenMiddle`, and therefore unproven at two removes from the open
root.""",
  """Same as `OpenMiddle`, one link further down.""",
  [("leafRung", 400, 370, "Descent from stage 400 to stage 370.")])
proof("OpenMiddle", "middleRung", full("OpenMiddle","middleRung"), [(full("OpenRoot","openRung"),400,390)], 400, 380,
      "Follows from the open root statement.", "Apply the open statement and weaken one further rung.")
proof("OpenLeaf", "leafRung", full("OpenLeaf","leafRung"), [(full("OpenMiddle","middleRung"),400,380)], 400, 370,
      "Follows from the middle of the open chain.", "Apply the middle statement and weaken one further rung.")

# ------------------------------------------------------- 12. deep linear chain
for k in range(1, 10):
    nm = f"Chain{k:02d}"
    b = 510 - k
    concept(nm, f"Deep chain, link {k} of 9", "theorem",
      f"""Link {k} of a linear chain of nine single-statement concepts, each proved from
the previous one. The chain exists to make the layout engine draw a long, deep
path with no branching.""",
      """Each link weakens the previous rung by one, so the chain is a genuine
composition rather than nine restatements.""",
      [("rung", 510, b, f"Descent from stage 510 to stage {b}.")])
    if k == 1:
        proof(nm, "rung", full(nm,"rung"), [], 510, b, "The first link holds outright.",
              "One application of the ladder's weakening lemma.")
    else:
        prev = f"Chain{k-1:02d}"
        proof(nm, "rung", full(nm,"rung"), [(full(prev,"rung"),510,b+1)], 510, b,
              f"Link {k} follows from link {k-1}.", "Apply the previous link and weaken one rung.")

# ------------------------------------------------------------- 12. long names
LONG = "AVeryLongConceptNameForTestingLabelWrappingInTheProofNetworkFigure"
LONGS1 = "everyDescentAlongTheBenchmarkLadderSurvivesWeakeningOfItsUpperRung"
LONGS2 = "theSecondDeliberatelyOverlongStatementNameInThisConceptModule"
concept(LONG, "A deliberately overlong concept title that exists only to see how the proof network figure wraps, truncates or overflows a label nobody would ever write in a real submission", "theorem",
  """Long module name, long title, long statement names. Nothing here is about
mathematics; the concept is a ruler for label wrapping.""",
  """Both statements are ordinary rungs of the benchmark ladder.""",
  [(LONGS1, 600, 599, "Descent from stage 600 to stage 599, under a needlessly long name."),
   (LONGS2, 600, 598, "Descent from stage 600 to stage 598, under a second needlessly long name.")])
proof(LONG, "first", full(LONG, LONGS1), [], 600, 599,
      "The first overlong statement holds outright.", "One application of the ladder's weakening lemma.")
proof(LONG, "second", full(LONG, LONGS2), [(full(LONG, LONGS1),600,599)], 600, 598,
      "The second overlong statement follows from the first.", "Apply the first statement and weaken one rung.")

# ---------------------------------------------------------------- 12. unicode
concept("UnicodeNames", "Ünïcode: $\\mu$-descent and $\\varepsilon$–$\\delta$ weakening (ℵ₀ rungs, ∀∃, 中文)", "theorem",
  """A concept whose title and whose statement names carry non-ASCII characters, to
check that the figure's labels, tooltips and anchors survive them. The Greek
letters have no mathematical meaning here.""",
  """`εδ_descent` sorts before `μ_descent` by code point, so the concept-named
docks come out in the order ε, μ and the sibling proof again has its conclusion
on the left.""",
  [("εδ_descent", 610, 608, "Descent from stage 610 to stage 608."),
   ("μ_descent", 610, 609, "Descent from stage 610 to stage 609.")])
proof("UnicodeNames", "mu", full("UnicodeNames","μ_descent"), [], 610, 609,
      "The $\\mu$ statement holds outright.", "One application of the ladder's weakening lemma.")
proof("UnicodeNames", "epsilonDelta", full("UnicodeNames","εδ_descent"),
      [(full("UnicodeNames","μ_descent"),610,609)], 610, 608,
      "The $\\varepsilon$–$\\delta$ statement follows from the $\\mu$ statement.",
      "Apply the other statement and weaken one rung.")

# -------------------------------------------------- 13. external submission use
concepts.append(dict(name="ExternalPrimes", title="Primality claims restated from lax-242665", type="theorem",
  desc="""Two statements phrased over the notion of primality of *An Introduction to
Lax* (`lax-242665`), each discharged by the corresponding statement of that
submission. They exist so that this submission's proof network contains external
nodes belonging to another archive record.""",
  notes="""The statements are verbatim copies of `lax-242665`'s two claims, so each
proof is the foreign statement itself. Importing `Lax242665.Primes` in the
concept package also puts an external node into the concept DAG.""",
  statements=[], extra=["Lax242665.Primes"], raw="""/-- Every natural number greater than `1` has a prime divisor, in the sense of
`lax-242665`. -/
axiom e1_has_prime_divisor : ∀ n : ℕ, 1 < n → ∃ p : ℕ, Lax242665.Primes.Prime p ∧ p ∣ n

/-- Beyond every natural number lies a prime, in the sense of `lax-242665`. -/
axiom e2_has_larger_prime : ∀ n : ℕ, ∃ p : ℕ, Lax242665.Primes.Prime p ∧ n < p
"""))

# --------------------------------------------------------------- render helpers
def wrap(text):
    return text.strip("\n")

def concept_file(c):
    imports = ["import Mathlib.Data.Nat.Notation"]
    if c["name"] not in ("Foundations", "IsolatedIsland", "ExternalPrimes"):
        imports.append(f"import {ID}.Foundations")
    for e in c["extra"]:
        imports.append(f"import {e}")
    body = []
    if c["name"] == "Foundations":
        body.append("""/-- `Stage k n` says that `n` is divisible by `2 ^ k`. -/
def Stage (k n : ℕ) : Prop := 2 ^ k ∣ n

/-- `Descent a b` is the one statement shape this submission uses: every natural
number divisible by `2 ^ a` is divisible by `2 ^ b`. -/
def Descent (a b : ℕ) : Prop := ∀ n : ℕ, Stage a n → Stage b n""")
    if c.get("raw"):
        body.append(c["raw"].strip("\n"))
    bare = c.get("bare")
    lines = []
    lines += imports
    lines.append("")
    lines.append("/-!")
    lines.append("---")
    lines.append(f"title: {c['title']}")
    lines.append(f"type: {c['type']}")
    lines.append("---")
    lines.append(wrap(c["desc"]))
    lines.append("")
    lines.append("# Formalization notes")
    lines.append("")
    lines.append(wrap(c["notes"]))
    lines.append("-/")
    lines.append("")
    if bare:
        lines.append(f"namespace {ID}")
        lines.append("")
        lines.append(f"/-- {bare[3]} -/")
        lines.append(f"axiom {bare[0]} : Foundations.Descent {bare[1]} {bare[2]}")
        lines.append("")
        lines.append(f"end {ID}")
        lines.append("")
    lines.append(f"namespace {ID}.{c['name']}")
    lines.append("")
    for b in body:
        lines.append(b)
        lines.append("")
    for (nm, a, bb, doc) in c["statements"]:
        lines.append(f"/-- {doc} -/")
        lines.append(f"axiom {nm} : Foundations.Descent {a} {bb}")
        lines.append("")
    lines.append(f"end {ID}.{c['name']}")
    return "\n".join(lines) + "\n"

def proof_term(pr):
    A, B = pr["A"], pr["B"]
    asm = pr["assumptions"]
    if not asm:
        return " :=\n  descent {} {} (by omega)".format(A, B)
    out = [" := by", "  intro n hn", f"  have h0 : Stage {A} n := hn"]
    cur = A
    for i, (nm, a, b) in enumerate(asm, start=1):
        assert a <= cur, (pr["thm"], a, cur)
        out.append(f"  have h{i} : Stage {b} n := {nm} n (weaken {cur} {a} (by omega) h{i-1})")
        cur = b
    assert B <= cur, (pr["thm"], B, cur)
    out.append(f"  exact weaken {cur} {B} (by omega) h{len(asm)}")
    return "\n".join(out)

BARE = f"{ID}.WholeConceptAssumption"

def home_module(statement_id):
    """The concept module a statement id belongs to."""
    if statement_id == BARE:
        return BARE
    return statement_id.rsplit(".", 1)[0]

def annotation(pr):
    lines = ["/--", "---", f"conclusion: {pr['conclusion']}"]
    if pr["assumptions"]:
        lines.append("assumptions:")
        for nm in sorted({nm for (nm, _, _) in pr["assumptions"]}):
            lines.append(f"  - {nm}")
    lines += ["---", wrap(pr["desc"]), "", "# Proof strategy", "", wrap(pr["strategy"]), "",
              "# Attribution", "", wrap(pr.get("attribution") or ATTR), "-/"]
    return lines

def proof_file(module, prs):
    mods = {f"{ID}.{module}"}
    for pr in prs:
        mods.add(home_module(pr["conclusion"]))
        for (nm, _, _) in pr["assumptions"]:
            mods.add(home_module(nm))
    lines = [f"import {P}.Ladder"] + [f"import {m}" for m in sorted(mods)]
    lines += ["", "/-!", f"Proofs for the concept `{ID}.{module}`.", "-/", "",
              f"namespace {P}.{module}", "", f"open {ID}.Foundations", f"open {P}.Ladder", ""]
    for pr in prs:
        lines += annotation(pr)
        lines.append(f"theorem {pr['thm']} : Descent {pr['A']} {pr['B']}{proof_term(pr)}")
        lines.append("")
    lines.append(f"end {P}.{module}")
    return "\n".join(lines) + "\n"

EXTERNAL_PROOFS = f"""import {ID}.ExternalPrimes
import Lax242665.PrimeDivisor
import Lax242665.InfinitelyManyPrimes

/-!
Proofs for the concept `{ID}.ExternalPrimes`. Each one is the corresponding
statement of `lax-242665` verbatim, which is the whole point: the proof network
of this submission then contains external nodes owned by another record.
-/

namespace {P}.ExternalPrimes

/--
---
conclusion: {ID}.ExternalPrimes.e1_has_prime_divisor
assumptions:
  - Lax242665.PrimeDivisor.exists_prime_dvd
---
Restates the prime-divisor claim of *An Introduction to Lax*.

# Proof strategy

Apply `Lax242665.PrimeDivisor.exists_prime_dvd`; the two statements have the
same type.

# Attribution

The mathematics belongs to `lax-242665`; this submission only re-exports it so
that the benchmark drawing contains an external assumption node.
-/
theorem e1_has_prime_divisor :
    ∀ n : ℕ, 1 < n → ∃ p : ℕ, Lax242665.Primes.Prime p ∧ p ∣ n :=
  Lax242665.PrimeDivisor.exists_prime_dvd

/--
---
conclusion: {ID}.ExternalPrimes.e2_has_larger_prime
assumptions:
  - Lax242665.InfinitelyManyPrimes.exists_prime_gt
---
Restates the infinitude-of-primes claim of *An Introduction to Lax*.

# Proof strategy

Apply `Lax242665.InfinitelyManyPrimes.exists_prime_gt`; the two statements have
the same type.

# Attribution

The mathematics belongs to `lax-242665`; this submission only re-exports it so
that the benchmark drawing contains an external assumption node.
-/
theorem e2_has_larger_prime :
    ∀ n : ℕ, ∃ p : ℕ, Lax242665.Primes.Prime p ∧ n < p :=
  Lax242665.InfinitelyManyPrimes.exists_prime_gt

end {P}.ExternalPrimes
"""

# ---------------------------------------------------------------- write it out
cdir = os.path.join(ROOT, "concepts", ID)
pdir = os.path.join(ROOT, "proofs", P)
os.makedirs(cdir, exist_ok=True)
os.makedirs(pdir, exist_ok=True)

for c in concepts:
    with open(os.path.join(cdir, c["name"] + ".lean"), "w") as f:
        f.write(concept_file(c))

with open(os.path.join(ROOT, "concepts", ID + ".lean"), "w") as f:
    for c in concepts:
        f.write(f"import {ID}.{c['name']}\n")

# the ladder helper module
with open(os.path.join(pdir, "Ladder.lean"), "w") as f:
    f.write(f"""import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import {ID}.Foundations

/-!
Helpers shared by every proof of this submission. Neither declaration carries
frontmatter, so both are helpers the archive ignores.
-/

namespace {P}.Ladder

open {ID}.Foundations

/-- Weakening: a number divisible by `2 ^ a` is divisible by `2 ^ b` whenever
`b ≤ a`. -/
theorem weaken (a b : ℕ) (h : b ≤ a) {{n : ℕ}} (hn : Stage a n) : Stage b n :=
  dvd_trans (pow_dvd_pow 2 h) hn

/-- Every descent down the ladder holds outright. -/
theorem descent (a b : ℕ) (h : b ≤ a) : Descent a b :=
  fun _ hn => weaken a b h hn

end {P}.Ladder
""")

modules = {}
for pr in proofs:
    modules.setdefault(pr["module"], []).append(pr)

for m, prs in modules.items():
    with open(os.path.join(pdir, m + ".lean"), "w") as f:
        f.write(proof_file(m, prs))

with open(os.path.join(pdir, "ExternalPrimes.lean"), "w") as f:
    f.write(EXTERNAL_PROOFS)

with open(os.path.join(ROOT, "proofs", P + ".lean"), "w") as f:
    f.write(f"import {P}.Ladder\n")
    for m in sorted(set(modules) | {"ExternalPrimes"}):
        f.write(f"import {P}.{m}\n")

print(f"{len(concepts)} concepts, {sum(len(c['statements']) + (1 if c.get('bare') else 0) for c in concepts)} statements, {len(proofs)} proofs, {len(modules)+1} proof modules")
