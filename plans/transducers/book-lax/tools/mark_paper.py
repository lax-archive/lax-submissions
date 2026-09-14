#!/usr/bin/env python3
"""Assemble the paper folder of the umbrella submission from the book sources.

    python3 tools/mark_paper.py            # writes transducers-book/paper/

Copies main.tex, the chapter files, the macros, the bibliography and the
pictures into `transducers-book/paper/`, and wraps every theorem-like
environment that carries a formalised `\\label` with the archive's markers:

    % lax begin Lax765601.KrohnRhodes
    \\begin{theorem}[Krohn-Rhodes Theorem]
    \\label{thm:krohn-rhodes} ...
    \\end{theorem}
    % lax end

and the `\\begin{proof} … \\end{proof}` that follows such an environment with
the marker of the archive proof (`% lax begin Lax765601Proofs.Results.…`).
Several concept ids on one environment nest. The map from labels to ids is
the table `CONCEPTS` below; it is the one place that records which concept
formalises which numbered result, so keep it in step with the concept files.
"""
import os, re, shutil, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # lax/
BOOK = os.path.dirname(ROOT)
PAPER = os.path.join(ROOT, "transducers-book", "paper")

A, B, C, L, K, D = "Lax765601", "Lax132576", "Lax916827", "Lax314295", "Lax709149", "Lax194892"

# label -> (concept ids, proof id or None). A proof id names the theorem of the
# proof package that discharges the (first) concept's statement.
CONCEPTS = {
    # introduction
    "def:continuity": ([f"{A}.Continuity"], None),
    # Part A
    "def:mealy-machine": ([f"{A}.MealyMachine"], None),
    "thm:equivalence-decidable-mealy": ([f"{A}.MealyEquivalenceBound"], f"{A}Proofs.Results.eval_eq_iff_short"),
    "thm:composition-mealy": ([f"{A}.MealyComposition"], f"{A}Proofs.Results.isMealy_comp"),
    "thm:continuity-mealy": ([f"{A}.MealyContinuity"], f"{A}Proofs.Results.continuous_of_isMealy"),
    "def:prime-mealy-machines": ([f"{A}.PrimeMealyMachines"], None),
    "thm:krohn-rhodes": ([f"{A}.KrohnRhodes"], f"{A}Proofs.Results.compClosure_primeMealy_of_isMealy"),
    "def:map-lifting": ([f"{A}.MapLifting"], None),
    "lem:map-lifting-decomposition-mealy": ([f"{A}.MapLiftingDecomposition"], f"{A}Proofs.Results.compClosure_mapLift"),
    "lem:Mealy-map-lifting": ([f"{A}.StateTransformationDecomposition"], f"{A}Proofs.Results.compClosure_stateTransTransducer"),
    "lem:reversible-composition": ([f"{A}.ReversibleComposition"], f"{A}Proofs.Results.isReversibleMealy_comp"),
    "def:aperiodic-mealy": ([f"{A}.Aperiodicity"], None),
    "thm:aperiodic-mealy": ([f"{A}.AperiodicMealy", f"{A}.FlipFlopsOfAperiodic", f"{A}.AperiodicOfFlipFlops"],
                            f"{A}Proofs.Results.aperiodic_iff_compClosure_flipFlop"),
    "claim:aperiodic-pumping": ([f"{A}.AperiodicPumping"], f"{A}Proofs.Results.aperiodic_iff_pumping"),
    "lemma:derivatives": ([f"{A}.MealyDerivatives", f"{A}.Derivatives"], f"{A}Proofs.Results.isMealy_iff_derivatives"),
    "lem:aperiodicity-minimal-machine": ([f"{A}.AperiodicityMinimalMachine"], f"{A}Proofs.Results.aperiodic_iff_transAperiodic"),
    # Part B
    "def:nfa-with-output": ([f"{B}.RationalRelations", f"{B}.LabelledAutomata"], None),
    "def:rational-relation": ([f"{B}.RationalRelations"], None),
    "thm:composition-rational-relations": ([f"{B}.RationalComposition"], f"{B}Proofs.Results.isRationalRel_comp"),
    "thm:continuity-rational-relations": ([f"{B}.RationalContinuity"], f"{B}Proofs.Results.relContinuous_of_isRationalRel"),
    "thm:undecidable-equivalence-rational-relations": ([f"{B}.RationalEquivalenceUndecidable"], f"{B}Proofs.Results.not_computablePred_codeRel_eq"),
    "claim:homomorphism-complement-rational": ([f"{B}.HomomorphismComplement"], f"{B}Proofs.Results.isRationalRel_ne_homOf"),
    "def:rational-function": ([f"{B}.RationalFunctions"], None),
    "def:bimachine": ([f"{B}.Bimachines"], None),
    "thm:bimachines": ([f"{B}.RationalUnambiguousBimachine", f"{B}.UnambiguousOfRational", f"{B}.BimachineOfRational", f"{B}.RationalOfBimachine"],
                       f"{B}Proofs.Results.tfae_rational_unambiguous_bimachine"),
    "lemma:eliminate-epsilon-transitions": ([f"{B}.EpsilonEliminationExtended", f"{B}.EpsilonEliminationFinite", f"{B}.EpsilonFreeAutomata"],
                                            f"{B}Proofs.Results.exists_extended_epsilonFree"),
    "lem:uniformisation": ([f"{B}.Uniformisation"], f"{B}Proofs.Results.exists_isUnambiguousRel_le"),
    "thm:rational-primes": ([f"{B}.RationalPrimes", f"{B}.PrimesOfRational", f"{B}.RationalOfPrimes", f"{B}.PrimeRationalFunctions"],
                            f"{B}Proofs.Results.isRationalFun_iff_compClosure_primeRational"),
    "thm:rational-is-mealy-characterisation": ([f"{B}.RationalMealyCharacterisation"], f"{B}Proofs.Results.isMealy_iff_of_isRationalFun"),
    "def:weighted-automaton": ([f"{B}.WeightedAutomata"], None),
    "thm:equivalence-weighted-automata": ([f"{B}.WeightedEquivalenceDecidable", f"{B}.WeightedCodes"], f"{B}Proofs.Results.decidable_wcodeEval_eq"),
    "thm:equivalence-rational-functions": ([f"{B}.RationalEquivalenceDecidable", f"{B}.TransducerCodes"], f"{B}Proofs.Results.decidable_codeRel_eq"),
    "lem:closure-weighted-automata-precomposition": ([f"{B}.WeightedPrecomposition"], f"{B}Proofs.Results.isWeighted_comp_of_isRationalFun"),
    "thm:characterisation-rational-functions-weighted-automata": ([f"{B}.RationalViaWeighted", f"{B}.RationalOfWeightedPrecomposition"],
                                                                  f"{B}Proofs.Results.isRationalFun_iff_weighted_precomp"),
    "thm:zeroness-weighted-automata": ([f"{B}.WeightedZeronessDecidable"], f"{B}Proofs.Results.decidable_wcodeEval_eq_zero"),
    "thm:mealy-machine-independent": ([f"{B}.MealyMachineIndependent", f"{A}.ElementaryProperties"], f"{B}Proofs.Results.isMealy_iff"),
    "thm:decide-if-mealy": ([f"{B}.MealyDecidable"], f"{B}Proofs.Results.decidable_isMealy"),
    "lem:decide-if-length-preserving": ([f"{B}.LengthPreservingDecidable"], f"{B}Proofs.Results.decidable_lengthPreserving"),
    "claim:typing-length-preserving": ([f"{B}.LengthPreservingTyping"], f"{B}Proofs.Results.lengthPreserving_iff_typing"),
    "lem:characterisation-length-preserving": ([f"{B}.LengthPreservingNormalForm"], f"{B}Proofs.Results.exists_nfao_length_eq"),
    "thm:sequential-function-independent": ([f"{B}.SequentialCharacterisation", f"{B}.SequentialTransducers"], f"{B}Proofs.Results.isSequential_iff"),
    "def:left-distance": ([f"{B}.LeftDistance"], None),
    "thm:subsequential-functions": ([f"{B}.SubsequentialCharacterisation", f"{B}.SubsequentialTransducers"], f"{B}Proofs.Results.isSubsequential_iff"),
    "thm:machine-independent-rational-functions": ([f"{B}.RationalMachineIndependent"], f"{B}Proofs.Results.isRationalFun_iff"),
    # Part C, sections 1-3
    "def:regular-functions": ([f"{C}.RegularFunctions"], None),
    "thm:regular-functions-are-continuous-and-closed-under-composition": ([f"{C}.RegularContinuity", f"{C}.RegularComposition"], f"{C}Proofs.Results.continuous_of_isRegularFun"),
    "lem:reversal-duplication-continuous": ([f"{C}.ReversalContinuous", f"{C}.DuplicationContinuous"], f"{C}Proofs.Results.continuous_reverse"),
    "lem:map-lifting-continuous": ([f"{C}.MapLiftingContinuity"], f"{C}Proofs.Results.continuous_mapLift"),
    "thm:decidable-equivalence-regular": ([f"{C}.RegularEquivalenceDecidable", f"{C}.TwoWayCodes"], f"{C}Proofs.Results.decidable_twoWayCodeRel_eq"),
    "def:two-way-transducer": ([f"{C}.TwoWayTransducers"], None),
    "thm:continuity-2dfas": ([f"{C}.TwoWayContinuity"], f"{C}Proofs.Results.continuous_of_isTwoWay"),
    "lem:compute-configuration-graph": ([f"{C}.ConfigurationGraphRational", f"{C}.ConfigurationGraphs"], f"{C}Proofs.Results.isRationalFun_enc"),
    "lem:check-if-output-string-of-configuration-graph-belongs-to-L": ([f"{C}.ConfigurationGraphOutput"], f"{C}Proofs.Results.isRegular_encOutputLang"),
    "thm:composition-of-two-way-transducers": ([f"{C}.TwoWayComposition"], f"{C}Proofs.Results.isTwoWay_comp"),
    "lem:2dfa-precomposition-with-mealy": ([f"{C}.TwoWayMealyPrecomposition"], f"{C}Proofs.Results.isTwoWay_comp_isMealy"),
    "cor:2dfa-closure-under-composition": ([f"{C}.TwoWayRationalPrecomposition"], f"{C}Proofs.Results.isTwoWay_comp_isRationalFun"),
    "cor:2dfa-computes-all-regular-functions": ([f"{C}.TwoWayOfRegular"], f"{C}Proofs.Results.isTwoWay_of_isRegularFun"),
    "thm:2dfa-decomposition-into-primes": ([f"{C}.TwoWayIffRegular", f"{C}.RegularOfTwoWay"], f"{C}Proofs.Results.isTwoWay_iff_isRegularFun"),
    "lem:regular-closure-properties": ([f"{C}.RegularMapLifting", f"{C}.RegularConcatenation", f"{C}.RegularConditional"], f"{C}Proofs.Results.isRegularFun_mapLift"),
    "claim:conditional": ([f"{C}.RegularSum"], f"{C}Proofs.Results.exists_isRegularFun_sum"),
    "lem:output-of-snake-graph-is-regular": ([f"{C}.SnakeLemma", f"{C}.SnakeGraphs"], f"{C}Proofs.Results.isRegularFun_snakeOut"),
    "def:sst": ([f"{C}.StreamingStringTransducers"], None),
    "theorem:sst-two-way-equivalence": ([f"{C}.SSTIffRegular", f"{C}.SSTOfRegular", f"{C}.RegularOfSST"], f"{C}Proofs.Results.isSST_iff_isRegularFun"),
    # Part C, section 4
    "thm:mso-logic-languages": ([f"{L}.BuchiTheorem", f"{L}.MSODefinableOfRegular", f"{L}.RegularOfMSODefinable", f"{L}.MSOLogic"], f"{L}Proofs.Results.isRegular_iff_msoDefinable"),
    "lem:mso-free-variables": ([f"{L}.MSOFreeVariables"], f"{L}Proofs.Results.isRegular_annotated"),
    "def:mso-relabeling": ([f"{L}.MSORelabellings"], None),
    "thm:logic-rational-functions": ([f"{L}.RationalIffRelabelling", f"{L}.RelabellingOfRational", f"{L}.RationalOfRelabelling"], f"{L}Proofs.Results.isRationalFun_iff_isMSORelabelling"),
    "claim:mso-annotation-regular": ([f"{L}.MSOAnnotationRegular"], f"{L}Proofs.Results.isRegular_annotation"),
    "def:mso-transduction": ([f"{L}.MSOTransductions"], None),
    "thm:logic-regular-functions": ([f"{L}.MSOTransductionIffRegular", f"{L}.RegularOfMSOTransduction", f"{L}.MSOTransductionOfRegular"], f"{L}Proofs.Results.isMSOTransduction_iff_isRegularFun"),
    "lem:logic-precomputation": ([f"{L}.LogicPrecomputation"], f"{L}Proofs.Results.exists_rational_precomputation"),
    "thm:logic-aperiodic": ([f"{L}.FOIffAperiodic", f"{L}.AperiodicOfFO", f"{L}.FOOfAperiodic"], f"{L}Proofs.Results.foDefinable_iff_aperiodic_dfa"),
    "def:k-types": ([f"{L}.KTypes"], None),
    "lem:k-types-fo-equivalence": ([f"{L}.KTypesFOEquivalence"], f"{L}Proofs.Results.tp_eq_iff_fo_equiv"),
    "lem:k-types-properties": ([f"{L}.KTypesRefinement", f"{L}.KTypesCongruence", f"{L}.KTypesAperiodicity"], f"{L}Proofs.Results.tp_eq_of_tp_succ_eq"),
    "thm:fo-rational-functions": ([f"{L}.FORelabellingIffAperiodicBimachine", f"{L}.AperiodicBimachineOfFORelabelling", f"{L}.FORelabellingOfAperiodicBimachine"], f"{L}Proofs.Results.isFORelabelling_iff_isAperiodicBimachine"),
    # Part C, section 5
    "def:types": ([f"{K}.Types"], None),
    "def:regular-functions-on-types-under-string-representation": ([f"{K}.RegularUnderRepresentation"], None),
    "def:regular-terms": ([f"{K}.RegularTerms"], None),
    "thm:regular-terms": ([f"{K}.RegularOfTerm"], f"{K}Proofs.Results.isRegularUnderRepr_of_isRegularTermFun"),
    # Part D
    "ex:marked-squaring": ([f"{D}.MarkedSquaring"], None),
    "def:polyregular-functions": ([f"{D}.PolyregularFunctions"], None),
    "thm:polyregular-functions-are-continuous": ([f"{D}.PolyregularContinuity"], f"{D}Proofs.Results.continuous_of_isPolyregular"),
    "thm:for-transducers-are-polyregular": ([f"{D}.ForIffPolyregular", f"{D}.ForOfPolyregular", f"{D}.PolyregularOfFor", f"{D}.ForTransducers"], f"{D}Proofs.Results.isPolyregular_iff_isForTransducer"),
    "def:prenex-normal-form-for-transducers": ([f"{D}.ForTransducers"], None),
    "lemma:prenex-normal-form": ([f"{D}.PrenexNormalForm"], f"{D}Proofs.Results.exists_prenexForm"),
    "lem:for-closed-under-composition": ([f"{D}.ForComposition"], f"{D}Proofs.Results.isForTransducer_comp"),
    "thm:pebble-are-continuous": ([f"{D}.PebbleContinuity", f"{D}.PebbleTransducers"], f"{D}Proofs.Results.continuous_of_isPebbleTransducer"),
    "lem:reachability-pebble-automaton": ([f"{D}.PebbleReachability", f"{D}.PebbleConfigurationEncoding"], f"{D}Proofs.Results.exists_regular_reachLang"),
    "claim:reachability-basic-run": ([f"{D}.BalancedRunReachability"], f"{D}Proofs.Results.exists_regular_balancedLang"),
    "thm:pebble-are-for": ([f"{D}.PebbleIffFor", f"{D}.ForOfPebble", f"{D}.PebbleOfFor"], f"{D}Proofs.Results.isPebbleTransducer_iff_isForTransducer"),
    "lem:children-of-configuration-in-pebble-run": ([f"{D}.ChildrenOfConfiguration", f"{D}.ChildConfigurationGraphs"], f"{D}Proofs.Results.exists_forTransducer_children"),
    "claim:from-configuration-to-child-configuration-graph": ([f"{D}.ChildGraphOfConfiguration"], f"{D}Proofs.Results.exists_forTransducer_childGraph"),
    "claim:from-child-configuration-graph-to-children": ([f"{D}.ChildrenOfChildGraph"], f"{D}Proofs.Results.exists_forTransducer_cgOut"),
}

# submission markers on the part introductions
PART_INTROS = {
    "partAMealy/intro.tex": "lax-765601",
    "partBRational/intro.tex": "lax-132576",
    "partCRegular/intro.tex": "lax-916827",
    "partDPolyregular/intro.tex": "lax-194892",
}

ENVS = r"(theorem|lemma|claim|corollary|definition|conjecture|fact|proposition|myexample|subclaim|example)"
BEGIN = re.compile(r"\\begin\{" + ENVS + r"\}")


def find_env(lines, label_line):
    """The (start, end) line indices of the innermost theorem-like environment
    containing the line `label_line`."""
    depth, start = 0, None
    for i in range(label_line, -1, -1):
        for m in re.finditer(r"\\(begin|end)\{" + ENVS + r"\}", lines[i]):
            pass
        ends = len(re.findall(r"\\end\{" + ENVS + r"\}", lines[i]))
        begins = len(re.findall(r"\\begin\{" + ENVS + r"\}", lines[i]))
        if i == label_line:
            begins_before_label = len(re.findall(r"\\begin\{" + ENVS + r"\}", lines[i].split("\\label")[0]))
            if begins_before_label:
                start = i
                break
            continue
        depth += ends - begins
        if depth < 0:
            start = i
            break
    if start is None:
        return None
    name = re.search(r"\\begin\{" + ENVS + r"\}", lines[start]).group(1)
    depth = 0
    for j in range(start, len(lines)):
        depth += len(re.findall(r"\\begin\{" + re.escape(name) + r"\}", lines[j]))
        depth -= len(re.findall(r"\\end\{" + re.escape(name) + r"\}", lines[j]))
        if depth == 0:
            return start, j
    return None


def find_proof(lines, after):
    """The (start, end) of a `proof` environment starting right after line `after`
    (blank lines and comments in between allowed)."""
    i = after + 1
    while i < len(lines) and (lines[i].strip() == "" or lines[i].lstrip().startswith("%")):
        i += 1
    if i >= len(lines) or not lines[i].lstrip().startswith("\\begin{proof}"):
        return None
    depth = 0
    for j in range(i, len(lines)):
        depth += lines[j].count("\\begin{proof}")
        depth -= lines[j].count("\\end{proof}")
        if depth == 0:
            return i, j
    return None


def mark_file(src, dst, wanted):
    lines = open(src).read().split("\n")
    inserts = {}  # line index -> (list of before-lines, list of after-lines)
    found = []
    for label, (ids, proof) in wanted.items():
        for i, l in enumerate(lines):
            if f"\\label{{{label}}}" in l:
                env = find_env(lines, i)
                if env is None:
                    sys.exit(f"{src}: no environment around \\label{{{label}}}")
                s, e = env
                inserts.setdefault(s, [[], []])[0].extend(f"% lax begin {cid}" for cid in ids)
                inserts.setdefault(e, [[], []])[1].extend(["% lax end"] * len(ids))
                if proof:
                    pr = find_proof(lines, e)
                    if pr:
                        ps, pe = pr
                        inserts.setdefault(ps, [[], []])[0].append(f"% lax begin {proof}")
                        inserts.setdefault(pe, [[], []])[1].append("% lax end")
                found.append(label)
                break
    out = []
    for i, l in enumerate(lines):
        before, after = inserts.get(i, ([], []))
        out.extend(before)
        out.append(l)
        if after:
            out.extend(after)
            # an own-line `% lax end` wants a blank-line neighbour
            if i + 1 < len(lines) and lines[i + 1].strip() != "":
                out.append("")
    open(dst, "w").write("\n".join(out))
    return found


def main():
    if os.path.isdir(PAPER):
        shutil.rmtree(PAPER)
    os.makedirs(PAPER)
    for f in ["macros.sty", "transducer-macros.sty", "knowledges.tex", "bib.bib",
              "transducer-book-pics.pdf", "preface.tex", "2dfa-primes.tex"]:
        shutil.copy(os.path.join(BOOK, f), PAPER)
    # main.tex: switch off the issue/review margin notes, keep the Lean flags
    main_tex = open(os.path.join(BOOK, "main.tex")).read()
    main_tex = main_tex.replace("\\usepackage{transducer-macros}\n",
        "\\usepackage{transducer-macros}\n\\showissuesfalse\\showreviewsfalse\n", 1)
    open(os.path.join(PAPER, "main.tex"), "w").write(main_tex)
    found = set()
    for rel in ["intro.tex"] + [os.path.join(d, f) for d in
                ["partAMealy", "partBRational", "partCRegular", "partDPolyregular"]
                for f in sorted(os.listdir(os.path.join(BOOK, d))) if f.endswith(".tex")]:
        src = os.path.join(BOOK, rel)
        dst = os.path.join(PAPER, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        found |= set(mark_file(src, dst, CONCEPTS))
        if rel in PART_INTROS:
            body = open(dst).read().rstrip("\n")
            open(dst, "w").write(f"% lax begin {PART_INTROS[rel]}\n{body}\n% lax end\n\n")
    missing = set(CONCEPTS) - found
    if missing:
        sys.exit("labels not found: " + ", ".join(sorted(missing)))
    print(f"marked {len(found)} labelled environments; paper folder at {PAPER}")


if __name__ == "__main__":
    main()
