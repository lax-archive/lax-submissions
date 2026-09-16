# Website features the *Transducers* submissions would like

Requests to the Lax website/build, collected while planning the seven
submissions of `PLAN.md`. Each entry says what the submissions do meanwhile
("workaround") so nothing here blocks the work. Numbered so `PLAN.md` can
cite them.

## 1. Cross-submission references in the paper layer

The book is one LaTeX document cut into seven papers. Part C's text says
`\cref{thm:krohn-rhodes}`, whose target is a theorem in Part A's paper
(another submission). `xr-hyper` against a shipped `.aux` snapshot of the
whole book makes the *text* right ("Theorem A.2.2"), but the link is dead.

Wanted: a way for a submission's paper to declare where a foreign label
lives, e.g. a file `paper/lax-labels.txt` (or a marker comment) mapping

    thm:krohn-rhodes  ->  lax-<A>  paper anchor thm:krohn-rhodes
    thm:krohn-rhodes  ->  Lax<A>.KrohnRhodes      (optionally: the concept)

so that the PDF/web view turns the `\cref` into a link to that submission's
paper (and, when the concept is named, to its card). Restricting the targets
to directly required submissions, as for markers, is fine.

Workaround: `xr-hyper` for the numbers; no links.

## 2. Series / collections

Seven submissions are the parts of one book. Wanted: a manifest key (or a
site-side collection) grouping submissions in order with a shared title
("*Transducers*, Part C of D") and a table of contents across them, shown on
each member's page. Also useful for lecture-note series such as lax-12.

Workaround: the abstract of each submission lists the others by id.

## 3. Reverse links from a concept to the papers that mark it

A concept card links to the passages of *its own submission's* paper. If an
umbrella submission carried the whole book (PLAN §1 D2 (b)), its markers
would name concepts of the seven part submissions; those concepts' pages
should then say "marked in the paper of lax-<umbrella>, §…". Without this
the umbrella's cards are reachable only from the umbrella.

Workaround: none; the umbrella is postponed.

## 4. Markers on helper declarations

Several numbered claims of the book are internal steps of a larger proof and
are formalised only in a reorganised form (Claims B.4.9–B.4.12, C.4.5,
C.4.14, Lemma C.4.9). They are not concepts (their Lean form is not the
book's) and not proofs (no `conclusion:`), so they cannot be marked at all.

Wanted: `% lax begin Lax<N>Proofs.someHelper` for a helper declaration,
rendered as a card with the declaration's signature and docstring, labelled
"helper" so nobody mistakes it for an endorsed statement.

Workaround: the passage is unmarked; the proof card of the enclosing
theorem names the helper in its `# Proof strategy`.

## 5. Grouping and ordering concepts on a submission page

The Part B submission has ~35 concepts, Part C §1–3 ~28. An alphabetical
list loses the book's order (definitions first, then the results of §1,
§2, …). Wanted: an optional frontmatter key on concepts, e.g.
`section: B.2 Rational functions` and/or `order: 12`, honoured by the
submission page as headings/sort keys. Today an unrecognised frontmatter key
is a build error, so this needs the schema to grow.

Workaround: concept ids are chosen so that a reader can find things, and
the abstract walks the reader through the sections.

## 6. Open statements, visibly

Two concepts will be stated without a proof anywhere (the hard half of
Theorem C.5.4, Conjecture C.1.5). The site already marks statements proven
or unproven; a distinct badge for "stated as open by the authors" (as
opposed to "the authors did not get around to it") would make the intent
clear, e.g. a frontmatter key `status: open` or `status: conjecture`.

Workaround: the concept's description says it in the first sentence.

## 7. Paper: lualatex and the web view

The book's preamble is engine-aware (`iftex`: T2A font encoding under
pdflatex for one Cyrillic citation, fontspec under lualatex). Nothing to
request, just a note that the web derivation (lualatex) will exercise the
other branch; if it diverges from the PDF the submissions accept the
"web view skipped" outcome for that submission.

## Dropped on purpose (no request)

- PDF previews of cited references (the book's web edition has them from
  `../literature/`): the bibliography entries with DOIs suffice.
- Foldable exercise solutions and the search index of the web edition.
