The word RAM is the machine the modern analysis of algorithms is
stated on. It is a random access machine in the register-transfer
format of Cook and Reckhow — a memory of cells addressed by number and
no other storage, an instruction that sets one cell from one or two
others, indirect addressing through a cell holding an address, an input
and an output tape, jumps against zero — with its numbers bounded
rather than its instruction set: cells hold `w`-bit words, and
multiplication, division, shifts and the bitwise operations each cost
one time unit because on words each of them is one instruction of a
real machine. This submission fixes the archive's canonical encoding of
that model. It carries two definitions and no proof obligations: the
machine, whose semantics is parameterized by the word length and obeys
one uniform truncation rule — every value the machine produces and
every address it uses is taken modulo `2 ^ w` — and the predicate
saying that a program computes a function of words within a time bound
on a set of admissible inputs, the running time being the machine's own
step count rather than an annotation carried alongside the program.
Neither is a claim, so neither is stated as one; the review question is
faithfulness of the model, and the formalization notes give the word
model and its sources, the truncation rule and what follows from it,
the constant-cost derivations of the remaining standard operations —
disjunction, exclusive or, the right shift, the remainder and the
comparisons — and the machine's halting behaviour and time measure.
