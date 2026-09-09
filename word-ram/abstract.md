This submission defines a word RAM and computation within an explicit
instruction bound on a stated domain of inputs. Writable memory has
`2 ^ w` cells holding `w`-bit words and starts at zero. The read-only
input is a finite array supplied at initialization, with constant-time
indexed access and length metadata, a sequential read operation, and
an explicit end-of-input test. Zero remains ordinary input data. Output
is append-only, and correctness constrains the complete output list.

Arithmetic values, input values and lengths, input indices, and
data-memory addresses are reduced modulo `2 ^ w`. Program labels and
the program counter are unrestricted natural numbers. Time charges one
unit per executed instruction, including explicit `halt` and exhausted
`read`; falling outside the program costs no nonexistent instruction.
The formalization notes state fitting conditions, the input-access
convention, the additive linear cost of loading sequential input when
comparing models, and the distinction from Cook and Reckhow's terminated
input encoding. The proof package provides compiler transfer theorems,
a verified execution driver, and semantic regression proofs for raw-list
length parity, constant-time indexed input access, and exact termination
costs.
