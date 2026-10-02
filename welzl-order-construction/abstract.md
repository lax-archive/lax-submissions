This submission proves the randomized near-linear Welzl-order theorem in
Lax195003. On valid graph inputs with linear neighborhood complexity, the
word-RAM program runs in O((n+m) log n) time, succeeds on at least two thirds
of finite random tapes, and returns an order with crossing number at most
12 c^2 ceil(log2 n)^2. Its readable source is compiled and supplied as the
existential witness in the proof package.

Supporting lemmas on contraction, crossings, sampling, collisions, and
reconstruction remain as proved helper results in the proof package; they
are not separate concepts.
