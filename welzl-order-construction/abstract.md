# Constructing Welzl Orders: Algorithm and Correctness

This submission develops a proof of the construction in Dreier and Kuske,
*Near-Linear Time Computation of Welzl Orders on Graphs with Linear
Neighborhood Complexity* (arXiv:2602.14625v1). The intended endpoint is the
randomized algorithmic claim in Lax195003. That claim is not yet discharged.

The development separates the explicit contraction and reconstruction
algorithm from its deterministic output guarantee, sampling probability,
and word-RAM running time. Initial claims isolate twin insertion, the
stability of crossings under membership changes, and the geometric size
recurrence. The full proof must additionally connect these claims to the
registered graph and machine definitions.
