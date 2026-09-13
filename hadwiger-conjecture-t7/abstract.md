TODO: describe this submission.
Hadwiger's conjecture at *t* = 7 asserts that every finite graph with no
*K*₇ minor is 6-colourable. This is the first unresolved case of the
conjecture: the cases through *t* = 6 are known.

The submission introduces 6-colourability as the existence of a proper
vertex colouring by `Fin 6`. It reuses, without alteration, the connected
branch-set definition of a graph minor from the Planar Graph Classes
submission (Lax68). Its sole theorem concept states the conjecture for graphs
on the canonical finite carriers `Fin n` and deliberately has no proof, so it
is presented by the archive as an open problem.

Promising intermediate directions include imposing a bound on the
independence number, forbidding additional induced subgraphs, or requiring a
special decomposition. Recent general structural bounds improve the best
known colouring bound for graphs with no *K*ₜ minor to
`O(t log log log t)`, but they do not settle the six-colour bound at *t* = 7.
