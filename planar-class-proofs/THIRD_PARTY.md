# Plane separation and the utility graph

The files under `proofs/Lax303502Proofs/Topology/`, except `GraphBase.lean`,
are adapted from Álvaro Begué's
[Jordan–Schönflies formalization](https://github.com/alonamaloh/schoenflies-lean),
commit `05a43d29cde026618777db3d4e4316204ccca237`.
The original copyright and Apache 2.0 license notices are retained in every
adapted file. The submission's `LICENSE` contains the Apache 2.0 license.

The selected files are the transitive import dependencies of
`Schoenflies.Graph.K33Land`. Their relative paths match the original paths
below `Schoenflies/`. They include the polygonal Jordan theorem, polygonal
crosscut separation, and the proof that nine arcs cannot realize the utility
graph. The general Jordan–Schönflies theorem is not imported.

Changes for this submission relocate declarations into `Lax303502Proofs`,
rewrite import paths, make implicit parameters explicit, and adapt proofs
to Lean and mathlib v4.33.0. `GraphBase.lean` supplies local aliases for the
underlying mathlib graph type and deletion operations; it introduces no
mathematical assumptions. The adapter in `K33Nonplanar.lean` connects the
ported result to the original Lax68 drawing and subdivision definitions.

The port preserves the original authorship. Neither an upstream build claim
nor a source citation substitutes for compilation and kernel replay of the
ported declarations in this submission.
