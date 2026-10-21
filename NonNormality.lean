/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import NonNormality.Frobenius
import NonNormality.SelfCommutator
import NonNormality.Holonomy
import NonNormality.Flatten
import NonNormality.Opposite
import NonNormality.AntiHolonomy
import NonNormality.TwoBooks
import NonNormality.Passive
import NonNormality.Admissible

/-!
# Non-normality is connection energy

Formalization of J. Beasley, *Non-normality is connection energy* (17 September 2026,
Zenodo record 22804072, v7): the Frobenius self-commutator energy of a block transport operator
`diagonal D + A` on a finite graph equals the connection energy of `D` for the connection on
endomorphisms induced by `A`, so the operator is normal exactly when `D` is parallel, and on a
connected graph the parallel Hermitian sections correspond to the Hermitian matrices fixed by the
holonomy.

`NonNormality.Opposite` adds the opposite identity: `‖H * H - Hᴴ * Hᴴ‖² / 8` is the anticommutator
(opposite) energy `∑_{{i, j} ∈ E} ‖D i + A i j * D j * (A i j)ᴴ‖²`, the two energies add up to
`2 ∑ i, deg i * ‖D i‖²`, and `H` normal with `H * H` Hermitian forces `D i = 0` on every vertex
with an edge.

Version 11 ("the two books"): `NonNormality.AntiHolonomy` proves the parity-twisted holonomy
kernel (the mirror of identity (3) for the opposite energy) and the bipartite sign flip;
`NonNormality.TwoBooks` proves the constant shift (`4 c A`), the trace split, the per-edge duality
`P² + V² + L² = 1`, the projector budget `4 k`, the bipartite double cover and the product of the
two books; `NonNormality.Passive` proves `E₋,e ≤ E₊,e` for positive semidefinite blocks.

`NonNormality.Admissible` proves the admissibility defect (a sector reflection flips the trace
form exactly, up to twice the trace form of the within-sector coupling), the half swap, the
first- and second-order overlap identities of a curve of idempotents, the two-outcome records
(`tanh` of half the log-odds) and Koide's `2 / 3` as a Born half and as a null vector.
-/
