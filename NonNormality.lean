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
-/
