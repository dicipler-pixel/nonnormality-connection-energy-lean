/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import NonNormality.Frobenius
import NonNormality.SelfCommutator
import NonNormality.Holonomy
import NonNormality.Flatten
import NonNormality.Kernel
import NonNormality.SymSkew
import NonNormality.Evenness
import NonNormality.Lattice
import NonNormality.QGT
import NonNormality.Localization
import NonNormality.Counterexamples

/-!
# Non-normality is connection energy

Formalization of J. Beasley, *Non-normality is connection energy* (17 September 2026,
Zenodo record 22804072, v7): the Frobenius self-commutator energy of a block transport operator
`diagonal D + A` on a finite graph equals the connection energy of `D` for the connection on
endomorphisms induced by `A`, so the operator is normal exactly when `D` is parallel, and on a
connected graph the parallel Hermitian sections correspond to the Hermitian matrices fixed by the
holonomy.

Branch `findings-v2` adds the findings of the earlier drafts and June 2026 companion papers that
were not in v7 (`Kernel`, `SymSkew`, `Evenness`, `Lattice`, `QGT`, `Localization`) and true
counterexamples to claims in those originals (`Counterexamples`); see `FINDINGS_INVENTORY.md`.
-/
