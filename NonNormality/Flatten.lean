/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Data.Matrix.Composition
import NonNormality.SelfCommutator

/-!
# The block transport operator as an `(ι × m) × (ι × m)` complex matrix

`Matrix.comp` identifies `Matrix ι ι (Matrix m m ℂ)` with `Matrix (ι × m) (ι × m) ℂ`. This file
records that the identification commutes with `conjTranspose` and preserves the Frobenius norm,
and restates identities (1) and (2) for the flattened operator
`Matrix.comp ι ι m m ℂ (diagonal D + A)`, an honest `|ι| r × |ι| r` complex matrix.

## Main results

* `NonNormality.comp_conjTranspose`, `NonNormality.frobenius_norm_comp`.
* `NonNormality.norm_sq_selfCommutator_comp_div_eight`: identity (1) for the flattened operator.
* `NonNormality.isStarNormal_comp_iff_isParallel`: identity (2) for the flattened operator.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace NonNormality

variable {I J K L α : Type*}

/-- `Matrix.comp` commutes with `conjTranspose` (blocks are conjugate-transposed). -/
theorem comp_conjTranspose [Star α] (M : Matrix I J (Matrix K K α)) :
    comp J I K K α Mᴴ = (comp I J K K α M)ᴴ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rfl

/-- `Matrix.comp` preserves the Frobenius norm (with the Frobenius norm on the blocks). -/
theorem frobenius_norm_comp [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [NormedAddCommGroup α] (M : Matrix I J (Matrix K L α)) :
    ‖comp I J K L α M‖ = ‖M‖ := by
  have h : ‖comp I J K L α M‖ ^ 2 = ‖M‖ ^ 2 := by
    simp only [frobenius_norm_sq, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
  {G : SimpleGraph ι}

omit [DecidableEq ι] [DecidableEq m] in
/-- The flattened self-commutator is the flattening of the block self-commutator. -/
theorem comp_selfCommutator (H : Matrix ι ι (Matrix m m ℂ)) :
    comp ι ι m m ℂ H * (comp ι ι m m ℂ H)ᴴ - (comp ι ι m m ℂ H)ᴴ * comp ι ι m m ℂ H =
      comp ι ι m m ℂ (H * Hᴴ - Hᴴ * H) := by
  classical
  rw [← comp_conjTranspose]
  simp only [← compRingEquiv_apply, map_sub, map_mul]

/-- **Identity (1), flattened.** For `H = comp (diagonal D + A)` with Hermitian blocks `D i`
and a unitary connection `A` on `G`, `‖[H, Hᴴ]‖² / 8 = connectionEnergy G A D`. -/
theorem norm_sq_selfCommutator_comp_div_eight [DecidableRel G.Adj] {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    ‖comp ι ι m m ℂ (diagonal D + A) * (comp ι ι m m ℂ (diagonal D + A))ᴴ -
        (comp ι ι m m ℂ (diagonal D + A))ᴴ * comp ι ι m m ℂ (diagonal D + A)‖ ^ 2 / 8 =
      connectionEnergy G A D := by
  rw [comp_selfCommutator, frobenius_norm_comp, norm_sq_selfCommutator_div_eight hA hD]

omit [DecidableEq ι] [DecidableEq m] in
/-- `Matrix.comp` preserves normality. -/
theorem isStarNormal_comp_iff (H : Matrix ι ι (Matrix m m ℂ)) :
    IsStarNormal (comp ι ι m m ℂ H) ↔ IsStarNormal H := by
  rw [isStarNormal_iff, isStarNormal_iff, commute_iff_eq, commute_iff_eq, star_eq_conjTranspose,
    star_eq_conjTranspose, ← comp_conjTranspose, ← compRingEquiv_apply, ← compRingEquiv_apply,
    ← map_mul, ← map_mul, (compRingEquiv ι m ℂ).injective.eq_iff]

/-- **Identity (2), flattened.** `comp (diagonal D + A)` is normal iff `D` is parallel. -/
theorem isStarNormal_comp_iff_isParallel {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    IsStarNormal (comp ι ι m m ℂ (diagonal D + A)) ↔ IsParallel G A D := by
  rw [isStarNormal_comp_iff, isStarNormal_iff_isParallel hA hD]

end NonNormality
