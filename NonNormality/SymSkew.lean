/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.LinearAlgebra.Matrix.Hermitian
import NonNormality.Frobenius

/-!
# Self-commutator of a Hermitian matrix plus a small perturbation

The June 2026 lattice papers study `H(ε) = H₀ + ε E` with `H₀` symmetric (normal) and a
"dominantly skew" coupling `E`. This file records the exact (not asymptotic) commutator algebra.

## Main results

* `NonNormality.selfCommutator_add_smul`: for `Sᴴ = S` and a self-adjoint scalar `ε`,
  `[S + ε E, (S + ε E)ᴴ] = ε [E - Eᴴ, S] + ε² [E, Eᴴ]`, exactly. Only the skew part of `E`
  enters at first order; the Hermitian part of `E` enters only through `ε² [E, Eᴴ]`.
* `NonNormality.selfCommutator_add_smul_of_skew`: if `Eᴴ = -E`, then
  `[S + ε E, (S + ε E)ᴴ] = 2 ε [E, S]` with **no** `ε²` term.
* `NonNormality.selfCommutator_add`: for any `H = S + K` with `Sᴴ = S`, `Kᴴ = -K`,
  `[H, Hᴴ] = 2 [K, S]`.
* `NonNormality.isStarNormal_add_iff_commute`: such an `H` is normal iff `S` and `K` commute.
* `NonNormality.isStarNormal_iff_commute_add_sub`: a complex matrix `H` is normal iff
  `H + Hᴴ` and `H - Hᴴ` commute.
* `NonNormality.norm_selfCommutator_add_smul_of_skew`: Frobenius norm
  `‖[H(ε), H(ε)ᴴ]‖ = 2 |ε| ‖[K, S]‖`, exactly linear in `ε`.

## References

* J. Beasley, *Spectral Stability Across Obstruction Interfaces in Geometric Transport Systems*
  (June 24, 2026), §3 (commutator expansion) and App. A.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace NonNormality

variable {n R : Type*} [Fintype n]

section Algebra

variable [CommRing R] [StarRing R]

/-- **Exact commutator expansion.** -/
theorem selfCommutator_add_smul {S : Matrix n n R} (hS : Sᴴ = S) (E : Matrix n n R) {ε : R}
    (hε : star ε = ε) :
    (S + ε • E) * (S + ε • E)ᴴ - (S + ε • E)ᴴ * (S + ε • E) =
      ε • ((E - Eᴴ) * S - S * (E - Eᴴ)) + ε ^ 2 • (E * Eᴴ - Eᴴ * E) := by
  rw [conjTranspose_add, conjTranspose_smul, hS, hε]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_sub, smul_smul, sq]
  abel

/-- **Skew coupling.** If `Eᴴ = -E` the expansion terminates at first order:
`[S + ε E, (S + ε E)ᴴ] = 2 ε [E, S]`. -/
theorem selfCommutator_add_smul_of_skew {S : Matrix n n R} (hS : Sᴴ = S) {E : Matrix n n R}
    (hE : Eᴴ = -E) {ε : R} (hε : star ε = ε) :
    (S + ε • E) * (S + ε • E)ᴴ - (S + ε • E)ᴴ * (S + ε • E) = (2 * ε) • (E * S - S * E) := by
  rw [selfCommutator_add_smul hS E hε, hE]
  simp only [sub_neg_eq_add, Matrix.mul_neg, Matrix.neg_mul, ← two_smul R E,
    Matrix.smul_mul, Matrix.mul_smul, neg_add_cancel, smul_zero, add_zero]
  module

/-- **Hermitian plus skew-Hermitian.** `[S + K, (S + K)ᴴ] = 2 [K, S]`. -/
theorem selfCommutator_add {S K : Matrix n n R} (hS : Sᴴ = S) (hK : Kᴴ = -K) :
    (S + K) * (S + K)ᴴ - (S + K)ᴴ * (S + K) = (2 : R) • (K * S - S * K) := by
  have h := selfCommutator_add_smul_of_skew hS hK (star_one R)
  rwa [one_smul, mul_one] at h

end Algebra

section Field

variable [Field R] [CharZero R] [StarRing R]

/-- A Hermitian-plus-skew-Hermitian matrix is normal iff the two parts commute. -/
theorem isStarNormal_add_iff_commute {S K : Matrix n n R} (hS : Sᴴ = S) (hK : Kᴴ = -K) :
    IsStarNormal (S + K) ↔ Commute S K := by
  rw [isStarNormal_iff, Commute, SemiconjBy, star_eq_conjTranspose, eq_comm, ← sub_eq_zero,
    selfCommutator_add hS hK, smul_eq_zero, or_iff_right two_ne_zero, sub_eq_zero, Commute,
    SemiconjBy, eq_comm]

/-- For a nonzero self-adjoint scalar `ε`, `S + ε K` is normal iff `S` and `K` commute. -/
theorem isStarNormal_add_smul_iff_commute {S K : Matrix n n R} (hS : Sᴴ = S) (hK : Kᴴ = -K)
    {ε : R} (hε : star ε = ε) (hε0 : ε ≠ 0) :
    IsStarNormal (S + ε • K) ↔ Commute S K := by
  rw [isStarNormal_iff, Commute, SemiconjBy, star_eq_conjTranspose, eq_comm, ← sub_eq_zero,
    selfCommutator_add_smul_of_skew hS hK hε, smul_eq_zero,
    or_iff_right (mul_ne_zero two_ne_zero hε0), sub_eq_zero, Commute, SemiconjBy, eq_comm]

end Field

/-- A complex matrix is normal iff its Hermitian and skew-Hermitian parts commute; equivalently
iff `H + Hᴴ` and `H - Hᴴ` commute. -/
theorem isStarNormal_iff_commute_add_sub (H : Matrix n n ℂ) :
    IsStarNormal H ↔ Commute (H + Hᴴ) (H - Hᴴ) := by
  have hS : ((2 : ℂ)⁻¹ • (H + Hᴴ))ᴴ = (2 : ℂ)⁻¹ • (H + Hᴴ) := by
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    simp
  have hK : ((2 : ℂ)⁻¹ • (H - Hᴴ))ᴴ = -((2 : ℂ)⁻¹ • (H - Hᴴ)) := by
    rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, ← smul_neg, neg_sub]
    simp
  have hH : (2 : ℂ)⁻¹ • (H + Hᴴ) + (2 : ℂ)⁻¹ • (H - Hᴴ) = H := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul ℂ H, smul_smul, inv_mul_cancel₀ two_ne_zero,
      one_smul]
  conv_lhs => rw [← hH]
  rw [isStarNormal_add_iff_commute hS hK, Commute.smul_left_iff₀ (inv_ne_zero two_ne_zero),
    Commute.smul_right_iff₀ (inv_ne_zero two_ne_zero)]

/-- **Linear scaling.** For Hermitian `S`, skew-Hermitian `K` and real `ε`,
`‖[S + ε K, (S + ε K)ᴴ]‖ = 2 |ε| ‖K S - S K‖` (Frobenius norm). -/
theorem norm_selfCommutator_add_smul_of_skew {S K : Matrix n n ℂ} (hS : Sᴴ = S) (hK : Kᴴ = -K)
    (ε : ℝ) :
    ‖(S + (ε : ℂ) • K) * (S + (ε : ℂ) • K)ᴴ - (S + (ε : ℂ) • K)ᴴ * (S + (ε : ℂ) • K)‖ =
      2 * |ε| * ‖K * S - S * K‖ := by
  rw [selfCommutator_add_smul_of_skew hS hK (Complex.conj_ofReal ε), norm_smul, norm_mul,
    Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, mul_assoc]

end NonNormality
