/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NoncommRing
import NonNormality.Admissible

/-!
# Direction, compression, gradings and unit eigenvalues

Identities added in version 15 of *Non-normality is connection energy, and its opposite*.

## Main results

* **The books cannot see direction.** Transposing `H` negates and transposes its
  self-commutator (`transpose_selfCommutator`) and transposes `H * H - Hᴴ * Hᴴ`
  (`transpose_opposite`), so both Frobenius books of `Hᵀ` equal those of `H`, while a one-way
  block and its transpose carry signal in opposite directions.
* **The instantaneous gain ignores the transport.** For `Dᴴ = D` and `Aᴴ = -A` the Hermitian
  part of `D + A` is `D` (`add_conjTranspose_of_skew`).
* **Compression.** For a Hermitian idempotent `P` and Hermitian `H`,
  `P * H * H * P - (P * H * P) * (P * H * P) = ((1 - P) * H * P)ᴴ * ((1 - P) * H * P)`
  (`compression_defect`): compressing a square to the retained block overstates nothing and
  loses exactly the coupling to the hidden block.
* **A grading makes the determinant even in the coupling.** If `S * S = 1`, `S` commutes with
  `D` and anticommutes with `A`, then `det (D + A) = det (D - A)`
  (`det_add_eq_det_sub_of_grading`).
* **The reflection of a projector.** `(P + P - 1) * (P + P - 1) = 1` for `P * P = P`
  (`reflection_of_idempotent`).
* **The two books of a unit eigenvalue.** `‖1 - z‖² + ‖1 + z‖² = 2 + 2 ‖z‖²`
  (`normSq_one_sub_add_normSq_one_add`) and `‖1 + z‖² - ‖1 - z‖² = 4 Re z`
  (`normSq_one_add_sub_normSq_one_sub`); on the unit circle the budget is `4`, and the opposite
  book vanishes exactly at `z = -1`.
-/

open Matrix

namespace NonNormality

/-- Transposition negates and transposes the self-commutator. -/
theorem transpose_selfCommutator {n : Type*} [Fintype n] (H : Matrix n n ℂ) :
    Hᵀ * (Hᵀ)ᴴ - (Hᵀ)ᴴ * Hᵀ = -(H * Hᴴ - Hᴴ * H)ᵀ := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  rw [neg_sub]
  congr 1 <;> exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Transposition transposes the opposite operator `H * H - Hᴴ * Hᴴ`. -/
theorem transpose_opposite {n : Type*} [Fintype n] (H : Matrix n n ℂ) :
    Hᵀ * Hᵀ - (Hᵀ)ᴴ * (Hᵀ)ᴴ = (H * H - Hᴴ * Hᴴ)ᵀ := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  congr 1 <;> exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- For Hermitian `D` and skew-Hermitian `A`, the Hermitian part of `D + A` is `D`. -/
theorem add_conjTranspose_of_skew {n : Type*} {D A : Matrix n n ℂ} (hD : Dᴴ = D)
    (hA : Aᴴ = -A) : (D + A) + (D + A)ᴴ = D + D := by
  rw [Matrix.conjTranspose_add, hD, hA]
  abel

/-- **Compression.** The square of the compression falls short of the compression of the square
by exactly the coupling to the complementary block. -/
theorem compression_defect {n : Type*} [Fintype n] [DecidableEq n] {P H : Matrix n n ℂ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hH : Hᴴ = H) :
    P * H * H * P - (P * H * P) * (P * H * P) =
      ((1 - P) * H * P)ᴴ * ((1 - P) * H * P) := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hPP, sub_self, sub_zero]
  have hc : ((1 - P) * H * P)ᴴ = P * H * (1 - P) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hP, hH, Matrix.mul_assoc]
  rw [hc]
  calc P * H * H * P - (P * H * P) * (P * H * P)
        = P * H * H * P - P * H * (P * P) * H * P := by simp only [Matrix.mul_assoc]
    _ = P * H * ((1 - P) * (1 - P)) * H * P := by rw [hPP, hQ]; noncomm_ring
    _ = P * H * (1 - P) * ((1 - P) * H * P) := by simp only [Matrix.mul_assoc]

/-- **A grading makes the determinant even in the coupling.** -/
theorem det_add_eq_det_sub_of_grading {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    {S D A : Matrix n n R} (hS : S * S = 1) (hD : S * D * S = D) (hA : S * A * S = -A) :
    det (D + A) = det (D - A) := by
  have hX : S * (D + A) * S = D - A := by
    rw [mul_add, add_mul, hD, hA, sub_eq_add_neg]
  have h1 : det S * det S = 1 := by rw [← Matrix.det_mul, hS, Matrix.det_one]
  rw [← hX, Matrix.det_mul, Matrix.det_mul]
  linear_combination (-det (D + A)) * h1

/-- The reflection `2 P - 1` of an idempotent is an involution. -/
theorem reflection_of_idempotent {n R : Type*} [Fintype n] [DecidableEq n] [Ring R]
    {P : Matrix n n R} (hPP : P * P = P) : (P + P - 1) * (P + P - 1) = 1 := by
  calc (P + P - 1) * (P + P - 1) = (P * P + P * P + P * P + P * P) - (P + P + P + P) + 1 := by
        noncomm_ring
    _ = 1 := by rw [hPP]; abel

/-- The two books of a complex number against `1` add up to `2 + 2 ‖z‖²`. -/
theorem normSq_one_sub_add_normSq_one_add (z : ℂ) :
    Complex.normSq (1 - z) + Complex.normSq (1 + z) = 2 + 2 * Complex.normSq z := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im]
  ring

/-- The difference of the two books of a complex number against `1` is `4 Re z`. -/
theorem normSq_one_add_sub_normSq_one_sub (z : ℂ) :
    Complex.normSq (1 + z) - Complex.normSq (1 - z) = 4 * z.re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im]
  ring

end NonNormality
