/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# First-order cancellation: symmetric plus skew perturbations are even

*Directional Transport Geometry of Admissible Channels* (June 29, 2026), Proposition 2, claims
that the first variation of `ε ↦ Tr log (H₀ + ε E + η)` vanishes at `ε = 0` when `H₀` is
symmetric and `E` is skew. The finite-dimensional content is an exact *evenness*: transposition
maps `S + ε K` to `S - ε K`, so the determinant and the resolvent trace are even functions of
`ε` and every odd-order term vanishes, not only the first one.

## Main results

* `NonNormality.trace_mul_eq_zero_of_symm_skew`: `Tr (S K) = 0` for symmetric `S`, skew `K`.
* `NonNormality.det_add_smul_neg`: `det (S - ε K) = det (S + ε K)`.
* `NonNormality.trace_inv_sub_add_smul_neg`: `Tr (z - S + ε K)⁻¹ = Tr (z - S - ε K)⁻¹`.
* `NonNormality.deriv_det_add_smul_zero`, `NonNormality.deriv_log_det_add_smul_zero`,
  `NonNormality.deriv_trace_inv_sub_add_smul_zero`: the first derivatives at `ε = 0` vanish
  (Proposition 2 and the first-order step of Lemma 5, without contour integrals).
* `NonNormality.det_diag_add_smul_skew_two` and `NonNormality.log_det_diag_add_smul_skew_two_gt`:
  for `S = diag(a, b)` and `K = !![0, k; -k, 0]`, `det (S + ε K) = a b + ε² k²`; so for `a, b > 0`
  and `ε k ≠ 0` the log-determinant strictly *increases*. The second-order coefficient is
  `+½ ∑ |Kₙₘ|² / (λₙ λₘ) > 0`, contradicting the negative `ε²` correction of Theorem 8 of the
  same paper.
-/

open Matrix

namespace NonNormality

variable {n R : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable [CommRing R] {S K : Matrix n n R}

omit [Fintype n] [DecidableEq n] in
theorem transpose_add_smul_of_symm_skew (hS : Sᵀ = S) (hK : Kᵀ = -K) (ε : R) :
    (S + ε • K)ᵀ = S + (-ε) • K := by
  rw [transpose_add, transpose_smul, hS, hK, smul_neg, neg_smul]

/-- **Evenness of the determinant.** -/
theorem det_add_smul_neg (hS : Sᵀ = S) (hK : Kᵀ = -K) (ε : R) :
    (S + (-ε) • K).det = (S + ε • K).det := by
  rw [← transpose_add_smul_of_symm_skew hS hK, det_transpose]

/-- **Evenness of the resolvent trace.** -/
theorem trace_inv_sub_add_smul_neg (hS : Sᵀ = S) (hK : Kᵀ = -K) (z ε : R) :
    (z • (1 : Matrix n n R) - (S + (-ε) • K))⁻¹.trace =
      (z • (1 : Matrix n n R) - (S + ε • K))⁻¹.trace := by
  rw [← transpose_add_smul_of_symm_skew hS hK, ← trace_transpose, transpose_nonsing_inv,
    transpose_sub, transpose_transpose, transpose_smul, transpose_one]

end CommRing

omit [DecidableEq n] in
/-- `Tr (S K) = 0` for symmetric `S` and skew `K`. -/
theorem trace_mul_eq_zero_of_symm_skew [Field R] [CharZero R] {S K : Matrix n n R}
    (hS : Sᵀ = S) (hK : Kᵀ = -K) : (S * K).trace = 0 := by
  have h : (S * K).trace = -(S * K).trace := by
    conv_lhs => rw [← trace_transpose]
    rw [transpose_mul, hS, hK, Matrix.neg_mul, trace_neg, trace_mul_comm K S]
  linear_combination h / 2

/-- An even function has zero derivative at `0`. -/
theorem deriv_zero_of_even {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ → F}
    (hg : ∀ x, g (-x) = g x) : deriv g 0 = 0 := by
  have h : deriv (fun x => g (-x)) 0 = -deriv g (-0) := deriv_comp_neg g 0
  simp only [hg, neg_zero] at h
  have h2 : (2 : ℝ) • deriv g 0 = 0 := by rw [two_smul]; nth_rw 1 [h]; exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

section Real

variable {S K : Matrix n n ℝ}

/-- **First-order cancellation for the determinant.** -/
theorem deriv_det_add_smul_zero (hS : Sᵀ = S) (hK : Kᵀ = -K) :
    deriv (fun ε : ℝ => (S + ε • K).det) 0 = 0 :=
  deriv_zero_of_even fun ε => det_add_smul_neg hS hK ε

/-- **First-order cancellation for the log-determinant** (Proposition 2, finite-dimensional
form: `log det = Tr log`). -/
theorem deriv_log_det_add_smul_zero (hS : Sᵀ = S) (hK : Kᵀ = -K) :
    deriv (fun ε : ℝ => Real.log (S + ε • K).det) 0 = 0 :=
  deriv_zero_of_even fun ε => by simp only [det_add_smul_neg hS hK ε]

end Real

/-- **First-order cancellation for the resolvent trace.** -/
theorem deriv_trace_inv_sub_add_smul_zero {S K : Matrix n n ℂ} (hS : Sᵀ = S) (hK : Kᵀ = -K)
    (z : ℂ) :
    deriv (fun ε : ℝ => (z • (1 : Matrix n n ℂ) - (S + (ε : ℂ) • K))⁻¹.trace) 0 = 0 :=
  deriv_zero_of_even fun ε => by
    simp only [Complex.ofReal_neg, trace_inv_sub_add_smul_neg hS hK z (ε : ℂ)]

/-- The `2 × 2` model: `det (diag(a, b) + ε !![0, k; -k, 0]) = a b + ε² k²`. -/
theorem det_diag_add_smul_skew_two [CommRing R] (a b k ε : R) :
    (!![a, 0; 0, b] + ε • !![0, k; -k, 0]).det = a * b + ε ^ 2 * k ^ 2 := by
  simp [det_fin_two]
  ring

/-- **The `ε²` correction to the log-determinant is positive.** For `a, b > 0` and `ε k ≠ 0`,
`log det (diag(a, b) + ε K) > log det diag(a, b)`. -/
theorem log_det_diag_add_smul_skew_two_gt {a b k ε : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hεk : ε * k ≠ 0) :
    Real.log (a * b) < Real.log (!![a, 0; 0, b] + ε • !![0, k; -k, 0]).det := by
  rw [det_diag_add_smul_skew_two]
  have : 0 < ε ^ 2 * k ^ 2 := by rw [← mul_pow]; positivity
  exact Real.log_lt_log (by positivity) (by linarith)

end NonNormality
