/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Auxiliary facts about the Frobenius norm

* `NonNormality.frobenius_norm_sq`: `‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2`.
* `NonNormality.frobenius_norm_sq_eq_re_trace`: `‖A‖ ^ 2 = re (trace (Aᴴ * A))` over `RCLike 𝕜`.
* `NonNormality.frobenius_norm_unitary_mul`, `NonNormality.frobenius_norm_mul_unitary`:
  the Frobenius norm is invariant under multiplication by a unitary matrix on either side.

All statements use the Frobenius norm, enabled with `open scoped Matrix.Norms.Frobenius`.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace NonNormality

variable {l m n 𝕜 α : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- The square of the Frobenius norm is the sum of the squares of the norms of the entries. -/
theorem frobenius_norm_sq [SeminormedAddCommGroup α] (A : Matrix m n α) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

variable [RCLike 𝕜]

/-- Over `RCLike 𝕜`, the squared Frobenius norm is the real part of `trace (Aᴴ * A)`. -/
theorem frobenius_norm_sq_eq_re_trace (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = RCLike.re (trace (Aᴴ * A)) := by
  rw [frobenius_norm_sq, Finset.sum_comm]
  simp only [trace, diag, mul_apply, conjTranspose_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Left multiplication by a unitary matrix preserves the Frobenius norm. -/
theorem frobenius_norm_unitary_mul [DecidableEq m] {U : Matrix m m 𝕜}
    (hU : U ∈ unitaryGroup m 𝕜) (A : Matrix m n 𝕜) : ‖U * A‖ = ‖A‖ := by
  have hsq : ‖U * A‖ ^ 2 = ‖A‖ ^ 2 := by
    rw [frobenius_norm_sq_eq_re_trace, frobenius_norm_sq_eq_re_trace, conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff').1 hU, Matrix.one_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- Right multiplication by a unitary matrix preserves the Frobenius norm. -/
theorem frobenius_norm_mul_unitary [DecidableEq n] (A : Matrix m n 𝕜) {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : ‖A * U‖ = ‖A‖ := by
  rw [← frobenius_norm_conjTranspose (A * U), conjTranspose_mul, ← star_eq_conjTranspose U,
    frobenius_norm_unitary_mul (Unitary.star_mem hU), frobenius_norm_conjTranspose]

end NonNormality
