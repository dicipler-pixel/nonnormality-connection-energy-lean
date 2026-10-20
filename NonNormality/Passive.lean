/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Analysis.Matrix.Order
import NonNormality.TwoBooks

/-!
# Passive fields: the connection book never exceeds the opposite book

For positive semidefinite `a`, `b` one has `re (trace (a * b)) ≥ 0`, hence
`‖a − b‖² ≤ ‖a + b‖²`. On an edge with positive semidefinite blocks this is `E₋,e ≤ E₊,e`, i.e.
the per-edge reflection coefficient has modulus at most one.

## Main results

* `NonNormality.re_trace_mul_nonneg_of_posSemidef`: `0 ≤ re (trace (a * b))` for positive
  semidefinite `a`, `b` (through the positive square root `CFC.sqrt b`).
* `NonNormality.norm_sub_sq_le_norm_add_sq_of_posSemidef`: `‖a − b‖² ≤ ‖a + b‖²`.
* `NonNormality.norm_sub_conj_sq_le_norm_add_conj_sq_of_posSemidef`: the edge form
  `‖Dᵢ − U Dⱼ Uᴴ‖² ≤ ‖Dᵢ + U Dⱼ Uᴴ‖²`.
-/

open Matrix
open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder

namespace NonNormality

variable {m : Type*} [Fintype m]

/-- For positive semidefinite `a`, `b`, `re (trace (a * b)) ≥ 0`. -/
theorem re_trace_mul_nonneg_of_posSemidef {a b : Matrix m m ℂ} (ha : a.PosSemidef)
    (hb : b.PosSemidef) : 0 ≤ RCLike.re (trace (a * b)) := by
  classical
  have hs : CFC.sqrt b * CFC.sqrt b = b :=
    CFC.sqrt_mul_sqrt_self b (Matrix.nonneg_iff_posSemidef.2 hb)
  have hH : (CFC.sqrt b).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg b)).isHermitian
  have htr := (ha.conjTranspose_mul_mul_same (CFC.sqrt b)).trace_nonneg
  rw [hH.eq] at htr
  rw [← hs, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
  exact (RCLike.nonneg_iff.1 htr).1

/-- **Passive fields.** For positive semidefinite `a`, `b`, `‖a − b‖² ≤ ‖a + b‖²`. -/
theorem norm_sub_sq_le_norm_add_sq_of_posSemidef {a b : Matrix m m ℂ} (ha : a.PosSemidef)
    (hb : b.PosSemidef) : ‖a - b‖ ^ 2 ≤ ‖a + b‖ ^ 2 := by
  rw [norm_sq_add_eq, norm_sq_sub_eq, frobeniusInner_eq_re_trace_mul ha.isHermitian]
  linarith [re_trace_mul_nonneg_of_posSemidef ha hb]

/-- **Passive fields, edge form.** For positive semidefinite blocks `Dᵢ`, `Dⱼ` and any transport
`U`, `‖Dᵢ − U Dⱼ Uᴴ‖² ≤ ‖Dᵢ + U Dⱼ Uᴴ‖²`: the connection book never exceeds the opposite book on
the edge, so the per-edge reflection coefficient has modulus at most one. -/
theorem norm_sub_conj_sq_le_norm_add_conj_sq_of_posSemidef {Di Dj : Matrix m m ℂ}
    (hi : Di.PosSemidef) (hj : Dj.PosSemidef) (U : Matrix m m ℂ) :
    ‖Di - U * Dj * Uᴴ‖ ^ 2 ≤ ‖Di + U * Dj * Uᴴ‖ ^ 2 :=
  norm_sub_sq_le_norm_add_sq_of_posSemidef hi (hj.mul_mul_conjTranspose_same U)

end NonNormality
