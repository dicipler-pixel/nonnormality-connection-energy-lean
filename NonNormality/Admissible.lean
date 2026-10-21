/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import NonNormality.Opposite

/-!
# Admissible switching, the overlap expansion, the two-outcome records and Koide

The sign of the trace form `q X = re (trace (X * X)) / 2` decides which book wins. This file
proves the algebra that says when a sector reflection `Γ` (`Γ * Γ = 1`) can flip that sign, and
how the same sign governs the Born overlap of a curve of idempotents.

## Main results

* **The admissibility defect.** Split `X = A + B` with `Γ * A * Γ = -A` (coupling across the
  sectors) and `Γ * B * Γ = B` (coupling inside a sector). Then `trace (A * B) = 0`
  (`trace_mul_eq_zero_of_odd_of_even`) and
  `trace (X * X) + trace ((Γ * X) * (Γ * X)) = 2 * trace (B * B)` (`trace_swap_defect`): the
  reflection flips the trace form exactly, and the whole failure is carried by the coupling that
  stays inside a sector. `trace_swap_of_odd` is the exact case `B = 0`.
* **The half swap.** For `Γᴴ = Γ`, `Γ * Γ = 1`, `Γ * X * Γ = -X`, the Hermitian part of `Γ * X`
  is `Γ` times the skew part of `X` (`add_conjTranspose_mul_of_odd`) and conversely
  (`sub_conjTranspose_mul_of_odd`).
* **Idempotent tangents.** For `P * P = P` and `P * V + V * P = V`: `P * V * P = 0`
  (`mul_mul_eq_zero_of_tangent`), `trace (P * V) = 0` (`trace_mul_eq_zero_of_tangent`), and for a
  second-order term `V * V + V * V + P * W + W * P = W`,
  `trace (P * W) = -trace (V * V)` (`trace_mul_eq_neg_of_second_order`). This is the second-order
  coefficient of the overlap `trace (P₀ * P t)`: it falls below `trace P₀` exactly when the trace
  form of the tangent is positive.
* **Two-outcome records.** For `0 < s < 1`, `tanh (log (s / (1 - s)) / 2) = 2 s - 1`
  (`tanh_half_log_odds`) and `4 s (1 - s) = 1 - (2 s - 1)²` (`four_mul_mul_one_sub`). Any rule
  with `F s + F (1 - s) = 1` has `F (1 / 2) = 1 / 2` (`apply_half_of_complement`).
* **Koide.** For `x + y + z ≠ 0` and `x² + y² + z² ≠ 0`, the Koide ratio
  `(x² + y² + z²) / (x + y + z)²` equals `2 / 3` exactly when the Born weight
  `(x + y + z)² / (3 (x² + y² + z²))` equals `1 / 2` (`koide_iff_born_half`), exactly when the
  vector is null for the form `+` along `(1, 1, 1)` and `-` across it (`koide_iff_null`).

## References

* J. Beasley, *Non-normality is connection energy* (2026), working ledger v2 (21 October 2026).
-/

open Matrix

namespace NonNormality

section Swap

variable {n R : Type*} [Fintype n] [DecidableEq n] [Field R] [CharZero R]

/-- Coupling across the sectors and coupling inside a sector are trace-orthogonal. -/
theorem trace_mul_eq_zero_of_odd_of_even {Γ A B : Matrix n n R} (hΓ : Γ * Γ = 1)
    (hA : Γ * A * Γ = -A) (hB : Γ * B * Γ = B) : trace (A * B) = 0 := by
  have hΓ' : ∀ M : Matrix n n R, Γ * (Γ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hΓ, Matrix.one_mul]
  have e : (Γ * A * Γ) * (Γ * B * Γ) = Γ * (A * B * Γ) := by
    simp only [Matrix.mul_assoc, hΓ']
  have t : trace (Γ * (A * B * Γ)) = trace (A * B) := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, hΓ, Matrix.mul_one]
  have h : trace (A * B) = -trace (A * B) := by
    calc trace (A * B) = trace ((Γ * A * Γ) * (Γ * B * Γ)) := by rw [e, t]
      _ = -trace (A * B) := by rw [hA, hB, Matrix.neg_mul, Matrix.trace_neg]
  have h2 : (2 : R) * trace (A * B) = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **The admissibility defect.** Reflecting `X = A + B` by the sector sign `Γ` flips the trace
form of the cross-sector part exactly; what is left over is twice the trace form of the
within-sector part `B`. -/
theorem trace_swap_defect {Γ A B : Matrix n n R} (hΓ : Γ * Γ = 1) (hA : Γ * A * Γ = -A)
    (hB : Γ * B * Γ = B) :
    trace ((A + B) * (A + B)) + trace ((Γ * (A + B)) * (Γ * (A + B))) =
      2 * trace (B * B) := by
  have hX : Γ * (A + B) * Γ = -A + B := by
    rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
  have e1 : (Γ * (A + B)) * (Γ * (A + B)) = (-A + B) * (A + B) := by
    rw [← hX]
    simp only [Matrix.mul_assoc]
  have hab := trace_mul_eq_zero_of_odd_of_even hΓ hA hB
  have hba : trace (B * A) = 0 := by rw [Matrix.trace_mul_comm]; exact hab
  rw [e1]
  simp only [add_mul, mul_add, neg_mul, Matrix.trace_add, Matrix.trace_neg]
  linear_combination 2 * hba

/-- **The exact swap.** For coupling only across the sectors, the reflection reverses the
trace form. -/
theorem trace_swap_of_odd {Γ X : Matrix n n R} (hΓ : Γ * Γ = 1) (hX : Γ * X * Γ = -X) :
    trace ((Γ * X) * (Γ * X)) = -trace (X * X) := by
  have h0 : Γ * (0 : Matrix n n R) * Γ = 0 := by simp
  have h := trace_swap_defect (A := X) (B := 0) hΓ hX h0
  simp only [add_zero, zero_mul, mul_zero, Matrix.trace_zero] at h
  linear_combination h

end Swap

section HalfSwap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A cross-sector `X` anticommutes, after conjugate transpose, with a Hermitian involution. -/
theorem conjTranspose_mul_of_odd {Γ X : Matrix n n ℂ} (hΓh : Γᴴ = Γ) (hΓ : Γ * Γ = 1)
    (hX : Γ * X * Γ = -X) : Xᴴ * Γ = -(Γ * Xᴴ) := by
  have h1 : Γ * Xᴴ * Γ = -Xᴴ := by
    have h := congrArg conjTranspose hX
    simpa [Matrix.conjTranspose_mul, hΓh, Matrix.mul_assoc] using h
  calc Xᴴ * Γ = Γ * (Γ * Xᴴ * Γ) := by
        simp only [← Matrix.mul_assoc, hΓ, Matrix.one_mul]
    _ = -(Γ * Xᴴ) := by rw [h1, Matrix.mul_neg]

/-- **The half swap.** The Hermitian part of `Γ * X` is `Γ` times the skew part of `X`. -/
theorem add_conjTranspose_mul_of_odd {Γ X : Matrix n n ℂ} (hΓh : Γᴴ = Γ) (hΓ : Γ * Γ = 1)
    (hX : Γ * X * Γ = -X) : Γ * X + (Γ * X)ᴴ = Γ * (X - Xᴴ) := by
  rw [Matrix.conjTranspose_mul, hΓh, conjTranspose_mul_of_odd hΓh hΓ hX, Matrix.mul_sub]
  abel

/-- **The half swap, other half.** The skew part of `Γ * X` is `Γ` times the Hermitian part of
`X`. -/
theorem sub_conjTranspose_mul_of_odd {Γ X : Matrix n n ℂ} (hΓh : Γᴴ = Γ) (hΓ : Γ * Γ = 1)
    (hX : Γ * X * Γ = -X) : Γ * X - (Γ * X)ᴴ = Γ * (X + Xᴴ) := by
  rw [Matrix.conjTranspose_mul, hΓh, conjTranspose_mul_of_odd hΓh hΓ hX, Matrix.mul_add]
  abel

end HalfSwap

section Tangent

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A tangent to the idempotents has no block inside the image of `P`. -/
theorem mul_mul_eq_zero_of_tangent {P V : Matrix n n R} (hP : P * P = P)
    (hV : P * V + V * P = V) : P * V * P = 0 := by
  have h := congrArg (P * ·) hV
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, hP] at h
  calc P * V * P = (P * V + P * V * P) - P * V := by abel
    _ = 0 := by rw [h, sub_self]

/-- The first-order overlap of a curve of idempotents vanishes: `trace (P * V) = 0`. -/
theorem trace_mul_eq_zero_of_tangent {P V : Matrix n n R} (hP : P * P = P)
    (hV : P * V + V * P = V) : trace (P * V) = 0 := by
  calc trace (P * V) = trace (P * P * V) := by rw [hP]
    _ = trace (P * V * P) := by rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    _ = 0 := by rw [mul_mul_eq_zero_of_tangent hP hV, Matrix.trace_zero]

/-- **The second-order overlap.** If `W` is the second-order term of a curve of idempotents
through `P` with tangent `V`, then `trace (P * W) = -trace (V * V)`: the overlap bends down
exactly by the trace form of the tangent. -/
theorem trace_mul_eq_neg_of_second_order {P V W : Matrix n n R} (hP : P * P = P)
    (hV : P * V + V * P = V) (hW : V * V + V * V + P * W + W * P = W) :
    trace (P * W) = -trace (V * V) := by
  have h1 : P * W * P = -(P * V * V + P * V * V) := by
    have h := congrArg (P * ·) hW
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hP] at h
    calc P * W * P = (P * V * V + P * V * V + P * W + P * W * P) - (P * V * V + P * V * V) -
          P * W := by abel
      _ = -(P * V * V + P * V * V) := by rw [h]; abel
  have h2 : trace (P * W) = trace (P * W * P) := by
    calc trace (P * W) = trace (P * P * W) := by rw [hP]
      _ = trace (P * W * P) := by rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  have hVV : V * V = (P * V + V * P) * V := by rw [hV]
  have h3 : trace (V * V) = trace (P * V * V) + trace (P * V * V) := by
    rw [hVV, Matrix.add_mul, Matrix.trace_add, Matrix.mul_assoc V P V,
      Matrix.trace_mul_comm V (P * V)]
  rw [h2, h1, Matrix.trace_neg, Matrix.trace_add, h3]

end Tangent

section Records

/-- **Linear record from log record.** For a two-outcome split `(s, 1 - s)`, the hyperbolic
tangent of half the log-odds is `2 s - 1`. -/
theorem tanh_half_log_odds {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    Real.tanh (Real.log (s / (1 - s)) / 2) = 2 * s - 1 := by
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have h1s' : (1 : ℝ) - s ≠ 0 := h1s.ne'
  have hq : 0 < s / (1 - s) := div_pos h0 h1s
  have he : Real.exp (Real.log (s / (1 - s)) / 2) * Real.exp (Real.log (s / (1 - s)) / 2) =
      s / (1 - s) := by
    rw [← Real.exp_add, add_halves, Real.exp_log hq]
  have he' : Real.exp (Real.log (s / (1 - s)) / 2) * Real.exp (Real.log (s / (1 - s)) / 2) *
      (1 - s) = s := by
    rw [he, div_mul_cancel₀ s h1s']
  have htpos : 0 < Real.exp (Real.log (s / (1 - s)) / 2) := Real.exp_pos _
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  generalize Real.exp (Real.log (s / (1 - s)) / 2) = t at htpos he' ⊢
  have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ htpos.ne'
  have hden : (t + t⁻¹) / 2 ≠ 0 := by
    have hi := inv_pos.mpr htpos
    exact (by linarith : (0 : ℝ) < (t + t⁻¹) / 2).ne'
  rw [div_eq_iff hden]
  linear_combination t⁻¹ * he' - t * (1 - s) * hinv

/-- **Even record.** The census of a two-outcome split is one minus the square of its linear
record. -/
theorem four_mul_mul_one_sub (s : ℝ) : 4 * s * (1 - s) = 1 - (2 * s - 1) ^ 2 := by ring

/-- **The fixed point of the complement.** Any rule that adds to one over a two-outcome split
assigns one half to the balanced split. -/
theorem apply_half_of_complement {F : ℝ → ℝ} (h : ∀ s, F s + F (1 - s) = 1) :
    F (1 / 2) = 1 / 2 := by
  have h2 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have h' := h (1 / 2)
  rw [h2] at h'
  linarith

end Records

section Koide

/-- **Koide as a Born half.** The Koide ratio is `2 / 3` exactly when the Born weight of the
square-root vector on the democratic direction is `1 / 2`. -/
theorem koide_iff_born_half {x y z : ℝ} (hs : x + y + z ≠ 0) (hn : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0) :
    (x ^ 2 + y ^ 2 + z ^ 2) / (x + y + z) ^ 2 = 2 / 3 ↔
      (x + y + z) ^ 2 / (3 * (x ^ 2 + y ^ 2 + z ^ 2)) = 1 / 2 := by
  have h3 : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 := mul_ne_zero three_ne_zero hn
  rw [div_eq_iff (pow_ne_zero 2 hs), div_eq_iff h3]
  constructor <;> intro h <;> linarith

/-- **Koide as a null vector.** The Koide ratio is `2 / 3` exactly when the square-root vector has
equal weight along `(1, 1, 1)` and across it: the on-site book equals the hopping book. -/
theorem koide_iff_null {x y z : ℝ} (hs : x + y + z ≠ 0) :
    (x ^ 2 + y ^ 2 + z ^ 2) / (x + y + z) ^ 2 = 2 / 3 ↔
      (x + y + z) ^ 2 / 3 - ((x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 / 3) = 0 := by
  rw [div_eq_iff (pow_ne_zero 2 hs)]
  constructor <;> intro h <;> linarith

end Koide

end NonNormality
