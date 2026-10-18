/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The projector quantum geometric tensor

For an orthogonal projector `P` (`Pᴴ = P`, `P * P = P`) and Hermitian `V W : Matrix n n ℂ`, the
June 2026 lattice and transport papers use

* `qgt P V W = Tr (P V W)` (the intrinsic tensor `Q_Π(V, W)`),
* `qgtMetric P V W = Re (qgt P V W)` (the metric `g_Π`),
* `qgtCurvature P V W = Re (-i Tr (P [V, W]))` (the curvature `Ω_Π`).

## Main results

* `NonNormality.neg_I_mul_trace_commutator`: `-i Tr (P [V, W]) = 2 Im (qgt P V W)`, so the
  curvature is real-valued and `qgtCurvature P V W = 2 Im (qgt P V W)`.
* `NonNormality.qgt_eq_metric_add_curvature`: `Q = g + (i / 2) Ω`. (The figure convention
  `Q = g + i Ω` is off by a factor of two; see `NonNormality.Counterexamples`.)
* `NonNormality.norm_sq_qgt_le`: Cauchy–Schwarz, `|Q(V, W)|² ≤ g(V, V) g(W, W)`.
* `NonNormality.abs_qgtCurvature_le`: the **metric–curvature inequality**
  `|Ω(V, W)| ≤ 2 √(g(V, V) g(W, W) - g(V, W)²)`, for all Hermitian `V`, `W` (no tangency needed).
* `NonNormality.qgtMetric_self_nonneg`: `0 ≤ g(V, V)` (the transport capacity `C(V)`).
* `NonNormality.qgtMetric_self_of_isTangent`: for a tangent vector
  `V = P V (1 - P) + (1 - P) V P`, `g(V, V) = Re Tr (V²) / 2`.
* `NonNormality.qgt_one_sub_of_isTangent`: on tangent vectors the complementary projector gives
  the conjugate tensor, so the metrics agree and the curvatures are opposite.

## References

* J. Beasley, *Non-Normal Lattice Transport Operators with Gradient-Controlled Pseudospectra and
  Effective Inertia Tensors* (June 22, 2026), §10.2.
* J. Beasley, *Directional Transport Geometry of Admissible Channels* (June 29, 2026), App. B,
  Theorem 12 and Proposition 3.
-/

open Matrix Complex
open scoped ComplexOrder

namespace NonNormality

variable {n : Type*} [Fintype n]

/-- The projector quantum geometric tensor `Q_P(V, W) = Tr (P V W)`. -/
def qgt (P V W : Matrix n n ℂ) : ℂ := (P * V * W).trace

/-- The metric part `g_P(V, W) = Re Tr (P V W)`. -/
noncomputable def qgtMetric (P V W : Matrix n n ℂ) : ℝ := (qgt P V W).re

/-- The curvature `Ω_P(V, W) = Re (-i Tr (P [V, W]))`; it is real-valued by
`NonNormality.neg_I_mul_trace_commutator`. -/
noncomputable def qgtCurvature (P V W : Matrix n n ℂ) : ℝ :=
  (-I * (P * (V * W - W * V)).trace).re

/-- For Hermitian `P`, `V`, `W`, swapping `V` and `W` conjugates the tensor. -/
theorem qgt_swap {P V W : Matrix n n ℂ} (hP : P.IsHermitian) (hV : V.IsHermitian)
    (hW : W.IsHermitian) : qgt P W V = star (qgt P V W) := by
  rw [qgt, qgt, ← trace_conjTranspose]
  simp only [conjTranspose_mul, hP.eq, hV.eq, hW.eq]
  rw [Matrix.mul_assoc P W V, trace_mul_comm P (W * V), Matrix.mul_assoc]

/-- `-i Tr (P [V, W]) = 2 Im Tr (P V W)`; in particular it is real. -/
theorem neg_I_mul_trace_commutator {P V W : Matrix n n ℂ} (hP : P.IsHermitian)
    (hV : V.IsHermitian) (hW : W.IsHermitian) :
    -I * (P * (V * W - W * V)).trace = ((2 * (qgt P V W).im : ℝ) : ℂ) := by
  have h : (P * (V * W - W * V)).trace = qgt P V W - star (qgt P V W) := by
    rw [← qgt_swap hP hV hW, qgt, qgt, Matrix.mul_sub, trace_sub, Matrix.mul_assoc,
      Matrix.mul_assoc]
  rw [h]
  apply Complex.ext
  · simp [Complex.mul_re]; ring
  · simp [Complex.mul_im]

theorem qgtCurvature_eq {P V W : Matrix n n ℂ} (hP : P.IsHermitian) (hV : V.IsHermitian)
    (hW : W.IsHermitian) : qgtCurvature P V W = 2 * (qgt P V W).im := by
  rw [qgtCurvature, neg_I_mul_trace_commutator hP hV hW, ofReal_re]

/-- **`Q = g + (i / 2) Ω`.** -/
theorem qgt_eq_metric_add_curvature {P V W : Matrix n n ℂ} (hP : P.IsHermitian)
    (hV : V.IsHermitian) (hW : W.IsHermitian) :
    qgt P V W = qgtMetric P V W + I / 2 * qgtCurvature P V W := by
  rw [qgtCurvature_eq hP hV hW, qgtMetric]
  apply Complex.ext <;> simp

/-- For an orthogonal projector `P` and Hermitian `V`, `W`,
`Q_P(V, W) = Tr ((V P)ᴴ (W P))`, the Frobenius inner product of `V P` and `W P`. -/
theorem qgt_eq_trace_conjTranspose_mul {P V W : Matrix n n ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (hV : V.IsHermitian) :
    qgt P V W = ((V * P)ᴴ * (W * P)).trace := by
  rw [conjTranspose_mul, hP.eq, hV.eq, qgt]
  simp only [← Matrix.mul_assoc]
  rw [trace_mul_comm _ P]
  simp only [← Matrix.mul_assoc, hPP]

/-- Cauchy–Schwarz for the Frobenius pairing `Tr (Xᴴ Y)`. -/
theorem norm_sq_trace_conjTranspose_mul_le (X Y : Matrix n n ℂ) :
    ‖(Xᴴ * Y).trace‖ ^ 2 ≤ (Xᴴ * X).trace.re * (Yᴴ * Y).trace.re := by
  let e : Matrix n n ℂ → EuclideanSpace ℂ (n × n) := fun M => WithLp.toLp 2 (fun p => M p.2 p.1)
  have hin : ∀ M N : Matrix n n ℂ, inner ℂ (e M) (e N) = (Mᴴ * N).trace := by
    intro M N
    simp [e, PiLp.inner_apply, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, mul_comm]
  have h := norm_inner_le_norm (𝕜 := ℂ) (e X) (e Y)
  rw [hin] at h
  have hx : (Xᴴ * X).trace.re = ‖e X‖ ^ 2 := by
    rw [← hin]; simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (e X)
  have hy : (Yᴴ * Y).trace.re = ‖e Y‖ ^ 2 := by
    rw [← hin]; simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (e Y)
  rw [hx, hy, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `Re Tr (Xᴴ X) ≥ 0`. -/
theorem re_trace_conjTranspose_mul_self_nonneg (X : Matrix n n ℂ) : 0 ≤ (Xᴴ * X).trace.re :=
  (Complex.le_def.1 (posSemidef_conjTranspose_mul_self X).trace_nonneg).1

variable {P V W : Matrix n n ℂ}

/-- The transport capacity `C(V) = g(V, V)` is nonnegative. -/
theorem qgtMetric_self_nonneg (hP : P.IsHermitian) (hPP : P * P = P) (hV : V.IsHermitian) :
    0 ≤ qgtMetric P V V := by
  rw [qgtMetric, qgt_eq_trace_conjTranspose_mul hP hPP hV]
  exact re_trace_conjTranspose_mul_self_nonneg _

/-- **Cauchy–Schwarz for the tensor**: `|Q(V, W)|² ≤ g(V, V) g(W, W)`. -/
theorem norm_sq_qgt_le (hP : P.IsHermitian) (hPP : P * P = P) (hV : V.IsHermitian)
    (hW : W.IsHermitian) : ‖qgt P V W‖ ^ 2 ≤ qgtMetric P V V * qgtMetric P W W := by
  rw [qgtMetric, qgtMetric, qgt_eq_trace_conjTranspose_mul hP hPP hV,
    qgt_eq_trace_conjTranspose_mul hP hPP hV, qgt_eq_trace_conjTranspose_mul hP hPP hW]
  exact norm_sq_trace_conjTranspose_mul_le _ _

/-- **Metric–curvature inequality.** For an orthogonal projector `P` and Hermitian `V`, `W`,
`|Ω(V, W)| ≤ 2 √(g(V, V) g(W, W) - g(V, W)²)`. -/
theorem abs_qgtCurvature_le (hP : P.IsHermitian) (hPP : P * P = P) (hV : V.IsHermitian)
    (hW : W.IsHermitian) :
    |qgtCurvature P V W| ≤
      2 * √(qgtMetric P V V * qgtMetric P W W - qgtMetric P V W ^ 2) := by
  have hcs := norm_sq_qgt_le hP hPP hV hW
  have key : (qgtCurvature P V W / 2) ^ 2 ≤
      qgtMetric P V V * qgtMetric P W W - qgtMetric P V W ^ 2 := by
    rw [qgtCurvature_eq hP hV hW]
    have h1 : ‖qgt P V W‖ ^ 2 = (qgt P V W).re ^ 2 + (qgt P V W).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h2 : (2 * (qgt P V W).im / 2) ^ 2 = (qgt P V W).im ^ 2 := by ring
    simp only [qgtMetric] at hcs ⊢
    linarith
  have h2 := Real.abs_le_sqrt key
  rw [abs_div, abs_two] at h2
  linarith

section Tangent

variable [DecidableEq n]

/-- `V` is tangent to the Grassmannian at `P`: `V = P V (1 - P) + (1 - P) V P` (block
off-diagonal with respect to `P`). -/
def IsTangent (P V : Matrix n n ℂ) : Prop := V = P * V * (1 - P) + (1 - P) * V * P

private theorem one_sub_mul_mul_eq_zero (hPP : P * P = P) (X : Matrix n n ℂ) :
    (1 - P) * (P * X) = 0 := by
  rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self, Matrix.zero_mul]

private theorem mul_one_sub_mul_eq_zero (hPP : P * P = P) (X : Matrix n n ℂ) :
    P * ((1 - P) * X) = 0 := by
  rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, Matrix.zero_mul]

theorem IsTangent.mul_mul_self (hPP : P * P = P) (hV : IsTangent P V) : P * V * P = 0 := by
  rw [show V = P * V * (1 - P) + (1 - P) * V * P from hV]
  simp only [Matrix.mul_add, Matrix.mul_assoc, mul_one_sub_mul_eq_zero hPP, add_zero]
  rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self, Matrix.mul_zero, Matrix.mul_zero,
    Matrix.mul_zero]

theorem IsTangent.one_sub_mul_mul_one_sub (hPP : P * P = P) (hV : IsTangent P V) :
    (1 - P) * V * (1 - P) = 0 := by
  rw [show V = P * V * (1 - P) + (1 - P) * V * P from hV]
  simp only [Matrix.mul_add, Matrix.mul_assoc, one_sub_mul_mul_eq_zero hPP, zero_add]
  rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, Matrix.mul_zero, Matrix.mul_zero,
    Matrix.mul_zero]

/-- On tangent vectors, `Tr ((1 - P) V W) = Tr (P W V)`. -/
theorem trace_one_sub_mul_mul_of_isTangent (hPP : P * P = P) (hV : IsTangent P V)
    (hW : IsTangent P W) : ((1 - P) * V * W).trace = (P * W * V).trace := by
  have e1 : (1 - P) * V * W = (1 - P) * V * P * W + (1 - P) * V * (1 - P) * W := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel]; simp
  have e2 : P * W * V = P * W * P * V + P * W * (1 - P) * V := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel]; simp
  rw [e1, e2, hV.one_sub_mul_mul_one_sub hPP, hW.mul_mul_self hPP, Matrix.zero_mul,
    Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc ((1 - P) * V), trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **Complementary projector.** On tangent vectors `Q_{1-P}(V, W) = Q_P(W, V)`. -/
theorem qgt_one_sub_of_isTangent (hPP : P * P = P) (hV : IsTangent P V)
    (hW : IsTangent P W) : qgt (1 - P) V W = qgt P W V :=
  trace_one_sub_mul_mul_of_isTangent hPP hV hW

/-- The complementary projector has the same metric on tangent vectors. -/
theorem qgtMetric_one_sub_of_isTangent (hP : P.IsHermitian) (hPP : P * P = P)
    (hV' : V.IsHermitian) (hW' : W.IsHermitian) (hV : IsTangent P V) (hW : IsTangent P W) :
    qgtMetric (1 - P) V W = qgtMetric P V W := by
  rw [qgtMetric, qgtMetric, qgt_one_sub_of_isTangent hPP hV hW, qgt_swap hP hV' hW']
  simp

/-- The complementary projector has the opposite curvature on tangent vectors. -/
theorem qgtCurvature_one_sub_of_isTangent (hP : P.IsHermitian) (hPP : P * P = P)
    (hV' : V.IsHermitian) (hW' : W.IsHermitian) (hV : IsTangent P V) (hW : IsTangent P W) :
    qgtCurvature (1 - P) V W = -qgtCurvature P V W := by
  have hP' : (1 - P).IsHermitian := isHermitian_one.sub hP
  rw [qgtCurvature_eq hP' hV' hW', qgtCurvature_eq hP hV' hW',
    qgt_one_sub_of_isTangent hPP hV hW, qgt_swap hP hV' hW']
  simp

/-- On a tangent vector, `g(V, V) = Re Tr (V²) / 2`. -/
theorem qgtMetric_self_of_isTangent (hPP : P * P = P) (hV : IsTangent P V) :
    qgtMetric P V V = (V * V).trace.re / 2 := by
  have h : (V * V).trace = (P * V * V).trace + ((1 - P) * V * V).trace := by
    rw [← trace_add, ← Matrix.add_mul, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  rw [h, trace_one_sub_mul_mul_of_isTangent hPP hV hV, qgtMetric, qgt, add_re]
  ring

end Tangent

end NonNormality
