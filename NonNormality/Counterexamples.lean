/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import NonNormality.Lattice
import NonNormality.QGT

/-!
# Counterexamples to statements in the June 2026 originals

Each theorem here is a *true* statement that refutes, or pins down the correct form of, a claim
printed in one of the June 2026 source papers. See `FINDINGS_INVENTORY.md` for page references.

## Main results

* `NonNormality.paperBlock_eq_symplecticJ_mul_sub` and `NonNormality.paperBlock_ne_anticommutator`:
  the block `!![2b, d - a; d - a, -2b]` printed for `M J + J M` (June 24, §10.4) is the
  commutator `J M - M J`, which is symmetric; the anticommutator is `(tr M) J`
  (`NonNormality.mul_symplecticJ_add`).
* `NonNormality.trace_gl_conj_ne`: congruence `B ↦ U B Uᵀ` by `U ∈ GL(2)` does not preserve the
  spectrum (`U = 2`, `B = 1`), refuting the `GL(2)` gauge invariance of June 24 §10.4.
* `NonNormality.qgt_ne_metric_add_I_mul_curvature`: the figure convention `Q = g + i Ω` fails;
  with the printed definitions `Q = g + (i / 2) Ω` (`NonNormality.qgt_eq_metric_add_curvature`).
* `NonNormality.not_real_eigenvector_smul_add_symplecticJ`: a skew perturbation of a degenerate
  real spectrum has no real eigenvalues at all, refuting "eigenvalues remain on the real axis".
* `NonNormality.not_diagonalizable_jordan`: for the stiffness `K = 0` (normal), the transport
  backbone `!![0, 1; -K, 0]` is a Jordan block, so an exceptional point occurs without
  non-normality (June 29, Theorem 3).
* `NonNormality.rigidity_lt_of_zero_gradient`: at zero gradient the regularized rigidity
  `1 / (λ + ε)` lies strictly below the claimed lower bound `1 / λ` (June 29, Lemma 10).
-/

open Matrix Complex

namespace NonNormality

/-- The `2 × 2` block printed for `M J + J M` in June 24 §10.4. -/
def paperBlock {R : Type*} [CommRing R] (a b d : R) : Matrix (Fin 2) (Fin 2) R :=
  !![2 * b, d - a; d - a, -2 * b]

/-- The printed block is the commutator `J M - M J` for `M = !![a, b; b, d]`. -/
theorem paperBlock_eq_symplecticJ_mul_sub {R : Type*} [CommRing R] (a b d : R) :
    paperBlock a b d = symplecticJ * !![a, b; b, d] - !![a, b; b, d] * symplecticJ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [paperBlock, symplecticJ] <;> ring

/-- The printed block is not the anticommutator: `M = !![1, 1; 1, 0]` over `ℚ`. -/
theorem paperBlock_ne_anticommutator :
    paperBlock (1 : ℚ) 1 0 ≠ !![1, 1; 1, 0] * symplecticJ + symplecticJ * !![1, 1; 1, 0] := by
  intro h
  have := congr_fun (congr_fun h 0) 0
  simp [paperBlock, symplecticJ] at this

/-- `GL(2)` congruence changes the spectrum: for `U = 2 • 1` and `B = 1`,
`Tr (U B Uᵀ) = 8 ≠ 2 = Tr B`. -/
theorem trace_gl_conj_ne :
    ((2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) * 1 * ((2 : ℚ) • 1)ᵀ).trace ≠
      (1 : Matrix (Fin 2) (Fin 2) ℚ).trace := by
  simp
  norm_num

/-- `Q = g + i Ω` fails: for `P = diag(1, 0)`, `V = σₓ`, `W = σ_y`, `Q = i`, `g = 0`, `Ω = 2`. -/
theorem qgt_ne_metric_add_I_mul_curvature :
    qgt !![1, 0; 0, 0] !![0, 1; 1, 0] !![0, -I; I, 0] ≠
      qgtMetric !![1, 0; 0, 0] !![0, 1; 1, 0] !![0, -I; I, 0] +
        I * qgtCurvature !![1, 0; 0, 0] !![0, 1; 1, 0] !![0, -I; I, 0] := by
  simp only [qgt, qgtMetric, qgtCurvature]
  simp [Matrix.trace_fin_two]

/-- A skew perturbation of a degenerate real spectrum leaves the real axis: for `ε ≠ 0`,
`c • 1 + ε • J` has no real eigenvector. -/
theorem not_real_eigenvector_smul_add_symplecticJ {c ε μ : ℝ} (hε : ε ≠ 0) {v : Fin 2 → ℝ}
    (hv : v ≠ 0) : (c • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ε • symplecticJ) *ᵥ v ≠ μ • v := by
  intro h
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  simp only [mulVec, dotProduct, symplecticJ, smul_of, smul_cons, smul_eq_mul, mul_zero, mul_one,
    smul_empty, mul_neg, Fin.isValue, Matrix.add_apply, Matrix.smul_apply, of_apply, cons_val',
    cons_val_fin_one, cons_val_zero, Fin.sum_univ_two, one_apply_eq, add_zero, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, cons_val_one, zero_add, Pi.smul_apply, one_ne_zero,
    neg_mul] at h0 h1
  have hsq : ε * (v 0 ^ 2 + v 1 ^ 2) = 0 := by linear_combination v 1 * h0 - v 0 * h1
  have hz : v 0 ^ 2 + v 1 ^ 2 = 0 := (mul_eq_zero.1 hsq).resolve_left hε
  apply hv
  ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- The Jordan block `!![0, 1; 0, 0]` (the backbone `!![0, 1; -K, 0]` at `K = 0`) is not
diagonalizable. -/
theorem not_diagonalizable_jordan (P : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) (d : Fin 2 → ℂ) :
    !![0, 1; 0, 0] ≠ P.val * diagonal d * P.inv := by
  intro h
  have hN2 : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 0, 0] = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hD : diagonal d * diagonal d = 0 := by
    have : P.val * (diagonal d * diagonal d) * P.inv = 0 := by
      rw [← hN2, h]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P.inv, P.inv_val, Matrix.one_mul]
    have h2 := congr_arg (fun X => P.inv * X * P.val) this
    simp only [Matrix.mul_assoc, Matrix.zero_mul, Matrix.mul_zero, P.inv_val,
      Matrix.mul_one] at h2
    rwa [← Matrix.mul_assoc, P.inv_val, Matrix.one_mul] at h2
  have hd : d = 0 := by
    rw [diagonal_mul_diagonal] at hD
    funext i
    have := congr_fun (congr_fun hD i) i
    simpa using this
  have h0 : P.val * diagonal d * P.inv = 0 := by
    rw [hd, show diagonal (0 : Fin 2 → ℂ) = 0 from diagonal_zero, Matrix.mul_zero,
      Matrix.zero_mul]
  rw [h0] at h
  have h01 := congr_fun (congr_fun h 0) 1
  simp at h01

/-- At zero gradient the regularized rigidity is strictly below the claimed bound:
`1 / (λ + ε) < 1 / λ` for `λ, ε > 0`. -/
theorem rigidity_lt_of_zero_gradient {lam ε : ℝ} (hl : 0 < lam) (hε : 0 < ε) :
    1 / (lam + ε) < 1 / lam :=
  one_div_lt_one_div_of_lt hl (by linarith)

end NonNormality
