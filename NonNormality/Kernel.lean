/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import NonNormality.Holonomy

/-!
# The kernel of the self-commutator energy without unitarity

Version 1 of *Non-normality is connection energy* (September 16, 2026) stated the kernel
corollary for merely skew-Hermitian edge blocks, and the companion note *Non-normality is
Dirichlet energy* treated scalar and rank-one channels. These statements were dropped from the
final one-page version (v7); this file restores them.

## Main results

* `NonNormality.isStarNormal_diagonal_add_iff`: with Hermitian `D i` and skew-Hermitian `A`
  (no unitarity, no graph), `diagonal D + A` is normal iff `D i * A i j = A i j * D j` for all
  `i j`.
* `NonNormality.isStarNormal_diagonal_add_scalar_iff`: scalar case; normal iff `d i = d j`
  whenever `a i j ≠ 0` (constant on the components of the support graph).
* `NonNormality.mul_vecMulVec_sub_vecMulVec_mul`: rank-one aligned channels
  `A = f • u vᵀ` with `D u = dᵢ u`, `v D' = dⱼ v` give `D A - A D' = f (dᵢ - dⱼ) u vᵀ`.
* `NonNormality.finrank_parallelSections_eq`: on a connected graph the real dimension of the
  zero-energy space equals that of the holonomy-fixed Hermitian matrices (the dimension count
  `3` / `5` of the 4-cycle example of v1 is an instance; see `numerics/check_findings.py`).
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace NonNormality

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- **Kernel corollary without unitarity.** -/
theorem isStarNormal_diagonal_add_iff (D : ι → Matrix m m ℂ) (hD : ∀ i, (D i).IsHermitian)
    (A : Matrix ι ι (Matrix m m ℂ)) (hA : Aᴴ = -A) :
    IsStarNormal (diagonal D + A) ↔ ∀ i j, D i * A i j = A i j * D j := by
  classical
  rw [isStarNormal_iff, Commute, SemiconjBy, star_eq_conjTranspose, eq_comm, ← sub_eq_zero,
    ← norm_eq_zero, ← pow_eq_zero_iff two_ne_zero, norm_sq_selfCommutator_eq D hD A hA,
    mul_eq_zero, or_iff_right four_ne_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun i => ?_
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity]
  simp [sub_eq_zero]

/-- **Scalar kernel.** For real `d` and skew-Hermitian `a`, `diagonal d + a` is normal iff
`d i = d j` whenever `a i j ≠ 0`. -/
theorem isStarNormal_diagonal_add_scalar_iff (d : ι → ℝ) (a : Matrix ι ι ℂ) (ha : aᴴ = -a) :
    IsStarNormal (diagonal (fun i => (d i : ℂ)) + a) ↔ ∀ i j, a i j ≠ 0 → d i = d j := by
  rw [isStarNormal_iff, Commute, SemiconjBy, star_eq_conjTranspose, eq_comm, ← sub_eq_zero,
    ← norm_eq_zero, ← pow_eq_zero_iff two_ne_zero, norm_sq_selfCommutator_scalar d a ha,
    mul_eq_zero, or_iff_right four_ne_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun i => ?_
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity]
  simp only [Finset.mem_univ, true_implies, mul_eq_zero, pow_eq_zero_iff two_ne_zero,
    norm_eq_zero, sub_eq_zero]
  exact forall_congr' fun j => or_iff_not_imp_left

omit [Fintype ι] [DecidableEq ι] [DecidableEq m] in
/-- **Rank-one aligned channels.** If `A = f • u vᵀ` with `D u = dᵢ u` and `v D' = dⱼ v`, then
`D A - A D' = (f (dᵢ - dⱼ)) • u vᵀ`. -/
theorem mul_vecMulVec_sub_vecMulVec_mul {R : Type*} [CommRing R] (D D' : Matrix m m R)
    (u v : m → R) (f di dj : R) (hu : D *ᵥ u = di • u) (hv : v ᵥ* D' = dj • v) :
    D * (f • vecMulVec u v) - (f • vecMulVec u v) * D' = (f * (di - dj)) • vecMulVec u v := by
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, hu, hv]
  ext i j
  simp [vecMulVec_apply]
  ring

variable {G : SimpleGraph ι} {A : Matrix ι ι (Matrix m m ℂ)}

omit [Fintype ι] [DecidableEq ι] in
/-- **Dimension of the zero-energy space.** On a connected graph, the real dimension of the
Hermitian parallel sections equals that of the holonomy-fixed Hermitian matrices at any base
vertex. -/
theorem finrank_parallelSections_eq (hA : IsUnitaryConnection G A) (hG : G.Connected)
    (i₀ : ι) :
    Module.finrank ℝ (parallelSections G A) = Module.finrank ℝ (holonomyFixed G A i₀) :=
  (parallelSectionsEquivHolonomyFixed hA hG i₀).finrank_eq

end NonNormality
