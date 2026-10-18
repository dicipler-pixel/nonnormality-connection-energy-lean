/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The symplectic lattice transport operator

The June 2026 lattice papers act on `⨁ₙ ℝ²` with the symplectic generator
`J = !![0, 1; -1, 0]`, the periodic central difference `(Δ₁ ψ)ₙ = ψₙ₊₁ - ψₙ₋₁` and the transport
operator `A = α J Δ₁`, here `α • (Δ₁ ⊗ₖ J)`. The coupling blocks are built from `M J` and `J M`
for symmetric `2 × 2` gradients `M`.

## Main results

* `NonNormality.centralDiff_transpose`, `NonNormality.latticeTransport_transpose`: `Δ₁` is skew
  and `A = α (Δ₁ ⊗ₖ J)` is symmetric (a Kronecker product of two skew matrices).
* `NonNormality.mul_symplecticJ_add`: for symmetric `M`, `M J + J M = (tr M) J`. Hence the
  paper's leading coupling block `Mₙ J + J Mₙ` sees only the *trace* of the gradient, and
  vanishes for every trace-free (purely anisotropic) gradient.
* `NonNormality.transpose_mul_symplecticJ`: `(M J)ᵀ = M J - (tr M) J`, so the skew part of each
  averaging block `δB J` is `(tr δB / 2) J` and `M J` is symmetric when `tr M = 0`.
* `NonNormality.transpose_mul_symplecticJ_sub`: `M J - J M` is symmetric.
* `NonNormality.rot_mul_symplecticJ_mul_transpose`: a rotation fixes `J` under congruence;
  `NonNormality.reflect_mul_symplecticJ_mul_transpose`: a reflection sends `J` to `-J`.
* `NonNormality.kronecker_one_rot_conj_latticeTransport`: a *constant* rotation of every site
  commutes with the transport operator, so it is an exact orthogonal similarity of
  `A + D₀` that only conjugates the obstruction field.

## References

* J. Beasley, *Spectral Stability Across Obstruction Interfaces in Geometric Transport Systems*
  (June 24, 2026), Thm. 3.1, §3, §10.4 and App. A.
-/

open Matrix
open scoped Kronecker

namespace NonNormality

variable {R : Type*} [CommRing R]

/-- The symplectic generator `J = !![0, 1; -1, 0]`. -/
def symplecticJ : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

theorem symplecticJ_transpose : (symplecticJ : Matrix (Fin 2) (Fin 2) R)ᵀ = -symplecticJ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symplecticJ]

theorem symplecticJ_mul_self : (symplecticJ : Matrix (Fin 2) (Fin 2) R) * symplecticJ = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symplecticJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The anticommutator with `J` sees only the trace.** For symmetric `M`,
`M J + J M = (tr M) J`. -/
theorem mul_symplecticJ_add {M : Matrix (Fin 2) (Fin 2) R} (hM : Mᵀ = M) :
    M * symplecticJ + symplecticJ * M = M.trace • symplecticJ := by
  have h10 : M 1 0 = M 0 1 := by simpa using congr_fun (congr_fun hM 0) 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [symplecticJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, h10, vecMul,
      dotProduct]

/-- `(M J)ᵀ = M J - (tr M) J` for symmetric `M`. -/
theorem transpose_mul_symplecticJ {M : Matrix (Fin 2) (Fin 2) R} (hM : Mᵀ = M) :
    (M * symplecticJ)ᵀ = M * symplecticJ - M.trace • symplecticJ := by
  rw [transpose_mul, symplecticJ_transpose, hM, ← mul_symplecticJ_add hM, Matrix.neg_mul]
  abel

/-- For a trace-free symmetric `M`, the block `M J` is symmetric. -/
theorem transpose_mul_symplecticJ_of_trace_eq_zero {M : Matrix (Fin 2) (Fin 2) R}
    (hM : Mᵀ = M) (htr : M.trace = 0) : (M * symplecticJ)ᵀ = M * symplecticJ := by
  rw [transpose_mul_symplecticJ hM, htr, zero_smul, sub_zero]

/-- For a trace-free symmetric `M`, the leading coupling block `M J + J M` vanishes. -/
theorem mul_symplecticJ_add_of_trace_eq_zero {M : Matrix (Fin 2) (Fin 2) R} (hM : Mᵀ = M)
    (htr : M.trace = 0) : M * symplecticJ + symplecticJ * M = 0 := by
  rw [mul_symplecticJ_add hM, htr, zero_smul]

/-- The commutator `M J - J M` of a symmetric `M` with `J` is symmetric. -/
theorem transpose_mul_symplecticJ_sub {M : Matrix (Fin 2) (Fin 2) R} (hM : Mᵀ = M) :
    (M * symplecticJ - symplecticJ * M)ᵀ = M * symplecticJ - symplecticJ * M := by
  rw [transpose_sub, transpose_mul, transpose_mul, symplecticJ_transpose, hM, Matrix.neg_mul,
    Matrix.mul_neg, sub_neg_eq_add, neg_add_eq_sub]

/-- A Kronecker product of two skew matrices is symmetric. -/
theorem kronecker_transpose_of_skew {l m : Type*} {A : Matrix l l R} {B : Matrix m m R}
    (hA : Aᵀ = -A) (hB : Bᵀ = -B) : (A ⊗ₖ B)ᵀ = A ⊗ₖ B := by
  rw [← kroneckerMap_transpose, hA, hB]
  ext ⟨i, k⟩ ⟨j, l⟩
  simp

/-- The periodic central difference `(Δ₁ ψ)ₙ = ψₙ₊₁ - ψₙ₋₁` on `ZMod N`. -/
def centralDiff (N : ℕ) : Matrix (ZMod N) (ZMod N) R :=
  fun i j => (if j = i + 1 then 1 else 0) - (if j = i - 1 then 1 else 0)

theorem centralDiff_transpose (N : ℕ) :
    (centralDiff N : Matrix (ZMod N) (ZMod N) R)ᵀ = -centralDiff N := by
  ext i j
  simp only [transpose_apply, centralDiff, Matrix.neg_apply, neg_sub]
  have h1 : (i = j + 1) ↔ (j = i - 1) := ⟨fun h => by rw [h, add_sub_cancel_right],
    fun h => by rw [h, sub_add_cancel]⟩
  have h2 : (i = j - 1) ↔ (j = i + 1) := ⟨fun h => by rw [h, sub_add_cancel],
    fun h => by rw [h, add_sub_cancel_right]⟩
  simp only [h1, h2]

/-- The lattice transport operator `A = α J Δ₁`, as `α • (Δ₁ ⊗ₖ J)` on `ZMod N × Fin 2`. -/
def latticeTransport (α : R) (N : ℕ) : Matrix (ZMod N × Fin 2) (ZMod N × Fin 2) R :=
  α • (centralDiff N ⊗ₖ symplecticJ)

/-- **The transport operator is symmetric** (Thm. 3.1 of the June 24 paper). -/
theorem latticeTransport_transpose (α : R) (N : ℕ) :
    (latticeTransport α N)ᵀ = latticeTransport α N := by
  rw [latticeTransport, transpose_smul,
    kronecker_transpose_of_skew (centralDiff_transpose N) symplecticJ_transpose]

/-- The rotation `!![c, -s; s, c]`. -/
def rot (c s : R) : Matrix (Fin 2) (Fin 2) R := !![c, -s; s, c]

theorem rot_transpose_mul_self {c s : R} (h : c ^ 2 + s ^ 2 = 1) : (rot c s)ᵀ * rot c s = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two]
    <;> [linear_combination h; ring; ring; linear_combination h]

/-- A rotation fixes `J` under congruence: `U J Uᵀ = J`. -/
theorem rot_mul_symplecticJ_mul_transpose {c s : R} (h : c ^ 2 + s ^ 2 = 1) :
    rot c s * symplecticJ * (rot c s)ᵀ = symplecticJ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, symplecticJ, Matrix.mul_apply, Fin.sum_univ_two]
    <;> [ring; linear_combination h; linear_combination -h; ring]

/-- A reflection reverses `J`: `R J Rᵀ = -J` for `R = diag(1, -1)`. -/
theorem reflect_mul_symplecticJ_mul_transpose :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) R) * symplecticJ * (!![1, 0; 0, -1])ᵀ =
      -symplecticJ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symplecticJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Constant-rotation gauge invariance.** Rotating every site by the same rotation `U`
leaves the transport operator unchanged: `(1 ⊗ₖ U) A (1 ⊗ₖ U)ᵀ = A`. Together with
`NonNormality.rot_transpose_mul_self` this makes `B ↦ U B Uᵀ` (constant `U ∈ SO(2)`) an exact
orthogonal similarity of `A + D₀`. -/
theorem kronecker_one_rot_conj_latticeTransport (α : R) (N : ℕ) [NeZero N] {c s : R}
    (h : c ^ 2 + s ^ 2 = 1) :
    ((1 : Matrix (ZMod N) (ZMod N) R) ⊗ₖ rot c s) * latticeTransport α N *
        ((1 : Matrix (ZMod N) (ZMod N) R) ⊗ₖ rot c s)ᵀ = latticeTransport α N := by
  rw [latticeTransport, Matrix.mul_smul, Matrix.smul_mul, ← kroneckerMap_transpose,
    transpose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, rot_mul_symplecticJ_mul_transpose h]

/-- The site-wise rotation `1 ⊗ₖ U` is orthogonal. -/
theorem kronecker_one_rot_transpose_mul_self (N : ℕ) [NeZero N] {c s : R}
    (h : c ^ 2 + s ^ 2 = 1) :
    ((1 : Matrix (ZMod N) (ZMod N) R) ⊗ₖ rot c s)ᵀ *
        ((1 : Matrix (ZMod N) (ZMod N) R) ⊗ₖ rot c s) = 1 := by
  rw [← kroneckerMap_transpose, transpose_one, ← mul_kronecker_mul,
    Matrix.one_mul, rot_transpose_mul_self h, one_kronecker_one]

end NonNormality
