/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import NonNormality.Opposite

/-!
# The two books: constants, duality, projectors, the double cover, the product

Let `E₋ = connectionEnergy G A D = ⅛‖[H, Hᴴ]‖²` and `E₊ = oppositeEnergy G A D = ⅛‖H² − (Hᴴ)²‖²`
for `H = diagonal D + A`. This file collects the algebra that ties the two books together.

## Main results

* **Constants.** `selfCommutator_add_smul_one`: `[H + c • 1, (H + c • 1)ᴴ] = [H, Hᴴ]` for real
  `c`; `mul_self_sub_conjTranspose_mul_self_diagonal_add_smul_one`:
  `(H + c • 1)² − ((H + c • 1)ᴴ)² = (H² − (Hᴴ)²) + (4 c) • A`. **Trace split**
  (`connectionEnergy_trace_split`, `oppositeEnergy_trace_split`): with `D i = c i • 1 + T i`,
  `trace (T i) = 0`, each book is `r ∑_E (c i ∓ c j)² + ∑_E ‖T i ∓ A i j * T j * (A i j)ᴴ‖²`
  with no cross term.
* **Per-edge duality.** For the real inner product `frobeniusInner a b = re (trace (aᴴ * b))`,
  `duality_sum_sq`: `P² + V² + L² = 1` with `P = (‖a‖² − ‖b‖²)/s`,
  `V = (‖a + b‖² − ‖a − b‖²)/(‖a + b‖² + ‖a − b‖²)`, `L² = 4(‖a‖²‖b‖² − ⟨a,b⟩²)/s²`,
  `s = ‖a‖² + ‖b‖²`; `frobeniusInner_sq_le` (Cauchy–Schwarz) gives `L² ≥ 0` and
  `duality_le_one`: `P² + V² ≤ 1`. Scalar edge: `scalar_edge_reflection`, `scalar_edge_flux`.
* **Projector fields.** `norm_sub_sq_add_norm_add_sq_of_projector`: for Hermitian idempotents of
  trace `k`, `‖P − R‖² + ‖P + R‖² = 4 k`; summed,
  `connectionEnergy_add_oppositeEnergy_of_projector`: `E₋ + E₊ = 4 k |E|`.
* **The double cover.** `connectionEnergy_doubleCover`: on the bipartite double cover
  `doubleCover G` with the lifted connection `liftConnection A`, the field
  `coverField S T = (S + T, S − T)` has connection energy `2 E₋(S) + 2 E₊(T)`.
* **The product.** `connectionEnergy_mul_oppositeEnergy`:
  `E₋ E₊ = ‖D A‖⁴ − (re (trace ((D A)²)))²`.

## References

* J. Beasley, *Non-normality is connection energy* (2026), v11: the two books.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace NonNormality

section Scalar

/-- **Scalar edge, reflection form.** `(dᵢ − dⱼ)² = Γ² (dᵢ + dⱼ)²` with
`Γ = (dᵢ − dⱼ)/(dᵢ + dⱼ)`. -/
theorem scalar_edge_reflection (di dj : ℝ) (h : di + dj ≠ 0) :
    (di - dj) ^ 2 = ((di - dj) / (di + dj)) ^ 2 * (di + dj) ^ 2 := by
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 h)]

/-- **Scalar edge, flux balance.** `(dᵢ + dⱼ)² − (dᵢ − dⱼ)² = 4 dᵢ dⱼ`. -/
theorem scalar_edge_flux (di dj : ℝ) : (di + dj) ^ 2 - (di - dj) ^ 2 = 4 * di * dj := by
  ring

/-- **The product of two numbers from their sum and difference.** -/
theorem mul_eq_half_add_sq_sub_half_sub_sq (a b : ℝ) :
    a * b = ((a + b) / 2) ^ 2 - ((a - b) / 2) ^ 2 := by
  ring

end Scalar

section Inner

variable {m : Type*} [Fintype m]

/-- The real Frobenius inner product `re (trace (aᴴ * b))`. -/
noncomputable def frobeniusInner (a b : Matrix m m ℂ) : ℝ := RCLike.re (trace (aᴴ * b))

theorem frobeniusInner_self (a : Matrix m m ℂ) : frobeniusInner a a = ‖a‖ ^ 2 :=
  (frobenius_norm_sq_eq_re_trace a).symm

/-- For Hermitian `a`, the inner product is `re (trace (a * b))`. -/
theorem frobeniusInner_eq_re_trace_mul {a : Matrix m m ℂ} (ha : a.IsHermitian)
    (b : Matrix m m ℂ) : frobeniusInner a b = RCLike.re (trace (a * b)) := by
  rw [frobeniusInner, ha.eq]

theorem frobeniusInner_comm (a b : Matrix m m ℂ) : frobeniusInner a b = frobeniusInner b a := by
  have h : bᴴ * a = (aᴴ * b)ᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [frobeniusInner, frobeniusInner, h, trace_conjTranspose, RCLike.star_def, RCLike.conj_re]

theorem frobeniusInner_smul_left (t : ℝ) (a b : Matrix m m ℂ) :
    frobeniusInner (t • a) b = t * frobeniusInner a b := by
  rw [frobeniusInner, frobeniusInner, conjTranspose_smul, star_trivial, Matrix.smul_mul,
    trace_smul, RCLike.smul_re]

/-- `‖a + b‖² = ‖a‖² + ‖b‖² + 2 ⟨a, b⟩`. -/
theorem norm_sq_add_eq (a b : Matrix m m ℂ) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * frobeniusInner a b := by
  have h : (a + b)ᴴ * (a + b) = aᴴ * a + bᴴ * b + (aᴴ * b + (aᴴ * b)ᴴ) := by
    rw [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose]
    noncomm_ring
  rw [frobenius_norm_sq_eq_re_trace, frobenius_norm_sq_eq_re_trace, frobenius_norm_sq_eq_re_trace,
    h, frobeniusInner]
  simp only [trace_add, map_add, trace_conjTranspose, RCLike.star_def, RCLike.conj_re]
  ring

/-- `‖a − b‖² = ‖a‖² + ‖b‖² − 2 ⟨a, b⟩`. -/
theorem norm_sq_sub_eq (a b : Matrix m m ℂ) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * frobeniusInner a b := by
  have h : (a - b)ᴴ * (a - b) = aᴴ * a + bᴴ * b - (aᴴ * b + (aᴴ * b)ᴴ) := by
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose]
    noncomm_ring
  rw [frobenius_norm_sq_eq_re_trace, frobenius_norm_sq_eq_re_trace, frobenius_norm_sq_eq_re_trace,
    h, frobeniusInner]
  simp only [trace_add, trace_sub, map_add, map_sub, trace_conjTranspose, RCLike.star_def,
    RCLike.conj_re]
  ring

theorem norm_sq_smul_real (t : ℝ) (a : Matrix m m ℂ) : ‖t • a‖ ^ 2 = t ^ 2 * ‖a‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- **Cauchy–Schwarz for the Frobenius inner product:** `⟨a, b⟩² ≤ ‖a‖² ‖b‖²`. -/
theorem frobeniusInner_sq_le (a b : Matrix m m ℂ) :
    frobeniusInner a b ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have h : ∀ t : ℝ, 0 ≤ ‖a‖ ^ 2 * (t * t) + (-(2 * frobeniusInner a b)) * t + ‖b‖ ^ 2 := by
    intro t
    have h0 := sq_nonneg ‖t • a - b‖
    rw [norm_sq_sub_eq, norm_sq_smul_real, frobeniusInner_smul_left] at h0
    linarith
  have hd := discrim_le_zero h
  rw [discrim] at hd
  nlinarith [hd]

/-- **Per-edge duality.** With `s = ‖a‖² + ‖b‖²`, `P = (‖a‖² − ‖b‖²)/s` (predictability),
`V = (‖a + b‖² − ‖a − b‖²)/(‖a + b‖² + ‖a − b‖²)` (visibility) and
`L² = 4 (‖a‖² ‖b‖² − ⟨a, b⟩²)/s²` (the third leg), `P² + V² + L² = 1`. -/
theorem duality_sum_sq (a b : Matrix m m ℂ) (hs : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≠ 0) :
    ((‖a‖ ^ 2 - ‖b‖ ^ 2) / (‖a‖ ^ 2 + ‖b‖ ^ 2)) ^ 2 +
      ((‖a + b‖ ^ 2 - ‖a - b‖ ^ 2) / (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2)) ^ 2 +
      4 * (‖a‖ ^ 2 * ‖b‖ ^ 2 - frobeniusInner a b ^ 2) / (‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 = 1 := by
  have hV : (‖a + b‖ ^ 2 - ‖a - b‖ ^ 2) / (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2) =
      2 * frobeniusInner a b / (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    have h2 : ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * frobeniusInner a b +
        (‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * frobeniusInner a b) ≠ 0 := by
      intro h
      exact hs (by linarith)
    rw [norm_sq_add_eq, norm_sq_sub_eq, div_eq_div_iff h2 hs]
    ring
  rw [hV, div_pow, div_pow, ← add_div, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hs)]
  ring

/-- The third leg is nonnegative (Cauchy–Schwarz), so `P² + V² ≤ 1`. -/
theorem duality_le_one (a b : Matrix m m ℂ) (hs : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≠ 0) :
    ((‖a‖ ^ 2 - ‖b‖ ^ 2) / (‖a‖ ^ 2 + ‖b‖ ^ 2)) ^ 2 +
      ((‖a + b‖ ^ 2 - ‖a - b‖ ^ 2) / (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2)) ^ 2 ≤ 1 := by
  have h := duality_sum_sq a b hs
  have hL : 0 ≤ 4 * (‖a‖ ^ 2 * ‖b‖ ^ 2 - frobeniusInner a b ^ 2) / (‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 := by
    apply div_nonneg
    · linarith [frobeniusInner_sq_le a b]
    · positivity
  linarith

/-- **The double cover, one edge.** Lifting an edge with transport `U` to the two edges
`(i,+)–(j,−)` and `(i,−)–(j,+)` of the double cover, the field `(S + T, S − T)` has
`‖(Sᵢ + Tᵢ) − U (Sⱼ − Tⱼ) Uᴴ‖² + ‖(Sᵢ − Tᵢ) − U (Sⱼ + Tⱼ) Uᴴ‖²
  = 2 ‖Sᵢ − U Sⱼ Uᴴ‖² + 2 ‖Tᵢ + U Tⱼ Uᴴ‖²`. -/
theorem doubleCover_edge_core (U Si Ti Sj Tj : Matrix m m ℂ) :
    ‖(Si + Ti) - U * (Sj - Tj) * Uᴴ‖ ^ 2 + ‖(Si - Ti) - U * (Sj + Tj) * Uᴴ‖ ^ 2 =
      2 * ‖Si - U * Sj * Uᴴ‖ ^ 2 + 2 * ‖Ti + U * Tj * Uᴴ‖ ^ 2 := by
  have h1 : (Si + Ti) - U * (Sj - Tj) * Uᴴ = (Si - U * Sj * Uᴴ) + (Ti + U * Tj * Uᴴ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have h2 : (Si - Ti) - U * (Sj + Tj) * Uᴴ = (Si - U * Sj * Uᴴ) - (Ti + U * Tj * Uᴴ) := by
    rw [Matrix.mul_add, Matrix.add_mul]
    abel
  rw [h1, h2]
  linarith [frobenius_parallelogram (Si - U * Sj * Uᴴ) (Ti + U * Tj * Uᴴ)]

end Inner

section Projector

variable {m : Type*} [Fintype m]

/-- A Hermitian idempotent of trace `k` has squared Frobenius norm `k`. -/
theorem norm_sq_of_projector {P : Matrix m m ℂ} (hP : P.IsHermitian) (hP2 : P * P = P) {k : ℝ}
    (hk : trace P = k) : ‖P‖ ^ 2 = k := by
  rw [frobenius_norm_sq_eq_re_trace, hP.eq, hP2, hk, RCLike.re_to_complex, Complex.ofReal_re]

/-- **Projector fields.** For Hermitian idempotents `P`, `R` of equal trace `k`,
`‖P − R‖² + ‖P + R‖² = 4 k`: on a projector field the opposite book is `4 k` minus the connection
book on every edge. -/
theorem norm_sub_sq_add_norm_add_sq_of_projector {P R : Matrix m m ℂ} (hP : P.IsHermitian)
    (hP2 : P * P = P) (hR : R.IsHermitian) (hR2 : R * R = R) {k : ℝ} (hkP : trace P = k)
    (hkR : trace R = k) : ‖P - R‖ ^ 2 + ‖P + R‖ ^ 2 = 4 * k := by
  rw [frobenius_parallelogram, norm_sq_of_projector hP hP2 hkP, norm_sq_of_projector hR hR2 hkR]
  ring

end Projector

section Unitary

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `‖a • 1 + T‖² = a² r + ‖T‖²` when `trace T = 0` (`r = |m|`): no cross term between the trace
sector and the trace-free sector. -/
theorem norm_sq_smul_one_add_of_trace_eq_zero (a : ℝ) (T : Matrix m m ℂ) (hT : trace T = 0) :
    ‖a • (1 : Matrix m m ℂ) + T‖ ^ 2 = a ^ 2 * Fintype.card m + ‖T‖ ^ 2 := by
  have h : (a • (1 : Matrix m m ℂ) + T)ᴴ * (a • (1 : Matrix m m ℂ) + T) =
      (a * a) • (1 : Matrix m m ℂ) + a • T + a • Tᴴ + Tᴴ * T := by
    rw [conjTranspose_add, conjTranspose_smul, star_trivial, conjTranspose_one]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_add, smul_smul]
    abel
  rw [frobenius_norm_sq_eq_re_trace, frobenius_norm_sq_eq_re_trace, h]
  simp only [trace_add, trace_smul, trace_one, trace_conjTranspose, hT, star_zero, smul_zero,
    add_zero, map_add, RCLike.smul_re, RCLike.natCast_re]
  ring

/-- **Trace split, connection book, one edge.** With `Dᵢ = cᵢ • 1 + Tᵢ` and trace-free `Tᵢ`,
`‖Dᵢ − U Dⱼ Uᴴ‖² = (cᵢ − cⱼ)² r + ‖Tᵢ − U Tⱼ Uᴴ‖²`. -/
theorem norm_sub_conj_trace_split {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ) (ci cj : ℝ)
    {Ti Tj : Matrix m m ℂ} (hTi : trace Ti = 0) (hTj : trace Tj = 0) :
    ‖(ci • (1 : Matrix m m ℂ) + Ti) - U * (cj • (1 : Matrix m m ℂ) + Tj) * Uᴴ‖ ^ 2 =
      (ci - cj) ^ 2 * Fintype.card m + ‖Ti - U * Tj * Uᴴ‖ ^ 2 := by
  have hU1 : U * Uᴴ = 1 := (mem_unitaryGroup_iff).1 hU
  have h : (ci • (1 : Matrix m m ℂ) + Ti) - U * (cj • (1 : Matrix m m ℂ) + Tj) * Uᴴ =
      (ci - cj) • (1 : Matrix m m ℂ) + (Ti - U * Tj * Uᴴ) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU1,
      sub_smul]
    abel
  have htr : trace (Ti - U * Tj * Uᴴ) = 0 := by
    rw [trace_sub, hTi, trace_mul_cycle, ← star_eq_conjTranspose, (mem_unitaryGroup_iff').1 hU,
      Matrix.one_mul, hTj, sub_zero]
  rw [h, norm_sq_smul_one_add_of_trace_eq_zero _ _ htr]

/-- **Trace split, opposite book, one edge.** With `Dᵢ = cᵢ • 1 + Tᵢ` and trace-free `Tᵢ`,
`‖Dᵢ + U Dⱼ Uᴴ‖² = (cᵢ + cⱼ)² r + ‖Tᵢ + U Tⱼ Uᴴ‖²`. -/
theorem norm_add_conj_trace_split {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ) (ci cj : ℝ)
    {Ti Tj : Matrix m m ℂ} (hTi : trace Ti = 0) (hTj : trace Tj = 0) :
    ‖(ci • (1 : Matrix m m ℂ) + Ti) + U * (cj • (1 : Matrix m m ℂ) + Tj) * Uᴴ‖ ^ 2 =
      (ci + cj) ^ 2 * Fintype.card m + ‖Ti + U * Tj * Uᴴ‖ ^ 2 := by
  have hU1 : U * Uᴴ = 1 := (mem_unitaryGroup_iff).1 hU
  have h : (ci • (1 : Matrix m m ℂ) + Ti) + U * (cj • (1 : Matrix m m ℂ) + Tj) * Uᴴ =
      (ci + cj) • (1 : Matrix m m ℂ) + (Ti + U * Tj * Uᴴ) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU1,
      add_smul]
    abel
  have htr : trace (Ti + U * Tj * Uᴴ) = 0 := by
    rw [trace_add, hTi, trace_mul_cycle, ← star_eq_conjTranspose, (mem_unitaryGroup_iff').1 hU,
      Matrix.one_mul, hTj, add_zero]
  rw [h, norm_sq_smul_one_add_of_trace_eq_zero _ _ htr]

/-- **Projector fields, one edge with transport.** -/
theorem norm_sub_conj_sq_add_norm_add_conj_sq_of_projector {U : Matrix m m ℂ}
    (hU : U ∈ unitaryGroup m ℂ) {P R : Matrix m m ℂ} (hP : P.IsHermitian) (hP2 : P * P = P)
    (hR : R.IsHermitian) (hR2 : R * R = R) {k : ℝ} (hkP : trace P = k) (hkR : trace R = k) :
    ‖P - U * R * Uᴴ‖ ^ 2 + ‖P + U * R * Uᴴ‖ ^ 2 = 4 * k := by
  rw [frobenius_parallelogram, norm_conj_of_mem_unitaryGroup hU, norm_sq_of_projector hP hP2 hkP,
    norm_sq_of_projector hR hR2 hkR]
  ring

end Unitary

section Constant

variable {n α : Type*} [Fintype n] [DecidableEq n] [Ring α] [StarRing α] [Algebra ℝ α]
  [StarModule ℝ α]

/-- **A real constant is invisible to the commutator book.**
`[H + c • 1, (H + c • 1)ᴴ] = [H, Hᴴ]`. -/
theorem selfCommutator_add_smul_one (H : Matrix n n α) (c : ℝ) :
    (H + c • 1) * (H + c • 1)ᴴ - (H + c • 1)ᴴ * (H + c • 1) = H * Hᴴ - Hᴴ * H := by
  rw [conjTranspose_add, conjTranspose_smul, star_trivial, conjTranspose_one]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_add, smul_smul]
  abel

/-- **A real constant moves the opposite book by `2 c (H − Hᴴ)`.**
`(H + c • 1)² − ((H + c • 1)ᴴ)² = (H² − (Hᴴ)²) + (2 c) • (H − Hᴴ)`. -/
theorem mul_self_sub_conjTranspose_mul_self_add_smul_one (H : Matrix n n α) (c : ℝ) :
    (H + c • 1) * (H + c • 1) - (H + c • 1)ᴴ * (H + c • 1)ᴴ =
      (H * H - Hᴴ * Hᴴ) + (2 * c) • (H - Hᴴ) := by
  have h2 : (2 * c) • (H - Hᴴ) = c • H + c • H - (c • Hᴴ + c • Hᴴ) := by
    rw [smul_sub, mul_smul, mul_smul, two_smul, two_smul]
  rw [h2, conjTranspose_add, conjTranspose_smul, star_trivial, conjTranspose_one]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_add, smul_smul]
  abel

end Constant

variable {ι m : Type*} {G : SimpleGraph ι}

/-- **A real constant moves the opposite book of a block transport operator by `4 c A`.**
For `H = diagonal D + A` (Hermitian blocks, skew-Hermitian `A`),
`(H + c • 1)² − ((H + c • 1)ᴴ)² = (H² − (Hᴴ)²) + (4 c) • A`. -/
theorem mul_self_sub_conjTranspose_mul_self_diagonal_add_smul_one [Fintype ι] [DecidableEq ι]
    [Fintype m] [DecidableEq m] (D : ι → Matrix m m ℂ) (hD : ∀ i, (D i).IsHermitian)
    (A : Matrix ι ι (Matrix m m ℂ)) (hA : Aᴴ = -A) (c : ℝ) :
    (diagonal D + A + c • 1) * (diagonal D + A + c • 1) -
        (diagonal D + A + c • 1)ᴴ * (diagonal D + A + c • 1)ᴴ =
      ((diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ) +
        (4 * c) • A := by
  rw [mul_self_sub_conjTranspose_mul_self_add_smul_one]
  congr 1
  have hstar : star D = D := funext fun i => hD i
  rw [conjTranspose_add, diagonal_conjTranspose, hstar, hA]
  have h : diagonal D + A - (diagonal D + -A) = A + A := by abel
  rw [h, smul_add, ← add_smul]
  congr 1
  ring

/-- **Trace split, connection book.** With `D i = c i • 1 + T i` and `trace (T i) = 0`,
`E₋(D) = r ∑_E (c i − c j)² + E₋(T)` (`r = |m|`, ordered-pair form of the edge sum). -/
theorem connectionEnergy_trace_split [Fintype ι] [DecidableRel G.Adj] [Fintype m] [DecidableEq m]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A) (c : ι → ℝ)
    {T : ι → Matrix m m ℂ} (hT : ∀ i, trace (T i) = 0) :
    connectionEnergy G A (fun i => c i • (1 : Matrix m m ℂ) + T i) =
      Fintype.card m * (∑ i, ∑ j, if G.Adj i j then (c i - c j) ^ 2 else 0) / 2 +
        connectionEnergy G A T := by
  have h : ∀ i j, (if G.Adj i j then
      ‖(c i • (1 : Matrix m m ℂ) + T i) - A i j * (c j • (1 : Matrix m m ℂ) + T j) * (A i j)ᴴ‖ ^ 2
      else 0) =
      Fintype.card m * (if G.Adj i j then (c i - c j) ^ 2 else 0) +
        (if G.Adj i j then ‖T i - A i j * T j * (A i j)ᴴ‖ ^ 2 else 0) := by
    intro i j
    split_ifs with hij
    · rw [norm_sub_conj_trace_split (hA.mem_unitaryGroup i j hij) (c i) (c j) (hT i) (hT j)]
      ring
    · simp
  rw [connectionEnergy, connectionEnergy]
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **Trace split, opposite book.** With `D i = c i • 1 + T i` and `trace (T i) = 0`,
`E₊(D) = r ∑_E (c i + c j)² + E₊(T)`. -/
theorem oppositeEnergy_trace_split [Fintype ι] [DecidableRel G.Adj] [Fintype m] [DecidableEq m]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A) (c : ι → ℝ)
    {T : ι → Matrix m m ℂ} (hT : ∀ i, trace (T i) = 0) :
    oppositeEnergy G A (fun i => c i • (1 : Matrix m m ℂ) + T i) =
      Fintype.card m * (∑ i, ∑ j, if G.Adj i j then (c i + c j) ^ 2 else 0) / 2 +
        oppositeEnergy G A T := by
  have h : ∀ i j, (if G.Adj i j then
      ‖(c i • (1 : Matrix m m ℂ) + T i) + A i j * (c j • (1 : Matrix m m ℂ) + T j) * (A i j)ᴴ‖ ^ 2
      else 0) =
      Fintype.card m * (if G.Adj i j then (c i + c j) ^ 2 else 0) +
        (if G.Adj i j then ‖T i + A i j * T j * (A i j)ᴴ‖ ^ 2 else 0) := by
    intro i j
    split_ifs with hij
    · rw [norm_add_conj_trace_split (hA.mem_unitaryGroup i j hij) (c i) (c j) (hT i) (hT j)]
      ring
    · simp
  rw [oppositeEnergy, oppositeEnergy]
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **Projector fields, summed.** If every `P i` is a Hermitian idempotent of trace `k`, then
`E₋ + E₊ = 4 k |E|`. -/
theorem connectionEnergy_add_oppositeEnergy_of_projector [Fintype ι] [DecidableEq ι]
    [DecidableRel G.Adj] [Fintype m] [DecidableEq m] {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {P : ι → Matrix m m ℂ} (hP : ∀ i, (P i).IsHermitian)
    (hP2 : ∀ i, P i * P i = P i) {k : ℝ} (hk : ∀ i, trace (P i) = k) :
    connectionEnergy G A P + oppositeEnergy G A P = 4 * k * G.edgeFinset.card := by
  rw [connectionEnergy_add_oppositeEnergy_eq_degree hA]
  have h : ∀ i, ‖P i‖ ^ 2 = k := fun i => norm_sq_of_projector (hP i) (hP2 i) (hk i)
  simp_rw [h]
  rw [← Finset.sum_mul, ← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
  push_cast
  ring

section DoubleCover

variable (G) in
/-- The bipartite double cover of `G`: vertices `(i, s)` with `s : Bool`, and `(i, s) ~ (j, t)`
iff `i ~ j` and `s ≠ t`. -/
def doubleCover : SimpleGraph (ι × Bool) where
  Adj a b := G.Adj a.1 b.1 ∧ a.2 ≠ b.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun a h => G.irrefl h.1⟩

theorem doubleCover_adj {a b : ι × Bool} :
    (doubleCover G).Adj a b ↔ G.Adj a.1 b.1 ∧ a.2 ≠ b.2 := Iff.rfl

instance [DecidableRel G.Adj] : DecidableRel (doubleCover G).Adj := fun a b =>
  inferInstanceAs (Decidable (G.Adj a.1 b.1 ∧ a.2 ≠ b.2))

/-- Every edge of the double cover joins the `true` sheet to the `false` sheet. -/
theorem doubleCover_adj_imp {a b : ι × Bool} (h : (doubleCover G).Adj a b) :
    (a.2 = true ↔ ¬ b.2 = true) := by
  obtain ⟨i, s⟩ := a
  obtain ⟨j, t⟩ := b
  have hne : s ≠ t := h.2
  cases s <;> cases t <;> simp at hne ⊢

variable (A : Matrix ι ι (Matrix m m ℂ)) in
/-- The connection `A` lifted to the double cover: `A i j` on the lifted edges, `0` elsewhere. -/
def liftConnection : Matrix (ι × Bool) (ι × Bool) (Matrix m m ℂ) :=
  Matrix.of fun a b => if a.2 ≠ b.2 then A a.1 b.1 else 0

@[simp]
theorem liftConnection_apply (A : Matrix ι ι (Matrix m m ℂ)) (a b : ι × Bool) :
    liftConnection A a b = if a.2 ≠ b.2 then A a.1 b.1 else 0 := rfl

/-- The lift of a unitary connection on `G` is a unitary connection on the double cover. -/
theorem IsUnitaryConnection.liftConnection [Fintype m] [DecidableEq m]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A) :
    IsUnitaryConnection (doubleCover G) (liftConnection A) where
  conjTranspose_eq_neg := by
    refine Matrix.ext fun a b => ?_
    rw [conjTranspose_apply, Matrix.neg_apply, liftConnection_apply, liftConnection_apply]
    by_cases h : a.2 = b.2
    · simp [h]
    · have h' : ¬ b.2 = a.2 := fun e => h e.symm
      simp only [ne_eq, h, h', not_false_eq_true, ↓reduceIte]
      rw [star_eq_conjTranspose, hA.apply_eq_neg_conjTranspose b.1 a.1, conjTranspose_neg,
        conjTranspose_conjTranspose]
  eq_zero_of_not_adj := by
    intro a b h
    rw [liftConnection_apply]
    split_ifs with hs
    · exact hA.eq_zero_of_not_adj _ _ fun hadj => h ⟨hadj, hs⟩
    · rfl
  mem_unitaryGroup := by
    intro a b h
    rw [liftConnection_apply]
    simp only [ne_eq, h.2, not_false_eq_true, ↓reduceIte]
    exact hA.mem_unitaryGroup _ _ h.1

/-- The field `(S + T, S − T)` on the double cover: `S i + T i` on the `true` sheet and
`S i − T i` on the `false` sheet. -/
def coverField (S T : ι → Matrix m m ℂ) : ι × Bool → Matrix m m ℂ :=
  fun a => match a.2 with
    | true => S a.1 + T a.1
    | false => S a.1 - T a.1

@[simp]
theorem coverField_true (S T : ι → Matrix m m ℂ) (i : ι) :
    coverField S T (i, true) = S i + T i := rfl

@[simp]
theorem coverField_false (S T : ι → Matrix m m ℂ) (i : ι) :
    coverField S T (i, false) = S i - T i := rfl

/-- The cover field is Hermitian when `S` and `T` are. -/
theorem coverField_isHermitian {S T : ι → Matrix m m ℂ} (hS : ∀ i, (S i).IsHermitian)
    (hT : ∀ i, (T i).IsHermitian) (a : ι × Bool) : (coverField S T a).IsHermitian := by
  obtain ⟨i, s⟩ := a
  cases s
  · exact (hS i).sub (hT i)
  · exact (hS i).add (hT i)

/-- A double sum over `ι × Bool`, reordered as a double sum over `ι` of a double sum over
`Bool`. -/
theorem sum_sum_prod_bool [Fintype ι] {β : Type*} [AddCommMonoid β]
    (f : ι × Bool → ι × Bool → β) :
    ∑ a, ∑ b, f a b = ∑ i, ∑ j, ∑ s : Bool, ∑ t : Bool, f (i, s) (j, t) := by
  simp only [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- **The double cover.** The connection energy of the field `(S + T, S − T)` on the bipartite
double cover of `G`, for the lifted connection, is `2 E₋(S) + 2 E₊(T)`: the two books are the
even and odd halves of one connection energy on the double cover. No unitarity is needed. -/
theorem connectionEnergy_doubleCover [Fintype ι] [DecidableRel G.Adj] [Fintype m] [DecidableEq m]
    (A : Matrix ι ι (Matrix m m ℂ)) (S T : ι → Matrix m m ℂ) :
    connectionEnergy (doubleCover G) (liftConnection A) (coverField S T) =
      2 * connectionEnergy G A S + 2 * oppositeEnergy G A T := by
  have key : ∀ i j, (∑ s : Bool, ∑ t : Bool, if (doubleCover G).Adj (i, s) (j, t) then
      ‖coverField S T (i, s) - liftConnection A (i, s) (j, t) * coverField S T (j, t) *
        (liftConnection A (i, s) (j, t))ᴴ‖ ^ 2 else 0) =
      2 * (if G.Adj i j then ‖S i - A i j * S j * (A i j)ᴴ‖ ^ 2 else 0) +
        2 * (if G.Adj i j then ‖T i + A i j * T j * (A i j)ᴴ‖ ^ 2 else 0) := by
    intro i j
    by_cases hij : G.Adj i j
    · simp only [Fintype.sum_bool, doubleCover_adj, liftConnection_apply, coverField_true,
        coverField_false, hij, ne_eq, not_true_eq_false, and_false, Bool.true_eq_false,
        Bool.false_eq_true, not_false_eq_true, and_true, ↓reduceIte, zero_add, add_zero]
      exact doubleCover_edge_core (A i j) (S i) (T i) (S j) (T j)
    · simp only [doubleCover_adj, hij, false_and, ↓reduceIte, Finset.sum_const_zero, mul_zero,
        add_zero]
  rw [connectionEnergy, connectionEnergy, oppositeEnergy, sum_sum_prod_bool]
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end DoubleCover

/-- **The product of the two books.** `E₋ E₊ = ((E₋ + E₊)/2)² − ((E₋ − E₊)/2)²`, and with
`E₋ + E₊ = 2 ‖D A‖²`, `E₋ − E₊ = 2 re (trace ((D A)²))` substituted,
`E₋ E₊ = ‖D A‖⁴ − (re (trace (X * X)))²` for the flattened `X = comp (diagonal D * A)`. -/
theorem connectionEnergy_mul_oppositeEnergy [Fintype ι] [DecidableEq ι] [DecidableRel G.Adj]
    [Fintype m] [DecidableEq m] {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A)
    {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    connectionEnergy G A D * oppositeEnergy G A D =
      (‖diagonal D * A‖ ^ 2) ^ 2 - (RCLike.re
        (trace (comp ι ι m m ℂ (diagonal D * A) * comp ι ι m m ℂ (diagonal D * A)))) ^ 2 := by
  have hs := norm_sq_selfCommutator_add_norm_sq_mul_self_sub_div_eight D hD A
    hA.conjTranspose_eq_neg
  have hd := norm_sq_selfCommutator_sub_norm_sq_mul_self_sub_div_eight D hD A
    hA.conjTranspose_eq_neg
  rw [norm_sq_selfCommutator_div_eight hA hD,
    norm_sq_mul_self_sub_conjTranspose_mul_self_div_eight hA hD] at hs hd
  linear_combination ((connectionEnergy G A D + oppositeEnergy G A D +
      2 * ‖diagonal D * A‖ ^ 2) / 4) * hs -
    ((connectionEnergy G A D - oppositeEnergy G A D + 2 * RCLike.re
      (trace (comp ι ι m m ℂ (diagonal D * A) * comp ι ι m m ℂ (diagonal D * A)))) / 4) * hd

end NonNormality
