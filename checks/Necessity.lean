import NonNormality

/-!
Why `D i` must be Hermitian (a check, compiled with warnings as errors).

On the single edge `0 — 1` with `A 0 1 = 1`, `A 1 0 = -1` (unitary, skew-Hermitian) and the
non-Hermitian potentials `D 0 = I`, `D 1 = -I`, the operator `H = !![I, 1; -1, -I]` is normal,
yet `D 0 ≠ A 0 1 * D 1 * star (A 0 1)`. So identities (1) and (2) fail without `D i = (D i)ᴴ`.
-/

open Matrix Complex

/-- `!![I, 1; -1, -I]` is normal. -/
example : IsStarNormal !![I, 1; -1, -I] := by
  rw [isStarNormal_iff, commute_iff_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose, conjTranspose_apply]

/-- ...but the potentials `I` and `-I` are not parallel along the edge. -/
example : (I : ℂ) ≠ 1 * -I * star 1 := by
  simp only [star_one, one_mul, mul_one, ne_eq]
  intro h
  have := congrArg Complex.im h
  norm_num at this
