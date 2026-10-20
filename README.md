# Non-normality is connection energy — Lean 4 formalization

Lean 4 / Mathlib formalization of

> Jeromie Beasley, *Non-normality is connection energy*, 17 September 2026,
> Zenodo record 22804072 (v7).

Every mathematical statement of the paper is proved, together with the opposite
(anticommutator) identity and its corollaries found on 20 October 2026, and the statements of
version 11 of the paper ("the two books": the twisted-holonomy kernel, constants and the trace
split, the per-edge duality, projector fields, the bipartite double cover, the product of the two
books, passive fields). Everything is proved with no `sorry`, no warnings and only the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Setting

`G : SimpleGraph ι` is a finite graph, `m` a finite type (the fibre `ℂ^r`). An operator
`H = diagonal D + A : Matrix ι ι (Matrix m m ℂ)` has Hermitian diagonal blocks `D i` and a
**unitary connection** `A` (`IsUnitaryConnection G A`): `Aᴴ = -A`, `A i j = 0` off the edges,
`A i j` unitary on the edges. Frobenius norms throughout (`open scoped Matrix.Norms.Frobenius`).

## Main theorems (namespace `NonNormality`)

```lean
-- Identity (1): self-commutator energy = connection energy
theorem norm_sq_selfCommutator_div_eight (hA : IsUnitaryConnection G A)
    (hD : ∀ i, (D i).IsHermitian) :
    ‖(diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)‖ ^ 2 / 8 =
      connectionEnergy G A D
-- where connectionEnergy G A D
--   = (∑ i, ∑ j, if G.Adj i j then ‖D i - A i j * D j * (A i j)ᴴ‖ ^ 2 else 0) / 2
-- (= the sum over edges; edge form: norm_sq_selfCommutator_div_eight_eq_sum_edgeFinset;
--  flattened (ι × m)-matrix form: norm_sq_selfCommutator_comp_div_eight)

-- Identity (2): normal ⇔ parallel
theorem isStarNormal_iff_isParallel (hA : IsUnitaryConnection G A)
    (hD : ∀ i, (D i).IsHermitian) :
    IsStarNormal (diagonal D + A) ↔ ∀ i j, G.Adj i j → D i = A i j * D j * (A i j)ᴴ

-- Identity (3): on a connected graph, parallel Hermitian sections ≅ holonomy-fixed matrices
noncomputable def parallelSectionsEquivHolonomyFixed (hA : IsUnitaryConnection G A)
    (hG : G.Connected) (i₀ : ι) : parallelSections G A ≃ₗ[ℝ] holonomyFixed G A i₀
-- holonomyFixed G A i₀ = {X | X.IsHermitian ∧ ∀ p : G.Walk i₀ i₀,
--                               holonomy A p * X * (holonomy A p)ᴴ = X}
--   (equivalently Commute X (holonomy A p): mem_holonomyFixed_iff_commute)

-- General form, no unitarity, and the scalar (weighted Dirichlet) case
theorem norm_sq_selfCommutator_eq (hD) (hA : Aᴴ = -A) :
    ‖[H, Hᴴ]‖ ^ 2 = 4 * ∑ i, ∑ j, ‖D i * A i j - A i j * D j‖ ^ 2
theorem norm_sq_selfCommutator_scalar (d : ι → ℝ) (a : Matrix ι ι ℂ) (ha : aᴴ = -a) :
    ‖[H, Hᴴ]‖ ^ 2 = 4 * ∑ i, ∑ j, ‖a i j‖ ^ 2 * (d i - d j) ^ 2
```

## The opposite: anticommutator energy

Since `Hᴴ = D − A`, the squared operator satisfies `H² − (Hᴴ)² = 2{D, A}` with the
anticommutator in place of the commutator, and on an edge `{D, A}ᵢⱼ = (Dᵢ + AᵢⱼDⱼAᵢⱼᴴ)Aᵢⱼ`.
Module `NonNormality/Opposite.lean` (namespace `NonNormality`) proves the mirror of identities
(1) and (2) and how the two energies fit together:

```lean
-- Opposite identity: ⅛‖H² − (Hᴴ)²‖² = ∑_{{i,j} ∈ E} ‖D i + A i j * D j * (A i j)ᴴ‖²
theorem norm_sq_mul_self_sub_conjTranspose_mul_self_div_eight (hA : IsUnitaryConnection G A)
    (hD : ∀ i, (D i).IsHermitian) :
    ‖(diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ‖ ^ 2 / 8 =
      oppositeEnergy G A D
-- H² Hermitian ⇔ D anti-parallel (D i = -(A i j * D j * (A i j)ᴴ) on every edge)
theorem mul_self_eq_conjTranspose_mul_self_iff_isAntiParallel (hA) (hD) :
    (diagonal D + A) * (diagonal D + A) = (diagonal D + A)ᴴ * (diagonal D + A)ᴴ ↔
      IsAntiParallel G A D
-- The budget (parallelogram law on each edge)
theorem connectionEnergy_add_oppositeEnergy_eq_degree (hA) (D) :
    connectionEnergy G A D + oppositeEnergy G A D = 2 * ∑ i, (G.degree i : ℝ) * ‖D i‖ ^ 2
-- H normal and H² Hermitian ⇒ D i = 0 at every vertex with an edge
theorem eq_zero_of_isStarNormal_of_mul_self_eq (hA) (hD) (hn : IsStarNormal (diagonal D + A))
    (hs : (diagonal D + A) * (diagonal D + A) = (diagonal D + A)ᴴ * (diagonal D + A)ᴴ)
    (hij : G.Adj i j) : D i = 0
-- Sum and difference of the two energies, X = comp (diagonal D * A) (the flattened DA)
theorem norm_sq_selfCommutator_add_norm_sq_mul_self_sub_div_eight :
    ⅛‖[H, Hᴴ]‖² + ⅛‖H² − (Hᴴ)²‖² = 2 * ‖diagonal D * A‖ ^ 2
theorem norm_sq_selfCommutator_sub_norm_sq_mul_self_sub_div_eight :
    ⅛‖[H, Hᴴ]‖² − ⅛‖H² − (Hᴴ)²‖² = 2 * re (trace (X * X))
-- Bipartite swap: flipping the sign of D on one side exchanges the two energies
theorem connectionEnergy_eq_oppositeEnergy_of_bipartite
theorem oppositeEnergy_eq_connectionEnergy_of_bipartite
```

Anti-parallel sections are transported along a walk of length `n` by `(−1)ⁿ` times the holonomy
(`IsAntiParallel.eq_conj_holonomy`).

## Version 11: the two books

`STATEMENTS.md`, section "v11: the two books", maps every statement to its Lean name. The
headline results:

```lean
-- The twisted kernel (mirror of identity (3)): on a connected graph, anti-parallel Hermitian
-- sections ≅ Hermitian matrices fixed by the parity-twisted holonomy of every closed walk at i₀
noncomputable def antiParallelSectionsEquivTwistedHolonomyFixed (hA : IsUnitaryConnection G A)
    (hG : G.Connected) (i₀ : ι) : antiParallelSections G A ≃ₗ[ℝ] twistedHolonomyFixed G A i₀
-- twistedHolonomyFixed G A i₀ = {X | X.IsHermitian ∧ ∀ p : G.Walk i₀ i₀,
--     (-1) ^ p.length • (holonomy A p * X * (holonomy A p)ᴴ) = X}
-- An odd closed walk whose holonomy commutes with the field kills it (eq_zero_of_odd_loop);
-- on a bipartite graph the sign flip exchanges parallel and anti-parallel sections
noncomputable def antiParallelSectionsEquivParallelSections (hS : ∀ i j, G.Adj i j → (i ∈ S ↔ j ∉ S)) :
    antiParallelSections G A ≃ₗ[ℝ] parallelSections G A

-- Constants: [H + c • 1, (H + c • 1)ᴴ] = [H, Hᴴ] and, for H = diagonal D + A,
-- (H + c • 1)² − ((H + c • 1)ᴴ)² = (H² − (Hᴴ)²) + (4 c) • A
theorem selfCommutator_add_smul_one (H : Matrix n n α) (c : ℝ) :
    (H + c • 1) * (H + c • 1)ᴴ - (H + c • 1)ᴴ * (H + c • 1) = H * Hᴴ - Hᴴ * H
theorem mul_self_sub_conjTranspose_mul_self_diagonal_add_smul_one (D) (hD) (A) (hA : Aᴴ = -A) (c) :
    (diagonal D + A + c • 1) * (diagonal D + A + c • 1) -
        (diagonal D + A + c • 1)ᴴ * (diagonal D + A + c • 1)ᴴ =
      ((diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ) + (4 * c) • A
-- Trace split: D i = c i • 1 + T i with trace (T i) = 0 (no cross term)
theorem connectionEnergy_trace_split (hA) (c : ι → ℝ) (hT : ∀ i, trace (T i) = 0) :
    connectionEnergy G A (fun i => c i • 1 + T i) =
      Fintype.card m * (∑ i, ∑ j, if G.Adj i j then (c i - c j) ^ 2 else 0) / 2 +
        connectionEnergy G A T
-- (oppositeEnergy_trace_split: the same with + in place of −)

-- Per-edge duality, with frobeniusInner a b = re (trace (aᴴ * b)): P² + V² + L² = 1
theorem duality_sum_sq (a b : Matrix m m ℂ) (hs : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≠ 0) :
    ((‖a‖ ^ 2 - ‖b‖ ^ 2) / (‖a‖ ^ 2 + ‖b‖ ^ 2)) ^ 2 +
      ((‖a + b‖ ^ 2 - ‖a - b‖ ^ 2) / (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2)) ^ 2 +
      4 * (‖a‖ ^ 2 * ‖b‖ ^ 2 - frobeniusInner a b ^ 2) / (‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 = 1
-- (frobeniusInner_sq_le: Cauchy–Schwarz, so L² ≥ 0; duality_le_one: P² + V² ≤ 1;
--  scalar_edge_reflection, scalar_edge_flux: the scalar edge)
-- Passive fields (NonNormality/Passive.lean): PSD blocks give E₋,e ≤ E₊,e
theorem norm_sub_conj_sq_le_norm_add_conj_sq_of_posSemidef (hi : Di.PosSemidef) (hj : Dj.PosSemidef) (U) :
    ‖Di - U * Dj * Uᴴ‖ ^ 2 ≤ ‖Di + U * Dj * Uᴴ‖ ^ 2

-- Projector fields: Hermitian idempotents of trace k give ‖P − R‖² + ‖P + R‖² = 4 k,
-- and summed, E₋ + E₊ = 4 k |E|
theorem norm_sub_sq_add_norm_add_sq_of_projector (hP) (hP2 : P * P = P) (hR) (hR2) (hkP : trace P = k)
    (hkR : trace R = k) : ‖P - R‖ ^ 2 + ‖P + R‖ ^ 2 = 4 * k
theorem connectionEnergy_add_oppositeEnergy_of_projector (hA) (hP) (hP2) (hk : ∀ i, trace (P i) = k) :
    connectionEnergy G A P + oppositeEnergy G A P = 4 * k * G.edgeFinset.card

-- The bipartite double cover doubleCover G on ι × Bool, lifted connection liftConnection A,
-- field coverField S T = (S + T on the true sheet, S − T on the false sheet); no unitarity needed
theorem connectionEnergy_doubleCover (A : Matrix ι ι (Matrix m m ℂ)) (S T : ι → Matrix m m ℂ) :
    connectionEnergy (doubleCover G) (liftConnection A) (coverField S T) =
      2 * connectionEnergy G A S + 2 * oppositeEnergy G A T

-- The product of the two books, X = comp (diagonal D * A)
theorem connectionEnergy_mul_oppositeEnergy (hA) (hD) :
    connectionEnergy G A D * oppositeEnergy G A D =
      (‖diagonal D * A‖ ^ 2) ^ 2 - (re (trace (X * X))) ^ 2
```

Not proved (see `LIMITATIONS.md`): the ring floors of the scalar-angle model
(`numerics/two_books_lockin.py`).

## Files

| File | Content |
|---|---|
| `NonNormality/Frobenius.lean` | `‖A‖² = ∑‖Aᵢⱼ‖²`, `‖A‖² = re tr(AᴴA)`, unitary invariance of the Frobenius norm |
| `NonNormality/SelfCommutator.lean` | identities (1), (2), general and scalar forms, edge-sum lemma |
| `NonNormality/Holonomy.lean` | walk holonomy, transport, identity (3) |
| `NonNormality/Flatten.lean` | `Matrix.comp` commutes with `ᴴ`, preserves the Frobenius norm; (1), (2) for the flattened matrix |
| `NonNormality/Opposite.lean` | the opposite (anticommutator) energy: identity, anti-parallel criterion, budget, normal-and-Hermitian-square corollary, sum and difference, bipartite swap |
| `NonNormality/AntiHolonomy.lean` | anti-parallel sections, the parity-twisted holonomy kernel (mirror of (3)), odd loops, the bipartite sign flip |
| `NonNormality/TwoBooks.lean` | constants and the trace split, per-edge duality `P² + V² + L² = 1`, projector fields, the bipartite double cover, the product of the two books |
| `NonNormality/Passive.lean` | positive semidefinite blocks: `E₋,e ≤ E₊,e` |
| `checks/Necessity.lean` | proves Hermitian `D` is necessary (normal but non-parallel example) |
| `checks/Negations.lean` | proves that each of the four v11 false controls is actually false (concrete counterexamples) |
| `FalseControls/` | 12 false statements that must fail to compile |
| `scripts/check_all.py` | runs every check, writes `verification/report.json` |
| `.github/workflows/ci.yml` | runs `scripts/check_all.py` on GitHub Actions on every push |
| `numerics/` | numerical checks of the paper (`check_paper.py`), of the opposite results (`anti_connection_*.py`, `two_books_map.py`, `two_books_gravity.py`) and of v11 (`two_books_duality.py`, `two_books_projectors.py`, `two_books_trace.py`, `two_books_lockin.py`) |
| `STATEMENTS.md` | every statement of the paper, classified, with remarks |
| `MATHLIB_FIT.md` | what could go to Mathlib, names, placement, verdict |

## Build and check

Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`, pinned in
`lake-manifest.json`).

```
lake build
python3 scripts/check_all.py
```

The same script runs on GitHub Actions (`.github/workflows/ci.yml`) on every push: build with no
warnings, `leanchecker` kernel replay of every module, the axiom audit of every declaration, the
false controls, the Mathlib linters. The run uploads `verification/` as an artifact.

## License

Code: MIT OR Apache-2.0 (see `LICENSE`). Copyright (c) 2026 Jeromie Beasley.
