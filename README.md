# Non-normality is connection energy — Lean 4 formalization

Lean 4 / Mathlib formalization of

> Jeromie Beasley, *Non-normality is connection energy*, 17 September 2026,
> Zenodo record 22804072 (v7).

Every mathematical statement of the paper is proved, together with the opposite
(anticommutator) identity and its corollaries found on 20 October 2026. Everything is proved
with no `sorry`, no warnings and only the three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

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
(`IsAntiParallel.eq_conj_holonomy`). The converse, a twisted analogue of identity (3), is not
proved here (see `LIMITATIONS.md`).

## Files

| File | Content |
|---|---|
| `NonNormality/Frobenius.lean` | `‖A‖² = ∑‖Aᵢⱼ‖²`, `‖A‖² = re tr(AᴴA)`, unitary invariance of the Frobenius norm |
| `NonNormality/SelfCommutator.lean` | identities (1), (2), general and scalar forms, edge-sum lemma |
| `NonNormality/Holonomy.lean` | walk holonomy, transport, identity (3) |
| `NonNormality/Flatten.lean` | `Matrix.comp` commutes with `ᴴ`, preserves the Frobenius norm; (1), (2) for the flattened matrix |
| `NonNormality/Opposite.lean` | the opposite (anticommutator) energy: identity, anti-parallel criterion, budget, normal-and-Hermitian-square corollary, sum and difference, bipartite swap |
| `checks/Necessity.lean` | proves Hermitian `D` is necessary (normal but non-parallel example) |
| `FalseControls/` | 8 false statements that must fail to compile |
| `scripts/check_all.py` | runs every check, writes `verification/report.json` |
| `.github/workflows/ci.yml` | runs `scripts/check_all.py` on GitHub Actions on every push |
| `numerics/` | numerical checks of the paper (`check_paper.py`) and of the opposite results (`anti_connection_*.py`, `two_books_*.py`) |
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
