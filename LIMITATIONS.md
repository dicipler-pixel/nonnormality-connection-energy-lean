# LIMITATIONS

## Proved (no `sorry`, no warnings, standard axioms only)

* Identity (1) in three forms: ordered pairs (Mathlib's `lapMatrix` convention), sum over
  `G.edgeFinset`, and for the flattened `(ι × m) × (ι × m)` complex matrix.
* The general identity without unitarity, `‖[H,Hᴴ]‖² = 4 ∑ᵢⱼ ‖DᵢAᵢⱼ − AᵢⱼDⱼ‖²`, and the
  scalar weighted Dirichlet identity.
* Identity (2), normality ⇔ parallel, for the block and the flattened operator.
* Identity (3) as an explicit `ℝ`-linear equivalence, on any connected graph (the equivalence does
  not even need `ι` finite), plus the commutant form `[X, W_C] = 0`.
* Necessity of the Hermitian hypothesis (`checks/Necessity.lean`).

## Choices of formulation

* The operator lives in `Matrix ι ι (Matrix m m ℂ)` (blocks as entries). The flattened statements
  in `Flatten.lean` translate to `Matrix (ι × m) (ι × m) ℂ` via Mathlib's `Matrix.comp`.
* "Loops `C` based at `i₀`" are all closed walks `G.Walk i₀ i₀`. Restricting to cycles should give
  the same fixed set (closed walks decompose into cycles and backtracks, and a backtrack has
  holonomy `±1`), but that equivalence is not proved here.
* "`Hol(i₀)`" is not built as a group; the fixed set is defined by conjugation by every loop
  holonomy, which is what the paper's formula (3) says.
* `ker E_A` is formalized as the zero set of the energy on Hermitian `D`, as a submodule
  (`parallelSections`), with `mem_parallelSections_iff_connectionEnergy_eq_zero`.

## Not formalized

* The differential-geometric reading ("a connection in the ordinary sense", "the classical
  correspondence between parallel sections and holonomy-fixed endomorphisms"): interpretation,
  not a statement. Its discrete content is what is proved.
* The novelty/priority sentence and the June 18, 2026 origin remark (`JB_{n+1} − B_nJ`): not
  mathematical statements and the objects are not defined in the paper.
* No dimension count of `ker E_A` (e.g. `dim = dim` of the commutant of the holonomy group in
  `Herm(r)`) is given; the paper does not state one.

## Verification scope

* Checked on this box only: `lake build`, `leanchecker` kernel replay, axiom audit, `#lint`,
  Mathlib standard linter set, `lake exe lint-style`. Nothing has been checked by a Mathlib
  reviewer. Nothing has been pushed anywhere.
