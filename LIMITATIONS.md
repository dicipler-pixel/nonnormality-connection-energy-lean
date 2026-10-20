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
* The opposite results of 20 October 2026 (`Opposite.lean`, `STATEMENTS.md` O1–O8): the opposite
  identity `⅛‖H² − (Hᴴ)²‖² = Σ_E ‖Dᵢ + AᵢⱼDⱼAᵢⱼᴴ‖²`, its zero set (anti-parallel `D`), the budget
  `E₋ + E₊ = 2 Σᵢ deg(i)‖Dᵢ‖²`, the operator forms of the sum (`2‖DA‖²`) and of the difference
  (`2 Re Tr((DA)²)`), the corollary that `H` normal with `H²` Hermitian forces `Dᵢ = 0` at every
  non-isolated vertex, the bipartite swap, and transport of anti-parallel sections with the sign
  `(−1)^length`.

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

## Opposite results: not proved

* **The twisted-holonomy kernel.** That on a connected graph the anti-parallel Hermitian sections
  correspond to the Hermitian `X` with `(−1)^{len C} W_C X W_Cᴴ = X` for every loop `C` at `i₀`
  (the analogue of identity (3) for `E₊`) is not proved. Only the necessary direction is proved
  (`IsAntiParallel.eq_conj_holonomy`); the extension of such an `X` to a section is not. The
  equivalence was checked numerically on cycles (`numerics/anti_connection_kernel.py`).
* **The double-cover reading** (`E₋` and `E₊` as the even and odd halves of one connection energy
  on the bipartite double cover) is checked numerically (`numerics/two_books_map.py`, T3) but not
  formalized; nor are the per-edge reflection coefficient and the passive-field bound (T1, T2).
* **The light and gravity readings** of the two energies, including the identification of
  `g(X) = ½ Re Tr(X²)` with the trace form of the gravity paper, are interpretations, not
  mathematical statements, and are not formalized. What is proved is the identity
  `E₋ − E₊ = 2 Re Tr((DA)²)`.
* The difference identity uses the trace of the flattened `(ι × m) × (ι × m)` matrix
  `comp (diagonal D * A)`; no block-trace version is stated.
* The bipartite swap is stated with an explicit set `S` such that every edge joins `S` to its
  complement, not with a Mathlib bipartiteness predicate.

## Verification scope

* The original modules were checked on the author's machine (logs in `verification/`, 18 Oct
  2026). From 20 October 2026 every push runs the same checks on GitHub Actions
  (`.github/workflows/ci.yml`): `lake build` with no warnings, `leanchecker` kernel replay, axiom
  audit, false controls, `#lint`, Mathlib standard linter set, `lake exe lint-style`. The
  committed `verification/` logs are from the 18 Oct run; CI regenerates them and uploads them as
  an artifact. Nothing has been checked by a Mathlib reviewer, and nothing has been submitted to
  Mathlib.
