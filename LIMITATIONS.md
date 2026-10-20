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

## Version 11 (the two books): proved

`STATEMENTS.md`, section "v11: the two books", has the full table. In short:

* **The twisted-holonomy kernel** (`AntiHolonomy.lean`): on a connected graph the Hermitian
  anti-parallel sections are `ℝ`-linearly isomorphic, by evaluation at `i₀`, to the Hermitian `X`
  with `(−1)^{len C} W_C X W_Cᴴ = X` for every closed walk `C` at `i₀`
  (`antiParallelSectionsEquivTwistedHolonomyFixed`). An odd closed walk whose holonomy commutes
  with the field forces the field to vanish; on a bipartite graph the sign flip on one side is an
  `ℝ`-linear isomorphism between anti-parallel and parallel sections.
* **Constants and the trace split** (`TwoBooks.lean`): `[H + c • 1, (H + c • 1)ᴴ] = [H, Hᴴ]`,
  `(H + c • 1)² − ((H + c • 1)ᴴ)² = (H² − (Hᴴ)²) + (4 c) • A`, and with `D i = c i • 1 + T i`,
  `trace (T i) = 0`, each book splits as `r ∑_E (c i ∓ c j)² + ∑_E ‖T i ∓ U T j‖²` with no cross
  term.
* **Per-edge duality** (`TwoBooks.lean`): `P² + V² + L² = 1` with the third leg a Gram
  determinant, `L² ≥ 0` by Cauchy–Schwarz, hence `P² + V² ≤ 1`; the scalar edge in reflection
  form. **Passive fields** (`Passive.lean`): positive semidefinite blocks give `E₋,e ≤ E₊,e`.
* **Projector fields**: `‖P − R‖² + ‖P + R‖² = 4 k`, and `E₋ + E₊ = 4 k |E|`.
* **The double cover**: the graph `doubleCover G` on `ι × Bool` and the lifted connection are
  modelled; the field `(S + T, S − T)` has connection energy `2 E₋(S) + 2 E₊(T)`.
* **The product**: `E₋ E₊ = ‖D A‖⁴ − (re (trace ((D A)²)))²`.

## Version 11: not proved

* **The ring floors** of the scalar-angle model (`numerics/two_books_lockin.py`): that
  `∑_k (1 − cos x_k)` subject to `∑ x_k ≡ d (mod 2π)` is at least `min_w N (1 − cos((d − 2πw)/N))`,
  and the interleaving of the two floors for odd `N`. This is a constrained minimisation over the
  torus, not an algebraic identity; it is checked numerically only.
* `Γ = tanh(ln(dᵢ/dⱼ)/2)` and the principal-angle forms `E₋,e = 2 ∑ sin² θ`,
  `E₊,e = 2 ∑ (1 + cos² θ)` for projector fields are not formalized (elementary; the algebraic
  content used by the paper, `E₊,e = 4 k − E₋,e`, is proved).
* The trace splits and the projector budget are stated in the ordered-pair form of the edge sum
  (half the sum over ordered adjacent pairs), as `connectionEnergy` itself is.
* The per-edge duality is proved for arbitrary (not necessarily Hermitian) `a`, `b` with the real
  inner product `re (trace (aᴴ * b))`; for Hermitian `a` this is `re (trace (a * b))`
  (`frobeniusInner_eq_re_trace_mul`).

## Opposite results: not proved

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
