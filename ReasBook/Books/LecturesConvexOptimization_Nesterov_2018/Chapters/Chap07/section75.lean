import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_75 (from Chap07) -/
open scoped BigOperators
open Matrix

noncomputable section

/- Definition 7.75 lies in the finite-horizon simplex-portfolio / attained-maximum domain.

Mandatory domain-style sampling before refinement:
- mathlib `stdSimplex`, the canonical owner for simplex-valued portfolio weights;
- mathlib `IsMaxOn`, the canonical owner for maximizers on a feasible set;
- mathlib `isMaxOn_iff`, the direct bridge from `IsMaxOn` to the textbook pointwise maximality
  condition;
- `sSup`, the canonical value owner for optimal objective values once the chosen maximizer is
  separated from the optimal value.

Best owner abstraction:
- source-facing: the cumulative return of a constant-share portfolio, the argmax set of optimal
  constant-share portfolios on `P`, and the corresponding optimal average growth rate;
- core/canonical: `stdSimplex NNReal (Fin n)`, `IsMaxOn`, and `sSup` on the image of the
  cumulative-return objective;
- bridge/view: the expansion theorems below and the attained-maximum comparison lemmas for members
  of the optimal-portfolio argmax set.

Primitive data:
- the price-relative sequence `c`;
- a constant-share portfolio `x : stdSimplex NNReal (Fin n)`;
- a feasible set `P` of such portfolios.

Derived API:
- the cumulative-return objective `x ↦ ∏_{k=0}^N ⟪c_k, x⟫`;
- the argmax set of optimal constant-share portfolios on `P`;
- the optimal cumulative return and its derived average growth rate.

Source/core/bridge triage:
- source-facing: `constantShareObjective`, `optimalConstantShareArgmax`,
  `optimalConstantShareCumulativeReturn`, and `optimalAverageGrowthRate`;
- core/canonical: `stdSimplex NNReal (Fin n)`, `IsMaxOn`, and `sSup`;
- bridge/view: the membership/value formulas relating these owners back to the textbook
  `argmax` and geometric-mean expressions.

The source names an arbitrary optimizer `x_N^⋆ ∈ argmax ...`. Since that choice is not canonical,
the main public owner here is the canonical argmax set of all optimal constant-share portfolios.
The optimal average growth rate is then defined from the canonical optimal cumulative return. -/

variable {n N : ℕ}

/-- The cumulative return of a constant-share portfolio over the periods `0, ..., N`. -/
def constantShareObjective
    (c : Fin (N + 1) → Fin n → NNReal)
    (x : stdSimplex NNReal (Fin n)) : NNReal :=
  ∏ k : Fin (N + 1), c k ⬝ᵥ x.1

-- Proof sketch: unfold `constantShareObjective`.
/-- Expanding `constantShareObjective c x` gives the product
`∏_{k=0}^N ⟪c_k, x⟫` of the period-by-period returns. -/
@[simp] theorem constantShareObjective_def
    (c : Fin (N + 1) → Fin n → NNReal)
    (x : stdSimplex NNReal (Fin n)) :
    constantShareObjective c x = ∏ k : Fin (N + 1), c k ⬝ᵥ x.1 := sorry

/-- Definition 7.75: the set of optimal constant-share portfolios on `P` consists of the feasible
portfolios that maximize the cumulative return `x ↦ ∏_{k=0}^N ⟪c_k, x⟫`. Any member of this set is
an admissible textbook choice of `x_N^⋆`. -/
def optimalConstantShareArgmax
    (P : Set (stdSimplex NNReal (Fin n)))
    (c : Fin (N + 1) → Fin n → NNReal) :
    Set (stdSimplex NNReal (Fin n)) :=
  {x | x ∈ P ∧ IsMaxOn (constantShareObjective c) P x}

-- Proof sketch: unfold `optimalConstantShareArgmax`.
/-- Membership in `optimalConstantShareArgmax P c` means feasibility in `P` together with
maximality of the cumulative-return objective on `P`. -/
@[simp] theorem mem_optimalConstantShareArgmax_iff
    {P : Set (stdSimplex NNReal (Fin n))}
    {c : Fin (N + 1) → Fin n → NNReal}
    {x : stdSimplex NNReal (Fin n)} :
    x ∈ optimalConstantShareArgmax P c ↔
      x ∈ P ∧ IsMaxOn (constantShareObjective c) P x := sorry

/-- The optimal cumulative return is the supremum of the cumulative-return objective over the
feasible set `P`. -/
def optimalConstantShareCumulativeReturn
    (P : Set (stdSimplex NNReal (Fin n)))
    (c : Fin (N + 1) → Fin n → NNReal) : NNReal :=
  sSup ((constantShareObjective c) '' P)

-- Proof sketch: unfold `optimalConstantShareCumulativeReturn`.
/-- Expanding `optimalConstantShareCumulativeReturn P c` gives the supremum of the image of `P`
under the cumulative-return objective. -/
@[simp] theorem optimalConstantShareCumulativeReturn_def
    (P : Set (stdSimplex NNReal (Fin n)))
    (c : Fin (N + 1) → Fin n → NNReal) :
    optimalConstantShareCumulativeReturn P c = sSup ((constantShareObjective c) '' P) := sorry

-- Proof sketch: if `xStar` lies in `optimalConstantShareArgmax P c`, then
-- `mem_optimalConstantShareArgmax_iff` gives `xStar ∈ P` and `IsMaxOn ... P xStar`; combine the
-- resulting upper bound on the image of `P` with membership of
-- `constantShareObjective c xStar` in that image to identify the supremum with the attained
-- value.
/-- Any optimal constant-share portfolio attains the canonical optimal cumulative return. -/
theorem optimalConstantShareCumulativeReturn_eq_of_mem_optimalConstantShareArgmax
    {P : Set (stdSimplex NNReal (Fin n))}
    {c : Fin (N + 1) → Fin n → NNReal}
    {xStar : stdSimplex NNReal (Fin n)}
    (hxStar : xStar ∈ optimalConstantShareArgmax P c) :
    optimalConstantShareCumulativeReturn P c = constantShareObjective c xStar := sorry

/-- The optimal average growth rate is the `(N + 1)`-st geometric mean of the optimal cumulative
return. -/
def optimalAverageGrowthRate
    (P : Set (stdSimplex NNReal (Fin n)))
    (c : Fin (N + 1) → Fin n → NNReal) : NNReal :=
  optimalConstantShareCumulativeReturn P c ^ ((1 : ℝ) / (N + 1 : ℝ))

-- Proof sketch: unfold `optimalAverageGrowthRate`.
/-- Expanding `optimalAverageGrowthRate P c` gives the `(N + 1)`-st root of the optimal cumulative
return. -/
@[simp] theorem optimalAverageGrowthRate_def
    (P : Set (stdSimplex NNReal (Fin n)))
    (c : Fin (N + 1) → Fin n → NNReal) :
    optimalAverageGrowthRate P c =
      optimalConstantShareCumulativeReturn P c ^ ((1 : ℝ) / (N + 1 : ℝ)) := sorry

-- Proof sketch: rewrite `optimalAverageGrowthRate P c` using `optimalAverageGrowthRate_def`, then
-- use `optimalConstantShareCumulativeReturn_eq_of_mem_optimalConstantShareArgmax hxStar`.
/-- If `xStar` is an optimal constant-share portfolio, then the optimal average growth rate equals
the geometric mean of the cumulative return attained at `xStar`. -/
theorem optimalAverageGrowthRate_eq_of_mem_optimalConstantShareArgmax
    {P : Set (stdSimplex NNReal (Fin n))}
    {c : Fin (N + 1) → Fin n → NNReal}
    {xStar : stdSimplex NNReal (Fin n)}
    (hxStar : xStar ∈ optimalConstantShareArgmax P c) :
    optimalAverageGrowthRate P c =
      constantShareObjective c xStar ^ ((1 : ℝ) / (N + 1 : ℝ)) := sorry
