import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_33 (from Chap03) -/
section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable (f : E → ℝ) (xStar : E)

/- Definition 3.33 lies in the unconstrained convex minimization domain on `ℝⁿ`.

Sampled owner-style declarations:
* mathlib `ConvexOn`, the canonical owner predicate for convexity of a real-valued objective on a
  set, specialized here to `Set.univ`;
* `SetConstrainedMinimizationProblem.unconstrained` in `Chap01/Definition_1_3_3`, the project
  owner for whole-space minimization problems;
* mathlib `IsMinOn` and `isMinOn_univ_iff`, the canonical owner and textbook bridge for global
  minimizers on `Set.univ`;
* mathlib `IsMinOn.isGLB` and `IsGLB.csInf_eq`, the attained-infimum bridge for the minimum value
  over the whole range.

Best owner abstraction:
* source-facing: a whole-space convex objective on `ℝⁿ`;
* core/canonical: `ConvexOn ℝ Set.univ f` together with
  `SetConstrainedMinimizationProblem.unconstrained f`;
* bridge/view: the attained-infimum theorem `isMinOn_iff_eq_sInf_range`.

Primitive data:
* the ambient objective `f : E → ℝ` for the source-facing definition;
* for the bridge theorem, only a function into an order type.

Derived API:
* the whole-space convexity predicate `ConvexOn ℝ Set.univ f`;
* the ambient minimization-problem owner `SetConstrainedMinimizationProblem.unconstrained f`;
* the generic order-theoretic minimum-value identity on `Set.range f`.

This file therefore deletes the duplicate local wrapper
`UnconstrainedConvexMinimizationProblem`: its primitive objective data are already owned by the
Chapter 1 unconstrained minimization owner, while convexity itself is already owned canonically by
`ConvexOn`. The remaining theorem is a genuine bridge from whole-space minimality to the attained
infimum of the range, and it lives at the generic order owner layer because its proof does not use
Euclidean or real-specific structure. -/

/-- Definition 3.33: an unconstrained convex minimization problem on `ℝⁿ` is a real-valued
objective `f : ℝⁿ → ℝ` together with the canonical whole-space convexity predicate
`ConvexOn ℝ Set.univ f`. -/
abbrev IsUnconstrainedConvexMinimizationProblem (f : E → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f

/-- Helper for Definition 3.33: a point `x*` is an optimal solution exactly when it is a global
minimizer of the objective on the whole ambient space. -/
abbrev IsOptimalSolution (f : E → ℝ) (xStar : E) : Prop :=
  IsMinOn f Set.univ xStar

set_option linter.hashCommand false in
#check ConvexOn ℝ Set.univ f

/- The same objective is packaged by the Chapter 1 owner for whole-space minimization problems. -/
set_option linter.hashCommand false in
#check (SetConstrainedMinimizationProblem.unconstrained f : SetConstrainedMinimizationProblem E)

/- Global minimizers of the unconstrained objective are the canonical whole-space minimizers
`IsMinOn f Set.univ xStar`. -/
set_option linter.hashCommand false in
#check IsMinOn f Set.univ xStar

end

section

universe u v

variable {X : Type u} {Y : Type v} [ConditionallyCompleteLattice Y]

/-- If the objective values are bounded below, then a point `x*` is a global minimizer exactly
when its objective value equals the infimum of the values of the objective on the whole ambient
space. -/
theorem isMinOn_iff_eq_sInf_range {f : X → Y} {xStar : X}
    (hbelow : BddBelow (Set.range f)) :
    IsMinOn f Set.univ xStar ↔ f xStar = sInf (Set.range f) := by
  constructor
  · intro hxMin
    have hglb : IsGLB (Set.range f) (f xStar) := by
      have hglb_univ : IsGLB {y | ∃ z ∈ Set.univ, f z = y} (f xStar) :=
        hxMin.isGLB (Set.mem_univ xStar)
      have hset : ({y | ∃ z ∈ Set.univ, f z = y} : Set Y) = Set.range f := by
        ext y
        constructor
        · rintro ⟨z, -, rfl⟩
          exact ⟨z, rfl⟩
        · rintro ⟨z, rfl⟩
          exact ⟨z, Set.mem_univ z, rfl⟩
      exact hset ▸ hglb_univ
    exact (hglb.csInf_eq ⟨f xStar, ⟨xStar, rfl⟩⟩).symm
  · intro hx
    rw [isMinOn_univ_iff]
    intro x
    simpa [hx] using csInf_le hbelow (show f x ∈ Set.range f from ⟨x, rfl⟩)

end

/-! ### Lemma_3_33 (from Chap03) -/
/- Lemma 3.33 lies in the chapter's level-method scalar-history domain.

Sampled owner declarations:
* `LevelMethodHistory` in `Lemma_3_3_1`, the owner bundle for `(\hat f_k^*, f_k^*)`
* `LevelMethodHistory.gap` in `Lemma_3_3_1`, the canonical gap `δ_k`
* `LevelMethodHistory.levelValue` in `Lemma_3_3_1`, the canonical level value `ℓ_k(α)`
* `LevelMethodHistory.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity` in
  `Lemma_3_3_1`, the exact owner theorem for the interval-monotonicity form of this item

Best owner abstraction:
* source-facing/core owner for this numbered item:
  `LevelMethodHistory.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity`
* core/canonical ambient owner: `LevelMethodHistory`

Primitive data:
* no new primitive data beyond the imported owner theorem

Derived API:
* the direct recall surface for the interval-monotonicity theorem

Source/core/bridge triage:
* source-facing: Lemma 3.33 itself
* core/canonical: the owner theorem already living in `Lemma_3_3_1`
* bridge/view: this recall file

The previous file kept a second declaration with the exact same theorem name and proof body as the
owner-level interval theorem. That was a duplicate wheel. The owner now lives only in
`Lemma_3_3_1`, and this numbered file is reduced to a pure recall surface.
-/

/- Lemma 3.33 is the direct recall of the owner interval-monotonicity theorem. -/
#check LevelMethodHistory.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity

/-! ### Proposition_3_33 (from Chap03) -/
/- Proposition 3.33 lies in the chapter's extended-valued convex-analysis / subdifferential
domain.

Sampled owner-style declarations:
- `dom` in `Definition_3_3`, the chapter owner for effective domains of `WithTop ℝ`-valued
  functions;
- `subdifferential` and `mem_subdifferential_iff` in `Definition_3_1_5`, the source-facing owner
  API for extended-valued subgradients;
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential` in `Theorem_3_1_18`, the canonical
  sublevel-set inequality behind the minimizer pairing result;
- `subgradient_inner_sub_nonneg_of_isMinOn` in `Theorem_3_1_5_6`, the chapter owner theorem for
  pairing a subgradient at a feasible point with the displacement to a minimizer.

Best owner abstraction:
- core/canonical: `subgradient_inner_sub_nonneg_of_isMinOn`;
- bridge/view: the codomain coercion from a real-valued objective `f : E → ℝ` to the
  `WithTop ℝ`-valued owner surface `fun y ↦ (f y : WithTop ℝ)`.

Primitive data:
- an inner-product space `E`, a feasible set `Q`, a real-valued objective `f`, points `x`, `xStar`
  and a subgradient `g`;
- the feasibility hypothesis `x ∈ Q`;
- the minimizing hypothesis `IsMinOn f Q xStar`;
- the owner-membership hypothesis `g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x)`.

Derived API:
- the nonnegativity inequality `0 ≤ inner ℝ g (x - xStar)`.

Source/core/bridge triage:
- source-facing: the textbook real-valued spelling of the minimizer-pairing inequality;
- core/canonical: `subgradient_inner_sub_nonneg_of_isMinOn`;
- bridge/view: the coercion from real-valued objectives to the chapter's extended-valued
  subdifferential owner.

This proposition contributes no new public owner beyond the existing theorem
`subgradient_inner_sub_nonneg_of_isMinOn`: its former local theorem was only the codomain-coercion
specialization of that owner theorem, and its second theorem was a verbatim alias of the first.
The file therefore keeps the canonical owner theorem directly instead of preserving a parallel
specialized wrapper API. -/

recall subgradient_inner_sub_nonneg_of_isMinOn

/-! ### Theorem_3_33 (from Chap03) -/
/- Theorem 3.33: this item contains only the cross-reference “Theorem 3.1.26.”, so its
source-faithful formalization is a direct recall of the existing Chapter 3 Karush--Kuhn--Tucker
optimality theorem rather than a second local theorem shell.

The recalled owner theorem is `isMinOn_iff_exists_karush_kuhn_tucker_multiplier`.
-/
recall isMinOn_iff_exists_karush_kuhn_tucker_multiplier
