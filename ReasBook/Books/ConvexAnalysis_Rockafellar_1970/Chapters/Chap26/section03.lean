import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_26_3_1 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
local notation "IsClosedProperConvexℝ" => Function.IsClosedProperConvex (𝕜 := ℝ)
local notation "IsEssentiallyStrictlyConvexℝ" => Function.IsEssentiallyStrictlyConvex (𝕜 := ℝ)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 26.3.1 says that, for a closed proper convex function, the
  subdifferential mapping is one-to-one exactly when the finite real branch is strictly convex on
  `interior (dom(f))` and the function is essentially smooth.
- `core/canonical`: the owner declarations already present in the project are the intrinsic graph
  relation `_root_.subdifferentialGraph f`, the Chapter 26 one-to-one owner
  `(_root_.subdifferentialGraph f).BiUnique`, the Chapter 26 owner
  `Function.IsEssentiallyStrictlyConvex`, the mathlib owner `StrictConvexOn`, and the chapter owner
  `Function.IsEssentiallySmooth`.
- `bridge/view`: the source-facing strict-convexity clause on `interior (dom(f))` is a companion
  view of the more owner-level Chapter 26 predicate `Function.IsEssentiallyStrictlyConvex`.

Domain-style sampling used here:
- `_root_.subdifferentialGraph` from `Definition_5_24_3`;
- `SetRel.BiUnique` from `Definition_26_0_3`;
- `Function.IsEssentiallyStrictlyConvex` together with
  `_root_.leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex`
  from `Theorem_26_4`;
- `_root_.rightUnique_subdifferentialGraph_iff_isEssentiallySmooth` from `Theorem_26_1`;
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `StrictConvexOn` and `Function.realBranch`.

Primitive data vs derived API:
- primitive input: a closed proper convex function `f`;
- primitive owner surface: bi-uniqueness of `_root_.subdifferentialGraph f`,
  `f.IsEssentiallyStrictlyConvex`, and `f.IsEssentiallySmooth`;
- derived/source-facing API here: the textbook strict-convexity clause on `interior (dom(f))`.

Layer target: `source-facing`.

Ambient refinement:
- the public statement uses only the intrinsic dual-valued graph owner, not the vector-valued
  Fréchet-Riesz graph owner;
- the canonical Chapter 23/26 bridge theorems reused to compare `dom∂(f)`, `riDom(f)`, and
  `interior (dom(f))` currently live on the finite-dimensional real inner-product side, so the
  ambient statement is refined to that existing owner ecosystem rather than restating a parallel
  weaker local bridge.
-/

/-- Owner-level Chapter 26 combination behind Corollary 26.3.1: for a closed proper convex
function, one-to-one-ness of the intrinsic subdifferential graph is exactly the conjunction of the
two canonical Chapter 26 owner predicates, essential strict convexity and essential smoothness. -/
theorem biUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex_and_isEssentiallySmooth
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvexℝ f) :
    (gph∂(f)).BiUnique ↔
      IsEssentiallyStrictlyConvexℝ f ∧ f.IsEssentiallySmooth := by
  rw [SetRel.biUnique_iff_leftUnique_and_rightUnique]
  constructor
  · rintro ⟨hLeft, hRight⟩
    exact ⟨(_root_.leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf).1 hLeft,
      (_root_.rightUnique_subdifferentialGraph_iff_isEssentiallySmooth hf).1 hRight⟩
  · rintro ⟨hStrict, hEss⟩
    exact ⟨(_root_.leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf).2 hStrict,
      (_root_.rightUnique_subdifferentialGraph_iff_isEssentiallySmooth hf).2 hEss⟩

omit [FiniteDimensional ℝ E] in
private theorem strictConvexOn_coe_real
    {C : Set E} {g : E → ℝ} (h : StrictConvexOn ℝ C g) :
    StrictConvexOn ℝ C (fun x ↦ ((g x : ℝ) : WithBotTop ℝ)) := by
  rcases h with ⟨hC_convex, hineq⟩
  refine ⟨hC_convex, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hltR : g (a • x + b • y) < a • g x + b • g y :=
    hineq hx hy hxy ha hb hab
  have hltE :
      (((g (a • x + b • y) : ℝ) : WithBotTop ℝ)) <
        (((a * g x + b * g y : ℝ) : WithBotTop ℝ)) :=
    WithBotTop.coe_lt_coe.mpr hltR
  change (((g (a • x + b • y) : ℝ) : WithBotTop ℝ)) <
      ((a : ℝ) : WithBotTop ℝ) * (((g x : ℝ) : WithBotTop ℝ)) +
        ((b : ℝ) : WithBotTop ℝ) * (((g y : ℝ) : WithBotTop ℝ))
  simpa [smul_eq_mul] using hltE

/-- For a closed proper convex function that is essentially smooth, the Chapter 26 owner
`Function.IsEssentiallyStrictlyConvex` is exactly the source-facing strict-convexity condition on
`interior (dom(f))`. -/
theorem isEssentiallyStrictlyConvex_iff_strictConvexOn_interior_dom_of_isEssentiallySmooth
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvexℝ f) (hess : f.IsEssentiallySmooth) :
    IsEssentiallyStrictlyConvexℝ f ↔
      StrictConvexOn ℝ (interior (dom(f))) f.realBranch := by
  have hri_eq :
      riDom(f) = interior (dom(f)) :=
    hess.riDom_eq_interior_dom
  constructor
  · intro hstrictly
    simpa [hri_eq] using hstrictly.strictConvexOn_realBranch_riDom
  · intro hstrict
    refine (Function.isEssentiallyStrictlyConvex_iff (𝕜 := ℝ) (f := f)).2 ?_
    refine ⟨hf.convex, hf.proper, ?_⟩
    intro C hC_convex hC_dom
    have hsub : C ⊆ interior (dom(f)) := by
      intro x hx
      have hxVec : x ∈ (Function.subdifferentialGraph f).dom := by
        rw [Function.subdifferentialGraph_dom_eq_intrinsic]
        exact hC_dom hx
      by_contra hxnot
      have hEmpty : Function.subdifferentialAt f x = ∅ :=
        Function.subdifferentialAt_eq_empty_of_not_mem_interior_dom
          hf.lowerSemicontinuous hess hxnot
      have hxNotVec : x ∉ (Function.subdifferentialGraph f).dom := by
        rw [SetRel.mem_dom]
        rintro ⟨xStar, hxStar⟩
        rw [Function.mem_subdifferentialGraph, hEmpty] at hxStar
        simp at hxStar
      exact hxNotVec hxVec
    have hEq :
        Set.EqOn f (fun x ↦ ((f.realBranch x : ℝ) : WithBotTop ℝ)) C := by
      intro x hx
      have hxdom : x ∈ dom(f) := interior_subset (hsub hx)
      have hneTop : f x ≠ ⊤ := ne_of_lt (mem_effectiveDomain.mp hxdom)
      have hneBot : f x ≠ ⊥ := hf.proper.ne_bot x
      simpa [Function.realBranch] using (EReal.coe_toReal hneTop hneBot).symm
    have hstrict_coe :
        StrictConvexOn ℝ C (fun x ↦ ((f.realBranch x : ℝ) : WithBotTop ℝ)) :=
      strictConvexOn_coe_real (hstrict.subset hsub hC_convex)
    exact hstrict_coe.congr hEq.symm

-- Proof sketch: first rewrite one-to-one-ness through the owner-level Chapter 26 conjunction
-- `f.IsEssentiallyStrictlyConvex ∧ f.IsEssentiallySmooth` above. The remaining step is exactly the
-- source-facing bridge between essential strict convexity and strict convexity of the finite real
-- branch on `interior (dom(f))` under essential smoothness.
/-- Corollary 26.3.1: for a closed proper convex function, the subdifferential mapping is
one-to-one exactly when the finite real branch is strictly convex on `interior (dom(f))` and the
function is essentially smooth. The source phrase “one-to-one” is expressed through the canonical
relation owner `(gph∂(f)).BiUnique`. -/
theorem biUnique_subdifferentialGraph_iff_strictConvexOn_interior_dom_and_isEssentiallySmooth
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvexℝ f) :
    (gph∂(f)).BiUnique ↔
      StrictConvexOn ℝ (interior (dom(f))) f.realBranch ∧ f.IsEssentiallySmooth := by
  rw [biUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex_and_isEssentiallySmooth hf]
  constructor
  · rintro ⟨hstrictly, hess⟩
    exact
      ⟨(isEssentiallyStrictlyConvex_iff_strictConvexOn_interior_dom_of_isEssentiallySmooth
          hf hess).1 hstrictly, hess⟩
  · rintro ⟨hstrict, hess⟩
    exact
      ⟨(isEssentiallyStrictlyConvex_iff_strictConvexOn_interior_dom_of_isEssentiallySmooth
          hf hess).2 hstrict, hess⟩

end

/-! ### Corollary_26_3_2 (from Chap05) -/
noncomputable section

open scoped Rockafellar

section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 26.3.2 states that if `f₁` is essentially smooth, `f₂` is proper
  convex on the ambient finite-dimensional real normed space, and `ri(dom f₁⋆)` meets
  `ri(dom f₂⋆)` on the canonical dual owner, then the infimal convolution
  `f₁ □ f₂` is essentially smooth.
- `core/canonical`: the project owners already present are `Function.IsClosedProperConvex`,
  `Function.IsEssentiallySmooth`, Fenchel conjugation `f⋆`, the relative-domain notation
  `riDom(f)`, and the binary infimal convolution `f □ g`.
- `bridge/view`: this corollary is the one-step Chapter 26 consequence obtained by combining the
  essential-smooth/essential-strict-convex duality of Theorem 26.3 with the Chapter 16
  conjugate-of-sum owner and the Chapter 23 subdifferential-of-sum owner.

Domain-style sampling used here:
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `Function.IsClosedProperConvex
    .isEssentiallyStrictlyConvex_iff_convexConjugate_isEssentiallySmooth`
  from `Theorem_26_3`;
- the canonical dual owner `StrongDual ℝ E` for conjugates on `NormedSpace ℝ E`;
- `riDom(·)` from `Definition_4_4`;
- the binary infimal convolution owner `f □ g` from `Text_5_4_0`.

Primitive data vs derived API:
- primitive inputs: the two functions `f₁`, `f₂`, the extra closedness hypothesis
  `LowerSemicontinuous f₁` needed to enter the Chapter 26 owner theorem on `f₁`, the essential
  smoothness hypothesis on `f₁` (which already carries convexity and properness), the
  proper-convex hypotheses on `f₂`, and the nonempty intersection
  `riDom((f₁⋆ : StrongDual ℝ E → WithBotTop ℝ)) ∩
    riDom((f₂⋆ : StrongDual ℝ E → WithBotTop ℝ))`;
- derived API: the essential smoothness of the infimal convolution `f₁ □ f₂`.

Layer target: `source-facing`, stated directly with the chapter owners rather than through a
surrogate wrapper around the dual sum `(f₁⋆ + f₂⋆)`.
-/

namespace Function.IsClosedProperConvex

variable {f₁ f₂ : E → WithBotTop ℝ}

local notation "f₁⋆ₛ" => ((f₁⋆ : StrongDual ℝ E → WithBotTop ℝ))
local notation "f₂⋆ₛ" => ((f₂⋆ : StrongDual ℝ E → WithBotTop ℝ))

/-- Corollary 26.3.2: if `f₁` is essentially smooth, `f₂` is proper convex on the ambient
finite-dimensional real normed space, and `ri(dom f₁⋆) ∩ ri(dom f₂⋆)` is nonempty on the
canonical dual owner `StrongDual ℝ E`, then the infimal convolution `f₁ □ f₂` is essentially
smooth. The Chapter 26 owner route also needs the explicit closedness hypothesis
`LowerSemicontinuous f₁` on the left input. -/
theorem
    infimal_convolution_isEssentiallySmooth_of_left_isEssentiallySmooth_of_common_riDom_conjugates
    (hclosed₁ : LowerSemicontinuous f₁) (hess₁ : f₁.IsEssentiallySmooth)
    (hf₂_convex : f₂.IsConvex ℝ) (hf₂_proper : f₂.IsProper)
    (hri : (riDom(f₁⋆ₛ) ∩ riDom(f₂⋆ₛ)).Nonempty) :
    (f₁ □ f₂).IsEssentiallySmooth := sorry

end Function.IsClosedProperConvex

end

/-! ### Corollary_26_3_3 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 26.3.3 says that if `f` is closed proper convex and essentially
  smooth, and if a surjective linear map `A` satisfies the source qualification
  `A* y* ∈ ri(dom f*)` for some `y*`, then the linear image `Af` is essentially smooth.
- `core/canonical`: the project owners already present are `Function.IsClosedProperConvex`,
  `Function.IsEssentiallySmooth`, Fenchel conjugation `f⋆`, the relative-domain notation
  `riDom(·)`, the linear-image owner `Function.linearImage` with notation `A ◁ f`, and the
  Euclidean adjoint `A.adjoint`.
- `bridge/view`: the source notation `Af` is rendered directly by `A ◁ f`, and the qualification
  `A* y* ∈ ri(dom f*)` is rendered as `A.adjoint yStar ∈ riDom(f⋆)`.

Domain-style sampling used here:
- `Function.linearImage` and the notation `A ◁ f` from `Theorem_16_3_1`;
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `Function.IsClosedProperConvex.
  isEssentiallyStrictlyConvex_iff_convexConjugate_isEssentiallySmooth`
  from `Theorem_26_3`;
- `Function.subdifferentialAt_comp_linearMap_eq_adjoint_image_of_riDom_or_polyhedral`
  from `Theorem_23_9`;
- Fenchel conjugation `f⋆` and adjoints `A.adjoint`.

Primitive data vs derived API:
- primitive inputs: the function `f`, the surjective linear map `A`, the canonical closed-proper-
  convex owner rebuilt from the genuinely extra closedness hypothesis `LowerSemicontinuous f`
  together with the convexity and properness fields already carried by `f.IsEssentiallySmooth`,
  and the source qualification `∃ yStar, A.adjoint yStar ∈ riDom(f⋆)`;
- derived API: essential smoothness of the source-facing linear image `A ◁ f`.

Layer target: `source-facing`, stated directly on the canonical owner `A ◁ f` rather than on a
surrogate package built from `(f⋆ ∘ A.adjoint)⋆`, and with the closed/proper/convex input carried
by the Chapter 26 owner pattern `LowerSemicontinuous f` plus `f.IsEssentiallySmooth`, rather
than by a redundant `f.IsClosedProperConvex` binder in the theorem surface.
-/

namespace Function.IsClosedProperConvex

-- Proof sketch: combine `hclosed` with the convexity and properness fields already carried by
-- `hess` to build the canonical owner `hf : f.IsClosedProperConvex`. Apply Theorem 26.3 to turn
-- essential smoothness of `f` into
-- essential strict convexity of `f⋆`. Theorem 16.3.1 identifies the conjugate of the linear image
-- `A ◁ f` with the precomposition `f⋆ ∘ A.adjoint`. Using Theorem 23.9 and surjectivity of `A`
-- (hence injectivity of `A.adjoint`), show that `f⋆ ∘ A.adjoint` is essentially strictly convex
-- under the source qualification `∃ yStar, A.adjoint yStar ∈ riDom(f⋆)`. Apply Theorem 26.3 again
-- to conclude that `A ◁ f` is essentially smooth.
/-- Corollary 26.3.3: let `f` be a closed proper convex function on the ambient finite-dimensional
real inner-product space `E`, and let `A : E →ₗ[ℝ] F` be surjective. If `f` is essentially smooth
and there exists `yStar : F` with `A.adjoint yStar ∈ ri(dom f⋆)`, rendered by
`A.adjoint yStar ∈ riDom(f⋆)`, then the linear image `A ◁ f` is essentially smooth. -/
theorem linearImage_isEssentiallySmooth_of_isEssentiallySmooth_of_exists_adjoint_mem_riDom_conjugate
    {f : E → WithBotTop ℝ} (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    (A : E →ₗ[ℝ] F) (hA : Function.Surjective A)
    (hri : ∃ yStar : F, A.adjoint yStar ∈ riDom(f⋆)) :
    (A ◁ f).IsEssentiallySmooth := sorry

end Function.IsClosedProperConvex

end

/-! ### Text_26_3_3_1 (from Chap05) -/
noncomputable section

universe u

open Metric
open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.3.3.1 concerns the powered distance-to-set function `x ↦ d(x, C)^p`.
  For calculus this is the finite real branch `x ↦ (d(x, C)).toReal ^ p`.
- `core/canonical`: the real-valued owner is `Metric.infDist`, while the chapter notation
  `d(x, C)` is the `EReal`-valued bridge coming from `Metric.infEDist`.
- `bridge/view`: the source-facing chapter notation is related to the canonical owner by
  `distanceToSet_toReal_eq_infDist`.

Domain-style sampling used here:
- `Metric.infDist` and `Metric.infDist_closure` from mathlib;
- `distanceToSet_toReal_eq_infDist` and `distanceToSet_eq_infDist` from
  `Chap01.Defintion_4_8_3`;
- `distanceToSet_isConvex` from `Chap01.Text_5_4_1_5`;
- `ConvexOn.rpow_of_one_lt` from `Chap01.Text_5_1_2`;
- `Function.continuous_gradient_realBranch_on_open_convex` from `Chap05.Corollary_25_5_1` for
  the finite-dimensional `C¹` upgrade.

Primitive data vs derived API:
- primitive data: the set `C`, the exponent `p`, and the owner `fun x ↦ infDist x C ^ p`;
- derived API: the metric bridge to `d(x, C)`, the global convexity/differentiability theorem,
  the finite-dimensional `ContDiff ℝ 1` upgrade, and the source-facing restatements.

Layer target:
- `infDist_rpow_convexOn_univ_and_differentiable` and its `d(x, C)` restatement:
  Hilbert-space `core/canonical` plus `bridge/view`;
- `infDist_rpow_contDiff` and its `d(x, C)` restatement: stronger finite-dimensional corollaries.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: the nonempty closed convex case is the source argument from Chapter 26. For an
-- arbitrary convex set, pass to `closure C`: convexity is preserved by closure and
-- `infDist x (closure C) = infDist x C`, so the canonical real-valued owner is unchanged while
-- the closedness hypothesis disappears. The empty-set case is then the constant-zero function at
-- the core `infDist` layer. The source-facing chapter notation is recovered through the global
-- finite-branch bridge `(d(x, C)).toReal = infDist x C`, so no separate nonemptiness hypothesis
-- remains on the public real-valued theorem surface.
/-- Canonical real-valued Hilbert-space owner form of Text 26.3.3.1: for a convex set `C` and
`1 < p`, the function `x ↦ infDist x C ^ p` is convex on the whole space and differentiable
everywhere. -/
theorem infDist_rpow_convexOn_univ_and_differentiable
    {C : Set E} (hC_convex : Convex ℝ C) {p : ℝ} (hp : 1 < p) :
    ConvexOn ℝ Set.univ (fun x ↦ infDist x C ^ p) ∧
      Differentiable ℝ (fun x ↦ infDist x C ^ p) := sorry

/-- Source-facing real-branch restatement of Text 26.3.3.1: for a convex set `C` and `1 < p`, the
function `x ↦ (d(x, C)).toReal ^ p` is convex on the whole space and differentiable
everywhere. -/
theorem distanceToSet_toReal_rpow_convexOn_univ_and_differentiable
    {C : Set E} (hC_convex : Convex ℝ C) {p : ℝ} (hp : 1 < p) :
    ConvexOn ℝ Set.univ (fun x ↦ (d(x, C)).toReal ^ p) ∧
      Differentiable ℝ (fun x ↦ (d(x, C)).toReal ^ p) := by
  have hdist :
      (fun x ↦ (d(x, C)).toReal ^ p) = fun x ↦ infDist x C ^ p := by
    funext x
    rw [distanceToSet_toReal_eq_infDist]
  simpa [hdist] using infDist_rpow_convexOn_univ_and_differentiable hC_convex hp

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: the Hilbert-space theorem above gives convexity together with everywhere
-- differentiability on the open set `univ`. Corollary 25.5.1 upgrades a convex real-valued
-- function differentiable on an open set to `C¹` there, so applying it to
-- `fun x ↦ infDist x C ^ p` on `univ` yields the finite-dimensional claim.
/-- In the finite-dimensional inner-product setting, the powered real-valued distance-to-set owner
is continuously differentiable when `1 < p`. -/
theorem infDist_rpow_contDiff
    {C : Set E} (hC_convex : Convex ℝ C) {p : ℝ} (hp : 1 < p) :
    ContDiff ℝ 1 (fun x ↦ infDist x C ^ p) := sorry

/-- Source-facing `C¹` restatement on the finite real branch of the chapter distance notation for a
convex set. -/
theorem distanceToSet_toReal_rpow_contDiff
    {C : Set E} (hC_convex : Convex ℝ C) {p : ℝ} (hp : 1 < p) :
    ContDiff ℝ 1 (fun x ↦ (d(x, C)).toReal ^ p) := by
  have hdist :
      (fun x ↦ (d(x, C)).toReal ^ p) = fun x ↦ infDist x C ^ p := by
    funext x
    rw [distanceToSet_toReal_eq_infDist]
  simpa [hdist] using infDist_rpow_contDiff hC_convex hp

end

/-! ### Text_26_3_3_2 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {E : Type u} {F : Type v}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid F] [Module ℝ F]

/- The owner-level convexity clause only uses the chapter convexity owner `Function.IsConvex`
and the source-facing linear-image owner `Function.linearImage`, so it lives on the minimal
`ℝ`-module layer. -/
/-- The linear image of a globally convex real-valued function is globally convex. -/
theorem linearImage_convexOn_univ (f : E → ℝ) (A : E →ₗ[ℝ] F)
    (hf_convex : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (A ◁ f) := by
  sorry

/-- The linear image of the lifted source function is convex on the canonical extended-real owner
layer. -/
theorem linearImage_toEReal_isConvex (f : E → ℝ) (A : E →ₗ[ℝ] F)
    (hf_convex : ConvexOn ℝ Set.univ f) :
    (A ◁ f.toEReal).IsConvex ℝ := by
  simpa [Function.toEReal] using
    Function.isConvex_linearImage A f.toEReal
      (Function.isConvex_coe_of_convexOn_univ hf_convex)

end

section

variable {𝕜 α : Type*} {E : Type u} {F : Type v}
variable [Semiring 𝕜]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

/-- Positivity of the recession function on every nonzero kernel vector gives the canonical
Chapter 2 owner hypothesis `A.noAsymmetricRecessionKernel h`. -/
theorem noAsymmetricRecessionKernel_of_positive_recession_on_ker
    (h : E → WithBotTop α) (A : E →ₗ[𝕜] F)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < ((h)₀⁺) x) :
    A.noAsymmetricRecessionKernel h := by
  intro x hx_nonpos hx_neg
  by_contra hxA
  by_cases hx_zero : x = 0
  · have hx_nonpos_zero : ((h)₀⁺) 0 ≤ 0 := by simpa [hx_zero] using hx_nonpos
    have hx_pos_zero : 0 < ((h)₀⁺) 0 := by simpa [hx_zero] using hx_neg
    exact (not_lt_of_ge hx_nonpos_zero hx_pos_zero).elim
  · have hx_pos : 0 < ((h)₀⁺) x :=
      hpositive_recession_on_ker x (LinearMap.mem_ker.mp hxA) hx_zero
    exact (not_lt_of_ge hx_nonpos hx_pos).elim

end

section

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommMonoid F] [Module ℝ F]

/-- The textbook positivity condition on nonzero kernel vectors implies the canonical Chapter 2
owner hypothesis `A.noAsymmetricRecessionKernel f.toEReal`. -/
theorem noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
    (f : E → ℝ) (A : E →ₗ[ℝ] F)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x) :
    A.noAsymmetricRecessionKernel f.toEReal :=
  noAsymmetricRecessionKernel_of_positive_recession_on_ker
    f.toEReal A hpositive_recession_on_ker

end

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-!
Source/core/bridge triage for this item.

- `source-facing`: this text says that a differentiable convex real-valued function remains
  differentiable convex after taking its linear image under a surjective map, provided the
  recession function is strictly positive on every nonzero kernel vector.
- `core/canonical`: the relevant owners already present in the project are `Function.linearImage`
  with notation `A ◁ f`, the finite-branch owner `Function.realBranch`, the relative-domain
  notation `riDom(·)`, Fenchel conjugation `f⋆`, the recession-function notation `0⁺`, and the
  essential-smoothness owner `Function.IsEssentiallySmooth`.
- `bridge/view`: the source real-valued function is expressed through the canonical lifted owner
  `f.toEReal`, while the source-facing image function remains the real-valued owner `A ◁ f`.
  The lifted image `A ◁ f.toEReal` is used only to invoke the Chapter 26 essential-smoothness
  owner and then bridge back to `A ◁ f` by identifying `A ◁ f.toEReal = (A ◁ f).toEReal`.

Domain-style sampling used here:
- `exists_image_mem_intrinsicInterior_effectiveDomain_iff_no_adjoint_asymmetric_recession`;
- `isConvex_toWithBotTopOn_iff`;
- `Function.isConvex_linearImage`;
- `linearImage_isEssentiallySmooth_of_isEssentiallySmooth_of_exists_adjoint_mem_riDom_conjugate`;
- `Function.IsEssentiallySmooth.differentiableOn_realBranch`.

Primitive data vs derived API:
- primitive source data: the convex real-valued function `f`, the surjective linear map `A`, and
  the Chapter 2 owner hypothesis `A.noAsymmetricRecessionKernel f.toEReal`;
- source-facing bridge data: the stronger textbook positivity condition on nonzero kernel vectors,
  used only to recover the owner hypothesis when one wants the theorem in its original prose form;
- derived API: the adjoint relative-interior qualification, essential smoothness of
  `A ◁ f.toEReal`, the canonical lift bridge `A ◁ f.toEReal = (A ◁ f).toEReal`, and the resulting
  differentiability of the source-facing real-valued image `A ◁ f`.
-/

-- Proof sketch: apply Corollary 16.2.1 to the adjoint map `A.adjoint` and to the conjugate
-- `(f.toEReal)⋆`. The source recession hypothesis on `ker A` is exactly the negation of the
-- asymmetric-recession obstruction after rewriting `(A.adjoint).adjoint = A` and viewing
-- `((f.toEReal)⋆)⋆0⁺` as the source recession function `f0⁺`.
variable (f : E → ℝ) (A : E →ₗ[ℝ] F)

/-- The canonical Chapter 2 recession-kernel owner forces the adjoint range to meet the relative
interior of the conjugate domain, expressed as `A.adjoint yStar ∈ riDom((f.toEReal)⋆)`. -/
theorem exists_adjoint_mem_riDom_convexConjugate_toEReal_of_no_asymmetric_recession_kernel
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hkernel : A.noAsymmetricRecessionKernel f.toEReal) :
    ∃ yStar : F, A.adjoint yStar ∈ riDom((f.toEReal)⋆) := sorry

/-- The positivity of `f0⁺` on the nonzero kernel of `A` forces the adjoint range to meet the
relative interior of the conjugate domain, expressed as `A.adjoint yStar ∈ riDom((f.toEReal)⋆)`. -/
theorem exists_adjoint_mem_riDom_convexConjugate_toEReal_of_positive_recession_on_ker
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x) :
    ∃ yStar : F, A.adjoint yStar ∈ riDom((f.toEReal)⋆) :=
  exists_adjoint_mem_riDom_convexConjugate_toEReal_of_no_asymmetric_recession_kernel
    f A hf_convex (noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
      f A hpositive_recession_on_ker)

-- Proof sketch: a differentiable convex real-valued function on all of `E` gives an essentially
-- smooth lifted function `f.toEReal`, because `dom(f.toEReal) = Set.univ` and the boundary
-- blow-up clause is vacuous. Then use the qualification theorem above together with
-- Corollary 26.3.3 for the surjective map `A`.
/-- Under the canonical Chapter 2 recession-kernel owner, the lifted image `A ◁ f.toEReal` is
essentially smooth on the canonical extended-real owner layer. -/
theorem linearImage_toEReal_isEssentiallySmooth_of_no_asymmetric_recession_kernel
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hkernel : A.noAsymmetricRecessionKernel f.toEReal)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    (A ◁ f.toEReal).IsEssentiallySmooth := sorry

/-- Under the textbook positivity condition on nonzero kernel vectors, the lifted image
`A ◁ f.toEReal` is essentially smooth. -/
theorem linearImage_toEReal_isEssentiallySmooth_of_positive_recession_on_ker
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    (A ◁ f.toEReal).IsEssentiallySmooth :=
  linearImage_toEReal_isEssentiallySmooth_of_no_asymmetric_recession_kernel
    f A hf_convex
    (noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
      f A hpositive_recession_on_ker)
    hf_diff hA

-- Proof sketch: surjectivity makes every fiber of `A` nonempty, so the lifted image
-- `A ◁ f.toEReal` is finite above at every point. The Chapter 9 attainment theorem then produces
-- a fiber minimizer, which is also a minimizer for the real-valued image owner `A ◁ f`. This
-- identifies the lifted owner with the canonical codomain lift of `A ◁ f`.
/-- Under the canonical Chapter 2 recession-kernel owner, the lifted image is exactly the
canonical codomain lift of the real-valued image owner. -/
theorem linearImage_toEReal_eq_toEReal_linearImage_of_no_asymmetric_recession_kernel
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hkernel : A.noAsymmetricRecessionKernel f.toEReal)
    (hA : Function.Surjective A) :
    A ◁ f.toEReal = (A ◁ f).toEReal := sorry

/-- Under the textbook positivity condition on nonzero kernel vectors, the lifted image is exactly
the canonical codomain lift of the real-valued image owner. -/
theorem linearImage_toEReal_eq_toEReal_linearImage_of_positive_recession_on_ker
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x)
    (hA : Function.Surjective A) :
    A ◁ f.toEReal = (A ◁ f).toEReal :=
  linearImage_toEReal_eq_toEReal_linearImage_of_no_asymmetric_recession_kernel
    f A hf_convex
    (noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
      f A hpositive_recession_on_ker)
    hA

-- Proof sketch: apply essential smoothness of `A ◁ f.toEReal`, rewrite that lifted owner as
-- `(A ◁ f).toEReal`, identify the real branch with `A ◁ f`, and use `dom((A ◁ f).toEReal) =
-- Set.univ` to upgrade `DifferentiableOn` on the interior domain to global differentiability.
/-- Under the canonical Chapter 2 recession-kernel owner, the real-valued image `A ◁ f` is
differentiable on all of `F`. -/
theorem linearImage_differentiable_of_no_asymmetric_recession_kernel
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hkernel : A.noAsymmetricRecessionKernel f.toEReal)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    Differentiable ℝ (A ◁ f) := by
  have hess : (A ◁ f.toEReal).IsEssentiallySmooth :=
    linearImage_toEReal_isEssentiallySmooth_of_no_asymmetric_recession_kernel
      f A hf_convex hkernel hf_diff hA
  have hEq :
      A ◁ f.toEReal = (A ◁ f).toEReal :=
    linearImage_toEReal_eq_toEReal_linearImage_of_no_asymmetric_recession_kernel
      f A hf_convex hkernel hA
  have hbranch : (A ◁ f.toEReal).realBranch = A ◁ f := by
    funext y
    rw [hEq]
    simp
  have hdom0 : dom(A ◁ f.toEReal) = Set.univ := by
    ext y
    rw [mem_effectiveDomain]
    constructor
    · intro _
      simp
    · intro _
      have hEqAt : (A ◁ f.toEReal) y = ((A ◁ f) y : EReal) := congrFun hEq y
      exact hEqAt ▸ WithBotTop.coe_lt_top ((A ◁ f) y)
  have hdom : interior (dom(A ◁ f.toEReal)) = Set.univ := by
    rw [hdom0]
    simp
  have hdiffOn : DifferentiableOn ℝ (A ◁ f) (interior (dom(A ◁ f.toEReal))) := by
    simpa [hbranch] using hess.differentiableOn_realBranch
  have hdiffOn_univ : DifferentiableOn ℝ (A ◁ f) Set.univ := by
    simpa [hdom] using hdiffOn
  exact differentiableOn_univ.1 hdiffOn_univ

/-- Under the textbook positivity condition on nonzero kernel vectors, the real-valued image
`A ◁ f` is differentiable on all of `F`. -/
theorem linearImage_differentiable_of_positive_recession_on_ker
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    Differentiable ℝ (A ◁ f) :=
  linearImage_differentiable_of_no_asymmetric_recession_kernel
    f A hf_convex
    (noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
      f A hpositive_recession_on_ker)
    hf_diff hA

/-- Canonical owner-layer form of Text 26.3.3.2: under the Chapter 2 recession-kernel owner
`A.noAsymmetricRecessionKernel f.toEReal`, the real-valued image `A ◁ f` is convex on `univ`
and differentiable on all of `F`. -/
theorem linearImage_convexOn_univ_and_differentiable_of_no_asymmetric_recession_kernel
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hkernel : A.noAsymmetricRecessionKernel f.toEReal)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    ConvexOn ℝ Set.univ (A ◁ f) ∧ Differentiable ℝ (A ◁ f) := by
  refine ⟨linearImage_convexOn_univ f A hf_convex, ?_⟩
  exact linearImage_differentiable_of_no_asymmetric_recession_kernel
    f A hf_convex hkernel hf_diff hA

/-- Text 26.3.3.2: if `f : E → ℝ` is differentiable and convex on the whole space, and if
`A : E →ₗ[ℝ] F` is surjective with `A x = 0`, `x ≠ 0` implying `0 < (f.toEReal)₀⁺ x`, then the
real-valued linear image `A ◁ f` is convex and differentiable on all of `F`. -/
theorem linearImage_convexOn_univ_and_differentiable_of_positive_recession_on_ker
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hpositive_recession_on_ker :
      ∀ x : E, A x = 0 → x ≠ 0 → 0 < (f.toEReal)₀⁺ x)
    (hf_diff : Differentiable ℝ f)
    (hA : Function.Surjective A) :
    ConvexOn ℝ Set.univ (A ◁ f) ∧ Differentiable ℝ (A ◁ f) :=
  linearImage_convexOn_univ_and_differentiable_of_no_asymmetric_recession_kernel
    f A hf_convex
    (noAsymmetricRecessionKernel_toEReal_of_positive_recession_on_ker
      f A hpositive_recession_on_ker)
    hf_diff hA

end

/-! ### Theorem_26_3 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 26.3 says that for a closed proper convex function, essential strict
  convexity is equivalent to essential smoothness of the Fenchel conjugate.
- `core/canonical`: the owner abstractions already present in the chapter are
  `Function.IsEssentiallyStrictlyConvex`, `Function.IsEssentiallySmooth`, and Fenchel conjugation
  `f⋆`.
- `bridge/view`: the proof route stays on the intrinsic subdifferential-graph owner
  `_root_.subdifferentialGraph`, together with
  `_root_.subdifferentialGraph_convexConjugate_eq_inv` from `Text_26_0_1` and the Chapter 26
  graph-uniqueness owner theorems
  `_root_.rightUnique_subdifferentialGraph_primalCodomain_iff_isEssentiallySmooth` from
  `Theorem_26_1` and
  `_root_.leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex`
  from `Theorem_26_4`.

Domain-style sampling used here:
- `Function.IsEssentiallyStrictlyConvex` from `Definition_26_2_1`;
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- Fenchel conjugation `f⋆` from `Text_26_0_1`;
- `_root_.subdifferentialGraph_convexConjugate_eq_inv` from `Text_26_0_1`;
- `_root_.rightUnique_subdifferentialGraph_primalCodomain_iff_isEssentiallySmooth` from
  `Theorem_26_1`;
- `_root_.leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex` from
  `Theorem_26_4`.

Primitive data vs derived API:
- primitive source data: a closed proper convex function `f` and its conjugate `f⋆`;
- primitive owner predicates: `f.IsEssentiallyStrictlyConvex` and `f⋆.IsEssentiallySmooth`;
- derived API here: none.

Layer target: `source-facing`, stated directly with the intrinsic Chapter 26 owners from
Definitions 26.1.1 and 26.2.1.
-/

namespace Function.IsClosedProperConvex

variable {f : E → WithBotTop ℝ}
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)
local notation "f⋆ₛ" => ((f⋆ : StrongDual ℝ E → WithBotTop ℝ))

-- Proof sketch: rewrite essential strict convexity of `f` as left-uniqueness of the intrinsic
-- graph owner `_root_.subdifferentialGraph f`, identify that owner with right-uniqueness of the
-- conjugate graph through `_root_.subdifferentialGraph_convexConjugate_eq_inv`, and apply
-- Theorem 26.1 to `f⋆`.
/-- Theorem 26.3: for a closed proper convex function on the ambient finite-dimensional real
normed space used in Chapter 26, essential strict convexity is equivalent to essential
smoothness of the Fenchel conjugate.

Scalar-layer note: this declaration remains over `ℝ` because, in this dependency closure, the
owner predicates `Function.IsEssentiallyStrictlyConvex` and `Function.IsEssentiallySmooth`
and the subdifferential-owner bridges in Theorems 26.1/26.4 are themselves real-specific. -/
theorem isEssentiallyStrictlyConvex_iff_convexConjugate_isEssentiallySmooth
    (hf : IsClosedProperConvex[ℝ] f) :
    Function.IsEssentiallyStrictlyConvex f ↔
      f⋆ₛ.IsEssentiallySmooth := by
  sorry

end Function.IsClosedProperConvex

end
