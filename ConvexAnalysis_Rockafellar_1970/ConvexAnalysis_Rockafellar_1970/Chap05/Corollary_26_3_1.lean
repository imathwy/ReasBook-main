import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_26_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_2_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_26_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_26_4

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
