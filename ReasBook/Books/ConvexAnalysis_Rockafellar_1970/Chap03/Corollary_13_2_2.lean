import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_10_1_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar
open Bornology

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ]

/-!
Source/core/bridge triage:
- `source-facing`: Corollary 13.2.2 classifies the support functions `δᵛ(· | C)` coming from
  nonempty bounded convex subsets of a finite-dimensional real seminormed space equipped with a
  continuous linear self-pairing, recovering the textbook `ℝ^n` statement by specialization.
- `core/canonical`: the owner abstractions are the chapter support function `supportFunction`,
  the owner characterization
  `exists_nonempty_convex_set_with_supportFunction_eq_iff_closed_proper_convex_and_positivelyHomogeneous`,
  the canonical set-side predicates `Set.Nonempty`, `IsClosed`, `Convex`, and `IsBounded`, the barrier-cone
  owner `barr[ℝ](C)`, the generic positive-homogeneity predicate
  `Function.PositivelyHomogeneous`, the chapter convexity owner `f.IsConvex`, and the
  closed/proper/convex owner `f.IsClosedProperConvex`, together with the canonical codomain-side
  finiteness owners `dom f = (univ : Set E)` and `∀ x, ⊥ < f x`.
- `bridge/view`: Rockafellar's boundedness side is mediated canonically by the barrier-cone owner
  `barr[ℝ](C)` together with the support-function finiteness bridge
  `xStar ∈ barr[ℝ](C) ↔ xStar ∈ dom(δᵛ(· | C))`.
  The source's textbook notation `δᵛ(· | C)` is the function-level surface form of the owner
  `supportFunction C`, and the source's “finite” condition on `f` is rendered by the intrinsic
  codomain-side conditions “never `⊤`” and “never `⊥`”, i.e. `dom f = (univ : Set E)` together
  with `∀ x, ⊥ < f x`.

Primitive data vs derived API:
- primitive source-facing data: the set `C : Set E` and the owner function `supportFunction C`;
- derived owner-side conditions: `f.IsClosedProperConvex` from convexity plus finite-codomain
  domain/lower-finiteness conditions, and boundedness of `C` from the owner-side criterion that every
  dual vector belongs to `barr[ℝ](C)`.

Domain-style sampling used here:
- the chapter support-function characterization owner
  `exists_nonempty_convex_set_with_supportFunction_eq_iff_closed_proper_convex_and_positivelyHomogeneous`
  from `Theorem_13_2`;
- the owner support function `supportFunction` from `Text_13_0_1`;
- the owner bridges `mem_barrierCone_iff_supportFunction_lt_top` and
  `mem_barrierCone_iff_mem_effectiveDomain_supportFunction_self` from `Text_13_0_4`;
- the owner bridge `ConvexOn.continuous_of_dom_eq_univ` from
  `Corollary_10_1_1`.
- Ambient refinement: those owner declarations already live on arbitrary finite-dimensional real
  spaces with continuous linear self-pairings, so this corollary is stated at that intrinsic
  owner layer instead of forcing an inner-product model. Specializing to
  `EuclideanSpace ℝ (Fin n)` with its canonical pairing recovers the textbook statement.
-/

-- Proof sketch: for the forward direction, apply the owner theorem from Theorem 13.2 to identify
-- `δᵛ(· | C)` as closed proper convex and positively homogeneous, then use the owner-side
-- boundedness criterion `IsBounded C ↔ ∀ xStar, xStar ∈ barr[ℝ](C)` together with
-- `mem_barrierCone_iff_supportFunction_lt_top` to recover the full-domain condition
-- `dom f = (univ : Set E)`; nonemptiness of `C` yields the pointwise lower-finiteness condition
-- `∀ xStar, ⊥ < δᵛ(xStar | C)`. For the
-- reverse direction, combine the owner continuity bridge
-- `ConvexOn.continuous_of_dom_eq_univ` with
-- `exists_nonempty_convex_set_with_supportFunction_eq_iff_closed_proper_convex_and_positivelyHomogeneous`;
-- the full-domain condition makes every vector lie in `barr[ℝ](C)`, hence the resulting witness
-- set is bounded.

private theorem isBounded_iff_forall_mem_barrierCone {C : Set E}
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) :
    IsBounded C ↔ ∀ xStar : E, xStar ∈ barr[ℝ](C) := by
  sorry

private theorem supportFunction_bot_lt_of_nonempty {C : Set E}
    (hC_nonempty : C.Nonempty) (xStar : E) :
    (⊥ : WithTopBot ℝ) < δᵛ(xStar | C) := by
  rcases hC_nonempty with ⟨x, hx⟩
  rw [supportFunction_def]
  exact lt_of_lt_of_le
    (WithTopBot.bot_lt_coe _)
    (le_iSup (fun y : C ↦ (⟪xStar, y.1⟫ₚ : WithTopBot ℝ)) ⟨x, hx⟩)

/-- Corollary 13.2.2, in canonical ambient form: a `WithTopBot ℝ`-valued function on a
finite-dimensional real seminormed space equipped with a continuous linear self-pairing is the support
function `δᵛ(· | C)` of a nonempty bounded convex set iff it is finite-valued, positively
homogeneous, and convex. Specializing to `EuclideanSpace ℝ (Fin n)` with its canonical pairing
recovers the textbook `R^n` statement. -/
theorem exists_nonempty_bounded_convex_supportFunction_iff_finite_positivelyHomogeneous_convex
    (f : E → WithTopBot ℝ) :
    (∃ C : Set E,
      C.Nonempty ∧ Convex ℝ C ∧ IsBounded C ∧ f = (δᵛ(· | C) : E → WithTopBot ℝ)) ↔
      dom(f) = (Set.univ : Set E) ∧
        (∀ x : E, (⊥ : WithTopBot ℝ) < f x) ∧
          f.PositivelyHomogeneous ℝ ∧ f.IsConvex ℝ := by
  constructor
  · rintro ⟨C, hC_nonempty, hC_convex, hC_bounded, rfl⟩
    have hsupport :
        Function.IsClosedProperConvex (𝕜 := ℝ) (δᵛ(· | C) : E → WithTopBot ℝ) ∧
          (δᵛ(· | C) : E → WithTopBot ℝ).PositivelyHomogeneous ℝ :=
      (exists_nonempty_convex_set_with_supportFunction_eq_iff_closed_proper_convex_and_positivelyHomogeneous
          (δᵛ(· | C) : E → WithTopBot ℝ)).1
        ⟨C, hC_nonempty, hC_convex, rfl⟩
    have hdom_subset :
        (Set.univ : Set E) ⊆ dom((δᵛ(· | C) : E → WithTopBot ℝ)) := by
      intro xStar _
      exact
        (mem_barrierCone_iff_mem_effectiveDomain_supportFunction_self
          (C := C) (zStar := xStar)).1
          ((isBounded_iff_forall_mem_barrierCone hC_nonempty hC_convex).1 hC_bounded xStar)
    have hdom : dom((δᵛ(· | C) : E → WithTopBot ℝ)) = (Set.univ : Set E) := by
      exact Set.Subset.antisymm (by intro x _; exact Set.mem_univ x) hdom_subset
    have hbot : ∀ x : E, (⊥ : WithTopBot ℝ) < (δᵛ(x | C) : WithTopBot ℝ) := by
      intro x
      exact supportFunction_bot_lt_of_nonempty hC_nonempty x
    exact ⟨hdom, hbot, hsupport.2, hsupport.1.convex⟩
  · rintro ⟨hf_dom, hf_bot_lt, hf_hom, hf_convex⟩
    have hf_dom_univ : dom(f) = (Set.univ : Set E) := by
      simpa using hf_dom
    have hf_convexOn : ConvexOn ℝ (Set.univ : Set E) f := by
      exact convexOn_of_convex_finiteHeight_epigraph
        (s := (Set.univ : Set E)) (f := f)
        (by simpa [Function.IsConvex] using hf_convex) convex_univ
    have hf_proper : f.IsProper := by
      rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
      refine ⟨?_, hf_bot_lt⟩
      refine ⟨0, ?_⟩
      rw [hf_dom_univ]
      exact Set.mem_univ 0
    have hf_closed : Function.IsClosedProperConvex (𝕜 := ℝ) f := by
      refine
        ⟨hf_convex, hf_proper,
          (hf_convexOn.continuous_of_dom_eq_univ hf_dom_univ).lowerSemicontinuous⟩
    rcases
        (exists_nonempty_convex_set_with_supportFunction_eq_iff_closed_proper_convex_and_positivelyHomogeneous
          f).2 ⟨hf_closed, hf_hom⟩ with
      ⟨C, hC_nonempty, hC_convex, hC_support⟩
    have hC_bounded : IsBounded C := by
      refine (isBounded_iff_forall_mem_barrierCone hC_nonempty hC_convex).2 ?_
      intro xStar
      exact
        (mem_barrierCone_iff_mem_effectiveDomain_supportFunction_self
          (C := C) (zStar := xStar)).2
          (by
            have hxStar_dom : xStar ∈ dom(f) := by
              rw [hf_dom_univ]
              exact Set.mem_univ xStar
            simpa [hC_support] using hxStar_dom)
    exact ⟨C, hC_nonempty, hC_convex, hC_bounded, hC_support⟩

end
