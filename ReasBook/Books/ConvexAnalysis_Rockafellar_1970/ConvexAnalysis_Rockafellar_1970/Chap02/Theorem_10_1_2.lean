import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_5
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Continuity
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_1

-- Declarations for this item will be appended below by the statement pipeline.

section ConvexityOwner

open Set

universe u v

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [AddCommMonoid β] [ConditionallyCompleteLattice β] [SMul 𝕜 β]
variable {T : Sort v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.1.2 takes a family `f : E → T → β`, assumes each section
  `x ↦ f x t` is convex on all of `E`, assumes each fiber `{f x t | t ∈ T}` is bounded above, and
  studies the envelope `x ↦ sSup (range (f x))` for a nonempty index family.
- `core/canonical`: the owner abstraction is convexity of a `WithTopBot β`-valued lift of the
  source envelope.
- `bridge/view`: identify the lifted source envelope with an indexed `iSup`, then use epigraph
  intersection for convexity of indexed suprema.

Domain-style sampling used here:
- `Function.epi_iSup`;
- `Function.IsConvex` and `Function.isConvex_iff_convex_epigraph`;
- `convex_iInter`;
- a local `WithTopBot` bridge theorem for `toWithTopBot` and `iSup`.

Primitive data vs derived API:
- primitive inputs for the owner theorem: the index type `T`, the family `f : E → T → β`, and
  sectionwise convexity of `x ↦ f x t` on the `WithTopBot` lift;
- bridge inputs for the source-facing `sSup` theorem: pointwise bounded-above fibers and
  nonemptiness of `T`;
- derived API: convexity of the source-facing envelope `fun x ↦ sSup (range (f x))`.
-/

variable (f : E → T → β)
variable (hf_isConvex : ∀ t : T, (fun x ↦ (f x t : WithTopBot β)).IsConvex 𝕜)
variable (hf_bddAbove : ∀ x : E, BddAbove (range (f x)))

namespace Function

/-- `WithTopBot` bridge for bounded-above pointwise suprema: coercing `x ↦ sSup (range (f x))`
coincides with indexed `iSup` of section lifts. -/
theorem toWithTopBot_sSup_range_eq_iSup [Nonempty T] :
    (h_bddAbove : ∀ x : E, BddAbove (range (f x))) →
    Function.toWithTopBot (fun x ↦ sSup (range (f x))) =
      (⨆ t : T, fun x ↦ (f x t : WithTopBot β)) := by
  intro h_bddAbove
  ext x
  simp only [Function.toWithTopBot_apply, iSup_apply]
  rw [sSup_range]
  change (↑(iSup (fun t : T ↦ f x t)) : WithTopBot β) =
    (⨆ t : T, (((f x t : β) : WithTopBot β)))
  rw [WithBot.coe_iSup (h_bddAbove x)]
  rw [WithTop.coe_iSup (fun t : T ↦ ((f x t : β) : WithBot β)) (by
    rcases h_bddAbove x with ⟨a, ha⟩
    refine ⟨(a : WithBot β), ?_⟩
    rintro _ ⟨t, rfl⟩
    exact WithBot.coe_le_coe.mpr (ha ⟨t, rfl⟩)
  )]

/-- Primitive owner step for Theorem 10.1.2(1): pointwise `iSup` of sectionwise-convex
`WithTopBot`-valued sections is convex. -/
theorem isConvex_iSup_toWithTopBot :
    (h_isConvex : ∀ t : T, (fun x ↦ (f x t : WithTopBot β)).IsConvex 𝕜) →
    (⨆ t : T, fun x ↦ (f x t : WithTopBot β)).IsConvex 𝕜 := by
  intro h_isConvex
  have hInter : Convex 𝕜 (⋂ t : T, epi (fun x ↦ (f x t : WithTopBot β))) :=
    convex_iInter (fun t ↦ by
      simpa [Function.IsConvex] using h_isConvex t)
  have hEpi : Convex 𝕜 (epi (⨆ t : T, fun x ↦ (f x t : WithTopBot β))) := by
    simpa [Function.epi_iSup] using hInter
  simpa [Function.IsConvex] using hEpi

/-- Canonical owner form of Theorem 10.1.2(1): for a nonempty index family, the lifted envelope
`x ↦ (sup {f (x, t) | t ∈ T} : WithTopBot β)` is convex. -/
theorem isConvex_toWithTopBot_sSup_range [Nonempty T] :
    (h_isConvex : ∀ t : T, (fun x ↦ (f x t : WithTopBot β)).IsConvex 𝕜) →
    (h_bddAbove : ∀ x : E, BddAbove (range (f x))) →
    (Function.toWithTopBot fun x ↦ sSup (range (f x))).IsConvex 𝕜 := by
  intro h_isConvex h_bddAbove
  rw [toWithTopBot_sSup_range_eq_iSup (f := f) h_bddAbove]
  exact isConvex_iSup_toWithTopBot (f := f) h_isConvex

end Function

end ConvexityOwner

section ConvexitySource

open Set

universe u v

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [AddCommMonoid β] [ConditionallyCompleteLattice β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]
variable {T : Sort v}

namespace Function

/-- Bridge back to finite codomain: convexity of `g.toWithTopBot` yields convexity of `g` on
`Set.univ`. -/
theorem convexOn_univ_of_isConvex_toWithTopBot {g : E → β}
    (hconv : (Function.toWithTopBot g).IsConvex 𝕜) :
    ConvexOn 𝕜 univ g := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx_epi : (x, g x) ∈ epi (Function.toWithTopBot g) := by
    simp [Function.toWithTopBot]
  have hy_epi : (y, g y) ∈ epi (Function.toWithTopBot g) := by
    simp [Function.toWithTopBot]
  have hconv_epi : Convex 𝕜 (epi (Function.toWithTopBot g)) := by
    simpa [Function.IsConvex] using hconv
  have hmem := hconv_epi hx_epi hy_epi ha hb hab
  simpa [epi, Function.toWithTopBot, smul_add, add_comm, add_left_comm, add_assoc] using hmem

end Function

variable (f : E → T → β)
variable (hf_convex : ∀ t : T, ConvexOn 𝕜 univ (fun x ↦ f x t))
variable (hf_bddAbove : ∀ x : E, BddAbove (range (f x)))

include hf_convex hf_bddAbove

/-- Theorem 10.1.2 (1): if each section `x ↦ f (x, t)` is convex and each fiber
`{f (x, t) | t ∈ T}` is bounded above for a nonempty index family `T`, then the envelope
`x ↦ sup {f (x, t) | t ∈ T}` is convex, represented here by convexity on `Set.univ`. -/
theorem convexOn_univ_sSup_range [Nonempty T] :
    ConvexOn 𝕜 univ (fun x ↦ sSup (range (f x))) := by
  have hconv :
      (Function.toWithTopBot fun x ↦ sSup (range (f x))).IsConvex 𝕜 := by
    exact
      Function.isConvex_toWithTopBot_sSup_range (f := f)
        (fun t ↦ Function.isConvex_coe_of_convexOn_univ (hf_convex t))
        hf_bddAbove
  exact
    Function.convexOn_univ_of_isConvex_toWithTopBot
      (g := fun x ↦ sSup (range (f x))) hconv

end ConvexitySource

section ContinuityOwner

open Set

universe u v

variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousConstSMul ℝ E] [FiniteDimensional ℝ E]
variable {T : Sort v}

namespace Function

/-- Lift finite-valued convexity on `univ` to convexity of the `toWithTopBot` codomain lift. -/
theorem convexOn_univ_toWithTopBot_of_convexOn_univ {g : E → ℝ}
    (hg : ConvexOn ℝ univ g) :
    ConvexOn ℝ univ (Function.toWithTopBot g) := by
  refine ⟨hg.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hg.2 hx hy ha hb hab
  have hcoe : ((g (a • x + b • y) : ℝ) : WithTopBot ℝ) ≤
      ((a • g x + b • g y : ℝ) : WithTopBot ℝ) := by
    exact_mod_cast h
  simpa [Function.toWithTopBot] using hcoe

end Function

variable (f : E → T → ℝ)
variable (hf_isConvex : ∀ t : T, (fun x ↦ (f x t : WithTopBot ℝ)).IsConvex ℝ)
variable (hf_bddAbove : ∀ x : E, BddAbove (range (f x)))

include hf_isConvex hf_bddAbove

/-- Owner form of Theorem 10.1.2 (2): for a sectionwise-convex lifted family, the lifted envelope
`x ↦ (sup {f (x, t) | t ∈ T} : WithTopBot ℝ)` is continuous. -/
theorem continuous_toWithTopBot_sSup_range [Nonempty T] :
    Continuous (Function.toWithTopBot (fun x ↦ sSup (range (f x)))) := by
  have hconv :
      (Function.toWithTopBot fun x ↦ sSup (range (f x))).IsConvex ℝ := by
    exact
      Function.isConvex_toWithTopBot_sSup_range (f := f)
        hf_isConvex hf_bddAbove
  have hg_convex : ConvexOn ℝ univ (fun x ↦ sSup (range (f x))) :=
    Function.convexOn_univ_of_isConvex_toWithTopBot
      (g := fun x ↦ sSup (range (f x))) hconv
  have hconv_lift : ConvexOn ℝ univ (Function.toWithTopBot (fun x ↦ sSup (range (f x)))) :=
    Function.convexOn_univ_toWithTopBot_of_convexOn_univ
      (g := fun x ↦ sSup (range (f x))) hg_convex
  have hdom :
      (univ : Set E) ⊆ dom(Function.toWithTopBot (fun x ↦ sSup (range (f x)))) := by
    intro x _
    simpa [mem_effectiveDomain, Function.toWithTopBot] using
      (WithTop.coe_lt_top ((sSup (range (f x)) : ℝ) : WithBot ℝ))
  have hcontOn :
      ContinuousOn (Function.toWithTopBot (fun x ↦ sSup (range (f x)))) univ :=
    Function.continuousOn_of_convexOn_univ
      hconv_lift isOpen_univ.isRelativelyOpen convex_univ hdom
  simpa [continuousOn_univ] using hcontOn

/-- Theorem 10.1.2 (2), owner-facing finite-codomain form: for a sectionwise-convex lifted
family, the pointwise supremum envelope depends continuously on `x`. -/
theorem continuous_sSup_range [Nonempty T] :
    Continuous (fun x ↦ sSup (range (f x))) := by
  exact (WithBotTop.continuous_coe_iff).1 <|
    by
      simpa [Function.toWithTopBot] using
        (continuous_toWithTopBot_sSup_range
          (f := f) hf_isConvex hf_bddAbove)

end ContinuityOwner

section ContinuitySource

open Set

universe u v

variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousConstSMul ℝ E] [FiniteDimensional ℝ E]
variable {T : Sort v}

variable (f : E → T → ℝ)
variable (hf_convex : ∀ t : T, ConvexOn ℝ univ (fun x ↦ f x t))
variable (hf_bddAbove : ∀ x : E, BddAbove (range (f x)))

include hf_convex hf_bddAbove

/-- Theorem 10.1.2 (2), source-facing form: if each section `x ↦ f (x, t)` is convex on `univ`
and each fiber `{f (x, t) | t ∈ T}` is bounded above, then `x ↦ sup {f (x, t) | t ∈ T}` is
continuous. -/
theorem continuous_sSup_range_of_convexOn_univ [Nonempty T] :
    Continuous (fun x ↦ sSup (range (f x))) := by
  exact
    continuous_sSup_range (f := f)
      (fun t ↦ Function.isConvex_coe_of_convexOn_univ (hf_convex t))
      hf_bddAbove

end ContinuitySource
