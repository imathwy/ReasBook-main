import Mathlib
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_10_1_1 (from Chap02) -/
section

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousConstSMul ℝ E] [FiniteDimensional ℝ E]

noncomputable local instance : SMul ℝ (WithTopBot ℝ) where
  smul r x := (r : WithTopBot ℝ) * x

open scoped Rockafellar
open Set

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 10.1.1 says that a finite convex function on `R^n`, hence an
  ordinary real-valued convex function on all of `R^n`, is continuous. As elsewhere in the chapter,
  the textbook `R^n` ambient space is rendered by the intrinsic owner layer of arbitrary
  finite-dimensional real topological vector spaces.
- `core/canonical`: the owner abstractions are mathlib's `ConvexOn ℝ (univ : Set E) f`,
  `ConvexOn.continuousOn`, and the whole-space bridge `continuousOn_univ`.
- `bridge/view`: the codomain owner layer is `WithTopBot ℝ`, with `EReal` used downstream only as
  notation/view. The whole-space finiteness owner is `dom(f) = univ`, while the specialization of
  Theorem 10.1 still takes the primitive bridge input `univ ⊆ dom(f)`.

Domain-style sampling used here:
- `ConvexOn.continuousOn`;
- `ConvexOn.locallyLipschitz`;
- `continuousOn_univ`;
- the chapter continuity theorem `Function.continuousOn_of_convexOn_univ`.

Primitive data vs derived API:
- primitive input: a real-valued function `f : E → ℝ` together with its global convexity owner
  `ConvexOn ℝ (univ : Set E) f`;
- derived API: global continuity `Continuous f`, obtained directly from the owner theorem
  `ConvexOn.continuousOn` and `continuousOn_univ`, so no parallel local theorem is kept;
- bridge API: continuity of a `WithTopBot ℝ`-valued convex function from the canonical full-domain
  owner hypothesis `dom(f) = univ`; the primitive Theorem 10.1 input `univ ⊆ dom(f)` is used only
  as an internal proof bridge. The pointwise real-valued condition is a downstream source-facing
  corollary.

Layer target: the real-valued content is `bridge/view`, handled by direct canonical recall of the
owner-side continuity declarations, while the extended-real theorem remains the nontrivial chapter
bridge.
-/

/- Corollary 10.1.1, real-valued owner form: for `f : E → ℝ`, whole-space continuity is obtained
directly from the canonical owner declarations `ConvexOn.continuousOn` and `continuousOn_univ`,
so no duplicate local theorem is introduced here. -/
recall ConvexOn.continuousOn
recall continuousOn_univ

namespace ConvexOn

-- Internal bridge: specialized Theorem 10.1 hypothesis shape at `C = univ`.
private theorem continuous_of_univ_subset_dom {f : E → WithTopBot ℝ}
    (hf : ConvexOn ℝ (univ : Set E) f)
    (hdom : (univ : Set E) ⊆ dom(f)) :
    Continuous f := by
  simpa [continuousOn_univ] using
    Function.continuousOn_of_convexOn_univ
      (f := f) hf isOpen_univ.isRelativelyOpen convex_univ hdom

/-- Canonical whole-domain owner form of Corollary 10.1.1:
if a convex `WithTopBot ℝ`-valued function has effective domain `univ`, then it is continuous. -/
theorem continuous_of_dom_eq_univ {f : E → WithTopBot ℝ}
    (hf : ConvexOn ℝ (univ : Set E) f)
    (hdom : dom(f) = (univ : Set E)) :
    Continuous f := by
  refine continuous_of_univ_subset_dom hf ?_
  intro x hx
  rw [hdom]
  exact hx

/-- Source-facing finite-valued corollary of Corollary 10.1.1:
if a convex `WithTopBot ℝ`-valued function is finite everywhere (equivalently, never `⊤`), then
it is continuous. -/
theorem continuous_of_finite {f : E → WithTopBot ℝ}
    (hf : ConvexOn ℝ (univ : Set E) f)
    (hf_finite : ∀ x : E, f x < ⊤) :
    Continuous f := by
  have hdom : dom(f) = (univ : Set E) := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      simpa [mem_effectiveDomain] using hf_finite x
  exact continuous_of_dom_eq_univ hf hdom

end ConvexOn

end

/-! ### Theorem_10_1 (from Chap02) -/
section

open scoped Rockafellar

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousConstSMul ℝ E] [FiniteDimensional ℝ E]

noncomputable instance instTopologicalSpaceWithTopBotRealFromEReal :
    TopologicalSpace (WithTopBot ℝ) := by
  change TopologicalSpace EReal
  infer_instance

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.1 states continuity of a convex extended-real-valued function on any
  relatively open convex subset of its effective domain. The textbook coordinate presentation is a
  specialization of the intrinsic finite-dimensional real topological-vector-space owner layer used
  here.
- `core/canonical`: the owner abstractions are `ConvexOn` on sets,
  `IsRelativelyOpen`, the effective-domain set `{x : E | f x < ⊤}`, and the relative continuity
  owner `ContinuousOn`.
- `bridge/view`: Rockafellar's `ri (dom f)` is represented by the chapter notation `riDom(f)`.

Domain-style sampling used here:
- `ConvexOn` and `ConvexOn.subset`;
- `ConvexOn.convex_dom` from `Prop_4_4_1`;
- `IsRelativelyOpen` and `isRelativelyOpen_ri` from `Text_6_11`/`Text_6_17`;
- `Convex.intrinsicInterior` from `Theorem_6_2`;
- mathlib's owner notion `ContinuousOn`.

Primitive data vs derived API:
- primitive inputs: the function `f`, its convexity-on-set owner hypothesis, and a relatively open
  convex set `C` contained in `dom(f)`;
- derived API: continuity of `f` on `C`, and the special case `C = riDom(f)` from whole-space
  convexity owner data `ConvexOn ℝ Set.univ f`.

Scalar-layer check for this item:
- the source item is an extended-real convex-analysis statement, and the codomain owner is
  intrinsically `WithTopBot ℝ`;
- replacing `ℝ` by a different scalar would define a different mathematical object rather than a
  weakening of assumptions for the same owner;
- therefore the canonical surface remains explicitly real, with domain notation `riDom(f)`.

Layer target: this item stays `source-facing`, expressed directly with the canonical owners
`ConvexOn`, `IsRelativelyOpen`, and `ContinuousOn`, with the real-domain notation `riDom(·)`.
-/

namespace ConvexOn

variable {f : E → WithTopBot ℝ} {C : Set E}

/-- Theorem 10.1 at the primitive restricted owner layer: if a `WithTopBot ℝ`-valued function is
convex on `C`, then it is continuous relative to every relatively open `C` contained in its
effective domain. -/
-- Proof sketch: same as the source statement, but at the primitive restricted owner layer
-- `ConvexOn ℝ C`. The convexity of `C` needed in the intrinsic-interior step is contained in `hf`.
theorem continuousOn_of_isRelativelyOpen_subset_dom
    (hf : ConvexOn ℝ C f) (hC_open : IsRelativelyOpen ℝ C)
    (hC_dom : C ⊆ dom(f)) :
    ContinuousOn f C := sorry

/-- The relative interior of the effective domain is a canonical relatively open convex subset on
which a globally convex `WithTopBot ℝ`-valued function is continuous. -/
theorem continuousOn_riDom
    (hf : ConvexOn ℝ (Set.univ : Set E) f) :
    ContinuousOn f (riDom(f)) := sorry

end ConvexOn

namespace Function

variable {f : E → WithTopBot ℝ}

/-- Theorem 10.1 source-facing whole-space-owner form: if `f` is convex on `Set.univ`, then `f`
is continuous relative to every relatively open convex set contained in its effective domain. -/
theorem continuousOn_of_convexOn_univ
    (hf : ConvexOn ℝ (Set.univ : Set E) f) {C : Set E}
    (hC_open : IsRelativelyOpen ℝ C)
    (hC_conv : Convex ℝ C) (hC_dom : C ⊆ dom(f)) :
    ContinuousOn f C := by
  exact ConvexOn.continuousOn_of_isRelativelyOpen_subset_dom
    (hf := hf.subset (Set.subset_univ C) hC_conv) hC_open hC_dom

/-- Theorem 10.1 `ri (dom f)` corollary at the whole-space-owner layer
`ConvexOn ℝ Set.univ f`. -/
theorem continuousOn_riDom_of_convexOn_univ
    (hf : ConvexOn ℝ (Set.univ : Set E) f) :
    ContinuousOn f (riDom(f)) :=
  hf.continuousOn_riDom

end Function

end

/-! ### Theorem_10_1_2 (from Chap02) -/
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

/-! ### Theorem_10_1_3 (from Chap02) -/
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Pointwise Rockafellar
open Set

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.1.3 studies the function
  `x ↦ inf {f y | y ∈ C + {x}}` attached to a convex function `f` and a convex set `C`.
- `core/canonical`: the owner abstractions are `indicatorFunction`, `infimal_convolution` / `□`,
  `Function.IsConvex`, the source formula `x ↦ sInf (f '' (C + {x}))` at
  `f : E → WithBotTop 𝕜`, and the continuity owner theorem from `Theorem_10_1`.
- `bridge/view`: the source formula is the indicator-specialized infimal convolution
  `((δ[𝕜](· | -C)) □ f) x`, identified with the translate infimum `sInf (f '' (C + {x}))`; the
  finite-valued textbook surface is recovered by specializing `f` to `f.toWithTopBot`.

Domain-style sampling used here:
- `infimal_convolution_indicator_neg_eq_sInf_image_translate`;
- `Function.IsConvex.indicator_neg_infimal_convolution`;
- the chapter bridge `Function.isConvex_coe_of_convexOn_univ`;
- the continuity owner theorem
  `Function.IsConvex.continuousOn`
  from Theorem 10.1.

Primitive data vs derived API:
- primitive inputs for convexity: the set `C`, the scalar `𝕜`, and an owner-level function
  `f : E → WithBotTop 𝕜` with the no-`⊥` guard `∀ y, ⊥ < f y` needed by the indicator-translate
  identity;
- primitive inputs for continuity: the same owner-level function in the real topological layer of
  Theorem 10.1, with the pointwise finite-above guard `∀ y, f y < ⊤`;
- derived API: the finite-valued source-facing corollaries obtained by specializing to
  `f.toWithTopBot` and `ConvexOn 𝕜 univ f`.
-/

section Pointwise

variable {E : Type*} [AddGroup E]
variable {α : Type*} [ConditionallyCompleteLattice α] [Add α] [Zero α]

private theorem indicator_neg_infimal_convolution_eq_sInf_image_translate
    (C : Set E) (f : E → WithBotTop α) (hf_bot : ∀ y : E, ⊥ < f y) :
    ((δ[α](· | -C)) □ f) =
      fun x ↦ sInf (f '' (C + {x})) := by
  funext x
  simpa using infimal_convolution_indicator_neg_eq_sInf_image_translate C f hf_bot x

end Pointwise

section Convex

variable {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: rewrite the translate-infimum surface by the canonical identity from
-- Example 9.2.2.2, then apply convexity of the indicator-specialized infimal convolution.
/-- Canonical owner form of Theorem 10.1.3 (1): for `f : E → WithBotTop 𝕜`, if `C` is convex,
`f` is convex, and `f` avoids `⊥`, then `x ↦ sInf (f '' (C + {x}))` is convex. -/
theorem Function.IsConvex.sInf_image_translate_of_bot_lt
    {f : E → WithBotTop 𝕜} (hf_convex : f.IsConvex 𝕜)
    (C : Set E) (hC_convex : Convex 𝕜 C) (hf_bot : ∀ y : E, ⊥ < f y) :
    (fun x ↦ sInf (f '' (C + {x}))).IsConvex 𝕜 := by
  rw [← indicator_neg_infimal_convolution_eq_sInf_image_translate C f hf_bot]
  exact hf_convex.indicator_neg_infimal_convolution C hC_convex

-- Proof sketch: this is the finite-valued specialization of
-- `Function.IsConvex.sInf_image_translate_of_bot_lt`; the no-`⊥` guard is automatic for
-- `f.toWithTopBot`.
/-- Canonical finite-valued owner form of Theorem 10.1.3 (1): if `f.toWithTopBot` is convex and
`C` is convex, then `x ↦ sInf (f.toWithTopBot '' (C + {x}))` is convex. -/
theorem Function.IsConvex.sInf_image_translate_toWithTopBot
    {f : E → 𝕜} (hf_convex : f.toWithTopBot.IsConvex 𝕜)
    (C : Set E) (hC_convex : Convex 𝕜 C) :
    (fun x ↦ sInf (f.toWithTopBot '' (C + {x}))).IsConvex 𝕜 := by
  exact
    hf_convex.sInf_image_translate_of_bot_lt
      C hC_convex (fun y ↦ WithBotTop.bot_lt_coe (f y))

-- Proof sketch: specialize the canonical owner theorem above to `f.toWithTopBot` and discharge
-- the no-`⊥` guard by `WithBotTop.bot_lt_coe`; convert the convexity assumption with
-- `Function.isConvex_coe_of_convexOn_univ`.
/-- Source-facing form of Theorem 10.1.3 (1): if `f : E → 𝕜` is convex and `C ⊆ E` is convex,
then the translate-infimum function
`x ↦ inf {f y | y ∈ C + {x}}`, rendered as
`x ↦ sInf (f.toWithTopBot '' (C + {x}))`, is convex. -/
theorem Function.isConvex_sInf_image_translate_toWithTopBot_of_convexOn_univ
    (C : Set E) (hC_convex : Convex 𝕜 C) (f : E → 𝕜)
    (hf_convex : ConvexOn 𝕜 univ f) :
    (fun x ↦ sInf (f.toWithTopBot '' (C + {x}))).IsConvex 𝕜 := by
  exact
    (Function.isConvex_coe_of_convexOn_univ hf_convex).sInf_image_translate_toWithTopBot
      C hC_convex

end Convex

section ContinuityAux

variable {E : Type*} [AddCommGroup E]
variable {α : Type*} [ConditionallyCompleteLattice α] [AddMonoid α]

private theorem indicator_neg_infimal_convolution_lt_top_of_nonempty
    (C : Set E) (hC_nonempty : C.Nonempty) (f : E → WithBotTop α)
    (hf_top : ∀ y : E, f y < ⊤) (x : E) :
    (((δ[α](· | -C)) □ f) x) < (⊤ : WithBotTop α) := by
  rcases hC_nonempty with ⟨c, hc⟩
  have hnegc : -c ∈ -C := by
    rwa [Set.mem_neg, neg_neg]
  have hle :
      (((δ[α](· | -C)) □ f) x) ≤
        f (x + c) := by
    rw [infimal_convolution_apply]
    refine iInf_le_of_le (-c) ?_
    simp [hnegc]
  exact lt_of_le_of_lt hle (hf_top (x + c))

end ContinuityAux

section Continuity

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousConstSMul ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: apply Theorem 10.1 on `univ` to
-- `g := ((δ[ℝ](· | -C)) □ f)`, using convexity from Example 9.2.2.2 and pointwise finiteness from
-- the nonempty-translate estimate.
/-- Nonempty-set owner form for Theorem 10.1.3 (2): if `C` is convex and nonempty, `f` is convex,
and `f` is finite from above, then `((δ[ℝ](· | -C)) □ f)` is continuous. -/
theorem Function.IsConvex.continuous_indicator_neg_infimal_convolution_of_nonempty_of_lt_top
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ)
    (C : Set E) (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty)
    (hf_top : ∀ x : E, f x < ⊤) :
    Continuous (((δ[ℝ](· | -C)) □ f)) := by
  let g : E → WithBotTop ℝ := ((δ[ℝ](· | -C)) □ f)
  have hconv : g.IsConvex ℝ := by
    simpa [g] using hf_convex.indicator_neg_infimal_convolution C hC_convex
  have hdom : (univ : Set E) ⊆ dom(g) := by
    intro x _
    exact
      indicator_neg_infimal_convolution_lt_top_of_nonempty
        C hC_nonempty f hf_top x
  simpa [g, continuousOn_univ] using
    Function.IsConvex.continuousOn
      hconv isOpen_univ.isRelativelyOpen convex_univ hdom

-- Proof sketch: Example 9.2.2.2 gives convexity of `((δ[ℝ](· | -C)) □ f)`. If `C = ∅`, then
-- `δ[ℝ](· | -C)` is constantly `⊤`; the no-`⊥` guard on `f` makes the infimal convolution
-- constantly `⊤`. If `C` is nonempty, the private lemma above gives `((δ[ℝ](· | -C)) □ f) x < ⊤`
-- everywhere, so Theorem 10.1 applies on `univ`.
/-- Canonical owner form of Theorem 10.1.3 (2): for `f : E → WithBotTop ℝ`, if `C` is convex, `f`
is convex, `f` avoids `⊥`, and `f` is finite from above, then
`((δ[ℝ](· | -C)) □ f)` is continuous. -/
theorem Function.IsConvex.continuous_indicator_neg_infimal_convolution_of_bot_lt_of_lt_top
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ)
    (C : Set E) (hC_convex : Convex ℝ C)
    (hf_bot : ∀ x : E, ⊥ < f x) (hf_top : ∀ x : E, f x < ⊤) :
    Continuous (((δ[ℝ](· | -C)) □ f)) := by
  let g : E → WithBotTop ℝ := ((δ[ℝ](· | -C)) □ f)
  have hcont : Continuous g := by
    have hconv : g.IsConvex ℝ := by
      simpa [g] using
        hf_convex.indicator_neg_infimal_convolution C hC_convex
    by_cases hC_empty : C = ∅
    · have htop :
        g =
          fun _ : E ↦ (⊤ : WithBotTop ℝ) := by
          subst hC_empty
          have hdelta :
              (δ[ℝ](· | -∅)) = fun _ : E ↦ (⊤ : WithBotTop ℝ) := by
            funext y
            simp
          ext x
          change (((δ[ℝ](· | -∅)) □ f) x) = ⊤
          rw [hdelta, infimal_convolution_apply]
          have hconst : ∀ i : E, (⊤ : WithBotTop ℝ) + f (x - i) = ⊤ := by
            intro i
            exact WithBotTop.top_add_of_ne_bot (ne_of_gt (hf_bot (x - i)))
          simp [hconst]
      rw [htop]
      exact continuous_const
    · have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
      simpa [g] using
        hf_convex.continuous_indicator_neg_infimal_convolution_of_nonempty_of_lt_top
          C hC_convex hC_nonempty hf_top
  simpa [g] using hcont

-- Proof sketch: rewrite by the indicator-translate identity from Example 9.2.2.2 and apply the
-- owner theorem above.
/-- Canonical source-form owner of Theorem 10.1.3 (2): under the same assumptions as
`Function.IsConvex.continuous_indicator_neg_infimal_convolution_of_bot_lt_of_lt_top`, the translate
infimum function `x ↦ sInf (f '' (C + {x}))` is continuous. -/
theorem Function.IsConvex.continuous_sInf_image_translate_of_bot_lt_of_lt_top
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ)
    (C : Set E) (hC_convex : Convex ℝ C)
    (hf_bot : ∀ x : E, ⊥ < f x) (hf_top : ∀ x : E, f x < ⊤) :
    Continuous (fun x ↦ sInf (f '' (C + {x}))) := by
  rw [← indicator_neg_infimal_convolution_eq_sInf_image_translate C f hf_bot]
  exact
    hf_convex.continuous_indicator_neg_infimal_convolution_of_bot_lt_of_lt_top
      C hC_convex hf_bot hf_top

-- Proof sketch: specialize the owner theorem above to `f.toWithTopBot`, where both
-- `⊥ < f.toWithTopBot x` and `f.toWithTopBot x < ⊤` are immediate.
/-- Canonical finite-valued owner form of Theorem 10.1.3 (2): if `f.toWithTopBot` is convex and
`C` is convex, then `((δ[ℝ](· | -C)) □ f.toWithTopBot)` is continuous. -/
theorem Function.IsConvex.continuous_indicator_neg_infimal_convolution_toWithTopBot
    {f : E → ℝ} (hf_convex : f.toWithTopBot.IsConvex ℝ)
    (C : Set E) (hC_convex : Convex ℝ C) :
    Continuous (((δ[ℝ](· | -C)) □ f.toWithTopBot)) := by
  exact
    hf_convex.continuous_indicator_neg_infimal_convolution_of_bot_lt_of_lt_top
      C hC_convex
      (fun y ↦ WithBotTop.bot_lt_coe (f y))
      (fun y ↦ WithBotTop.coe_lt_top (f y))

-- Proof sketch: specialize the owner theorem to `f.toWithTopBot`, where both
-- `⊥ < f.toWithTopBot x` and `f.toWithTopBot x < ⊤` are immediate.
/-- Source-facing owner form of Theorem 10.1.3 (2): if `f : E → ℝ` is convex on `univ` and `C` is
convex, then `((δ[ℝ](· | -C)) □ f.toWithTopBot)` is continuous. -/
theorem continuous_indicator_neg_infimal_convolution_toWithTopBot_of_convexOn_univ
    (C : Set E) (hC_convex : Convex ℝ C) (f : E → ℝ)
    (hf_convex : ConvexOn ℝ univ f) :
    Continuous (((δ[ℝ](· | -C)) □ f.toWithTopBot)) := by
  exact
    Function.IsConvex.continuous_indicator_neg_infimal_convolution_toWithTopBot
      (hf_convex := Function.isConvex_coe_of_convexOn_univ hf_convex)
      C hC_convex

-- Proof sketch: specialize the canonical source-form owner theorem above to `f.toWithTopBot`.
/-- Canonical finite-valued source-form owner of Theorem 10.1.3 (2): if `f.toWithTopBot` is convex
and `C` is convex, then `x ↦ sInf (f.toWithTopBot '' (C + {x}))` is continuous. -/
theorem Function.IsConvex.continuous_sInf_image_translate_toWithTopBot
    {f : E → ℝ} (hf_convex : f.toWithTopBot.IsConvex ℝ)
    (C : Set E) (hC_convex : Convex ℝ C) :
    Continuous (fun x ↦ sInf (f.toWithTopBot '' (C + {x}))) := by
  exact
    hf_convex.continuous_sInf_image_translate_of_bot_lt_of_lt_top
      C hC_convex
      (fun y ↦ WithBotTop.bot_lt_coe (f y))
      (fun y ↦ WithBotTop.coe_lt_top (f y))

-- Proof sketch: specialize the canonical source-form owner theorem above to `f.toWithTopBot`.
/-- Source-facing form of Theorem 10.1.3 (2): if `f : E → ℝ` is convex and `C ⊆ E` is convex,
then the translate-infimum function
`x ↦ inf {f y | y ∈ C + {x}}`, rendered as
`x ↦ sInf (f.toWithTopBot '' (C + {x}))`, depends continuously on `x`. -/
theorem continuous_sInf_image_translate_toWithTopBot_of_convexOn_univ
    (C : Set E) (hC_convex : Convex ℝ C) (f : E → ℝ)
    (hf_convex : ConvexOn ℝ univ f) :
    Continuous (fun x ↦ sInf (f.toWithTopBot '' (C + {x}))) := by
  exact
    Function.IsConvex.continuous_sInf_image_translate_toWithTopBot
      (hf_convex := Function.isConvex_coe_of_convexOn_univ hf_convex)
      C hC_convex

end Continuity

/-! ### Theorem_10_1_4 (from Chap02) -/
noncomputable section

open Filter
open scoped Rockafellar

section FunctionOwner

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]

local notation "R2" => 𝕜 × 𝕜

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.1.4 introduces a specific quadratic-over-linear owner, identifies
  its effective domain and support-set representation, and then records continuity/path behavior at
  the boundary point `0`.
- `core/canonical`: the owner abstractions are the chapter support function `supportFunction`, the
  chapter convexity predicate `Function.IsConvex`, and the effective-domain owner `dom(·)`.
- `bridge/view`: continuity/path-limit consequences reuse Theorem 10.1's real topological owner
  layer, so they remain in the `𝕜 = ℝ` specialization section below.
- `bridge/view`: Rockafellar's coordinate formula is rendered directly as the concrete function
  `quadraticOverLinearFunction`, while the set
  `{(x₁, x₂) | x₁ + x₂² / 2 ≤ 0}` is rendered as `quadraticOverLinearSupportSet`.

Domain-style sampling used here:
- the project owner `supportFunction` from Definition 4.8.2;
- the project predicate `Function.IsConvex` from Theorem 4.2;
- the project theorem `Function.isConvex_supportFunction` sampled in Text 5.5.0.

Primitive data vs derived API:
- primitive source-facing data: the explicit function and its support set;
- auxiliary source-facing syntax: the parabolic approach in part (7) is kept directly in that
  theorem statement rather than packaged as a separate public wrapper;
- derived API: convexity, the effective-domain description, the support-function identity,
  continuity away from the boundary, lower semicontinuity at the origin, and the two contrasting
  path limits.

Layer target:
- core owner/API at the scalar-generic layer `R2 = 𝕜 × 𝕜`, codomain `WithTopBot 𝕜`;
- real topological consequences in the `𝕜 = ℝ` bridge section.
-/

/-- The scalar-generic quadratic-over-linear owner on `R² = 𝕜 × 𝕜`, valued in `WithTopBot 𝕜`,
extended by
the value `0` at the origin
and `+∞` elsewhere outside the open half-space `x₁ > 0`. -/
def quadraticOverLinearFunction : R2 → WithTopBot 𝕜 :=
  fun ξ ↦
    if 0 < ξ.1 then
      ((ξ.2 ^ 2 / (2 * ξ.1) : 𝕜) : WithTopBot 𝕜)
    else if ξ = 0 then
      (0 : WithTopBot 𝕜)
    else
      ⊤

/-- The Chapter 10 quadratic-over-linear owner never takes the value `⊥`; its only nonfinite
value is `⊤`. -/
theorem quadraticOverLinearFunction_neBot (ξ : R2) :
    quadraticOverLinearFunction ξ ≠ ⊥ := by
  unfold quadraticOverLinearFunction
  split_ifs with h0 hξ
  · simp
  · simp
  · simp

/-- Theorem 10.1.4 (2): the effective domain of the quadratic-over-linear example is
`{ξ | ξ₁ > 0} ∪ {(0, 0)}`, rendered canonically as `dom(quadraticOverLinearFunction)`. -/
-- Proof sketch: either `ξ.1 > 0`, in which case the finite quadratic-over-linear branch applies,
-- or `ξ.1 ≤ 0`. In the latter case the only finite point is `ξ = 0`, handled by the middle
-- branch; every other point falls in the `⊤` branch. This gives exactly the displayed union.
theorem quadraticOverLinearFunction_effectiveDomain :
    dom(quadraticOverLinearFunction) = {ξ : R2 | 0 < ξ.1} ∪ ({0} : Set R2) := sorry

end FunctionOwner

section SupportSetOwner

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜

/-- The parabolic sublevel set `{(x₁, x₂) | 2 x₁ + x₂² ≤ 0}` used in Theorem 10.1.4. -/
def quadraticOverLinearSupportSet : Set R2 :=
  {x : R2 | (2 : 𝕜) * x.1 + x.2 ^ 2 ≤ 0}

end SupportSetOwner

section GenericBase

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜

/-- Theorem 10.1.4 (3): the set
`quadraticOverLinearSupportSet = {(x₁, x₂) | 2 x₁ + x₂² ≤ 0}` is convex. -/
-- Proof sketch: write the defining inequality as the sublevel condition
-- `x.1 ≤ -x.2 ^ 2 / 2`. The right-hand side is a concave quadratic in the second coordinate, so
-- the hypograph is convex; equivalently, check the defining inequality directly on convex
-- combinations.
theorem quadraticOverLinearSupportSet_convex :
    Convex 𝕜 (quadraticOverLinearSupportSet : Set R2) := sorry

end GenericBase

section GenericRepresentation

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [SupSet (WithTopBot 𝕜)]

local notation "R2" => 𝕜 × 𝕜
local notation "qol" => (quadraticOverLinearFunction : R2 → WithTopBot 𝕜)

local instance instHasPairingScalar : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y

/-- Theorem 10.1.4 (4): the quadratic-over-linear example is the support function
`δᵛ(· | quadraticOverLinearSupportSet)` of the convex set
`quadraticOverLinearSupportSet = {(x₁, x₂) | 2 x₁ + x₂² ≤ 0}`. -/
-- Proof sketch: identify the support function of `quadraticOverLinearSupportSet` by maximizing
-- the affine functional `x ↦ ⟪ξ, x⟫` over the parabola boundary `x₁ = -x₂² / 2`. For `ξ₁ > 0`
-- the supremum is attained at `x₂ = ξ₂ / ξ₁` and equals `ξ₂² / (2 ξ₁)`; for `ξ₁ < 0` or
-- `ξ₁ = 0 ≠ ξ₂`, the supremum is `+∞`; at `ξ = 0` it is `0`.
theorem quadraticOverLinearFunction_eq_supportFunction :
    qol =
      (δᵛ(· | quadraticOverLinearSupportSet)) :=
    sorry

end GenericRepresentation

section GenericSupport

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜
local notation "qol" => (quadraticOverLinearFunction : R2 → WithTopBot 𝕜)

/-- Theorem 10.1.4 (1): the quadratic-over-linear example is a convex function on `R²`. -/
-- Proof sketch: combine the support-function identity in part (4) with the chapter fact that the
-- support function of any set is convex.
theorem quadraticOverLinearFunction_isConvex :
    (qol).IsConvex 𝕜 := sorry

end GenericSupport

section RealBridge

local notation "R2" => ℝ × ℝ
local notation "qol" => (quadraticOverLinearFunction : R2 → WithTopBot ℝ)

/-- Theorem 10.1.4 (5), canonical intrinsic form: the quadratic-over-linear example is continuous
on the relative interior `riDom(quadraticOverLinearFunction)` of its effective domain. -/
theorem quadraticOverLinearFunction_continuousOn_riDom :
    ContinuousOn qol riDom(qol) :=
  (quadraticOverLinearFunction_isConvex : (qol).IsConvex ℝ).continuousOn_riDom

/-- Source-facing corollary of Theorem 10.1.4 (5): the quadratic-over-linear example is continuous
on the open half-space `{ξ : R2 | 0 < ξ.1}`. -/
-- Proof sketch: apply Theorem 10.1 on the relatively open convex subset
-- `{ξ : R2 | 0 < ξ.1} ⊆ dom(quadraticOverLinearFunction)` identified in part (2).
theorem quadraticOverLinearFunction_continuousOn_posFirstCoordinate :
    ContinuousOn qol {ξ : R2 | 0 < ξ.1} := by
  have hOpen : IsRelativelyOpen ℝ {ξ : R2 | 0 < ξ.1} :=
    (isOpen_lt continuous_const continuous_fst).isRelativelyOpen
  have hConv : Convex ℝ {ξ : R2 | 0 < ξ.1} := by
    simpa using convex_halfSpace_gt (LinearMap.fst ℝ ℝ ℝ).isLinear (0 : ℝ)
  have hDom : {ξ : R2 | 0 < ξ.1} ⊆ dom(qol) := by
    intro ξ hξ
    rw [quadraticOverLinearFunction_effectiveDomain]
    exact Or.inl hξ
  exact
    Function.IsConvex.continuousOn
      (quadraticOverLinearFunction_isConvex : (qol).IsConvex ℝ) hOpen hConv hDom

/-- Theorem 10.1.4 (6): at the relative-boundary point `(0, 0)`, the quadratic-over-linear
example is lower semicontinuous. -/
-- Proof sketch: all function values are nonnegative and the value at the origin is `0`, so every
-- liminf at `0` is at least `0 = quadraticOverLinearFunction 0`. Equivalently, use the
-- support-function representation from part (4) together with lower semicontinuity of support
-- functions.
theorem quadraticOverLinearFunction_lowerSemicontinuousAt_zero :
    LowerSemicontinuousAt qol 0 := sorry

/-- Theorem 10.1.4 (7): along the parabolic approach `ξ₁ = ξ₂² / (2 α)` with `α > 0`, the value
of the quadratic-over-linear example converges to `α` at the origin. -/
-- Proof sketch: along `t ↦ (t² / (2 α), t)` with `t ≠ 0`, for
-- `α > 0` the positive first-coordinate branch applies and simplifies identically to the
-- constant value `α`.
theorem quadraticOverLinearFunction_tendsto_parabolic_path
    {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun t : ℝ ↦ qol (t ^ 2 / (2 * α), t))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (α : WithTopBot ℝ)) := sorry

/-- Theorem 10.1.4 (8): along every ray `t ↦ t x` with `x₁ > 0`, the quadratic-over-linear
example tends to `0` as `t ↓ 0`. -/
-- Proof sketch: if `x₁ > 0`, then for every `t > 0` the point `t • x` stays in the branch
-- `ξ₁ > 0`, where the formula simplifies to
-- `quadraticOverLinearFunction (t • x) = t * (x₂² / (2 x₁))`. This tends to `0` as `t ↓ 0`.
theorem quadraticOverLinearFunction_tendsto_radial_to_zero
    {x : R2} (hx : 0 < x.1) :
    Tendsto (fun t : ℝ ↦ qol (t • x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (0 : WithTopBot ℝ)) := sorry

/-- Theorem 10.1.4 (9): the quadratic-over-linear example is not continuous at `(0, 0)`; the
limit depends on the path of approach. -/
-- Proof sketch: parts (7) and (8) give two approaches to the origin with different limits: `α`
-- along the parabola for any chosen `α > 0`, and `0` along every ray from a point with positive
-- first coordinate. Therefore the ordinary limit at `0` cannot exist, so the function is not
-- continuous there.
theorem quadraticOverLinearFunction_not_continuousAt_zero :
    ¬ ContinuousAt qol 0 := sorry

end RealBridge

/-! ### Definition_10_1_5 (from Chap02) -/
section

open scoped Topology

variable {V : Type*} {P : Type*}

/-
Source/core/bridge triage:
- `source-facing`: Definition 10.1.5 introduces the local property of a subset of an affine
  space being covered near each of its points by finitely many simplices lying inside the set.
- `core/canonical`: subsets `s : Set P`, relative neighborhoods `𝓝[s] x`, finite simplex families
  represented canonically as finite sets
  `T : Set (Σ m : ℕ, Affine.Simplex k P m)` with witness `T.Finite`; each simplex carrier is
  `t.2.closedInterior`.
- `bridge/view`: `Finset` and open-neighborhood formulations are bridge API.
- Primitive data vs derived API: the primitive data are the finite simplex family and the
  relative-neighborhood witness that the simplex union covers `s` near each point.
- Domain-style sampling: the relevant owner-level declarations are
  `Affine.Simplex.closedInterior`, `𝓝[s] x`, and `Set.exists_finite_iff_finset`.
-/

/-- Definition 10.1.5: a subset of an affine space is locally simplicial if each point admits a
relative neighborhood in the set covered by finitely many simplices lying inside the set. The
owner-level finite-family witness is the intrinsic finite-set layer `Set` + `Finite`. -/
def Set.IsLocallySimplicial (k : Type*) [Ring k] [PartialOrder k]
    [AddCommGroup V] [Module k V] [AddTorsor V P] [TopologicalSpace P] (s : Set P) : Prop :=
  ∀ x ∈ s, ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
    (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
      (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x

variable {k : Type*} [Ring k] [PartialOrder k] [AddCommGroup V] [Module k V] [AddTorsor V P]
  [TopologicalSpace P]

/-- Relative-neighborhood + finite-`Set` formulation of local simpliciality. -/
theorem Set.isLocallySimplicial_iff_exists {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x :=
  Iff.rfl

/-- Deprecated alias for `Set.isLocallySimplicial_iff_exists`. -/
@[deprecated Set.isLocallySimplicial_iff_exists (since := "2026-05-17")]
theorem Set.isLocallySimplicial_iff_exists_finite {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x :=
  Set.isLocallySimplicial_iff_exists

/-- `Finset` bridge formulation of `Set.IsLocallySimplicial`. -/
theorem Set.isLocallySimplicial_iff_exists_finset {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ T : Finset (Σ m : ℕ, Affine.Simplex k P m),
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x := by
  simp [Set.IsLocallySimplicial, Set.exists_finite_iff_finset]

/-- Open-set + finite-`Finset` bridge formulation of `Set.IsLocallySimplicial` using
relative-neighborhood witnesses. -/
theorem Set.isLocallySimplicial_iff_exists_open_finset {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
        ∃ T : Finset (Σ m : ℕ, Affine.Simplex k P m),
          (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
            u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior := by
  constructor
  · intro hs x hx
    rcases (Set.isLocallySimplicial_iff_exists_finset.1 hs) x hx with ⟨T, hTsubset, hcov⟩
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hcov with ⟨u, hu_nhds, hu_sub⟩
    rcases mem_nhds_iff.1 hu_nhds with ⟨v, hv_sub, hv_open, hxv⟩
    refine ⟨v, hv_open, hxv, T, hTsubset, ?_⟩
    intro y hy
    exact hu_sub ⟨hv_sub hy.1, hy.2⟩
  · intro hs
    refine (Set.isLocallySimplicial_iff_exists_finset).2 ?_
    intro x hx
    rcases hs x hx with ⟨u, hu_open, hxu, T, hTsubset, hu_sub⟩
    refine ⟨T, hTsubset, ?_⟩
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨u, hu_open.mem_nhds hxu, hu_sub⟩

/-- Open-set + finite-`Set` bridge formulation of local simpliciality. -/
theorem Set.isLocallySimplicial_iff_exists_open {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
        ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
          (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
            u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior := by
  constructor
  · intro hs x hx
    rcases (Set.isLocallySimplicial_iff_exists_open_finset.1 hs) x hx with
      ⟨u, hu_open, hxu, T, hTsubset, hu_sub⟩
    refine ⟨u, hu_open, hxu, (T : Set (Σ m : ℕ, Affine.Simplex k P m)), T.finite_toSet, ?_, ?_⟩
    · intro t ht
      exact hTsubset t (Finset.mem_coe.1 ht)
    · simpa using hu_sub
  · intro hs
    refine (Set.isLocallySimplicial_iff_exists_open_finset).2 ?_
    intro x hx
    rcases hs x hx with ⟨u, hu_open, hxu, T, hTfin, hTsubset, hu_sub⟩
    refine ⟨u, hu_open, hxu, hTfin.toFinset, ?_, ?_⟩
    · intro t ht
      exact hTsubset t (hTfin.mem_toFinset.1 ht)
    · simpa [hTfin.coe_toFinset] using hu_sub

/-- Deprecated alias for `Set.isLocallySimplicial_iff_exists_open`. -/
@[deprecated Set.isLocallySimplicial_iff_exists_open (since := "2026-05-17")]
theorem Set.isLocallySimplicial_iff_exists_open_finite {s : Set P} :
    s.IsLocallySimplicial k ↔
      ∀ x ∈ s, ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
        ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
          (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
            u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior :=
  Set.isLocallySimplicial_iff_exists_open

namespace Set.IsLocallySimplicial

/-- A locally simplicial set admits a finite-family simplicial description in the relative
neighborhood filter near each point. -/
theorem exists_finset {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ T : Finset (Σ m : ℕ, Affine.Simplex k P m),
      (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
        (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x :=
  (Set.isLocallySimplicial_iff_exists_finset.1 hs) x hx

/-- A locally simplicial set admits a finite-`Set` simplicial description in the relative
neighborhood filter near each point. -/
theorem exists_set {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
      (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
        (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x :=
  hs x hx

/-- Deprecated alias for `Set.IsLocallySimplicial.exists_set`. -/
@[deprecated Set.IsLocallySimplicial.exists_set (since := "2026-05-17")]
theorem exists_finite {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
      (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
        (⋃ t ∈ T, t.2.closedInterior) ∈ 𝓝[s] x :=
  exists_set hs hx

/-- A locally simplicial set admits an open-neighborhood finite-family simplicial description. -/
theorem exists_open_finset {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
      ∃ T : Finset (Σ m : ℕ, Affine.Simplex k P m),
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior := by
  exact (Set.isLocallySimplicial_iff_exists_open_finset.1 hs) x hx

/-- A locally simplicial set admits an open-neighborhood finite-`Set` simplicial description. -/
theorem exists_open {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
      ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior := by
  exact (Set.isLocallySimplicial_iff_exists_open.1 hs) x hx

/-- Deprecated alias for `Set.IsLocallySimplicial.exists_open`. -/
@[deprecated Set.IsLocallySimplicial.exists_open (since := "2026-05-17")]
theorem exists_open_finite {s : Set P} (hs : s.IsLocallySimplicial k) {x : P} (hx : x ∈ s) :
    ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
      ∃ T : Set (Σ m : ℕ, Affine.Simplex k P m), T.Finite ∧
        (∀ t ∈ T, t.2.closedInterior ⊆ s) ∧
          u ∩ s ⊆ ⋃ t ∈ T, t.2.closedInterior := by
  exact exists_open hs hx

end Set.IsLocallySimplicial

end

/-! ### Theorem_10_1_6 (from Chap02) -/
section

variable {𝕜 : Type*} {V : Type*} {P : Type*}
variable [DivisionRing 𝕜]
variable [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
variable {m : ℕ}

namespace Affine.Simplex

/-
Source/core/bridge triage:
- `source-facing`: Theorem 10.1.6 says that if `x ∈ s.closedInterior`, then every
  `y ∈ s.closedInterior` lies in a same-dimensional simplex contained in `s` whose vertices are
  `x` together with exactly `m` of the `m + 1` original vertices of `s`.
- `core/canonical`: the owner abstraction is mathlib's bundled simplex `Affine.Simplex 𝕜 P m`,
  with carrier set `Affine.Simplex.closedInterior`; public theorem surfaces are stated in terms of
  an existential pointed subsimplex `t : Affine.Simplex 𝕜 P m`.
- `bridge/view`: under `[NeZero m]`, the codimension-one piece is packaged as
  `Affine.Simplex.faceOpposite`, with `s.range_faceOpposite_points` providing the thin bridge to
  the primitive omitted-vertex set.
- Primitive data vs derived API: the public source-facing output is the omitted index
  `i : Fin (m + 1)` together with a same-dimensional simplex `t` whose vertex set is
  `insert x (s.points '' ({i}ᶜ))`; `replaceVertex` is an internal constructor used to witness this
  existential output. The omitted-face owner `s.faceOpposite i` is bridge-level data.
- Domain-style sampling used here: `Affine.Simplex.closedInterior`,
  `Affine.Simplex.faceOpposite`, `Affine.Simplex.range_faceOpposite_points`, and
  `AffineIndependent.affineIndependent_update_of_notMem_affineSpan`.
- Layer target: this item stays source-facing, but its public API is attached directly to the
  canonical owner `Affine.Simplex`; `replaceVertex` is kept as implementation scaffolding at the
  primitive omitted-vertex layer, and `faceOpposite` remains a thin bridge/view companion.
- Ambient refinement: the source theorem is real-simplex geometry, but its barycentric
  comparison/minimum-ratio argument is expected to live at an ordered-field layer rather than a
  normed or finite-dimensional real model. We keep the public statements at
  `[DivisionRing 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]` (not the stronger concrete `ℝ`
  specialization).
-/

section ReplaceVertex

/-- The simplex obtained from `s` by replacing the vertex indexed by `i` with `x`. The hypothesis
states that `x` lies outside the affine span of the omitted-vertex set
`s.points '' ({i}ᶜ)`. -/
private def replaceVertex (s : Simplex 𝕜 P m) (i : Fin (m + 1)) (x : P)
    (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) : Simplex 𝕜 P m where
  points := Function.update s.points i x
  independent :=
    s.independent.affineIndependent_update_of_notMem_affineSpan <| by
      simpa using hxi

@[simp] private theorem replaceVertex_points_self (s : Simplex 𝕜 P m) (i : Fin (m + 1)) (x : P)
    (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) :
    (s.replaceVertex i x hxi).points i = x := by
  simp [replaceVertex, Function.update]

@[simp] private theorem replaceVertex_points_of_ne (s : Simplex 𝕜 P m) {i j : Fin (m + 1)} (x : P)
    (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) (hji : j ≠ i) :
    (s.replaceVertex i x hxi).points j = s.points j := by
  simp [replaceVertex, Function.update, hji]

/-- The vertices of `s.replaceVertex i x hxi` are exactly `x` together with the vertices of the
simplex `s` other than `s.points i`, at the primitive omitted-vertex-set layer. -/
private theorem range_replaceVertex_points (s : Simplex 𝕜 P m) (i : Fin (m + 1)) (x : P)
    (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) :
    Set.range (s.replaceVertex i x hxi).points =
      insert x (s.points '' ({i}ᶜ)) := by
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hji : j = i
    · subst hji
      simp
    · right
      refine ⟨j, ?_, ?_⟩
      · simpa using hji
      · simp [replaceVertex, Function.update, hji]
  · intro hp
    rcases hp with rfl | hp
    · exact ⟨i, by simp [replaceVertex, Function.update]⟩
    · rcases hp with ⟨j, hj, rfl⟩
      have hji : j ≠ i := by simpa using hj
      refine ⟨j, ?_⟩
      simp [replaceVertex, Function.update, hji]

section FaceOppositeBridge

variable [NeZero m]

/-- Under `m ≠ 0`, the primitive omitted-vertex set agrees with the opposite-face vertex set. -/
private theorem range_replaceVertex_points_faceOpposite (s : Simplex 𝕜 P m) (i : Fin (m + 1)) (x : P)
    (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) :
    Set.range (s.replaceVertex i x hxi).points =
      insert x (Set.range (s.faceOpposite i).points) := by
  simpa [s.range_faceOpposite_points] using s.range_replaceVertex_points i x hxi

end FaceOppositeBridge

end ReplaceVertex

private theorem affineCombination_replaceVertex_transfer
    (s : Simplex 𝕜 P m) (i : Fin (m + 1)) (x : P) (α β : Fin (m + 1) → 𝕜)
    (hαsum : ∑ j, α j = 1) (hβsum : ∑ j, β j = 1)
    (hxEq : Finset.univ.affineCombination 𝕜 s.points α = x) (c : 𝕜)
    (hci : c * α i = β i) :
    Finset.univ.affineCombination 𝕜 (Function.update s.points i x)
        (Function.update (fun j => β j - c * α j) i c) =
      Finset.univ.affineCombination 𝕜 s.points β := by
  have hUpdateSum : ∑ j, (Function.update (fun j => β j - c * α j) i c) j = 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [Finset.sdiff_singleton_eq_erase]
    rw [hβsum, hαsum, ← hci]
    noncomm_ring
  apply (vsub_left_cancel (p := s.points i))
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
      (s := Finset.univ) (w := Function.update (fun j => β j - c * α j) i c)
      (p := Function.update s.points i x) hUpdateSum (b := s.points i)]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
      (s := Finset.univ) (w := β) (p := s.points) hβsum (b := s.points i)]
  simp only [vadd_vsub]
  have hxv : x -ᵥ s.points i = ∑ j, α j • (s.points j -ᵥ s.points i) := by
    calc
      x -ᵥ s.points i = (Finset.univ.affineCombination 𝕜 s.points α) -ᵥ s.points i := by simp [hxEq]
      _ = (Finset.univ.weightedVSubOfPoint s.points (s.points i)) α := by
        rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
          (s := Finset.univ) (w := α) (p := s.points) hαsum (b := s.points i)]
        simp
      _ = ∑ j, α j • (s.points j -ᵥ s.points i) := by
        simp [Finset.weightedVSubOfPoint_apply]
  rw [Finset.weightedVSubOfPoint_apply, Finset.weightedVSubOfPoint_apply]
  have hsplitL := Finset.sum_eq_sum_diff_singleton_add (s := Finset.univ)
    (i := i) (h := Finset.mem_univ i)
    (f := fun j => (Function.update (fun j => β j - c * α j) i c) j •
      (Function.update s.points i x j -ᵥ s.points i))
  have hsplitR := Finset.sum_eq_sum_diff_singleton_add (s := Finset.univ)
    (i := i) (h := Finset.mem_univ i) (f := fun j => β j • (s.points j -ᵥ s.points i))
  rw [hsplitL, hsplitR]
  simp only [Function.update_self, vsub_self, smul_zero, add_zero, add_right_inj]
  have hxv' : c • (x -ᵥ s.points i) = ∑ j, (c * α j) • (s.points j -ᵥ s.points i) := by
    rw [hxv, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [smul_smul]
  rw [hxv']
  have hsplitC := Finset.sum_eq_sum_diff_singleton_add (s := Finset.univ)
    (i := i) (h := Finset.mem_univ i) (f := fun j => (c * α j) • (s.points j -ᵥ s.points i))
  rw [hsplitC]
  simp only [vsub_self, smul_zero, add_zero]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hji : j ≠ i := by
    exact fun hji => (Finset.mem_sdiff.mp hj).2 (by simpa [hji])
  simp [Function.update_of_ne hji, hji, ← add_smul, sub_add_cancel]

section Ordered

variable [LinearOrder 𝕜] [IsOrderedRing 𝕜]

private theorem closedInterior_replaceVertex_subset_of_mem_closedInterior
    (s : Simplex 𝕜 P m) (x : P) (hx : x ∈ s.closedInterior)
    (i : Fin (m + 1)) (hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ))) :
    (s.replaceVertex i x hxi).closedInterior ⊆ s.closedInterior := by
  rcases hx with ⟨α, hαsum, hαIcc, hxEq⟩
  intro z hz
  rcases hz with ⟨lam, hLamSum, hLamIcc, hzEq⟩
  let c : 𝕜 := lam i
  let β : Fin (m + 1) → 𝕜 := Function.update (fun j => lam j + c * α j) i (c * α i)
  have hβdef : Function.update (fun j => β j - c * α j) i c = lam := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp [β, c]
    · simp [β, c, hji, sub_add_cancel]
  have hβsum : ∑ j, β j = 1 := by
    dsimp [β]
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sdiff_singleton_eq_erase]
    rw [hLamSum, hαsum]
    noncomm_ring
  have hβIcc : ∀ j, β j ∈ Set.Icc (0 : 𝕜) 1 := by
    intro j
    by_cases hji : j = i
    · subst hji
      constructor
      · simp [β, c, mul_nonneg, (hLamIcc j).1, (hαIcc j).1]
      · have hmul_le : c * α j ≤ (1 : 𝕜) * 1 := by
          refine mul_le_mul (hLamIcc j).2 (hαIcc j).2 (hαIcc j).1 ?_
          simpa using (show (0 : 𝕜) ≤ (1 : 𝕜) from zero_le_one)
        simpa [β, c] using hmul_le
    · constructor
      · have hmul_nonneg : 0 ≤ c * α j := mul_nonneg (hLamIcc i).1 (hαIcc j).1
        have hnonneg : 0 ≤ lam j + c * α j := add_nonneg (hLamIcc j).1 hmul_nonneg
        simpa [β, c, hji] using hnonneg
      · have hmul_le_c : c * α j ≤ c := by
          calc
            c * α j ≤ c * 1 := mul_le_mul_of_nonneg_left (hαIcc j).2 (hLamIcc i).1
            _ = c := by simp
        have hlamj_le_sumErase : lam j ≤ Finset.sum (Finset.univ.erase i) lam := by
          refine Finset.single_le_sum ?_ ?_
          · intro k hk
            exact (hLamIcc k).1
          · exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
        have hsumErase_plus_c : Finset.sum (Finset.univ.erase i) lam + c = 1 := by
          calc
            Finset.sum (Finset.univ.erase i) lam + c = ∑ k, lam k := by
              simpa [c] using (Finset.sum_erase_add (s := Finset.univ) (f := lam) (h := Finset.mem_univ i))
            _ = 1 := hLamSum
        have hlamj_plus_c_le_one : lam j + c ≤ (1 : 𝕜) := by
          calc
            lam j + c = c + lam j := by simp [add_comm]
            _ ≤ c + Finset.sum (Finset.univ.erase i) lam := add_le_add_right hlamj_le_sumErase c
            _ = 1 := by simpa [add_comm] using hsumErase_plus_c
        have hβj_le_one : lam j + c * α j ≤ (1 : 𝕜) := by
          calc
            lam j + c * α j = c * α j + lam j := by simp [add_comm]
            _ ≤ c + lam j := add_le_add_left hmul_le_c (lam j)
            _ = lam j + c := by simp [add_comm]
            _ ≤ 1 := hlamj_plus_c_le_one
        simpa [β, c, hji] using hβj_le_one
  have hzEq' : Finset.univ.affineCombination 𝕜 s.points β = z := by
    calc
      Finset.univ.affineCombination 𝕜 s.points β
          = Finset.univ.affineCombination 𝕜 (Function.update s.points i x) lam := by
            symm
            have hci' : c * α i = β i := by simp [β, c]
            simpa [hβdef] using
              s.affineCombination_replaceVertex_transfer i x α β hαsum hβsum hxEq c hci'
      _ = z := by
            simpa [replaceVertex] using hzEq
  exact ⟨β, hβsum, hβIcc, hzEq'⟩

-- Proof sketch: write `y` in barycentric coordinates relative to `s`. At least one coordinate can
-- be chosen as the omitted vertex while keeping the remaining coefficients nonnegative after
-- transferring the missing mass to the new vertex `x`; this yields a same-dimensional simplex
-- contained in `s` whose vertices are `x` together with the complementary original vertices
-- `s.points '' ({i}ᶜ)`.
-- Internal bridge: this dependent formulation is used only to construct the public
-- non-dependent existential theorem surface below.
private theorem exists_replaceVertex_of_mem_closedInterior_aux (s : Simplex 𝕜 P m) (x y : P)
    (hx : x ∈ s.closedInterior) (hy : y ∈ s.closedInterior) :
    ∃ i : Fin (m + 1),
      ∃ hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ)),
      (s.replaceVertex i x hxi).closedInterior ⊆ s.closedInterior ∧
        y ∈ (s.replaceVertex i x hxi).closedInterior := by
  rcases hx with ⟨α, hαsum, hαIcc, hxEq⟩
  rcases hy with ⟨β, hβsum, hβIcc, hyEq⟩
  let nz : Finset (Fin (m + 1)) := Finset.univ.filter (fun j => α j ≠ 0)
  have hnz : nz.Nonempty := by
    have hsum_ne : (∑ j, α j) ≠ 0 := by simpa [hαsum] using (one_ne_zero : (1 : 𝕜) ≠ 0)
    rcases Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := α) hsum_ne with ⟨j, -, hj⟩
    exact ⟨j, by simpa [nz, hj]⟩
  have hαsum_nz : Finset.sum nz α = 1 := by
    simpa [nz, hαsum] using (Finset.sum_filter_ne_zero (s := Finset.univ) (f := α))
  have hβsum_nz_le_one : Finset.sum nz β ≤ (1 : 𝕜) := by
    have hcomp_nonneg : 0 ≤ Finset.sum (Finset.univ.filter (fun j => ¬ α j ≠ 0)) β := by
      refine Finset.sum_nonneg ?_
      intro j hj
      exact (hβIcc j).1
    have hsplit :
        Finset.sum nz β + Finset.sum (Finset.univ.filter (fun j => ¬ α j ≠ 0)) β = ∑ j, β j := by
      simpa [nz] using (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun j => α j ≠ 0) (f := β))
    calc
      Finset.sum nz β ≤ Finset.sum nz β + Finset.sum (Finset.univ.filter (fun j => ¬ α j ≠ 0)) β :=
        le_add_of_nonneg_right hcomp_nonneg
      _ = ∑ j, β j := hsplit
      _ = 1 := hβsum
  have hβsum_nz_le_hαsum_nz : Finset.sum nz β ≤ Finset.sum nz α := by
    simpa [hαsum_nz] using hβsum_nz_le_one
  obtain ⟨k, hk_nz, hβk_le_αk⟩ :=
    Finset.exists_le_of_sum_le (s := nz) (f := β) (g := α) hnz hβsum_nz_le_hαsum_nz
  obtain ⟨i, hi_nz, hmin⟩ := Finset.exists_min_image nz (fun j => β j / α j) hnz
  have hαi_ne : α i ≠ 0 := (Finset.mem_filter.mp hi_nz).2
  have hαk_ne : α k ≠ 0 := (Finset.mem_filter.mp hk_nz).2
  have hαi_pos : 0 < α i := lt_of_le_of_ne (hαIcc i).1 (by simpa [eq_comm] using hαi_ne)
  have hαk_pos : 0 < α k := lt_of_le_of_ne (hαIcc k).1 (by simpa [eq_comm] using hαk_ne)
  have hratio_k_le_one : β k / α k ≤ (1 : 𝕜) := div_le_one_of_le₀ hβk_le_αk (hαIcc k).1
  have hc_le_one : β i / α i ≤ (1 : 𝕜) := le_trans (hmin k hk_nz) hratio_k_le_one
  have hxi : x ∉ affineSpan 𝕜 (s.points '' ({i}ᶜ)) := by
    intro hxspan
    have hm : Finset.univ.affineCombination 𝕜 s.points α ∈ affineSpan 𝕜 (s.points '' ({i}ᶜ)) := by
      simpa [hxEq] using hxspan
    have hαi_zero : α i = 0 := s.independent.eq_zero_of_affineCombination_mem_affineSpan
      (fs := Finset.univ) (w := α) (hw := by simpa using hαsum)
      (s := ({i}ᶜ : Set (Fin (m + 1)))) hm (hifs := by simp) (his := by simp)
    exact hαi_ne hαi_zero
  have hsub :
      (s.replaceVertex i x hxi).closedInterior ⊆ s.closedInterior :=
    s.closedInterior_replaceVertex_subset_of_mem_closedInterior x ⟨α, hαsum, hαIcc, hxEq⟩ i hxi
  let c : 𝕜 := β i / α i
  let lam : Fin (m + 1) → 𝕜 := Function.update (fun j => β j - c * α j) i c
  have hci : c * α i = β i := by
    dsimp [c]
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hαi_ne, mul_one]
  have hLamSum : ∑ j, lam j = 1 := by
    dsimp [lam]
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [Finset.sdiff_singleton_eq_erase]
    rw [hβsum, hαsum, ← hci]
    noncomm_ring
  have hLamIcc : ∀ j, lam j ∈ Set.Icc (0 : 𝕜) 1 := by
    intro j
    by_cases hji : j = i
    ·
      constructor
      · simpa [lam, c, hji] using (div_nonneg (hβIcc j).1 (hαIcc j).1)
      · simpa [lam, c, hji] using hc_le_one
    · constructor
      · by_cases hαj_ne : α j ≠ 0
        · have hj_nz : j ∈ nz := by simp [nz, hαj_ne]
          have hαj_pos : 0 < α j := lt_of_le_of_ne (hαIcc j).1 (by simpa [eq_comm] using hαj_ne)
          have hratio : c ≤ β j / α j := by simpa [c] using hmin j hj_nz
          have hmul_le : c * α j ≤ β j := (le_div_iff₀ hαj_pos).1 hratio
          have hnonneg : 0 ≤ β j - c * α j := (sub_nonneg).2 hmul_le
          simpa [lam, c, hji] using hnonneg
        · have hαj_zero : α j = 0 := by simpa using hαj_ne
          have hnonneg : 0 ≤ β j := (hβIcc j).1
          simpa [lam, c, hji, hαj_zero] using hnonneg
      · have hmul_nonneg : 0 ≤ c * α j := by
          exact mul_nonneg (div_nonneg (hβIcc i).1 (hαIcc i).1) (hαIcc j).1
        have hle : β j - c * α j ≤ β j := sub_le_self _ hmul_nonneg
        have hβj_le_one : β j ≤ (1 : 𝕜) := (hβIcc j).2
        exact (le_trans (by simpa [lam, c, hji] using hle) hβj_le_one)
  have hyi : y ∈ (s.replaceVertex i x hxi).closedInterior := by
    refine ⟨lam, hLamSum, hLamIcc, ?_⟩
    calc
      Finset.univ.affineCombination 𝕜 (s.replaceVertex i x hxi).points lam
          = Finset.univ.affineCombination 𝕜 (Function.update s.points i x) lam := by
            simp [replaceVertex]
      _ = Finset.univ.affineCombination 𝕜 s.points β := by
            simpa [lam] using
              s.affineCombination_replaceVertex_transfer i x α β hαsum hβsum hxEq c hci
      _ = y := hyEq
  exact ⟨i, hxi, hsub, hyi⟩

/-- Theorem 10.1.6, canonical source-facing owner form: `y` lies in a same-dimensional simplex
contained in `s` whose vertices are `x` together with exactly `m` of the `m + 1` vertices of
`s`. -/
theorem exists_pointedSubsimplex_of_mem_closedInterior (s : Simplex 𝕜 P m) (x y : P)
    (hx : x ∈ s.closedInterior) (hy : y ∈ s.closedInterior) :
    ∃ i : Fin (m + 1), ∃ t : Simplex 𝕜 P m,
      Set.range t.points = insert x (s.points '' ({i}ᶜ)) ∧
        t.closedInterior ⊆ s.closedInterior ∧ y ∈ t.closedInterior := by
  rcases s.exists_replaceVertex_of_mem_closedInterior_aux x y hx hy with ⟨i, hxi, hsub, hyi⟩
  refine ⟨i, s.replaceVertex i x hxi, ?_, hsub, hyi⟩
  exact s.range_replaceVertex_points i x hxi

section FaceOppositeBridge

variable [NeZero m]

/-- Face-opposite bridge form of Theorem 10.1.6 on the same non-dependent theorem surface. -/
theorem exists_pointedSubsimplex_of_mem_closedInterior_faceOpposite
    (s : Simplex 𝕜 P m) (x y : P) (hx : x ∈ s.closedInterior) (hy : y ∈ s.closedInterior) :
    ∃ i : Fin (m + 1), ∃ t : Simplex 𝕜 P m,
      Set.range t.points = insert x (Set.range (s.faceOpposite i).points) ∧
        t.closedInterior ⊆ s.closedInterior ∧ y ∈ t.closedInterior := by
  rcases s.exists_pointedSubsimplex_of_mem_closedInterior x y hx hy with ⟨i, t, hrange, hsub, hyi⟩
  refine ⟨i, t, ?_, hsub, hyi⟩
  simpa [s.range_faceOpposite_points] using hrange

end FaceOppositeBridge

end Ordered

end Affine.Simplex

end
