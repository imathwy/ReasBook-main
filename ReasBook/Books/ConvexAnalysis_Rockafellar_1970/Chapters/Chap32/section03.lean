import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_32_3_1 (from Chap06) -/
open scoped Rockafellar

universe u v

section Core

variable {𝕜 : Type v} [Field 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [HasLinearPairing E E 𝕜]
variable {α : Type*} [AddCommMonoid α] [LinearOrder α]
  [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable {f : E → WithBotTop α} {C : Set E}
variable [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
variable (hf : f.IsConvex 𝕜) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
variable (hC_dom : C ⊆ dom(f))

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 32.3.1 says that, when `C` contains no affine lines, an attained
  supremum of a convex function on `C` is attained at an extreme point of `C`.
- `core/canonical`: this file stays on the same scalar/pairing-generic Chapter 32 owner layer as
  `exists_mem_isMaxOn_extremePoints_linealAnnihilatorSlice_of_exists_mem_isMaxOn`:
  `f.IsConvex 𝕜`,
  `dom(f)`, `Set.lineality 𝕜 C`, `Set.linealAnnihilator`,
  `C.extremePoints 𝕜`, `affineHalfLine`, and `IsMaxOn`.
- `bridge/view`: the source phrase “contains no affine lines” is already owned upstream by
  `¬ Set.HasAffineLine 𝕜 C`, and Theorem 8.4.8 bridges that owner to the canonical lineality
  condition `Set.lineality 𝕜 C = 0`.

Domain-style sampling used here:
- `exists_mem_isMaxOn_extremePoints_linealAnnihilatorSlice_of_exists_mem_isMaxOn` from
  Theorem 32.3;
- `Set.linealAnnihilator` and `linAnn[𝕜](C)` from Theorem 32.3;
- `Set.lineality_eq_zero_iff_not_hasAffineLine`;
- `Set.extremePoints`;
- `IsMaxOn`.

Primitive data vs derived API:
- primitive inputs: the convex function `f`, the feasible set `C`, the closedness/convexity and
  domain hypotheses inherited from Theorem 32.3, and explicit maximizer data `x ∈ C` with
  `IsMaxOn f C x`;
- derived API: existence of a maximizer lying in `C.extremePoints 𝕜`, obtained in Theorem 32.3
  by reducing first to `(linAnn[𝕜](C)).extremePoints 𝕜`;
- local derived bridge for invoking Theorem 32.3: `IsMaxOn.on_subset` and `IsMaxOn.bddAbove`
  produce the affine-half-line boundedness hypothesis from any maximizer on `C`;
- bridge/view: `Set.lineality 𝕜 C = 0` is retained only as the canonical bridge from the
  source-facing owner `¬ Set.HasAffineLine 𝕜 C`.

Layer target: `source-facing` for the main corollary, with the lineality-zero statement retained
as a thin core bridge.
-/

-- Proof sketch: apply Theorem 32.3 (2) to transfer an attained maximum from `C` to the extreme
-- points of `linAnn[𝕜](C) = C ∩ Lᗮₚ`, where
-- `L = Submodule.span 𝕜 (lin[𝕜](C))`. The half-line boundedness hypothesis needed there is
-- supplied by `hxmax` through `IsMaxOn.on_subset` and `IsMaxOn.bddAbove`. When
-- `Set.lineality 𝕜 C = 0`, that slice identifies with `C`, so the resulting maximizing point is
-- an extreme point of `C`.
include hf hC_closed hC_convex hC_dom
/-- Core bridge companion for Corollary 32.3.1: under the hypotheses of Theorem 32.3, if
`Set.lineality 𝕜 C = 0` and `f` attains a maximum on `C`, then `f` attains its
supremum at an extreme point of `C`. The source-facing no-line corollary below keeps the textbook
existential packaging and is obtained from this bridge via
`Set.lineality_eq_zero_iff_not_hasAffineLine`. -/
theorem exists_mem_extremePoints_isMaxOn_of_exists_mem_isMaxOn_of_lineality_eq_zero
    (hC_lineality : Set.lineality 𝕜 C = 0) (hmax : ∃ x ∈ C, IsMaxOn f C x) :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  rcases hmax with ⟨x, hxC, hxmax⟩
  have hhalfLine_bddAbove :
      ∀ ⦃z : E⦄ ⦃r : Module.Ray 𝕜 E⦄,
        affineHalfLine z r ⊆ C → BddAbove (f '' affineHalfLine z r) := by
    intro z r hzC
    exact (hxmax.on_subset hzC).bddAbove
  have hmax' : ∃ z ∈ C, IsMaxOn f C z := ⟨x, hxC, hxmax⟩
  obtain ⟨y, hyext, hymax⟩ :=
    exists_mem_isMaxOn_extremePoints_linealAnnihilatorSlice_of_exists_mem_isMaxOn
      hf hC_closed hC_convex hC_dom hhalfLine_bddAbove hmax'
  have hlinAnn_univ : linAnn[𝕜](C) = (Set.univ : Set E) := by
    let A : AffineSubspace 𝕜 E := affineSpan 𝕜 (lin[𝕜](C))
    have h0lineal : (0 : E) ∈ lin[𝕜](C) := by
      rw [Set.mem_lineal_iff]
      constructor <;>
        (rw [Set.mem_recessionCone_iff]; intro z hz a ha; simpa)
    have h0A : (0 : E) ∈ A :=
      (subset_affineSpan 𝕜 (lin[𝕜](C))) h0lineal
    have hAne : A ≠ ⊥ := by
      intro hbot
      have : (0 : E) ∉ (A : Set E) := by simp [hbot]
      exact this h0A
    have hfin : Module.finrank 𝕜 A.direction = 0 := by
      rw [show Set.lineality 𝕜 C = A.affineDim by rfl,
        AffineSubspace.affineDim, if_neg hAne] at hC_lineality
      exact_mod_cast hC_lineality
    have hdir : A.direction = ⊥ := Submodule.finrank_eq_zero.mp hfin
    have hlineal_sub : lin[𝕜](C) ⊆ ({0} : Set E) := by
      intro z hz
      have hzA : z ∈ A := (subset_affineSpan 𝕜 (lin[𝕜](C))) hz
      have hzdir : z ∈ A.direction := by
        simpa using A.vsub_mem_direction hzA h0A
      have hz0 : z = 0 := by simpa [hdir] using hzdir
      simp [hz0]
    have hspan_le : Submodule.span 𝕜 (lin[𝕜](C)) ≤ (⊥ : Submodule 𝕜 E) := by
      refine Submodule.span_le.mpr ?_
      intro z hz
      have hz0 : z = 0 := by
        exact Set.mem_singleton_iff.mp (hlineal_sub hz)
      simp [hz0]
    have hspan_eq : Submodule.span 𝕜 (lin[𝕜](C)) = (⊥ : Submodule 𝕜 E) :=
      le_antisymm hspan_le bot_le
    change (((Submodule.span 𝕜 (lin[𝕜](C)))ᗮₚ : Submodule 𝕜 E) : Set E) = Set.univ
    rw [hspan_eq]
    ext z
    constructor
    · intro hz
      trivial
    · intro hz
      exact (Submodule.mem_pairingOrthogonal_iff (K := (⊥ : Submodule 𝕜 E)) (y := z)).2 <|
        by
          intro w hw
          have hw0 : w = 0 := by simpa using hw
          simp [hw0]
  have hyext' : y ∈ C.extremePoints 𝕜 := by
    simpa [hlinAnn_univ, Set.inter_univ] using hyext
  exact ⟨y, hyext', hymax⟩
omit hf hC_closed hC_convex hC_dom

end Core

section SourceFacing

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [HasLinearPairing E E 𝕜]
variable {C : Set E}
variable [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
variable {α : Type*} [AddCommMonoid α] [LinearOrder α]
  [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable {f : E → WithBotTop α}
variable (hf : f.IsConvex 𝕜) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
variable (hC_dom : C ⊆ dom(f))

-- Proof sketch: convert the source-facing owner hypothesis `¬ Set.HasAffineLine 𝕜 C` into the
-- canonical lineality condition `Set.lineality 𝕜 C = 0` via Theorem 8.4.8, then apply the
-- owner-form theorem from `Core`.
include hf hC_closed hC_convex hC_dom
/-- Corollary 32.3.1, source-facing owner form: under the same hypotheses, if `C` contains no
affine lines in the sense of `¬ Set.HasAffineLine 𝕜 C` and `f` attains its supremum on `C`, then
that supremum is attained at an extreme point of `C`. -/
theorem exists_mem_extremePoints_isMaxOn_of_exists_mem_isMaxOn_of_not_hasAffineLine
    (hC_no_affineLine : ¬ Set.HasAffineLine 𝕜 C) (hmax : ∃ x ∈ C, IsMaxOn f C x) :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  have hC_nonempty : C.Nonempty := by
    rcases hmax with ⟨x, hxC, hxmax⟩
    exact ⟨x, hxC⟩
  have hC_lineality : Set.lineality 𝕜 C = 0 :=
    (Set.lineality_eq_zero_iff_not_hasAffineLine hC_nonempty hC_closed hC_convex).2
      hC_no_affineLine
  exact exists_mem_extremePoints_isMaxOn_of_exists_mem_isMaxOn_of_lineality_eq_zero
    hf hC_closed hC_convex hC_dom hC_lineality hmax
omit hf hC_closed hC_convex hC_dom

end SourceFacing

/-! ### Corollary_32_3_2 (from Chap06) -/
open scoped Rockafellar

universe u v

section CoreOwner

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 32.3.2 is usually presented on `ri(dom f)`.
- `core/canonical`: the primitive attainment inputs are compactness, continuity on the working set,
  and the extreme-point hull identity.
- `bridge/view`: relative-interior hypotheses are treated as a thin bridge through an explicit
  continuity-on-`riDom` owner hypothesis.

Primitive data vs derived API:
- primitive core inputs: `C.Nonempty`, `IsCompact C`, `ContinuousOn f C`, and
  `C = convexHull 𝕜 (C.extremePoints 𝕜)`;
- derived core output: existence of an extreme-point maximizer and the value companion
  `∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C)`;
- bridge input/output: `C ⊆ riDom[𝕜](f)` plus `ContinuousOn f (riDom[𝕜](f))`.
-/

section IsMaxOnCore

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]
variable {α : Type v} [LinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α} {C : Set E}

/-- Core canonical owner form behind Corollary 32.3.2: on a nonempty compact set whose carrier
equals the convex hull of its extreme points, a convex `WithBotTop α`-valued function that is
continuous on that set attains its supremum at an extreme point. -/
theorem exists_mem_extremePoints_isMaxOn_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hC_cont : ContinuousOn f C) (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  obtain ⟨x, hxC, hxmax⟩ := hC_compact.exists_isMaxOn hC_nonempty hC_cont
  have hxHull : x ∈ convexHull 𝕜 (C.extremePoints 𝕜) := by
    rw [← hC_eq]
    exact hxC
  have hxmaxHull : IsMaxOn f (convexHull 𝕜 (C.extremePoints 𝕜)) x := by
    rw [← hC_eq]
    exact hxmax
  obtain ⟨y, hyext, hymaxext⟩ :=
    hf.exists_isMaxOn_of_isMaxOn_convexHull hxHull hxmaxHull
  have hymax : IsMaxOn f C y := by
    rw [hC_eq]
    have hsub : C.extremePoints 𝕜 ⊆ {z : E | f z ≤ f y} := by
      intro z hz
      exact hymaxext hz
    have hsubHull : convexHull 𝕜 (C.extremePoints 𝕜) ⊆ {z : E | f z ≤ f y} :=
      convexHull_min hsub (by simpa using hf.convex_le (f y))
    intro z hz
    exact hsubHull hz
  exact ⟨y, hyext, hymax⟩

end IsMaxOnCore

section IsMaxOnRiDomBridge

variable {𝕜 : Type v} [Ring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {α : Type v} [LinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α} {C : Set E}

/-- Bridge form of Corollary 32.3.2 using relative-interior domain data:
if `f` is continuous on `riDom[𝕜](f)` and `C ⊆ riDom[𝕜](f)`, then the compact/extreme-hull
conclusion follows. -/
theorem exists_mem_extremePoints_isMaxOn_of_nonempty_compact_subset_riDom_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hcont_riDom : ContinuousOn f (riDom[𝕜](f))) (hC_subset : C ⊆ riDom[𝕜](f))
    (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  exact exists_mem_extremePoints_isMaxOn_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
    (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
    (hC_cont := hcont_riDom.mono hC_subset) (hC_eq := hC_eq)

end IsMaxOnRiDomBridge

section ValueCore

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]
variable {α : Type v} [ConditionallyCompleteLinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α} {C : Set E}

/-- Core compact-value companion for Corollary 32.3.2: under the same compact owner hypotheses,
some extreme point realizes `sSup (f '' C)`. -/
theorem exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hC_cont : ContinuousOn f C) (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) := by
  obtain ⟨y, hyext, hymax⟩ :=
    exists_mem_extremePoints_isMaxOn_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
      (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
      (hC_cont := hC_cont) (hC_eq := hC_eq)
  have hyC : y ∈ C := (mem_extremePoints.mp hyext).1
  have hRange : Set.range (fun z : C ↦ f z) = f '' C := by
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.2, rfl⟩
    · rintro ⟨z, hzC, rfl⟩
      exact ⟨⟨z, hzC⟩, rfl⟩
  refine ⟨y, hyext, ?_⟩
  calc
    f y = ⨆ z : C, f z := (hymax.iSup_eq hyC).symm
    _ = sSup (Set.range fun z : C ↦ f z) := by rw [sSup_range]
    _ = sSup (f '' C) := by rw [hRange]

/-- Proper-convex compact companion on the canonical scalar layer: under the same compact owner
hypotheses plus `C ⊆ dom(f)`, the supremum value on `C` is represented by a scalar in `α`. -/
theorem exists_scalar_eq_sSup_image_of_proper_nonempty_compact_of_subset_dom_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hf_proper : f.IsProper)
    (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C) (hC_cont : ContinuousOn f C)
    (hC_dom : C ⊆ dom(f)) (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ r : α, sSup (f '' C) = (r : WithBotTop α) := by
  obtain ⟨y, hyext, hySup⟩ :=
    exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
      (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
      (hC_cont := hC_cont) (hC_eq := hC_eq)
  have hyC : y ∈ C := (mem_extremePoints.mp hyext).1
  have hy_dom : y ∈ dom(f) := hC_dom hyC
  have hy_top : f y ≠ ⊤ := (mem_effectiveDomain.mp hy_dom).ne
  have hy_bot : f y ≠ ⊥ := hf_proper.ne_bot y
  lift f y to α using ⟨hy_top, hy_bot⟩ with r hr
  refine ⟨r, ?_⟩
  simpa [hr] using hySup.symm

end ValueCore

section ValueRiDomBridge

variable {𝕜 : Type v} [Ring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {α : Type v} [ConditionallyCompleteLinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α} {C : Set E}

/-- Bridge value companion for Corollary 32.3.2 on `riDom[𝕜](f)`. -/
theorem exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_subset_riDom_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hcont_riDom : ContinuousOn f (riDom[𝕜](f))) (hC_subset : C ⊆ riDom[𝕜](f))
    (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) := by
  exact exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_of_continuousOn_of_eq_extremeHull
    (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
    (hC_cont := hcont_riDom.mono hC_subset) (hC_eq := hC_eq)

/-- Proper-convex bridge companion on `riDom[𝕜](f)`. -/
theorem exists_scalar_eq_sSup_image_of_proper_nonempty_compact_subset_riDom_of_eq_extremeHull
    (hf : Function.IsConvex 𝕜 f) (hf_proper : f.IsProper)
    (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hcont_riDom : ContinuousOn f (riDom[𝕜](f))) (hC_subset : C ⊆ riDom[𝕜](f))
    (hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜)) :
    ∃ r : α, sSup (f '' C) = (r : WithBotTop α) := by
  refine
    exists_scalar_eq_sSup_image_of_proper_nonempty_compact_of_subset_dom_of_eq_extremeHull
      (hf := hf) (hf_proper := hf_proper) (hC_nonempty := hC_nonempty)
      (hC_compact := hC_compact) (hC_cont := hcont_riDom.mono hC_subset)
      (hC_dom := ?_) (hC_eq := hC_eq)
  intro x hx
  exact intrinsicInterior_subset (hC_subset hx)

end ValueRiDomBridge

end CoreOwner

section CompactConvexBridge

open Bornology

variable {𝕜 : Type v} [NormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]

private theorem compact_convex_eq_convexHull_extremePoints
    (hC_compact : IsCompact C) (hC_convex : Convex 𝕜 C) :
    C = convexHull 𝕜 (C.extremePoints 𝕜) :=
  eq_convexHull_extremePoints_of_isClosed_of_isBounded_of_convex
    hC_compact.isClosed hC_compact.isBounded hC_convex

section IsMaxOnLayer

variable {α : Type v} [LinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α}
variable (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
  (hC_convex : Convex 𝕜 C) (hcont_riDom : ContinuousOn f (riDom[𝕜](f)))
  (hC_subset : C ⊆ riDom[𝕜](f))

include hf hC_nonempty hC_compact hC_convex hcont_riDom hC_subset

/-- Compact-convex bridge form of Corollary 32.3.2. -/
theorem exists_mem_extremePoints_isMaxOn_of_nonempty_compact_convex_subset_riDom
    :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  have hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜) :=
    compact_convex_eq_convexHull_extremePoints (𝕜 := 𝕜) (C := C) hC_compact hC_convex
  exact exists_mem_extremePoints_isMaxOn_of_nonempty_compact_subset_riDom_of_eq_extremeHull
    (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
    (hcont_riDom := hcont_riDom) (hC_subset := hC_subset) (hC_eq := hC_eq)

end IsMaxOnLayer

section ValueLayer

variable {α : Type v} [ConditionallyCompleteLinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α}
variable (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
  (hC_convex : Convex 𝕜 C) (hcont_riDom : ContinuousOn f (riDom[𝕜](f)))
  (hC_subset : C ⊆ riDom[𝕜](f))

include hf hC_nonempty hC_compact hC_convex hcont_riDom hC_subset

/-- Compact-convex value companion: some extreme point of `C` realizes `sSup (f '' C)`. -/
theorem exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_convex_subset_riDom
    :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) := by
  have hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜) :=
    compact_convex_eq_convexHull_extremePoints (𝕜 := 𝕜) (C := C) hC_compact hC_convex
  exact exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_subset_riDom_of_eq_extremeHull
    (hf := hf) (hC_nonempty := hC_nonempty) (hC_compact := hC_compact)
    (hcont_riDom := hcont_riDom) (hC_subset := hC_subset) (hC_eq := hC_eq)

/-- Compact-convex proper companion: the supremum over `C` is represented by a scalar in `α`. -/
theorem exists_scalar_eq_sSup_image_of_proper_nonempty_compact_convex_subset_riDom
    (hf_proper : f.IsProper) :
    ∃ r : α, sSup (f '' C) = (r : WithBotTop α) := by
  have hC_eq : C = convexHull 𝕜 (C.extremePoints 𝕜) :=
    compact_convex_eq_convexHull_extremePoints (𝕜 := 𝕜) (C := C) hC_compact hC_convex
  exact
    exists_scalar_eq_sSup_image_of_proper_nonempty_compact_subset_riDom_of_eq_extremeHull
      (hf := hf) (hf_proper := hf_proper) (hC_nonempty := hC_nonempty)
      (hC_compact := hC_compact) (hcont_riDom := hcont_riDom)
      (hC_subset := hC_subset) (hC_eq := hC_eq)

end ValueLayer

end CompactConvexBridge

section ClosedBoundedBridge

open Bornology

variable {𝕜 : Type v} [NormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
variable {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]

private theorem closed_bounded_isCompact (hC_closed : IsClosed C)
    (hC_bounded : IsBounded C) : IsCompact C :=
  Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded

section IsMaxOnLayer

variable {α : Type v} [LinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α}
variable (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
  (hC_bounded : IsBounded C) (hC_convex : Convex 𝕜 C)
  (hcont_riDom : ContinuousOn f (riDom[𝕜](f))) (hC_subset : C ⊆ riDom[𝕜](f))

include hf hC_nonempty hC_closed hC_bounded hC_convex hcont_riDom hC_subset

/-- Source-facing closed-bounded specialization of Corollary 32.3.2. -/
theorem exists_mem_extremePoints_isMaxOn_of_nonempty_closed_bounded_convex_subset_riDom
    :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  exact exists_mem_extremePoints_isMaxOn_of_nonempty_compact_convex_subset_riDom
    (hf := hf) (hC_nonempty := hC_nonempty)
    (hC_compact := closed_bounded_isCompact hC_closed hC_bounded)
    (hC_convex := hC_convex) (hcont_riDom := hcont_riDom) (hC_subset := hC_subset)

end IsMaxOnLayer

section ValueLayer

variable {α : Type v} [ConditionallyCompleteLinearOrder α]
  [AddCommMonoid α] [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [TopologicalSpace (WithBotTop α)] [ClosedIciTopology (WithBotTop α)]
variable {f : E → WithBotTop α}
variable (hf : Function.IsConvex 𝕜 f) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
  (hC_bounded : IsBounded C) (hC_convex : Convex 𝕜 C)
  (hcont_riDom : ContinuousOn f (riDom[𝕜](f))) (hC_subset : C ⊆ riDom[𝕜](f))

include hf hC_nonempty hC_closed hC_bounded hC_convex hcont_riDom hC_subset

/-- Source-facing closed-bounded value companion: some extreme point of `C` realizes
`sSup (f '' C)`. -/
theorem exists_mem_extremePoints_eq_sSup_image_of_nonempty_closed_bounded_convex_subset_riDom
    :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) := by
  exact exists_mem_extremePoints_eq_sSup_image_of_nonempty_compact_convex_subset_riDom
    (hf := hf) (hC_nonempty := hC_nonempty)
    (hC_compact := closed_bounded_isCompact hC_closed hC_bounded)
    (hC_convex := hC_convex) (hcont_riDom := hcont_riDom) (hC_subset := hC_subset)

/-- Source-facing closed-bounded proper companion: the supremum over `C` is represented by a
scalar in `α`. -/
theorem exists_scalar_eq_sSup_image_of_proper_nonempty_closed_bounded_convex_subset_riDom
    (hf_proper : f.IsProper) :
    ∃ r : α, sSup (f '' C) = (r : WithBotTop α) := by
  exact exists_scalar_eq_sSup_image_of_proper_nonempty_compact_convex_subset_riDom
    (hf := hf) (hC_nonempty := hC_nonempty)
    (hC_compact := closed_bounded_isCompact hC_closed hC_bounded)
    (hC_convex := hC_convex) (hcont_riDom := hcont_riDom) (hC_subset := hC_subset)
    hf_proper

end ValueLayer

end ClosedBoundedBridge

/-! ### Corollary_32_3_3 (from Chap06) -/
open scoped Rockafellar

section

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 32.3.3 concludes that the supremum of a convex function over `C` is
  attained when no half-line contained in `C` carries `f` unbounded above.
- `core/canonical`: the primitive set-side owner for the Chapter 19 finite-extreme bridge is
  `C.IsFinitelyGeneratedConvex R`; the canonical half-line surface is `affineHalfLine x r`; the
  canonical boundedness surface is `BddAbove (f '' s)`; and the canonical attainment owner is
  `IsMaxOn`.
- `bridge/view`: the source phrase “there are no half-lines in `C` on which `f` is unbounded
  above” is expressed directly as `BddAbove (f '' affineHalfLine x r)` on each included half-line.

Domain-style sampling used here:
- `Set.IsFinitelyGeneratedConvex` from `Chap04/Text_19_0_4`;
- `affineHalfLine` from `Chap04/Defn_18_4`;
- `ConvexOn` from the canonical convex-function owner layer;
- `IsMaxOn` as the canonical mathlib owner for attained suprema.

Primitive data vs derived API:
- primitive inputs: the convex function `f`, the feasible set `C`, the primitive finite-generation
  owner `C.IsFinitelyGeneratedConvex R`, convexity of `f` on `C`, explicit nonemptiness of `C`,
  and the source half-line boundedness hypothesis;
- derived API: existence of a maximizer in owner form `∃ x ∈ C, IsMaxOn f C x`, and the
  companion source wording `f x = sSup (f '' C)`.

Semantic-fidelity note:
- the extracted sentence omits the ambient setup needed by its proof. The explicit hypothesis
  `C.Nonempty` is made visible because attainment over `∅` would be false.

Ambient refinement:
- codomain layer: the public codomain surface is `WithTopBot α` rather than a concrete alias;
- scalar layer: the geometric owner is stated on the scalar-generic Chapter 18/19 layer.

Layer target: `core/canonical` for the primitive owner theorem.
-/

namespace Set.IsFinitelyGeneratedConvex

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {E : Type*} [AddCommMonoid E] [Module R E]

section IsMaxOnLayer

variable {α : Type*} [PartialOrder α] [AddCommMonoid α]
variable [SMul R α] [SMul R (WithTopBot α)]

/-- Core owner form of Corollary 32.3.3: for a nonempty finitely generated convex set `C`, if
`f` is convex on `C` and every affine half-line contained in `C` has bounded image under `f`,
then the supremum of `f` over `C` is attained. -/
theorem exists_mem_isMaxOn_of_bddAbove_affineHalfLines
    {f : E → WithTopBot α} {C : Set E} (hC_fg : C.IsFinitelyGeneratedConvex R)
    (hf : ConvexOn R C f) (hC_nonempty : C.Nonempty)
    (hhalfLine_bddAbove :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray R E⦄,
        affineHalfLine x r ⊆ C →
          BddAbove (f '' affineHalfLine x r)) :
    ∃ x ∈ C, IsMaxOn f C x := by
  sorry

end IsMaxOnLayer

section sSupLayer

variable {α : Type*}
variable [ConditionallyCompleteLinearOrder α] [AddCommMonoid α]
variable [SMul R α] [SMul R (WithTopBot α)]

/-- Core owner companion to Corollary 32.3.3: under the same finitely generated hypotheses, some
point of `C` realizes the supremum value `sSup (f '' C)`. -/
theorem exists_mem_eq_sSup_image_of_bddAbove_affineHalfLines
    {f : E → WithTopBot α} {C : Set E} (hC_fg : C.IsFinitelyGeneratedConvex R)
    (hf : ConvexOn R C f) (hC_nonempty : C.Nonempty)
    (hhalfLine_bddAbove :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray R E⦄,
        affineHalfLine x r ⊆ C →
          BddAbove (f '' affineHalfLine x r)) :
    ∃ x ∈ C, f x = sSup (f '' C) := by
  by_cases htop : ∃ x ∈ C, f x = (⊤ : WithTopBot α)
  · rcases htop with ⟨x, hxC, hfx_top⟩
    refine ⟨x, hxC, ?_⟩
    have hsSup_top : sSup (f '' C) = ⊤ := by
      exact top_le_iff.mp <| by
        simpa [hfx_top] using (le_sSup (Set.mem_image_of_mem f hxC))
    rw [hfx_top, hsSup_top]
  obtain ⟨x, hxC, hxmax⟩ :=
    hC_fg.exists_mem_isMaxOn_of_bddAbove_affineHalfLines
      hf hC_nonempty hhalfLine_bddAbove
  have hRange : Set.range (fun y : C ↦ f y) = f '' C := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hyC, rfl⟩
      exact ⟨⟨y, hyC⟩, rfl⟩
  refine ⟨x, hxC, ?_⟩
  calc
    f x = ⨆ y : C, f y := (hxmax.iSup_eq hxC).symm
    _ = sSup (Set.range fun y : C ↦ f y) := by rw [sSup_range]
    _ = sSup (f '' C) := by rw [hRange]

end sSupLayer

end Set.IsFinitelyGeneratedConvex

end

/-! ### Theorem_32_3 (from Chap06) -/
open scoped Rockafellar

universe u

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 32.3 reduces maximization on `C` to the textbook slice
  `C ∩ Lᗮ`, where `L = span (lin C)`.
- `core/canonical`: lineality `lin[𝕜](C)`, submodule span, pairing annihilator `ᗮₚ`,
  `Set.extremePoints`, `sSup`, and `IsMaxOn`.
- `bridge/view`: this file exposes the pairing-level annihilator owner
  `Set.linealAnnihilator`; the textbook slice is then written directly as
  `C ∩ linAnn[𝕜](C)` in the theorem surfaces.

Primitive data vs derived API:
- primitive owner data: `C` and `lin[𝕜](C)`;
- derived API: `linAnn[𝕜](C) = ((span 𝕜 (lin[𝕜](C)))ᗮₚ : Set Y)` and the
  source-facing slice `C ∩ linAnn[𝕜](C)`.

Layer target: `source-facing`, on the scalar/pairing-generic owner layer.
-/

namespace Set

open scoped Rockafellar
open Submodule

section PairingAnnihilator

/-- Pairing-level annihilator of the lineality subspace `span 𝕜 (lin[𝕜](C))`. -/
abbrev linealAnnihilator (𝕜 : Type*) [CommSemiring 𝕜] [LE 𝕜]
    {E : Type u} [AddCommGroup E] [Module 𝕜 E]
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]
    (C : Set E) : Set Y :=
  (((span 𝕜 (lin[𝕜](C)))ᗮₚ : Submodule 𝕜 Y) : Set Y)

scoped[Rockafellar] notation "linAnn[" 𝕜 "](" C ")" =>
  Set.linealAnnihilator (𝕜 := 𝕜) C

end PairingAnnihilator

end Set

section SupremumClause

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [HasLinearPairing E E 𝕜]
variable {α : Type*} [AddCommMonoid α] [ConditionallyCompleteLinearOrder α]
  [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

-- Proof sketch: remove the lineality directions of `C` by passing to the textbook slice
-- `C ∩ Lᗮₚ`, where `L = Submodule.span 𝕜 (lin[𝕜](C))`. On that slice there are no affine-line
-- directions coming from `lin[𝕜](C)`, so the Chapter 18 representation by extreme
-- points/extreme directions can be combined with half-line boundedness of `f` to eliminate the
-- direction part and reduce the supremum to extreme points.
/-- Theorem 32.3 (1): under convexity/domain and half-line boundedness hypotheses on a closed
convex set `C`, the supremum of `f` on `C` agrees with the supremum on the extreme points of
`C ∩ linAnn[𝕜](C)`. -/
theorem sSup_image_eq_sSup_image_extremePoints_linealAnnihilatorSlice
    {f : E → WithBotTop α} {C : Set E} (hf : f.IsConvex 𝕜)
    (hC_closed : IsClosed C)
    (hC_convex : Convex 𝕜 C) (hC_dom : C ⊆ dom(f))
    (hhalfLine_bddAbove :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray 𝕜 E⦄,
        affineHalfLine x r ⊆ C → BddAbove (f '' affineHalfLine x r)) :
    sSup (f '' C) = sSup (f '' (Set.extremePoints 𝕜 (C ∩ linAnn[𝕜](C)))) := sorry

end SupremumClause

section AttainmentClause

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [HasLinearPairing E E 𝕜]
variable {α : Type*} [AddCommMonoid α] [LinearOrder α]
  [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

-- Proof sketch: once the supremum side is reduced to extreme points of the slice `C ∩ Lᗮₚ`,
-- combine that reduction with the attainment bridge from Theorem 32.2 to transfer a maximizer on
-- `C` to a maximizer on those extreme points.
/-- Theorem 32.3 (2): if `f` attains a maximum on `C`, then under the same geometric hypotheses
it attains that maximum at an extreme point of
`C ∩ linAnn[𝕜](C)`.
This clause is kept in a separate section so it does not inherit unnecessary
`ConditionallyCompleteLinearOrder` assumptions from the supremum clause. -/
theorem exists_mem_isMaxOn_extremePoints_linealAnnihilatorSlice_of_exists_mem_isMaxOn
    {f : E → WithBotTop α} {C : Set E} (hf : f.IsConvex 𝕜)
    (hC_closed : IsClosed C)
    (hC_convex : Convex 𝕜 C) (hC_dom : C ⊆ dom(f))
    (hhalfLine_bddAbove :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray 𝕜 E⦄,
        affineHalfLine x r ⊆ C → BddAbove (f '' affineHalfLine x r))
    (hmax : ∃ x ∈ C, IsMaxOn f C x) :
    ∃ y ∈ Set.extremePoints 𝕜 (C ∩ linAnn[𝕜](C)),
      IsMaxOn f C y := sorry

end AttainmentClause

/-! ### Corollary_32_3_4 (from Chap06) -/
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E E 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 32.3.4 says that for a polyhedral set `C` containing no affine
  lines, any convex function whose value-image on `C` is bounded above attains its supremum at an
  extreme point of `C`.
- `core/canonical`: this file now reuses canonical boundedness owners
  `BddAbove (f '' C)` and `BddAbove (f '' affineHalfLine x r)`, the canonical convex-function
  owner `ConvexOn 𝕜 C f`, and the Chapter 32 attainment owners `IsMaxOn` / `Set.extremePoints`.
- `bridge/view`: this file is the thin source-facing specialization that first uses the Chapter 19
  bridge `Set.IsPolyhedral.isFinitelyGeneratedConvex` to obtain a maximizer from Corollary 32.3.3,
  then invokes Corollary 32.3.1 to move that maximizer to an extreme point.

Domain-style sampling used here:
- `Set.IsPolyhedral.isFinitelyGeneratedConvex` from `Theorem_19_1`;
- `Set.IsFinitelyGeneratedConvex.exists_mem_isMaxOn_of_bddAbove_affineHalfLines` from
  Corollary 32.3.3;
- `exists_mem_extremePoints_isMaxOn_of_exists_mem_isMaxOn_of_not_hasAffineLine` from
  Corollary 32.3.1;
- `Set.IsPolyhedral.convex` and `Set.IsPolyhedral.isClosed`.

Primitive data vs derived API:
- primitive inputs: global convexity `f.IsConvex 𝕜`, local convexity owner `ConvexOn 𝕜 C f`, the
  polyhedral owner `C.IsPolyhedral 𝕜`, explicit nonemptiness of `C`, the source-facing no-line
  hypothesis `¬ Set.HasAffineLine 𝕜 C`, explicit domain inclusion `C ⊆ dom(f)`, and boundedness of
  `f '' C`;
- derived API: existence of a maximizing extreme point in owner form `IsMaxOn`, and the companion
  `sSup` equality at such an extreme point.

Semantic-fidelity note:
- the textbook sentence omits nonemptiness/setup needed for attainment. This is made explicit
  because the conclusion is false for `C = ∅`.

Ambient refinement:
- this file stays on the scalar/pairing-generic finite-dimensional topological module layer used by
  Chapter 32 owner theorems.

Layer target: `bridge/view`, keeping the source-facing polyhedral hypothesis while delegating the
maximizer and extreme-point steps to existing owner theorems.
-/

section IsMaxOnLayer

variable {α : Type*} [AddCommMonoid α] [LinearOrder α]
  [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [SMul 𝕜 (WithTopBot α)]

namespace Set.IsPolyhedral

/-- Corollary 32.3.4 owner form: if `C` is polyhedral, contains no affine lines, and `f '' C` is
bounded above, then `f` attains its maximum over `C` at an extreme point of `C`. Nonemptiness of
`C` is stated explicitly because attainment would otherwise be false for `C = ∅`.
-/
theorem exists_mem_extremePoints_isMaxOn_of_not_hasAffineLine_of_bddAbove
    {f : E → WithTopBot α} {C : Set E} (hC_poly : C.IsPolyhedral 𝕜)
    (hf : f.IsConvex 𝕜) (hf_onC : ConvexOn 𝕜 C f) (hC_nonempty : C.Nonempty)
    (hC_noAffineLine : ¬ Set.HasAffineLine 𝕜 C) (hC_dom : C ⊆ dom(f))
    (hC_bddAbove : BddAbove (f '' C)) :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y := by
  have hhalfLine_bddAbove :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray 𝕜 E⦄,
        affineHalfLine x r ⊆ C →
          BddAbove (f '' affineHalfLine x r) := by
    intro x r hsubset
    exact hC_bddAbove.mono (by
      intro z hz
      exact ⟨z, hsubset hz, rfl⟩)
  have hC_closed : IsClosed C := (hC_poly.isClosed_hasFiniteFaces).1
  obtain ⟨x, hxC, hxmax⟩ :=
    hC_poly.isFinitelyGeneratedConvex.exists_mem_isMaxOn_of_bddAbove_affineHalfLines
      hf_onC hC_nonempty hhalfLine_bddAbove
  exact exists_mem_extremePoints_isMaxOn_of_exists_mem_isMaxOn_of_not_hasAffineLine
    hf hC_closed hC_poly.convex hC_dom hC_noAffineLine ⟨x, hxC, hxmax⟩

end Set.IsPolyhedral

/-- Corollary 32.3.4: if `C` is polyhedral, contains no affine lines, and `f '' C` is bounded
above, then `f` attains its maximum over `C` at an extreme point of `C`.
-/
theorem exists_mem_extremePoints_isMaxOn_of_polyhedral_of_not_hasAffineLine_of_bddAbove
    {f : E → WithTopBot α} {C : Set E}
    (hf : f.IsConvex 𝕜) (hf_onC : ConvexOn 𝕜 C f) (hC_poly : C.IsPolyhedral 𝕜)
    (hC_nonempty : C.Nonempty) (hC_noAffineLine : ¬ Set.HasAffineLine 𝕜 C)
    (hC_dom : C ⊆ dom(f)) (hC_bddAbove : BddAbove (f '' C)) :
    ∃ y ∈ C.extremePoints 𝕜, IsMaxOn f C y :=
  hC_poly.exists_mem_extremePoints_isMaxOn_of_not_hasAffineLine_of_bddAbove
    hf hf_onC hC_nonempty hC_noAffineLine hC_dom hC_bddAbove

end IsMaxOnLayer

section sSupLayer

variable {α : Type*} [ConditionallyCompleteLinearOrder α] [AddCommMonoid α]
  [IsOrderedAddMonoid α] [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]
variable [SMul 𝕜 (WithTopBot α)]

namespace Set.IsPolyhedral

/-- Corollary 32.3.4 value companion: under the hypotheses of the main corollary, some extreme
point of `C` realizes the supremum value `sSup (f '' C)`.
-/
theorem exists_mem_extremePoints_eq_sSup_image_of_not_hasAffineLine_of_bddAbove
    {f : E → WithTopBot α} {C : Set E} (hC_poly : C.IsPolyhedral 𝕜)
    (hf : f.IsConvex 𝕜) (hf_onC : ConvexOn 𝕜 C f) (hC_nonempty : C.Nonempty)
    (hC_noAffineLine : ¬ Set.HasAffineLine 𝕜 C) (hC_dom : C ⊆ dom(f))
    (hC_bddAbove : BddAbove (f '' C)) :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) := by
  obtain ⟨y, hyext, hymax⟩ :=
    hC_poly.exists_mem_extremePoints_isMaxOn_of_not_hasAffineLine_of_bddAbove
      hf hf_onC hC_nonempty hC_noAffineLine hC_dom hC_bddAbove
  refine ⟨y, hyext, le_antisymm ?_ ?_⟩
  · exact le_sSup <| Set.mem_image_of_mem f (mem_extremePoints.mp hyext).1
  · refine sSup_le ?_
    rintro _ ⟨z, hzC, rfl⟩
    exact hymax hzC

end Set.IsPolyhedral

/-- A source-facing supremum-value companion: under the hypotheses of the main corollary, some
extreme point of `C` realizes the supremum value `sSup (f '' C)`.
-/
theorem exists_mem_extremePoints_eq_sSup_image_of_polyhedral_of_not_hasAffineLine_of_bddAbove
    {f : E → WithTopBot α} {C : Set E}
    (hf : f.IsConvex 𝕜) (hf_onC : ConvexOn 𝕜 C f) (hC_poly : C.IsPolyhedral 𝕜)
    (hC_nonempty : C.Nonempty) (hC_noAffineLine : ¬ Set.HasAffineLine 𝕜 C)
    (hC_dom : C ⊆ dom(f)) (hC_bddAbove : BddAbove (f '' C)) :
    ∃ y ∈ C.extremePoints 𝕜, f y = sSup (f '' C) :=
  hC_poly.exists_mem_extremePoints_eq_sSup_image_of_not_hasAffineLine_of_bddAbove
    hf hf_onC hC_nonempty hC_noAffineLine hC_dom hC_bddAbove

end sSupLayer

end
