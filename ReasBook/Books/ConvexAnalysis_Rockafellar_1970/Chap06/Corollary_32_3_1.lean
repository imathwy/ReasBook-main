import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_4_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_32_3

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
