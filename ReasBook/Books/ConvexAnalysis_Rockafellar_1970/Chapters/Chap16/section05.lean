import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_16_5_1_1 (from Chap03) -/
noncomputable section

open scoped Rockafellar
open Function

universe u v w

section ConvexIndicatorBridge

variable {𝕜 : Type*} {X : Type u}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]

omit [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] in
private theorem convex_minorant_indicator_le_indicator_convexHull
    (S : Set X) {g : X → WithBotTop 𝕜} (hg_convex : g.IsConvex 𝕜)
    (hg_le : g ≤ (δ[𝕜](· | S))) :
    g ≤ (δ[𝕜](· | convexHull 𝕜 S)) := by
  intro x
  by_cases hx : x ∈ convexHull 𝕜 S
  · have hsubset_epi : (LinearMap.inl 𝕜 X 𝕜) '' S ⊆ epi g := by
      intro p hp
      rcases hp with ⟨s, hs, rfl⟩
      rw [mem_epi_iff]
      exact (hg_le s).trans (by simp [hs])
    have hconv_epi : Convex 𝕜 (epi g) := hg_convex.convex_epi
    have hconvHull_subset :
        convexHull 𝕜 ((LinearMap.inl 𝕜 X 𝕜) '' S) ⊆ epi g :=
      convexHull_min hsubset_epi hconv_epi
    have himage :
        (LinearMap.inl 𝕜 X 𝕜) '' convexHull 𝕜 S =
          convexHull 𝕜 ((LinearMap.inl 𝕜 X 𝕜) '' S) := by
      simpa using (LinearMap.image_convexHull (f := LinearMap.inl 𝕜 X 𝕜) (s := S))
    have hx_image : (x, (0 : 𝕜)) ∈ convexHull 𝕜 ((LinearMap.inl 𝕜 X 𝕜) '' S) := by
      have hx' : (x, (0 : 𝕜)) ∈ (LinearMap.inl 𝕜 X 𝕜) '' convexHull 𝕜 S :=
        ⟨x, hx, rfl⟩
      exact himage ▸ hx'
    have hx_epi : (x, (0 : 𝕜)) ∈ epi g := hconvHull_subset hx_image
    have hx_le_zero : g x ≤ (0 : 𝕜) := by
      simpa [mem_epi_iff] using hx_epi
    simpa [hx] using hx_le_zero
  · simp [hx]

omit [DenselyOrdered 𝕜] in
private theorem convexHullFunction_indicatorFunction_eq_indicatorFunction_convexHull
    (S : Set X) :
    conv((δ[𝕜](· | S))) = (δ[𝕜](· | convexHull 𝕜 S)) := by
  let f : Unit → X → WithBotTop 𝕜 := fun _ ↦ (δ[𝕜](· | S))
  let hHull := Function.isGreatest_conv_iInf_minorant f
  have hminor : conv((δ[𝕜](· | S))) ≤ (δ[𝕜](· | S)) := by
    simpa [f] using hHull.1.2
  have hconvex : (conv((δ[𝕜](· | S)))).IsConvex 𝕜 := by
    simpa [f] using hHull.1.1
  have hindicator_convex : ((δ[𝕜](· | convexHull 𝕜 S))).IsConvex 𝕜 :=
    (indicator_isConvex_iff (C := convexHull 𝕜 S)).2 (convex_convexHull 𝕜 S)
  have hindicator_minor :
      (δ[𝕜](· | convexHull 𝕜 S)) ≤ (δ[𝕜](· | S)) := by
    intro x
    by_cases hxS : x ∈ S
    · have hxh : x ∈ convexHull 𝕜 S := subset_convexHull 𝕜 S hxS
      simp [hxS, hxh]
    · by_cases hxh : x ∈ convexHull 𝕜 S
      · simp [hxS, hxh]
      · simp [hxS, hxh]
  have hind_le_conv :
      (δ[𝕜](· | convexHull 𝕜 S)) ≤ conv((δ[𝕜](· | S))) := by
    have hmem :
        (δ[𝕜](· | convexHull 𝕜 S)) ∈ Function.convexMinorants (⨅ i : Unit, f i) := by
      simpa [f] using
        (show (δ[𝕜](· | convexHull 𝕜 S)) ∈ Function.convexMinorants (δ[𝕜](· | S)) from
          ⟨hindicator_convex, hindicator_minor⟩)
    simpa [f] using hHull.2 hmem
  have hconv_le_hind :
      conv((δ[𝕜](· | S))) ≤ (δ[𝕜](· | convexHull 𝕜 S)) :=
    convex_minorant_indicator_le_indicator_convexHull S hconvex hminor
  exact le_antisymm hconv_le_hind hind_le_conv

end ConvexIndicatorBridge

section IndicatorIUnion

private theorem iInf_indicatorFunction_eq_indicatorFunction_iUnion
    {F : Type*} {𝕜 : Type*} [Zero 𝕜] [ConditionallyCompleteLattice 𝕜]
    {I : Sort w} (C : I → Set F) :
    (fun x : F ↦ ⨅ i : I, δ[𝕜](x | C i)) = (δ[𝕜](· | ⋃ i : I, C i)) := by
  funext x
  by_cases hx : x ∈ ⋃ i : I, C i
  · rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    rw [indicator_def, if_pos hx]
    apply le_antisymm
    · refine iInf_le_of_le i ?_
      simp [hi]
    · refine le_iInf fun j ↦ ?_
      by_cases hj : x ∈ C j
      · simp [hj]
      · simp [hj]
  · have hnot : ∀ i : I, x ∉ C i := by
      simpa [Set.mem_iUnion] using hx
    rw [indicator_def, if_neg hx]
    by_cases hI : Nonempty I
    · refine le_antisymm le_top ?_
      refine le_iInf fun j ↦ ?_
      simp [hnot j]
    · haveI : IsEmpty I := not_nonempty_iff.mp hI
      simp

end IndicatorIUnion

section

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]
variable {I : Sort w}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.5.1.1 identifies the support function of
  `convexHull 𝕜 (⋃ i, C i)` with the pointwise supremum of the family support functions.
- `core/canonical`: `supportFunction`, `indicator`, `Function.convexHull`, and
  `convexConjugate_conv_iInf_eq_iSup`.
- `bridge/view`: rewrite support functions as conjugates of indicators by
  `convexConjugate_indicatorFunction_eq_supportFunction`, then apply Theorem 16.5.1.
-/

/-- Corollary 16.5.1.1 at the pairing layer: the support function of the convex hull of a union
is the pointwise supremum of the support functions of the members. -/
theorem supportFunction_convexHull_iUnion_eq_iSup_supportFunction
    (C : I → Set X) :
    (fun y : Y ↦ δᵛ[WithBotTop 𝕜](y | convexHull 𝕜 (⋃ i : I, C i))) =
      ⨆ i : I, (fun y : Y ↦ δᵛ[WithBotTop 𝕜](y | C i)) := by
  let f : I → X → WithBotTop 𝕜 := fun i ↦ (δ[𝕜](· | C i))
  calc
    (fun y : Y ↦ δᵛ[WithBotTop 𝕜](y | convexHull 𝕜 (⋃ i : I, C i)))
        = ((δ[𝕜](· | convexHull 𝕜 (⋃ i : I, C i)))⋆) := by
            simpa using
              (convexConjugate_indicatorFunction_eq_supportFunction
                (C := convexHull 𝕜 (⋃ i : I, C i))).symm
    _ = (conv((δ[𝕜](· | ⋃ i : I, C i))))⋆ := by
          rw [convexHullFunction_indicatorFunction_eq_indicatorFunction_convexHull]
    _ = (conv(⨅ i : I, f i))⋆ := by
          have hf : (δ[𝕜](· | ⋃ i : I, C i)) = ⨅ i : I, f i := by
            funext x
            simpa [f] using congrFun (iInf_indicatorFunction_eq_indicatorFunction_iUnion C).symm x
          rw [hf]
    _ = ⨆ i : I, (f i)⋆ :=
          convexConjugate_conv_iInf_eq_iSup f
    _ = ⨆ i : I, (fun y : Y ↦ δᵛ[WithBotTop 𝕜](y | C i)) := by
          ext y
          rw [iSup_apply, iSup_apply]
          congr with i
          simpa [f] using
            congrFun
              (convexConjugate_indicatorFunction_eq_supportFunction
                (C := C i)) y

end

/-! ### Corollary_16_5_1_2 (from Chap03) -/
noncomputable section

universe u v

section

open scoped Rockafellar

variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜]
variable [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]
variable {I : Sort v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.5.1.2 identifies the support function of the intersection of the
  closures `closure (C i)` with the closure of the convex hull of the individual support
  functions. A stronger intrinsic-closure view is added below.
- `core/canonical`: the owner abstractions already present in the project are `supportFunction`,
  `conv`, `convexConjugate`, and `lowerSemicontinuousHull`.
- `bridge/view`: Rockafellar's `δ^*(· | C)` is represented by `δᵛ(· | C)`, while
  `cl (conv {δ^*(· | C_i)})` is represented by
  `cl(conv(⨅ i, (δᵛ(· | C i) : E → WithBotTop 𝕜)))`.

Domain-style sampling used here:
- `δ[𝕜](· | C)` / `δᵛ(· | C)`;
- `convexConjugate_supportFunction_eq_indicatorFunction_closure`;
- `convexConjugate_conv_iInf_eq_iSup`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`.
- `Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan` (for the intrinsic bridge theorem below).

Primitive data vs derived API:
- primitive input: a family of sets `C : I → Set E`;
- source-essential hypotheses: `I` is nonempty and each `C i` is convex;
- derived API: the support-function identity for the intersection of closures, then its
  intrinsic-closure restatement under the primitive affine-hull-closedness bridge assumptions.

Layer target: `source-facing`, stated directly on the finite-dimensional scalar-field pairing
owner layer already used by Theorem 16.5.1 and Text 13.1.5, with codomain `WithBotTop 𝕜`
instead of the over-concrete `EReal`/`ℝ` inner-product specialization.

Topology note: the primary conjugacy bridge imported from Text 13.1.5 is stated with ambient
`closure`; the intrinsic version uses the primitive bridge
`Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan` and is exposed below with explicit
affine-hull closedness assumptions on each set.
-/

omit [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [IsStrictOrderedRing 𝕜]
  [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜] [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
  [HasPairingSwap E E 𝕜] in
private theorem iSup_indicator_eq_indicator_iInter
    (C : I → Set E) (hI : Nonempty I) :
    (⨆ i : I, (δ[𝕜](· | C i) : E → WithBotTop 𝕜)) = (δ[𝕜](· | ⋂ i : I, C i)) := by
  letI : Nonempty I := hI
  classical
  funext x
  by_cases hx : ∀ i : I, x ∈ C i
  · have hx_not_union : x ∉ ⋃ i : I, (C i)ᶜ := by
      intro hx_union
      rcases Set.mem_iUnion.1 hx_union with ⟨i, hi⟩
      exact hi (hx i)
    have hδ : δ[𝕜](x | ⋂ i : I, C i) = (0 : WithBotTop 𝕜) := by
      simp [hx_not_union]
    rw [iSup_apply]
    calc
      (⨆ i : I, δ[𝕜](x | C i)) = (0 : WithBotTop 𝕜) := by
        refine le_antisymm ?_ ?_
        · refine iSup_le ?_
          intro i
          simp [hx i]
        · obtain ⟨i⟩ := hI
          exact le_iSup_of_le i (by simp [hx i])
      _ = δ[𝕜](x | ⋂ i : I, C i) := hδ.symm
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hsup : (⨆ i : I, δ[𝕜](x | C i)) = ⊤ := by
      apply top_unique
      refine le_iSup_of_le i ?_
      simp [hi]
    have hx' : x ∉ ⋂ i : I, C i := by
      simpa [Set.mem_iInter] using hx
    have hx_union : x ∈ ⋃ i : I, (C i)ᶜ := by
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    have hδ : δ[𝕜](x | ⋂ i : I, C i) = (⊤ : WithBotTop 𝕜) := by
      simp [hx_union]
    calc
      (⨆ i : I, (δ[𝕜](· | C i) : E → WithBotTop 𝕜)) x = ⊤ := by
        rw [iSup_apply]
        exact hsup
      _ = δ[𝕜](x | ⋂ i : I, C i) := by
        exact hδ.symm

-- Proof sketch: apply Theorem 16.5.1 to `fun i ↦ δᵛ(· | C i)`.
-- Text 13.1.5 rewrites each conjugate as `δ[𝕜](· | closure (C i))`, and the supremum of those
-- indicators is the indicator of `⋂ i, closure (C i)` because the family is nonempty.
-- Applying biconjugacy to `conv(⨅ i, ...)` yields the right-hand closure.
/-- Corollary 16.5.1.2 at the pairing owner layer: for a nonempty family of convex sets on a
finite-dimensional scalar-field space with continuous linear self-pairing, the support function
of `⋂ i, closure (C i)` is `cl(conv {δ^*(· | C_i)})`, rendered as
`cl(conv(⨅ i, (δᵛ(· | C i) : E → WithBotTop 𝕜)))`. -/
theorem supportFunction_iInter_closure_eq_cl_conv_iInf_supportFunction_of_convex
    (C : I → Set E) (hI : Nonempty I) (hC_convex : ∀ i : I, Convex 𝕜 (C i)) :
    (δᵛ(· | ⋂ i : I, closure (C i)) : E → WithBotTop 𝕜) =
      cl(conv(⨅ i : I, (δᵛ(· | C i) : E → WithBotTop 𝕜))) := by
  letI : Nonempty I := hI
  let g : I → E → WithBotTop 𝕜 := fun i ↦ (δᵛ(· | C i) : E → WithBotTop 𝕜)
  have hg_convex : (conv(⨅ i : I, g i)).IsConvex 𝕜 :=
    (Function.isGreatest_conv_iInf_minorant g).1.1
  have hconj :
      convexConjugate (conv(⨅ i : I, g i)) = (δ[𝕜](· | ⋂ i : I, closure (C i))) := by
    calc
      convexConjugate (conv(⨅ i : I, g i))
          = ⨆ i : I, convexConjugate (g i) :=
            convexConjugate_conv_iInf_eq_iSup g
      _ = ⨆ i : I, (δ[𝕜](· | closure (C i))) := by
            funext x
            simp [iSup_apply, g,
              convexConjugate_supportFunction_eq_indicatorFunction_closure, hC_convex]
      _ = (δ[𝕜](· | ⋂ i : I, closure (C i))) :=
            iSup_indicator_eq_indicator_iInter (C := fun i ↦ closure (C i)) hI
  simpa [g] using
    (calc
      (δᵛ(· | ⋂ i : I, closure (C i)) : E → WithBotTop 𝕜)
          = convexConjugate (δ[𝕜](· | ⋂ i : I, closure (C i))) := by
              simpa using
                (convexConjugate_indicatorFunction_eq_supportFunction
                  (E := E) (EStar := E) (α := 𝕜)
                  (⋂ i : I, closure (C i))).symm
      _ = convexConjugate (convexConjugate (conv(⨅ i : I, g i))) := by
            rw [hconj.symm]
      _ = cl(conv(⨅ i : I, g i)) :=
            hg_convex.biconjugate_eq_lowerSemicontinuousHull)

end

section

open scoped Rockafellar

variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]
variable {I : Sort v}

/-- Intrinsic-closure bridge of Corollary 16.5.1.2 at the same pairing owner layer: if each
`affineSpan 𝕜 (C i)` is closed, then the same support formula is read on
`⋂ i, intrinsicClosure 𝕜 (C i)` rather than `⋂ i, closure (C i)`. -/
theorem supportFunction_iInter_intrinsicClosure_eq_cl_conv_iInf_supportFunction_of_convex
    (C : I → Set E) (hI : Nonempty I) (hC_convex : ∀ i : I, Convex 𝕜 (C i))
    (hC_affineClosed : ∀ i : I, IsClosed (affineSpan 𝕜 (C i) : Set E)) :
    (δᵛ(· | ⋂ i : I, intrinsicClosure 𝕜 (C i)) : E → WithBotTop 𝕜) =
      cl(conv(⨅ i : I, (δᵛ(· | C i) : E → WithBotTop 𝕜))) := by
  have hIntrinsic :
      ∀ i : I, intrinsicClosure 𝕜 (C i) = closure (C i) := by
    intro i
    exact Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan (𝕜 := 𝕜) (C := C i)
      (hC_affineClosed i)
  calc
    (δᵛ(· | ⋂ i : I, intrinsicClosure 𝕜 (C i)) : E → WithBotTop 𝕜) =
        (δᵛ(· | ⋂ i : I, closure (C i)) : E → WithBotTop 𝕜) := by
          simp [hIntrinsic]
    _ = cl(conv(⨅ i : I, (δᵛ(· | C i) : E → WithBotTop 𝕜))) := by
      simpa using
        (supportFunction_iInter_closure_eq_cl_conv_iInf_supportFunction_of_convex
          C hI hC_convex)

end

/-! ### Text_16_5_1 (from Chap03) -/
open scoped BigOperators Rockafellar

noncomputable section

section

variable {E : Type*} [SeminormedAddCommGroup E]
variable {ι : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.5.1 specializes Theorem 16.5.3 to the finite family
  `fᵢ(x) = ‖x - aᵢ‖`, so that the conjugate of the pointwise maximum is described by a minimum
  of weighted pairings under unit-ball constraints.
- `core/canonical`: the owner abstractions are `convexConjugate`,
  Theorem 16.5.3's finite-family `StdSimplex` interface, and the norm/pairing structure reused
  from earlier Chapter 3 items.
- `bridge/view`: the textbook coefficients `λᵢ` are represented by `w : StdSimplex ℝ ι`,
  while the constraints `|xᵢ⋆| ≤ 1` become `‖xStarFamily i‖ ≤ 1`.

Domain-style sampling used here:
- `convexConjugate`;
- `StdSimplex`;
- `convexConjugate_iSup_eq_sInf_finite_convex_combinations_`
  `convexConjugate_of_common_closure_effectiveDomain`;
- `exists_finite_convex_combination_eq_convexConjugate_iSup_of_common_closure_effectiveDomain`.

Primitive data vs derived API:
- primitive data: the family of centers `a : ι → E`, with finiteness needed only when
  specializing Theorem 16.5.3;
- derived API: the source-facing owner `maximumDistanceToFamily a`, its admissible dual-value
  set, the `sInf` formula for the conjugate, the outside-the-unit-ball emptiness companion for
  that admissible set, and the minimum statement on the unit ball as an `IsLeast` assertion.

Layer target: the owner `maximumDistanceToFamily` is kept `source-facing`, but it is defined at
the weaker seminormed-additive-group layer because it only uses translated norms. The dual-value
set is a `bridge/view` item and therefore reintroduces an abstract dual owner via pairing for
its affine objective. The ambient `R^n` model and `Fin m` indexing from the prose are nonessential
here, so finite-dimensionality and finite-family assumptions are imposed only on the two
Theorem 16.5.3 specializations that actually use them.
-/

/-- The source-facing owner for the pointwise maximum of the translated norms `x ↦ ‖x - a i‖`,
implemented canonically as their pointwise supremum. -/
def maximumDistanceToFamily (a : ι → E) : E → WithBotTop ℝ :=
  fun x ↦ ⨆ i, (‖x - a i‖ : WithBotTop ℝ)

end

namespace maximumDistanceToFamily

section

variable {E EStar : Type*}
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable [SeminormedAddCommGroup EStar] [NormedSpace ℝ EStar]
variable [HasLinearPairing E EStar ℝ]
variable {ι : Type*}

/-- The admissible weighted pairing values in the dual formula for
`(maximumDistanceToFamily a)⋆ x⋆`. -/
def dualValues (a : ι → E) (xStar : EStar) : Set (WithBotTop ℝ) :=
  {r : WithBotTop ℝ |
    ∃ w : StdSimplex ℝ ι,
      ∃ xStarFamily : ι → EStar,
        w.sum (fun i wgt ↦ wgt • xStarFamily i) = xStar ∧
        (∀ i, ‖xStarFamily i‖ ≤ 1) ∧
        r = ((w.sum (fun i wgt ↦ wgt * ⟪a i, xStarFamily i⟫ₚ) : ℝ) : WithBotTop ℝ)}

section

variable [Finite ι] [FiniteDimensional ℝ E] [Nonempty ι]

/-- The conjugate of `maximumDistanceToFamily a` at `x⋆` is the infimum of the weighted
pairing values allowed by the textbook unit-ball and simplex constraints. -/
-- Proof sketch: apply Theorem 16.5.3 (2) to the family `x ↦ ‖x - a i‖`. For each summand, the
-- conjugate of the translated norm is the indicator of the dual unit ball plus the affine pairing
-- term `⟪a i, ·⟫ₚ`, so the general finite-convex-combination formula reduces to this explicit
-- admissible-value set. The unit-ball bridge is supplied by `h_norm_conj`.
theorem conjugate_eq_sInf_dualValues
    (a : ι → E) (xStar : EStar)
    (h_norm_conj :
      ((fun x : E ↦ (‖x‖ : WithBotTop ℝ))⋆ : EStar → WithBotTop ℝ) =
        (δ[ℝ](· | Metric.closedBall (0 : EStar) 1) : EStar → WithBotTop ℝ)) :
    (maximumDistanceToFamily a)⋆ xStar = sInf (dualValues a xStar) := sorry

end

-- Proof sketch: every admissible witness expresses `x⋆` as a convex combination of points in the
-- closed unit ball. Since that ball is convex, such a witness can exist only when `‖x⋆‖ ≤ 1`.
theorem dualValues_eq_empty_of_one_lt_norm
    (a : ι → E) {xStar : EStar} (hxStar : 1 < ‖xStar‖) :
    dualValues a xStar = ∅ := sorry

section

variable [Finite ι] [FiniteDimensional ℝ E] [Nonempty ι]

/-- Text 16.5.1, minimum form on the unit ball: for `f(x) = max_i ‖x - a_i‖` and `‖x⋆‖ ≤ 1`, the
conjugate value `f⋆(x⋆)` is the minimum of `∑ i λᵢ ⟪aᵢ, xᵢ⋆⟫ₚ` over all simplex weights
`w : StdSimplex ℝ ι` and vectors `xStarFamily : ι → EStar` satisfying `∑ i λᵢ xᵢ⋆ = x⋆` and
`‖xᵢ⋆‖ ≤ 1`. Outside the unit ball, `dualValues a x⋆ = ∅`, so the source `sInf` formula above
still yields the correct `⊤` value but there is no minimizing element. -/
-- Proof sketch: under `‖x⋆‖ ≤ 1`, specialize Theorem 16.5.3 (3) to the translated-norm family
-- `x ↦ ‖x - a i‖`. The resulting attaining finite-convex-combination formula lands in
-- `dualValues a x⋆`, because each translated-norm conjugate is finite exactly on the unit ball and
-- there it equals the affine pairing term `⟪a i, ·⟫ₚ`. Together with
-- `conjugate_eq_sInf_dualValues`, this
-- gives the `IsLeast` formulation of the textbook minimum claim on the finite-valued regime.
theorem isLeast_dualValues_of_norm_le_one
    (a : ι → E) {xStar : EStar} (hxStar : ‖xStar‖ ≤ 1)
    (h_norm_conj :
      ((fun x : E ↦ (‖x‖ : WithBotTop ℝ))⋆ : EStar → WithBotTop ℝ) =
        (δ[ℝ](· | Metric.closedBall (0 : EStar) 1) : EStar → WithBotTop ℝ)) :
    IsLeast (dualValues a xStar) ((maximumDistanceToFamily a)⋆ xStar) := sorry

end

end

end maximumDistanceToFamily

/-! ### Theorem_16_5_1 (from Chap03) -/
noncomputable section

universe u v w

section

open Function
open scoped Rockafellar

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [DenselyOrdered 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort w}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.5.1 identifies the conjugate of the convex hull of an arbitrary
  family of functions with the pointwise supremum of the individual conjugates.
- `core/canonical`: the owner constructions already present in the project are
  `conv(⨅ i, f i)` for `conv {f_i | i ∈ I}` and `convexConjugate` for Fenchel conjugation.
- `bridge/view`: the proof uses the maximal-minorant characterization
  `Function.isGreatest_conv_iInf_minorant` together with a direct pointwise bridge between
  affine-defect upper bounds and conjugate upper bounds.

Domain-style sampling used here:
- `conv`;
- `Function.isGreatest_conv_iInf_minorant`;
- `convexConjugate`;
- `convexConjugate_le_convexConjugate_of_le`;
- `convexConjugate_eq_iSup_pairing_sub`;
- the complete-lattice pointwise supremum `⨆ i, ...`.

Primitive data vs derived API:
- primitive input: the family `f : I → X → WithTopBot 𝕜`;
- derived API: the conjugacy identity between the family convex hull and the supremum of the
  individual conjugates as functions on the dual owner `Y`.

Layer target: `source-facing`, stated directly in terms of the already-canonical family hull owner
`conv(⨅ i, f i)` and the conjugate owner. The source proper-convex hypotheses are redundant for
this identity, so they are omitted from the public statement.
-/

-- Proof sketch: rewrite `f⋆ y⋆` as `⨆ x, (⟪x, y⋆⟫ - f x)` and solve the inequality
-- `(fun x ↦ (⟪x, y⋆⟫ - μ⋆ : 𝕜)).toWithTopBot ≤ f` pointwise using
-- `WithTopBot.sub_le_iff_le_add` in both directions.
private theorem pairingSubConst_toWithTopBot_le_iff_convexConjugate_le
    (f : X → WithTopBot 𝕜) (yStar : Y) (μStar : 𝕜) :
    (fun x : X ↦ (⟪x, yStar⟫ₚ - μStar : 𝕜)).toWithTopBot ≤ f ↔
      f⋆ yStar ≤ (μStar : WithTopBot 𝕜) := by
  rw [show f⋆ yStar =
      ⨆ x : X, (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜) - f x) by
    simpa using convexConjugate_eq_iSup_pairing_sub f yStar]
  constructor
  · intro h
    refine iSup_le fun x ↦ ?_
    have hx' : (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μStar : WithTopBot 𝕜)) ≤ f x := by
      simpa [Function.toWithTopBot, sub_eq_add_neg, WithTopBot.sub_eq_add_neg] using h x
    have hx'' : (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) ≤ f x + (μStar : WithTopBot 𝕜) :=
      (WithTopBot.sub_le_iff_le_add
        (b := (μStar : WithTopBot 𝕜))
        (c := f x)
        (.inl (WithTopBot.coe_ne_bot μStar))
        (.inl (WithTopBot.coe_ne_top μStar))).1 hx'
    exact
      (WithTopBot.sub_le_iff_le_add
        (b := f x)
        (c := (μStar : WithTopBot 𝕜))
        (.inr (WithTopBot.coe_ne_top μStar))
        (.inr (WithTopBot.coe_ne_bot μStar))).2
        (by simpa [add_comm] using hx'')
  · intro h x
    have hx : (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜) - f x) ≤ (μStar : WithTopBot 𝕜) :=
      (le_iSup_of_le x le_rfl).trans h
    have hx' : (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) ≤ (μStar : WithTopBot 𝕜) + f x := by
      exact
        (WithTopBot.sub_le_iff_le_add
          (b := f x)
          (c := (μStar : WithTopBot 𝕜))
          (.inr (WithTopBot.coe_ne_top μStar))
          (.inr (WithTopBot.coe_ne_bot μStar))).1 hx
    have hx'' : (((⟪x, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜) - (μStar : WithTopBot 𝕜)) ≤ f x := by
      exact
        (WithTopBot.sub_le_iff_le_add
          (b := (μStar : WithTopBot 𝕜))
          (c := f x)
          (.inl (WithTopBot.coe_ne_bot μStar))
          (.inl (WithTopBot.coe_ne_top μStar))).2
          (by simpa [add_comm] using hx')
    simpa [Function.toWithTopBot, sub_eq_add_neg, WithTopBot.sub_eq_add_neg] using hx''

/-- Theorem 16.5.1: the Fenchel conjugate of `conv {f_i | i ∈ I}`, represented by
`conv(⨅ i, f i)`, is the pointwise supremum of the individual conjugates. The source assumption
that each `f_i` is proper convex is redundant for this identity. -/
theorem convexConjugate_conv_iInf_eq_iSup (f : I → X → WithTopBot 𝕜) :
    (conv(⨅ i : I, f i))⋆ = (⨆ i : I, (f i)⋆) := by
  classical
  let hHull := Function.isGreatest_conv_iInf_minorant f
  have hHull_le_iInf : conv(⨅ i : I, f i) ≤ ⨅ i : I, f i := hHull.1.2
  have hHull_le : ∀ i : I, conv(⨅ i : I, f i) ≤ f i := le_iInf_iff.mp hHull_le_iInf
  have hHull_greatest :
      ∀ {g : X → WithTopBot 𝕜},
        Function.IsConvex 𝕜 g → (∀ i : I, g ≤ f i) → g ≤ conv(⨅ i : I, f i) :=
    fun hg_convex hg_le ↦ hHull.2 ⟨hg_convex, le_iInf_iff.mpr hg_le⟩
  funext xStar
  rw [iSup_apply]
  simpa using
    (iSup_eq_of_forall_le_of_forall_lt_exists_gt
      (fun i ↦
        (convexConjugate_le_convexConjugate_of_le (hHull_le i)) xStar)
      (fun w hw ↦ by
        rcases WithTopBot.exists_between_coe_of_lt hw with ⟨μStar, hwμ, hμhull⟩
        by_contra h_exists
        have hno_gt : ∀ i : I, (f i)⋆ xStar ≤ w := by
          intro i
          by_contra hi
          exact h_exists ⟨i, lt_of_not_ge hi⟩
        have hfamily_le : ∀ i : I, (f i)⋆ xStar ≤ (μStar : WithTopBot 𝕜) :=
          fun i ↦ (hno_gt i).trans hwμ.le
        have h_affine_convex :
            Function.IsConvex 𝕜
              (fun x : X ↦ ((⟪x, xStar⟫ₚ - μStar : 𝕜) : WithTopBot 𝕜)) := by
          simpa [Function.IsConvex, convexOn_iff_convex_epigraph, Set.mem_univ] using
            (LinearMap.convexOn (HasLinearPairing.pairingLinear.flip xStar) convex_univ).sub
              (convexOn_const μStar convex_univ)
        have hminorant :
            (fun x : X ↦ ((⟪x, xStar⟫ₚ - μStar : 𝕜) : WithTopBot 𝕜)) ≤
              conv(⨅ i : I, f i) := by
          exact hHull_greatest h_affine_convex fun i ↦
            (pairingSubConst_toWithTopBot_le_iff_convexConjugate_le
              (f i) xStar μStar).2
              (hfamily_le i)
        have hconj_le : (conv(⨅ i : I, f i))⋆ xStar ≤ (μStar : WithTopBot 𝕜) :=
          (pairingSubConst_toWithTopBot_le_iff_convexConjugate_le
            (conv(⨅ i : I, f i)) xStar μStar).1 hminorant
        exact (not_le_of_gt hμhull) hconj_le)).symm

end

/-! ### Corollary_16_5_2_1 (from Chap03) -/
universe u v

section

open scoped Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]
variable {I : Sort*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.5.2.1 identifies the polar of the convex hull of a family of
  sets with the intersection of the individual polar sets.
- `core/canonical`: the owner abstractions already present in the project are the source-facing
  set polar `Set.polar : Set X → Set Y` and the convex hull `convexHull 𝕜 (⋃ i, C i)`.
- `bridge/view`: Rockafellar's notation `Cᵒ[𝕜]` is used directly on the theorem surface, while
  `conv {C_i | i ∈ I}` is rendered by `convexHull 𝕜 (⋃ i, C i)`.

Domain-style sampling used here:
- `Set.polar`;
- the scalar-parameterized notation `Cᵒ[𝕜]`;
- `Set.mem_polar_iff`;
- `convexHull_min`.

Primitive data vs derived API:
- primitive input: a family of primal sets `C : I → Set X` with dual points in `Y`, on a
  module/pairing layer equipped with swap compatibility;
- derived output: the polar/intersection identity itself.

Layer target: `source-facing`, stated directly as an equality in the pairing owner layer
`Set X → Set Y`, with no specialization to `ℝ` or self-dual ambient choices. Specializing to
`X = Y` with the canonical self-dual pairing recovers the textbook `R^n` statement. The source
assumption that each `C i` is convex is redundant for this identity and is therefore omitted from
the public statement.
-/

-- Proof sketch: use `Set.mem_polar_iff` for the two inclusions.
-- `⊆`: membership in the polar of the convex hull immediately restricts to each `C i` via
-- `subset_convexHull`.
-- `⊇`: if `xStar` is in every `(C i)ᵒ[𝕜]`, then `⟪xStar, ·⟫ ≤ 1` on the union.
-- Using pairing swap, this says `⟪·, xStar⟫ ≤ 1` on the union. The latter inequality defines a
-- convex half-space, so by `convexHull_min` it holds on `convexHull 𝕜 (⋃ i, C i)`, and swapping
-- back yields membership in the left polar.
/-- Corollary 16.5.2.1: the polar of the convex hull of a family of sets is the intersection of
the individual polars at the pairing owner level `Set X → Set Y`. Specializing `X = Y` with the
canonical self-dual pairing recovers the source `R^n` statement. The source assumption that each
`C i` is convex is redundant for this identity. -/
theorem polar_convexHull_iUnion_eq_iInter_polar
    (C : I → Set X) :
    ((convexHull 𝕜 (⋃ i : I, C i))ᵒ[𝕜] : Set Y) = ⋂ i : I, (C i)ᵒ[𝕜] := by
  ext xStar
  constructor
  · intro hx
    refine Set.mem_iInter.2 ?_
    intro i
    refine Set.mem_polar_iff.2 ?_
    intro x hxCi
    have hxconv : x ∈ convexHull 𝕜 (⋃ j : I, C j) :=
      subset_convexHull 𝕜 (⋃ j : I, C j) <| Set.mem_iUnion.2 ⟨i, hxCi⟩
    exact Set.mem_polar_iff.1 hx x hxconv
  · intro hx
    let H : Set X := {x : X | (⟪x, xStar⟫ₚ : 𝕜) ≤ (1 : 𝕜)}
    have hH_convex : Convex 𝕜 H := by
      intro x hxH y hyH a b ha hb hab
      change (⟪a • x + b • y, xStar⟫ₚ : 𝕜) ≤ (1 : 𝕜)
      have hx1 : (⟪x, xStar⟫ₚ : 𝕜) ≤ (1 : 𝕜) := hxH
      have hy1 : (⟪y, xStar⟫ₚ : 𝕜) ≤ (1 : 𝕜) := hyH
      calc
        (⟪a • x + b • y, xStar⟫ₚ : 𝕜)
            = a * (⟪x, xStar⟫ₚ : 𝕜) + b * (⟪y, xStar⟫ₚ : 𝕜) := by
                simp [HasLinearPairing.pairing_eq_pairingLinear]
        _ ≤ a * (1 : 𝕜) + b * (1 : 𝕜) := by
              exact add_le_add (mul_le_mul_of_nonneg_left hx1 ha)
                (mul_le_mul_of_nonneg_left hy1 hb)
        _ = (1 : 𝕜) := by simpa [mul_one] using hab
    have hUnion_subset : (⋃ i : I, C i) ⊆ H := by
      intro x hxU
      rcases Set.mem_iUnion.1 hxU with ⟨i, hxi⟩
      have hxiPolar : xStar ∈ (C i)ᵒ[𝕜] := (Set.mem_iInter.1 hx) i
      exact (Set.mem_polar_iff_swap (C := C i) (xStar := xStar)).1 hxiPolar x hxi
    have hConv_subset : convexHull 𝕜 (⋃ i : I, C i) ⊆ H :=
      convexHull_min hUnion_subset hH_convex
    refine (Set.mem_polar_iff_swap (C := convexHull 𝕜 (⋃ i : I, C i)) (xStar := xStar)).2 ?_
    intro z hz
    exact hConv_subset hz

end

/-! ### Corollary_16_5_2_2 (from Chap03) -/
universe u v

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y]
variable [Module 𝕜 Y] [ContinuousConstSMul 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasLinearPairing Y X 𝕜]
variable [HasPairingSwap X Y 𝕜]

variable {I : Sort*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.5.2.2 identifies the polar of the intersection of the closures
  `closure (C i)` with the closure of the convex hull of the individual polars.
- `core/canonical`: the owner layer is scalar/pairing-generic, with the closed-convex bipolar
  bridge used internally.
--/

-- Proof sketch: apply Corollary 16.5.2.1 in the dual orientation to the family `(K i)ᵒ[𝕜]`
-- to compute the dual polar of `closure (convexHull 𝕜 (⋃ i, (K i)ᵒ[𝕜]))`. Then rewrite each
-- double polar by the closed-convex bipolar bridges on `X` and `Y`, and apply the `Y`-side bridge
-- once more to the closed convex set `closure (convexHull 𝕜 (⋃ i, (K i)ᵒ[𝕜]))`, which contains
-- `0` because the family is nonempty and every polar set contains `0`.
/-- Corollary 16.5.2.2 at the scalar/pairing owner layer: for a nonempty family of closed convex
sets containing `0`, the polar of their intersection equals the closure of the convex hull of
their individual polars. -/
theorem polar_iInter_eq_closure_convexHull_iUnion_polar
    (hbipolarX : ∀ {S : Set X}, IsClosed S → Convex 𝕜 S → (0 : X) ∈ S →
      (((Sᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) = S))
    (hbipolarY : ∀ {S : Set Y}, IsClosed S → Convex 𝕜 S → (0 : Y) ∈ S →
      (((Sᵒ[𝕜] : Set X)ᵒ[𝕜] : Set Y) = S))
    (hpolar_closureY : ∀ S : Set Y,
      (((closure S)ᵒ[𝕜] : Set X) = (Sᵒ[𝕜] : Set X)))
    (K : I → Set X) (hI : Nonempty I) (hK_closed : ∀ i, IsClosed (K i))
    (hK_convex : ∀ i, Convex 𝕜 (K i)) (h0K : ∀ i, (0 : X) ∈ K i) :
    ((⋂ i, K i)ᵒ[𝕜] : Set Y) = closure (convexHull 𝕜 (⋃ i, (K i)ᵒ[𝕜])) := by
  let U : Set Y := ⋃ i, (K i)ᵒ[𝕜]
  let Q : Set Y := convexHull 𝕜 U
  let P : Set Y := closure Q
  letI : HasPairingSwap Y X 𝕜 :=
    ⟨fun y x => (HasPairingSwap.pairing_swap (x := x) (y := y)).symm⟩
  have hdouble : ∀ i,
      (((K i)ᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) = K i :=
    fun i ↦ hbipolarX (hK_closed i) (hK_convex i) (h0K i)
  have hQ_polar :
      (Qᵒ[𝕜] : Set X) = ⋂ i, (((K i)ᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) := by
    unfold Q U
    simpa using
      (polar_convexHull_iUnion_eq_iInter_polar (𝕜 := 𝕜)
        (C := fun i ↦ ((K i)ᵒ[𝕜] : Set Y)))
  have hP_polar : (Pᵒ[𝕜] : Set X) = ⋂ i, K i := by
    have hP_closure :
        (Pᵒ[𝕜] : Set X) = (Qᵒ[𝕜] : Set X) := by
      unfold P
      exact hpolar_closureY Q
    calc
      (Pᵒ[𝕜] : Set X) = (Qᵒ[𝕜] : Set X) := hP_closure
      _ = ⋂ i, (((K i)ᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) := hQ_polar
      _ = ⋂ i, K i := by
        simp [hdouble]
  have h0polar : ∀ i, (0 : Y) ∈ (K i)ᵒ[𝕜] := by
    intro i
    refine (Set.mem_polar_iff (C := K i) (xStar := (0 : Y))).2 ?_
    intro x hx
    simp [zero_le_one]
  have hP_zero : (0 : Y) ∈ P := by
    rcases hI with ⟨i0⟩
    have h0U : (0 : Y) ∈ U := Set.mem_iUnion.2 ⟨i0, h0polar i0⟩
    have h0Q : (0 : Y) ∈ Q := subset_convexHull 𝕜 U h0U
    simpa [P] using (subset_closure h0Q)
  have hQ_convex : Convex 𝕜 Q := by
    simpa [Q] using (convex_convexHull 𝕜 U)
  have hP_convex : Convex 𝕜 P := by
    simpa [P] using hQ_convex.closure
  have hPP : (((Pᵒ[𝕜] : Set X)ᵒ[𝕜] : Set Y) = P) :=
    hbipolarY isClosed_closure hP_convex hP_zero
  calc
    ((⋂ i, K i)ᵒ[𝕜] : Set Y) = (((Pᵒ[𝕜] : Set X)ᵒ[𝕜] : Set Y)) := by
          rw [hP_polar]
    _ = P := hPP
    _ = closure (convexHull 𝕜 (⋃ i, (K i)ᵒ[𝕜])) := by rfl

-- Proof sketch: apply the owner theorem above to the closed family `fun i ↦ closure (C i)` and
-- use `hpolar_closureX` to remove the redundant closure inside each primal polar.
/-- Corollary 16.5.2.2, source-facing closure form: for a nonempty family of convex sets whose
closures contain `0`, the polar of `⋂ i, closure (C i)` equals
`closure (convexHull 𝕜 (⋃ i, (C i)ᵒ[𝕜]))`. -/
theorem polar_iInter_closure_eq_closure_convexHull_iUnion_polar_of_convex
    [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
    (hbipolarX : ∀ {S : Set X}, IsClosed S → Convex 𝕜 S → (0 : X) ∈ S →
      (((Sᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) = S))
    (hbipolarY : ∀ {S : Set Y}, IsClosed S → Convex 𝕜 S → (0 : Y) ∈ S →
      (((Sᵒ[𝕜] : Set X)ᵒ[𝕜] : Set Y) = S))
    (hpolar_closureX : ∀ S : Set X,
      (((closure S)ᵒ[𝕜] : Set Y) = (Sᵒ[𝕜] : Set Y)))
    (hpolar_closureY : ∀ S : Set Y,
      (((closure S)ᵒ[𝕜] : Set X) = (Sᵒ[𝕜] : Set X)))
    (C : I → Set X) (hI : Nonempty I) (hC_convex : ∀ i, Convex 𝕜 (C i))
    (h0C : ∀ i, (0 : X) ∈ closure (C i)) :
    ((⋂ i, closure (C i))ᵒ[𝕜] : Set Y) = closure (convexHull 𝕜 (⋃ i, (C i)ᵒ[𝕜])) := by
  simpa [hpolar_closureX] using
    polar_iInter_eq_closure_convexHull_iUnion_polar
      hbipolarX hbipolarY hpolar_closureY
      (fun i ↦ closure (C i)) hI (fun _ ↦ isClosed_closure)
      (fun i ↦ (hC_convex i).closure) h0C

end

/-! ### Theorem_16_5_2 (from Chap03) -/
universe u v

section

open scoped Rockafellar

variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable {I : Sort v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.5.2 identifies the conjugate of the pointwise supremum of the
  closures `cl fᵢ` with the closure of the convex hull of the conjugates `fᵢ*`.
- `core/canonical`: the project owner constructions are `convexConjugate`,
  `lowerSemicontinuousHull`, and the family convex-hull owner `conv(⨅ i, f i)`.
- `bridge/view`: Rockafellar's `sup {cl fᵢ | i ∈ I}` is rendered by the pointwise supremum
  `⨆ i, cl(f i)`, while `cl (conv {fᵢ* | i ∈ I})` is rendered by
  `cl(conv(⨅ i, (f i)⋆))`.

Domain-style sampling used here:
- `convexConjugate_conv_iInf_eq_iSup`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`;
- `Function.isGreatest_conv_iInf_minorant`;
- `lowerSemicontinuousHull`;
- `conv`.

Primitive data vs derived API:
- primitive inputs: an indexed family `f : I → E → WithBotTop 𝕜`;
- source-essential hypothesis: each `f i` is convex, which is needed to identify `fᵢ**` with
  `cl fᵢ`;
- derived API: the conjugacy identity between the supremum of the closures and the closure of the
  convex hull of the conjugates.

Layer target: `source-facing`, stated directly through the existing owner constructions. The source
properness assumption is redundant for this identity, but convexity is not. The source's `R^n`
wording is rendered on the canonical finite-dimensional scalar-field owner layer with continuous
linear self-pairing. The codomain surface is the chapter's canonical `WithBotTop 𝕜` layer.
-/

-- Proof sketch: apply Theorem 16.5.1 to the family `fun i ↦ convexConjugate (f i)` to get
-- `(conv {fᵢ*})* = ⨆ i, fᵢ**`, rendered as `(conv(⨅ i, (f i)⋆))⋆ = ⨆ i, ((f i)⋆)⋆`.
-- Use Theorem 12.2 to rewrite each `fᵢ**` as
-- `lowerSemicontinuousHull (f i)` under the convexity hypothesis. Then apply Theorem 12.2 again
-- to the convex function `conv(⨅ i, (f i)⋆)`, whose
-- biconjugate is the lower-semicontinuous hull of `conv {fᵢ*}`.
/-- Theorem 16.5.2: for a family of convex functions on a finite-dimensional scalar-field space
equipped with a continuous linear self-pairing, the conjugate of the pointwise supremum of the
closures `cl f_i`, represented here by `⨆ i, cl(f i)`, is the closure of the convex hull of the
conjugates `f_i*`, represented here as `cl (conv(⨅ i, (f i)⋆))`. The source properness assumption
is redundant for this identity. -/
theorem
    convexConjugate_iSup_cl_eq_cl_conv_iInf_convexConjugate_of_convex
    (f : I → E → WithBotTop 𝕜) (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    ((⨆ i, cl(f i))⋆ : E → WithBotTop 𝕜) = cl(conv(⨅ i, (f i)⋆)) := by
  let g : I → E → WithBotTop 𝕜 := fun i ↦ (f i)⋆
  have hcl : ∀ i : I, cl(f i) = (f i)⋆⋆ := by
    intro i
    simpa using ((hf_convex i).biconjugate_eq_lowerSemicontinuousHull).symm
  have hconj :
      (conv(⨅ i : I, g i))⋆ = (⨆ i : I, (f i)⋆⋆) := by
    simpa [g] using
      (convexConjugate_conv_iInf_eq_iSup (f := g))
  have hiSup_cl :
      (⨆ i : I, cl(f i)) = (conv(⨅ i : I, g i))⋆ := by
    calc
      (⨆ i : I, cl(f i)) = (⨆ i : I, (f i)⋆⋆) := by
        simp [hcl]
      _ = (conv(⨅ i : I, g i))⋆ := by
        simpa using hconj.symm
  have hconvex : (conv(⨅ i : I, g i)).IsConvex 𝕜 :=
    (Function.isGreatest_conv_iInf_minorant g).1.1
  calc
    (⨆ i : I, cl(f i))⋆ = ((conv(⨅ i : I, g i))⋆)⋆ := by
      rw [hiSup_cl]
    _ = cl(conv(⨅ i : I, g i)) := by
      simpa using hconvex.biconjugate_eq_lowerSemicontinuousHull
    _ = cl(conv(⨅ i : I, (f i)⋆)) := by
      simp [g]

end

/-! ### Theorem_16_5_3 (from Chap03) -/
open scoped BigOperators Rockafellar

noncomputable section

universe u v

section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [CompleteSpace 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
variable [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable {ι : Type v} [Finite ι]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.5.3 identifies the conjugate of the pointwise supremum of a finite
  family of proper convex functions with the convex hull of the conjugate family, under pairwise
  equality of closure of effective domains. It also gives the convex-combination infimum formula
  and the corresponding attainment statement (with nonempty index type for attainment).
- `core/canonical`: the owner abstractions already present are Theorem 16.5.2 for the closed-side
  conjugacy identity, Corollary 9.8.3.1 for the common-recession-function closedness/attainment
  package of `conv(⨅ i, g i)`, and Theorem 5.6 for the canonical owner
  `Function.convexCombinationValues`.
- `bridge/view`: Rockafellar's `sup {f_i}` is rendered by `⨆ i, f i`; the common-closure
  hypothesis on `cl (dom f_i)` is written directly with the chapter effective-domain notation
  `dom(f i)`; and the common-closure assumption is converted into the owner-side common recession
  function of the conjugate family through Theorem 13.3 together with `supportFunction_closure`.

Domain-style sampling used here:
- `convexConjugate_iSup_cl_eq_cl_conv_iInf_convexConjugate_of_convex`;
- `lowerSemicontinuous_convexHull_iInf_of_pairwise_recessionFunction`;
- `exists_finite_convex_combination_eq_convexHull_iInf_of_pairwise_recessionFunction`;
- `supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate`;
- `supportFunction_closure`;
- `Function.convexHull_iInf_apply_eq_sInf_convexCombination_values`.

Primitive data vs derived API:
- primitive inputs: a finite family `f : ι → E → WithBotTop 𝕜`, convexity and
  properness of each `f i`, and the pairwise common-closure condition
  `Pairwise (fun i j ↦ closure dom(f i) = closure dom(f j))`;
- derived API: the conjugacy identity, the convex-combination infimum formula for the conjugate of
  the supremum, and the corresponding attainment statement.

Layer target: `source-facing`, stated directly through the canonical owner
`conv(⨅ i, (f i)⋆)` and Fenchel conjugation on the pairing owner layer, with no extra wrapper
around the family or around the common-domain hypothesis. The finite-convex-combination
companions are kept in the canonical owner interface
`Function.convexCombinationValues`.
-/

-- Proof sketch: Theorem 16.5.2 gives the identity for `⨆ i, lowerSemicontinuousHull (f i)`. The
-- common closure-of-domain hypothesis lets Theorem 9.4 identify
-- `lowerSemicontinuousHull (⨆ i, f i)`
-- with that supremum of closures. On the dual side, Theorem 13.3 identifies the recession
-- function of each `convexConjugate (f i)` with `supportFunction dom(f i)`, and
-- `supportFunction_closure` turns the pairwise common-closure hypothesis into pairwise equality
-- of recession functions.
-- Corollary 9.8.3.1 therefore shows that `conv(⨅ i, (f i)⋆)` is already lower semicontinuous, so
-- the closure on the right side of Theorem 16.5.2 drops out.
/-- Theorem 16.5.3 (1): if a finite family `fᵢ` of proper convex functions on a
finite-dimensional scalar-field pairing space has pairwise-equal closures of effective domains,
then the conjugate of its pointwise supremum is the convex hull of the conjugate family. -/
theorem convexConjugate_iSup_eq_conv_iInf_convexConjugate_of_pairwise_closure_dom
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_closure :
      Pairwise (fun i j : ι => closure (dom(f i)) = closure (dom(f j)))) :
    ((⨆ i, f i)⋆ : E → WithBotTop 𝕜) = conv(⨅ i, (f i)⋆) := sorry

-- Proof sketch: combine clause (1) with Theorem 5.6 at owner level,
-- `Function.convexHull_iInf_apply_eq_sInf_convexCombination_values`, applied to
-- `fun i ↦ (f i)⋆`.
/-- Theorem 16.5.3 (2): under the same hypotheses, for each `x⋆` the value of
`(sup_i f_i)⋆(x⋆)` is the infimum over canonical convex-combination values of the conjugate
family owner `⨅ i, (f i)⋆`. -/
theorem convexConjugate_iSup_apply_eq_sInf_convexCombinationValues_of_pairwise_closure_dom
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_closure :
      Pairwise (fun i j : ι => closure (dom(f i)) = closure (dom(f j))))
    (xStar : E) :
    ((⨆ i, f i)⋆ : E → WithBotTop 𝕜) xStar =
      sInf (Function.convexCombinationValues (⨅ i, (f i)⋆) xStar) := sorry

-- Proof sketch: by Theorem 13.3 and `supportFunction_closure`, the conjugate family has pairwise
-- equal recession functions because the closures `closure dom(f i)` agree pairwise.
-- Corollary 9.8.3.1 then applies directly to the family `fun i ↦ (f i)⋆`, producing a witness in
-- `Function.convexCombinationValues (⨅ i, (f i)⋆) x⋆` for the value `conv(⨅ i, (f i)⋆) x⋆`.
-- Clause (1) identifies that value with `(⨆ i, f i)⋆ x⋆`.
/-- Theorem 16.5.3 (3): under the same hypotheses, for every `x⋆` the infimum in clause (2) is
attained, expressed canonically by membership in
`Function.convexCombinationValues (⨅ i, (f i)⋆) x⋆`. -/
theorem convexConjugate_iSup_apply_mem_convexCombinationValues_of_pairwise_closure_dom
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper)
    (h_pairwise_closure :
      Pairwise (fun i j : ι => closure (dom(f i)) = closure (dom(f j))))
    [Nonempty ι] (xStar : E) :
    ((⨆ i, f i)⋆ : E → WithBotTop 𝕜) xStar ∈
      Function.convexCombinationValues (⨅ i, (f i)⋆) xStar := sorry

end
