import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_38_7_1 (from Chap08) -/
/-!
Corollary 38.7.1 is already owned upstream by
`ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_7_1`.

Layer triage:
- `source-facing`: the textbook corollary is the fixed-dual-point specialization of the Chapter 38
  image/adjoint duality bridge.
- `core/canonical`: the owner declarations are
  `Bifunction.hasInnerProduct_adjointFunction_of_common_riDom` and
  `Bifunction.convexConjugate_image_eq_innerProduct_adjointFunction_of_common_riDom`.
- `bridge/view`: this file contributes only the source label, so it should be a pure recall bridge
  rather than a second local theorem family specialized to the self-dual `EReal` setting.

Primitive data vs derived API:
- primitive owner layer: `Bifunction.image`, `Bifunction.adjoint`, `Function.HasInnerProduct`, and
  `Function.innerProduct`, already used directly by the owner file;
- derived API here: none beyond re-exposing the existing canonical owner theorems under the
  textbook item label.
-/

/- Corollary 38.7.1, existence clause: reuse the canonical owner theorem directly. -/
recall Bifunction.hasInnerProduct_adjointFunction_of_common_riDom

/- Corollary 38.7.1, equality clause: reuse the canonical owner theorem directly. -/
recall Bifunction.convexConjugate_image_eq_innerProduct_adjointFunction_of_common_riDom

/-! ### Definition_38_7_1 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u} {XStar : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X]
variable [Neg UStar] [HasPairing U UStar 𝕜]
variable [HasPairing X XStar 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: despite the legacy file name, this item is Rockafellar's Corollary 38.7.1. For
  a fixed `x⋆`, it specializes the Chapter 38 image/adjoint duality to the statement that the
  pairing `(f, F⋆ x⋆)` exists and that `(Ff, x⋆) = (f, F⋆ x⋆)`.
- `core/canonical`: the owner abstractions already present upstream are `Function.innerProduct`
  and `Function.HasInnerProduct` from `Definition_38_5_2`, together with the Chapter 38 image
  owner `Bifunction.image`, the adjoint owner `Bifunction.adjoint`, the slice-domain owner
  `Bifunction.dom`, and Fenchel conjugation `f⋆`.
  evaluation `(image F f)⋆ xStar`. Likewise `F⋆ x⋆` is the existing adjoint slice
  `adjoint XStar UStar F xStar`.

Primary mathematical domain:
- Fenchel pairings between a convex image `image F f` and fixed adjoint slices of a convex
  bifunction.

Domain-style sampling used here:
- `Function.innerProduct` and `Function.HasInnerProduct` from `Definition_38_5_2`;
- `Bifunction.image_apply_eq_iInf_sub_inverse` from `Definition_38_3_1`;
- `Bifunction.adjoint` from `Lemma_31_0_8`;
- `Bifunction.dom` / `Bifunction.IsProper` from `Theorem_38_1`.

Primitive data vs derived API:
- primitive inputs: a bifunction `F : U → X → WithBotTop 𝕜`, a function
  `f : U → WithBotTop 𝕜`, and a dual point `xStar : XStar`;
- primitive owner layer already upstream: `image F f`, `adjoint XStar UStar F xStar`,
  `image_apply_eq_iInf_sub_inverse`, `Function.innerProduct`, and
  `Function.HasInnerProduct`;
- primitive hypothesis layer used here: convexity of the graph function `Function.uncurry F`,
  properness of `F`, convexity/properness of `f`, and the common-relative-interior condition
  `(riDom[𝕜](f) ∩ ri[𝕜](dom F)).Nonempty`;
- derived API in this file: existence of the pairing with the adjoint slice, and the equality
  between that pairing and the conjugate evaluation of `image F f`.

Layer target: `bridge/view`. The source corollary is recorded directly in the existing owner
language, without introducing a new wrapper for pairings with a dual vector.

-/

/- The inverse-slice evaluation formula for `image` is already owned by
`Bifunction.image_apply_eq_iInf_sub_inverse`; this file only records the Chapter 38.7.1 pairing
reformulation on top of that owner layer. -/
recall Bifunction.image_apply_eq_iInf_sub_inverse

variable (F : U → X → WithBotTop 𝕜) (f : U → WithBotTop 𝕜)

/-- Corollary 38.7.1, existence clause at the `WithBotTop 𝕜` pairing layer: if `F` is convex and
proper, `f` is convex and proper, and `riDom[𝕜](f)` meets `ri[𝕜](dom F)`, then the pairing of `f`
with the adjoint slice `adjoint XStar UStar F xStar` exists for every `xStar`. -/
theorem hasInnerProduct_adjointFunction_of_common_riDom
    (hF_convex : (Function.uncurry F).IsConvex 𝕜) (hF_proper : IsProper F)
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hri : (riDom[𝕜](f) ∩ ri[𝕜](dom F)).Nonempty)
    (xStar : XStar) :
    Function.HasInnerProduct f (adjoint XStar UStar F xStar : UStar → WithBotTop 𝕜) := by
  sorry

/-- Corollary 38.7.1, equality clause in owner form: the source notation `(Ff, x⋆)` is the
conjugate value `(image F f)⋆ xStar`, so for every `xStar` one has
`(image F f)⋆ xStar = Function.innerProduct f (adjoint XStar UStar F xStar)` under the same
convexity/properness and common-relative-interior hypotheses. -/
theorem convexConjugate_image_eq_innerProduct_adjointFunction_of_common_riDom
    (hF_convex : (Function.uncurry F).IsConvex 𝕜) (hF_proper : IsProper F)
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hri : (riDom[𝕜](f) ∩ ri[𝕜](dom F)).Nonempty)
    (xStar : XStar) :
    (image F f)⋆ xStar =
      Function.innerProduct f (adjoint XStar UStar F xStar : UStar → WithBotTop 𝕜) := by
  sorry

end

end Bifunction

/-! ### Corollary_38_7_2 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {Y : Type w}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [HasLinearPairing Y Y ℝ] [HasContinuousPairing Y Y ℝ]
variable {F : U → X → EReal} {G : X → Y → EReal}

local notation "ri(" C ")" => intrinsicInterior ℝ C
local notation "F⋆" => adjoint X U F
local notation "G⋆" => adjoint Y X G

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 38.7.2 identifies the three source terms
  `⟨GFu, y⋆⟩`, `⟨Fu, G⋆ y⋆⟩`, and `⟨u, F⋆ G⋆ y⋆⟩` under the regularity hypothesis
  `ri(dom F⋆) ∩ ri(dom G) ≠ ∅` and the slice qualification `u ∈ ri(dom (comp G F))`.
- `core/canonical`: the owner layer already present in the chapter is `Bifunction.comp`,
  `Bifunction.adjoint`, `Bifunction.dom`, and the Chapter 33 convex-pairing notation
  `⟪·, ·⟫ᶠ`.
- `bridge/view`: the two atomic equalities in the source chain are stated directly here on the
  existing owner layer, while the proof route still reuses Corollary 38.7.1's image/adjoint
  pairing bridge and Theorem 38.5's product-adjoint identity.

Primary mathematical domain:
- composition of proper convex bifunctions and slice-wise Fenchel pairings.

Domain-style sampling used here:
- `Bifunction.comp` and the adjoint identity theorems from `Theorem_38_5`;
- the Chapter 33 source-facing convex-pairing notation `⟪f, y⟫ᶠ` from
  `Definition33_0_8`;
- Corollary 38.7.1 in `Definition_38_7_1`, which already owns the slice-wise bridge between
  a bifunction image conjugate and the Chapter 38 inner-product owner.

Primitive data vs derived API:
- primitive inputs: proper convex bifunctions `F` and `G`, a primal point `u`, and a dual point
  `yStar`;
- primitive owner hypotheses: convexity and properness of `F` and `G`, the common-relative-
  interior hypothesis on `dom F⋆` and `dom G`, and the slice qualification
  `u ∈ ri(dom (comp G F))`;
- derived API: the two source-facing atomic equalities
  `⟨GFu, y⋆⟩ = innerProduct(Fu, G⋆ y⋆)` and
  `innerProduct(Fu, G⋆ y⋆) = ⟨u, F⋆ G⋆ y⋆⟩`, together with the transitive outer equality as a
  companion consequence.

Layer target: `source-facing`, using the existing Chapter 38 owners directly rather than
introducing a separate “composition pairing data” wrapper.
-/

-- Proof sketch: the source middle equality `⟨GFu, y^*⟩ = ⟨Fu, G^* y^*⟩` is the Chapter 38.7.1
-- image/adjoint bridge specialized to the slice pair `(F u, G)`, where the middle term is the
-- Chapter 38 owner `Function.innerProduct (F u) (G⋆ yStar)`. The second equality then reads that
-- same owner through Theorem 38.5's identity `(GF)^* = F^* G^*`.
variable
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F)) (hF_proper : IsProper F)
    (hG_convex : Function.IsConvex ℝ (Function.uncurry G)) (hG_proper : IsProper G)
    (hri : (ri(dom (adjoint X U F)) ∩ ri(dom G)).Nonempty)

include hF_convex hF_proper hG_convex hG_proper hri

/-- Corollary 38.7.2, first source edge: under the common-relative-interior hypothesis and
`u ∈ ri (dom (GF))`, the pairing `⟨GFu, y^*⟩` agrees with the Chapter 38 inner-product owner
`Function.innerProduct (F u) (G^* y^*)`. -/
theorem convexPairing_comp_slice_eq_innerProduct_adjointFunction_slice_of_mem_riDom_comp
    (u : U) (hu : u ∈ ri(dom (comp G F))) (yStar : Y) :
    ⟪comp G F u, yStar⟫ᶠ = Function.innerProduct (F u) (G⋆ yStar) := by
  sorry

/-- Corollary 38.7.2, second source edge: the Chapter 38 middle term
`Function.innerProduct (F u) (G^* y^*)` is the pairing `⟨u, F^* G^* y^*⟩`. -/
theorem innerProduct_adjointFunction_slice_eq_convexPairing_comp_adjoint_slice_of_mem_riDom_comp
    (u : U) (hu : u ∈ ri(dom (comp G F))) (yStar : Y) :
    Function.innerProduct (F u) (G⋆ yStar) = ⟪u, comp F⋆ G⋆ yStar⟫ᶠ := by
  sorry

/-- Corollary 38.7.2, transitive companion: the first and third source pairings coincide. -/
theorem convexPairing_comp_slice_eq_convexPairing_comp_adjoint_slice_of_mem_riDom_comp
    (u : U) (hu : u ∈ ri(dom (comp G F))) (yStar : Y) :
    ⟪comp G F u, yStar⟫ᶠ =
      ⟪u, comp F⋆ G⋆ yStar⟫ᶠ := by
  exact
    (convexPairing_comp_slice_eq_innerProduct_adjointFunction_slice_of_mem_riDom_comp
      hF_convex hF_proper hG_convex hG_proper hri u hu yStar).trans
      (innerProduct_adjointFunction_slice_eq_convexPairing_comp_adjoint_slice_of_mem_riDom_comp
        hF_convex hF_proper hG_convex hG_proper hri u hu yStar)

end

end Bifunction

/-! ### Proposition_38_7_2 (from Chap08) -/
noncomputable section

universe u v u' v' w

open scoped Rockafellar

namespace Bifunction

section Owner

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L] [InfSet L]
variable [Neg UStar]
variable [HasPairing U UStar L] [HasPairing X XStar L]
variable [HasPairing (U × X) (UStar × XStar) L]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.7.2 studies co-finite convex bifunctions through the global
  agreement of the two Chapter 34 pairing representatives attached to `F`.
- `core/canonical`: the upstream owner layer already provides the global pairing owners
  `Bifunction.lowerPairing` and `Bifunction.upperAdjointPairing`, together with the pointwise
  owner `Bifunction.PairingEquationAt`, the adjoint owner `Bifunction.adjoint`, the
  slice-domain owner `Bifunction.dom`, and the closed-convex owner `Bifunction.IsClosedConvex`.
- `bridge/view`: this file owns only the source-facing property owner `Bifunction.IsCofinite`,
  whose primitive field is the canonical global owner equality
  `lowerPairing XStar F = upperAdjointPairing XStar UStar F`; the universal Chapter 33
  pairing-equation formulation is derived API.

Primary mathematical domain:
- convex bifunction duality and co-finiteness via adjoint-slice pairings.

Domain-style sampling used here:
- `Bifunction.lowerPairing` and `Bifunction.upperAdjointPairing` from `Chap07.Defn_34_2`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`;
- `Bifunction.PairingEquationAt` from `Chap07.Definition33_0_31`;
- `Bifunction.dom` from `Chap06.Definition_6_29_8`;
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → L`;
- primitive global owners reused here: `Bifunction.lowerPairing XStar F` and
  `Bifunction.upperAdjointPairing XStar UStar F`;
- primitive global owner introduced here: the reusable property class
  `Bifunction.IsCofinite XStar UStar F`, defined directly by equality of those two canonical
  pairing maps and keeping the dual ambient types explicit because they are not recoverable from
  `F` alone;
- derived pointwise API: `Bifunction.PairingEquationAt F u xStar`;
- derived API: adjoint stability of co-finiteness, the graph-properness bridge needed by
  Section 38.2, and the closed-convex/full-domain characterization.

Layer target: `source-facing`.
-/

/-- A convex bifunction is co-finite when its two canonical Chapter 34 pairing representatives
agree globally. -/
@[mk_iff isCofinite_iff]
class IsCofinite (XStar : Type v') (UStar : Type u')
    [Neg UStar] [HasPairing U UStar L] [HasPairing X XStar L]
    [HasPairing (U × X) (UStar × XStar) L] (F : U → X → L) : Prop where
  lowerPairing_eq_upperAdjointPairing :
    lowerPairing XStar F = upperAdjointPairing XStar UStar F

/-- The global Chapter 34 owner equality defining co-finiteness specializes pointwise to the
Chapter 33 pairing equation. -/
theorem IsCofinite.pairingEquationAt {F : U → X → L} (hF : IsCofinite XStar UStar F)
    (u : U) (xStar : XStar) :
    PairingEquationAt F u xStar := by
  simpa [PairingEquationAt, lowerPairing_apply, upperAdjointPairing_apply] using
    congrFun (congrFun hF.lowerPairing_eq_upperAdjointPairing u) xStar

/-- Companion pointwise form of co-finiteness: the canonical global owner equality is equivalent
to the universal Chapter 33 pairing equation. -/
theorem isCofinite_iff_forall_pairingEquationAt {F : U → X → L} :
    IsCofinite XStar UStar F ↔ ∀ u : U, ∀ xStar : XStar, PairingEquationAt F u xStar := by
  constructor
  · intro hF u xStar
    exact hF.pairingEquationAt u xStar
  · intro hF
    rw [isCofinite_iff XStar UStar F]
    funext u xStar
    simpa [PairingEquationAt, lowerPairing_apply, upperAdjointPairing_apply] using hF u xStar

end Owner

section Adjoint

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L] [InfSet L]
variable [Neg UStar] [Neg X]
variable [HasPairing U UStar L] [HasPairing X XStar L]
variable [HasPairing UStar U L] [HasPairing XStar X L]
variable [HasPairing (U × X) (UStar × XStar) L]
variable [HasPairing (XStar × UStar) (X × U) L]

-- Proof sketch: invoke the Chapter 33 symmetry theorem pointwise on the adjoint slices, then
-- reassemble the resulting equations into the canonical owner equality
-- `lowerPairing = upperAdjointPairing`.
/-- The adjoint of a co-finite convex bifunction is again co-finite. -/
theorem isCofinite_adjointFunction_of_isCofinite
    {F : U → X → L} (hF : IsCofinite XStar UStar F) :
    IsCofinite U X (adjoint XStar UStar F) := by
  sorry

end Adjoint

section Characterization

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup UStar] [NormedSpace ℝ UStar] [FiniteDimensional ℝ UStar]
variable [NormedAddCommGroup XStar] [NormedSpace ℝ XStar] [FiniteDimensional ℝ XStar]
variable [HasLinearPairing U UStar ℝ] [HasContinuousPairing U UStar ℝ]
variable [HasLinearPairing X XStar ℝ] [HasContinuousPairing X XStar ℝ]
variable {F : U → X → WithBotTop ℝ}

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithBotTop ℝ)

-- Proof sketch: Proposition 38.7.2 forces `dom F = Set.univ`, so the graph function has a
-- finite point over `u = 0`, while the Chapter 33 pairing equation rules out any `⊥`-value on
-- the graph. This is exactly the graph-properness owner reused by Theorem 38.2.
/-- Bridge/view lemma for Proposition 38.7.3: a closed convex co-finite bifunction has proper
graph function in the Chapter 6 owner sense `(Function.uncurry F).IsProper`. -/
theorem uncurry_isProper_of_isClosedConvex_of_isCofinite
    (hF : IsClosedConvex F) (hcof : IsCofinite XStar UStar F) :
    (Function.uncurry F).IsProper := by
  sorry

-- Proof sketch: if `F` is co-finite, the global pairing equation excludes any missing point in
-- either the primal domain or the Chapter 33 adjoint-side source domain `dom (-F⋆)`.
-- Conversely, for a closed convex bifunction, the Chapter 34
-- closure theory upgrades the two full-domain hypotheses to the universal pairing equation.
/-- Proposition 38.7.2: for a closed convex bifunction `F`, co-finiteness is equivalent to the
full-domain conditions on the primal source domain and the adjoint-side source domain, rendered
here in the established Chapter 33/34 owner language as `dom F = Set.univ` and
`dom (-F⋆) = Set.univ`. -/
theorem isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ
    (hF : IsClosedConvex F) :
    IsCofinite XStar UStar F ↔
      dom F = Set.univ ∧
        dom (-F⋆) = Set.univ := by
  sorry

end Characterization

end Bifunction

/-! ### Proposition_38_7_3 (from Chap08) -/
noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]

local notation "ri(" C ")" => intrinsicInterior ℝ C

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.7.3 states that the Chapter 38 infimal convolution of two
  closed convex co-finite bifunctions is again closed convex and co-finite, and that the adjoint
  commutes with this infimal convolution.
- `core/canonical`: the owner abstractions already present upstream are `Bifunction.IsClosedConvex`
  from Chapter 34, the pairing-generic owner `Bifunction.IsCofinite X U` from
  Proposition 38.7.2, the source-facing infimal convolution owner `F₁ D F₂`, and the adjoint
  owner `adjoint X U`, used here directly through the Chapter 6 scoped canonical source
  notation `F⋆`.
- `bridge/view`: this file is the bridge from the co-finite owner hypotheses to the already-owned
  common-`ri(dom)` infimal-convolution theorems of Section 38.2.

Primary mathematical domain:
- convex bifunction duality for infimal convolution in the finite-dimensional self-dual real
  setting.

Domain-style sampling used here:
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`;
- `Bifunction.IsCofinite X U` and
  `Bifunction.isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ`,
  `Bifunction.uncurry_isProper_of_isClosedConvex_of_isCofinite` from
  `Proposition_38_7_2`;
- `Bifunction.isClosedConvex_infimalConvolution_of_common_riDom` from
  `Corollary_38_2_1`;
- `Bifunction.adjointFunction_infimalConvolution_eq_infimalConvolution_\
adjointFunction_of_common_riDom` from `Theorem_38_2`.

Primitive data vs derived API:
- primitive inputs: bifunctions `F₁`, `F₂`;
- primitive owner hypotheses: `IsClosedConvex F₁`, `IsCofinite X U F₁`,
  `IsClosedConvex F₂`, `IsCofinite X U F₂`;
- derived API: closed-convexity and co-finiteness of `F₁ D F₂`, and the adjoint infimal
  convolution identity.

Layer target: `bridge/view`.
-/

variable {F₁ F₂ : U → X → WithBotTop ℝ}

/-- Bridge/view lemma: co-finite closed-convex bifunctions satisfy the common-relative-interior
qualification required by the Section 38.2 infimal-convolution theorems. -/
theorem common_riDom_of_isClosedConvex_of_isCofinite
    (hF₁ : IsClosedConvex F₁) (hcof₁ : IsCofinite X U F₁)
    (hF₂ : IsClosedConvex F₂) (hcof₂ : IsCofinite X U F₂) :
    (ri(dom F₁) ∩ ri(dom F₂)).Nonempty := by
  rcases (isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ hF₁).1 hcof₁ with
    ⟨hdom₁, _⟩
  rcases (isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ hF₂).1 hcof₂ with
    ⟨hdom₂, _⟩
  refine ⟨0, ?_⟩
  constructor <;> simp [hdom₁, hdom₂, intrinsicInterior, AffineSubspace.span_univ]

-- Proof sketch: Proposition 38.7.2 upgrades the co-finite hypotheses on `F₁` and `F₂` to the
-- common-relative-interior qualification owned here by
-- `common_riDom_of_isClosedConvex_of_isCofinite`, so Corollary 38.2.1 applies directly on the
-- canonical owner `IsClosedConvex`.
/-- Proposition 38.7.3, closed-convex clause in owner form: the infimal convolution of two closed
convex co-finite bifunctions is again closed convex. -/
theorem isClosedConvex_infimalConvolution_of_isClosedConvex_of_isCofinite
    (hF₁ : IsClosedConvex F₁) (hcof₁ : IsCofinite X U F₁)
    (hF₂ : IsClosedConvex F₂) (hcof₂ : IsCofinite X U F₂) :
    IsClosedConvex (F₁ D F₂) := by
  have hri :
      (ri(dom F₁) ∩ ri(dom F₂)).Nonempty :=
    common_riDom_of_isClosedConvex_of_isCofinite hF₁ hcof₁ hF₂ hcof₂
  simpa using
    isClosedConvex_infimalConvolution_of_common_riDom hF₁ hF₂ hri

-- Proof sketch: Proposition 38.7.2 upgrades the co-finite hypotheses in two ways: first to the
-- common-relative-interior qualification owned here by
-- `common_riDom_of_isClosedConvex_of_isCofinite`, and second to the graph-properness owner
-- `(Function.uncurry F).IsProper` via
-- `uncurry_isProper_of_isClosedConvex_of_isCofinite`. The exact adjoint identity then comes
-- directly from the qualified Section 38.2 theorem.
/-- Proposition 38.7.3, adjoint clause: under the same closed-convex co-finite hypotheses,
`(F₁ D F₂)⋆ = F₁⋆ D F₂⋆`. -/
theorem
    adjointFunction_infimalConvolution_eq_infimalConvolution_adjoint_of_isClosedConvex_of_isCofinite
    (hF₁ : IsClosedConvex F₁) (hcof₁ : IsCofinite X U F₁)
    (hF₂ : IsClosedConvex F₂) (hcof₂ : IsCofinite X U F₂) :
    adjoint X U (F₁ D F₂) = adjoint X U F₁ D adjoint X U F₂ := by
  have hri :
      (ri(dom F₁) ∩ ri(dom F₂)).Nonempty :=
    common_riDom_of_isClosedConvex_of_isCofinite hF₁ hcof₁ hF₂ hcof₂
  have hF₁_proper : (Function.uncurry F₁).IsProper :=
    uncurry_isProper_of_isClosedConvex_of_isCofinite hF₁ hcof₁
  have hF₂_proper : (Function.uncurry F₂).IsProper :=
    uncurry_isProper_of_isClosedConvex_of_isCofinite hF₂ hcof₂
  simpa using
    adjointFunction_infimalConvolution_eq_infimalConvolution_adjointFunction_of_common_riDom
      hF₁.convex hF₁_proper hF₂.convex hF₂_proper hri

-- Proof sketch: first obtain `IsClosedConvex (F₁ D F₂)` from the preceding theorem and the
-- adjoint identity
-- `adjoint X U (F₁ D F₂) = adjoint X U F₁ D adjoint X U F₂` from the
-- local bridge theorem above. Then Proposition 38.7.2 characterizes co-finiteness by full primal
-- domain and full `dom (-F⋆)`, and those domain equalities are driven by the
-- same bridge
-- `common_riDom_of_isClosedConvex_of_isCofinite`.
/-- Proposition 38.7.3, co-finite clause in owner form: the infimal convolution of two closed
convex co-finite bifunctions is again co-finite. -/
theorem isCofinite_infimalConvolution_of_isClosedConvex_of_isCofinite
    (hF₁ : IsClosedConvex F₁) (hcof₁ : IsCofinite X U F₁)
    (hF₂ : IsClosedConvex F₂) (hcof₂ : IsCofinite X U F₂) :
    IsCofinite X U (F₁ D F₂) := by
  have hclosed : IsClosedConvex (F₁ D F₂) :=
    isClosedConvex_infimalConvolution_of_isClosedConvex_of_isCofinite hF₁ hcof₁ hF₂ hcof₂
  have hadj :
      adjoint X U (F₁ D F₂) = adjoint X U F₁ D adjoint X U F₂ :=
    adjointFunction_infimalConvolution_eq_infimalConvolution_adjoint_of_isClosedConvex_of_isCofinite
      hF₁ hcof₁ hF₂ hcof₂
  rcases (isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ hF₁).1 hcof₁ with
    ⟨hdom₁, hdomAdj₁⟩
  rcases (isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ hF₂).1 hcof₂ with
    ⟨hdom₂, hdomAdj₂⟩
  change dom (-(adjoint X U F₁)) = Set.univ at hdomAdj₁
  change dom (-(adjoint X U F₂)) = Set.univ at hdomAdj₂
  have hF₁_slice_convex : ∀ u, (F₁ u).IsConvex ℝ := hF₁.convex.slice_uncurry
  have hF₂_slice_convex : ∀ u, (F₂ u).IsConvex ℝ := hF₂.convex.slice_uncurry
  have hdom : dom (F₁ D F₂) = Set.univ := by
    rw [dom_infimalConvolution_eq_inter hF₁_slice_convex hF₂_slice_convex, hdom₁, hdom₂,
      Set.univ_inter]
  refine (isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ hclosed).2 ?_
  refine ⟨hdom, ?_⟩
  change dom (-(adjoint X U (F₁ D F₂))) = Set.univ
  sorry

end

end Bifunction

/-! ### Proposition_38_7_4 (from Chap08) -/
noncomputable section

universe u v u' v'

namespace Bifunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.7.4 says that positive scalar rescaling preserves co-finiteness
  for Chapter 38 bifunctions.
- `core/canonical`: the relevant owners are the Chapter 38 rescaling owner `rightScalarMul`, the
  Chapter 38 adjoint-rescaling theorem `adjointFunction_rightScalarMul`, the positive-scalar
  convex-conjugacy owner `convexConjugate_rightScalarMul_eq_left_smul_of_pos`, and the
  bifunction-side co-finiteness owner `Bifunction.IsCofinite XStar UStar` from
  Proposition 38.7.2.
- `bridge/view`: this file adds no new owner; it is a direct preservation theorem for the
  canonical source-facing property.

Domain-style sampling used here:
- `rightScalarMul` from `Definition_38_2_2`;
- `convexConjugate_rightScalarMul_eq_left_smul_of_pos` from `Chap03.Theorem_16_1`,
  reused through the order-dual view `concaveConjugate`;
- `adjointFunction_rightScalarMul` from `Theorem_38_3`;
- `Bifunction.IsCofinite XStar UStar` from `Proposition_38_7_2`.

Primitive data vs derived API:
- primitive source-facing input: a bifunction `F : U → X → WithBotTop 𝕜` and a positive scalar
  `lam`;
- primitive owner hypothesis reused here: `IsCofinite XStar UStar F`;
- derived conclusion: `IsCofinite XStar UStar (rightScalarMul F lam)`.

Layer target: `source-facing`, proved as a thin owner-preservation theorem.
-/

-- Proof sketch: reuse the Chapter 38 owner theorem for the scaled lower pairing on the primal
-- slice, evaluate the adjoint-side pairing by changing to the underlying convex-conjugate owner
-- on the adjoint slice and applying the positive-scalar scaling theorem there, and then rewrite
-- the scaled adjoint by
-- `adjointFunction_rightScalarMul`.
/-- Proposition 38.7.4: a positive scalar multiple of a co-finite bifunction is again
co-finite. -/
theorem isCofinite_rightScalarMul
    {F : U → X → WithBotTop 𝕜} (hF : IsCofinite XStar UStar F)
    (lam : Set.Ioi (0 : 𝕜)) :
    IsCofinite XStar UStar (rightScalarMul F lam) := by
  sorry

end

end Bifunction

/-! ### Proposition_38_7_5 (from Chap08) -/
noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {Y : Type w}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable [HasLinearPairing Y Y ℝ] [HasContinuousPairing Y Y ℝ]
variable {F : U → X → EReal} {G : X → Y → EReal}

local notation "F⋆" => (adjoint X U F : X → U → EReal)
local notation "G⋆" => (adjoint Y X G : Y → X → EReal)

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 38.7.5 studies the Chapter 38 product `GF` of co-finite
  closed-convex bifunctions, asserting that this product is again co-finite and that the adjoint
  commutes with it as `(GF)^* = F^* G^*`.
- `core/canonical`: the stable owner layer is already present upstream as `Bifunction.comp`,
  `Bifunction.adjoint`, the Chapter 38.5 product-adjoint theorem
  `adjointFunction_comp_eq_comp_adjointFunction_of_common_riDom`, and the co-finiteness owner
  `Bifunction.IsCofinite`.
- `bridge/view`: this item contributes only the bridge from the Chapter 38.7 closed-convex
  co-finite owner hypotheses to the common-`riDom` qualification and properness data needed by
  Theorem 38.5, together with the co-finiteness preservation statement for `comp`.

Primary mathematical domain:
- convex bifunction duality for Chapter 38 products in the finite-dimensional real paired setting.

Domain-style sampling used here:
- `Bifunction.comp` and
  `Bifunction.adjointFunction_comp_eq_comp_adjointFunction_of_common_riDom` from `Theorem_38_5`;
- `Bifunction.IsCofinite` and
  `Bifunction.isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ`,
  `Bifunction.uncurry_isProper_of_isClosedConvex_of_isCofinite` from `Proposition_38_7_2`;
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`.

Primitive data vs derived API:
- primitive inputs: bifunctions `F : U → X → EReal` and `G : X → Y → EReal`;
- primitive owner hypotheses: `IsClosedConvex F`, `IsCofinite X U F`,
  `IsClosedConvex G`, `IsCofinite Y X G`;
- derived API: the common-relative-interior bridge for Theorem 38.5, the induced Chapter 38
  properness data, the adjoint identity, and co-finiteness of `comp G F`.

Layer target: `bridge/view`.
-/

-- Proof sketch: Proposition 38.7.2 upgrades co-finiteness, under the closed-convex owner, to
-- full source domain `dom G = Set.univ` and full adjoint-side source domain `dom (-F⋆) = Set.univ`.
-- For `EReal`-valued slices these are the same effective domains as `dom G` and `dom F⋆`, so the
-- relative interiors are both all of the ambient spaces. This is exactly the qualification needed
-- by Theorem 38.5.
/-- Bridge/view lemma: closed-convex co-finite bifunctions satisfy the common-relative-interior
qualification `riDom(F⋆) ∩ riDom(G) ≠ ∅` required by the Chapter 38 product-adjoint theorem. -/
theorem common_riDom_adjoint_of_isClosedConvex_of_isCofinite
    (hF : IsClosedConvex F) (hF_cofinite : IsCofinite X U F)
    (hG : IsClosedConvex G) (hG_cofinite : IsCofinite Y X G) :
    (riDom(F⋆) ∩ riDom(G)).Nonempty := sorry

-- Proof sketch: combine the bridge theorem
-- `common_riDom_adjoint_of_isClosedConvex_of_isCofinite` with the Chapter 38.5 adjoint formula
-- for the product `comp G F`, and derive the Chapter 38 properness owner from the full-domain
-- consequences of Proposition 38.7.2.
/-- Proposition 38.7.5: if `F` and `G` are closed-convex co-finite bifunctions, then the adjoint
of their product is the reversed product of the adjoints, i.e.
`adjoint Y U (comp G F) = comp F⋆ G⋆`. -/
theorem adjointFunction_comp_eq_comp_adjoint_of_isClosedConvex_of_isCofinite
    (hF : IsClosedConvex F) (hF_cofinite : IsCofinite X U F)
    (hG : IsClosedConvex G) (hG_cofinite : IsCofinite Y X G) :
    adjoint Y U (comp G F) = comp F⋆ G⋆ := sorry

-- Proof sketch: express co-finiteness of `comp G F` through the Chapter 33 pointwise pairing
-- equation, then use the product adjoint identity above together with the co-finiteness
-- equations for `F` and `G` to rewrite the required pairings into a composed finite duality
-- expression.
/-- The product of closed-convex co-finite bifunctions is again co-finite. Convexity of
`comp G F` itself is already provided upstream by `uncurry_comp_isConvex`. -/
theorem isCofinite_comp_of_isClosedConvex_of_isCofinite
    (hF : IsClosedConvex F) (hF_cofinite : IsCofinite X U F)
    (hG : IsClosedConvex G) (hG_cofinite : IsCofinite Y X G) :
    IsCofinite Y U (comp G F) := sorry

end

end Bifunction

/-! ### Proposition_38_7_6 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

section Assoc

variable {U : Type u} {X : Type v} {Y : Type w} {Z : Type z}

-- Proof sketch: expand both sides with `comp_apply_eq_iInf`. Both expressions are the same
-- iterated infimum over the intermediate variables, so the equality follows by extensionality.
/-- The Chapter 38 product of `EReal`-valued bifunctions is associative. -/
theorem comp_assoc
    (F : U → X → EReal) (G : X → Y → EReal) (H : Y → Z → EReal) :
    comp H (comp G F) = comp (comp H G) F := sorry

end Assoc

end Bifunction

namespace Rockafellar

scoped instance endobifunctionMul
    {U : Type u} :
    Mul (U → U → EReal) where
  mul F G := Bifunction.comp F G

scoped instance endobifunctionSemigroup
    {U : Type u} :
    Semigroup (U → U → EReal) where
  mul_assoc F G H := by
    simpa using (Bifunction.comp_assoc H G F).symm

end Rockafellar

namespace Bifunction

section Mul

variable {U : Type u}

/-- Endobifunction multiplication is the Chapter 38 product `F * G = comp F G`. -/
@[simp] theorem mul_apply (F G : U → U → EReal) (u x : U) :
    (F * G) u x = comp F G u x :=
  rfl

end Mul

section Semigroup

variable {U : Type u}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 38.7.6 studies the Chapter 38 product on closed-convex co-finite
  bifunction endomorphisms and records that, under a noncommuting pair of linear endomorphisms,
  this semigroup is noncommutative.
- `core/canonical`: the owner abstractions are `Bifunction.comp`, the `Rockafellar`-scoped
  semigroup structure on actual endobifunctions `U → U → EReal` induced by `comp`, mathlib's
  `Subsemigroup`, and the regularity owners `Bifunction.IsClosedConvex` and
  `Bifunction.IsCofinite`.
- `bridge/view`: the final noncommutativity witness passes through singleton-graph indicator
  bifunctions of linear maps and the bridge theorem `comp_graphIndicator_eq_graphIndicator_comp`.

Primary mathematical domain:
- semigroup structure on closed-convex co-finite endobifunctions under Chapter 38 composition.

Domain-style sampling used here:
- `Bifunction.comp` from `Theorem_38_5`;
- `Subsemigroup` from mathlib's algebraic subobject API;
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`;
- `Bifunction.isClosedConvex_comp_of_common_riDom_adjoint_inverse` from `Proposition_38_5_1`;
- `Bifunction.isCofinite_comp_of_isClosedConvex_of_isCofinite` from `Proposition_38_7_5`.

Primitive data vs derived API:
- primitive source data: endobifunctions `F : U → U → EReal`;
- primitive owner operation: `comp`;
- derived API: the `Rockafellar`-scoped multiplication surface `F * G = comp F G`, together with
  the canonical `Subsemigroup` cut out by `IsClosedConvex` and `IsCofinite`.

Layer target: `source-facing`.
-/

variable (U)

-- Proof sketch: Proposition 38.7.5 supplies co-finiteness of the Chapter 38 product under the
-- closed-convex/co-finite owner hypotheses, and Proposition 38.5.1 supplies closed-convexity of
-- the same product after deriving the common-`riDom` qualification from those hypotheses.
/-- The closed-convex co-finite endobifunctions form the canonical `Subsemigroup` of
`U → U → EReal` cut out by the Chapter 38 product and the Chapter 38.5/38.7 closure theorems. -/
def closedConvexCofinite
    (U : Type u) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ] :
    Subsemigroup (U → U → EReal) where
  carrier := {F | IsClosedConvex F ∧ IsCofinite U U F}
  mul_mem' hF hG := by
    sorry

@[simp] theorem mem_closedConvexCofinite {F : U → U → EReal} :
    F ∈ closedConvexCofinite U ↔ IsClosedConvex F ∧ IsCofinite U U F :=
  Iff.rfl

-- Proof sketch: choose noncommuting linear endomorphisms `A` and `B`, represent them by their
-- singleton-graph indicator bifunctions, and use Proposition 38.4.3 to identify the Chapter 38
-- products with the graph indicators of `B.comp A` and `A.comp B`.
/-- Proposition 38.7.6: if `U` admits two noncommuting linear endomorphisms, then the
closed-convex co-finite endobifunctions from `U` to itself form a noncommutative subsemigroup of
`U → U → EReal` under the Chapter 38 product. Noncommutativity is expressed by two elements of
`closedConvexCofinite U` whose products in opposite orders are unequal. -/
theorem exists_noncommuting_closedConvexCofinite_of_exists_noncommuting_linearMap
    (hlin : ∃ A B : U →ₗ[ℝ] U, B.comp A ≠ A.comp B) :
    ∃ F G : closedConvexCofinite U, F * G ≠ G * F := sorry

end Semigroup

end Bifunction

/-! ### Proposition_38_7_7 (from Chap08) -/
noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]
variable {F : U → X → WithBotTop ℝ} {f : U → WithBotTop ℝ} {gStar : X → WithBotTop ℝ}

local notation "IsCofinite[ℝ]" => Function.IsCofinite (𝕜 := ℝ)
local notation "F⋆" => (adjoint X U F : X → U → WithBotTop ℝ)
local notation "adjointUpperImage" =>
  upperPerturbationFunction (fun u x ↦ gStar x - F⋆ x u)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.7.7 states the inner-product identity
  `⟨Ff, g⋆⟩ = ⟨f, F⋆ g⋆⟩` for a co-finite closed-convex bifunction `F`, a co-finite convex
  function `f`, and a co-finite concave function `gStar`.
- `core/canonical`: the stable owners already present in the project are `Bifunction.image`,
  `Bifunction.adjoint`, `Bifunction.upperPerturbationFunction`, `Function.innerProduct`,
  `Function.IsCofinite`, `Bifunction.IsClosedConvex`, and `Bifunction.IsCofinite X U`.
- `bridge/view`: no new owner is introduced here; the source term `F⋆ g⋆` is written directly
  with the canonical owner `upperPerturbationFunction`.

Domain-style sampling used here:
- `Bifunction.image` from `Definition_38_0_4`;
- `Bifunction.adjoint` from `Definition_6_30_14`, reused through
  `Proposition_38_7_2`;
- `Bifunction.upperPerturbationFunction` from `Definition_6_30_11`;
- `Function.innerProduct` from `Definition_38_5_2`;
- `Function.IsCofinite` from `Text_13_3_1`;
- `Bifunction.IsClosedConvex` and `Bifunction.IsCofinite X U` from `Proposition_38_7_2`.

Primitive data vs derived API:
- primitive source inputs: a bifunction `F : U → X → WithBotTop ℝ`, a convex-side function
  `f : U → WithBotTop ℝ`, and a concave-side function `gStar : X → WithBotTop ℝ`;
- primitive source-facing owners reused upstream: `image F f`, `adjoint X U F`,
  `upperPerturbationFunction`, `innerProduct`, `IsClosedConvex`, and `IsCofinite X U`;
- derived API here: the co-finite inner-product identity written directly with that owner.

Layer target: `source-facing`.
-/

-- Proof sketch: expand the left inner product using Definition 38.5.2, express the adjoint-side
-- action `F⋆ g⋆` with `upperPerturbationFunction`, and apply the Chapter 38.7 duality identity
-- slice by slice. The co-finiteness hypotheses on `F`, `f`, and `gStar` let one exchange the two
-- suprema/infima without a duality gap.
/-- Proposition 38.7.7: for a co-finite closed-convex bifunction `F`, a co-finite convex
function `f`, and a co-finite concave function `gStar`, the Chapter 38 inner product of
`image F f` with `gStar` equals the inner product of `f` with the adjoint-side concave image
`adjointUpperImage`, which is the source term `F⋆ g⋆` rendered in the existing owner language. -/
theorem innerProduct_image_eq_innerProduct_adjointUpperImage
    (hF_closedConvex : IsClosedConvex F) (hF_cofinite : IsCofinite X U F)
    (hf_cofinite : IsCofinite[ℝ] f) (hgStar_cofinite : IsCofinite[ℝ] (-gStar)) :
    Function.innerProduct (image F f) gStar =
      Function.innerProduct f adjointUpperImage := by
  sorry

end

end Bifunction

/-! ### Theorem_38_7 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v u' v'

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup UStar] [Module ℝ UStar]
variable [AddCommGroup XStar] [Module ℝ XStar]
variable [HasLinearPairing U UStar ℝ] [HasContinuousPairing U UStar ℝ]
variable [HasLinearPairing X XStar ℝ] [HasContinuousPairing X XStar ℝ]
variable {F : U → X → EReal} {f : U → EReal} {g : X → EReal}

local notation "ri(" C ")" => intrinsicInterior ℝ C
local instance : HasPairing UStar U ℝ := HasPairing.swap
local instance : HasPairing XStar X ℝ := HasPairing.swap

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → EReal)
local notation "f⋆" => (convexConjugate f : UStar → EReal)
local notation "g∗" => (concaveConjugate g : XStar → EReal)
local notation "adjointUpperImage" =>
  upperPerturbationFunction (fun uStar xStar ↦ g∗ xStar - F⋆ xStar uStar)
local notation "inverseUpperImage" =>
  upperPerturbationFunction (fun u x ↦ g x - F _* x u)
local notation "adjointImage" =>
  image (Function.swap F⋆) f⋆

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 38.7 is the four-term Chapter 38 duality chain
  `⟨Ff, g^*⟩ = ⟨f, F^* g^*⟩ = -⟨f^*, F_* g⟩ = -⟨F^*_* f^*, g⟩`.
- `core/canonical`: the owner layer is already present in the project as `Bifunction.image`,
  `Bifunction.adjoint`, `Bifunction.inverse`, `Bifunction.upperPerturbationFunction`,
  `Function.innerProduct`, and the conjugate owners `f⋆` and `g∗`.
- `bridge/view`: no new owner is introduced here; the source term `F^* g^*` is written directly
  with the canonical owner `upperPerturbationFunction`, while `F_* g` and `F^*_* f^*` are kept as
  local notation for repeated canonical expressions.

Primary mathematical domain:
- convex bifunction duality and Chapter 38 inner products under a relative-interior qualification.

Domain-style sampling used here:
- `Bifunction.image` from `Definition_38_0_4`;
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Bifunction.inverse` from `Definition_36_4_1`;
- `Bifunction.upperPerturbationFunction` from `Definition_6_30_11`;
- `Bifunction.convexConjugate_image_eq_image_adjoint_conjugate_of_common_riDom` from
  `Theorem_38_4`;
- `Function.hasInnerProduct_convexConjugate_concaveConjugate`,
  `Function.innerProduct_convexConjugate_concaveConjugate_eq_neg`,
  `Function.hasInnerProduct_lowerSemicontinuousHull_concaveClosure`, and
  `Function.innerProduct_lowerSemicontinuousHull_concaveClosure_eq` from `Lemma_38_6`.

Primitive data vs derived API:
- primitive inputs: a convex bifunction `F`, a proper convex function `f`, and a proper concave
  function `g`;
- primitive owner layer already upstream: `image F f`, `F⋆`, `F _*`, `upperPerturbationFunction`,
  `Function.innerProduct`, and `Function.HasInnerProduct`;
- derived API here: existence of the four Chapter 38 inner products under the source slicewise
  relative-interior qualification, together with the three atomic equalities making up the
  displayed chain in Theorem 38.7.

Layer target: `source-facing`, stated directly in the existing owner language on the paired spaces
`U/UStar` and `X/XStar` rather than on an unnecessary self-dual specialization.
-/

variable (hF_convex : (Function.uncurry F).IsConvex ℝ)
variable (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
variable (hg_concave : g.IsConcave ℝ) (hg_proper : (-g).IsProper)
variable
  (hqual :
    ∃ u : U,
      u ∈ riDom(f) ∩ ri(dom F) ∧
        (riDom(F u) ∩ riDom(-g)).Nonempty)

-- Proof sketch: use the source qualification to derive the relative-interior hypothesis needed
-- for the pair `(image F f, g∗)`, then combine the image/adjoint conjugacy theorem of
-- Theorem 38.4 with the Chapter 38.5 existence criterion for function inner products.
/-- The first two Chapter 38 inner products in Theorem 38.7 exist under the source slicewise
relative-interior qualification. -/
theorem hasInnerProduct_image_concaveConjugate_and_adjointUpperImage_of_qualification :
    Function.HasInnerProduct (image F f) g∗ ∧
      Function.HasInnerProduct f adjointUpperImage := sorry

-- Proof sketch: first apply the preceding existence theorem to the qualified pair
-- `(image F f, g∗)`. Then rewrite the conjugate of `image F f` by Theorem 38.4 as the adjoint-side
-- image of `f⋆`, and use the Theorem 38.7 duality argument to identify the common inner-product
-- value with the adjoint-side upper image of `g∗`.
/-- Theorem 38.7: under the source slicewise relative-interior qualification,
`⟨Ff, g^*⟩ = ⟨f, F^* g^*⟩`, rendered in the chapter owner language as the equality between the
inner product of `image F f` with `g∗` and the inner product of `f` with the adjoint-side upper
image of `g∗`. This is the first equality in the displayed chain
`⟨Ff, g^*⟩ = ⟨f, F^* g^*⟩ = -⟨f^*, F_* g⟩ = -⟨F^*_* f^*, g⟩`. -/
theorem innerProduct_image_concaveConjugate_eq_innerProduct_adjointUpperImage_of_qualification :
    Function.innerProduct (image F f) g∗ =
      Function.innerProduct f adjointUpperImage := sorry

-- Proof sketch: reinterpret the source theorem for the inverse bifunction `F _*`, using the same
-- slicewise relative-interior hypothesis in the swapped orientation. This yields existence of the
-- Chapter 38 inner products for `(f⋆, inverseUpperImage)` and `(adjointImage, g)`.
/-- The last two Chapter 38 inner products in Theorem 38.7 exist under the same source
qualification. Here `inverseUpperImage` is the source term `F_* g`, and `adjointImage` is the
source term `F^*_* f^*`. -/
theorem hasInnerProduct_convexConjugate_inverseUpperImage_and_adjointImage_of_qualification :
    Function.HasInnerProduct f⋆ inverseUpperImage ∧
      Function.HasInnerProduct adjointImage g := sorry

-- Proof sketch: apply the inverse-bifunction form of the same strong-duality argument used for
-- the main theorem. The resulting equality is exactly the middle equality in the source chain,
-- written with the canonical owner `upperPerturbationFunction` for `F_* g`.
/-- The middle equality in Theorem 38.7: the inner product of `f` with the adjoint-side upper
image of `g∗` equals the negative of the inner product of `f⋆` with the inverse-side upper image
of `g`. -/
theorem innerProduct_adjointUpperImage_eq_neg_innerProduct_inverseUpperImage_of_qualification :
    Function.innerProduct f adjointUpperImage =
      -Function.innerProduct f⋆ inverseUpperImage := sorry

-- Proof sketch: rewrite `adjointImage` by Theorem 38.4 as the conjugate of `image F f`, then
-- apply Lemma 38.6 to the qualified pair `(image F f, g∗)` and simplify the double sign change.
/-- The final equality in Theorem 38.7 after cancelling the common minus sign:
the inner product of `f⋆` with the inverse-side upper image of `g` equals the inner product of
the adjoint image `image (Function.swap F⋆) (f⋆)` with `g`. -/
theorem innerProduct_inverseUpperImage_eq_innerProduct_adjointImage_of_qualification :
    Function.innerProduct f⋆ inverseUpperImage =
      Function.innerProduct adjointImage g := sorry

end

end Bifunction
