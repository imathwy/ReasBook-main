import StacksProject_2024.stacks_project.Chap30.Lemma_30_12_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme}

-- Semantic recall: `lean_leansearch` surfaced general support and Noetherian-scheme
-- infrastructure; the local Chapter 30 owner for this devissage step is Lemma 30.12.7's
-- `DevissageShortExactClosed`, `DevissageDescendsFromFiniteCoproducts`, and affine-open
-- ideal-multiple containment API.

/-- A subsheaf of a generic model which is contained in an ideal multiple, agrees with the
generic model at the selected generic point, and satisfies the devissage property. -/
structure DevissageGenericIdealMultipleSubsheaf
    (J : X.IdealSheafData) {𝒢 : X.Modules} (𝒢' : Subobject 𝒢)
    (ξ : X) (P : X.Modules → Prop) : Prop where
  /-- The selected subsheaf is quasi-coherent. -/
  isQuasicoherent : (𝒢' : X.Modules).IsQuasicoherent
  /-- The selected subsheaf is contained in the ideal multiple on affine opens. -/
  contained : IsContainedInIdealMultipleOnAffineOpens J 𝒢'
  /-- The quotient by the selected subsheaf has no support at the generic point. -/
  not_mem_cokernel_support : ξ ∉ moduleSupport (cokernel 𝒢'.arrow)
  /-- The selected subsheaf satisfies the devissage property. -/
  property : P (𝒢' : X.Modules)

/-- A coherent generic model over an integral closed subscheme for the devissage step. -/
structure DevissageIntegralClosedGenericModel
    (Z : X.IdealSheafData) (ξ : X) (P : X.Modules → Prop) (𝒢 : X.Modules) : Prop where
  /-- The generic model is coherent. -/
  coherent : 𝒢.IsCoherent
  /-- The support of the generic model is exactly the support of the closed subscheme. -/
  support_eq : moduleSupport 𝒢 = (Z.support : Set X)
  /-- The maximal ideal at the generic point annihilates the generic stalk. -/
  maximalIdeal_smul_eq_zero :
    ∀ a : X.presheaf.stalk ξ,
      a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) →
        ∀ m : RingedSpace.stalkModuleCat 𝒢 ξ, a • m = 0
  /-- After multiplying by any ideal which is the unit ideal at the generic point, there is a
  quasi-coherent subsheaf satisfying the property and agreeing generically with the model. -/
  idealMultipleSubsheaf :
    ∀ J : X.IdealSheafData, ξ ∉ (J.support : Set X) →
      ∃ 𝒢' : Subobject 𝒢, DevissageGenericIdealMultipleSubsheaf J 𝒢' ξ P

/-- Lemma 30.12.8: let `X` be a Noetherian scheme and let `P` be a property of coherent
`\mathcal O_X`-modules. Suppose `P` is closed under extensions in coherent short exact
sequences, descends from a nonempty finite direct sum, and for every integral closed subscheme
`Z ⊆ X` with generic point `ξ` there is a coherent generic model `𝒢`, supported exactly on `Z`,
annihilated at `ξ` by the maximal ideal, such that after multiplying by any quasi-coherent
ideal sheaf which is the unit ideal at `ξ` there is a quasi-coherent subsheaf agreeing with `𝒢`
at `ξ` and satisfying `P`. Then `P` holds for every coherent module on `X`. -/
@[stacks 01YM]
theorem devissagePropertyHoldsOfIntegralClosedGenericModels
    [IsNoetherian X]
    (P : X.Modules → Prop)
    (h_shortExact : DevissageShortExactClosed P)
    (h_coproduct : DevissageDescendsFromFiniteCoproducts P)
    (h_generic :
      ∀ (Z : X.IdealSheafData) (h_integral : IsIntegral Z.subscheme)
        (ξ : X), IsGenericPoint ξ (Z.support : Set X) →
          ∃ 𝒢 : X.Modules, DevissageIntegralClosedGenericModel Z ξ P 𝒢)
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    P ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
