import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap30.Lemma_30_12_2
import StacksProject_2024.stacks_project.Chap30.Lemma_30_12_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.support` and the nearby
-- Chapter 30 files use `X.IdealSheafData` for integral closed subschemes, `moduleSupport` for
-- supports of module sheaves, and `ShortComplex.ShortExact` for short exact sequences.

/-- A module property satisfies two-out-of-three for coherent short exact sequences whose terms
are supported on a fixed closed subscheme. -/
structure DevissageTwoOutOfThreeOnSupport
    {X : Scheme.{u}} (Z₀ : X.IdealSheafData) (P : X.Modules → Prop) : Prop where
  /-- If the left and middle terms satisfy `P`, then so does the right term. -/
  right_of_left_middle {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hSupp₁ : moduleSupport S.X₁ ⊆ (Z₀.support : Set X))
    (hSupp₂ : moduleSupport S.X₂ ⊆ (Z₀.support : Set X))
    (hSupp₃ : moduleSupport S.X₃ ⊆ (Z₀.support : Set X))
    (hP₁ : P S.X₁) (hP₂ : P S.X₂) : P S.X₃
  /-- If the left and right terms satisfy `P`, then so does the middle term. -/
  middle_of_left_right {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hSupp₁ : moduleSupport S.X₁ ⊆ (Z₀.support : Set X))
    (hSupp₂ : moduleSupport S.X₂ ⊆ (Z₀.support : Set X))
    (hSupp₃ : moduleSupport S.X₃ ⊆ (Z₀.support : Set X))
    (hP₁ : P S.X₁) (hP₃ : P S.X₃) : P S.X₂
  /-- If the middle and right terms satisfy `P`, then so does the left term. -/
  left_of_middle_right {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
    (hSupp₁ : moduleSupport S.X₁ ⊆ (Z₀.support : Set X))
    (hSupp₂ : moduleSupport S.X₂ ⊆ (Z₀.support : Set X))
    (hSupp₃ : moduleSupport S.X₃ ⊆ (Z₀.support : Set X))
    (hP₂ : P S.X₂) (hP₃ : P S.X₃) : P S.X₁

/-- A coherent module sheaf supported exactly on `Z₀`, killed generically by the maximal ideal,
with one-dimensional generic residue fiber, and satisfying a property `P`. -/
structure DevissageGenericRankOneSheaf
    {X : Scheme.{u}} (Z₀ : X.IdealSheafData) (ξ : X)
    (P : X.Modules → Prop) (𝒢 : X.Modules) : Prop where
  /-- The generic model is coherent. -/
  coherent : 𝒢.IsCoherent
  /-- The support is exactly the fixed closed subscheme support. -/
  support_eq : moduleSupport 𝒢 = (Z₀.support : Set X)
  /-- The maximal ideal at the generic point annihilates the stalk. -/
  maximalIdeal_smul_eq_zero
    (a : X.presheaf.stalk ξ)
    (ha : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ))
    (m : RingedSpace.stalkModuleCat 𝒢 ξ) : a • m = 0
  /-- The generic residue-field fiber has dimension one. -/
  fiber_finrank_eq_one :
    Module.finrank
      (IsLocalRing.ResidueField (X.presheaf.stalk ξ))
      ((IsLocalRing.ResidueField (X.presheaf.stalk ξ)) ⊗[
        X.presheaf.stalk ξ]
        RingedSpace.stalkModuleCat 𝒢 ξ) = 1
  /-- The generic model satisfies the property. -/
  property : P 𝒢

/-- Lemma 30.12.5: let `X` be a Noetherian scheme, let `Z₀ ⊆ X` be an integral closed subscheme
representing the irreducible closed subset with generic point `ξ`, and let `P` be a property of
coherent `\mathcal O_X`-modules supported on `Z₀`. If `P` satisfies two-out-of-three for short
exact sequences, holds for pushforwards of quasi-coherent ideal sheaves on every integral closed
subscheme whose support is properly contained in `Z₀`, and holds for one coherent sheaf with
support `Z₀`, generic stalk annihilated by `\mathfrak m_ξ`, and one-dimensional residue-field
fiber at `ξ`, then `P` holds for every coherent `\mathcal O_X`-module supported on `Z₀`. -/
@[stacks 01YH]
theorem devissagePropertyHoldsOfIdealPushforwardsAndGenericRankOne
    {X : Scheme.{u}} [IsNoetherian X]
    (Z₀ : X.IdealSheafData) [IsIntegral Z₀.subscheme]
    (ξ : X) (hξ : IsGenericPoint ξ (Z₀.support : Set X))
    (P : X.Modules → Prop)
    (hP_shortExact : DevissageTwoOutOfThreeOnSupport Z₀ P)
    (hP_ideal :
      ∀ (Z : X.IdealSheafData) [IsIntegral Z.subscheme],
        (Z.support : Set X) ⊂ (Z₀.support : Set X) →
        ∀ I : Subobject
          (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules),
          (Subobject.underlying.obj I : Z.subscheme.Modules).IsQuasicoherent →
          P ((Scheme.Modules.pushforward Z.subschemeι).obj
            (Subobject.underlying.obj I : Z.subscheme.Modules)))
    (hP_generic :
      ∃ 𝒢 : X.Modules,
        DevissageGenericRankOneSheaf Z₀ ξ P 𝒢)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hSuppℱ : moduleSupport ℱ ⊆ (Z₀.support : Set X)) :
    P ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
