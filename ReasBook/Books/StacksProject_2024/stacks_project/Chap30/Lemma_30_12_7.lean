import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme}

-- Semantic recall: `lean_leansearch` returned `ShortComplex.ShortExact`,
-- `Scheme.IdealSheafData.support`, and `Scheme.Modules.pushforward`; nearby Chapter 30 files
-- represent coherent supports by `moduleSupport`, ideal sheaves by subobjects of the unit module,
-- and ideal-multiple containment by affine-open section submodules.

/-- The support of a scheme module, expressed as the support of its underlying additive sheaf. -/
abbrev moduleSupport (ℱ : X.Modules) : Set X :=
  {x | ¬ IsZero (TopCat.Presheaf.stalk ℱ.val.presheaf x)}

/-- Unfold the support of a scheme module as nonvanishing of the underlying additive stalk. -/
theorem moduleSupport_def (ℱ : X.Modules) :
    moduleSupport ℱ =
      {x | ¬ IsZero (TopCat.Presheaf.stalk ℱ.val.presheaf x)} := sorry

/-- The affine-open section map induced by a subobject of a module sheaf. -/
private def affineOpenSubobjectSectionMap
    {𝒢 : X.Modules} (𝒢' : Subobject 𝒢) (U : X.affineOpens) :
    Γ((𝒢' : X.Modules), U.1) →ₗ[Γ(X, U.1)] Γ(𝒢, U.1) :=
  ((𝒢'.arrow.val.app (op U.1)).hom)

/-- The affine-open section submodule determined by a subobject of a module sheaf. -/
private def affineOpenSubobjectSections
    {𝒢 : X.Modules} (𝒢' : Subobject 𝒢) (U : X.affineOpens) :
    Submodule Γ(X, U.1) Γ(𝒢, U.1) :=
  LinearMap.range (affineOpenSubobjectSectionMap 𝒢' U)

/-- A subsheaf `𝒢' ⊆ 𝒢` is contained in the ideal multiple `J𝒢` when, on every affine open
`U`, its sections lie in the submodule `J(U) • 𝒢(U)`. This is the source-facing affine-open
encoding of the containment `𝒢' ⊂ J𝒢`. -/
def IsContainedInIdealMultipleOnAffineOpens
    (J : X.IdealSheafData) {𝒢 : X.Modules} (𝒢' : Subobject 𝒢) : Prop :=
  ∀ U : X.affineOpens,
    affineOpenSubobjectSections 𝒢' U ≤
      J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(𝒢, U.1))

/-- Unfold the affine-open ideal-multiple containment predicate for a subsheaf. -/
theorem isContainedInIdealMultipleOnAffineOpens_iff
    (J : X.IdealSheafData) {𝒢 : X.Modules} (𝒢' : Subobject 𝒢) :
    IsContainedInIdealMultipleOnAffineOpens J 𝒢' ↔
      ∀ U : X.affineOpens,
        affineOpenSubobjectSections 𝒢' U ≤
          J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(𝒢, U.1)) := sorry

/-- A module property is closed under short exact extensions of coherent modules. -/
def DevissageShortExactClosed (P : X.Modules → Prop) : Prop :=
  ∀ {S : ShortComplex X.Modules}, S.ShortExact →
    S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
    P S.X₁ → P S.X₃ → P S.X₂

/-- Unfold the short-exact-extension closure condition used in devissage. -/
theorem devissageShortExactClosed_iff (P : X.Modules → Prop) :
    DevissageShortExactClosed P ↔
      ∀ {S : ShortComplex X.Modules}, S.ShortExact →
        S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
        P S.X₁ → P S.X₃ → P S.X₂ := sorry

/-- A module property descends from a nonempty finite coproduct `ℱ^{⊕ r}` to `ℱ`. -/
def DevissageDescendsFromFiniteCoproducts (P : X.Modules → Prop) : Prop :=
  ∀ (ℱ : X.Modules), ℱ.IsCoherent → ∀ (r : ℕ), 0 < r →
    P (∐ fun _ : Fin r ↦ ℱ) → P ℱ

/-- Unfold the finite-coproduct descent condition used in devissage. -/
theorem devissageDescendsFromFiniteCoproducts_iff (P : X.Modules → Prop) :
    DevissageDescendsFromFiniteCoproducts P ↔
      ∀ (ℱ : X.Modules), ℱ.IsCoherent → ∀ (r : ℕ), 0 < r →
        P (∐ fun _ : Fin r ↦ ℱ) → P ℱ := sorry

/-- The property holds for pushforwards of quasi-coherent ideal sheaves from every integral
closed subscheme whose support is properly contained in `Z₀`. -/
def DevissageHoldsOnProperIntegralIdealPushforwards
    (Z₀ : TopologicalSpace.IrreducibleCloseds X) (P : X.Modules → Prop) : Prop :=
  ∀ (Z : X.IdealSheafData), IsIntegral Z.subscheme →
    (Z.support : Set X) ⊂ (Z₀ : Set X) →
      ∀ I : Subobject (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules),
        (Subobject.underlying.obj I : Z.subscheme.Modules).IsQuasicoherent →
          P ((Scheme.Modules.pushforward Z.subschemeι).obj
            (Subobject.underlying.obj I : Z.subscheme.Modules))

/-- Unfold the proper-integral-closed-subscheme ideal-pushforward condition. -/
theorem devissageHoldsOnProperIntegralIdealPushforwards_iff
    (Z₀ : TopologicalSpace.IrreducibleCloseds X) (P : X.Modules → Prop) :
    DevissageHoldsOnProperIntegralIdealPushforwards Z₀ P ↔
      ∀ (Z : X.IdealSheafData), IsIntegral Z.subscheme →
        (Z.support : Set X) ⊂ (Z₀ : Set X) →
          ∀ I : Subobject
              (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules),
            (Subobject.underlying.obj I : Z.subscheme.Modules).IsQuasicoherent →
              P ((Scheme.Modules.pushforward Z.subschemeι).obj
                (Subobject.underlying.obj I : Z.subscheme.Modules)) := sorry

/-- The generic-model hypothesis: there is a coherent `𝒢` supported exactly on `Z₀`, whose stalk
at `ξ` is killed by the maximal ideal, and whose ideal-multiple subsheaves which agree with `𝒢`
at `ξ` contain quasi-coherent subsheaves satisfying the property. -/
def DevissageGenericModel
    (Z₀ : TopologicalSpace.IrreducibleCloseds X) (ξ : X) (P : X.Modules → Prop) : Prop :=
  ∃ 𝒢 : X.Modules, ∃ _ : 𝒢.IsCoherent,
    moduleSupport 𝒢 = (Z₀ : Set X) ∧
      (∀ a : X.presheaf.stalk ξ,
        a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) →
          ∀ m : RingedSpace.stalkModuleCat 𝒢 ξ, a • m = 0) ∧
      ∀ J : X.IdealSheafData, ξ ∉ (J.support : Set X) →
        ∃ 𝒢' : Subobject 𝒢,
          (𝒢' : X.Modules).IsQuasicoherent ∧
            IsContainedInIdealMultipleOnAffineOpens J 𝒢' ∧
            ξ ∉ moduleSupport (cokernel 𝒢'.arrow) ∧
            P (𝒢' : X.Modules)

/-- Unfold the generic-model hypothesis used in devissage. -/
theorem devissageGenericModel_iff
    (Z₀ : TopologicalSpace.IrreducibleCloseds X) (ξ : X) (P : X.Modules → Prop) :
    DevissageGenericModel Z₀ ξ P ↔
      ∃ 𝒢 : X.Modules, ∃ _ : 𝒢.IsCoherent,
        moduleSupport 𝒢 = (Z₀ : Set X) ∧
          (∀ a : X.presheaf.stalk ξ,
            a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) →
              ∀ m : RingedSpace.stalkModuleCat 𝒢 ξ, a • m = 0) ∧
          ∀ J : X.IdealSheafData, ξ ∉ (J.support : Set X) →
            ∃ 𝒢' : Subobject 𝒢,
              (𝒢' : X.Modules).IsQuasicoherent ∧
                IsContainedInIdealMultipleOnAffineOpens J 𝒢' ∧
                ξ ∉ moduleSupport (cokernel 𝒢'.arrow) ∧
                P (𝒢' : X.Modules) := sorry

/-- Lemma 30.12.7: let `X` be Noetherian and let `Z₀` be an irreducible closed subset with
generic point `ξ`. Suppose a property `P` of coherent `\mathcal O_X`-modules is closed under
extensions, descends from a nonempty finite direct sum, holds for pushforwards of quasi-coherent
ideal sheaves on every integral closed subscheme properly contained in `Z₀`, and is available on
the generic model `𝒢` after multiplying by any ideal sheaf which is the unit ideal at `ξ`. Then
`P` holds for every coherent module whose support is contained in `Z₀`. -/
@[stacks 01YL]
theorem devissage_property_of_support_subset_irreducibleClosed
    [IsNoetherian X]
    (Z₀ : TopologicalSpace.IrreducibleCloseds X)
    (ξ : X) (hξ : IsGenericPoint ξ (Z₀ : Set X))
    (P : X.Modules → Prop)
    (h_shortExact : DevissageShortExactClosed P)
    (h_coproduct : DevissageDescendsFromFiniteCoproducts P)
    (h_proper_closed : DevissageHoldsOnProperIntegralIdealPushforwards Z₀ P)
    (h_generic_model : DevissageGenericModel Z₀ ξ P)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hSupp : moduleSupport ℱ ⊆ (Z₀ : Set X)) :
    P ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
