import StacksProject_2024.Chap17.Definition_17_25_9
import StacksProject_2024.Chap17.Lemma_17_25_3
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.PolynomialLaw.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped RingedSpacePicard

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ)

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "JY" => Opens.grothendieckTopology Y.toTopCat
local notation "ModX" => X.Modules
local notation "ModY" => Y.Modules
local notation "SiteModX" => ringedSiteModuleCategory JX X.𝒪
local notation "SiteModY" => ringedSiteModuleCategory JY Y.𝒪

/- Semantic recall note: `lean_leansearch` surfaced the existing Picard-group and scheme-module
pullback APIs, and local Chapter 31 precedent uses `Norm`/`IsNorm` for norms and
`Pic(X.toLocallyRingedSpace.toRingedSpace)` for scheme Picard groups. -/

/-- The section ring on the inverse image of an open set is an algebra over the section ring on
that open set via the morphism of schemes. -/
instance normPullbackSectionAlgebra (U : Y.Opens) :
    Algebra (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U)) :=
  (π.app U).hom.toAlgebra

/-- A norm datum for a morphism of schemes, recorded affine-open-wise as polynomial laws on
sections. -/
abbrev FiniteMorphismNorm (π : X ⟶ Y) :=
  ∀ (U : Y.Opens) (_ : IsAffineOpen U),
    Γ(X, π ⁻¹ᵁ U) →ₚₗ[Γ(Y, U)] Γ(Y, U)

/-- A norm datum has degree `d` when its affine-open ground maps agree with the algebra norm and
send base sections to their `d`th powers. -/
structure IsFiniteMorphismNorm (π : X ⟶ Y) (d : ℕ) (N : FiniteMorphismNorm π) : Prop where
  /-- The ground map of each affine-open polynomial law is the canonical algebra norm. -/
  ground_eq_norm :
    ∀ (U : Y.Opens) (hU : IsAffineOpen U),
      (N U hU).ground = Algebra.norm (Γ(Y, U))
  /-- The norm of a pulled-back base section is its `d`th power. -/
  ground_algebraMap_pow :
    ∀ (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U)),
      (N U hU).ground (algebraMap (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U)) r) = r ^ d

/-- The pullback of a module, expressed on the ringed-site module owner used by the Picard group.
-/
abbrev picardPullbackModule (π : X ⟶ Y) (𝒩 : SiteModY) : SiteModX :=
  (((Scheme.Modules.pullback π).obj (𝒩 : Y.Modules) : X.Modules) : SiteModX)

/-- Pulling back an invertible module along a morphism of schemes gives an invertible module on
the source. This is the scheme-module bridge used to form the Picard class of a pullback. -/
instance pullback_isInvertible_of_isInvertible
    [MonoidalCategory SiteModX] [MonoidalCategory SiteModY]
    (𝒩 : SiteModY) [Functor.IsEquivalence (tensorRight 𝒩)] :
    Functor.IsEquivalence (tensorRight (picardPullbackModule π 𝒩)) := sorry

/-- Lemma 31.17.2: let `π : X ⟶ Y` be a finite morphism of schemes. If there exists a norm of
degree `d` for `π`, then there is a homomorphism
`Pic(X) → Pic(Y)` whose value on the pullback of every invertible `\mathcal O_Y`-module
`\mathcal N` is the Picard class of `\mathcal N^{\otimes d}`. Since the project Picard group is
written additively, the latter class is expressed as `d • [\mathcal N]`. -/
@[stacks 0BCY]
theorem exists_picardNorm_of_exists_norm
    [MonoidalCategory SiteModX] [SymmetricCategory SiteModX]
    [MonoidalCategory SiteModY] [SymmetricCategory SiteModY]
    [IsFinite π]
    (hnorm : ∃ N : FiniteMorphismNorm π, IsFiniteMorphismNorm π d N) :
    ∃ normπ :
      ringedSitePicardGroup JX X.𝒪 →+
        ringedSitePicardGroup JY Y.𝒪,
      ∀ (𝒩 : SiteModY) [Functor.IsEquivalence (tensorRight 𝒩)],
        normπ (ringedSitePicardGroup.mk JX X.𝒪 (picardPullbackModule π 𝒩)) =
          d • ringedSitePicardGroup.mk JY Y.𝒪 𝒩 := sorry

end AlgebraicGeometry.Scheme
