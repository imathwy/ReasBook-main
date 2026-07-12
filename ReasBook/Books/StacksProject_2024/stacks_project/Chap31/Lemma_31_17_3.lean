import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap31.Lemma_31_17_2

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
local notation "SiteModX" => ringedSiteModuleCategory JX X.𝒪
local notation "SiteModY" => ringedSiteModuleCategory JY Y.𝒪

/- Semantic recall note: `lean_leansearch` surfaced Picard-group representatives and stalk maps;
local Chapter 31 norm precedent is `FiniteMorphismNorm`, `IsFiniteMorphismNorm`, and the
Picard-level norm hom from Lemma 31.17.2. The Stacks tag evidence is consistent: tag `0BCZ`
comes from `https://stacks.math.columbia.edu/tag/0BCZ`. -/

/-- Lemma 31.17.3: let `π : X ⟶ Y` be a finite morphism of schemes admitting a norm of
degree `d`. For every morphism of invertible `\mathcal O_X`-modules
`φ : \mathcal L ⟶ \mathcal L'`, there is a morphism between the Picard-norm representatives
`Normπ(\mathcal L) ⟶ Normπ(\mathcal L')`. Moreover, for every `y : Y`, this norm morphism
is zero at `y` iff `φ` is zero at some point `x` above `y`. -/
@[stacks 0BCZ]
theorem exists_picardNormMap_zeroAt_iff_of_exists_finiteMorphismNorm
    [MonoidalCategory SiteModX] [SymmetricCategory SiteModX]
    [MonoidalCategory SiteModY] [SymmetricCategory SiteModY]
    [IsFinite π]
    (hnorm : ∃ N : FiniteMorphismNorm π, IsFiniteMorphismNorm π d N) :
    ∃ normπ :
      ringedSitePicardGroup JX X.𝒪 →+
        ringedSitePicardGroup JY Y.𝒪,
      (∀ (𝒩 : SiteModY) [Functor.IsEquivalence (tensorRight 𝒩)],
        normπ (ringedSitePicardGroup.mk JX X.𝒪 (picardPullbackModule π 𝒩)) =
          d • ringedSitePicardGroup.mk JY Y.𝒪 𝒩) ∧
        ∀ (ℒ ℒ' : SiteModX) [Functor.IsEquivalence (tensorRight ℒ)]
          [Functor.IsEquivalence (tensorRight ℒ')] (φ : ℒ ⟶ ℒ'),
          ∃ normφ :
            ringedSitePicardGroup.repr JY Y.𝒪
                (normπ (ringedSitePicardGroup.mk JX X.𝒪 ℒ)) ⟶
              ringedSitePicardGroup.repr JY Y.𝒪
                (normπ (ringedSitePicardGroup.mk JX X.𝒪 ℒ')),
            ∀ y : Y,
              ((∃ x : {x : X // π.base x = y}, RingedSpace.moduleStalkHom x.1 φ = 0) ↔
                RingedSpace.moduleStalkHom y normφ = 0) := sorry

end AlgebraicGeometry.Scheme
