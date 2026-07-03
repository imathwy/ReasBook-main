import Mathlib
import StacksProject_2024.Chap20.Lemma_20_13_4_Leray_spectral_sequence
import StacksProject_2024.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/-- The category of additive commutative groups has its standard derived category. -/
local instance addCommGrpCat_hasDerivedCategory : HasDerivedCategory AddCommGrpCat.{u} :=
  HasDerivedCategory.standard AddCommGrpCat.{u}

-- Proof sketch: replace `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)` by the morphism of ringed
-- spaces `f' : (X, \mathcal O_X) ⟶ (Y, f_* \mathcal O_X)`. By Lemma `20.13.3`, the Leray
-- spectral sequence for `f'` has the same underlying additive `E_r^{p,q}` terms as the usual
-- Leray spectral sequence for `f` for every `r ≥ 2`. Since
-- `Γ(Y, f_* \mathcal O_X) = Γ(X, \mathcal O_X)`, these terms inherit a
-- `Γ(X, \mathcal O_X)`-module structure.
/-- Remark 20.13.5: in the bounded-below-complex form of the Leray spectral sequence for
`f : X ⟶ Y`, every page entry `E_r^{p,q}` with `r ≥ 2` can be viewed as a
`\Gamma(X, \mathcal O_X)`-module. Concretely, there exists an object of
`ModuleCat (globalSectionsRing X)` whose underlying additive group is the given
`E_r^{p,q}`-term. -/
theorem leraySpectralSequence_page_has_globalSectionsModule_lift
    (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [AdditiveFunctorDerivedLocalizationSituation (𝟭 (RingedSpace.Modules X))]
    [(RingedSpace.Hom.pushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (RingedSpace.Hom.pushforward f)]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]
    (K : CochainComplex.Plus (RingedSpace.Modules X))
    (S : LeraySpectralSequenceBoundedBelow f K)
    {r : ℕ} (hr : 2 ≤ r) (p q : ℕ) :
    ∃ M : ModuleCat (globalSectionsRing X),
      IsIsomorphic
        ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat).obj M)
        ((S.spectralSequence.page r).X (p, q)) := sorry

end AlgebraicGeometry.RingedSpace
