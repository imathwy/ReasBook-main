import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Lemma_15_67_4
import stacks_project.Chap15.Lemma_15_60_3
import stacks_project.Chap15.Definition_15_75_1
import stacks_project.Chap15.Lemma_15_77_2

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: localization and three-term truncation splittings for pseudo-coherent derived
  objects, combining the chapter owners for perfectness and tor-amplitude with the module-level
  owners for finiteness, freeness, and single-degree embeddings of localized homology;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeGE`,
  `Module.Free`,
  `Module.Finite`,
  `DerivedCategory.singleFunctor`;
- best owner abstraction: this source-facing theorem should expose the localized upper-truncation
  properties, the finiteness/free-ness of the middle homology module, and the existence of the
  three-term decomposition directly, using the canonical owners
  `K ⊗[R]^L[Localization.Away f]`, `LocalizedModule.Away`, and
  `DerivedCategory.singleFunctor`, rather than local wrapper aliases;
- primitive data: the localized object, its lower and upper truncations, the localized middle
  homology module, and the three-term biproduct object;
- derived API: perfectness and tor-amplitude of the upper truncation, finiteness/free-ness of the
  middle term, and existence of the decomposition isomorphism.

Source/core/bridge triage:
- `source-facing`: the existential three-term localization theorem below;
- `core/canonical`: `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, `Module.Free`, and
  `Module.Finite`;
- `bridge/view`: the explicit isomorphism to the three-summand object, which is an existence claim
  and not a second owner abstraction.
-/

variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField

-- Proof sketch: apply Lemma `15.77.2` in degree `i` to split off
-- `τ_{\ge i + 1}(K \otimes_R^{\mathbf L} R_f)`, then apply the same lemma in degree `i - 1` to
-- the lower truncation to split off `H^i(K)_f[-i]`. The second application makes `H^i(K)_f`
-- finite projective; after shrinking once more, replace finite projective by finite free and
-- compose the two splittings.
/-- Lemma 15.77.3: let `R` be a commutative ring, let `𝔭` be a prime ideal of `R` represented by
`𝔭 : PrimeSpectrum R`, and let `K^•` be a pseudo-coherent object of `D(R)`. Assume the
canonical base-change maps
`H^i(K^•) ⊗_R κ(𝔭) ⟶ H^i(K^• \otimes_R^{\mathbf L} κ(𝔭))`
and
`H^(i - 1)(K^•) ⊗_R κ(𝔭) ⟶ H^(i - 1)(K^• \otimes_R^{\mathbf L} κ(𝔭))`
are surjective. Then there exists `f ∈ R` with `f ∉ 𝔭` such that
`τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f)` is perfect with tor-amplitude in `[i + 1, ∞]`,
the localized degree-`i` homology `H^i(K^•)_f` is a finite free `R_f`-module, and
`K^• \otimes_R^{\mathbf L} R_f` decomposes in `D(R_f)` as
`τ_{\le i - 1}(K^• \otimes_R^{\mathbf L} R_f) ⊕ H^i(K^•)_f[-i] ⊕
  τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f)`. -/
theorem exists_localizationAway_threeTermSplit_of_residueField_homology_surjective
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hsurj_i : Epi (derivedTensorWithAlgebraHomologyComparison κ K i))
    (hsurj_im1 : Epi (derivedTensorWithAlgebraHomologyComparison κ K (i - 1))) :
    ∃ f : R,
        ∃ e :
          K ⊗[R]^L[Localization.Away f] ≅
            ((t.truncLE (i - 1)).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                ((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) i).obj
                  (ModuleCat.of (Localization.Away f) (Away f ((H i).obj K))))) ⊞
              (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
        f ∉ 𝔭.asIdeal ∧
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
            HasTorAmplitudeGE
              ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
              (i + 1) ∧
              Module.Free (Localization.Away f) (Away f ((H i).obj K)) ∧
                Module.Finite (Localization.Away f) (Away f ((H i).obj K)) := sorry

end

end CategoryTheory
