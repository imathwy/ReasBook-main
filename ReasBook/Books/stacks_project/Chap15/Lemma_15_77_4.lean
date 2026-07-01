import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Definition_15_75_1
import stacks_project.Chap15.Lemma_15_60_3
import stacks_project.Chap15.Lemma_15_67_4
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

variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField
local notation "Hκ" => DerivedCategory.homologyFunctor (ModuleCat κ)

/- Domain-style sampling:
- primary domain: localization of pseudo-coherent derived objects, residue-field homology
  vanishing, and canonical gap splittings in the standard `t`-structure;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeGE`,
  `exists_localizationAway_split_of_residueField_homology_surjective`,
  `existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge`;
- best owner abstraction: this item is a `source-facing` zero-fiber specialization of
  `exists_localizationAway_split_of_residueField_homology_surjective`; the compatible splitting
  data should stay in the owner-level `∃! e` form rather than a local package;
- primitive data: `K`, `i`, the pseudo-coherence witness `hK`, and the vanishing of the derived
  residue-field homology object
  `((Hκ i).obj (K ⊗[R]^L[κ]))`;
- derived API: perfectness and tor-amplitude of the localized upper truncation, together with the
  unique compatible gap splitting.

Source/core/bridge triage:
- `source-facing`: the localization theorem below;
- `core/canonical`: `exists_localizationAway_split_of_residueField_homology_surjective`,
  `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, and the standard truncation API;
- `bridge/view`: the zero-fiber hypothesis in degree `i`, which upgrades the localized
  `τ_{\le i} ⊞ τ_{\ge i + 1}` splitting to the gap splitting
  `τ_{\le i - 1} ⊞ τ_{\ge i + 1}` without introducing a second owner abstraction.
-/

-- Proof sketch: apply Lemma `15.77.2` to the vanishing hypothesis, viewed as a trivially
-- surjective base-change map onto zero, to split off the perfect upper truncation after
-- inverting some `f ∉ 𝔭`. Then shrink once more so that the localized degree-`i` homology
-- vanishes, which identifies `τ_{\le i}` with `τ_{\le i - 1}` and yields the canonical gap
-- decomposition.
/-- Lemma 15.77.4: if `K^•` is a pseudo-coherent complex of `R`-modules and
`H^i(K^• \otimes_R^{\mathbf L} \kappa(\mathfrak p)) = 0`, then after inverting some
`f \notin \mathfrak p` the localized object `K^• \otimes_R^{\mathbf L} R_f` admits a canonical
direct-sum decomposition
`τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f) ⊕ τ_{\le i - 1}(K^• \otimes_R^{\mathbf L} R_f)`
in `D(R_f)`, and the upper summand is perfect with tor-amplitude in `[i + 1, ∞]`. -/
theorem exists_localizationAway_gapSplit_of_residueField_homology_isZero
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hHi : IsZero ((Hκ i).obj (K ⊗[R]^L[κ]))) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        HasTorAmplitudeGE
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          ∃! e :
              K ⊗[R]^L[Localization.Away f] ≅
                (t.truncLE (i - 1)).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                  (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
            ((t.truncLEι (i - 1)).app (K ⊗[R]^L[Localization.Away f])) ≫ e.hom = biprod.inl ∧
              e.hom ≫ biprod.snd =
                ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away f])) := sorry

end

end CategoryTheory
