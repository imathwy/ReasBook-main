import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import stacks_project.Chap10.Lemma_10_110_8
import stacks_project.Chap13.Definition_13_11_3
import stacks_project.Chap15.Lemma_15_77_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open DerivedCategory.TStructure
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsRegularRing R]

/- Domain-style sampling:
- primary domain: hom-vanishing in `D((ModuleCat R))` over a regular ring of finite Krull
  dimension, with the bounded-above source object expressed through the Chapter `13` notation
  `D⁻((ModuleCat R))`;
- sampled owner declarations:
  `IsRegularRing`,
  `ringKrullDim`,
  `finiteGlobalDimension_regularRing_localizations_tfae`,
  `HasGlobalDimensionLE`,
  `globalDimension`,
  `boundedAboveDerivedCategory` and its notation `D⁻(-)`,
  `DerivedCategory.IsLE`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge`,
  `CochainComplex.derivedCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge`;
- best owner abstraction: this lemma is a `bridge/view` specialization of the projective-amplitude
  hom-vanishing owner to the regular finite-dimension setting. The ring-side canonical owner used
  by the proof is the induced finite-global-dimension data obtained from
  `[IsRegularRing R]` and `ringKrullDim R = d` through
  `finiteGlobalDimension_regularRing_localizations_tfae`, while the bounded-above source object
  should use the chapter owner `D⁻((ModuleCat R))` rather than a separate membership proof in
  `t.minus`;
- primitive data: `d`, the owner instance `[IsRegularRing R]`, the bridge datum
  `hdim : ringKrullDim R = d`, the bounded-above source object `K : D⁻((ModuleCat R))`, the
  target object `L : D((ModuleCat R))`, the lower-gap owner datum `K.obj.IsGE (k + 1)`, and the
  upper-gap owner datum `L.IsLE (k - d)`;
- derived API: the vanishing of every morphism `K.obj ⟶ L` in `D((ModuleCat R))`.

Source/core/bridge triage:
- `source-facing`: Lemma `15.80.3`;
- `core/canonical`: `HasGlobalDimensionLE R d`, `D((ModuleCat R))`, `D⁻((ModuleCat R))`,
  `HasProjectiveAmplitudeIn`, `IsGE`, and `IsLE`;
- `bridge/view`: the finite-dimensional equality `ringKrullDim R = d` together with the derived
  finite-global-dimension owner coming from
  `finiteGlobalDimension_regularRing_localizations_tfae`.
-/

/-- Lemma 15.80.3: if `R` is a regular ring of finite Krull dimension `d`, if
`K : D⁻((ModuleCat R))`, if `L : D((ModuleCat R))` satisfies `L.IsLE (k - d)`, and if
`K.obj.IsGE (k + 1)`, then every morphism `K.obj ⟶ L` is zero. The bounded-above source object
is kept in the Chapter `13` owner `D⁻((ModuleCat R))`; the source upper-gap and lower-gap
hypotheses are recorded by the canonical owner data `L.IsLE (k - d)` and `K.obj.IsGE (k + 1)`;
and the finite-dimensional regularity input is carried by `[IsRegularRing R]` together with the
bridge datum `ringKrullDim R = d`. -/
theorem hom_eq_zero_of_boundedAbove_of_homology_gap_over_regularRing
    (d : ℕ) (hdim : ringKrullDim R = d) (K : D⁻((ModuleCat R)))
    {L : D((ModuleCat R))} {k : ℤ}
    (hK : K.obj.IsGE (k + 1))
    (hL : L.IsLE (k - d))
    (f : K.obj ⟶ L) :
    f = 0 := by
  obtain ⟨b, hKb⟩ := K.property
  have htfae :
      List.TFAE
        [ ∃ _ : IsFiniteGlobalDimensionRing R, globalDimension R = d
        , IsRegularRing R ∧ ringKrullDim R = d
        , (∀ m : MaximalSpectrum R,
              IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
                ringKrullDim (Localization.AtPrime m.asIdeal) ≤ d) ∧
            ∃ m : MaximalSpectrum R, ringKrullDim (Localization.AtPrime m.asIdeal) = d
        , (∀ p : PrimeSpectrum R,
              IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
                ringKrullDim (Localization.AtPrime p.asIdeal) ≤ d) ∧
            ∃ p : PrimeSpectrum R, ringKrullDim (Localization.AtPrime p.asIdeal) = d ] :=
    finiteGlobalDimension_regularRing_localizations_tfae d
  have hregularDim : IsRegularRing R ∧ ringKrullDim R = d := ⟨inferInstance, hdim⟩
  have hfiniteGlobal :
      ∃ _ : IsFiniteGlobalDimensionRing R, globalDimension R = d :=
    (htfae.out 1 0).mp hregularDim
  rcases hfiniteGlobal with ⟨hfgd, hglobal⟩
  letI : IsFiniteGlobalDimensionRing R := hfgd
  letI : HasGlobalDimensionLE R d := by
    simpa [hglobal] using hasGlobalDimensionLE_globalDimension R
  letI : K.obj.IsGE (k + 1) := hK
  letI : K.obj.IsLE b := hKb
  letI : L.IsLE (k - d) := hL
  have hKamp : HasProjectiveAmplitudeIn K.obj (k + 1) b := by
    sorry
  exact hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge hKamp
    (fun i hi ↦ by
      have hi' : k - d < i := by
        omega
      simpa using isZero_of_isLE L (k - d) i hi')
    f

end

end CategoryTheory
