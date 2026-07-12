import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksProject_2024.Chap10.Lemma_10_110_8
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_19_3
import StacksProject_2024.Chap15.Lemma_15_77_1

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

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

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

/-- Helper for Lemma 15.80.3: a bounded-above derived object admits a bounded-above projective
representative whose image in the derived category is the original object. -/
-- TODO: restore the Chapter 13 projective-resolution construction after fixing the local
-- `EnoughProjectives (ModuleCat R)` universe elaboration for `Q.objPreimage K.obj`.
private theorem projective_resolution_model_of_boundedAbove
    (K : D⁻((ModuleCat R))) :
    ∃ P : CochainComplex.ProjectiveResolution (DerivedCategory.Q.objPreimage K.obj),
      ∃ b : ℤ,
        (P : Cpx).IsStrictlyLE b ∧
          Nonempty (DerivedCategory.Q.obj (P : Cpx) ≅ K.obj) := sorry

/-- Helper for Lemma 15.80.3: an upper truncation bound on `L` forces all cohomology in degrees
at least `k - d + 1` to vanish. -/
private theorem homology_vanishing_ge_of_isLE_cutoff
    (d : ℕ) {L : DMod} {k : ℤ}
    (hL : L.IsLE (k - d)) :
    ∀ i : ℤ, k - d + 1 ≤ i → IsZero ((H i).obj L) := by
  intro i hi
  have hi' : k - d < i := by
    omega
  simpa using isZero_of_isLE L (k - d) i hi'

/-- Helper for Lemma 15.80.3: over a ring of global dimension at most `d`, a bounded-above
derived object with no cohomology in degrees `≤ k` has projective amplitude starting in degree
`k - d + 1`. -/
private theorem projectiveAmplitude_of_isGE_boundedAbove_over_hasGlobalDimensionLE
    (d : ℕ) [HasGlobalDimensionLE R d]
    (K : D⁻((ModuleCat R))) {k : ℤ}
    (hK : K.obj.IsGE (k + 1)) :
    ∃ b : ℤ, HasProjectiveAmplitudeIn K.obj (k - d + 1) b := by
  -- Route correction: finite global dimension only yields the lower endpoint `k - d + 1`,
  -- not the over-strong cutoff `k + 1` from the original placeholder proof.
  obtain ⟨P, b, hPb, he⟩ := projective_resolution_model_of_boundedAbove (R := R) K
  obtain ⟨e⟩ := he
  -- TODO: prove the cutoff term of `P.truncGE (k - d + 1)` is projective by descending the
  -- projective-dimension bound along the exact opcycles sequence attached to `P`, then package
  -- that truncation as the amplitude witness using `e`.
  sorry

/-- Lemma 15.80.3: if `R` is a regular ring of finite Krull dimension `d`, if
`K : D⁻((ModuleCat R))`, if `L : D((ModuleCat R))` satisfies `L.IsLE (k - d)`, and if
`K.obj.IsGE (k + 1)`, then every morphism `K.obj ⟶ L` is zero. The bounded-above source object
is kept in the Chapter `13` owner `D⁻((ModuleCat R))`; the source upper-gap and lower-gap
hypotheses are recorded by the canonical owner data `L.IsLE (k - d)` and `K.obj.IsGE (k + 1)`;
and the finite-dimensional regularity input is carried by `[IsRegularRing R]` together with the
bridge datum `ringKrullDim R = d`. -/
theorem hom_eq_zero_of_boundedAbove_of_homology_gap_over_regularRing
    (d : ℕ) (hdim : ringKrullDim R = d) (K : D⁻((ModuleCat R)))
    {L : DMod} {k : ℤ}
    (hK : K.obj.IsGE (k + 1))
    (hL : L.IsLE (k - d))
    (f : K.obj ⟶ L) :
    f = 0 := by
  -- Route correction: replace the impossible amplitude bound starting at `k + 1` by the
  -- source-faithful bound `k - d + 1` coming from finite global dimension.
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
  obtain ⟨b, hKamp⟩ :=
    projectiveAmplitude_of_isGE_boundedAbove_over_hasGlobalDimensionLE
      (R := R) d K hK
  -- Apply the Chapter 15 amplitude-vanishing theorem once the target-side cohomology gap is
  -- rewritten in the required `i ≥ k - d + 1` form.
  exact
    hom_eq_zero_of_projectiveAmplitude_of_homology_vanishing_ge
      hKamp
      (homology_vanishing_ge_of_isLE_cutoff (R := R) d hL)
      f

end

end CategoryTheory
