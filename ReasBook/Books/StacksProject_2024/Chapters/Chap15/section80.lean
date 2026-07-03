import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_80_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.ObjectProperty
open scoped CategoryTheory.ObjectProperty.GeneratedNotation

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.80.1:
- primary domain: ghost maps in the derived category `D(R)`, detected by the canonical homology
  functor family and combined along finite chains of composable arrows;
- sampled owner declarations:
  `H^i`,
  `ComposableArrows`,
  `objectGeneratedStage_eq_iSup_intervalStages`,
  `exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero`;
- best owner abstraction: the source-facing stage condition should use the Chapter 13 owner
  `⟨ringSingle⟩_n`, the chain itself is canonically a `ComposableArrows`, and the stepwise
  vanishing mechanism is already owned upstream by
  `exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero`; the stage hypothesis should be
  converted only through the Chapter 13 interval-stage bridge, not through a new local ghost
  wrapper;
- primitive vs. derived:
  primitive data are the stage-membership hypothesis on the leftmost object and the degreewise
  vanishing of each arrow under all cohomology functors;
  derived API is the vanishing of the total composite, obtained by converting the stage
  hypothesis through the interval-stage bridge and then applying the owner-level truncation
  factorization from Lemma `13.12.5`.

Source/core/bridge triage:
- `source-facing`: the ghost hypothesis and the zero-composite conclusion;
- `core/canonical`: `⟨ringSingle⟩_n`, `ComposableArrows`, `H^i`,
  `exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero`;
- `bridge/view`: `objectGeneratedStage_eq_iSup_intervalStages`, used only to pass from the
  source-facing stage hypothesis to the canonical bounded-support owner. -/

-- Proof sketch: use `objectGeneratedStage_eq_iSup_intervalStages` only as a bridge from
-- `X.left ∈ ⟨ringSingle⟩_n` to an interval-stage presentation with explicit cohomological
-- support. After shifting so that the support interval starts in degree `0`, apply
-- `exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero`; the resulting factorization
-- passes through a truncation object that vanishes because the shifted source has cohomology
-- supported in fewer than `n` consecutive degrees. Undo the shift to obtain `X.hom = 0`.
/-- Lemma 15.80.1: if the leftmost object of a chain of composable morphisms in `D(R)` lies in
`⟨R[0]⟩_n` and every arrow is ghost, then the composite of the chain is zero. -/
theorem ghost_composite_zero_of_mem_objectGeneratedStage
    {n : ℕ+} {X : ComposableArrows DMod n}
    (hX : (⟨ringSingle⟩_n) X.left)
    (hghost : ∀ j (hj : j < n) (i : ℤ), (H^i).map (X.arrow j hj).hom = 0) :
    X.hom = 0 := sorry

end

end CategoryTheory

/-! ### Lemma_15_80_2 (from Chap15) -/
noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-
Domain-style sampling for Lemma 15.80.2:
- primary domain: strong generators in the perfect derived category of a Noetherian ring and the
  Chapter 10 owner API for regular rings of finite Krull dimension;
- sampled owner declarations:
  `IsStrongGenerator`,
  `ringSingleInPerfectDerived`,
  `IsRegularRing`,
  `finiteGlobalDimension_regularRing_localizations_tfae`;
- best owner abstraction: the ring-side owner inside the conclusion is `IsRegularRing R`, but the
  source-facing main theorem must keep the combined finite-dimensional regularity conclusion
  `∃ n : ℕ, IsRegularRing R ∧ ringKrullDim R = n`;
- primitive vs. derived: primitive data here is only the strong-generation hypothesis on `R[0]`
  in `D_{perf}(R)`; the source-facing combined existential conclusion is the full derived API; the
  regularity owner `IsRegularRing R` and the explicit dimension witness remain logically derived
  consequences rather than separate public declarations;
- source/core/bridge triage:
  `source-facing`: the implication from strong generation of `R[0]` to the existence of a finite
    Krull-dimension witness together with `IsRegularRing R`;
  `core/canonical`: `IsRegularRing R`;
  `bridge/view`: any downstream extraction of the explicit equality `ringKrullDim R = n` from the
    source-facing existential conclusion.
-/

-- Proof sketch: apply the strong-generation hypothesis to the canonical object `R[0]` in
-- `D_{perf}(R)` and use Lemma `15.80.1` to force vanishing of composites of sufficiently many
-- ghosts. Represent finite modules by bounded finite free complexes in `D_{perf}(R)` to deduce
-- vanishing of high `Ext`, hence finite global dimension by Lemma `10.109.12`, and then conclude
-- with Lemma `10.110.8` that `R` is regular of some finite Krull dimension.
/-- Lemma 15.80.2: if the canonical object `R[0]` is a strong generator of the perfect derived
category `D_{perf}(R)`, then `R` is a regular ring of finite Krull dimension. -/
theorem exists_regularRing_and_ringKrullDim_eq_of_ringSingleInPerfectDerived_isStrongGenerator
    (hstrong : IsStrongGenerator (ringSingleInPerfectDerived R)) :
    ∃ n : ℕ, IsRegularRing R ∧ ringKrullDim R = n := sorry

end

end CategoryTheory

/-! ### Lemma_15_80_3 (from Chap15) -/
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

/-! ### Lemma_15_80_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R] [IsRegularRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling:
- primary domain: perfect objects in `D(R)` over a regular ring of finite Krull dimension, and
  splitting of the canonical truncation triangle along a cohomology gap;
- sampled owner declarations:
  `IsRegularRing`,
  `ringKrullDim`,
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ`,
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
- best owner abstraction: the ring-side core owner is `[IsRegularRing R]`, and the finite
  Krull-dimension clause should stay as the direct bridge datum `ringKrullDim R = d`; this item is
  the `source-facing`
  perfect-complex specialization of the split-triangle owner
  `exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ`
  applied to the canonical truncation triangle; the compatibility data should stay in the
  owner theorem's native pair of equations rather than a repackaged local predicate;
- primitive data: `d`, the owner instance `[IsRegularRing R]`, the bridge datum
  `hdim : ringKrullDim R = d`, the perfectness of `K`, and the cohomology-gap hypothesis;
- derived API: the compatible biproduct decomposition of `K` into the lower and upper truncations.

Source/core/bridge triage:
- `source-facing`: the specific truncation-gap splitting statement below;
- `core/canonical`: `[IsRegularRing R]` for the ring-side hypothesis and the split-triangle
  owner from Lemma `15.77.1`;
- `bridge/view`: the regular-ring/perfect specialization supplying the projective-amplitude input
  needed by that owner.
-/

-- Proof sketch: apply the canonical owner
-- `exists_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge_succ`
-- to the truncation triangle
-- `τ_{\le k - d + 1} K ⟶ K ⟶ τ_{\ge k + 1} K ⟶ τ_{\le k - d + 1} K⟦1⟧`.
-- The upper truncation has projective amplitude starting in degree `k + 1` because `K` is
-- perfect over the regular ring `R`; the equality `ringKrullDim R = d` is a separate bridge
-- datum, and Lemma `15.80.3` gives the required vanishing of maps
-- into the shifted lower truncation from the stated cohomology gap.
/-- Lemma 15.80.4: over a regular ring `R` of Krull dimension `d`, a perfect
object `K` of `D(R)` whose cohomology vanishes in degrees `k - d + 2, \ldots, k` admits a direct
sum decomposition
`K ≅ τ_{\le k - d + 1} K ⊞ τ_{\ge k + 1} K`
compatible with the canonical truncation maps. -/
theorem exists_truncation_gap_biprod_of_isPerfect_of_homology_vanishing
    (d : ℕ) (hdim : ringKrullDim R = d) (K : DMod) (k : ℤ)
    (hperfect : K.IsPerfect)
    (hvanish : ∀ i : ℤ, k - d + 2 ≤ i → i ≤ k → IsZero ((H i).obj K)) :
    ∃ e : K ≅ (t.truncLE (k - d + 1)).obj K ⊞ (t.truncGE (k + 1)).obj K,
      ((t.truncLEι (k - d + 1)).app K) ≫ e.hom = biprod.inl ∧
        e.hom ≫ biprod.snd = ((t.truncGEπ (k + 1)).app K) := sorry

end

/-! ### Lemma_15_80_5 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] [IsRegularRing R]

/-
Domain-style sampling for Lemma 15.80.5:
- primary domain: strong generators in the perfect derived category of a regular ring;
- sampled owner declarations:
  `IsRegularRing`,
  `Ring.KrullDimLE`,
  `Ring.krullDimLE_iff`,
  `IsStrongGenerator`,
  `DPerf`,
  `ringSingleInPerfectDerived`;
- best owner abstraction: the ring-side owners are `[IsRegularRing R]` together with the explicit
  finite-dimensional bridge `∃ d : ℕ, Ring.KrullDimLE d R`, since the conclusion only needs a
  finite dimension bound and not a chosen exact value;
- primitive vs. derived:
  primitive data are `R`, the owner instance `[IsRegularRing R]`, and the finite-dimensional
  bridge `∃ d : ℕ, Ring.KrullDimLE d R`;
- source/core/bridge triage:
  `source-facing`: the textbook regular-plus-finite-Krull-dimension hypothesis;
  `core/canonical`: `IsRegularRing R`;
  `bridge/view`: the explicit existence of a Krull-dimension bound.
-/

-- Proof sketch: choose `d` with `Ring.KrullDimLE d R`. By Lemma `15.75.14`, every perfect complex
-- is bounded with finite cohomology modules, and regularity plus this dimension bound control the
-- projective dimensions of those cohomology modules by `d`. Induct on that bound using the
-- standard triangle built from finite free surjections onto cohomology modules to show every
-- perfect object lies in the `(d + 1)`st extension stage generated by shifts of `R[0]`.
/-- Lemma 15.80.5: if `R` is a regular ring of finite Krull dimension, then the degree-zero object
`R[0]` is a strong generator of the perfect derived category `D_{perf}(R)`. The finite-dimensional
hypothesis is carried by the canonical bound-existence bridge `∃ d : ℕ, Ring.KrullDimLE d R`. -/
theorem ringSingleInPerfectDerived_isStrongGenerator
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d R) :
    IsStrongGenerator (ringSingleInPerfectDerived R) := by
  sorry

end

end CategoryTheory

/-! ### Proposition_15_80_6 (from Chap15) -/
noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/- Domain-style sampling for Proposition 15.80.6:
- primary domain: strong generators in the perfect derived category of a Noetherian ring;
- sampled owner declarations:
  `IsRegularRing`,
  `Ring.KrullDimLE`,
  `DPerf`,
  `IsStrongGenerator`,
  `ringSingleInPerfectDerived`,
  `strong_generator_of_classical_generator`;
- best owner abstraction: the proposition is a source-facing `List.TFAE`, but clause `(1)` should
  split the ring-side content into the owner `IsRegularRing R` and the canonical finite-dimension
  bridge `∃ d : ℕ, Ring.KrullDimLE d R`, avoiding a non-canonical exact-dimension witness in the
  main TFAE; clause `(3)` is canonically owned by the distinguished object
  `ringSingleInPerfectDerived : DPerf R`;
- primitive vs. derived:
  primitive data are exactly the three proposition clauses;
  clause `(2)` is only the derived existence statement that `DPerf R` has some strong generator,
  so the proof should reuse the chapter owner theorem upgrading the canonical classical generator
  `R[0]` to a strong generator instead of introducing a local wrapper for this existence clause;
- source/core/bridge triage:
  `source-facing`: the three-way equivalence in the proposition;
  `core/canonical`: `IsRegularRing`, `Ring.KrullDimLE`, `IsStrongGenerator`, `DPerf`, and
    `ringSingleInPerfectDerived`;
  `bridge/view`: the existential middle clause relating the source-facing formulation to the
    canonical object `R[0]`, together with the source-facing finite-dimension clause `(1)`.
-/

-- Proof sketch: Lemma `15.80.5` gives `(1) → (3)`. Clause `(3) → (2)` is immediate by taking the
-- exhibited generator. For `(2) → (3)`, combine the classical-generation statement for `R[0]` in
-- `D_{perf}(R)` with Derived Categories, Lemma `13.36.6`, which upgrades any classical generator
-- in a triangulated category admitting a strong generator to a strong generator. Finally, the
-- exact-dimension output of Lemma `15.80.2` is used only as an internal bridge to recover the
-- canonical finite-dimensional clause `(1)` from the canonical object `R[0]`.
/-- Proposition 15.80.6: for a Noetherian ring `R`, the following are equivalent: `R` is regular
of finite Krull dimension, the perfect derived category `D_{perf}(R)` has a strong generator, and
the canonical object `R[0]` is a strong generator of `D_{perf}(R)`. Clause `(1)` records finite
Krull dimension in the canonical owner form `∃ d : ℕ, Ring.KrullDimLE d R`, rather than by
choosing an exact dimension value in the public statement. -/
theorem regularFiniteKrullDimension_tfae_perfectDerived_hasStrongGenerator_ringSingleStrongGenerator :
    List.TFAE
      [IsRegularRing R ∧ ∃ d : ℕ, Ring.KrullDimLE d R,
        ∃ E : DPerf R, IsStrongGenerator E,
        IsStrongGenerator (ringSingleInPerfectDerived R)] := by
  tfae_have 1 → 3 := fun h ↦ by
    rcases h with ⟨hreg, hfinite⟩
    letI : IsRegularRing R := hreg
    exact ringSingleInPerfectDerived_isStrongGenerator hfinite
  tfae_have 3 → 2 := fun h ↦
    ⟨ringSingleInPerfectDerived R, h⟩
  tfae_have 2 → 3 := fun h ↦ by
    rcases h with ⟨E, hE⟩
    exact strong_generator_of_classical_generator
      (ringSingleInPerfectDerived R)
      ⟨E, hE⟩
      ring_single_isClassicalGenerator_in_perfectDerivedCategory
  tfae_have 3 → 1 := fun h ↦ by
    rcases
        exists_regularRing_and_ringKrullDim_eq_of_ringSingleInPerfectDerived_isStrongGenerator h
      with ⟨d, hreg, hdim⟩
    exact ⟨hreg, ⟨d, Ring.krullDimLE_iff.mpr (by simpa [hdim])⟩⟩
  tfae_finish

end

end CategoryTheory
