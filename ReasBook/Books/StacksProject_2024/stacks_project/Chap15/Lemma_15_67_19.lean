import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_105_3
import StacksProject_2024.stacks_project.Chap15.Definition_15_67_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure
open scoped CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Bounded" => (t.bounded : ObjectProperty DMod)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling for Lemma 15.67.19:
- primary domain: tor-amplitude in the derived category of modules, boundedness via the
  derived-category t-structure, and weak-dimension bounds on the ring;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ModuleHasTorDimensionLE`,
  `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`,
  `t.bounded`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`;
- best owner abstraction: the ring-side primitive datum for these tor-dimension conclusions is the
  weak-dimension owner `HasWeakDimensionLE R d`, whose module-level consequence is the canonical
  owner `ModuleHasTorDimensionLE`; the stronger Chapter 10 owner `HasGlobalDimensionLE R d`
  belongs only to the bridge layer through the instance from Definition `15.105.3`; the canonical
  way to say that `K` has cohomology concentrated in `[a, b]` is the t-structure owner data
  `K.IsGE a` and `K.IsLE b`, not a parallel pointwise vanishing hypothesis;
- primitive vs. derived:
  primitive data are the ring bound `[HasWeakDimensionLE R d]` and the bounded-support owner
  data `K.IsGE a`, `K.IsLE b`;
  derived API is the resulting tor-amplitude interval and the bounded-derived equivalence;
- source/core/bridge triage:
  `source-facing`: the two tor-dimension consequences below;
  `core/canonical`: `HasWeakDimensionLE`, `ModuleHasTorDimensionLE`, `HasTorAmplitudeIn`,
    `HasFiniteTorDimension`, `t.bounded`, `K.IsGE a`, and `K.IsLE b`;
  `bridge/view`: the instance chain
    `HasGlobalDimensionLE R d ⟹ HasWeakDimensionLE R d ⟹ ModuleHasTorDimensionLE M d`, together
    with the cohomology-vanishing characterization of `K.IsGE a` and `K.IsLE b`; the former stays
    a bridge rather than a primitive hypothesis in this file.
-/

-- Proof sketch: if `K.IsGE a` and `K.IsLE b`, then `H^i(K)` vanishes unless `a ≤ i ≤ b`. For
-- the nonvanishing cohomology objects, the weak-dimension owner gives tor dimension at most `d`,
-- so their degree-zero derived objects have tor-amplitude in
-- `[(-d) - i, -i]`, hence in `[(a - d) - i, b - i]`. Apply Lemma `15.67.9`.
/-- Helper for Lemma 15.67.19: the zero object of `D(R)` has tor-amplitude in every interval. -/
lemma hasTorAmplitudeIn_of_isZero_local {K : DMod} (hK : IsZero K) (a b : ℤ) :
    HasTorAmplitudeIn K a b := by
  intro M i hi
  letI : (derivedTensorProduct ((single₀).obj M)).CommShift ℤ :=
    derivedTensorProduct_commShift ((single₀).obj M)
  letI : (derivedTensorProduct ((single₀).obj M)).IsTriangulated :=
    derivedTensorProduct_isTriangulated ((single₀).obj M)
  letI : (derivedTensorProduct ((single₀).obj M)).Additive := inferInstance
  letI : (derivedTensorProduct ((single₀).obj M)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  -- Tensor and homology preserve zero objects, so every test homology object vanishes.
  exact (H i).map_isZero <| (derivedTensorProduct ((single₀).obj M)).map_isZero hK

/-- If `R` has weak dimension at most `d` and the cohomology of `K` is concentrated in `[a, b]`,
then `K` has tor-amplitude in `[(a - d), b]`. -/
theorem hasTorAmplitudeIn_of_cohomology_concentrated_of_hasWeakDimensionLE
    (d : ℕ) [HasWeakDimensionLE R d] (K : DMod) (a b : ℤ) (hGE : K.IsGE a) (hLE : K.IsLE b) :
    HasTorAmplitudeIn K (a - (d : ℤ)) b := by
  by_cases hba : b < a
  · -- An empty cohomological support interval forces `K` to be zero.
    exact hasTorAmplitudeIn_of_isZero_local (R := R) (t.isZero K b a hba) (a - (d : ℤ)) b
  · have hnonneg : 0 ≤ b - a := by
      omega
    let n : ℕ := Int.toNat (b - a)
    have hab : a + n = b := by
      dsimp [n]
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    have hLE' : K.IsLE (a + n) := by
      simpa [hab] using hLE
    have hShifted :
        ∀ i : Set.Icc a (a + n),
          HasTorAmplitudeIn (shiftedCohomology Mod K i.1) (a - (d : ℤ)) b := by
      intro i
      let hwd : HasWeakDimensionLE R d := inferInstance
      have hModule :
          ModuleHasTorDimensionLE ((H i.1).obj K) d := hwd.hasTorDimensionLE ((H i.1).obj K)
      have hBase :
          HasTorAmplitudeIn ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj ((H i.1).obj K))
            ((i.1 - (d : ℤ)) - i.1) (i.1 - i.1) := by
        simpa [ModuleHasTorDimensionLE, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          hModule
      have hSingle :
          HasTorAmplitudeIn (shiftedCohomology Mod K i.1) (i.1 - (d : ℤ)) i.1 := by
        -- Convert the module-level tor-dimension bound on `H^i(K)` to the intrinsic shifted
        -- cohomology object `H^i(K)[-i]`.
        simpa [shiftedCohomology, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (singleFunctor_hasTorAmplitudeIn_iff (R := R) ((H i.1).obj K) i.1
            (i.1 - (d : ℤ)) i.1).2 hBase
      have hleft : a - (d : ℤ) ≤ i.1 - (d : ℤ) := by
        simpa [sub_eq_add_neg, add_assoc] using sub_le_sub_right i.2.1 (d : ℤ)
      have hright : i.1 ≤ b := by
        simpa [hab] using i.2.2
      -- Enlarge the interval from the individual degree `i` to the common support interval.
      exact hasTorAmplitudeIn_mono hSingle hleft hright
    -- Reassemble the finitely many shifted cohomology pieces along the support interval.
    exact
      hasTorAmplitudeIn_of_isGE_isLE_of_shiftedCohomology (R := R)
        (a - (d : ℤ)) b a n K hGE hLE' hShifted

/-- Helper for Lemma 15.67.19: evaluating tor-amplitude on the degree-zero copy of `R` shows
that ordinary cohomology of `K` vanishes outside the same interval. -/
noncomputable def regular_single0_tensorUnit_iso :
    (single₀).obj (ModuleCat.of R R) ≅ 𝟙_ DMod :=
  ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
    (ModuleCat.of R R)) ≪≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        (ModuleCat.of R R))).symm

/-- Helper for Lemma 15.67.19: tensoring with the degree-zero regular `R`-module is canonically
the identity on `D(R)`. -/
noncomputable def tensor_regular_single0_iso (K : DMod) :
    K ⊗[R]^L ((single₀).obj (ModuleCat.of R R)) ≅ K :=
  -- Proof comment: compare the chapter tensor notation with the derived tensor functor, then
  -- identify `R[0]` with the tensor unit and apply the right unitor.
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      K ((single₀).obj (ModuleCat.of R R))).symm ≪≫
    whiskerLeftIso K regular_single0_tensorUnit_iso ≪≫
      ρ_ K

/-- Helper for Lemma 15.67.19: evaluating tor-amplitude on the degree-zero copy of `R` shows
that ordinary cohomology of `K` vanishes outside the same interval. -/
lemma isZero_homology_of_hasTorAmplitudeIn_outside {K : DMod} {a b i : ℤ}
    (hK : HasTorAmplitudeIn K a b) (hi : i ∉ Set.Icc a b) :
    IsZero ((H i).obj K) := by
  let ringSingle : DMod := (single₀).obj (ModuleCat.of R R)
  have eTensor : K ⊗[R]^L ringSingle ≅ K := by
    simpa [ringSingle] using tensor_regular_single0_iso (R := R) K
  have hzeroTensor : IsZero ((H i).obj (K ⊗[R]^L ringSingle)) := by
    simpa [ringSingle] using hK (ModuleCat.of R R) i hi
  -- Transport the vanishing statement across the canonical tensor-unit comparison.
  exact hzeroTensor.of_iso ((H i).mapIso eTensor.symm)

/-- Helper for Lemma 15.67.19: tor-amplitude in a finite interval forces bounded cohomology
support, hence membership in `D^b(R)`. -/
lemma bounded_of_hasTorAmplitudeIn {K : DMod} {a b : ℤ}
    (hK : HasTorAmplitudeIn K a b) :
    Bounded K := by
  rw [derivedCategory_t_bounded_iff]
  constructor
  · refine ⟨a, ?_⟩
    intro i hi
    have hi_outside : i ∉ Set.Icc a b := by
      intro hmem
      exact (not_lt_of_ge hmem.1 hi).elim
    -- Degrees below `a` are excluded from the tor-amplitude interval.
    exact isZero_homology_of_hasTorAmplitudeIn_outside (R := R) hK hi_outside
  · refine ⟨b, ?_⟩
    intro i hi
    have hi_outside : i ∉ Set.Icc a b := by
      intro hmem
      exact (not_lt_of_ge hmem.2 hi).elim
    -- Degrees above `b` are excluded from the tor-amplitude interval.
    exact isZero_homology_of_hasTorAmplitudeIn_outside (R := R) hK hi_outside

-- Proof sketch: if `K` has finite tor dimension, test the defining tor-amplitude condition
-- against the unit module `R[0]` to see that the cohomology of `K` is supported in a finite
-- interval, hence `K` is bounded. Conversely, if `K` is bounded, choose an interval containing its
-- cohomology, apply the previous theorem to obtain finite tor-amplitude, and conclude that `K`
-- has finite tor dimension.
/-- Lemma 15.67.19: over a ring of weak dimension at most `d`, an object of `D(R)` has finite
tor dimension if and only if it satisfies the canonical boundedness owner `t.bounded`, i.e. if
and only if it belongs to the bounded derived category `D^b(R)`. -/
theorem hasFiniteTorDimension_iff_mem_boundedDerivedCategory
    (d : ℕ) [HasWeakDimensionLE R d] (K : DMod) :
    HasFiniteTorDimension K ↔ Bounded K := by
  constructor
  · rintro ⟨a, b, hAmp⟩
    -- Test tor-amplitude on the tensor unit to recover bounded cohomological support.
    exact bounded_of_hasTorAmplitudeIn (R := R) hAmp
  · intro hBounded
    rw [derivedCategory_t_bounded_iff] at hBounded
    rcases hBounded with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hGE : K.IsGE a := by
      -- Repackage the lower vanishing bound as the canonical `IsGE` owner.
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact ha i hi
    have hLE : K.IsLE b := by
      -- Repackage the upper vanishing bound as the canonical `IsLE` owner.
      rw [DerivedCategory.isLE_iff]
      intro i hi
      exact hb i hi
    -- Apply the uniform weak-dimension bound to the resulting finite cohomological interval.
    exact
      (hasTorAmplitudeIn_of_cohomology_concentrated_of_hasWeakDimensionLE
        (R := R) d K a b hGE hLE).hasFiniteTorDimension

end

end CategoryTheory
