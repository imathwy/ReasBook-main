import Mathlib
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {ι : Type*}

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.75.12:
- primary domain: local-global perfection in `D(R)` under localization away from a finite
  principal-open cover;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `isPseudoCoherent_of_localizationAway_unitIdeal`,
  `hasTorAmplitudeIn_of_localizationAway_unitIdeal`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction: this item is `source-facing`, while the canonical owners are
  `DerivedCategory.IsPerfect` with object-prefix theorem surface `K.IsPerfect`,
  `K.IsPseudoCoherent`, and `HasFiniteTorDimension K`;
- primitive vs. derived:
  the primitive data are the finite family `f`, the unit-ideal hypothesis, and the localized
  perfectness assumptions;
  pseudo-coherence and finite tor dimension are derived owner-level consequences and should not be
  stored as parallel local data;
- source/core/bridge triage:
  `source-facing`: perfection descends from a finite localization-away cover;
  `core/canonical`: the perfectness characterization by pseudo-coherence and finite tor dimension;
  `bridge/view`: the localized derived base-change objects
    `K ⊗[R]^L[Localization.Away (f i)]`. -/

-- Proof sketch: use Lemma `15.75.2` to reduce perfection to pseudo-coherence and finite tor
-- dimension. Pseudo-coherence descends directly by Lemma `15.65.14 (2)`. For finite tor
-- dimension, choose a tor-amplitude interval on each localization, enlarge them to one common
-- interval over the finite index set, descend that uniform tor-amplitude by Lemma `15.67.16`, and
-- then reassemble perfection with Lemma `15.75.2`.

/-- Helper for Lemma 15.75.12: enlarging an interval preserves tor-amplitude. -/
lemma hasTorAmplitudeIn_mono
    {S : Type u} [CommRing S]
    {L : DerivedCategory (ModuleCat S)} {a b a' b' : ℤ}
    (hL : HasTorAmplitudeIn L a b) (ha : a' ≤ a) (hb : b ≤ b') :
    HasTorAmplitudeIn L a' b' := by
  intro M i hi
  -- Any degree outside the larger interval is already outside the smaller interval.
  have houtside : i ∉ Set.Icc a b := by
    intro hi'
    exact hi ⟨le_trans ha hi'.1, le_trans hi'.2 hb⟩
  exact hL M i houtside

/-- Helper for Lemma 15.75.12: a finite family of interval witnesses can be enlarged to one
common interval when the owner predicate is monotone in the bounds. -/
lemma exists_common_interval_on_finset
    (P : ι → ℤ → ℤ → Prop)
    (hmono :
      ∀ i {a b a' b' : ℤ}, P i a b → a' ≤ a → b ≤ b' → P i a' b')
    (s : Finset ι)
    (hP : ∀ i, i ∈ s → ∃ a b : ℤ, P i a b) :
    ∃ a b : ℤ, ∀ i, i ∈ s → P i a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, 0, ?_⟩
      -- The empty family imposes no interval conditions.
      intro i hi
      have hfalse : False := by
        simpa using hi
      exact False.elim hfalse
  | @insert i s hi hs =>
      rcases hP i (Finset.mem_insert_self i s) with ⟨a₀, b₀, hiP⟩
      rcases hs (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj)) with ⟨a₁, b₁, hsP⟩
      refine ⟨min a₀ a₁, max b₀ b₁, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hEq | hj'
      · -- Enlarge the interval chosen for the newly inserted index.
        simpa [hEq] using hmono i hiP (min_le_left _ _) (le_max_left _ _)
      · -- Enlarge the common interval already chosen on the tail of the finite set.
        exact hmono j (hsP j hj') (min_le_right _ _) (le_max_right _ _)

/-- Helper for Lemma 15.75.12: perfect objects are exactly the pseudo-coherent objects of finite
tor dimension. -/
lemma isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
    (K : DerivedCategory (ModuleCat.{u} R)) :
    K.IsPerfect ↔ K.IsPseudoCoherent ∧ HasFiniteTorDimension K := by
  let _ := K
  sorry

/-- Helper for Lemma 15.75.12: pseudo-coherence descends from a finite localization-away cover. -/
lemma isPseudoCoherent_of_localizationAway_unitIdeal
    [Finite ι]
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPseudoCoherent) :
    K.IsPseudoCoherent := by
  let _ := hunit
  let _ := hloc
  sorry

/-- Helper for Lemma 15.75.12: a uniform tor-amplitude bound descends from a finite
localization-away cover. -/
lemma hasTorAmplitudeIn_of_localizationAway_unitIdeal
    [Finite ι]
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hloc : ∀ i,
      HasTorAmplitudeIn (K ⊗[R]^L[Localization.Away (f i)]) a b) :
    HasTorAmplitudeIn K a b := by
  let _ := hunit
  let _ := hloc
  sorry

/-- Lemma 15.75.12: if a finite family `f : ι → R` generates the unit ideal and each derived
localization `K^• ⊗_R R_{f_i}` is perfect, then `K^•` is perfect. -/
theorem isPerfect_of_localizationAway_unitIdeal
    [Finite ι]
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPerfect) :
    K.IsPerfect := by
  have hbase :
      ∀ i,
        (K ⊗[R]^L[Localization.Away (f i)]).IsPseudoCoherent ∧
          HasFiniteTorDimension (K ⊗[R]^L[Localization.Away (f i)]) := by
    intro i
    -- Decompose localized perfectness into the two source-facing invariants from Lemma `15.75.2`.
    exact
      (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
        (K ⊗[R]^L[Localization.Away (f i)])).1
        (hloc i)
  -- Reassemble perfectness once the two descent statements are established globally.
  refine (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension K).2 ?_
  refine ⟨?_, ?_⟩
  · -- Descend pseudo-coherence directly from the localization-away cover.
    exact
      isPseudoCoherent_of_localizationAway_unitIdeal f hunit K
        (fun i ↦ (hbase i).1)
  · let _ : Fintype ι := Fintype.ofFinite ι
    have hinterval :
        ∀ i,
          ∃ a b : ℤ,
            HasTorAmplitudeIn (K ⊗[R]^L[Localization.Away (f i)]) a b := by
      intro i
      exact
        (hasFiniteTorDimension_iff (K ⊗[R]^L[Localization.Away (f i)])).1
          (hbase i).2
    have hmem_univ : ∀ i : ι, i ∈ (Finset.univ : Finset ι) := by
      intro i
      simp
    rcases
        exists_common_interval_on_finset
          (P := fun i a b ↦
            HasTorAmplitudeIn (K ⊗[R]^L[Localization.Away (f i)]) a b)
          (hmono := by
            intro i a b a' b' htor ha hb
            exact hasTorAmplitudeIn_mono htor ha hb)
          (s := Finset.univ)
          (hP := by
            intro i _
            exact hinterval i) with
      ⟨a, b, hab⟩
    have htor : HasTorAmplitudeIn K a b := by
      -- Uniformize the local intervals first, then descend that common tor-amplitude bound.
      apply hasTorAmplitudeIn_of_localizationAway_unitIdeal f hunit K a b
      intro i
      exact hab i (hmem_univ i)
    exact htor.hasFiniteTorDimension

end

end CategoryTheory
