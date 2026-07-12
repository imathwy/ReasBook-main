import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_3_4
import LinearRepresentations_Serre_1977.Chap04.Definition_4_9
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5
import Mathlib.MeasureTheory.Group.Measure

noncomputable section
classical

open Subgroup
open scoped BigOperators Pointwise

-- Semantic recall: `Representation.character_eq_sum_over_representatives_of_equiv_induced`
-- is the canonical owner for Serre's representative-sum induced-character formula.

universe u v

namespace Representation

local instance subgroupMemDecidablePred {G : Type u} [Group G] (H : Subgroup G) :
    DecidablePred fun x : G ↦ x ∈ H :=
  Classical.decPred _

section CompactInducedCharacters

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G] [CompactSpace G]
  [IsTopologicalGroup G]
variable (H : Subgroup G) [H.FiniteIndex]
variable {W : Type (max u v)} [AddCommGroup W] [Module ℂ W]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℂ W]
  [FiniteDimensional ℂ W]
variable (θ : Representation ℂ H W) [Representation.IsContinuous θ]

omit [TopologicalSpace G] [T2Space G] [CompactSpace G] [IsTopologicalGroup G] [H.FiniteIndex]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [FiniteDimensional ℂ W]
  [Representation.IsContinuous θ] in
/-- Helper for Theorem 4-45: the character summand attached to `r * h` depends only on the
left-coset representative `r`. -/
lemma leftCosetCharacterSummand_right_mul_eq
    (u r : G) (h : H) :
    (if hsur : (r * h : G)⁻¹ * u * (r * h : G) ∈ H then
      θ.character ⟨(r * h : G)⁻¹ * u * (r * h : G), hsur⟩
    else 0) =
      (if hur : r⁻¹ * u * r ∈ H then
        θ.character ⟨r⁻¹ * u * r, hur⟩
      else 0) := by
  -- Right multiplication by `h ∈ H` only conjugates `r⁻¹ * u * r` inside `H`.
  by_cases hur : r⁻¹ * u * r ∈ H
  · have hsur : (r * h : G)⁻¹ * u * (r * h : G) ∈ H := by
      simpa [mul_assoc] using H.mul_mem (H.mul_mem (H.inv_mem h.2) hur) h.2
    have hconj :
        IsConj
          (⟨(r * h : G)⁻¹ * u * (r * h : G), hsur⟩ : H)
          ⟨r⁻¹ * u * r, hur⟩ := by
      refine isConj_iff.2 ?_
      refine ⟨h, ?_⟩
      apply Subtype.ext
      simp [mul_assoc]
    rw [dif_pos hsur, dif_pos hur]
    exact (character_isClassFunction θ).eq_of_isConj hconj
  · have hsur : ¬ (r * h : G)⁻¹ * u * (r * h : G) ∈ H := by
      intro hsur
      apply hur
      simpa [mul_assoc] using H.mul_mem (H.mul_mem h.2 hsur) (H.inv_mem h.2)
    rw [dif_neg hsur, dif_neg hur]

omit [TopologicalSpace G] [T2Space G] [CompactSpace G] [IsTopologicalGroup G] [H.FiniteIndex]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℂ W]
  [Representation.IsContinuous θ] in
/-- Helper for Theorem 4-45: summing the character summand over one left coset contributes
`Nat.card H` times the representative term. -/
lemma leftCosetCharacterBlockSum [Finite G]
    (u r : G) :
    ∑ h : H,
      (if hsur : (r * h : G)⁻¹ * u * (r * h : G) ∈ H then
        θ.character ⟨(r * h : G)⁻¹ * u * (r * h : G), hsur⟩
      else 0) =
      (Nat.card H : ℂ) *
        (if hur : r⁻¹ * u * r ∈ H then
          θ.character ⟨r⁻¹ * u * r, hur⟩
        else 0) := by
  -- Each summand in the left-coset block is constant by the previous conjugacy calculation.
  have hconst (h : H) :
      (if hsur : (r * h : G)⁻¹ * u * (r * h : G) ∈ H then
        θ.character ⟨(r * h : G)⁻¹ * u * (r * h : G), hsur⟩
      else 0) =
        (if hur : r⁻¹ * u * r ∈ H then
          θ.character ⟨r⁻¹ * u * r, hur⟩
        else 0) :=
    leftCosetCharacterSummand_right_mul_eq H θ u r h
  calc
    ∑ h : H,
        (if hsur : (r * h : G)⁻¹ * u * (r * h : G) ∈ H then
          θ.character ⟨(r * h : G)⁻¹ * u * (r * h : G), hsur⟩
        else 0)
        = ∑ _h : H,
            (if hur : r⁻¹ * u * r ∈ H then
              θ.character ⟨r⁻¹ * u * r, hur⟩
            else 0) := by
              simpa using
                (Fintype.sum_congr
                  (fun h : H ↦
                    if hsur : (r * h : G)⁻¹ * u * (r * h : G) ∈ H then
                      θ.character ⟨(r * h : G)⁻¹ * u * (r * h : G), hsur⟩
                    else 0)
                  (fun _h : H ↦
                    if hur : r⁻¹ * u * r ∈ H then
                      θ.character ⟨r⁻¹ * u * r, hur⟩
                    else 0)
                  hconst)
    _ = (Nat.card H : ℂ) *
          (if hur : r⁻¹ * u * r ∈ H then
            θ.character ⟨r⁻¹ * u * r, hur⟩
          else 0) := by
            simp [Nat.card_eq_fintype_card]

omit [TopologicalSpace G] [T2Space G] [CompactSpace G] [IsTopologicalGroup G] [H.FiniteIndex]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℂ W]
  [Representation.IsContinuous θ] in
/-- Helper for Theorem 4-45: reindexing the full group sum by a left transversal factors it into
left-coset blocks. -/
lemma sumOverGroup_eq_cardSubgroup_mul_sumOverRepresentatives [Finite G]
    (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G)) (u : G) :
    ∑ s : G,
      (if hsu : s⁻¹ * u * s ∈ H then
        θ.character ⟨s⁻¹ * u * s, hsu⟩
      else 0) =
      (Nat.card H : ℂ) *
        ∑ r ∈ R,
          (if hur : r⁻¹ * u * r ∈ H then
            θ.character ⟨r⁻¹ * u * r, hur⟩
          else 0) := by
  classical
  let summand : G → ℂ := fun s ↦
    if hsu : s⁻¹ * u * s ∈ H then
      θ.character ⟨s⁻¹ * u * s, hsu⟩
    else 0
  have hsum :
      ∑ s : G, summand s = ∑ p : ↥(R : Set G) × H, summand (p.1 * p.2) := by
    -- The complement equivalence rewrites the group sum as a double sum over representatives.
    refine Fintype.sum_equiv hR.equiv summand (fun p ↦ summand (p.1 * p.2)) ?_
    intro s
    simpa [summand] using congrArg summand (hR.equiv_fst_mul_equiv_snd s).symm
  have hinner (r : ↥(R : Set G)) :
      ∑ h : H, summand ((r : G) * h) =
        (Nat.card H : ℂ) * summand r := by
    -- Inside a fixed block, the subgroup factor does not change the character term.
    calc
      ∑ h : H, summand ((r : G) * h)
          = ∑ h : H,
              (if hsur : ((r : G) * h : G)⁻¹ * u * ((r : G) * h : G) ∈ H then
                θ.character ⟨((r : G) * h : G)⁻¹ * u * ((r : G) * h : G), hsur⟩
              else 0) := by
                rfl
      _ = (Nat.card H : ℂ) *
            (if hur : (r : G)⁻¹ * u * r ∈ H then
              θ.character ⟨(r : G)⁻¹ * u * r, hur⟩
            else 0) := by
              simpa [summand] using leftCosetCharacterBlockSum H θ u (r : G)
      _ = (Nat.card H : ℂ) * summand r := by
            rfl
  -- Flatten the double sum into one block sum for each representative.
  calc
    ∑ s : G, summand s = ∑ p : ↥(R : Set G) × H, summand (p.1 * p.2) := hsum
    _ = ∑ r : ↥(R : Set G), ∑ h : H, summand ((r : G) * h) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ r : ↥(R : Set G), (Nat.card H : ℂ) * summand r := by
          simpa using
            (Fintype.sum_congr
              (fun r : ↥(R : Set G) ↦ ∑ h : H, summand ((r : G) * h))
              (fun r : ↥(R : Set G) ↦ (Nat.card H : ℂ) * summand r)
              hinner)
    _ = (Nat.card H : ℂ) * ∑ r : ↥(R : Set G), summand r := by
          simp [Finset.mul_sum]
    _ = (Nat.card H : ℂ) *
          ∑ r ∈ R,
            (if hur : r⁻¹ * u * r ∈ H then
              θ.character ⟨r⁻¹ * u * r, hur⟩
            else 0) := by
          rw [← Finset.sum_attach R
            (fun r : G ↦
              if hur : r⁻¹ * u * r ∈ H then
                θ.character ⟨r⁻¹ * u * r, hur⟩
              else 0)]
          rfl

omit [TopologicalSpace G] [T2Space G] [CompactSpace G] [IsTopologicalGroup G] [H.FiniteIndex]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℂ W]
  [Representation.IsContinuous θ] in
/-- Theorem 4-45 — Character Formula for Finite-Index Induction.

Let `ρ = Representation.ind H.subtype θ`, and let `R` be a finite system of representatives for
`G / H` in the left-coset convention. Then for each `u : G`, the character of `ρ` at `u` is the
sum of the values of `θ.character` over those `r ∈ R` with `r⁻¹ * u * r ∈ H`. -/
theorem inducedCharacter_eq_sum_over_representatives
    (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G)) (u : G) :
    (Representation.ind H.subtype θ).character u =
      ∑ r ∈ R,
        if hur : r⁻¹ * u * r ∈ H then
          θ.character ⟨r⁻¹ * u * r, hur⟩
        else
          0 := by
  -- The Chapter 3 representative-sum theorem already matches this compact finite-index setting.
  letI : H.FiniteIndex := (hR.finite_left_iff).1 inferInstance
  simpa using
    Representation.character_eq_sum_over_representatives_of_equiv_induced
      (Representation.ind H.subtype θ) H θ (Representation.Equiv.refl _) R hR u

omit [TopologicalSpace G] [T2Space G] [CompactSpace G] [IsTopologicalGroup G] [H.FiniteIndex]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℂ W]
  [Representation.IsContinuous θ] in
/-- Companion finite-group specialization of Theorem 4-45: when `G` is finite, the same
character value is the average over all `s : G`, with denominator `Nat.card H`. -/
theorem inducedCharacter_eq_inv_card_subgroup_mul_sum
    [Finite G] (u : G) :
    (Representation.ind H.subtype θ).character u =
      (Nat.card H : ℂ)⁻¹ *
        ∑ s : G,
          if hsu : s⁻¹ * u * s ∈ H then
            θ.character ⟨s⁻¹ * u * s, hsu⟩
          else
            0 := by
  classical
  obtain ⟨S, hS, h1S⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := hS.finite_left.toFinset
  have hR : IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  have hsum :
      ∑ s : G,
        (if hsu : s⁻¹ * u * s ∈ H then
          θ.character ⟨s⁻¹ * u * s, hsu⟩
        else 0) =
      (Nat.card H : ℂ) *
        ∑ r ∈ R,
          (if hur : r⁻¹ * u * r ∈ H then
            θ.character ⟨r⁻¹ * u * r, hur⟩
          else 0) := by
    -- Reindex the full group sum by the chosen left transversal.
    simpa [R] using
      sumOverGroup_eq_cardSubgroup_mul_sumOverRepresentatives H θ R hR u
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  calc
    (Representation.ind H.subtype θ).character u
        = ∑ r ∈ R,
            if hur : r⁻¹ * u * r ∈ H then
              θ.character ⟨r⁻¹ * u * r, hur⟩
            else 0 := by
              simpa [R] using
                inducedCharacter_eq_sum_over_representatives H θ R hR u
    _ = (Nat.card H : ℂ)⁻¹ *
          ((Nat.card H : ℂ) *
            ∑ r ∈ R,
              if hur : r⁻¹ * u * r ∈ H then
                θ.character ⟨r⁻¹ * u * r, hur⟩
              else 0) := by
                field_simp [hcard]
    _ = (Nat.card H : ℂ)⁻¹ *
          ∑ s : G,
            if hsu : s⁻¹ * u * s ∈ H then
              θ.character ⟨s⁻¹ * u * s, hsu⟩
            else 0 := by
              rw [hsum]

section HaarIntegralFormula

variable [MeasurableSpace G] [BorelSpace G]

local notation "μG" => (normalizedHaarMeasure : MeasureTheory.Measure G)

/-- Helper for Theorem 4-45: once a finite-index subgroup is known to be closed, the canonical
mathlib finite-index API upgrades it to an open subgroup. -/
lemma subgroupIsOpenOfFiniteIndexCompact_of_isClosed
    (hClosed : IsClosed (H : Set G)) :
    IsOpen (H : Set G) := by
  -- This packages the standard closed-subgroup step so the remaining blocker is purely topological.
  exact H.isOpen_of_isClosed_of_finiteIndex hClosed

/-- Helper for Theorem 4-45: an open subgroup is Borel measurable. -/
lemma subgroupMeasurableSetOfIsOpen
    (hOpen : IsOpen (H : Set G)) :
    MeasurableSet (H : Set G) := by
  -- The Haar-measure arguments below only need the subgroup as a measurable set.
  exact hOpen.measurableSet

/-- Helper for Theorem 4-45: in the compact Hausdorff setting, a finite-index subgroup should be
measurable, so the representative selector has measurable fibers. -/
lemma subgroupMeasurableSetOfFiniteIndexCompact :
    MeasurableSet (H : Set G) := by
  -- Route correction: the measure-theoretic part is already reduced to a single structural input.
  have hOpen : IsOpen (H : Set G) := by
    -- TODO: prove the missing compact-group fact that a finite-index subgroup is closed/open;
    -- once that topological lemma is supplied, the Haar branch below compiles as written.
    sorry
  exact subgroupMeasurableSetOfIsOpen (H := H) hOpen

/-- Helper for Theorem 4-45: the representative chosen by a left transversal has fiber equal to
the corresponding left coset of `H`. -/
lemma representativeEquivPreimage_singleton
    (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G))
    (r : ↥(R : Set G)) :
    (fun g : G ↦ (hR.equiv g).fst) ⁻¹' ({r} : Set ↥(R : Set G)) =
      Set.range (fun h : H ↦ (r : G) * h) := by
  -- Membership in the singleton fiber is exactly the condition of lying in the left coset of `r`.
  ext x
  constructor
  · intro hx
    refine ⟨(hR.equiv x).snd, ?_⟩
    have hfst : (hR.equiv x).fst = r := by
      simpa using hx
    calc
      (r : G) * ((hR.equiv x).snd : H)
          = ((hR.equiv x).fst : G) * ((hR.equiv x).snd : H) := by rw [hfst]
      _ = x := by
            simpa using hR.equiv_fst_mul_equiv_snd x
  · rintro ⟨h, rfl⟩
    have hcoset : LeftCosetEquivalence H ((r : G) * h : G) (r : G) := by
      rw [LeftCosetEquivalence, leftCoset_eq_iff]
      simpa [mul_assoc] using H.inv_mem h.2
    have hfst_eq : (hR.equiv ((r : G) * h : G)).fst = (hR.equiv (r : G)).fst := by
      exact
        (hR.equiv_fst_eq_iff_leftCosetEquivalence (g₁ := ((r : G) * h : G))
          (g₂ := (r : G))).2 hcoset
    have hr_self : (hR.equiv (r : G)).fst = r := by
      simpa using hR.equiv_fst_eq_self_of_mem_of_one_mem (by simp) r.2
    simpa [hr_self] using hfst_eq

/-- Helper for Theorem 4-45: pushing normalized Haar measure to a finite left transversal gives
the subgroup mass times counting measure. -/
lemma representativeMapMeasure_eq_subgroupMeasure_smul_count
    (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G)) :
    MeasureTheory.Measure.map (fun g : G ↦ (hR.equiv g).fst) μG =
      μG (H : Set G) • (MeasureTheory.Measure.count : MeasureTheory.Measure ↥(R : Set G)) := by
  classical
  let representative : G → ↥(R : Set G) := fun g ↦ (hR.equiv g).fst
  have hH_meas : MeasurableSet (H : Set G) := subgroupMeasurableSetOfFiniteIndexCompact (H := H)
  have hfiber_meas (r : ↥(R : Set G)) :
      MeasurableSet (representative ⁻¹' ({r} : Set ↥(R : Set G))) := by
    -- The singleton fibers are left translates of `H`, so they inherit measurability from `H`.
    rw [representativeEquivPreimage_singleton (H := H) (R := R) hR r]
    have hrange :
        Set.range (fun h : H ↦ (r : G) * h) = ((fun x : G ↦ (r : G)⁻¹ * x) ⁻¹' (H : Set G)) := by
      ext x
      constructor
      · rintro ⟨h, rfl⟩
        simp [mul_assoc]
      · intro hx
        refine ⟨⟨(r : G)⁻¹ * x, hx⟩, ?_⟩
        simp [mul_assoc]
    rw [hrange]
    exact hH_meas.preimage (measurable_const_mul _)
  have hrepresentative_meas : Measurable representative :=
    measurable_to_countable' hfiber_meas
  -- A measure on a finite representative set is determined by the masses of singletons.
  apply MeasureTheory.Measure.ext_of_singleton
  intro r
  rw [MeasureTheory.Measure.map_apply hrepresentative_meas (measurableSet_singleton r)]
  rw [representativeEquivPreimage_singleton (H := H) (R := R) hR r]
  have hrange :
      Set.range (fun h : H ↦ (r : G) * h) = ((fun x : G ↦ (r : G)⁻¹ * x) ⁻¹' (H : Set G)) := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      simp [mul_assoc]
    · intro hx
      refine ⟨⟨(r : G)⁻¹ * x, hx⟩, ?_⟩
      simp [mul_assoc]
  rw [hrange, MeasureTheory.measure_preimage_mul (μ := μG) (g := (r : G)⁻¹) (A := (H : Set G))]
  simp [MeasureTheory.Measure.smul_apply]

/-- For a finite-index subgroup of a compact group, the normalized Haar measure of the subgroup is
the reciprocal of its index. This is the measure factor appearing in the Haar form of Theorem
4-45. -/
theorem normalizedHaarMeasure_subgroup_eq_inv_index
    : μG (H : Set G) = (H.index : ENNReal)⁻¹ := by
  have hH_meas : MeasurableSet (H : Set G) := subgroupMeasurableSetOfFiniteIndexCompact (H := H)
  have hmul :
      (μG (H : Set G)) * (H.index : ENNReal) = 1 := by
    -- The normalized Haar measure of `G` is `1`, so the subgroup measure is forced by index.
    simpa [mul_comm] using
      (MeasureTheory.Subgroup.index_mul_measure (H := H) hH_meas μG).trans
        (normalizedHaarMeasure_univ (G := G))
  exact ENNReal.eq_inv_of_mul_eq_one_left hmul

/-- Helper for Theorem 4-45: the Haar integral of the conjugacy summand is the subgroup-measure
weighted average of the representative sum. -/
lemma integral_characterSummand_eq_subgroupMeasure_mul_sum_over_representatives
    (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G)) (u : G) :
    ∫ s,
      (if hsu : s⁻¹ * u * s ∈ H then
        θ.character ⟨s⁻¹ * u * s, hsu⟩
      else
        0) ∂μG =
      ((μG (H : Set G)).toReal : ℂ) *
        ∑ r ∈ R,
          if hur : r⁻¹ * u * r ∈ H then
            θ.character ⟨r⁻¹ * u * r, hur⟩
          else
            0 := by
  classical
  let representative : G → ↥(R : Set G) := fun g ↦ (hR.equiv g).fst
  let summandOnRepresentatives : ↥(R : Set G) → ℂ := fun r ↦
    if hur : (r : G)⁻¹ * u * r ∈ H then
      θ.character ⟨(r : G)⁻¹ * u * r, hur⟩
    else
      0
  have hfiber_meas (r : ↥(R : Set G)) :
      MeasurableSet (representative ⁻¹' ({r} : Set ↥(R : Set G))) := by
    -- The same singleton-fiber calculation makes the selector measurable.
    rw [representativeEquivPreimage_singleton (H := H) (R := R) hR r]
    have hrange :
        Set.range (fun h : H ↦ (r : G) * h) = ((fun x : G ↦ (r : G)⁻¹ * x) ⁻¹' (H : Set G)) := by
      ext x
      constructor
      · rintro ⟨h, rfl⟩
        simp [mul_assoc]
      · intro hx
        refine ⟨⟨(r : G)⁻¹ * x, hx⟩, ?_⟩
        simp [mul_assoc]
    rw [hrange]
    exact
      (subgroupMeasurableSetOfFiniteIndexCompact (H := H)).preimage (measurable_const_mul _)
  have hrepresentative_meas : Measurable representative :=
    measurable_to_countable' hfiber_meas
  have hsummand_comp :
      (fun s : G ↦
        if hsu : s⁻¹ * u * s ∈ H then
          θ.character ⟨s⁻¹ * u * s, hsu⟩
        else
          0) =
      fun s : G ↦ summandOnRepresentatives (representative s) := by
    -- Decompose `s` into its chosen representative and subgroup factor, then drop the factor.
    funext s
    have hs_eq : s = ((hR.equiv s).fst : G) * ((hR.equiv s).snd : H) := by
      simpa using (hR.equiv_fst_mul_equiv_snd s).symm
    have hmain :
        (if hsu :
            (((hR.equiv s).fst : G) * ((hR.equiv s).snd : H))⁻¹ * u *
              (((hR.equiv s).fst : G) * ((hR.equiv s).snd : H)) ∈ H then
          θ.character
            ⟨(((hR.equiv s).fst : G) * ((hR.equiv s).snd : H))⁻¹ * u *
              (((hR.equiv s).fst : G) * ((hR.equiv s).snd : H)), hsu⟩
        else
          0) =
        summandOnRepresentatives ((hR.equiv s).fst) := by
      simpa [summandOnRepresentatives] using
        leftCosetCharacterSummand_right_mul_eq
          (H := H) (θ := θ) u ((hR.equiv s).fst : G) ((hR.equiv s).snd)
    have hrepresentative_decomp :
        representative (((hR.equiv s).fst : G) * ((hR.equiv s).snd : H)) = (hR.equiv s).fst := by
      -- The selector fixes an already chosen representative after multiplying on the right by `H`.
      dsimp [representative]
      have hfst :
          (hR.equiv (((hR.equiv s).fst : G) * ((hR.equiv s).snd : H))).fst =
            (hR.equiv ((hR.equiv s).fst : G)).fst := by
        simpa using congrArg Prod.fst
          (hR.equiv_mul_right ((hR.equiv s).fst : G) ((hR.equiv s).snd))
      exact hfst.trans <|
        hR.equiv_fst_eq_self_of_mem_of_one_mem (by simp) ((hR.equiv s).fst).2
    rw [hs_eq, hrepresentative_decomp]
    exact hmain
  have hsummand_meas : Measurable summandOnRepresentatives :=
    measurable_of_finite summandOnRepresentatives
  -- Push the integrand to the finite representative set, then evaluate the counting integral.
  calc
    ∫ s,
        (if hsu : s⁻¹ * u * s ∈ H then
          θ.character ⟨s⁻¹ * u * s, hsu⟩
        else
          0) ∂μG
        = ∫ s, summandOnRepresentatives (representative s) ∂μG := by
            rw [hsummand_comp]
    _ = ∫ r, summandOnRepresentatives r ∂MeasureTheory.Measure.map representative μG := by
          rw [← MeasureTheory.integral_map hrepresentative_meas.aemeasurable
            hsummand_meas.aestronglyMeasurable]
    _ = ∫ r, summandOnRepresentatives r ∂(μG (H : Set G) • MeasureTheory.Measure.count) := by
          simpa [representative] using
            congrArg
              (fun ν : MeasureTheory.Measure ↥(R : Set G) ↦
                ∫ r, summandOnRepresentatives r ∂ν)
              (representativeMapMeasure_eq_subgroupMeasure_smul_count
                (H := H) (R := R) hR)
    _ = ((μG (H : Set G)).toReal : ℂ) *
          ∫ r, summandOnRepresentatives r ∂(MeasureTheory.Measure.count) := by
            rw [MeasureTheory.integral_smul_measure]
            change
              (((μG (H : Set G)).toReal : ℂ) *
                ∫ r, summandOnRepresentatives r ∂(MeasureTheory.Measure.count)) =
              (((μG (H : Set G)).toReal : ℂ) *
                ∫ r, summandOnRepresentatives r ∂(MeasureTheory.Measure.count))
            rfl
    _ = ((μG (H : Set G)).toReal : ℂ) *
          ∑ r : ↥(R : Set G), summandOnRepresentatives r := by
            simp [MeasureTheory.integral_count]
    _ = ((μG (H : Set G)).toReal : ℂ) *
          ∑ r ∈ R,
            (if hur : r⁻¹ * u * r ∈ H then
              θ.character ⟨r⁻¹ * u * r, hur⟩
            else
              0) := by
            rw [← Finset.sum_attach R
              (fun r : G ↦
                if hur : r⁻¹ * u * r ∈ H then
                  θ.character ⟨r⁻¹ * u * r, hur⟩
                else
                  0)]
            rfl

/-- Companion compact-group Haar-integral form of Theorem 4-45: in the compact finite-index
setting, the induced character is the index-weighted Haar integral of the subgroup character along
the conjugacy locus. Together with `normalizedHaarMeasure_subgroup_eq_inv_index`, this is Serre's
`μ_G(H)⁻¹` formula. -/
theorem inducedCharacter_eq_index_mul_integral
    (u : G) :
    (Representation.ind H.subtype θ).character u =
      (H.index : ℂ) *
        ∫ s,
          (if hsu : s⁻¹ * u * s ∈ H then
            θ.character ⟨s⁻¹ * u * s, hsu⟩
          else
            0) ∂μG := by
  classical
  obtain ⟨S, hS, _h1S⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := hS.finite_left.toFinset
  have hR : IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  have hindex_ne_zero : (H.index : ENNReal) ≠ 0 := by
    exact_mod_cast H.index_ne_zero_of_finite
  have hindex_ne_zeroC : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast H.index_ne_zero_of_finite
  have hmeasure_toReal :
      ((μG (H : Set G)).toReal : ℂ) = (((H.index : ENNReal)⁻¹).toReal : ℂ) := by
    rw [normalizedHaarMeasure_subgroup_eq_inv_index (H := H)]
  have hmeasure_inv :
      ((((H.index : ENNReal)⁻¹).toReal : ℂ)) = (H.index : ℂ)⁻¹ := by
    simp [ENNReal.toReal_inv]
  -- The representative sum theorem and the subgroup-measure identity finish the Haar formula.
  calc
    (Representation.ind H.subtype θ).character u
        =
          ∑ r ∈ R,
            if hur : r⁻¹ * u * r ∈ H then
              θ.character ⟨r⁻¹ * u * r, hur⟩
            else
              0 := by
            simpa [R] using inducedCharacter_eq_sum_over_representatives H θ R hR u
    _ =
        (H.index : ℂ) *
          (((μG (H : Set G)).toReal : ℂ) *
            ∑ r ∈ R,
              if hur : r⁻¹ * u * r ∈ H then
                θ.character ⟨r⁻¹ * u * r, hur⟩
              else
                0) := by
      calc
        ∑ r ∈ R,
            (if hur : r⁻¹ * u * r ∈ H then
              θ.character ⟨r⁻¹ * u * r, hur⟩
            else
              0) =
            1 *
              ∑ r ∈ R,
                (if hur : r⁻¹ * u * r ∈ H then
                  θ.character ⟨r⁻¹ * u * r, hur⟩
                else
                  0) := by simp
        _ = ((H.index : ℂ) * (H.index : ℂ)⁻¹) *
              ∑ r ∈ R,
                (if hur : r⁻¹ * u * r ∈ H then
                  θ.character ⟨r⁻¹ * u * r, hur⟩
                else
                  0) := by
              simp [hindex_ne_zeroC]
        _ = (H.index : ℂ) *
              ((H.index : ℂ)⁻¹ *
                ∑ r ∈ R,
                  (if hur : r⁻¹ * u * r ∈ H then
                    θ.character ⟨r⁻¹ * u * r, hur⟩
                  else
                    0)) := by
              rw [mul_assoc]
        _ = (H.index : ℂ) *
              ((((H.index : ENNReal)⁻¹).toReal : ℂ) *
                ∑ r ∈ R,
                  (if hur : r⁻¹ * u * r ∈ H then
                    θ.character ⟨r⁻¹ * u * r, hur⟩
                  else
                    0)) := by
              rw [hmeasure_inv]
        _ = (H.index : ℂ) *
              (((μG (H : Set G)).toReal : ℂ) *
                ∑ r ∈ R,
                  (if hur : r⁻¹ * u * r ∈ H then
                    θ.character ⟨r⁻¹ * u * r, hur⟩
                  else
                    0)) := by
              rw [hmeasure_toReal]
    _ = (H.index : ℂ) *
          ∫ s,
            (if hsu : s⁻¹ * u * s ∈ H then
              θ.character ⟨s⁻¹ * u * s, hsu⟩
            else
              0) ∂μG := by
          rw [integral_characterSummand_eq_subgroupMeasure_mul_sum_over_representatives
            (H := H) (θ := θ) (R := R) hR u]
    _ = (H.index : ℂ) *
          ∫ s,
            (if hsu : s⁻¹ * u * s ∈ H then
              θ.character ⟨s⁻¹ * u * s, hsu⟩
            else
              0) ∂μG := by
            rfl

end HaarIntegralFormula

end CompactInducedCharacters

end Representation
