import stacks_proof.stacks_project.Chap15.Definition_15_124_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfValuationRings

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [ValuationRing A]
variable [CommRing B] [IsDomain B] [ValuationRing B]
variable [Algebra A B] [h : IsExtensionOfValuationRings A B]

local notation "K[" A "]" => FractionRing A
local notation "Γ[" B "]" => ValuativeRel.ValueGroupWithZero K[B]
local notation "Q" =>
  Γ[B]ˣ ⧸ MonoidWithZeroHom.valueGroup (ValuativeExtension.mapValueGroupWithZero K[A] K[B])

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Helper for Lemma 15.124.2: in a finite family of elements of a valuation ring, one element
divides all the others. -/
lemma exists_mem_finset_dvd_all {ι : Type*} (s : Finset ι) (f : ι → A)
    (hs : s.Nonempty) :
    ∃ j ∈ s, ∀ i ∈ s, f j ∣ f i := by
  classical
  refine Finset.induction_on s ?_ ?_ hs
  · intro hs0
    simpa using hs0
  · intro a s ha hsind hsas
    by_cases hs' : s.Nonempty
    · rcases hsind hs' with ⟨j, hj, hdiv⟩
      have htotal : Std.Total (fun I J : Ideal A ↦ I ≤ J) :=
        ValuationRing.iff_ideal_total.mp inferInstance
      rcases htotal.total (Ideal.span ({f a} : Set A)) (Ideal.span ({f j} : Set A)) with
          hle | hle
      · refine ⟨j, Finset.mem_insert_of_mem hj, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact (Ideal.span_singleton_le_span_singleton.mp hle)
        · exact hdiv i hi'
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact dvd_rfl
        · exact dvd_trans (Ideal.span_singleton_le_span_singleton.mp hle) (hdiv i hi')
    · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst hs_empty
      refine ⟨a, by simp, ?_⟩
      intro i hi
      have hi' : i = a := by simpa using hi
      subst hi'
      exact dvd_rfl

/-- Helper for Lemma 15.124.2: residue-field linear independence of lifts already implies
`A`-linear independence in `B`. -/
lemma residue_lifts_linearIndependent_over_base
    {ι : Type*} (u : ι → B)
    (hu : LinearIndependent (ResidueField A) (fun i ↦ IsLocalRing.residue B (u i))) :
    LinearIndependent A u := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  by_cases hl0 : l = 0
  · exact hl0
  have hs : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hl0
  rcases exists_mem_finset_dvd_all (A := A) l.support (fun i ↦ l i) hs with ⟨j, hj, hdiv⟩
  have hj0 : l j ≠ 0 := (Finsupp.mem_support_iff.mp hj)
  have hcoeff :
      ∀ i, i ∈ l.support → ∃ a : A, l i = a * l j := by
    intro i hi
    rcases hdiv i hi with ⟨a, ha⟩
    exact ⟨a, by simpa [mul_comm] using ha⟩
  let mFun : ι → A := fun i ↦
    if hli : l i = 0 then 0 else
      Classical.choose (hcoeff i (Finsupp.mem_support_iff.mpr hli))
  have hmFun_support : ∀ i, mFun i ≠ 0 → i ∈ l.support := by
    intro i hi
    by_cases hli : l i = 0
    · simp [mFun, hli] at hi
    · exact Finsupp.mem_support_iff.mpr hli
  let m : ι →₀ A := Finsupp.onFinset l.support mFun hmFun_support
  have hm_eq :
      ∀ i, i ∈ l.support → l i = m i * l j := by
    intro i hi
    have hli : l i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hchoice := Classical.choose_spec (hcoeff i hi)
    simpa [m, mFun, hli] using hchoice
  have hl_eq_smul : l = l j • m := by
    apply Finsupp.ext
    intro i
    by_cases hi : i ∈ l.support
    · rw [Finsupp.smul_apply]
      calc
        l i = m i * l j := hm_eq i hi
        _ = l j * m i := by simp [mul_comm]
        _ = (l j • m) i := by simp [smul_eq_mul]
    · have hli : l i = 0 := by
        by_contra hli
        exact hi (Finsupp.mem_support_iff.mpr hli)
      have hmi : m i = 0 := by
        rw [Finsupp.onFinset_apply]
        simp [mFun, hli]
      simp [Finsupp.smul_apply, hli, hmi]
  have hm_relation : Finsupp.linearCombination A u m = 0 := by
    -- Factor out the coefficient of smallest valuation from the original relation.
    have hsmul :
        (Finsupp.linearCombination A u) (l j • m) =
          l j • (Finsupp.linearCombination A u m) := by
      simpa using (Finsupp.linearCombination A u).map_smul (l j) m
    have hscaled' : (Finsupp.linearCombination A u) (l j • m) = 0 := by
      exact hl_eq_smul ▸ hl
    have hscaled : l j • Finsupp.linearCombination A u m = 0 := by
      calc
        l j • Finsupp.linearCombination A u m
            = (Finsupp.linearCombination A u) (l j • m) := by simpa using hsmul.symm
        _ = 0 := hscaled'
    have hmul :
        algebraMap A B (l j) * Finsupp.linearCombination A u m = 0 := by
      simpa [smul_eq_mul] using hscaled
    have hmapj : algebraMap A B (l j) ≠ 0 := by
      intro hzero
      exact hj0 (h.algebraMap_injective (by simpa using hzero))
    exact (mul_eq_zero.mp hmul).resolve_left hmapj
  let mκ : ι →₀ ResidueField A :=
    m.mapRange (IsLocalRing.residue A) (by simp)
  have hmκ_relation :
      Finsupp.linearCombination (ResidueField A)
        (fun i ↦ IsLocalRing.residue B (u i)) mκ = 0 := by
    -- Reducing the normalized relation modulo the maximal ideal transfers it to the residue field.
    let ρ : B →+* ResidueField B := IsLocalRing.residue B
    have hm_relation_sum : m.sum (fun i c ↦ c • u i) = 0 := by
      simpa [Finsupp.linearCombination] using hm_relation
    have hresEq : ρ (m.sum fun i c ↦ c • u i) = ρ (0 : B) := by
      exact congrArg ρ hm_relation_sum
    have hmapSum :
        ρ (m.sum fun i c ↦ c • u i) = Finset.sum m.support (fun i ↦ ρ (m i • u i)) := by
      simpa [Finsupp.sum] using (map_sum ρ (fun i ↦ m i • u i) m.support)
    have hres1 :
        m.sum (fun i c ↦ IsLocalRing.residue A c • ρ (u i)) = 0 := by
      calc
        m.sum (fun i c ↦ IsLocalRing.residue A c • ρ (u i))
            = Finset.sum m.support (fun i ↦ ρ (m i • u i)) := by
                change
                  Finset.sum m.support (fun i ↦ IsLocalRing.residue A (m i) • ρ (u i)) =
                    Finset.sum m.support (fun i ↦ ρ (m i • u i))
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [Algebra.smul_def]
                rw [show
                  algebraMap (ResidueField A) (ResidueField B) =
                    IsLocalRing.ResidueField.map (algebraMap A B) by rfl]
                calc
                  (IsLocalRing.ResidueField.map (algebraMap A B) (IsLocalRing.residue A (m i))) *
                      ρ (u i)
                      = ρ (algebraMap A B (m i)) * ρ (u i) := by
                          rw [IsLocalRing.ResidueField.map_residue (algebraMap A B)]
                  _ = ρ ((algebraMap A B (m i)) * u i) := by rw [← map_mul]
                  _ = ρ (m i • u i) := by simp [ρ, Algebra.smul_def]
        _ = ρ (m.sum fun i c ↦ c • u i) := by simpa using hmapSum.symm
        _ = ρ (0 : B) := hresEq
        _ = 0 := by simp [ρ]
    have hmκ_sum :
        mκ.sum (fun i c ↦ c • ρ (u i)) =
          m.sum (fun i c ↦ IsLocalRing.residue A c • ρ (u i)) := by
      simpa [mκ] using
        (Finsupp.sum_mapRange_index
          (f := IsLocalRing.residue A) (hf := by simp) (g := m)
          (h := fun i c ↦ c • ρ (u i))
          (fun i ↦ by simp))
    simpa [Finsupp.linearCombination] using hmκ_sum.trans hres1
  have hmκ_zero : mκ = 0 := by
    exact (linearIndependent_iff.mp hu) mκ hmκ_relation
  have hmj : m j = 1 := by
    have hmjj : l j = m j * l j := hm_eq j hj
    exact (mul_eq_right₀ hj0).mp hmjj.symm
  have hmκj : mκ j = 1 := by
    simpa [mκ, hmj] using congrArg (IsLocalRing.residue A) hmj
  have : mκ j = 0 := by simpa [hmκ_zero]
  exact False.elim (zero_ne_one (this.symm.trans hmκj))

/-- Helper for Lemma 15.124.2: residue-field linear independence of lifts in `B` should imply
linear independence of their images in `K[B]` over `K[A]`. -/
lemma residue_lifts_linearIndependent
    {ι : Type*} (u : ι → B)
    (hu : LinearIndependent (ResidueField A) (fun i ↦ IsLocalRing.residue B (u i))) :
    LinearIndependent K[A] (fun i ↦ algebraMap B K[B] (u i)) := by
  -- First prove linear independence over the valuation ring itself.
  have hbase : LinearIndependent A u :=
    residue_lifts_linearIndependent_over_base (A := A) (B := B) u hu
  have hmap : LinearIndependent A (fun i ↦ algebraMap B K[B] (u i)) := by
    refine hbase.map' (IsScalarTower.toAlgHom A B K[B]).toLinearMap ?_
    exact LinearMap.ker_eq_bot.mpr (IsFractionRing.injective B K[B])
  -- Then pass from `A` to its fraction field by the canonical scalar-extension equivalence.
  exact (LinearIndependent.iff_fractionRing A K[A]).mp hmap

/-- Helper for Lemma 15.124.2: multiplying by the image of a source-field unit does not change the
target value-group quotient class. -/
lemma value_group_quotient_class_mul_source_unit
    (a : K[A]ˣ) (c : K[B]ˣ) :
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        ((Units.map (algebraMap K[A] K[B]).toMonoidHom a) * c))) : Q) =
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c)) : Q) := by
  rw [QuotientGroup.eq]
  -- The quotient difference is the valuation of a mapped source unit, hence lies in the subgroup.
  apply Subgroup.subset_closure
  refine ⟨Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[A])).toMonoidHom a⁻¹, ?_⟩
  simp [ValuativeExtension.mapValueGroupWithZero, map_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 15.124.2: if a normalized product has trivial quotient class, then the two
target unit classes coincide in `Q`. -/
lemma value_group_quotient_class_eq_of_mul_source_unit_eq_one
    (a : K[A]ˣ) (c₁ c₂ : K[B]ˣ)
    (htriv :
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (((Units.map (algebraMap K[A] K[B]).toMonoidHom a) * c₁) * c₂⁻¹))) : Q) =
      ((Quotient.mk''
        (1 : Γ[B]ˣ)) : Q)) :
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c₁)) : Q) =
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c₂)) : Q) := by
  have hcancel :
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (c₁ * c₂⁻¹))) : Q) =
      ((Quotient.mk''
        (1 : Γ[B]ˣ)) : Q) := by
    have hmul :
        ((Quotient.mk''
          (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
            (((Units.map (algebraMap K[A] K[B]).toMonoidHom a) * c₁) * c₂⁻¹))) : Q) =
        ((Quotient.mk''
          (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
            (c₁ * c₂⁻¹))) : Q) := by
      simpa [mul_assoc] using
        value_group_quotient_class_mul_source_unit (A := A) (B := B) a (c₁ * c₂⁻¹)
    exact hmul.symm.trans htriv
  rw [QuotientGroup.eq]
  rw [QuotientGroup.eq] at hcancel
  -- Rewriting the trivial-class statement identifies the quotient difference `c₁⁻¹ * c₂`.
  simpa [map_mul, mul_comm, mul_left_comm, mul_assoc] using hcancel

/-- Helper for Lemma 15.124.2: a `B`-element with nonzero residue is a unit of `B`. -/
lemma isUnit_of_residue_ne_zero (d : B)
    (hd : IsLocalRing.residue B d ≠ 0) :
    IsUnit d := by
  -- A nonunit lies in the maximal ideal, so its residue class must vanish.
  by_contra hunit
  have hd_nonunit : d ∈ nonunits B := hunit
  have hd_max : d ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal d).2 hd_nonunit
  exact hd ((Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal B) (a := d)).2 hd_max)

/-- Helper for Lemma 15.124.2: the valuation of a unit coming from the valuation ring itself is
trivial in the target value group. -/
lemma target_ring_unit_value_eq_one (b : Bˣ) :
    (ValuativeRel.valuation K[B]) (algebraMap B K[B] (b : B)) = 1 := by
  let v := ValuationRing.valuation B K[B]
  let e := ValuativeRel.ValueGroupWithZero.orderMonoidIso v
  have hcompat : v.Compatible := Valuation.Compatible.ofValuation v
  have hbase : v (algebraMap B K[B] (b : B)) = 1 := by
    have hb_le_one : v (algebraMap B K[B] (b : B)) ≤ 1 := by
      rw [← Valuation.mem_integer_iff]
      exact (ValuationRing.mem_integer_iff B K[B] _).2 ⟨(b : B), rfl⟩
    have hbinv_le_one : v (algebraMap B K[B] ((↑b⁻¹ : Bˣ) : B)) ≤ 1 := by
      rw [← Valuation.mem_integer_iff]
      exact (ValuationRing.mem_integer_iff B K[B] _).2 ⟨(((↑b⁻¹ : Bˣ) : B)), rfl⟩
    have hmul : v (algebraMap B K[B] (b : B)) * v (algebraMap B K[B] ((↑b⁻¹ : Bˣ) : B)) = 1 := by
      calc
        v (algebraMap B K[B] (b : B)) * v (algebraMap B K[B] ((↑b⁻¹ : Bˣ) : B))
            = v ((algebraMap B K[B] (b : B)) * (algebraMap B K[B] ((↑b⁻¹ : Bˣ) : B))) := by
                rw [← map_mul]
        _ = v 1 := by simp
        _ = 1 := map_one _
    have h_one_le : 1 ≤ v (algebraMap B K[B] (b : B)) := by
      calc
        1 = v (algebraMap B K[B] (b : B)) * v (algebraMap B K[B] ((↑b⁻¹ : Bˣ) : B)) := hmul.symm
        _ ≤ v (algebraMap B K[B] (b : B)) * 1 := by gcongr
        _ = v (algebraMap B K[B] (b : B)) := by simp
    exact le_antisymm hb_le_one h_one_le
  -- Compare the canonical valuative-rel valuation with the valuation-ring valuation.
  have horder :
      e ((ValuativeRel.valuation K[B]) (algebraMap B K[B] (b : B))) = e 1 := by
    simp [e, v, hbase, ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]
  exact e.injective horder

/-- Helper for Lemma 15.124.2: multiplying by the image of a unit from `B` does not change the
target value-group quotient class. -/
lemma value_group_quotient_class_mul_target_ring_unit
    (b : Bˣ) (c : K[B]ˣ) :
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        ((Units.map (algebraMap B K[B]).toMonoidHom b) * c))) : Q) =
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c)) :
      Q) := by
  -- The extra factor contributes valuation `1`, so the quotient class is unchanged.
  calc
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        ((Units.map (algebraMap B K[B]).toMonoidHom b) * c))) : Q)
        =
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (Units.map (algebraMap B K[B]).toMonoidHom b) *
          Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c)) :
        Q) := by
          rw [map_mul]
    _ =
      ((Quotient.mk''
        ((1 : Γ[B]ˣ) *
          Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c)) :
        Q) := by
          rw [show
            Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
              (Units.map (algebraMap B K[B]).toMonoidHom b) = 1 by
                ext
                exact target_ring_unit_value_eq_one b]
    _ =
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c)) :
        Q) := by simp

/-- Helper for Lemma 15.124.2: after canceling both a source-field unit and a target-ring unit, a
trivial normalized quotient class forces the two target unit classes to agree. -/
lemma value_group_quotient_class_eq_of_mul_source_and_target_unit_eq_one
    (a : K[A]ˣ) (b : Bˣ) (c₁ c₂ : K[B]ˣ)
    (htriv :
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          ((((Units.map (algebraMap K[A] K[B]).toMonoidHom a) *
              (Units.map (algebraMap B K[B]).toMonoidHom b)) * c₁) * c₂⁻¹))) : Q) =
      ((Quotient.mk''
        (1 : Γ[B]ˣ)) : Q)) :
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c₁)) :
      Q) =
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c₂)) :
      Q) := by
  have hstrip :
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (((Units.map (algebraMap K[A] K[B]).toMonoidHom a) * c₁) * c₂⁻¹))) : Q) =
      ((Quotient.mk''
        (1 : Γ[B]ˣ)) : Q) := by
    calc
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (((Units.map (algebraMap K[A] K[B]).toMonoidHom a) * c₁) * c₂⁻¹))) : Q)
          =
        ((Quotient.mk''
          (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
            ((Units.map (algebraMap B K[B]).toMonoidHom b) *
              (((Units.map (algebraMap K[A] K[B]).toMonoidHom a) * c₁) * c₂⁻¹)))) : Q) := by
            symm
            simpa [mul_assoc] using
              value_group_quotient_class_mul_target_ring_unit (A := A) (B := B) b
                (((Units.map (algebraMap K[A] K[B]).toMonoidHom a) * c₁) * c₂⁻¹)
      _ =
        ((Quotient.mk''
          (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
            ((((Units.map (algebraMap K[A] K[B]).toMonoidHom a) *
                (Units.map (algebraMap B K[B]).toMonoidHom b)) * c₁) * c₂⁻¹))) : Q) := by
              congr 1
              simp [mul_assoc, mul_left_comm, mul_comm]
      _ =
        ((Quotient.mk''
          (1 : Γ[B]ˣ)) : Q) := htriv
  -- Once the target-ring unit is canceled, the earlier source-unit lemma applies verbatim.
  exact value_group_quotient_class_eq_of_mul_source_unit_eq_one (A := A) (B := B) a c₁ c₂ hstrip

/-- Helper for Lemma 15.124.2: in the normalized relation, a nonzero residue coefficient forces
its `σ`-index to match the leading `σ`-index. -/
lemma normalized_trivial_class_forces_same_sigma
    {σ : Type*} (c : σ → K[B]ˣ)
    (hc : Function.Injective fun s ↦
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (c s))) : Q))
    {s s0 : σ} {a : K[A]ˣ} {b : Bˣ}
    (htriv :
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          ((((Units.map (algebraMap K[A] K[B]).toMonoidHom a) *
              (Units.map (algebraMap B K[B]).toMonoidHom b)) * c s) * (c s0)⁻¹))) : Q) =
      ((Quotient.mk''
        (1 : Γ[B]ˣ)) : Q)) :
    s = s0 := by
  -- Cancel the normalized source and target units, then use injectivity of the chosen classes.
  apply hc
  exact value_group_quotient_class_eq_of_mul_source_and_target_unit_eq_one
    (A := A) (B := B) a b (c s) (c s0) htriv

/-- Helper for Lemma 15.124.2: if every nonzero residue coefficient in a nonleading slice would
force the slice to be leading, then the nonleading residue must vanish. -/
lemma normalized_nonleading_slice_residue_eq_zero
    {σ : Type*} (c : σ → K[B]ˣ)
    (hc : Function.Injective fun s ↦
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (c s))) : Q))
    {s s0 : σ} {a : K[A]ˣ} {d : B}
    (hs : s ≠ s0)
    (htriv :
      ∀ hd : IsLocalRing.residue B d ≠ 0,
        ((Quotient.mk''
          (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
            ((((Units.map (algebraMap K[A] K[B]).toMonoidHom a) *
                (Units.map (algebraMap B K[B]).toMonoidHom
                  (isUnit_of_residue_ne_zero (B := B) d hd).unit)) * c s) * (c s0)⁻¹))) : Q) =
        ((Quotient.mk''
          (1 : Γ[B]ˣ)) : Q)) :
    IsLocalRing.residue B d = 0 := by
  -- Contraposition turns the residue-vanishing claim into the previous uniqueness-of-slice lemma.
  by_contra hd
  exact hs
    (normalized_trivial_class_forces_same_sigma (A := A) (B := B) c hc
      (a := a) (b := (isUnit_of_residue_ne_zero (B := B) d hd).unit) (s := s) (s0 := s0)
      (htriv hd))

/-- Helper for Lemma 15.124.2: once a normalized support term is rewritten as a source unit times
the leading term, the resulting quotient class is trivial. -/
lemma normalized_support_term_trivial_class
    {σ : Type*} (c : σ → K[B]ˣ)
    {s s0 : σ} {lp lp0 : K[A]} {d : B}
    (hlp : lp ≠ 0) (hlp0 : lp0 ≠ 0)
    (hd : IsLocalRing.residue B d ≠ 0)
    (hterm :
      algebraMap K[A] K[B] lp * (c s : K[B]) =
        algebraMap B K[B] d * (algebraMap K[A] K[B] lp0 * (c s0 : K[B]))) :
    let a : K[A]ˣ := Units.mk0 lp hlp * (Units.mk0 lp0 hlp0)⁻¹
    let b : Bˣ := (isUnit_of_residue_ne_zero (B := B) d hd).unit
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        ((((Units.map (algebraMap K[A] K[B]).toMonoidHom a) *
            (Units.map (algebraMap B K[B]).toMonoidHom b)) * c s) * (c s0)⁻¹))) : Q) =
    ((Quotient.mk'' (1 : Γ[B]ˣ)) : Q) := by
  let a : K[A]ˣ := Units.mk0 lp hlp * (Units.mk0 lp0 hlp0)⁻¹
  let b : Bˣ := (isUnit_of_residue_ne_zero (B := B) d hd).unit
  let fA : K[A]ˣ →* K[B]ˣ := Units.map (algebraMap K[A] K[B]).toMonoidHom
  let fB : Bˣ →* K[B]ˣ := Units.map (algebraMap B K[B]).toMonoidHom
  have hb : (b : B) = d := by
    exact (isUnit_of_residue_ne_zero (B := B) d hd).unit_spec
  have hterm_units :
      fA (Units.mk0 lp hlp) * c s = fB b * (fA (Units.mk0 lp0 hlp0) * c s0) := by
    -- Rewrite the normalized equality at the level of units in the fraction field.
    apply Units.ext
    simpa [fA, fB, b, hb, mul_assoc, mul_left_comm, mul_comm] using hterm
  have hnormalized :
      fA a * c s = fB b * c s0 := by
    -- Cancel the leading source coefficient to isolate the normalized slice comparison.
    calc
      fA a * c s = (fA (Units.mk0 lp hlp) * (fA (Units.mk0 lp0 hlp0))⁻¹) * c s := by
        simp [a, fA, map_mul]
      _ = (fA (Units.mk0 lp0 hlp0))⁻¹ * (fA (Units.mk0 lp hlp) * c s) := by
        simp [mul_assoc, mul_comm]
      _ = (fA (Units.mk0 lp0 hlp0))⁻¹ * (fB b * (fA (Units.mk0 lp0 hlp0) * c s0)) := by
        rw [hterm_units]
      _ = fB b * c s0 := by
        simp [mul_assoc, mul_left_comm, mul_comm]
  have hratio :
      (fA a * c s) * (c s0)⁻¹ = fB b := by
    -- Divide by the leading slice unit to obtain the target-ring unit representative.
    calc
      (fA a * c s) * (c s0)⁻¹ = (fB b * c s0) * (c s0)⁻¹ := by rw [hnormalized]
      _ = fB b := by simp [mul_assoc]
  have hb_class :
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (fB b))) : Q) =
      ((Quotient.mk'' (1 : Γ[B]ˣ)) : Q) := by
    -- A target-ring unit has trivial quotient class in the value-group quotient.
    simpa [fB] using
      value_group_quotient_class_mul_target_ring_unit (A := A) (B := B) b (1 : K[B]ˣ)
  have hdrop_target_unit :
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (fB b * ((fA a * c s) * (c s0)⁻¹)))) : Q) =
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          ((fA a * c s) * (c s0)⁻¹))) : Q) := by
    -- The extra target-ring unit can be stripped before applying the residue argument.
    simpa [fB] using
      value_group_quotient_class_mul_target_ring_unit (A := A) (B := B) b
        ((fA a * c s) * (c s0)⁻¹)
  have hratio_class :
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          ((fA a * c s) * (c s0)⁻¹))) : Q) =
      ((Quotient.mk'' (1 : Γ[B]ˣ)) : Q) := by
    -- The normalized ratio itself is the image of a target-ring unit, hence already trivial.
    rw [hratio]
    exact hb_class
  -- Combine the normalized-ratio computation with the unit-cancellation step.
  have hprepend :
      ((fA a * fB b) * c s) * (c s0)⁻¹ = fB b * ((fA a * c s) * (c s0)⁻¹) := by
    -- Reassociate the normalized term so the target-ring unit cancellation lemma applies directly.
    simp [mul_left_comm, mul_comm]
  change
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        (((fA a * fB b) * c s) * (c s0)⁻¹))) : Q) =
      ((Quotient.mk'' (1 : Γ[B]ˣ)) : Q)
  rw [hprepend]
  exact hdrop_target_unit.trans hratio_class

/-- Helper for Lemma 15.124.2: the pointwise normalized support identity already kills every
nonleading residue coefficient. -/
lemma normalized_support_term_residue_eq_zero
    {σ : Type*} (c : σ → K[B]ˣ)
    (hc : Function.Injective fun s ↦
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (c s))) : Q))
    {s s0 : σ} {lp lp0 : K[A]} {d : B}
    (hlp : lp ≠ 0) (hlp0 : lp0 ≠ 0)
    (hs : s ≠ s0)
    (hterm :
      algebraMap K[A] K[B] lp * (c s : K[B]) =
        algebraMap B K[B] d * (algebraMap K[A] K[B] lp0 * (c s0 : K[B]))) :
    IsLocalRing.residue B d = 0 := by
  -- Feed the explicit normalized quotient-class identity into the earlier slice-vanishing lemma.
  refine normalized_nonleading_slice_residue_eq_zero (A := A) (B := B) c hc
    (a := Units.mk0 lp hlp * (Units.mk0 lp0 hlp0)⁻¹) (d := d) hs ?_
  intro hd
  simpa using
    normalized_support_term_trivial_class (A := A) (B := B) c hlp hlp0 hd hterm

/-- Helper for Lemma 15.124.2: among finitely many nonzero elements of the target fraction field,
one term divides all the others through a coefficient from `B`. -/
lemma exists_support_term_multiple_all
    {α : Type*} (s : Finset α) (t : α → K[B])
    (hs : s.Nonempty) (ht : ∀ a ∈ s, t a ≠ 0) :
    ∃ a0 ∈ s, ∀ a ∈ s, ∃ d : B, t a = algebraMap B K[B] d * t a0 := by
  classical
  revert hs ht
  refine Finset.induction_on s ?_ ?_
  · intro hs0 ht
    simpa using hs0
  · intro head s hhead hsind hne ht
    by_cases hs' : s.Nonempty
    · have hrest : ∀ b ∈ s, t b ≠ 0 := fun b hb ↦ ht b (Finset.mem_insert_of_mem hb)
      rcases hsind hs' hrest with ⟨a0, ha0, hmul⟩
      have hthead : t head ≠ 0 := ht head (Finset.mem_insert_self head s)
      have hta0 : t a0 ≠ 0 := hrest a0 ha0
      have hcompare :=
        (ValuationRing.iff_isInteger_or_isInteger B K[B]).mp inferInstance
          (t head * (t a0)⁻¹)
      rcases hcompare with ⟨d, hd⟩ | ⟨d, hd⟩
      · refine ⟨a0, Finset.mem_insert_of_mem ha0, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with hb | hb'
        · refine ⟨d, ?_⟩
          subst hb
          -- Rewrite the comparison ratio back into a divisibility statement by `t a0`.
          calc
            t b = (t b * (t a0)⁻¹) * t a0 := by
              rw [mul_assoc, inv_mul_cancel₀ hta0, mul_one]
            _ = algebraMap B K[B] d * t a0 := by rw [hd]
        · exact hmul b hb'
      · refine ⟨head, Finset.mem_insert_self head s, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with hb | hb'
        · subst hb
          refine ⟨1, by simp⟩
        · rcases hmul b hb' with ⟨d', hd'⟩
          refine ⟨d' * d, ?_⟩
          have ha0_multiple : t a0 = algebraMap B K[B] d * t head := by
            -- The inverse-ratio case shows that the previous leading term is itself a multiple of
            -- the new candidate `t head`.
            calc
              t a0 = ((t head * (t a0)⁻¹)⁻¹) * t head := by
                field_simp [hthead, hta0]
              _ = algebraMap B K[B] d * t head := by rw [hd]
          calc
            t b = algebraMap B K[B] d' * t a0 := hd'
            _ = algebraMap B K[B] d' * (algebraMap B K[B] d * t head) := by
              rw [ha0_multiple]
            _ = algebraMap B K[B] (d' * d) * t head := by
              simp [mul_assoc]
    · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst hs_empty
      refine ⟨head, by simp, ?_⟩
      intro b hb
      have hb' : b = head := by simpa using hb
      subst hb'
      refine ⟨1, by simp⟩

/-- Helper for Lemma 15.124.2: if a source fraction becomes an element of `B` after mapping to the
target fraction field, then it already comes from `A`. -/
lemma source_fraction_eq_target_integer
    (x : K[A]) {d : B}
    (hx : algebraMap K[A] K[B] x = algebraMap B K[B] d) :
    ∃ a : A, x = algebraMap A K[A] a := by
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  · rcases (ValuationRing.iff_isInteger_or_isInteger A K[A]).mp inferInstance x with
        ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, ha.symm⟩
    · have ha' : algebraMap B K[B] (algebraMap A B a) = (algebraMap K[A] K[B] x)⁻¹ := by
        calc
          algebraMap B K[B] (algebraMap A B a) = algebraMap A K[B] a := by
            simpa [RingHom.comp_apply] using
              (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B K[B]) a).symm
          _ = algebraMap K[A] K[B] (algebraMap A K[A] a) := by
            simpa [RingHom.comp_apply] using
              DFunLike.congr_fun (IsScalarTower.algebraMap_eq A K[A] K[B]) a
          _ = (algebraMap K[A] K[B] x)⁻¹ := by
            rw [ha]
            simp
      have hmul : d * algebraMap A B a = 1 := by
        have hxmap : algebraMap K[A] K[B] x ≠ 0 := by
          exact (map_ne_zero_iff (algebraMap K[A] K[B]) (RingHom.injective _)).mpr hx0
        apply IsFractionRing.injective B K[B]
        calc
          algebraMap B K[B] (d * algebraMap A B a)
              = algebraMap B K[B] d * algebraMap B K[B] (algebraMap A B a) := by
                  simp
          _ = algebraMap B K[B] d * (algebraMap K[A] K[B] x)⁻¹ := by
                  rw [ha']
          _ = algebraMap K[A] K[B] x * (algebraMap K[A] K[B] x)⁻¹ := by
                  rw [hx]
          _ = algebraMap B K[B] 1 := by
                  simp [hxmap]
      have hunitB : IsUnit (algebraMap A B a) := IsUnit.of_mul_eq_one_right d hmul
      have hunitA : IsUnit a := isUnit_of_map_unit (algebraMap A B) a hunitB
      refine ⟨↑hunitA.unit⁻¹, ?_⟩
      -- Inverting the source-integrality witness turns the unit coefficient back into `x`.
      simpa [hx0] using (congrArg Inv.inv ha).symm

/-- Helper for Lemma 15.124.2: once every support term is normalized against the same leading
term, the original fraction-field relation becomes a genuine relation in `B`. -/
lemma normalized_support_relation_sum_eq_zero
    {ι σ : Type*} (u : ι → B) (c : σ → K[B]ˣ)
    (l : (ι × σ) →₀ K[A]) {i0 : ι} {s0 : σ}
    (hl : Finsupp.linearCombination K[A]
      (fun p : ι × σ ↦ algebraMap B K[B] (u p.1) * (c p.2 : K[B])) l = 0)
    (hl0 : l (i0, s0) ≠ 0)
    (d : ι × σ → B)
    (hnormalize :
      ∀ p ∈ l.support,
        algebraMap K[A] K[B] (l p) * (c p.2 : K[B]) =
          algebraMap B K[B] (d p) *
            (algebraMap K[A] K[B] (l (i0, s0)) * (c s0 : K[B]))) :
    l.support.sum (fun p ↦ d p * u p.1) = 0 := by
  let lead : K[B] := algebraMap K[A] K[B] (l (i0, s0)) * (c s0 : K[B])
  have hlead_ne_zero : lead ≠ 0 := by
    -- The chosen leading coefficient and the fixed unit representative are both nonzero.
    have hmap_ne_zero : algebraMap K[A] K[B] (l (i0, s0)) ≠ 0 := by
      exact (map_ne_zero_iff (algebraMap K[A] K[B]) (RingHom.injective _)).mpr hl0
    exact mul_ne_zero hmap_ne_zero (Units.ne_zero _)
  have hl_sum :
      l.support.sum
        (fun p ↦ algebraMap K[A] K[B] (l p) *
          (algebraMap B K[B] (u p.1) * (c p.2 : K[B]))) = 0 := by
    -- Rewrite the linear relation as an explicit finite sum over the support.
    simpa [Finsupp.linearCombination, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using hl
  have hrewritten :
      l.support.sum (fun p ↦ algebraMap B K[B] (d p * u p.1) * lead) = 0 := by
    -- Replace each summand by its normalized form relative to the chosen leading term.
    calc
      l.support.sum (fun p ↦ algebraMap B K[B] (d p * u p.1) * lead)
          = l.support.sum
              (fun p ↦ algebraMap K[A] K[B] (l p) *
                (algebraMap B K[B] (u p.1) * (c p.2 : K[B]))) := by
                  refine Finset.sum_congr rfl ?_
                  intro p hp
                  calc
                    algebraMap B K[B] (d p * u p.1) * lead
                        = algebraMap B K[B] (u p.1) *
                            (algebraMap B K[B] (d p) * lead) := by
                              simp [lead, mul_assoc, mul_left_comm, mul_comm]
                    _ = algebraMap B K[B] (u p.1) *
                          (algebraMap K[A] K[B] (l p) * (c p.2 : K[B])) := by
                              rw [hnormalize p hp]
                    _ = algebraMap K[A] K[B] (l p) *
                          (algebraMap B K[B] (u p.1) * (c p.2 : K[B])) := by
                              simp [mul_assoc, mul_left_comm, mul_comm]
      _ = 0 := hl_sum
  have hsum_map_zero :
      l.support.sum (fun p ↦ algebraMap B K[B] (d p * u p.1)) = 0 := by
    -- Cancel the common nonzero leading factor in the fraction field.
    have hmul_zero :
        l.support.sum (fun p ↦ algebraMap B K[B] (d p * u p.1)) * lead = 0 := by
      calc
        l.support.sum (fun p ↦ algebraMap B K[B] (d p * u p.1)) * lead
            = l.support.sum (fun p ↦ algebraMap B K[B] (d p * u p.1) * lead) := by
                rw [Finset.sum_mul]
        _ = 0 := hrewritten
    exact (mul_eq_zero.mp hmul_zero).resolve_right hlead_ne_zero
  have hmap_sum :
      algebraMap B K[B] (l.support.sum fun p ↦ d p * u p.1) =
        l.support.sum (fun p ↦ algebraMap B K[B] (d p * u p.1)) := by
    -- Pull the normalized relation back through the injective fraction-field map.
    simpa using (map_sum (algebraMap B K[B]) (fun p ↦ d p * u p.1) l.support)
  apply IsFractionRing.injective B K[B]
  rw [hmap_sum, hsum_map_zero, map_zero]

/-- Helper for Lemma 15.124.2: in the leading slice, a normalized coefficient already comes from
the source valuation ring. -/
lemma normalized_same_slice_coefficient_from_source
    {σ : Type*} (c : σ → K[B]ˣ)
    {s0 : σ} {lp lp0 : K[A]} {d : B}
    (hlp0 : lp0 ≠ 0)
    (hterm :
      algebraMap K[A] K[B] lp * (c s0 : K[B]) =
        algebraMap B K[B] d * (algebraMap K[A] K[B] lp0 * (c s0 : K[B]))) :
    ∃ a : A, d = algebraMap A B a ∧ lp = algebraMap A K[A] a * lp0 := by
  have hc_ne_zero : (c s0 : K[B]) ≠ 0 := Units.ne_zero _
  have hcancel :
      algebraMap K[A] K[B] lp =
        algebraMap B K[B] d * algebraMap K[A] K[B] lp0 := by
    -- Cancel the common unit representative of the leading value-group slice.
    apply mul_right_cancel₀ hc_ne_zero
    simpa [mul_assoc, mul_left_comm, mul_comm] using hterm
  have hlp0_map : algebraMap K[A] K[B] lp0 ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap K[A] K[B]) (RingHom.injective _)).mpr hlp0
  have hsource :
      algebraMap K[A] K[B] (lp * lp0⁻¹) = algebraMap B K[B] d := by
    -- Divide by the leading source coefficient to isolate the normalized scalar.
    calc
      algebraMap K[A] K[B] (lp * lp0⁻¹)
          = algebraMap K[A] K[B] lp * (algebraMap K[A] K[B] lp0)⁻¹ := by
              simp
      _ = (algebraMap B K[B] d * algebraMap K[A] K[B] lp0) *
            (algebraMap K[A] K[B] lp0)⁻¹ := by
              rw [hcancel]
      _ = algebraMap B K[B] d := by
              simp [mul_assoc, mul_left_comm, mul_comm, hlp0_map]
  rcases source_fraction_eq_target_integer (A := A) (B := B) (lp * lp0⁻¹) hsource with ⟨a, ha⟩
  have hd_eq :
      d = algebraMap A B a := by
    -- The normalized scalar agrees with the image of the recovered source coefficient.
    apply IsFractionRing.injective B K[B]
    calc
      algebraMap B K[B] d = algebraMap K[A] K[B] (lp * lp0⁻¹) := hsource.symm
      _ = algebraMap K[A] K[B] (algebraMap A K[A] a) := by rw [ha]
      _ = algebraMap B K[B] (algebraMap A B a) := by
            calc
              algebraMap K[A] K[B] (algebraMap A K[A] a) = algebraMap A K[B] a := by
                simpa [RingHom.comp_apply] using
                  (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A K[A] K[B]) a).symm
              _ = algebraMap B K[B] (algebraMap A B a) := by
                simpa [RingHom.comp_apply] using
                  (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B K[B]) a).symm
  have hl_eq :
      lp = algebraMap A K[A] a * lp0 := by
    -- Multiplying back by the chosen leading coefficient recovers the original source scalar.
    calc
      lp = (lp * lp0⁻¹) * lp0 := by
            simp [hlp0, mul_assoc, mul_left_comm, mul_comm]
      _ = algebraMap A K[A] a * lp0 := by rw [ha]
  exact ⟨a, hd_eq, hl_eq⟩

/-- Helper for Lemma 15.124.2: reducing a product with a source coefficient transports that
coefficient to the residue-field scalar action. -/
lemma residue_mul_algebraMap_eq_smul (a : A) (b : B) :
    IsLocalRing.residue B (algebraMap A B a * b) =
      IsLocalRing.residue A a • IsLocalRing.residue B b := by
  -- Compare the residue-field scalar action with the residue-field map induced by `A → B`.
  rw [Algebra.smul_def]
  rw [show algebraMap (ResidueField A) (ResidueField B) =
    IsLocalRing.ResidueField.map (algebraMap A B) by rfl]
  calc
    (IsLocalRing.ResidueField.map (algebraMap A B) (IsLocalRing.residue A a)) *
        IsLocalRing.residue B b
        = IsLocalRing.residue B (algebraMap A B a) * IsLocalRing.residue B b := by
            rw [IsLocalRing.ResidueField.map_residue (algebraMap A B)]
    _ = IsLocalRing.residue B (algebraMap A B a * b) := by
            rw [← map_mul]

lemma products_of_residue_lifts_and_distinct_value_classes_linearIndependent
    {ι σ : Type*} (u : ι → B) (c : σ → K[B]ˣ)
    (hu : LinearIndependent (ResidueField A) (fun i ↦ IsLocalRing.residue B (u i)))
    (hc : Function.Injective fun s ↦
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (c s))) : Q)) :
    LinearIndependent K[A] (fun p : ι × σ ↦ algebraMap B K[B] (u p.1) * (c p.2 : K[B])) := by
  -- Route correction: the remaining blocker is the quotient-class normalization step. The intended
  -- proof chooses a term of maximal valuation, divides by that term, uses quotient-class invariance
  -- under multiplication by source-field units to isolate a single `σ`-slice, and then reduces to
  -- the already-proved residue-lift linear independence statement.
  classical
  rw [linearIndependent_iff]
  intro l hl
  by_cases hl0 : l = 0
  · exact hl0
  have hsupport : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hl0
  let t : ι × σ → K[B] := fun p ↦ algebraMap K[A] K[B] (l p) * (c p.2 : K[B])
  have ht_nonzero : ∀ p ∈ l.support, t p ≠ 0 := by
    intro p hp
    have hlp : l p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hlp_map : algebraMap K[A] K[B] (l p) ≠ 0 := by
      exact (map_ne_zero_iff (algebraMap K[A] K[B]) (RingHom.injective _)).mpr hlp
    exact mul_ne_zero hlp_map (Units.ne_zero _)
  -- Choose a support term whose valuation is minimal, expressed as divisibility through `B`.
  rcases exists_support_term_multiple_all l.support t hsupport ht_nonzero with
      ⟨p0, hp0, hmultiple⟩
  rcases p0 with ⟨i0, s0⟩
  have hp0_support : (i0, s0) ∈ l.support := hp0
  have hlp0 : l (i0, s0) ≠ 0 := Finsupp.mem_support_iff.mp hp0_support
  have hnormalize :
      ∀ p ∈ l.support, ∃ d : B,
        algebraMap K[A] K[B] (l p) * (c p.2 : K[B]) =
          algebraMap B K[B] d *
            (algebraMap K[A] K[B] (l (i0, s0)) * (c s0 : K[B])) := by
    intro p hp
    simpa [t] using hmultiple p hp
  let d : ι × σ → B := fun p ↦
    if hp : p ∈ l.support then Classical.choose (hnormalize p hp) else 0
  have hd_normalize :
      ∀ p ∈ l.support,
        algebraMap K[A] K[B] (l p) * (c p.2 : K[B]) =
          algebraMap B K[B] (d p) *
            (algebraMap K[A] K[B] (l (i0, s0)) * (c s0 : K[B])) := by
    -- Freeze one normalization witness for each support term.
    intro p hp
    rw [d, dif_pos hp]
    exact Classical.choose_spec (hnormalize p hp)
  have hsumB_zero :
      l.support.sum (fun p ↦ d p * u p.1) = 0 := by
    -- Cancel the common leading factor and pull the relation back to `B`.
    exact normalized_support_relation_sum_eq_zero (A := A) (B := B) u c l hl hlp0 d hd_normalize
  let ρ : B →+* ResidueField B := IsLocalRing.residue B
  have hres_sum :
      l.support.sum (fun p ↦ ρ (d p * u p.1)) = 0 := by
    -- Reducing the normalized `B`-relation modulo the maximal ideal is the residue-level relation.
    have hres_eq : ρ (l.support.sum (fun p ↦ d p * u p.1)) = 0 := by
      simpa [ρ] using congrArg ρ hsumB_zero
    simpa [ρ, map_sum] using hres_eq
  let leadSlice : Finset (ι × σ) := l.support.filter (fun p : ι × σ ↦ p.2 = s0)
  have hnonleading_residue :
      ∀ p ∈ l.support, p.2 ≠ s0 → ρ (d p) = 0 := by
    -- Any support term outside the leading slice has residue-zero normalizing coefficient.
    intro p hp hs
    exact normalized_support_term_residue_eq_zero (A := A) (B := B) c hc
      (hlp := Finsupp.mem_support_iff.mp hp) (hlp0 := hlp0) (hs := hs) (hd_normalize p hp)
  have hnonleading_sum_zero :
      (l.support.filter fun p : ι × σ ↦ p.2 ≠ s0).sum (fun p ↦ ρ (d p * u p.1)) = 0 := by
    -- Off the leading slice, every residue term vanishes because the coefficient residue is zero.
    refine Finset.sum_eq_zero ?_
    intro p hp
    have hp_support : p ∈ l.support := (Finset.mem_filter.mp hp).1
    have hp_ne : p.2 ≠ s0 := (Finset.mem_filter.mp hp).2
    calc
      ρ (d p * u p.1) = ρ (d p) * ρ (u p.1) := by rw [map_mul]
      _ = 0 := by simp [hnonleading_residue p hp_support hp_ne]
  have hlead_sum :
      leadSlice.sum (fun p ↦ ρ (d p * u p.1)) = 0 := by
    -- Splitting the support into the leading slice and its complement isolates the only surviving
    -- residue terms.
    calc
      leadSlice.sum (fun p ↦ ρ (d p * u p.1))
          = leadSlice.sum (fun p ↦ ρ (d p * u p.1)) +
              (l.support.filter fun p : ι × σ ↦ p.2 ≠ s0).sum (fun p ↦ ρ (d p * u p.1)) := by
                rw [hnonleading_sum_zero, add_zero]
      _ = l.support.sum (fun p ↦ ρ (d p * u p.1)) := by
            simpa [leadSlice] using
              (Finset.sum_filter_add_sum_filter_not (s := l.support)
                (p := fun p : ι × σ ↦ p.2 = s0)
                (f := fun p ↦ ρ (d p * u p.1)))
      _ = 0 := hres_sum
  have hsame_slice :
      ∀ i, (i, s0) ∈ l.support →
        ∃ a : A, d (i, s0) = algebraMap A B a ∧
          l (i, s0) = algebraMap A K[A] a * l (i0, s0) := by
    -- On the leading slice, the normalized coefficient already lies in the image of `A`.
    intro i hi
    exact normalized_same_slice_coefficient_from_source (A := A) (B := B) c hlp0
      (hd_normalize (i, s0) hi)
  let aFun : ι → A := fun i ↦
    if hi : (i, s0) ∈ l.support then Classical.choose (hsame_slice i hi) else 0
  have haFun_d :
      ∀ i, (i, s0) ∈ l.support → d (i, s0) = algebraMap A B (aFun i) := by
    -- Record the recovered source coefficient on each surviving leading-slice term.
    intro i hi
    rw [aFun, dif_pos hi]
    exact (Classical.choose_spec (hsame_slice i hi)).1
  have haFun_l :
      ∀ i, (i, s0) ∈ l.support →
        l (i, s0) = algebraMap A K[A] (aFun i) * l (i0, s0) := by
    -- The same source coefficient describes the original source-field scalar as well.
    intro i hi
    rw [aFun, dif_pos hi]
    exact (Classical.choose_spec (hsame_slice i hi)).2
  let leadIndices : Finset ι := leadSlice.image Prod.fst
  let mFun : ι → ResidueField A := fun i ↦ IsLocalRing.residue A (aFun i)
  have hmFun_support : ∀ i, mFun i ≠ 0 → i ∈ leadIndices := by
    -- Only indices that actually occur in the leading slice can contribute a nonzero coefficient.
    intro i hi
    by_cases his : (i, s0) ∈ l.support
    · show i ∈ leadSlice.image Prod.fst
      exact Finset.mem_image.mpr ⟨(i, s0), by simpa [leadSlice, his], rfl⟩
    · have hzero : mFun i = 0 := by
        change IsLocalRing.residue A (aFun i) = 0
        simp [aFun, his]
      exact False.elim (hi hzero)
  let m : ι →₀ ResidueField A := Finsupp.onFinset leadIndices mFun hmFun_support
  have hlead_term :
      ∀ p ∈ leadSlice, ρ (d p * u p.1) = mFun p.1 • ρ (u p.1) := by
    -- Each leading-slice term is the residue of a source coefficient times the chosen lift.
    intro p hp
    rcases p with ⟨i, s⟩
    have hp_filter : (i, s) ∈ l.support.filter (fun q : ι × σ ↦ q.2 = s0) := by
      simpa [leadSlice] using hp
    have hp_support : (i, s) ∈ l.support := (Finset.mem_filter.mp hp_filter).1
    have hs : s = s0 := by
      simpa using (Finset.mem_filter.mp hp_filter).2
    subst hs
    calc
      ρ (d (i, s0) * u i) = ρ (algebraMap A B (aFun i) * u i) := by
        rw [haFun_d i hp_support]
      _ = mFun i • ρ (u i) := by
        simpa [mFun] using residue_mul_algebraMap_eq_smul (A := A) (B := B) (aFun i) (u i)
  have hleadIndices_sum :
      leadIndices.sum (fun i ↦ mFun i • ρ (u i)) = 0 := by
    -- Reindex the surviving leading slice by its first coordinate and keep the residue relation.
    calc
      leadIndices.sum (fun i ↦ mFun i • ρ (u i))
          = leadSlice.sum (fun p ↦ mFun p.1 • ρ (u p.1)) := by
              show (leadSlice.image Prod.fst).sum (fun i ↦ mFun i • ρ (u i)) =
                leadSlice.sum (fun p ↦ mFun p.1 • ρ (u p.1))
              rw [Finset.sum_image]
              intro p hp q hq hpq
              rcases p with ⟨i, s⟩
              rcases q with ⟨j, t⟩
              have hp_filter : (i, s) ∈ l.support.filter (fun r : ι × σ ↦ r.2 = s0) := by
                simpa [leadSlice] using hp
              have hq_filter : (j, t) ∈ l.support.filter (fun r : ι × σ ↦ r.2 = s0) := by
                simpa [leadSlice] using hq
              have hs : s = s0 := by
                simpa using (Finset.mem_filter.mp hp_filter).2
              have ht : t = s0 := by
                simpa using (Finset.mem_filter.mp hq_filter).2
              subst hs
              subst ht
              simpa using hpq
      _ = leadSlice.sum (fun p ↦ ρ (d p * u p.1)) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            symm
            exact hlead_term p hp
      _ = 0 := hlead_sum
  have hm_relation :
      Finsupp.linearCombination (ResidueField A)
        (fun i ↦ IsLocalRing.residue B (u i)) m = 0 := by
    -- Package the leading-slice residue relation as a finitely supported coefficient family on `ι`.
    have hm_supported :
        m ∈ Finsupp.supported (ResidueField A) (ResidueField A) (↑leadIndices : Set ι) := by
      -- The coefficient family `m` is supported exactly on the leading indices by construction.
      rw [Finsupp.mem_supported]
      simpa [m] using
        (Finsupp.support_onFinset_subset (s := leadIndices) (f := mFun) (hf := hmFun_support))
    calc
      Finsupp.linearCombination (ResidueField A)
          (fun i ↦ IsLocalRing.residue B (u i)) m
          = leadIndices.sum (fun i ↦ m i • IsLocalRing.residue B (u i)) := by
              exact Finsupp.linearCombination_apply_of_mem_supported hm_supported
      _ = leadIndices.sum (fun i ↦ mFun i • IsLocalRing.residue B (u i)) := by
            -- On the chosen finite support, `m` agrees pointwise with the original coefficient
            -- function `mFun`.
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finsupp.onFinset_apply]
      _ = 0 := hleadIndices_sum
  have hi0_lead : i0 ∈ leadIndices := by
    -- The chosen leading term certainly contributes to the leading slice index set.
    show i0 ∈ leadSlice.image Prod.fst
    exact Finset.mem_image.mpr
      ⟨(i0, s0), by simpa [leadSlice] using Finset.mem_filter.mpr ⟨hp0_support, rfl⟩, rfl⟩
  have haFun_i0 : aFun i0 = 1 := by
    -- The leading term normalizes against itself, so its recovered source coefficient is `1`.
    have hself :
        l (i0, s0) = algebraMap A K[A] (aFun i0) * l (i0, s0) := haFun_l i0 hp0_support
    have hmap_one : algebraMap A K[A] (aFun i0) = 1 := by
      apply (mul_right_cancel₀ hlp0)
      simpa using hself.symm
    exact IsFractionRing.injective A K[A] (by simpa using hmap_one)
  have hm_i0 : m i0 = 1 := by
    -- The resulting residue-field coefficient family is nontrivial at the leading index.
    rw [Finsupp.onFinset_apply]
    simp [m, leadIndices, mFun, hi0_lead, haFun_i0]
  have hm_zero : m = 0 := by
    exact (linearIndependent_iff.mp hu) m hm_relation
  have : m i0 = 0 := by
    simpa [hm_zero]
  exact False.elim (zero_ne_one (this.symm.trans hm_i0))

/-- Helper for Lemma 15.124.2: every class in the target value-group quotient is represented by a
unit of `K[B]`. -/
lemma exists_value_group_quotient_representative (q : Q) :
    ∃ c : K[B]ˣ,
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c)) :
        Q) = q := by
  classical
  -- Choose a concrete unit-valued representative of the quotient class.
  let γ : Γ[B]ˣ := Quotient.out q
  let x : K[B] := Classical.choose (ValuativeRel.valuation_surjective (γ : Γ[B]))
  have hx : (ValuativeRel.valuation K[B]) x = γ := by
    exact Classical.choose_spec (ValuativeRel.valuation_surjective (γ : Γ[B]))
  have hx0 : x ≠ 0 := by
    intro hx0
    have hγ : (γ : Γ[B]) = 0 := by
      simpa [hx0] using hx.symm
    exact γ.ne_zero hγ
  refine ⟨Units.mk0 x hx0, ?_⟩
  -- The chosen unit maps back to the original quotient class by construction.
  change
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        (Units.mk0 x hx0))) : Q) = q
  have hval :
      Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        (Units.mk0 x hx0) = γ := by
    ext
    simp [hx]
  rw [hval]
  exact Quotient.out_eq q

/-- Helper for Lemma 15.124.2: a fixed choice of unit representative for each value-group quotient
class. -/
noncomputable def value_group_quotient_representative (q : Q) : K[B]ˣ :=
  Classical.choose (exists_value_group_quotient_representative (A := A) (B := B) q)

/-- Helper for Lemma 15.124.2: the chosen unit representative maps to the prescribed quotient
class. -/
lemma value_group_quotient_representative_spec (q : Q) :
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        (value_group_quotient_representative (A := A) (B := B) q))) : Q) = q :=
  Classical.choose_spec (exists_value_group_quotient_representative (A := A) (B := B) q)

-- Proof sketch: compare the induced map `A → B` on valuation rings with the reduction modulo their
-- maximal ideals. The usual linear-independence argument over the residue field shows that any
-- residue-field basis lifts to a `K`-linearly independent family in `L`, forcing finiteness.
/-- The residue field extension of a finite fraction-field extension of valuation rings is
finite-dimensional. -/
theorem finiteDimensional_residueField_of_finiteDimensional_fractionField_extension
    [FiniteDimensional K[A] K[B]] :
    FiniteDimensional (ResidueField A) (ResidueField B) := by
  classical
  let ι := Module.Free.ChooseBasisIndex (ResidueField A) (ResidueField B)
  let b : Module.Basis ι (ResidueField A) (ResidueField B) :=
    Module.Free.chooseBasis (ResidueField A) (ResidueField B)
  let u : ι → B := fun i ↦ Classical.choose (IsLocalRing.residue_surjective (b i))
  have hu : ∀ i, IsLocalRing.residue B (u i) = b i := by
    intro i
    exact Classical.choose_spec (IsLocalRing.residue_surjective (b i))
  -- Lift a residue-field basis to elements of `B` and transfer independence to `K[B]`.
  have hlin_res : LinearIndependent (ResidueField A) (fun i ↦ IsLocalRing.residue B (u i)) := by
    simpa [hu] using b.linearIndependent
  have hlin_frac : LinearIndependent K[A] (fun i ↦ algebraMap B K[B] (u i)) :=
    residue_lifts_linearIndependent (A := A) (B := B) u hlin_res
  -- The lifted independent family is bounded by the `K[A]`-dimension of `K[B]`.
  have hcard : Cardinal.mk ι ≤ Module.finrank K[A] K[B] :=
    hlin_frac.cardinalMk_le_finrank
  have hrank_lt : Module.rank (ResidueField A) (ResidueField B) < Cardinal.aleph0 := by
    calc
      Module.rank (ResidueField A) (ResidueField B) = Cardinal.mk ι := by
        simpa using b.mk_eq_rank''.symm
      _ ≤ Module.finrank K[A] K[B] := hcard
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  -- Once the basis index is finite, the residue field extension is finite-dimensional.
  letI : Fintype ι := Module.Basis.fintypeIndexOfRankLtAleph0 b hrank_lt
  exact Module.Basis.finiteDimensional_of_finite b

attribute [local instance]
  finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

-- Proof sketch: pick units of `B` whose residue classes are linearly independent over
-- `ResidueField A` and pick nonzero elements whose values represent distinct cosets in the quotient
-- `Γ_B / Γ_A`. The textbook minimal-valuation argument shows that all products `bᵢ cⱼ` are
-- `K`-linearly independent in `L`, giving the stated inequality.
/-- Lemma 15.124.2: if `A ⊆ B` is an extension of valuation rings with fraction fields `K ⊆ L`
and `L / K` is finite, then the value-group index times the residue-field degree is bounded by the
fraction-field degree. -/
@[stacks 0ASH]
theorem ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension
    [FiniteDimensional K[A] K[B]] :
    ramificationIndex A B * residueDegree A B ≤
      Module.finrank K[A] K[B] := by
  classical
  let ι := Module.Free.ChooseBasisIndex (ResidueField A) (ResidueField B)
  let b : Module.Basis ι (ResidueField A) (ResidueField B) :=
    Module.Free.chooseBasis (ResidueField A) (ResidueField B)
  let u : ι → B := fun i ↦ Classical.choose (IsLocalRing.residue_surjective (b i))
  have hu : ∀ i, IsLocalRing.residue B (u i) = b i := by
    intro i
    exact Classical.choose_spec (IsLocalRing.residue_surjective (b i))
  -- Start from a residue-field basis and choose one unit representative for each quotient class.
  have hlin_res : LinearIndependent (ResidueField A) (fun i ↦ IsLocalRing.residue B (u i)) := by
    simpa [hu] using b.linearIndependent
  let c : Q → K[B]ˣ := value_group_quotient_representative (A := A) (B := B)
  have hc : Function.Injective fun q ↦
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (c q))) : Q) := by
    intro q₁ q₂ hq
    simpa [c, value_group_quotient_representative_spec] using hq
  -- The product family indexed by the residue basis and the value-group quotient is independent.
  have hlin_prod : LinearIndependent K[A] (fun p : ι × Q ↦
      algebraMap B K[B] (u p.1) * (c p.2 : K[B])) :=
    products_of_residue_lifts_and_distinct_value_classes_linearIndependent
      (A := A) (B := B) u c hlin_res hc
  have hcard : Cardinal.mk (ι × Q) ≤ Module.finrank K[A] K[B] :=
    hlin_prod.cardinalMk_le_finrank
  have hrank_lt : Module.rank (ResidueField A) (ResidueField B) < Cardinal.aleph0 := by
    calc
      Module.rank (ResidueField A) (ResidueField B) = Cardinal.mk ι := by
        simpa using b.mk_eq_rank''.symm
      _ ≤ Module.finrank K[A] K[B] := by
        exact
          (residue_lifts_linearIndependent (A := A) (B := B) u hlin_res).cardinalMk_le_finrank
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  letI : Fintype ι := Module.Basis.fintypeIndexOfRankLtAleph0 b hrank_lt
  -- Convert the cardinal bound on the product family into the stated `ℕ∞` inequality.
  have henat : ENat.card (ι × Q) ≤ (Module.finrank K[A] K[B] : ℕ∞) := by
    have h_toENat := OrderHomClass.monotone Cardinal.toENat hcard
    rw [Cardinal.toENat_nat] at h_toENat
    simpa [ENat.card] using h_toENat
  calc
    ramificationIndex A B * residueDegree A B = ENat.card Q * ENat.card ι := by
      simp [IsExtensionOfValuationRings.ramificationIndex,
        IsExtensionOfValuationRings.residueDegree, Module.finrank_eq_card_basis b,
        ENat.card_eq_coe_fintype_card]
    _ = ENat.card (ι × Q) := by
      rw [ENat.card_prod, mul_comm]
    _ ≤ Module.finrank K[A] K[B] := henat

end
