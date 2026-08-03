module

public import Topology_Munkres_2000.Book.Exercise_58_2
public import Topology_Munkres_2000.Book.Example_53_6.Polar
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Proposition_61_1.Stereographic
public import Mathlib.Analysis.SpecialFunctions.Exp

public section

open Set

namespace PuncturedPlaneMap

/-- Helper for Remark 65.1: a set avoids any two points chosen from its complement. -/
lemma curve_subset_pairComplement
    {X : Type*} (C : Set X) (p q : (Cᶜ : Set X)) :
    C ⊆ ({(p : X), (q : X)}ᶜ : Set X) := by
  -- A point of `C` cannot equal either point whose membership proof lies in `Cᶜ`.
  intro x hxC hxPair
  rcases hxPair with hxp | hxq
  · exact p.property (hxp ▸ hxC)
  · exact q.property (hxq ▸ hxC)

end PuncturedPlaneMap

namespace StandardSphere

/-- Helper for Remark 65.1: forgetting the second puncture gives a nested point of the
once-punctured sphere. -/
private def pairComplementToNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) →
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  fun x ↦ ⟨⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩, fun hq ↦ x.2 (Or.inr hq)⟩

/-- Helper for Remark 65.1: flattening a nested puncture gives a point outside the
corresponding two-point set. -/
private def nestedPunctureToPairComplement (p q : StandardSphere 2) :
    {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} →
      ({p, q}ᶜ : Set (StandardSphere 2)) :=
  fun x ↦ ⟨x.1.1, fun h ↦ h.elim x.1.2 x.2⟩

/-- Helper for Remark 65.1: nesting a point outside two punctures is continuous. -/
private lemma continuous_pairComplementToNestedPuncture (p q : StandardSphere 2) :
    Continuous (pairComplementToNestedPuncture p q) := by
  -- Construct the two subtype layers one at a time so no transport is exposed later.
  have hinner : Continuous (fun x : ({p, q}ᶜ : Set (StandardSphere 2)) ↦
      (⟨x.1, fun hp ↦ x.2 (Or.inl hp)⟩ : ({p}ᶜ : Set (StandardSphere 2)))) :=
    continuous_subtype_val.subtype_mk
      (fun (x : ({p, q}ᶜ : Set (StandardSphere 2))) hp ↦ x.2 (Or.inl hp))
  exact hinner.subtype_mk (fun x hq ↦ x.2 (Or.inr hq))

/-- Helper for Remark 65.1: flattening a nested puncture is continuous. -/
private lemma continuous_nestedPunctureToPairComplement (p q : StandardSphere 2) :
    Continuous (nestedPunctureToPairComplement p q) := by
  -- The underlying map is the composite of the two canonical subtype projections.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x h ↦ h.elim x.1.2 x.2)

/-- Helper for Remark 65.1: flattening after nesting fixes a pair-complement point. -/
private lemma nestedPunctureToPairComplement_leftInverse (p q : StandardSphere 2) :
    Function.LeftInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- Compare the inexpensive ambient sphere values; membership proofs are irrelevant.
  intro x
  apply Subtype.ext
  exact Eq.refl x.1

/-- Helper for Remark 65.1: nesting after flattening fixes a nested puncture point. -/
private lemma nestedPunctureToPairComplement_rightInverse (p q : StandardSphere 2) :
    Function.RightInverse (nestedPunctureToPairComplement p q)
      (pairComplementToNestedPuncture p q) := by
  -- The outer subtype is determined by its once-punctured-sphere value.
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact Eq.refl x.1.1

/-- The complement of two sphere points is canonically the complement of the second
point inside the sphere punctured at the first. -/
private def pairComplementHomeomorphNestedPuncture (p q : StandardSphere 2) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ
      {x : ({p}ᶜ : Set (StandardSphere 2)) // x.1 ≠ q} :=
  { toFun := pairComplementToNestedPuncture p q
    invFun := nestedPunctureToPairComplement p q
    left_inv := nestedPunctureToPairComplement_leftInverse p q
    right_inv := nestedPunctureToPairComplement_rightInverse p q
    continuous_toFun := continuous_pairComplementToNestedPuncture p q
    continuous_invFun := continuous_nestedPunctureToPairComplement p q }

/-- Helper for Remark 65.1: distinct sphere points put the second point in the
complement of the first. -/
private lemma secondPoint_mem_firstPointComplement
    (p q : StandardSphere 2) (hpq : p ≠ q) : q ∈ ({p}ᶜ : Set (StandardSphere 2)) := by
  -- Complement membership is the reversed form of the distinctness hypothesis.
  simpa using hpq.symm

/-- Stereographic projection followed by the standard Euclidean-complex identification. -/
private noncomputable def puncturedSphereHomeomorphComplex (p : StandardSphere 2) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (puncturedHomeomorphPlane p).trans
    Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Remark 65.1: stereographic coordinates translated to send the second
puncture to zero. -/
private noncomputable def translatedPuncturedSphereChart
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p}ᶜ : Set (StandardSphere 2)) ≃ₜ ℂ :=
  (puncturedSphereHomeomorphComplex p).trans
    (Homeomorph.subRight
      (puncturedSphereHomeomorphComplex p
        ⟨q, secondPoint_mem_firstPointComplement p q hpq⟩))

/-- Helper for Remark 65.1: the translated chart is nonzero precisely away from the
second puncture. -/
private lemma translatedPuncturedSphereChart_ne_zero_iff
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p}ᶜ : Set (StandardSphere 2))) :
    x.1 ≠ q ↔ translatedPuncturedSphereChart p q hpq x ≠ 0 := by
  -- Translation converts nonvanishing into inequality of the original chart values.
  simp only [translatedPuncturedSphereChart, Homeomorph.trans_apply,
    Homeomorph.subRight_apply, sub_ne_zero]
  rw [(puncturedSphereHomeomorphComplex p).injective.ne_iff]
  simpa using (Subtype.coe_ne_coe (a := x)
    (b := (⟨q, secondPoint_mem_firstPointComplement p q hpq⟩ :
      ({p}ᶜ : Set (StandardSphere 2)))))

/-- Distinct punctures identify the twice-punctured sphere with the punctured complex plane. -/
noncomputable def pairComplementHomeomorphPuncturedComplex
    (p q : StandardSphere 2) (hpq : p ≠ q) :
    ({p, q}ᶜ : Set (StandardSphere 2)) ≃ₜ {z : ℂ // z ≠ 0} :=
  (pairComplementHomeomorphNestedPuncture p q).trans
    ((translatedPuncturedSphereChart p q hpq).subtype
      (translatedPuncturedSphereChart_ne_zero_iff p q hpq))

/-- Polar and logarithmic coordinates identify the punctured complex plane with the
infinite cylinder. -/
private noncomputable def puncturedComplexHomeomorphInfiniteCylinder :
    {z : ℂ // z ≠ 0} ≃ₜ Circle × ℝ :=
  Complex.polarHomeomorph.symm.trans
    ((Homeomorph.refl Circle).prodCongr Real.expOrderIso.toHomeomorph.symm)

/-- The punctured complex plane has infinite-cyclic fundamental group at every basepoint. -/
private lemma puncturedComplex_fundamentalGroupEquivInt
    (z : {z : ℂ // z ≠ 0}) :
    Nonempty (FundamentalGroup {z : ℂ // z ≠ 0} z ≃* Multiplicative ℤ) := by
  -- Transfer the standard infinite-cylinder computation through polar coordinates.
  let e := puncturedComplexHomeomorphInfiniteCylinder
  exact ⟨(e.fundamentalGroupMulEquiv z).trans
    (fundamentalGroup_infiniteCylinder (e z)).some⟩

/-- The fundamental group of a twice-punctured two-sphere is infinite cyclic. -/
lemma pairComplementFundamentalGroupEquivInt
    (p q : StandardSphere 2) (hpq : p ≠ q)
    (x : ({p, q}ᶜ : Set (StandardSphere 2))) :
    Nonempty (FundamentalGroup ({p, q}ᶜ : Set (StandardSphere 2)) x ≃*
      Multiplicative ℤ) := by
  -- First pass to the punctured complex plane, then use its cylinder model.
  let e := pairComplementHomeomorphPuncturedComplex p q hpq
  exact ⟨(e.fundamentalGroupMulEquiv x).trans
    (puncturedComplex_fundamentalGroupEquivInt (e x)).some⟩

end StandardSphere
