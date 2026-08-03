module

public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Topology.Covering.Quotient

public section

namespace RealProjectiveSpace

/-- Helper for Definition 60.4: the unit sphere whose antipodal quotient is real projective
`n`-space. -/
private abbrev UnitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Helper for Definition 60.4: `Bool` acts on the unit `n`-sphere by the identity and
antipode. -/
private noncomputable instance antipodalBoolVAdd (n : ℕ) : VAdd Bool (UnitSphere n) :=
  -- Encode the two deck transformations by the two Boolean values.
  ⟨fun b x ↦ if b = true then -x else x⟩

/-- Helper for Definition 60.4: the false Boolean fixes every point of the unit sphere. -/
@[simp]
private lemma false_vadd_unitSphere {n : ℕ} (x : UnitSphere n) : false +ᵥ x = x := by
  -- Select the identity branch of the antipodal action.
  rfl

/-- Helper for Definition 60.4: the true Boolean sends each sphere point to its antipode. -/
@[simp]
private lemma true_vadd_unitSphere {n : ℕ} (x : UnitSphere n) : true +ᵥ x = -x := by
  -- Select the negation branch of the antipodal action.
  rfl

/-- Helper for Definition 60.4: the antipodal Boolean action respects Boolean addition. -/
private lemma antipodalBool_add_vadd {n : ℕ} (b c : Bool) (x : UnitSphere n) :
    (b + c) +ᵥ x = b +ᵥ c +ᵥ x := by
  -- Verify the action law on the four pairs of Boolean elements.
  cases b
  · cases c
    · have hbc : false + false = false := by decide
      rw [hbc]
      simp only [false_vadd_unitSphere]
    · have hbc : false + true = true := by decide
      rw [hbc]
      simp only [false_vadd_unitSphere, true_vadd_unitSphere]
  · cases c
    · have hbc : true + false = true := by decide
      rw [hbc]
      simp only [false_vadd_unitSphere, true_vadd_unitSphere]
    · have hbc : true + true = false := by decide
      rw [hbc]
      simp only [false_vadd_unitSphere, true_vadd_unitSphere, neg_neg]

/-- Helper for Definition 60.4: Boolean zero acts trivially on the unit sphere. -/
private lemma antipodalBool_zero_vadd {n : ℕ} (x : UnitSphere n) :
    (0 : Bool) +ᵥ x = x := by
  -- Boolean zero is the false deck transformation.
  exact false_vadd_unitSphere x

/-- Helper for Definition 60.4: identity and antipode define an additive Boolean action on
the unit sphere. -/
private noncomputable instance antipodalBoolAction (n : ℕ) : AddAction Bool (UnitSphere n) :=
  -- Package the two action laws proved above.
  { add_vadd := antipodalBool_add_vadd
    zero_vadd := antipodalBool_zero_vadd }

/-- Helper for Definition 60.4: each Boolean deck transformation of the unit sphere is
continuous. -/
private lemma continuous_antipodalBoolVAdd {n : ℕ} (b : Bool) :
    Continuous fun x : UnitSphere n ↦ b +ᵥ x := by
  -- The two action maps are the identity and continuous negation.
  cases b
  · exact continuous_id
  · exact continuous_neg

/-- Helper for Definition 60.4: the antipodal Boolean action is continuous in the sphere
variable. -/
private instance antipodalBoolContinuousConstVAdd (n : ℕ) :
    ContinuousConstVAdd Bool (UnitSphere n) :=
  -- Supply the pointwise continuity theorem to the action API.
  ⟨continuous_antipodalBoolVAdd⟩

/-- Helper for Definition 60.4: each Boolean deck transformation of the unit sphere is
injective. -/
private lemma antipodalBool_left_cancel {n : ℕ} (b : Bool) (x y : UnitSphere n)
    (h : b +ᵥ x = b +ᵥ y) : x = y := by
  -- Identity is injective, and negation is injective after negating both sides.
  cases b
  · simpa using h
  · simpa using congrArg Neg.neg h

/-- Helper for Definition 60.4: distinct Boolean deck transformations never agree at a
point of the unit sphere. -/
private lemma antipodalBool_right_cancel {n : ℕ} (b c : Bool) (x : UnitSphere n)
    (h : b +ᵥ x = c +ᵥ x) : b = c := by
  -- The two unequal cases would identify a unit vector with its antipode.
  cases b
  · cases c
    · rfl
    · exact False.elim (ne_neg_of_mem_unit_sphere ℝ x h)
  · cases c
    · exact False.elim (ne_neg_of_mem_unit_sphere ℝ x h.symm)
    · rfl

/-- Helper for Definition 60.4: the antipodal Boolean action on the unit sphere is
cancellative. -/
private instance antipodalBoolIsCancelVAdd (n : ℕ) : IsCancelVAdd Bool (UnitSphere n) :=
  -- Package injectivity of each transformation and freeness of the action.
  { left_cancel' := antipodalBool_left_cancel
    right_cancel' := antipodalBool_right_cancel }

/-- Helper for Definition 60.4: Boolean orbits on the unit sphere are precisely antipodal
pairs. -/
private lemma mem_antipodalBoolOrbit_iff {n : ℕ} (x y : UnitSphere n) :
    x ∈ AddAction.orbit Bool y ↔ y = x ∨ y = -x := by
  -- Expand an orbit witness and inspect the two possible deck transformations.
  rw [AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨b, hb⟩
    cases b
    · left
      simpa using hb
    · right
      simpa using congrArg Neg.neg hb
  · rintro (rfl | rfl)
    · use false
      simp only [false_vadd_unitSphere]
    · use true
      simp only [true_vadd_unitSphere, neg_neg]

/-- Helper for Definition 60.4: the projective-space projection is the quotient covering
associated to the antipodal Boolean action. -/
private lemma quotientMap_isAddQuotientCoveringMap (n : ℕ) :
    IsAddQuotientCoveringMap (quotientMap n) Bool := by
  -- Identify the explicit antipodal equivalence classes with Boolean orbits.
  refine (quotientMap_isQuotientMap n).isAddQuotientCoveringMap_of_properlyDiscontinuousVAdd ?_
  intro x y
  exact (quotientMap_eq_iff n x y).trans (mem_antipodalBoolOrbit_iff x y).symm

/-- For positive `n`, the projection from `Sⁿ` to real projective `n`-space is a
covering map in mathlib's sense. -/
theorem quotientMap_isCoveringMap (n : ℕ) (hn : 0 < n) :
    IsCoveringMap (quotientMap n) := by
  -- Forget the deck-group structure from the stronger quotient-covering package.
  exact (quotientMap_isAddQuotientCoveringMap n).isCoveringMap

/-- The projection from `Sⁿ` to real projective `n`-space is surjective. -/
theorem quotientMap_surjective (n : ℕ) : Function.Surjective (quotientMap n) :=
  (quotientMap_isQuotientMap n).surjective

/-- For positive `n`, the projection from `Sⁿ` to real projective `n`-space is a
covering map in Munkres's surjective sense. -/
theorem quotientMap_isMunkresCoveringMap (n : ℕ) (hn : 0 < n) :
    IsCoveringMap (quotientMap n) ∧ Function.Surjective (quotientMap n) :=
  ⟨quotientMap_isCoveringMap n hn, quotientMap_surjective n⟩

end RealProjectiveSpace
