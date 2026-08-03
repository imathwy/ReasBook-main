module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Constructions

public section

noncomputable section

namespace KleinBottle

/-- The fixed-point-free involution of the torus used to model the Klein bottle. -/
def involution (point : Circle × Circle) : Circle × Circle :=
  (-point.1, point.2⁻¹)

/-- Applying the standard Klein-bottle involution twice fixes every torus point. -/
theorem involution_involutive : Function.Involutive involution := by
  -- Negation and inversion are both involutions on the two circle coordinates.
  intro point
  apply Prod.ext
  · simp [involution]
  · simp [involution]

/-- Helper for Exercise 74.3: equality up to the Klein-bottle involution is an equivalence
relation on the torus. -/
private lemma identified_equivalence :
    Equivalence (fun x y : Circle × Circle ↦ y = x ∨ y = involution x) := by
  -- Reflexivity uses equality, while symmetry and transitivity use involutivity.
  constructor
  · intro x
    exact Or.inl rfl
  · intro x y hxy
    rcases hxy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (involution_involutive x).symm
  · intro x y z hxy hyz
    rcases hxy with rfl | rfl
    · exact hyz
    · rcases hyz with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (involution_involutive x)

/-- The orbit relation of the standard Klein-bottle involution on the torus. -/
def identified : Setoid (Circle × Circle) where
  r x y := y = x ∨ y = involution x
  iseqv := identified_equivalence

end KleinBottle

/-- The Klein bottle, modeled as the quotient of the torus by its standard free involution. -/
abbrev KleinBottle : Type :=
  Quotient KleinBottle.identified

namespace KleinBottle

/-- The canonical quotient map from the torus to the Klein bottle. -/
def quotientMap : C(Circle × Circle, KleinBottle) :=
  ⟨Quotient.mk'', continuous_quotient_mk'⟩

/-- The basepoint of the Klein bottle induced by the torus basepoint `(1, 1)`. -/
def basepoint : KleinBottle :=
  quotientMap (1, 1)

/-- The standard quotient map sends the torus basepoint to the Klein-bottle basepoint. -/
@[simp] theorem quotientMap_basepoint : quotientMap (1, 1) = basepoint := by
  -- The basepoint was defined as this image.
  rfl

/-- Two torus points have the same Klein-bottle image exactly when they are equal or exchanged by
the standard involution. -/
theorem quotientMap_eq_iff (x y : Circle × Circle) :
    quotientMap x = quotientMap y ↔ y = x ∨ y = involution x := by
  -- Equality in the quotient is exactly the defining setoid relation.
  constructor
  · intro hxy
    exact Quotient.exact hxy
  · intro hxy
    exact Quotient.sound hxy

end KleinBottle
