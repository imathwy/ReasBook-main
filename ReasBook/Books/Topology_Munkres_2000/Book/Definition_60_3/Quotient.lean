module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Topology.Constructions

public section

namespace RealProjectiveSpace

/-- Two points of the unit sphere `Sⁿ` are antipodal-equivalent when they are equal or
negatives. -/
def antipodal (n : ℕ)
    (x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : Prop :=
  y = x ∨ y = -x

/-- The antipodal relation has the explicit equal-or-negative description. -/
theorem antipodal_iff (n : ℕ)
    (x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    antipodal n x y ↔ y = x ∨ y = -x :=
  Iff.rfl

/-- The antipodal relation on the unit sphere `Sⁿ` is an equivalence relation. -/
theorem antipodalEquivalence (n : ℕ) : Equivalence (antipodal n) := by
  constructor
  · intro x
    exact Or.inl rfl
  · intro x y h
    rcases h with rfl | h
    · exact Or.inl rfl
    · subst y
      exact Or.inr (by simp)
  · intro x y z hxy hyz
    rcases hxy with rfl | hxy
    · exact hyz
    · rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inl (by simpa [hxy] using hyz)

/-- The setoid on the unit sphere `Sⁿ` identifying each point with its antipode. -/
def antipodalSetoid (n : ℕ) :
    Setoid (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) where
  r := antipodal n
  iseqv := antipodalEquivalence n

/-- The setoid relation holds exactly for equal or antipodal sphere points. -/
theorem setoid_rel_iff (n : ℕ)
    (x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    antipodalSetoid n x y ↔ y = x ∨ y = -x :=
  Iff.rfl

end RealProjectiveSpace

/-- Real projective `n`-space as the antipodal quotient of the unit sphere `Sⁿ`. -/
abbrev RealProjectiveSpace (n : ℕ) : Type :=
  Quotient (RealProjectiveSpace.antipodalSetoid n)

namespace RealProjectiveSpace

/-- The canonical map from the unit sphere `Sⁿ` to real projective `n`-space. -/
def quotientMap (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → RealProjectiveSpace n :=
  Quotient.mk (antipodalSetoid n)

/-- Two sphere points have the same image exactly when they are equal or antipodal. -/
theorem quotientMap_eq_iff (n : ℕ)
    (x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    quotientMap n x = quotientMap n y ↔ y = x ∨ y = -x := by
  rw [quotientMap, Quotient.eq]
  exact setoid_rel_iff n x y

/-- The quotient map identifies every sphere point with its antipode. -/
theorem quotientMap_neg (n : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    quotientMap n (-x) = quotientMap n x := by
  rw [quotientMap_eq_iff]
  exact Or.inr (by simp)

/-- The canonical map gives real projective `n`-space its quotient topology. -/
theorem quotientMap_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (quotientMap n) :=
  isQuotientMap_quotient_mk'

end RealProjectiveSpace

/-- The real projective plane is real projective `2`-space. -/
abbrev RealProjectivePlane : Type :=
  RealProjectiveSpace 2

namespace RealProjectivePlane

/-- The canonical quotient map from `S²` to the real projective plane. -/
abbrev quotientMap :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → RealProjectivePlane :=
  RealProjectiveSpace.quotientMap 2

/-- Two points of `S²` have the same image exactly when they are equal or antipodal. -/
theorem quotientMap_eq_iff
    (x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    quotientMap x = quotientMap y ↔ y = x ∨ y = -x :=
  RealProjectiveSpace.quotientMap_eq_iff 2 x y

/-- The quotient map identifies every point of `S²` with its antipode. -/
theorem quotientMap_neg (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    quotientMap (-x) = quotientMap x :=
  RealProjectiveSpace.quotientMap_neg 2 x

/-- The canonical map gives the real projective plane its quotient topology. -/
theorem quotientMap_isQuotientMap : Topology.IsQuotientMap quotientMap :=
  RealProjectiveSpace.quotientMap_isQuotientMap 2

end RealProjectivePlane
