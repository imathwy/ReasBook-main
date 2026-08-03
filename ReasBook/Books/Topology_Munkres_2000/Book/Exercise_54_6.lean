module

public import Topology_Munkres_2000.Book.Exercise_54_6.Power

public section

noncomputable section

/-- Helper for Exercise 54.6: the integer-power computation specializes directly to a
natural-number exponent. -/
lemma CircleMap.induced_zpower_nat (n : ℕ)
    (e : FundamentalGroup Circle 1 ≃* Multiplicative ℤ) :
    e.toMonoidHom.comp
        (FundamentalGroup.mapOfEq (CircleMap.zpower (n : ℤ))
          (CircleMap.zpower_one (n : ℤ))) =
      (zpowGroupHom (n : ℤ)).comp e.toMonoidHom := by
  -- Transport the natural exponent once to the canonical integer-power theorem.
  exact CircleMap.induced_zpower (n : ℤ) e

/-- Exercise 54.6 (1): under an identification of `π₁(S¹, 1)` with the infinite cyclic
group `Multiplicative ℤ`, the homomorphism induced by `z ↦ z ^ n` is multiplication by `n`. -/
theorem circlePower_induced (n : ℕ) (e : FundamentalGroup Circle 1 ≃* Multiplicative ℤ) :
    e.toMonoidHom.comp
        (FundamentalGroup.mapOfEq (CircleMap.zpower (n : ℤ))
          (CircleMap.zpower_one (n : ℤ))) =
      (zpowGroupHom (n : ℤ)).comp e.toMonoidHom :=
  -- Apply the natural-number interface to the canonical integer-power computation.
  CircleMap.induced_zpower_nat n e

/-- Exercise 54.6 (2): under an identification of `π₁(S¹, 1)` with the infinite cyclic
group `Multiplicative ℤ`, the homomorphism induced by `z ↦ 1 / z ^ n` is multiplication by `-n`. -/
theorem circleInversePower_induced (n : ℕ)
    (e : FundamentalGroup Circle 1 ≃* Multiplicative ℤ) :
    e.toMonoidHom.comp
        (FundamentalGroup.mapOfEq (CircleMap.zpower (-(n : ℤ)))
          (CircleMap.zpower_one (-(n : ℤ)))) =
      (zpowGroupHom (-(n : ℤ))).comp e.toMonoidHom :=
  -- A reciprocal power is the integer power with exponent `-n`.
  CircleMap.induced_zpower (-(n : ℤ)) e
