module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

universe u v

/-- The homomorphism from an infinite cyclic group determined by the image of a generator. -/
noncomputable def MonoidHom.ofInfiniteCyclicGenerator
    {G : Type u} {H : Type v} [Group G] [Group H] [Infinite G]
    (x : G) (h_generator : Subgroup.zpowers x = ⊤) (y : H) : G →* H :=
  (zpowersHom H y).comp (intEquivOfZPowersEqTop x h_generator).symm.toMonoidHom

/-- The homomorphism determined by `x ↦ y` sends the chosen generator to `y`. -/
@[simp]
theorem MonoidHom.ofInfiniteCyclicGenerator_apply_generator
    {G : Type u} {H : Type v} [Group G] [Group H] [Infinite G]
    (x : G) (h_generator : Subgroup.zpowers x = ⊤) (y : H) :
    MonoidHom.ofInfiniteCyclicGenerator x h_generator y x = y := by
  -- The inverse cyclic equivalence sends the generator to the integer one.
  simp [MonoidHom.ofInfiniteCyclicGenerator,
    intEquivOfZPowersEqTop_symm_self h_generator]

/-- The homomorphism determined by `x ↦ y` sends every integer power of `x` to the
corresponding integer power of `y`. -/
@[simp]
theorem MonoidHom.ofInfiniteCyclicGenerator_apply_zpow
    {G : Type u} {H : Type v} [Group G] [Group H] [Infinite G]
    (x : G) (h_generator : Subgroup.zpowers x = ⊤) (y : H) (n : ℤ) :
    MonoidHom.ofInfiniteCyclicGenerator x h_generator y (x ^ n) = y ^ n := by
  -- The inverse cyclic equivalence records the exponent of each power.
  simp [MonoidHom.ofInfiniteCyclicGenerator,
    mulintEquivOfZPowersEqTop_symm_apply_zpow h_generator n]
