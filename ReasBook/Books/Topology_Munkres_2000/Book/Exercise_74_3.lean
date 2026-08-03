module

public import Topology_Munkres_2000.Book.Definition_53_6.Covering
public import Topology_Munkres_2000.Book.Exercise_54_7.Product
public import Topology_Munkres_2000.Book.Exercise_74_3.Presentation
import all Topology_Munkres_2000.Book.Exercise_74_3.Presentation
public import Topology_Munkres_2000.Book.Exercise_74_3.Quotient
import all Topology_Munkres_2000.Book.Exercise_74_3.Quotient
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Topology.Covering.Quotient

public section

noncomputable section

namespace KleinBottle

/-- Helper for Exercise 74.3: `Bool` acts on the torus by the identity and the defining
Klein-bottle involution. -/
private instance kleinBoolVAdd : VAdd Bool (Circle × Circle) :=
  ⟨fun c point ↦ if c = true then involution point else point⟩

/-- Helper for Exercise 74.3: the identity Boolean fixes every torus point. -/
@[simp]
private lemma false_vadd_torus (point : Circle × Circle) : false +ᵥ point = point := by
  -- Select the identity branch of the two-element action.
  rfl

/-- Helper for Exercise 74.3: the nonidentity Boolean acts by the Klein-bottle involution. -/
@[simp]
private lemma true_vadd_torus (point : Circle × Circle) : true +ᵥ point = involution point := by
  -- Select the involution branch of the two-element action.
  rfl

/-- Helper for Exercise 74.3: the Boolean action respects Boolean addition. -/
private lemma kleinBool_add_vadd (c d : Bool) (point : Circle × Circle) :
    (c + d) +ᵥ point = c +ᵥ d +ᵥ point := by
  -- Check the four deck-transformation products, using involutivity in the last case.
  cases c
  · cases d
    · have hsum : false + false = false := by decide
      rw [hsum]
      simp only [false_vadd_torus]
    · have hsum : false + true = true := by decide
      rw [hsum]
      simp only [false_vadd_torus, true_vadd_torus]
  · cases d
    · have hsum : true + false = true := by decide
      rw [hsum]
      simp only [false_vadd_torus, true_vadd_torus]
    · have htrue : true + true = false := by decide
      rw [htrue]
      simp only [false_vadd_torus, true_vadd_torus, involution_involutive point]

/-- Helper for Exercise 74.3: Boolean zero acts trivially on the torus. -/
private lemma kleinBool_zero_vadd (point : Circle × Circle) :
    (0 : Bool) +ᵥ point = point := by
  -- Boolean zero is the identity deck transformation.
  exact false_vadd_torus point

/-- Helper for Exercise 74.3: identity and involution form an additive Boolean action. -/
private instance kleinBoolAction : AddAction Bool (Circle × Circle) :=
  { add_vadd := kleinBool_add_vadd
    zero_vadd := kleinBool_zero_vadd }

/-- Helper for Exercise 74.3: every Boolean deck transformation of the torus is continuous. -/
private lemma continuous_kleinBoolVAdd (c : Bool) :
    Continuous fun point : Circle × Circle ↦ c +ᵥ point := by
  -- The two action maps are the identity and the coordinatewise involution.
  cases c
  · exact continuous_id
  · exact continuous_fst.neg.prodMk (continuous_inv.comp continuous_snd)

/-- Helper for Exercise 74.3: the Boolean action is continuous in the torus variable. -/
private instance kleinBoolContinuousConstVAdd : ContinuousConstVAdd Bool (Circle × Circle) :=
  ⟨continuous_kleinBoolVAdd⟩

/-- Helper for Exercise 74.3: each Boolean deck transformation is injective. -/
private lemma kleinBool_left_cancel (c : Bool) (x y : Circle × Circle)
    (h : c +ᵥ x = c +ᵥ y) : x = y := by
  -- The identity case is immediate; involutivity gives injectivity in the other case.
  cases c
  · simpa only [false_vadd_torus] using h
  · simpa only [true_vadd_torus] using involution_involutive.injective h

/-- Helper for Exercise 74.3: distinct Boolean deck transformations disagree everywhere. -/
private lemma kleinBool_right_cancel (c d : Bool) (point : Circle × Circle)
    (h : c +ᵥ point = d +ᵥ point) : c = d := by
  -- In the unequal cases, first coordinates would identify a circle point with its negative.
  cases c
  · cases d
    · rfl
    · have hfirst : point.1 = -point.1 := by
        simpa only [false_vadd_torus, true_vadd_torus, involution] using congrArg Prod.fst h
      exact False.elim (Circle.neg_ne_self point.1 hfirst.symm)
  · cases d
    · have hfirst : -point.1 = point.1 := by
        simpa only [false_vadd_torus, true_vadd_torus, involution] using congrArg Prod.fst h
      exact False.elim (Circle.neg_ne_self point.1 hfirst)
    · rfl

/-- Helper for Exercise 74.3: the Boolean deck action on the torus is cancellative. -/
private instance kleinBoolIsCancelVAdd : IsCancelVAdd Bool (Circle × Circle) :=
  { left_cancel' := kleinBool_left_cancel
    right_cancel' := kleinBool_right_cancel }

/-- Helper for Exercise 74.3: Boolean orbits are precisely the pairs identified in the
Klein-bottle quotient. -/
private lemma mem_kleinBoolOrbit_iff (x y : Circle × Circle) :
    x ∈ AddAction.orbit Bool y ↔ y = x ∨ y = involution x := by
  -- Expand an orbit witness and inspect the two possible deck transformations.
  rw [AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨c, hc⟩
    cases c
    · have hy : y = x := by
        simpa only [false_vadd_torus] using hc
      exact Or.inl hy
    · exact Or.inr (involution_involutive.injective
        (hc.trans (involution_involutive x).symm))
  · rintro (rfl | hy)
    · exact ⟨false, false_vadd_torus y⟩
    · have haction : true +ᵥ y = x := by
        simp only [true_vadd_torus]
        exact hy ▸ involution_involutive x
      exact ⟨true, haction⟩

/-- Helper for Exercise 74.3: the canonical map to the Klein bottle is a quotient map. -/
private lemma quotientMap_isQuotientMap :
    Topology.IsQuotientMap (quotientMap : Circle × Circle → KleinBottle) := by
  -- The underlying function is the canonical map of the defining setoid quotient.
  exact @isQuotientMap_quotient_mk' (Circle × Circle) _ identified

/-- Helper for Exercise 74.3: the torus quotient is the quotient covering associated to the
Boolean deck action. -/
private lemma quotientMap_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap quotientMap Bool := by
  -- Match the quotient fibers with Boolean orbits and invoke the finite free-action API.
  refine quotientMap_isQuotientMap.isAddQuotientCoveringMap_of_properlyDiscontinuousVAdd ?_
  intro x y
  exact (quotientMap_eq_iff x y).trans (mem_kleinBoolOrbit_iff x y).symm

/-- Helper for Exercise 74.3: an integer multiple of `2 * π` belongs to the circle period
subgroup. -/
private lemma circlePeriodMultiple_mem (n : ℤ) :
    n • (2 * Real.pi) ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
  -- Use the integer itself as the defining multiple witness.
  exact ⟨n, rfl⟩

/-- Helper for Exercise 74.3: the explicit element of the circle period subgroup associated
to an integer. -/
private def circlePeriodMultiple (n : ℤ) : AddSubgroup.zmultiples (2 * Real.pi) :=
  ⟨n • (2 * Real.pi), circlePeriodMultiple_mem n⟩

/-- Helper for Exercise 74.3: the zero integer gives the zero period. -/
private lemma circlePeriodMultiple_zero : circlePeriodMultiple 0 = 0 := by
  -- Compare underlying real numbers.
  apply Subtype.ext
  simp [circlePeriodMultiple]

/-- Helper for Exercise 74.3: period multiples preserve integer addition. -/
private lemma circlePeriodMultiple_add (m n : ℤ) :
    circlePeriodMultiple (m + n) = circlePeriodMultiple m + circlePeriodMultiple n := by
  -- Compare underlying real numbers and distribute scalar multiplication.
  apply Subtype.ext
  simp [circlePeriodMultiple, add_smul]

/-- Helper for Exercise 74.3: integers map additively to the period subgroup of `Circle.exp`. -/
private def circlePeriodHom : ℤ →+ AddSubgroup.zmultiples (2 * Real.pi) :=
  { toFun := circlePeriodMultiple
    map_zero' := circlePeriodMultiple_zero
    map_add' := circlePeriodMultiple_add }

/-- Helper for Exercise 74.3: the explicit integer-to-period homomorphism is bijective. -/
private lemma circlePeriodHom_bijective : Function.Bijective circlePeriodHom := by
  -- A nonzero period gives injectivity, while membership supplies every preimage.
  constructor
  · intro m n hmn
    apply (smul_left_injective ℤ (show (2 * Real.pi : ℝ) ≠ 0 by positivity))
    exact congrArg Subtype.val hmn
  · intro period
    obtain ⟨n, hn⟩ := period.property
    exact ⟨n, Subtype.ext hn⟩

/-- Helper for Exercise 74.3: the explicit additive equivalence between integers and circle
periods. -/
private def circlePeriodAddEquiv : ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi) :=
  AddEquiv.ofBijective circlePeriodHom circlePeriodHom_bijective

/-- Helper for Exercise 74.3: the circle exponential sends zero to the identity. -/
private lemma circleExp_zero_eq_one : Circle.exp 0 = 1 := by
  -- This is the zero-angle exponential computation.
  simp

/-- Helper for Exercise 74.3: explicit integer coordinates on the circle fundamental group
whose positive exponential loop has coordinate one. -/
private noncomputable def circleFundamentalCoordinates :
    FundamentalGroup Circle 1 ≃* Multiplicative ℤ :=
  (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
      ⟨0, circleExp_zero_eq_one⟩).trans
    (MulOpposite.opMulEquiv.symm.trans
      (AddEquiv.toMultiplicative circlePeriodAddEquiv).symm)

/-- Helper for Exercise 74.3: the two circle winding numbers give integer coordinates on the
fundamental group of the torus. -/
private noncomputable def torusFundamentalCoordinates :
    FundamentalGroup (Circle × Circle) (1, 1) ≃*
      Multiplicative ℤ × Multiplicative ℤ :=
  (FundamentalGroup.prodMulEquiv 1 1).trans
    (MulEquiv.prodCongr circleFundamentalCoordinates circleFundamentalCoordinates)

/-- Helper for Exercise 74.3: the homomorphism induced by the torus covering is injective. -/
private lemma quotientMap_induced_injective :
    Function.Injective
      (FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint) := by
  -- Reuse the general injectivity theorem for a covering-induced fundamental-group map.
  exact quotientMap_isAddQuotientCoveringMap.isCoveringMap.fundamentalGroupMap_injective
    quotientMap_basepoint

/-- Helper for Exercise 74.3: a Klein-bottle loop has trivial Boolean monodromy exactly when it
comes from a loop in the torus cover. -/
private lemma quotientMap_monodromyKernel :
    (quotientMap_isAddQuotientCoveringMap.isCoveringMap.monodromyPerm basepoint).ker =
      (FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint).range := by
  -- Apply the quotient-cover kernel theorem at the distinguished point of the fiber.
  exact quotientMap_isAddQuotientCoveringMap.ker_monodromyPerm
    ⟨(1, 1), quotientMap_basepoint⟩

/-- Helper for Exercise 74.3: trivial Boolean deck coordinate characterizes the image of the
torus fundamental group. -/
private lemma quotientMap_deckParityKernel :
    (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
        (⟨(1, 1), quotientMap_basepoint⟩ : quotientMap ⁻¹' {basepoint})).ker =
      (FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint).range := by
  -- Pass from the deck-coordinate kernel to the monodromy kernel already identified above.
  rw [quotientMap_isAddQuotientCoveringMap.ker_fundamentalGroupToMulOpposite,
    quotientMap_monodromyKernel]

/-- Helper for Exercise 74.3: every Boolean deck transformation is realized as monodromy of a
Klein-bottle loop. -/
private lemma quotientMap_deckParity_surjective :
    Function.Surjective
      (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
        (⟨(1, 1), quotientMap_basepoint⟩ : quotientMap ⁻¹' {basepoint})) := by
  -- Path connectedness of the torus makes the quotient-cover monodromy onto.
  exact quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite_surjective
    ⟨(1, 1), quotientMap_basepoint⟩

/-- Helper for Exercise 74.3: the exponential at angle `π` is the antipodal point of `1`. -/
private lemma circleExp_pi_eq_negOne : Circle.exp Real.pi = (-1 : Circle) := by
  -- Compare the underlying complex numbers and use Euler's formula at `π`.
  apply Subtype.ext
  rw [Circle.coe_exp, Complex.exp_pi_mul_I]
  rfl

/-- Helper for Exercise 74.3: the first-coordinate half-turn has the required continuity. -/
private lemma continuous_halfTorusPathParam :
    Continuous (fun t : unitInterval ↦
      (Circle.exp (Real.pi * (t : ℝ)), (1 : Circle))) := by
  -- Continuity follows coordinatewise from the circle exponential covering map.
  fun_prop

/-- Helper for Exercise 74.3: the first-coordinate half-turn starts at `(1, 1)`. -/
private lemma halfTorusPath_source :
    (Circle.exp (Real.pi * ((0 : unitInterval) : ℝ)), (1 : Circle)) =
      ((1, 1) : Circle × Circle) := by
  -- Evaluate the exponential at angle zero.
  simp

/-- Helper for Exercise 74.3: the first-coordinate half-turn ends at `(-1, 1)`. -/
private lemma halfTorusPath_target :
    (Circle.exp (Real.pi * ((1 : unitInterval) : ℝ)), (1 : Circle)) =
      ((-1, 1) : Circle × Circle) := by
  -- Evaluate the exponential at angle `π`.
  simp only [Set.Icc.coe_one, mul_one, circleExp_pi_eq_negOne]

/-- Helper for Exercise 74.3: the canonical path in the torus joining the two points of the
base fiber is a positive half-turn in the first circle. -/
private def halfTorusPath : Path ((1, 1) : Circle × Circle) (-1, 1) :=
  { toFun := fun t ↦ (Circle.exp (Real.pi * (t : ℝ)), 1)
    continuous_toFun := continuous_halfTorusPathParam
    source' := halfTorusPath_source
    target' := halfTorusPath_target }

/-- Helper for Exercise 74.3: the two endpoints of the torus half-turn have the same image in
the Klein bottle. -/
private lemma quotientMap_negOne_one :
    quotientMap ((-1, 1) : Circle × Circle) = basepoint := by
  -- The endpoint is exchanged with the basepoint by the defining involution.
  rw [← quotientMap_basepoint, quotientMap_eq_iff]
  apply Or.inr
  simp [involution]

/-- Helper for Exercise 74.3: the torus basepoint belongs to the distinguished covering
fiber. -/
private lemma torusBasepoint_mem_fiber :
    ((1, 1) : Circle × Circle) ∈ quotientMap ⁻¹' ({basepoint} : Set KleinBottle) := by
  -- Membership in the singleton fiber is the basepoint computation.
  exact quotientMap_basepoint

/-- Helper for Exercise 74.3: the antipodal endpoint belongs to the distinguished covering
fiber. -/
private lemma torusAntipode_mem_fiber :
    ((-1, 1) : Circle × Circle) ∈ quotientMap ⁻¹' ({basepoint} : Set KleinBottle) := by
  -- Membership in the singleton fiber is the endpoint quotient computation.
  exact quotientMap_negOne_one

/-- Helper for Exercise 74.3: the selected point in the base fiber of the torus cover. -/
private def torusBaseFiber : quotientMap ⁻¹' ({basepoint} : Set KleinBottle) :=
  ⟨(1, 1), torusBasepoint_mem_fiber⟩

/-- Helper for Exercise 74.3: the second point in the base fiber of the torus cover. -/
private def torusAntipodeFiber : quotientMap ⁻¹' ({basepoint} : Set KleinBottle) :=
  ⟨(-1, 1), torusAntipode_mem_fiber⟩

/-- Helper for Exercise 74.3: projecting the torus half-turn gives a based Klein-bottle loop. -/
private def halfTurnPath : Path basepoint basepoint :=
  (halfTorusPath.map quotientMap.continuous).cast
    quotientMap_basepoint.symm quotientMap_negOne_one.symm

/-- Helper for Exercise 74.3: the canonical half-turn element of the Klein-bottle fundamental
group. -/
private def halfTurn : FundamentalGroup KleinBottle basepoint :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk halfTurnPath)

/-- Helper for Exercise 74.3: monodromy of the canonical half-turn exchanges the two points of
the distinguished covering fiber. -/
private lemma halfTurn_monodromy :
    quotientMap_isAddQuotientCoveringMap.isCoveringMap.monodromy halfTurn
        torusBaseFiber = torusAntipodeFiber := by
  -- Use the explicit torus half-turn as the lift of the projected loop.
  apply quotientMap_isAddQuotientCoveringMap.isCoveringMap.monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk halfTorusPath)
  unfold halfTurn halfTurnPath torusBaseFiber torusAntipodeFiber
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- Helper for Exercise 74.3: the Boolean deck coordinate of the canonical half-turn is the
nonidentity element. -/
private lemma halfTurn_deckParity :
    quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
        torusBaseFiber halfTurn =
      MulOpposite.op (Multiplicative.ofAdd true) := by
  -- Characterize the deck coordinate by its action on the chosen point of the fiber.
  rw [quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff,
    halfTurn_monodromy]
  simp only [MulOpposite.unop_op, ofAdd_smul, torusBaseFiber,
    torusAntipodeFiber, true_vadd_torus, involution, inv_one]

/-- Helper for Exercise 74.3: the nonidentity Boolean deck coordinate has order two. -/
private lemma kleinDeckGenerator_orderOf :
    orderOf (MulOpposite.op (Multiplicative.ofAdd true)) = 2 := by
  -- Its square is the identity, while the generator itself is nontrivial.
  apply orderOf_eq_prime
  · decide
  · decide

/-- Helper for Exercise 74.3: a power of the half-turn has trivial deck coordinate exactly
when its exponent is even. -/
private lemma halfTurn_zpow_deckParity_eq_one_iff_even (k : ℤ) :
    quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
        torusBaseFiber (halfTurn ^ k) = 1 ↔ Even k := by
  -- Evaluate the deck homomorphism and use the order-two power criterion.
  rw [map_zpow, halfTurn_deckParity, ← orderOf_dvd_iff_zpow_eq_one,
    kleinDeckGenerator_orderOf]
  exact even_iff_two_dvd.symm

/-- Helper for Exercise 74.3: integer powers of inversion give the action defining the
Klein-bottle semidirect product. -/
private def kleinInversionAction : Multiplicative ℤ →* MulAut (Multiplicative ℤ) :=
  zpowersHom _ (MulEquiv.inv (Multiplicative ℤ))

/-- Helper for Exercise 74.3: the standard algebraic model of the Klein-bottle group is the
semidirect product in which the acting generator inverts the normal generator. -/
private abbrev KleinDeck :=
  Multiplicative ℤ ⋊[kleinInversionAction] Multiplicative ℤ

/-- Helper for Exercise 74.3: one unit in the acting factor acts by inversion. -/
private lemma kleinInversionAction_generator (n : Multiplicative ℤ) :
    kleinInversionAction (Multiplicative.ofAdd 1) n = n⁻¹ := by
  -- Evaluate the power homomorphism at its distinguished generator.
  simp [kleinInversionAction]

/-- Helper for Exercise 74.3: the defining relator says that `a` conjugates `b` to its
inverse. -/
private lemma presentation_conjugates_b : a * b * a⁻¹ = b⁻¹ := by
  -- Separate the final `b` from the defining four-letter relator.
  have hrel := PresentedGroup.one_of_mem (Set.mem_singleton relator)
  change a * b * a⁻¹ * b = 1 at hrel
  exact (mul_eq_one_iff_eq_inv.mp hrel)

/-- Helper for Exercise 74.3: the two presentation generators satisfy the relator in the
inversion semidirect product. -/
private lemma deckGeneratorsRespectRelator (word : FreeGroup (Fin 2))
    (hword : word ∈ ({relator} : Set (FreeGroup (Fin 2)))) :
    FreeGroup.lift
        (fun i ↦ if i = 0 then
          (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) : KleinDeck)
        else SemidirectProduct.inl (Multiplicative.ofAdd (1 : ℤ))) word = 1 := by
  -- The singleton hypothesis reduces the calculation to the displayed relator.
  rw [Set.mem_singleton_iff] at hword
  subst word
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simp only [relator, map_mul, map_inv, FreeGroup.lift_apply_of,
    if_pos, if_neg hone]
  -- Conjugation by the acting generator is inversion on the normal factor.
  rw [← map_inv]
  rw [← SemidirectProduct.inl_aut, kleinInversionAction_generator]
  simp

/-- Helper for Exercise 74.3: the presented group maps to its inversion semidirect-product
model by the two canonical generators. -/
private def presentationToKleinDeck : Presentation →* KleinDeck :=
  PresentedGroup.toGroup deckGeneratorsRespectRelator

/-- Helper for Exercise 74.3: the first presentation generator is the acting generator in the
semidirect-product model. -/
private lemma presentationToKleinDeck_a :
    presentationToKleinDeck a =
      SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) := by
  -- Evaluate the presented-group universal map at generator zero.
  simp [presentationToKleinDeck, a]

/-- Helper for Exercise 74.3: the second presentation generator is the normal generator in the
semidirect-product model. -/
private lemma presentationToKleinDeck_b :
    presentationToKleinDeck b =
      SemidirectProduct.inl (Multiplicative.ofAdd (1 : ℤ)) := by
  -- Evaluate the presented-group universal map at generator one.
  simp [presentationToKleinDeck, b]

/-- Helper for Exercise 74.3: an intertwining homomorphism also intertwines every integer power
of two automorphisms. -/
private lemma map_mulAut_zpow_of_intertwines {N H : Type*} [Group N] [Group H]
    (f : N →* H) (u : MulAut N) (v : MulAut H)
    (h : ∀ x, f (u x) = v (f x)) (k : ℤ) (x : N) :
    f ((u ^ k) x) = (v ^ k) (f x) := by
  -- The inverse step follows by applying the target automorphism once.
  have hInv (y : N) : f (u⁻¹ y) = v⁻¹ (f y) := by
    apply v.injective
    simpa using (h (u⁻¹ y)).symm
  -- Integer induction propagates the intertwining equation in both directions.
  induction k using Int.inductionOn' (b := 0) generalizing x with
  | zero => simp
  | succ k hk ih =>
      calc
        f ((u ^ (k + 1)) x) = f ((u ^ k) (u x)) := by
          rw [zpow_add_one, MulAut.mul_apply]
        _ = (v ^ k) (f (u x)) := ih (u x)
        _ = (v ^ k) (v (f x)) := congrArg (v ^ k) (h x)
        _ = (v ^ (k + 1)) (f x) := by
          rw [zpow_add_one, MulAut.mul_apply]
  | pred k hk ih =>
      calc
        f ((u ^ (k - 1)) x) = f ((u ^ k) (u⁻¹ x)) := by
          rw [zpow_sub_one, MulAut.mul_apply]
        _ = (v ^ k) (f (u⁻¹ x)) := ih (u⁻¹ x)
        _ = (v ^ k) (v⁻¹ (f x)) := congrArg (v ^ k) (hInv x)
        _ = (v ^ (k - 1)) (f x) := by
          rw [zpow_sub_one, MulAut.mul_apply]

/-- Helper for Exercise 74.3: powers of `b` form the normal cyclic factor in the
presentation. -/
private def presentationNormalGenerator : Multiplicative ℤ →* Presentation :=
  zpowersHom _ b

/-- Helper for Exercise 74.3: powers of `a` form the acting cyclic factor in the
presentation. -/
private def presentationActingGenerator : Multiplicative ℤ →* Presentation :=
  zpowersHom _ a

/-- Helper for Exercise 74.3: inversion of the normal integer coordinate corresponds to
conjugation by `a`. -/
private lemma presentationGeneratorIntertwines (n : Multiplicative ℤ) :
    presentationNormalGenerator ((MulEquiv.inv (Multiplicative ℤ)) n) =
      MulAut.conj a (presentationNormalGenerator n) := by
  -- Both sides are homomorphisms from the infinite cyclic group, so check its generator.
  suffices hhom :
      presentationNormalGenerator.comp
          (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom =
        (MulAut.conj a).toMonoidHom.comp presentationNormalGenerator by
    exact DFunLike.congr_fun hhom n
  apply MonoidHom.ext_mint
  simpa [presentationNormalGenerator] using presentation_conjugates_b.symm

/-- Helper for Exercise 74.3: the cyclic-factor maps into the presentation satisfy the
compatibility required by the inversion semidirect product. -/
private lemma presentationCyclicFactorsCompatible (g : Multiplicative ℤ) :
    presentationNormalGenerator.comp (kleinInversionAction g).toMonoidHom =
      (MulAut.conj (presentationActingGenerator g)).toMonoidHom.comp
        presentationNormalGenerator := by
  -- Write the acting coordinate as an integer power and use the intertwining lemma.
  rw [← ofAdd_toAdd g]
  apply MonoidHom.ext
  intro n
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [kleinInversionAction, zpowersHom_apply,
    map_mulAut_zpow_of_intertwines presentationNormalGenerator
      (MulEquiv.inv (Multiplicative ℤ)) (MulAut.conj a)
      presentationGeneratorIntertwines]
  simp only [presentationActingGenerator, zpowersHom_apply]
  rw [← map_zpow]

/-- Helper for Exercise 74.3: the inversion semidirect product maps back to the presentation
through the two cyclic generators. -/
private def kleinDeckToPresentation : KleinDeck →* Presentation :=
  SemidirectProduct.lift presentationNormalGenerator presentationActingGenerator
    presentationCyclicFactorsCompatible

/-- Helper for Exercise 74.3: mapping the presentation to the semidirect product and back is
the identity. -/
private lemma kleinDeckToPresentation_comp_presentationToKleinDeck :
    kleinDeckToPresentation.comp presentationToKleinDeck = MonoidHom.id Presentation := by
  -- Presented-group extensionality reduces the composite to its two generators.
  apply PresentedGroup.ext
  intro i
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · rw [MonoidHom.comp_apply, MonoidHom.id_apply]
    change kleinDeckToPresentation (presentationToKleinDeck a) = a
    rw [presentationToKleinDeck_a]
    simp [kleinDeckToPresentation, presentationActingGenerator, a]
  · rw [MonoidHom.comp_apply, MonoidHom.id_apply]
    change kleinDeckToPresentation (presentationToKleinDeck b) = b
    rw [presentationToKleinDeck_b]
    simp [kleinDeckToPresentation, presentationNormalGenerator, b]

/-- Helper for Exercise 74.3: mapping the semidirect product to the presentation and back is
the identity. -/
private lemma presentationToKleinDeck_comp_kleinDeckToPresentation :
    presentationToKleinDeck.comp kleinDeckToPresentation = MonoidHom.id KleinDeck := by
  -- A homomorphism out of a semidirect product is determined on both cyclic factors.
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext_mint
    simp [kleinDeckToPresentation, presentationNormalGenerator,
      presentationToKleinDeck_b]
  · apply MonoidHom.ext_mint
    simp [kleinDeckToPresentation, presentationActingGenerator,
      presentationToKleinDeck_a]

/-- Helper for Exercise 74.3: the standard presentation is canonically equivalent to the
inversion semidirect-product model. -/
private def presentationMulEquivKleinDeck : Presentation ≃* KleinDeck :=
  MonoidHom.toMulEquiv presentationToKleinDeck kleinDeckToPresentation
    kleinDeckToPresentation_comp_presentationToKleinDeck
    presentationToKleinDeck_comp_kleinDeckToPresentation

/-- Helper for Exercise 74.3: the positive first-circle generator in the chosen torus
coordinates. -/
private def torusHorizontalGenerator : FundamentalGroup (Circle × Circle) (1, 1) :=
  torusFundamentalCoordinates.symm (Multiplicative.ofAdd 1, 1)

/-- Helper for Exercise 74.3: the positive second-circle generator in the chosen torus
coordinates. -/
private def torusVerticalGenerator : FundamentalGroup (Circle × Circle) (1, 1) :=
  torusFundamentalCoordinates.symm (1, Multiplicative.ofAdd 1)

/-- Helper for Exercise 74.3: every torus loop is the product of the powers of its horizontal
and vertical coordinate generators. -/
private lemma torus_eq_horizontal_zpow_mul_vertical_zpow
    (x : FundamentalGroup (Circle × Circle) (1, 1)) :
    x = torusHorizontalGenerator ^ (torusFundamentalCoordinates x).1.toAdd *
      torusVerticalGenerator ^ (torusFundamentalCoordinates x).2.toAdd := by
  -- Apply the coordinate equivalence and calculate in the product of two infinite cyclic groups.
  apply torusFundamentalCoordinates.injective
  rw [map_mul, map_zpow, map_zpow]
  simp only [torusHorizontalGenerator, torusVerticalGenerator,
    torusFundamentalCoordinates.apply_symm_apply]
  apply Prod.ext
  · have hhorizontal :
        (((Multiplicative.ofAdd (1 : ℤ), (1 : Multiplicative ℤ)) ^
          (torusFundamentalCoordinates x).1.toAdd).1) =
            Multiplicative.ofAdd 1 ^ (torusFundamentalCoordinates x).1.toAdd :=
      map_zpow (MonoidHom.fst (Multiplicative ℤ) (Multiplicative ℤ)) _ _
    have hvertical :
        ((((1 : Multiplicative ℤ), Multiplicative.ofAdd (1 : ℤ)) ^
          (torusFundamentalCoordinates x).2.toAdd).1) =
            1 ^ (torusFundamentalCoordinates x).2.toAdd :=
      map_zpow (MonoidHom.fst (Multiplicative ℤ) (Multiplicative ℤ)) _ _
    rw [Prod.fst_mul, hhorizontal, hvertical]
    simp only [one_zpow, mul_one, ← ofAdd_zsmul, zsmul_eq_mul, one_mul,
      ofAdd_toAdd]
    exact (ofAdd_toAdd _).symm
  · have hhorizontal :
        (((Multiplicative.ofAdd (1 : ℤ), (1 : Multiplicative ℤ)) ^
          (torusFundamentalCoordinates x).1.toAdd).2) =
            1 ^ (torusFundamentalCoordinates x).1.toAdd :=
      map_zpow (MonoidHom.snd (Multiplicative ℤ) (Multiplicative ℤ)) _ _
    have hvertical :
        ((((1 : Multiplicative ℤ), Multiplicative.ofAdd (1 : ℤ)) ^
          (torusFundamentalCoordinates x).2.toAdd).2) =
            Multiplicative.ofAdd 1 ^ (torusFundamentalCoordinates x).2.toAdd :=
      map_zpow (MonoidHom.snd (Multiplicative ℤ) (Multiplicative ℤ)) _ _
    rw [Prod.snd_mul, hhorizontal, hvertical]
    simp only [one_zpow, one_mul, ← ofAdd_zsmul, zsmul_eq_mul, one_mul,
      ofAdd_toAdd]
    rw [mul_one]
    exact (ofAdd_toAdd _).symm

/-- Helper for Exercise 74.3: the horizontal and vertical coordinate generators of the torus
fundamental group commute. -/
private lemma torusGenerators_commute :
    Commute torusHorizontalGenerator torusVerticalGenerator := by
  -- Integer-pair coordinates reduce the commutator equation to componentwise multiplication.
  apply torusFundamentalCoordinates.injective
  rw [map_mul, map_mul]
  simp only [torusHorizontalGenerator, torusVerticalGenerator,
    torusFundamentalCoordinates.apply_symm_apply]
  rfl

/-- Helper for Exercise 74.3: the standard positive circle loop is continuous. -/
private lemma continuous_horizontalCircleLoopParam :
    Continuous (fun t : unitInterval ↦ Circle.exp (2 * Real.pi * (t : ℝ))) := by
  -- The loop is the exponential of a linear real parameter.
  fun_prop

/-- Helper for Exercise 74.3: the standard positive circle loop starts at `1`. -/
private lemma horizontalCircleLoop_source :
    Circle.exp (2 * Real.pi * ((0 : unitInterval) : ℝ)) = 1 := by
  -- Evaluate the exponential at zero.
  simp

/-- Helper for Exercise 74.3: the standard positive circle loop ends at `1`. -/
private lemma horizontalCircleLoop_target :
    Circle.exp (2 * Real.pi * ((1 : unitInterval) : ℝ)) = 1 := by
  -- Evaluate the exponential after one full turn.
  simp

/-- Helper for Exercise 74.3: the explicit positive one-turn loop in the circle. -/
private def horizontalCircleLoop : Path (1 : Circle) 1 :=
  { toFun := fun t ↦ Circle.exp (2 * Real.pi * (t : ℝ))
    continuous_toFun := continuous_horizontalCircleLoopParam
    source' := horizontalCircleLoop_source
    target' := horizontalCircleLoop_target }

/-- Helper for Exercise 74.3: the real lift of the positive circle loop is continuous. -/
private lemma continuous_horizontalRealLiftParam :
    Continuous (fun t : unitInterval ↦ 2 * Real.pi * (t : ℝ)) := by
  -- The lifted angle varies linearly from zero to `2 * π`.
  fun_prop

/-- Helper for Exercise 74.3: the real lift starts at zero. -/
private lemma horizontalRealLift_source :
    2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by
  -- Evaluate the linear lift at the initial endpoint.
  simp

/-- Helper for Exercise 74.3: the real lift ends at one full period. -/
private lemma horizontalRealLift_target :
    2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by
  -- Evaluate the linear lift at the terminal endpoint.
  simp

/-- Helper for Exercise 74.3: the standard positive circle loop lifts from `0` to `2 * π`. -/
private def horizontalRealLift : Path (0 : ℝ) (2 * Real.pi) :=
  { toFun := fun t ↦ 2 * Real.pi * (t : ℝ)
    continuous_toFun := continuous_horizontalRealLiftParam
    source' := horizontalRealLift_source
    target' := horizontalRealLift_target }

/-- Helper for Exercise 74.3: the explicit positive circle loop has integer coordinate one. -/
private lemma horizontalCircleLoop_coordinate :
    circleFundamentalCoordinates
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk horizontalCircleLoop)) =
        Multiplicative.ofAdd 1 := by
  let q : FundamentalGroup Circle 1 :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk horizontalCircleLoop)
  let e₀ : Circle.exp ⁻¹' ({1} : Set Circle) := ⟨0, circleExp_zero_eq_one⟩
  have circleExp_twoPi_eq_one : Circle.exp (2 * Real.pi) = 1 := by
    -- One full period maps back to the identity.
    simp
  let e₁ : Circle.exp ⁻¹' ({1} : Set Circle) :=
    ⟨2 * Real.pi, circleExp_twoPi_eq_one⟩
  -- The displayed real path is the canonical lift, so monodromy ends at `2 * π`.
  have hmonodromy : Circle.isCoveringMap_exp.monodromy q e₀ = e₁ := by
    apply Circle.isCoveringMap_exp.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk horizontalRealLift)
    rw [← Path.Homotopic.Quotient.mk_map]
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    rfl
  have hperiodMem : 2 * Real.pi ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
    have hmultiple : (1 : ℤ) • (2 * Real.pi) = 2 * Real.pi := by
      simp
    exact ⟨1, hmultiple⟩
  let period : AddSubgroup.zmultiples (2 * Real.pi) :=
    ⟨2 * Real.pi, hperiodMem⟩
  -- Translate the lifted endpoint into the quotient-cover coordinate.
  have hcoveringCoordinate :
      Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e₀ q =
        MulOpposite.op (Multiplicative.ofAdd period) := by
    apply Circle.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
    change (period : ℝ) + (e₀ : ℝ) =
      (Circle.isCoveringMap_exp.monodromy q e₀ : ℝ)
    rw [hmonodromy]
    simp [period, e₀, e₁]
  have hperiodCoordinate : circlePeriodAddEquiv.symm period = 1 := by
    apply circlePeriodAddEquiv.injective
    rw [circlePeriodAddEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [circlePeriodAddEquiv, circlePeriodHom, circlePeriodMultiple, period]
  -- Unfold only the public equivalence chain and apply the period computation.
  change circleFundamentalCoordinates q = Multiplicative.ofAdd 1
  rw [circleFundamentalCoordinates, MulEquiv.trans_apply, MulEquiv.trans_apply,
    hcoveringCoordinate]
  simpa only [hperiodCoordinate]

/-- Helper for Exercise 74.3: the explicit horizontal torus loop keeps the second coordinate
constant. -/
private def horizontalTorusLoop : Path ((1, 1) : Circle × Circle) (1, 1) :=
  horizontalCircleLoop.prod (Path.refl 1)

/-- Helper for Exercise 74.3: the explicit horizontal torus loop represents the chosen
horizontal generator. -/
private lemma horizontalTorusLoop_eq_generator :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk horizontalTorusLoop) =
      torusHorizontalGenerator := by
  -- Product fundamental-group coordinates reduce the claim to the circle computation above.
  apply torusFundamentalCoordinates.injective
  rw [torusHorizontalGenerator, torusFundamentalCoordinates.apply_symm_apply]
  rw [torusFundamentalCoordinates, MulEquiv.trans_apply,
    FundamentalGroup.prodMulEquiv_apply]
  change
    (circleFundamentalCoordinates
        (FundamentalGroup.fromPath
          (Path.Homotopic.projLeft (Path.Homotopic.Quotient.mk horizontalTorusLoop))),
      circleFundamentalCoordinates
        (FundamentalGroup.fromPath
          (Path.Homotopic.projRight (Path.Homotopic.Quotient.mk horizontalTorusLoop)))) =
      (Multiplicative.ofAdd 1, 1)
  have hprod : Path.Homotopic.Quotient.mk horizontalTorusLoop =
      Path.Homotopic.prod (Path.Homotopic.Quotient.mk horizontalCircleLoop)
        (Path.Homotopic.Quotient.mk (Path.refl 1)) := by
    rfl
  rw [hprod, Path.Homotopic.projLeft_prod, Path.Homotopic.projRight_prod,
    horizontalCircleLoop_coordinate]
  rw [Path.Homotopic.Quotient.mk_refl]
  have hone : FundamentalGroup.fromPath (Path.Homotopic.Quotient.refl (1 : Circle)) = 1 := rfl
  rw [hone, map_one circleFundamentalCoordinates]

/-- Helper for Exercise 74.3: the explicit vertical torus loop keeps the first coordinate
constant. -/
private def verticalTorusLoop : Path ((1, 1) : Circle × Circle) (1, 1) :=
  (Path.refl 1).prod horizontalCircleLoop

/-- Helper for Exercise 74.3: the explicit vertical torus loop represents the chosen vertical
generator. -/
private lemma verticalTorusLoop_eq_generator :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk verticalTorusLoop) =
      torusVerticalGenerator := by
  -- Product fundamental-group coordinates reduce the claim to the same circle computation.
  apply torusFundamentalCoordinates.injective
  rw [torusVerticalGenerator, torusFundamentalCoordinates.apply_symm_apply]
  rw [torusFundamentalCoordinates, MulEquiv.trans_apply,
    FundamentalGroup.prodMulEquiv_apply]
  change
    (circleFundamentalCoordinates
        (FundamentalGroup.fromPath
          (Path.Homotopic.projLeft (Path.Homotopic.Quotient.mk verticalTorusLoop))),
      circleFundamentalCoordinates
        (FundamentalGroup.fromPath
          (Path.Homotopic.projRight (Path.Homotopic.Quotient.mk verticalTorusLoop)))) =
      (1, Multiplicative.ofAdd 1)
  have hprod : Path.Homotopic.Quotient.mk verticalTorusLoop =
      Path.Homotopic.prod (Path.Homotopic.Quotient.mk (Path.refl 1))
        (Path.Homotopic.Quotient.mk horizontalCircleLoop) := by
    rfl
  rw [hprod, Path.Homotopic.projLeft_prod, Path.Homotopic.projRight_prod,
    horizontalCircleLoop_coordinate]
  rw [Path.Homotopic.Quotient.mk_refl]
  have hone : FundamentalGroup.fromPath (Path.Homotopic.Quotient.refl (1 : Circle)) = 1 := rfl
  rw [hone, map_one circleFundamentalCoordinates]

/-- Helper for Exercise 74.3: the images of the two torus generators under the covering map. -/
private def horizontalImage : FundamentalGroup KleinBottle basepoint :=
  FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint torusHorizontalGenerator

/-- Helper for Exercise 74.3: the vertical generator in the Klein-bottle fundamental group. -/
private def verticalImage : FundamentalGroup KleinBottle basepoint :=
  FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint torusVerticalGenerator

/-- Helper for Exercise 74.3: the explicit projected vertical loop based at the Klein-bottle
basepoint. -/
private def projectedVerticalPath : Path basepoint basepoint :=
  (verticalTorusLoop.map quotientMap.continuous).cast
    quotientMap_basepoint.symm quotientMap_basepoint.symm

/-- Helper for Exercise 74.3: the explicit projected vertical loop represents `verticalImage`. -/
private lemma projectedVerticalPath_class_eq_verticalImage :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk projectedVerticalPath) =
      verticalImage := by
  -- Rewrite the chosen torus generator by its explicit representative before applying the map.
  rw [verticalImage, ← verticalTorusLoop_eq_generator,
    FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  rfl

/-- Helper for Exercise 74.3: the vertical circle maps into the Klein bottle at first coordinate
`1`. -/
private def verticalForwardMap : C(Circle, KleinBottle) :=
  ⟨fun z ↦ quotientMap (1, z),
    quotientMap.continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- Helper for Exercise 74.3: the inverse vertical circle maps into the Klein bottle at first
coordinate `1`. -/
private def verticalReverseMap : C(Circle, KleinBottle) :=
  ⟨fun z ↦ quotientMap (1, z⁻¹),
    quotientMap.continuous.comp (continuous_const.prodMk continuous_inv)⟩

/-- Helper for Exercise 74.3: the forward vertical circle map preserves the chosen basepoint. -/
private lemma verticalForwardMap_one : verticalForwardMap 1 = basepoint := by
  -- Unfold the forward map at the identity of the circle.
  rfl

/-- Helper for Exercise 74.3: the reverse vertical circle map preserves the chosen basepoint. -/
private lemma verticalReverseMap_one : verticalReverseMap 1 = basepoint := by
  -- Inversion fixes the identity of the circle.
  simp [verticalReverseMap]

/-- Helper for Exercise 74.3: the square interpolating between the vertical circle map and its
inverse is continuous. -/
private lemma continuous_verticalGeneratorHomotopyParam :
    Continuous (fun point : unitInterval × Circle ↦
      quotientMap (Circle.exp (Real.pi * (point.1 : ℝ)), point.2)) := by
  -- Continuity follows from the exponential path and the quotient map.
  fun_prop

/-- Helper for Exercise 74.3: the vertical-generator square starts at the forward circle map. -/
private lemma verticalGeneratorHomotopy_zero (z : Circle) :
    quotientMap (Circle.exp (Real.pi * ((0 : unitInterval) : ℝ)), z) =
      verticalForwardMap z := by
  -- At parameter zero the first coordinate is `1`.
  simp [verticalForwardMap]

/-- Helper for Exercise 74.3: the vertical-generator square ends at the inverse circle map in
the quotient. -/
private lemma verticalGeneratorHomotopy_one (z : Circle) :
    quotientMap (Circle.exp (Real.pi * ((1 : unitInterval) : ℝ)), z) =
      verticalReverseMap z := by
  -- At parameter one, the quotient involution changes `(-1, z)` into `(1, z⁻¹)`.
  rw [Set.Icc.coe_one, mul_one]
  unfold verticalReverseMap
  change quotientMap (Circle.exp Real.pi, z) = quotientMap (1, z⁻¹)
  rw [circleExp_pi_eq_negOne, quotientMap_eq_iff]
  apply Or.inr
  simp [involution]

/-- Helper for Exercise 74.3: moving the first circle through a half-turn homotopes the vertical
circle map to its inverse. -/
private def verticalGeneratorHomotopy :
    verticalForwardMap.Homotopy verticalReverseMap :=
  { toFun := fun point ↦
      quotientMap (Circle.exp (Real.pi * (point.1 : ℝ)), point.2)
    continuous_toFun := continuous_verticalGeneratorHomotopyParam
    map_zero_left := verticalGeneratorHomotopy_zero
    map_one_left := verticalGeneratorHomotopy_one }

/-- Helper for Exercise 74.3: the basepoint trace of the vertical-generator square is the
canonical half-turn. -/
private lemma verticalGeneratorHomotopy_evalAt_one :
    (verticalGeneratorHomotopy.evalAt 1).cast
        verticalForwardMap_one.symm verticalReverseMap_one.symm = halfTurnPath := by
  -- Both paths use the same projected half-turn formula.
  ext t
  rfl

/-- Helper for Exercise 74.3: the forward edge of the vertical-generator square is the explicit
projected vertical loop. -/
private lemma horizontalCircleLoop_map_verticalForwardMap :
    (horizontalCircleLoop.map verticalForwardMap.continuous).cast
        verticalForwardMap_one.symm verticalForwardMap_one.symm = projectedVerticalPath := by
  -- Both paths project `(1, exp (2 * π * t))`.
  ext t
  rfl

/-- Helper for Exercise 74.3: the reverse edge of the vertical-generator square is the inverse
of the explicit projected vertical loop. -/
private lemma horizontalCircleLoop_map_verticalReverseMap :
    (horizontalCircleLoop.map verticalReverseMap.continuous).cast
        verticalReverseMap_one.symm verticalReverseMap_one.symm =
      projectedVerticalPath.symm := by
  -- Inversion changes the positive exponential loop into its reversed parametrization.
  ext t
  apply congrArg quotientMap
  apply Prod.ext
  · rfl
  · change (Circle.exp (2 * Real.pi * (t : ℝ)))⁻¹ =
      Circle.exp (2 * Real.pi * (1 - (t : ℝ)))
    rw [← Circle.exp_neg]
    have hangle : 2 * Real.pi * (1 - (t : ℝ)) =
        -(2 * Real.pi * (t : ℝ)) + 2 * Real.pi := by
      ring
    rw [hangle, Circle.exp_add_two_pi]

/-- Helper for Exercise 74.3: the naturality square gives the commutation relation between the
half-turn and the vertical loop. -/
private lemma halfTurn_mul_verticalImage :
    halfTurn * verticalImage = verticalImage⁻¹ * halfTurn := by
  -- Descend the square homotopy after identifying its four boundary paths.
  have hsquare :=
    Path.Homotopic.map_trans_evalAt verticalGeneratorHomotopy horizontalCircleLoop
  have hsquareBased := Path.Homotopic.pathCast hsquare
    verticalForwardMap_one.symm verticalReverseMap_one.symm
  rw [Path.cast_trans
      (horizontalCircleLoop.map verticalForwardMap.continuous)
      (verticalGeneratorHomotopy.evalAt 1)
      verticalForwardMap_one.symm verticalForwardMap_one.symm
      verticalReverseMap_one.symm,
    Path.cast_trans
      (verticalGeneratorHomotopy.evalAt 1)
      (horizontalCircleLoop.map verticalReverseMap.continuous)
      verticalForwardMap_one.symm verticalReverseMap_one.symm
      verticalReverseMap_one.symm] at hsquareBased
  rw [horizontalCircleLoop_map_verticalForwardMap,
    horizontalCircleLoop_map_verticalReverseMap,
    verticalGeneratorHomotopy_evalAt_one] at hsquareBased
  have hquotient :
      FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (projectedVerticalPath.trans halfTurnPath)) =
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (halfTurnPath.trans projectedVerticalPath.symm)) :=
    Path.Homotopic.Quotient.eq.mpr hsquareBased
  calc
    halfTurn * verticalImage =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk halfTurnPath) *
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk projectedVerticalPath) := by
      rw [projectedVerticalPath_class_eq_verticalImage]
      rfl
    _ = FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (projectedVerticalPath.trans halfTurnPath)) := by
      rw [FundamentalGroup.mul_def, ← Path.Homotopic.Quotient.mk_trans]
    _ = FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (halfTurnPath.trans projectedVerticalPath.symm)) :=
      hquotient
    _ = (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk projectedVerticalPath))⁻¹ *
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk halfTurnPath) := by
      rw [FundamentalGroup.mul_def, FundamentalGroup.inv_def,
        ← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans]
    _ = verticalImage⁻¹ * halfTurn := by
      rw [projectedVerticalPath_class_eq_verticalImage]
      rfl

/-- Helper for Exercise 74.3: the projected full horizontal turn is the concatenation of two
projected half-turns. -/
private lemma horizontalTorusLoop_map_eq_halfTurnPath_trans :
    (horizontalTorusLoop.map quotientMap.continuous).cast
        quotientMap_basepoint.symm quotientMap_basepoint.symm =
      halfTurnPath.trans halfTurnPath := by
  -- Compare the two projected paths on the first and second halves of the interval.
  ext t
  rw [Path.trans_apply]
  split_ifs with ht
  · apply congrArg quotientMap
    apply Prod.ext
    · change Circle.exp (2 * Real.pi * (t : ℝ)) =
        Circle.exp (Real.pi * (2 * (t : ℝ)))
      congr 1
      ring
    · rfl
  · change quotientMap (Circle.exp (2 * Real.pi * (t : ℝ)), 1) =
      quotientMap (Circle.exp (Real.pi * (2 * (t : ℝ) - 1)), 1)
    rw [quotientMap_eq_iff]
    apply Or.inr
    apply Prod.ext
    · change Circle.exp (Real.pi * (2 * (t : ℝ) - 1)) =
        -Circle.exp (2 * Real.pi * (t : ℝ))
      have hangle : 2 * Real.pi * (t : ℝ) =
          Real.pi * (2 * (t : ℝ) - 1) + Real.pi := by
        ring
      rw [hangle, Circle.exp_add, circleExp_pi_eq_negOne]
      simp
    · simp [involution]

/-- Helper for Exercise 74.3: two projected half-turns form the horizontal torus generator. -/
private lemma halfTurn_sq_eq_horizontalImage : halfTurn ^ 2 = horizontalImage := by
  -- Descend the explicit path identity and translate concatenation into multiplication.
  rw [pow_two, halfTurn, horizontalImage, ← horizontalTorusLoop_eq_generator,
    FundamentalGroup.mapOfEq_apply, FundamentalGroup.mul_def,
    ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  exact congrArg Path.Homotopic.Quotient.mk
    horizontalTorusLoop_map_eq_halfTurnPath_trans.symm

/-- Helper for Exercise 74.3: conjugation by the half-turn reverses the vertical generator. -/
private lemma halfTurn_conj_vertical :
    halfTurn * verticalImage * halfTurn⁻¹ = verticalImage⁻¹ := by
  -- Commute the half-turn past the vertical loop, then cancel the inverse half-turn.
  rw [halfTurn_mul_verticalImage]
  exact mul_inv_cancel_right verticalImage⁻¹ halfTurn

/-- Helper for Exercise 74.3: a loop with trivial deck coordinate has a normal form with an
even power of the half-turn. -/
private lemma exists_evenHalfTurnNormalForm_of_deckParity_eq_one
    (x : FundamentalGroup KleinBottle basepoint)
    (hx : quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
      torusBaseFiber x = 1) :
    ∃ m n : ℤ, x = verticalImage ^ n * halfTurn ^ (2 * m) := by
  -- The kernel theorem first lifts the loop to the torus cover.
  have hxker : x ∈
      (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
        torusBaseFiber).ker := by
    exact MonoidHom.mem_ker.mpr hx
  change x ∈
    (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
      (⟨(1, 1), quotientMap_basepoint⟩ : quotientMap ⁻¹' {basepoint})).ker at hxker
  rw [quotientMap_deckParityKernel] at hxker
  obtain ⟨y, hy⟩ := hxker
  let m := (torusFundamentalCoordinates y).1.toAdd
  let n := (torusFundamentalCoordinates y).2.toAdd
  refine ⟨m, n, ?_⟩
  -- Reorder the commuting torus coordinates and identify the horizontal image with two
  -- half-turns.
  have hyCoordinates :
      y = torusVerticalGenerator ^ n * torusHorizontalGenerator ^ m := by
    calc
      y = torusHorizontalGenerator ^ m * torusVerticalGenerator ^ n :=
        torus_eq_horizontal_zpow_mul_vertical_zpow y
      _ = torusVerticalGenerator ^ n * torusHorizontalGenerator ^ m :=
        (torusGenerators_commute.zpow_zpow m n).eq
  calc
    x = FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint y := hy.symm
    _ = FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint
        (torusVerticalGenerator ^ n * torusHorizontalGenerator ^ m) :=
      congrArg (FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint) hyCoordinates
    _ = verticalImage ^ n * horizontalImage ^ m := by
      rw [map_mul, map_zpow, map_zpow]
      rfl
    _ = verticalImage ^ n * halfTurn ^ (2 * m) := by
      have hsq : halfTurn ^ (2 : ℤ) = horizontalImage := by
        exact (zpow_ofNat halfTurn 2).trans halfTurn_sq_eq_horizontalImage
      rw [← hsq, ← zpow_mul]

/-- Helper for Exercise 74.3: every Klein-bottle loop is a vertical power followed by a
half-turn power. -/
private lemma exists_verticalHalfTurnNormalForm
    (x : FundamentalGroup KleinBottle basepoint) :
    ∃ n k : ℤ, x = verticalImage ^ n * halfTurn ^ k := by
  -- Split on the two Boolean deck coordinates.
  cases hparity :
      (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
        torusBaseFiber x).unop.toAdd
  · have hx : quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
        torusBaseFiber x = 1 := by
      apply MulOpposite.unop_injective
      calc
        (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
            torusBaseFiber x).unop = Multiplicative.ofAdd
              (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
                torusBaseFiber x).unop.toAdd :=
          (ofAdd_toAdd _).symm
        _ = Multiplicative.ofAdd false := congrArg Multiplicative.ofAdd hparity
        _ = (1 : Multiplicative Bool) := rfl
    obtain ⟨m, n, hnormal⟩ :=
      exists_evenHalfTurnNormalForm_of_deckParity_eq_one x hx
    exact ⟨n, 2 * m, hnormal⟩
  · have hx : quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
        torusBaseFiber x = MulOpposite.op (Multiplicative.ofAdd true) := by
      apply MulOpposite.unop_injective
      calc
        (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
            torusBaseFiber x).unop = Multiplicative.ofAdd
              (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
                torusBaseFiber x).unop.toAdd :=
          (ofAdd_toAdd _).symm
        _ = Multiplicative.ofAdd true := congrArg Multiplicative.ofAdd hparity
        _ = (MulOpposite.op (Multiplicative.ofAdd true)).unop := rfl
    have hcorrected :
        quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
          torusBaseFiber (x * halfTurn⁻¹) = 1 := by
      rw [map_mul, map_inv, hx, halfTurn_deckParity]
      exact mul_inv_cancel _
    obtain ⟨m, n, hnormal⟩ :=
      exists_evenHalfTurnNormalForm_of_deckParity_eq_one (x * halfTurn⁻¹) hcorrected
    refine ⟨n, 2 * m + 1, ?_⟩
    calc
      x = (x * halfTurn⁻¹) * halfTurn := by group
      _ = (verticalImage ^ n * halfTurn ^ (2 * m)) * halfTurn :=
        congrArg (fun z ↦ z * halfTurn) hnormal
      _ = verticalImage ^ n * halfTurn ^ (2 * m + 1) := by
        rw [mul_assoc, zpow_add_one]

/-- Helper for Exercise 74.3: powers of the vertical loop give the normal cyclic factor in the
Klein-bottle fundamental group. -/
private def fundamentalNormalGenerator :
    Multiplicative ℤ →* FundamentalGroup KleinBottle basepoint :=
  zpowersHom _ verticalImage

/-- Helper for Exercise 74.3: powers of the half-turn give the acting cyclic factor in the
Klein-bottle fundamental group. -/
private def fundamentalActingGenerator :
    Multiplicative ℤ →* FundamentalGroup KleinBottle basepoint :=
  zpowersHom _ halfTurn

/-- Helper for Exercise 74.3: inversion of the vertical coordinate is conjugation by the
canonical half-turn. -/
private lemma fundamentalGeneratorIntertwines (n : Multiplicative ℤ) :
    fundamentalNormalGenerator ((MulEquiv.inv (Multiplicative ℤ)) n) =
      MulAut.conj halfTurn (fundamentalNormalGenerator n) := by
  -- Both sides are homomorphisms from the infinite cyclic group, so use the geometric
  -- conjugation relation on its generator.
  suffices hhom :
      fundamentalNormalGenerator.comp
          (MulEquiv.inv (Multiplicative ℤ)).toMonoidHom =
        (MulAut.conj halfTurn).toMonoidHom.comp fundamentalNormalGenerator by
    exact DFunLike.congr_fun hhom n
  apply MonoidHom.ext_mint
  simpa [fundamentalNormalGenerator] using halfTurn_conj_vertical.symm

/-- Helper for Exercise 74.3: the two cyclic maps into the fundamental group satisfy the
semidirect-product compatibility. -/
private lemma fundamentalCyclicFactorsCompatible (g : Multiplicative ℤ) :
    fundamentalNormalGenerator.comp (kleinInversionAction g).toMonoidHom =
      (MulAut.conj (fundamentalActingGenerator g)).toMonoidHom.comp
        fundamentalNormalGenerator := by
  -- Propagate the generator relation through every integer power of the acting automorphism.
  rw [← ofAdd_toAdd g]
  apply MonoidHom.ext
  intro n
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [kleinInversionAction, zpowersHom_apply,
    map_mulAut_zpow_of_intertwines fundamentalNormalGenerator
      (MulEquiv.inv (Multiplicative ℤ)) (MulAut.conj halfTurn)
      fundamentalGeneratorIntertwines]
  simp only [fundamentalActingGenerator, zpowersHom_apply]
  rw [← map_zpow]

/-- Helper for Exercise 74.3: the canonical semidirect product acts on the Klein-bottle
fundamental group through the vertical loop and half-turn. -/
private def kleinDeckRepresentation :
    KleinDeck →* FundamentalGroup KleinBottle basepoint :=
  SemidirectProduct.lift fundamentalNormalGenerator fundamentalActingGenerator
    fundamentalCyclicFactorsCompatible

/-- Helper for Exercise 74.3: the representation sends the normal generator to the vertical
loop. -/
private lemma kleinDeckRepresentation_inl :
    kleinDeckRepresentation (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ℤ))) =
      verticalImage := by
  -- Evaluate the semidirect-product lift on its normal cyclic factor.
  simp [kleinDeckRepresentation, fundamentalNormalGenerator]

/-- Helper for Exercise 74.3: the representation sends the acting generator to the canonical
half-turn. -/
private lemma kleinDeckRepresentation_inr :
    kleinDeckRepresentation (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))) =
      halfTurn := by
  -- Evaluate the semidirect-product lift on its acting cyclic factor.
  simp [kleinDeckRepresentation, fundamentalActingGenerator]

/-- Helper for Exercise 74.3: the vertical generator has trivial Boolean deck coordinate. -/
private lemma verticalImage_deckParity :
    quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
      torusBaseFiber verticalImage = 1 := by
  -- The vertical loop is visibly in the range of the induced torus homomorphism.
  apply MonoidHom.mem_ker.mp
  change verticalImage ∈
    (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
      (⟨(1, 1), quotientMap_basepoint⟩ : quotientMap ⁻¹' {basepoint})).ker
  rw [quotientMap_deckParityKernel]
  exact ⟨torusVerticalGenerator, rfl⟩

/-- Helper for Exercise 74.3: the semidirect-product representation has trivial kernel. -/
private lemma kleinDeckRepresentation_eq_one_imp_eq_one (d : KleinDeck)
    (hd : kleinDeckRepresentation d = 1) : d = 1 := by
  let n := d.left.toAdd
  let k := d.right.toAdd
  -- Expand the semidirect-product element in its canonical normal form.
  have hrepresentation :
      kleinDeckRepresentation d = verticalImage ^ n * halfTurn ^ k := by
    calc
      kleinDeckRepresentation d = kleinDeckRepresentation
          (SemidirectProduct.inl d.left * SemidirectProduct.inr d.right) :=
        congrArg kleinDeckRepresentation (SemidirectProduct.inl_left_mul_inr_right d).symm
      _ = verticalImage ^ n * halfTurn ^ k := by
        simp only [map_mul, kleinDeckRepresentation, SemidirectProduct.lift_inl,
          SemidirectProduct.lift_inr, fundamentalNormalGenerator,
          fundamentalActingGenerator, zpowersHom_apply, n, k, ofAdd_toAdd]
  -- Applying deck parity shows that the acting exponent is even.
  have hhalfParity :
      quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite
        torusBaseFiber (halfTurn ^ k) = 1 := by
    have hparity := congrArg
      (quotientMap_isAddQuotientCoveringMap.fundamentalGroupToMulOpposite torusBaseFiber) hd
    rw [hrepresentation, map_mul, map_zpow, verticalImage_deckParity, one_zpow,
      one_mul, map_one] at hparity
    exact hparity
  have hkEven : Even k :=
    (halfTurn_zpow_deckParity_eq_one_iff_even k).mp hhalfParity
  obtain ⟨m, hm⟩ := hkEven
  have hk : k = 2 * m := by
    simpa only [two_mul] using hm
  -- Once the acting exponent is even, the equation lies in the injective torus subgroup.
  have hnormal : verticalImage ^ n * horizontalImage ^ m = 1 := by
    have hnormal' : verticalImage ^ n * halfTurn ^ k = 1 :=
      hrepresentation.symm.trans hd
    have hsq : halfTurn ^ (2 : ℤ) = horizontalImage := by
      exact (zpow_ofNat halfTurn 2).trans halfTurn_sq_eq_horizontalImage
    rw [hk, zpow_mul, hsq] at hnormal'
    exact hnormal'
  have htorus :
      torusVerticalGenerator ^ n * torusHorizontalGenerator ^ m = 1 := by
    apply quotientMap_induced_injective
    rw [map_mul, map_zpow, map_zpow, map_one]
    exact hnormal
  -- Integer-pair coordinates force both exponents to vanish.
  have hcoordinates := congrArg torusFundamentalCoordinates htorus
  rw [map_mul, map_zpow, map_zpow, map_one] at hcoordinates
  simp only [torusVerticalGenerator, torusHorizontalGenerator,
    torusFundamentalCoordinates.apply_symm_apply] at hcoordinates
  have hmZero : m = 0 := by
    have hvertical :
        (((((1 : Multiplicative ℤ), Multiplicative.ofAdd (1 : ℤ)) ^ n).1)) =
          (1 : Multiplicative ℤ) ^ n :=
      map_zpow (MonoidHom.fst (Multiplicative ℤ) (Multiplicative ℤ)) _ _
    have hhorizontal :
        (((Multiplicative.ofAdd (1 : ℤ), (1 : Multiplicative ℤ)) ^ m).1) =
          Multiplicative.ofAdd (1 : ℤ) ^ m :=
      map_zpow (MonoidHom.fst (Multiplicative ℤ) (Multiplicative ℤ)) _ _
    have hfirstPair := congrArg Prod.fst hcoordinates
    rw [Prod.fst_mul, hvertical, hhorizontal, one_zpow, one_mul] at hfirstPair
    have hfirst := congrArg Multiplicative.toAdd hfirstPair
    simpa using hfirst
  have hnZero : n = 0 := by
    have hvertical :
        (((((1 : Multiplicative ℤ), Multiplicative.ofAdd (1 : ℤ)) ^ n).2)) =
          Multiplicative.ofAdd (1 : ℤ) ^ n :=
      map_zpow (MonoidHom.snd (Multiplicative ℤ) (Multiplicative ℤ)) _ _
    have hhorizontal :
        (((Multiplicative.ofAdd (1 : ℤ), (1 : Multiplicative ℤ)) ^ m).2) =
          (1 : Multiplicative ℤ) ^ m :=
      map_zpow (MonoidHom.snd (Multiplicative ℤ) (Multiplicative ℤ)) _ _
    have hsecondPair := congrArg Prod.snd hcoordinates
    rw [Prod.snd_mul, hvertical, hhorizontal, one_zpow, mul_one] at hsecondPair
    have hsecond := congrArg Multiplicative.toAdd hsecondPair
    simpa using hsecond
  have hkZero : k = 0 := by
    rw [hk, hmZero, mul_zero]
  -- The two structure coordinates are therefore the identity elements.
  apply SemidirectProduct.ext
  · rw [← ofAdd_toAdd d.left]
    change Multiplicative.ofAdd n = 1
    rw [hnZero]
    rfl
  · rw [← ofAdd_toAdd d.right]
    change Multiplicative.ofAdd k = 1
    rw [hkZero]
    rfl

/-- Helper for Exercise 74.3: the canonical semidirect-product representation is bijective. -/
private lemma kleinDeckRepresentation_bijective :
    Function.Bijective kleinDeckRepresentation := by
  -- Triviality of the kernel gives injectivity, while the normal form supplies a preimage.
  constructor
  · intro d e hde
    apply mul_inv_eq_one.mp
    apply kleinDeckRepresentation_eq_one_imp_eq_one
    rw [map_mul, map_inv, hde, mul_inv_cancel]
  · intro x
    obtain ⟨n, k, hnormal⟩ := exists_verticalHalfTurnNormalForm x
    refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd n) *
      SemidirectProduct.inr (Multiplicative.ofAdd k), ?_⟩
    rw [map_mul]
    simp only [kleinDeckRepresentation, SemidirectProduct.lift_inl,
      SemidirectProduct.lift_inr, fundamentalNormalGenerator,
      fundamentalActingGenerator, zpowersHom_apply, ofAdd_toAdd]
    exact hnormal.symm

/-- Helper for Exercise 74.3: the canonical semidirect-product model is equivalent to the
Klein-bottle fundamental group. -/
private def kleinDeckFundamentalMulEquiv :
    KleinDeck ≃* FundamentalGroup KleinBottle basepoint :=
  MulEquiv.ofBijective kleinDeckRepresentation kleinDeckRepresentation_bijective

/-- Helper for Exercise 74.3: fixed presentation coordinates on the Klein-bottle fundamental
group. -/
private def kleinFundamentalCoordinates :
    FundamentalGroup KleinBottle basepoint ≃* Presentation :=
  kleinDeckFundamentalMulEquiv.symm.trans presentationMulEquivKleinDeck.symm

/-- Helper for Exercise 74.3: the fixed Klein-bottle coordinates send the half-turn to `a`. -/
private lemma kleinFundamentalCoordinates_halfTurn :
    kleinFundamentalCoordinates halfTurn = a := by
  -- Pull the half-turn back through the acting generator in both equivalences.
  have hpull : kleinDeckFundamentalMulEquiv.symm halfTurn =
      SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) := by
    apply kleinDeckFundamentalMulEquiv.injective
    rw [kleinDeckFundamentalMulEquiv.apply_symm_apply]
    simpa only [kleinDeckFundamentalMulEquiv, MulEquiv.ofBijective_apply] using
      kleinDeckRepresentation_inr.symm
  have ppull : presentationMulEquivKleinDeck.symm
      (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))) = a := by
    apply presentationMulEquivKleinDeck.injective
    rw [presentationMulEquivKleinDeck.apply_symm_apply]
    exact presentationToKleinDeck_a.symm
  -- Compose the two inverse-coordinate computations.
  rw [kleinFundamentalCoordinates, MulEquiv.trans_apply, hpull, ppull]

/-- Helper for Exercise 74.3: the fixed Klein-bottle coordinates send the vertical loop to
`b`. -/
private lemma kleinFundamentalCoordinates_verticalImage :
    kleinFundamentalCoordinates verticalImage = b := by
  -- Pull the vertical loop back through the normal generator in both equivalences.
  have hpull : kleinDeckFundamentalMulEquiv.symm verticalImage =
      SemidirectProduct.inl (Multiplicative.ofAdd (1 : ℤ)) := by
    apply kleinDeckFundamentalMulEquiv.injective
    rw [kleinDeckFundamentalMulEquiv.apply_symm_apply]
    simpa only [kleinDeckFundamentalMulEquiv, MulEquiv.ofBijective_apply] using
      kleinDeckRepresentation_inl.symm
  have ppull : presentationMulEquivKleinDeck.symm
      (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ℤ))) = b := by
    apply presentationMulEquivKleinDeck.injective
    rw [presentationMulEquivKleinDeck.apply_symm_apply]
    exact presentationToKleinDeck_b.symm
  -- Compose the two inverse-coordinate computations.
  rw [kleinFundamentalCoordinates, MulEquiv.trans_apply, hpull, ppull]

/-- Helper for Exercise 74.3: the fixed Klein-bottle coordinates send the horizontal image to
`a ^ 2`. -/
private lemma kleinFundamentalCoordinates_horizontalImage :
    kleinFundamentalCoordinates horizontalImage = a ^ (2 : ℤ) := by
  -- Rewrite the horizontal image as two half-turns, then use multiplicativity.
  calc
    kleinFundamentalCoordinates horizontalImage =
        kleinFundamentalCoordinates (halfTurn ^ (2 : ℤ)) :=
      congrArg kleinFundamentalCoordinates halfTurn_sq_eq_horizontalImage.symm
    _ = kleinFundamentalCoordinates halfTurn ^ (2 : ℤ) :=
      map_zpow kleinFundamentalCoordinates halfTurn 2
    _ = a ^ (2 : ℤ) := congrArg (· ^ (2 : ℤ))
      kleinFundamentalCoordinates_halfTurn

/-- Exercise 74.3 (1): The fundamental group of the Klein bottle has presentation
`⟨a, b | a * b * a⁻¹ * b = 1⟩`. -/
theorem fundamentalGroupMulEquiv :
    Nonempty (FundamentalGroup KleinBottle basepoint ≃* Presentation) := by
  -- Use the fixed equivalence assembled from the geometric semidirect-product model.
  exact ⟨kleinFundamentalCoordinates⟩

/-- Exercise 74.3 (2): The standard quotient map from the torus to the Klein bottle is a double
covering. -/
instance quotientMap.isKFoldCovering : IsKFoldCovering 2 quotientMap := by
  -- Forget the deck action for the covering property and identify each fiber with `Bool`.
  refine
    { isCoveringMap := quotientMap_isAddQuotientCoveringMap.isCoveringMap
      surjective := quotientMap_isAddQuotientCoveringMap.surjective
      fiberEquiv := fun point ↦ ?_ }
  obtain ⟨lift, hlift⟩ := quotientMap_isAddQuotientCoveringMap.surjective point
  exact ⟨(quotientMap_isAddQuotientCoveringMap.fiberEquivAddGroup ⟨lift, hlift⟩).trans
    finTwoEquiv.symm⟩

/-- Exercise 74.3 (3): In suitable integer-pair and presentation coordinates, the homomorphism on
fundamental groups induced by the double covering is `(m, n) ↦ a ^ (2 * m) * b ^ n`. -/
theorem quotientMap_induced :
    ∃ torusCoordinates : FundamentalGroup (Circle × Circle) (1, 1) ≃*
        Multiplicative ℤ × Multiplicative ℤ,
      ∃ kleinCoordinates : FundamentalGroup KleinBottle basepoint ≃* Presentation,
        kleinCoordinates.toMonoidHom.comp
            (FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint) =
          torusHom.comp torusCoordinates.toMonoidHom := by
  -- Use the same torus and Klein-bottle coordinates as in the geometric construction.
  refine ⟨torusFundamentalCoordinates, kleinFundamentalCoordinates, ?_⟩
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  let m := (torusFundamentalCoordinates x).1.toAdd
  let n := (torusFundamentalCoordinates x).2.toAdd
  calc
    kleinFundamentalCoordinates
        (FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint x) =
      kleinFundamentalCoordinates
        (FundamentalGroup.mapOfEq quotientMap quotientMap_basepoint
          (torusHorizontalGenerator ^ m * torusVerticalGenerator ^ n)) := by
        rw [torus_eq_horizontal_zpow_mul_vertical_zpow x]
    _ = a ^ (2 * m) * b ^ n := by
      simp only [map_mul, map_zpow]
      change kleinFundamentalCoordinates horizontalImage ^ m *
        kleinFundamentalCoordinates verticalImage ^ n = _
      rw [kleinFundamentalCoordinates_horizontalImage,
        kleinFundamentalCoordinates_verticalImage, ← zpow_mul]
    _ = torusHom (torusFundamentalCoordinates x) := by
      exact (torusHom_apply _ _).symm

end KleinBottle
