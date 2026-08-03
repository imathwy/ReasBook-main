module

public import Topology_Munkres_2000.Book.Exercise_74_3
public import Topology_Munkres_2000.Book.Theorem_75_2
public import Mathlib.Data.ZMod.Basic

import all Topology_Munkres_2000.Book.Exercise_74_3.Presentation

public section

open CategoryTheory AlgebraicTopology

namespace KleinBottle

/-- Helper for Exercise 75.2: the two presentation generators have the standard coordinates in
`Multiplicative (ℤ × ZMod 2)`. -/
private def presentationGeneratorCoordinates : Fin 2 → Multiplicative (ℤ × ZMod 2) :=
  fun i ↦ if i = 0 then Multiplicative.ofAdd (1, 0) else Multiplicative.ofAdd (0, 1)

/-- Helper for Exercise 75.2: the standard generator coordinates satisfy the Klein-bottle
relator. -/
private lemma presentationGeneratorCoordinatesRespectsRelator
    (r : FreeGroup (Fin 2)) (hr : r ∈ ({relator} : Set (FreeGroup (Fin 2)))) :
    FreeGroup.lift presentationGeneratorCoordinates r = 1 := by
  -- Membership in the singleton reduces the calculation to the displayed relator.
  rw [Set.mem_singleton_iff.mp hr]
  -- Its two `b`-coordinates cancel modulo two, while the `a`-coordinates cancel integrally.
  norm_num [relator, presentationGeneratorCoordinates]
  change ((0 : ℤ), (1 : ZMod 2)) + (0, 1) = 0
  norm_num
  exact CharP.cast_eq_zero (ZMod 2) 2

/-- Helper for Exercise 75.2: twice the second presentation generator vanishes after
abelianization. -/
private lemma twoNsmulAbelianizedB :
    2 • Additive.ofMul (Abelianization.of b) = 0 := by
  -- The defining relator is trivial in the presented group.
  have hpresentation : a * b * a⁻¹ * b = 1 := by
    have hrelator := PresentedGroup.one_of_mem (Set.mem_singleton relator)
    unfold relator at hrelator
    simp only [map_mul, map_inv] at hrelator
    unfold a b PresentedGroup.of
    exact hrelator
  -- Map that relation to the additive form of the abelianization and cancel the `a`-terms.
  have habelianized := congrArg
    (fun x : Presentation ↦ Additive.ofMul (Abelianization.of x)) hpresentation
  change Additive.ofMul (Abelianization.of a) + Additive.ofMul (Abelianization.of b) -
      Additive.ofMul (Abelianization.of a) + Additive.ofMul (Abelianization.of b) = 0
    at habelianized
  abel_nf at habelianized
  exact habelianized

/-- Helper for Exercise 75.2: the additive abelianization of the Klein-bottle presentation has
coordinates `ℤ × ZMod 2`. -/
private lemma nonemptyPresentationAbelianizationAddEquiv :
    Nonempty
      (Additive (Abelianization Presentation) ≃+ ℤ × ZMod 2) := by
  -- Extend the two generator coordinates first through the presentation and then through its
  -- abelianization.
  let presentationCoordinates : Presentation →* Multiplicative (ℤ × ZMod 2) :=
    PresentedGroup.toGroup presentationGeneratorCoordinatesRespectsRelator
  let forward : Abelianization Presentation →* Multiplicative (ℤ × ZMod 2) :=
    Abelianization.lift presentationCoordinates
  -- The inverse sends the integral and mod-two coordinate generators to the two abelianized
  -- presentation generators.
  let abelianizedA : Additive (Abelianization Presentation) :=
    Additive.ofMul (Abelianization.of a)
  let abelianizedB : Additive (Abelianization Presentation) :=
    Additive.ofMul (Abelianization.of b)
  let integerCoordinate : ℤ →+ Additive (Abelianization Presentation) :=
    zmultiplesHom _ abelianizedA
  have modTwoCondition : (zmultiplesHom _ abelianizedB) (2 : ℤ) = 0 := by
    simpa only [zmultiplesHom_apply, abelianizedB, ofNat_zsmul] using
      twoNsmulAbelianizedB
  let modTwoCoordinate : ZMod 2 →+ Additive (Abelianization Presentation) :=
    ZMod.lift 2 ⟨zmultiplesHom _ abelianizedB, modTwoCondition⟩
  have modTwoCoordinate_intCast (n : ℤ) :
      modTwoCoordinate (n : ZMod 2) = n • abelianizedB := by
    -- The computation rule for `ZMod.lift` gives the inverse map on every representative.
    simp only [modTwoCoordinate, ZMod.lift_coe, zmultiplesHom_apply]
  let backwardAdd : ℤ × ZMod 2 →+ Additive (Abelianization Presentation) :=
    integerCoordinate.coprod modTwoCoordinate
  let backward : Multiplicative (ℤ × ZMod 2) →* Abelianization Presentation :=
    AddMonoidHom.toMultiplicativeLeft backwardAdd
  -- On the abelianized presentation, the first composite is determined by the two generators.
  have backwardForward : backward.comp forward = MonoidHom.id _ := by
    apply Abelianization.hom_ext
    apply PresentedGroup.ext
    intro i
    fin_cases i
    · simp [backward, backwardAdd, modTwoCoordinate, integerCoordinate, abelianizedA,
        abelianizedB, forward, presentationCoordinates, presentationGeneratorCoordinates, a]
    · have modTwoCoordinate_one : modTwoCoordinate 1 = abelianizedB := by
        simpa only [Int.cast_one, one_zsmul] using modTwoCoordinate_intCast 1
      simp [backward, backwardAdd, integerCoordinate, abelianizedA, abelianizedB, forward,
        presentationCoordinates, presentationGeneratorCoordinates, modTwoCoordinate_one, b]
  -- For the other composite, integer representatives reduce the mod-two coordinate to the
  -- computation on its generator.
  have forwardBackward : forward.comp backward = MonoidHom.id _ := by
    apply MonoidHom.ext
    rintro ⟨m, z⟩
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    change forward (backward (Multiplicative.ofAdd (m, (n : ZMod 2)))) =
      Multiplicative.ofAdd (m, (n : ZMod 2))
    suffices hcoordinates :
        Multiplicative.ofAdd ((1 : ℤ), (0 : ZMod 2)) ^ m *
            Multiplicative.ofAdd ((0 : ℤ), (1 : ZMod 2)) ^ n =
          Multiplicative.ofAdd (m, (n : ZMod 2)) by
      simpa [backward, backwardAdd, integerCoordinate, abelianizedA, abelianizedB, forward,
        presentationCoordinates, presentationGeneratorCoordinates, modTwoCoordinate_intCast,
        a, b] using hcoordinates
    change m • ((1 : ℤ), (0 : ZMod 2)) + n • ((0 : ℤ), (1 : ZMod 2)) =
      (m, (n : ZMod 2))
    ext
    · simp
    · simp
  -- Package the mutually inverse homomorphisms and remove the additive/multiplicative type tags.
  exact ⟨MulEquiv.toAdditiveLeft
    (MonoidHom.toMulEquiv forward backward backwardForward forwardBackward)⟩

/-- Helper for Exercise 75.2: over a universe-zero path-connected space, integral first
homology is the additive abelianization of the fundamental group. -/
private lemma integralFirstHomologyIsoAbelianization {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (x₀ : X) :
    Nonempty
      (((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).obj
          (TopCat.of X) ≅
        AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x₀)))) := by
  -- Theorem 75.2 supplies Hurewicz with lifted integer coefficients.
  obtain ⟨hurewicz⟩ := AlgebraicTopology.firstHomologyIsoAbelianization x₀
  let coefficientIso : AddCommGrpCat.of (ULift.{0} ℤ) ≅ AddCommGrpCat.of ℤ :=
    AddEquiv.ulift.toAddCommGrpIso
  -- Functoriality in the coefficient group transports those coefficients back to `ℤ`.
  exact ⟨(((singularHomologyFunctor AddCommGrpCat 1).mapIso coefficientIso).app
    (TopCat.of X)).symm ≪≫ hurewicz⟩

/-- Exercise 75.2. The first integral singular homology group of the Klein bottle is
isomorphic to `ℤ × ZMod 2`. -/
theorem firstHomology :
    Nonempty
      (((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).obj
          (TopCat.of KleinBottle) ≅ AddCommGrpCat.of (ℤ × ZMod 2)) := by
  -- Hurewicz reduces the calculation to the abelianized fundamental group.
  obtain ⟨hurewicz⟩ := integralFirstHomologyIsoAbelianization basepoint
  obtain ⟨fundamentalCoordinates⟩ := fundamentalGroupMulEquiv
  obtain ⟨presentationCoordinates⟩ := nonemptyPresentationAbelianizationAddEquiv
  let fundamentalIso :
      AddCommGrpCat.of
          (Additive (Abelianization (FundamentalGroup KleinBottle basepoint))) ≅
        AddCommGrpCat.of (Additive (Abelianization Presentation)) :=
    (MulEquiv.toAdditive fundamentalCoordinates.abelianizationCongr).toAddCommGrpIso
  let presentationIso :
      AddCommGrpCat.of (Additive (Abelianization Presentation)) ≅
        AddCommGrpCat.of (ℤ × ZMod 2) :=
    presentationCoordinates.toAddCommGrpIso
  -- Transport through the presentation and finish with its explicit abelian coordinates.
  exact ⟨hurewicz ≪≫ fundamentalIso ≪≫ presentationIso⟩

end KleinBottle

end
