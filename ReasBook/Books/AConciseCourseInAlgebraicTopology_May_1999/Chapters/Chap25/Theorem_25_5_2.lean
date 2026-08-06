import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_5_3.StableHurewicz
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_5_2.PiStar
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_4_7.Milnor
import Mathlib.RingTheory.Coalgebra.Basic

noncomputable section

universe u w

open scoped StableHomotopy
open scoped TensorProduct

section CoactionComparison

variable
    (TO : RingPrespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction : PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    [Ring (homologyPresentation.HStar TO.toPrespectrum)]
    [Algebra (ZMod 2) (homologyPresentation.HStar TO.toPrespectrum)]

/-- Theorem 25.5.2. Let `f : H_*(TO) → N_*` send `a_i` to `u_i` outside the excluded
degrees and to zero in degrees `2^r - 1`. Then
`g = (id ⊗ f) ∘ γ : H_*(TO) → A_* ⊗ N_*` is simultaneously an isomorphism of
`ZMod 2`-algebras and a morphism of `A_*`-comodules. -/
theorem thomCoactionComparison_isomorphism
    (dualA : ModTwoSteenrodAlgebraDualMilnorPresentation)
    (dualCoalgebra : Coalgebra (ZMod 2) modTwoSteenrodAlgebraGradedDual)
    (coaction : PrespectrumModTwoSteenrodCoaction
      cohomologyPresentation cohomologyAction homologyPresentation)
    (presentationEquiv :
      RingPrespectrumModTwoHomologyPolynomialEquiv
        TO
        (homologyPresentation.homologyPresentation TO.toPrespectrum)
        homologyPresentation.sphereZero)
    (NStar : ThomUnorientedCobordismPolynomialAlgebra) :
    letI : CommRing N_* := NStar.toCommRing
    letI : Algebra (ZMod 2) N_* := NStar.toAlgebra
    letI : Coalgebra (ZMod 2) modTwoSteenrodAlgebraGradedDual := dualCoalgebra
    ∃ nStarModule : Module (ZMod 2) N_*,
    letI : Module (ZMod 2) N_* := nStarModule
    let canonicalTargetAddCommGroup :
        AddCommGroup (modTwoSteenrodAlgebraGradedDual ⊗[ZMod 2] N_*) := inferInstance
    ∃ f : homologyPresentation.HStar TO.toPrespectrum → N_*,
      f 0 = NStar.toCommRing.zero ∧
      (∀ x y, f (x + y) = NStar.toCommRing.add (f x) (f y)) ∧
      f 1 = NStar.toCommRing.one ∧
      (∀ x y, f (x * y) = NStar.toCommRing.mul (f x) (f y)) ∧
      (∀ r : ZMod 2,
        f (algebraMap (ZMod 2) (homologyPresentation.HStar TO.toPrespectrum) r) =
          algebraMap (ZMod 2) N_* r) ∧
      (∀ i : BOHomologyGeneratorIndex,
        f (presentationEquiv (MvPolynomial.X i)) =
          thomComparisonGeneratorImage NStar i) ∧
    ∃ idTensorF :
        (modTwoSteenrodAlgebraGradedDual ⊗[ZMod 2]
          homologyPresentation.HStar TO.toPrespectrum) →ₗ[ZMod 2]
            (modTwoSteenrodAlgebraGradedDual ⊗[ZMod 2] N_*),
      (∀ a x, idTensorF (a ⊗ₜ[ZMod 2] x) = a ⊗ₜ[ZMod 2] f x) ∧
      ∃ targetRing : Ring
          (modTwoSteenrodAlgebraGradedDual ⊗[ZMod 2] N_*),
        targetRing.toAddCommGroup = canonicalTargetAddCommGroup ∧
        targetRing.one =
          dualA.toDualAlgebra.toRing.one ⊗ₜ[ZMod 2] NStar.toCommRing.one ∧
        (∀ a b x y,
          targetRing.mul (a ⊗ₜ[ZMod 2] x) (b ⊗ₜ[ZMod 2] y) =
            dualA.toDualAlgebra.toRing.mul a b ⊗ₜ[ZMod 2]
              NStar.toCommRing.mul x y) ∧
        letI := targetRing
        ∃ targetAlgebra : Algebra (ZMod 2)
            (modTwoSteenrodAlgebraGradedDual ⊗[ZMod 2] N_*),
          letI := targetAlgebra
          ∃ e : homologyPresentation.HStar TO.toPrespectrum ≃ₐ[ZMod 2]
              modTwoSteenrodAlgebraGradedDual ⊗[ZMod 2] N_*,
            (∀ x, e x = idTensorF (coaction.gamma TO.toPrespectrum x)) ∧
            ∃ idTensorE :
                (modTwoSteenrodAlgebraGradedDual ⊗[ZMod 2]
                  homologyPresentation.HStar TO.toPrespectrum) →ₗ[ZMod 2]
                    (modTwoSteenrodAlgebraGradedDual ⊗[ZMod 2]
                      (modTwoSteenrodAlgebraGradedDual ⊗[ZMod 2] N_*)),
              (∀ a x, idTensorE (a ⊗ₜ[ZMod 2] x) = a ⊗ₜ[ZMod 2] e x) ∧
              ∀ x,
                (TensorProduct.assoc (ZMod 2)
                    modTwoSteenrodAlgebraGradedDual
                    modTwoSteenrodAlgebraGradedDual N_*)
                    (Coalgebra.comul.rTensor N_* (e x)) =
                  idTensorE (coaction.gamma TO.toPrespectrum x) := by
  sorry

end CoactionComparison

-- The reusable nonnegative stable-homotopy owner lives in the item-local foundation module
-- `Theorem_25_5_2.PiStar`.

section ThomComparison

variable
    (TO : RingPrespectrum.{u, w})
    (stableHomotopyRing : StableHomotopyGradedRing TO)
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    [Ring (homologyPresentation.HStar TO.toPrespectrum)]
    [Algebra (ZMod 2) (homologyPresentation.HStar TO.toPrespectrum)]
    (stableHurewicz :
      PrespectrumModTwoStableHurewicz
        TO.toPrespectrum
        cohomologyPresentation
        cohomologyAction
        homologyPresentation)
    (presentationEquiv :
      RingPrespectrumModTwoHomologyPolynomialEquiv
        TO
        (homologyPresentation.homologyPresentation TO.toPrespectrum)
        homologyPresentation.sphereZero)
    (A : ThomUnorientedCobordismPolynomialAlgebra)

/-- The degree-`n` homogeneous piece of the Chapter 25 composite `g ∘ h`, viewed as an additive
homomorphism from `π_n(TO)` into the Thom polynomial algebra `N_*`. -/
def thomComparisonCompositeDegreeAddHom (n : ℕ) :
    Additive (Prespectrum.stableHomotopyGroup TO.toPrespectrum (n : ℤ)) →+ N_* where
  toFun x :=
    thomComparisonAlgHom TO
      (homologyPresentation.homologyPresentation TO.toPrespectrum)
      homologyPresentation.sphereZero A presentationEquiv
      (stableHurewicz.map (n : ℤ) x.toMul)
  map_zero' := by
    sorry
  map_add' := by
    intro x y
    sorry

/-- The Chapter 25 composite `g ∘ h` from `π_*(TO)` to `N_*`, packaged as the additive homomorphism
induced on the nonnegative direct sum `π_*(TO)` by the degreewise stable Hurewicz maps followed by
the comparison algebra homomorphism. -/
def thomComparisonCompositeAddHom :
    π_*(TO.toPrespectrum) →+ N_* :=
  DirectSum.toAddMonoid fun n ↦
    thomComparisonCompositeDegreeAddHom
      TO
      cohomologyPresentation
      cohomologyAction
      homologyPresentation
      stableHurewicz
      presentationEquiv
      A
      n

/-- On a homogeneous class in degree `n`, `thomComparisonCompositeAddHom` is exactly the composite
of the degree-`n` stable Hurewicz map with the comparison algebra homomorphism `g`. -/
@[simp] theorem thomComparisonCompositeAddHom_piStarClass
    (n : ℕ) (x : Prespectrum.stableHomotopyGroup TO.toPrespectrum (n : ℤ)) :
    thomComparisonCompositeAddHom
        TO
        cohomologyPresentation
        cohomologyAction
        homologyPresentation
        stableHurewicz
        presentationEquiv
        A
        (TO.piStarClass n x) =
      thomComparisonAlgHom TO
        (homologyPresentation.homologyPresentation TO.toPrespectrum)
        homologyPresentation.sphereZero A presentationEquiv
        (stableHurewicz.map (n : ℤ) x) := by
  rw [RingPrespectrum.piStarClass, Prespectrum.piStarClass, DirectSum.lof_eq_of]
  simp [thomComparisonCompositeAddHom, thomComparisonCompositeDegreeAddHom]

/-- For the source-facing comparison algebra homomorphism
`g : H_*(TO) → N_*` from Construction 25.5.1, the composite `g ∘ h` identifies the nonnegative
stable homotopy object `π_*(TO)` with `N_*`: the induced additive map
`thomComparisonCompositeAddHom` is bijective, and on homogeneous classes it carries the graded
product on `π_*(TO)` to multiplication in `N_*`. -/
theorem thomComparisonAlgHom_composite_identifies_nStar :
    Function.Bijective
        (thomComparisonCompositeAddHom
          TO
          cohomologyPresentation
          cohomologyAction
          homologyPresentation
          stableHurewicz
          presentationEquiv
          A) ∧
      ∀ (m n : ℕ)
        (x : Prespectrum.stableHomotopyGroup TO.toPrespectrum (m : ℤ))
        (y : Prespectrum.stableHomotopyGroup TO.toPrespectrum (n : ℤ)),
        thomComparisonCompositeAddHom
            TO
            cohomologyPresentation
            cohomologyAction
            homologyPresentation
            stableHurewicz
            presentationEquiv
            A
            (TO.piStarClass (m + n) (stableHomotopyRing.mul (m : ℤ) (n : ℤ) x y)) =
          A.toCommRing.mul
            (thomComparisonCompositeAddHom
              TO
              cohomologyPresentation
              cohomologyAction
              homologyPresentation
              stableHurewicz
              presentationEquiv
              A
              (TO.piStarClass m x))
            (thomComparisonCompositeAddHom
              TO
              cohomologyPresentation
              cohomologyAction
              homologyPresentation
              stableHurewicz
              presentationEquiv
              A
              (TO.piStarClass n y)) := by
  sorry

/-- Forgetting the multiplicative structure, the Chapter 25 composite `g ∘ h` already identifies
`π_*(TO)` with `N_*` through the named additive homomorphism
`thomComparisonCompositeAddHom`. -/
theorem thomComparisonCompositeAddHom_bijective
    (stableRing : StableHomotopyGradedRing TO) :
    Function.Bijective
      (thomComparisonCompositeAddHom
        TO
        cohomologyPresentation
        cohomologyAction
        homologyPresentation
        stableHurewicz
        presentationEquiv
        A) := by
  exact
    (thomComparisonAlgHom_composite_identifies_nStar
      TO
      stableRing
      cohomologyPresentation
      cohomologyAction
      homologyPresentation
      stableHurewicz
      presentationEquiv
      A).1

variable
    (homologyGenerators :
      BOHomologyGeneratorIndex → homologyPresentation.HStar TO.toPrespectrum)
    (presentation :
      IsRingPrespectrumModTwoHomologyPolynomialPresentationOn
        TO
        (homologyPresentation.homologyPresentation TO.toPrespectrum)
        homologyPresentation.sphereZero
        homologyGenerators
        presentationEquiv)

include presentation

/-- Companion API for the later Theorem 25.5.4.  The map obtained by following the stable
Hurewicz homomorphism with `f : H_*(TO) → N_*` is bijective and multiplicative on homogeneous
classes.  This is not the statement of Theorem 25.5.2; its `A_* ⊗ N_*` comparison is recorded
above by `thomCoactionComparison_isomorphism`. -/
theorem thomComparisonAlgHom_detects_nStar :
    (∀ i : BOHomologyGeneratorIndex,
      thomComparisonAlgHom TO
          (homologyPresentation.homologyPresentation TO.toPrespectrum)
          homologyPresentation.sphereZero A presentationEquiv
          (homologyGenerators i) =
        thomComparisonGeneratorImage A i) ∧
      Function.Bijective
          (thomComparisonCompositeAddHom
            TO
            cohomologyPresentation
            cohomologyAction
            homologyPresentation
            stableHurewicz
            presentationEquiv
            A) ∧
      (∀ (m n : ℕ)
          (x : Prespectrum.stableHomotopyGroup TO.toPrespectrum (m : ℤ))
          (y : Prespectrum.stableHomotopyGroup TO.toPrespectrum (n : ℤ)),
          thomComparisonCompositeAddHom
              TO
              cohomologyPresentation
              cohomologyAction
              homologyPresentation
              stableHurewicz
              presentationEquiv
              A
              (TO.piStarClass (m + n) (stableHomotopyRing.mul (m : ℤ) (n : ℤ) x y)) =
            A.toCommRing.mul
              (thomComparisonCompositeAddHom
                TO
                cohomologyPresentation
                cohomologyAction
                homologyPresentation
                stableHurewicz
                presentationEquiv
                A
                (TO.piStarClass m x))
              (thomComparisonCompositeAddHom
                TO
                cohomologyPresentation
                cohomologyAction
                homologyPresentation
                stableHurewicz
                presentationEquiv
                A
                (TO.piStarClass n y))) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact thomComparisonAlgHom_apply_generator
      TO
      (homologyPresentation.homologyPresentation TO.toPrespectrum)
      homologyPresentation.sphereZero A homologyGenerators presentationEquiv presentation i
  · exact thomComparisonAlgHom_composite_identifies_nStar
      TO
      stableHomotopyRing
      cohomologyPresentation
      cohomologyAction
      homologyPresentation
      stableHurewicz
      presentationEquiv
      A

end ThomComparison
