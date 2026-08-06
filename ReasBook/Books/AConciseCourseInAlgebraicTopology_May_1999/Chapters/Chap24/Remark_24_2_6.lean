import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_2_6

open CategoryTheory HomotopicalAlgebra

noncomputable section

universe w

-- This file keeps the Bott-to-periodicity construction for an arbitrary Ω-prespectrum as the
-- generic Chapter 22 helper. Remark 24.2.6 then reuses Definition 24.2.5's source-facing owner
-- `ComplexKTheoryPrespectrum` and its packaged degree-`0` comparison with reduced complex
-- `K`-theory.

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

/-- A Bott identification of double suspension with the identity exhibits the degreewise natural
`2`-periodicity isomorphism for the Chapter 22 additive reduced cohomology theory represented by
an Ω-prespectrum `KU`. -/
noncomputable def omegaPrespectrumReducedCohomologyAdditiveTwoPeriodicOfBott
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (KU : Prespectrum.{w, 0}) [OmegaPrespectrum KU]
    (bottDoubleSuspension :
      ∀ q : ℤ,
        setup.suspension.op ⋙ setup.suspension.op ⋙ omegaPrespectrumReducedCohomologyAdditive KU q ≅
          omegaPrespectrumReducedCohomologyAdditive KU q)
    (q : ℤ) :
    omegaPrespectrumReducedCohomologyAdditive KU (q + 2) ≅
      omegaPrespectrumReducedCohomologyAdditive KU q :=
  let suspensionIsoSucc :
      setup.suspension.op ⋙ omegaPrespectrumReducedCohomologyAdditive KU (q + 2) ≅
        omegaPrespectrumReducedCohomologyAdditive KU (q + 1) :=
    ReducedCohomologyTheoryOnBasedCWComplexes.suspensionNatIso.{0, w} (q + 2) ≪≫
      eqToIso
        (congrArg (omegaPrespectrumReducedCohomologyAdditive KU)
          (Eq.trans (add_sub_assoc q 2 1)
            (congrArg (fun t : ℤ ↦ q + t) (show (2 : ℤ) - 1 = 1 from rfl))))
  let suspensionIsoBase :
      setup.suspension.op ⋙ omegaPrespectrumReducedCohomologyAdditive KU (q + 1) ≅
        omegaPrespectrumReducedCohomologyAdditive KU q :=
    ReducedCohomologyTheoryOnBasedCWComplexes.suspensionNatIso.{0, w} (q + 1) ≪≫
      eqToIso
        (congrArg (omegaPrespectrumReducedCohomologyAdditive KU)
          (Eq.trans (add_sub_assoc q 1 1)
            (Eq.trans
              (congrArg (fun t : ℤ ↦ q + t) (show (1 : ℤ) - 1 = 0 from rfl))
              (add_zero q))))
  (bottDoubleSuspension (q + 2)).symm ≪≫
    Functor.isoWhiskerLeft setup.suspension.op suspensionIsoSucc ≪≫
    suspensionIsoBase

/-- `omegaPrespectrumReducedCohomologyAdditiveTwoPeriodicOfBott` is obtained by composing the
inverse Bott double-suspension identification with the two suspension isomorphisms from the
reduced-theory structure. -/
theorem omegaPrespectrumReducedCohomologyAdditiveTwoPeriodicOfBott_def
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (KU : Prespectrum.{w, 0}) [OmegaPrespectrum KU]
    (bottDoubleSuspension :
      ∀ q : ℤ,
        setup.suspension.op ⋙ setup.suspension.op ⋙ omegaPrespectrumReducedCohomologyAdditive KU q ≅
          omegaPrespectrumReducedCohomologyAdditive KU q)
    (q : ℤ) :
    omegaPrespectrumReducedCohomologyAdditiveTwoPeriodicOfBott setup KU bottDoubleSuspension q =
      let suspensionIsoSucc :
          setup.suspension.op ⋙ omegaPrespectrumReducedCohomologyAdditive KU (q + 2) ≅
            omegaPrespectrumReducedCohomologyAdditive KU (q + 1) :=
        ReducedCohomologyTheoryOnBasedCWComplexes.suspensionNatIso.{0, w} (q + 2) ≪≫
          eqToIso
            (congrArg (omegaPrespectrumReducedCohomologyAdditive KU)
              (Eq.trans (add_sub_assoc q 2 1)
                (congrArg (fun t : ℤ ↦ q + t) (show (2 : ℤ) - 1 = 1 from rfl))))
      let suspensionIsoBase :
          setup.suspension.op ⋙ omegaPrespectrumReducedCohomologyAdditive KU (q + 1) ≅
            omegaPrespectrumReducedCohomologyAdditive KU q :=
        ReducedCohomologyTheoryOnBasedCWComplexes.suspensionNatIso.{0, w} (q + 1) ≪≫
          eqToIso
            (congrArg (omegaPrespectrumReducedCohomologyAdditive KU)
              (Eq.trans (add_sub_assoc q 1 1)
                (Eq.trans
                  (congrArg (fun t : ℤ ↦ q + t) (show (1 : ℤ) - 1 = 0 from rfl))
                  (add_zero q))))
      (bottDoubleSuspension (q + 2)).symm ≪≫
        Functor.isoWhiskerLeft setup.suspension.op suspensionIsoSucc ≪≫
        suspensionIsoBase := by
  rfl

namespace ComplexKTheoryPrespectrum

variable [CategoryWithCofibrations BasedSpace]
variable [CategoryWithCofibrations BasedCWComplex]
variable [CategoryWithWeakEquivalences BasedCWComplex]
variable (setup : BasedCWReducedSuspensionCofiberSetup)
variable (KU : Prespectrum.{w, 0}) [ComplexKTheoryPrespectrum KU]

/-- For a complex `K`-theory prespectrum `KU`, a Bott identification of double suspension with the
identity exhibits the degreewise natural `2`-periodicity isomorphism of the packaged reduced
cohomology theory `omegaPrespectrumRepresentsReducedCohomologyTheory setup KU`. -/
noncomputable def reducedTheoryTwoPeriodicOfBott
    (bottDoubleSuspension :
      ∀ q : ℤ,
        setup.suspension.op ⋙ setup.suspension.op ⋙
            (omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology q ≅
          (omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology q)
    (q : ℤ) :
    (omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology (q + 2) ≅
      (omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology q :=
  omegaPrespectrumReducedCohomologyAdditiveTwoPeriodicOfBott setup KU bottDoubleSuspension q

/-- `reducedTheoryTwoPeriodicOfBott` is the packaged-theory specialization of the generic
Ω-prespectrum periodicity isomorphism. -/
theorem reducedTheoryTwoPeriodicOfBott_def
    (bottDoubleSuspension :
      ∀ q : ℤ,
        setup.suspension.op ⋙ setup.suspension.op ⋙
            (omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology q ≅
          (omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology q)
    (q : ℤ) :
    reducedTheoryTwoPeriodicOfBott setup KU bottDoubleSuspension q =
      omegaPrespectrumReducedCohomologyAdditiveTwoPeriodicOfBott
        setup KU bottDoubleSuspension q := by
  rfl

/-- The explicit periodicity isomorphism in `reducedTheoryTwoPeriodicOfBott` yields the older
existence form immediately. -/
theorem reducedTheoryTwoPeriodicOfBott_nonempty
    (bottDoubleSuspension :
      ∀ q : ℤ,
        setup.suspension.op ⋙ setup.suspension.op ⋙
            (omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology q ≅
          (omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology q)
    (q : ℤ) :
    Nonempty
      ((omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology (q + 2) ≅
        (omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology q) :=
  ⟨reducedTheoryTwoPeriodicOfBott setup KU bottDoubleSuspension q⟩

end ComplexKTheoryPrespectrum

/- Remark 24.2.6. If `KU` is a `ComplexKTheoryPrespectrum`, then
`ComplexKTheoryPrespectrum.reducedTheoryComparison` identifies degree `0` of the packaged reduced
cohomology theory `omegaPrespectrumRepresentsReducedCohomologyTheory setup KU` with reduced
complex `K`-theory. A Bott identification of double suspension with the identity then feeds into
the generic helper `omegaPrespectrumReducedCohomologyAdditiveTwoPeriodicOfBott`; the source-facing
bridge `ComplexKTheoryPrespectrum.reducedTheoryTwoPeriodicOfBott` records the corresponding
degreewise natural `2`-periodicity isomorphism for the packaged represented theory, with the
existential form kept only as the companion
`ComplexKTheoryPrespectrum.reducedTheoryTwoPeriodicOfBott_nonempty`. -/
#check ComplexKTheoryPrespectrum
#check ComplexKTheoryPrespectrum.reducedTheoryComparison
#check omegaPrespectrumRepresentsReducedCohomologyTheory
#check omegaPrespectrumReducedCohomologyAdditiveTwoPeriodicOfBott
#check ComplexKTheoryPrespectrum.reducedTheoryTwoPeriodicOfBott
