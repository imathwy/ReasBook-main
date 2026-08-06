import Mathlib.LinearAlgebra.Contraction
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_4_9.Homology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_6.DualAlgebra

open scoped TensorProduct

noncomputable section

universe u w

-- Semantic recall: `lean_leansearch` confirms `dualTensorHom` and `dualTensorHom_apply` in
-- `Mathlib.LinearAlgebra.Contraction` as the canonical tensor-evaluation API used below.
/-- The helper predicate asserting that a chosen coaction `gamma` and chosen Kronecker pairing
satisfy the duality formula from Construction 25.4.9. -/
def prespectrumModTwoSteenrodCoactionDuality
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation)
    (gamma :
      ∀ T : Prespectrum.{u, w},
        homologyPresentation.HStar T →ₗ[(ZMod 2)]
          modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)] homologyPresentation.HStar T)
    (kroneckerPairing :
      ∀ T : Prespectrum.{u, w},
        homologyPresentation.HStar T →ₗ[(ZMod 2)]
          Module.Dual (ZMod 2) (cohomologyPresentation.HStar T)) : Prop :=
  ∀ (T : Prespectrum.{u, w}) (x : homologyPresentation.HStar T)
    (a : ModTwoSteenrodAlgebra) (φ : cohomologyPresentation.HStar T),
    -- Local instance justification (proof-local temporary data): `a • φ` uses the specific
    -- `ModTwoSteenrodAlgebra`-module structure stored by `cohomologyAction` on
    -- `cohomologyPresentation.HStar T`.
    letI := cohomologyAction.module T
    kroneckerPairing T x (a • φ) =
      kroneckerPairing T
        ((dualTensorHom (ZMod 2) ModTwoSteenrodAlgebra (homologyPresentation.HStar T)
            (modTwoSteenrodAlgebraGradedDual.tensorInclusion
              (homologyPresentation.HStar T) (gamma T x))) a)
        φ

/-- Expanding `prespectrumModTwoSteenrodCoactionDuality` gives the Kronecker-pairing formula
expressing that the coaction on `H_*(T)` is dual to the Steenrod action on `H^*(T)`. -/
theorem prespectrumModTwoSteenrodCoactionDuality_iff
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation)
    (gamma :
      ∀ T : Prespectrum.{u, w},
        homologyPresentation.HStar T →ₗ[(ZMod 2)]
          modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)] homologyPresentation.HStar T)
    (kroneckerPairing :
      ∀ T : Prespectrum.{u, w},
        homologyPresentation.HStar T →ₗ[(ZMod 2)]
          Module.Dual (ZMod 2) (cohomologyPresentation.HStar T)) :
    prespectrumModTwoSteenrodCoactionDuality
        cohomologyPresentation cohomologyAction homologyPresentation gamma kroneckerPairing ↔
      ∀ (T : Prespectrum.{u, w}) (x : homologyPresentation.HStar T)
        (a : ModTwoSteenrodAlgebra) (φ : cohomologyPresentation.HStar T),
        -- Local instance justification (proof-local temporary data): `a • φ` is interpreted
        -- using the module structure chosen by `cohomologyAction` on
        -- `cohomologyPresentation.HStar T`.
        letI := cohomologyAction.module T
        kroneckerPairing T x (a • φ) =
          kroneckerPairing T
            ((dualTensorHom (ZMod 2) ModTwoSteenrodAlgebra (homologyPresentation.HStar T)
                (modTwoSteenrodAlgebraGradedDual.tensorInclusion
                  (homologyPresentation.HStar T) (gamma T x))) a)
            φ :=
  Iff.rfl

/-- Construction 25.4.9. A source-facing coaction owner carrying the coaction
`gamma : H_*(T) → A_* ⊗[(ZMod 2)] H_*(T)`, a Kronecker pairing between `H_*(T)` and `H^*(T)`,
and the statement that they satisfy the duality formula. Here `A_*` is the fixed dual Steenrod
algebra owner from Lemma 25.4.6, represented by `modTwoSteenrodAlgebraGradedDual`. -/
structure PrespectrumModTwoSteenrodCoaction
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation) where
  /-- The chosen coaction on the source-facing total mod-`2` homology object `H_*(T)`. -/
  gamma :
    ∀ T : Prespectrum.{u, w},
      homologyPresentation.HStar T →ₗ[(ZMod 2)]
        modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)] homologyPresentation.HStar T
  /-- The chosen Kronecker pairing between the fixed homology presentation and the chosen
  Steenrod-module presentation of cohomology. -/
  kroneckerPairing :
    ∀ T : Prespectrum.{u, w},
      homologyPresentation.HStar T →ₗ[(ZMod 2)]
        Module.Dual (ZMod 2) (cohomologyPresentation.HStar T)
  /-- The stored coaction and Kronecker pairing realize the source duality: pairing `x` with
  `a • φ` agrees with first applying `gamma` to `x`, then evaluating the `A_*`-component on `a`,
  and finally pairing the resulting homology class with `φ`. -/
  duality :
    prespectrumModTwoSteenrodCoactionDuality
      cohomologyPresentation cohomologyAction homologyPresentation gamma kroneckerPairing

namespace PrespectrumModTwoSteenrodCoaction

/-- A coaction datum can be evaluated at a prespectrum `T` to recover its chosen coaction map on
`H_*(T)`. -/
instance instCoeFun
    {cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w}}
    {cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation}
    {homologyPresentation : PrespectrumModTwoHomologyPresentation} :
    CoeFun
      (PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
      (fun _ ↦
        ∀ T : Prespectrum.{u, w},
          homologyPresentation.HStar T →ₗ[(ZMod 2)]
            modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)] homologyPresentation.HStar T) where
  coe coaction := coaction.gamma

/-- Evaluating a coaction datum as a function recovers its stored coaction map on `H_*(T)`. -/
@[simp] theorem coe_apply
    {cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w}}
    {cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation}
    {homologyPresentation : PrespectrumModTwoHomologyPresentation}
    (coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (T : Prespectrum.{u, w}) :
    coaction T = coaction.gamma T :=
  rfl

/-- The stored duality proof in a coaction datum gives the Kronecker-pairing formula for its
chosen coaction and pairing. -/
theorem duality_apply
    {cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w}}
    {cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation}
    {homologyPresentation : PrespectrumModTwoHomologyPresentation}
    (coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (T : Prespectrum.{u, w}) (x : homologyPresentation.HStar T)
    (a : ModTwoSteenrodAlgebra) (φ : cohomologyPresentation.HStar T) :
    -- Local instance justification (proof-local temporary data): the Steenrod scalar action in
    -- `a • φ` comes from the chosen cohomology action on `cohomologyPresentation.HStar T`.
    letI := cohomologyAction.module T
    coaction.kroneckerPairing T x (a • φ) =
      coaction.kroneckerPairing T
        ((dualTensorHom (ZMod 2) ModTwoSteenrodAlgebra (homologyPresentation.HStar T)
            (modTwoSteenrodAlgebraGradedDual.tensorInclusion
              (homologyPresentation.HStar T) (coaction.gamma T x))) a)
        φ :=
  coaction.duality T x a φ

end PrespectrumModTwoSteenrodCoaction
