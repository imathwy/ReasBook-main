import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_4_9.Homology

noncomputable section

universe u w

/-- The degree-`n` summand in the chosen total homology object `H_*(T)`. -/
abbrev prespectrumModTwoHomologyDegree
    (T : RingPrespectrum.{u, w})
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (n : ℕ) : Type _ :=
  ((connectivePrespectrumReducedHomology
      T.toPrespectrum
      (homologyPresentation.homologyPresentation T.toPrespectrum))
    (n : ℤ)).obj homologyPresentation.sphereZero

/-- Unfolding `prespectrumModTwoHomologyDegree` recovers the degree-`n` reduced homology group
used in the chosen presentation of `H_*(T)`. -/
theorem prespectrumModTwoHomologyDegree_def
    (T : RingPrespectrum.{u, w})
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (n : ℕ) :
    prespectrumModTwoHomologyDegree T homologyPresentation n =
      ((connectivePrespectrumReducedHomology
          T.toPrespectrum
          (homologyPresentation.homologyPresentation T.toPrespectrum))
        (n : ℤ)).obj homologyPresentation.sphereZero :=
  rfl

/-- The preexisting additive commutative group structure on the chosen total homology object
`H_*(T)`. -/
abbrev prespectrumModTwoHomologyStarAddCommGroup
    (T : RingPrespectrum.{u, w})
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w}) :
    AddCommGroup (homologyPresentation.HStar T.toPrespectrum) :=
  inferInstance

/-- A chosen `ZMod 2`-algebra structure on `H_*(T)` whose underlying additive commutative group,
unit, and multiplication agree with the source-semantic direct-sum homology object and the
degreewise multiplication induced by the ring prespectrum structure on `T`. -/
class PrespectrumModTwoHomologyAlgebra
    (T : RingPrespectrum.{u, w})
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    extends Ring (homologyPresentation.HStar T.toPrespectrum),
      Algebra (ZMod 2) (homologyPresentation.HStar T.toPrespectrum) where
  /-- The additive commutative group induced by the chosen ring structure on `H_*(T)` agrees
  with the preexisting direct-sum additive structure. -/
  addCommGroup_eq :
    toRing.toAddCommGroup = prespectrumModTwoHomologyStarAddCommGroup T homologyPresentation
  /-- The multiplicative unit in the chosen ring structure on `H_*(T)` is represented by a
  distinguished degree-`0` homology class. -/
  oneClass : prespectrumModTwoHomologyDegree T homologyPresentation 0
  /-- The chosen degree-`0` class maps to the ring unit in `H_*(T)`. -/
  one_eq :
    let _ : Ring (homologyPresentation.HStar T.toPrespectrum) := toRing
    DirectSum.lof ℤ ℕ
      (fun n ↦ prespectrumModTwoHomologyDegree T homologyPresentation n)
      0 oneClass =
        (1 : homologyPresentation.HStar T.toPrespectrum)
  /-- The degreewise multiplication induced by the ring prespectrum structure on `T`. -/
  mulHomogeneous (p q : ℕ)
      (x : prespectrumModTwoHomologyDegree T homologyPresentation p)
      (y : prespectrumModTwoHomologyDegree T homologyPresentation q) :
      prespectrumModTwoHomologyDegree T homologyPresentation (p + q)
  /-- Multiplication in the total homology ring is induced on homogeneous classes by the chosen
  degreewise product maps. -/
  lof_mul_eq (p q : ℕ)
      (x : prespectrumModTwoHomologyDegree T homologyPresentation p)
      (y : prespectrumModTwoHomologyDegree T homologyPresentation q) :
      let _ : Ring (homologyPresentation.HStar T.toPrespectrum) := toRing
      DirectSum.lof ℤ ℕ
        (fun n ↦ prespectrumModTwoHomologyDegree T homologyPresentation n)
        p x *
        DirectSum.lof ℤ ℕ
        (fun n ↦ prespectrumModTwoHomologyDegree T homologyPresentation n)
        q y =
          DirectSum.lof ℤ ℕ
          (fun n ↦ prespectrumModTwoHomologyDegree T homologyPresentation n)
          (p + q) (mulHomogeneous p q x y)

/-- The chosen `ZMod 2`-algebra structure on `H_*(T)` is compatible with the preexisting
direct-sum additive commutative group and with the source-semantic unit and multiplication on the
homology of the ring prespectrum `T`. -/
theorem prespectrumModTwoHomologyAlgebra_spec
    (T : RingPrespectrum.{u, w})
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    [HStarAlg : PrespectrumModTwoHomologyAlgebra T homologyPresentation] :
    (HStarAlg.toRing.toAddCommGroup =
        prespectrumModTwoHomologyStarAddCommGroup T homologyPresentation) ∧
      (DirectSum.lof ℤ ℕ
          (fun n ↦ prespectrumModTwoHomologyDegree T homologyPresentation n)
          0 HStarAlg.oneClass =
        (1 : homologyPresentation.HStar T.toPrespectrum)) ∧
      (∀ p q : ℕ,
        ∀ x : prespectrumModTwoHomologyDegree T homologyPresentation p,
        ∀ y : prespectrumModTwoHomologyDegree T homologyPresentation q,
          DirectSum.lof ℤ ℕ
              (fun n ↦ prespectrumModTwoHomologyDegree T homologyPresentation n)
              p x *
            DirectSum.lof ℤ ℕ
              (fun n ↦ prespectrumModTwoHomologyDegree T homologyPresentation n)
              q y =
              DirectSum.lof ℤ ℕ
                (fun n ↦ prespectrumModTwoHomologyDegree T homologyPresentation n)
                (p + q) (HStarAlg.mulHomogeneous p q x y)) :=
  ⟨HStarAlg.addCommGroup_eq, HStarAlg.one_eq, HStarAlg.lof_mul_eq⟩
