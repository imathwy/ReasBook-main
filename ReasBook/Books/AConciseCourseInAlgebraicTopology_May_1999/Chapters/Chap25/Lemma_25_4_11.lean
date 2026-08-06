import Mathlib.RingTheory.TensorProduct.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_4_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_11.HomologyAlgebra

open scoped TensorProduct

noncomputable section

universe u w

-- The reusable source-facing homology-algebra owner for `H_*(T)` lives in the item-local
-- foundation module `Lemma_25_4_11.HomologyAlgebra`, so later files can import that API directly
-- without importing this labeled lemma file.

/-- The preexisting additive commutative group structure on the tensor-product target
`A_* ⊗[(ZMod 2)] H_*(T)` of the coaction. -/
private abbrev prespectrumModTwoSteenrodCoactionTargetAddCommGroup
    (T : RingPrespectrum.{u, w})
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w}) :
    AddCommGroup
      (modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)]
        homologyPresentation.HStar T.toPrespectrum) :=
  inferInstance

/-- A chosen `ZMod 2`-algebra structure on `A_* ⊗[(ZMod 2)] H_*(T)` for which the ambient
ring/algebra operations are the tensor-product ones relative to the chosen dual Steenrod algebra
owner `AStar` and the chosen homology algebra structure on `H_*(T)`. -/
class PrespectrumModTwoSteenrodCoactionTargetAlgebra
    (T : RingPrespectrum.{u, w})
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    extends Ring
      (modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)]
        homologyPresentation.HStar T.toPrespectrum),
      Algebra
      (ZMod 2)
      (modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)]
        homologyPresentation.HStar T.toPrespectrum) where
  /-- The additive commutative group induced by the chosen tensor-product ring structure agrees
  with the preexisting additive structure on `A_* ⊗[(ZMod 2)] H_*(T)`. -/
  addCommGroup_eq :
    toRing.toAddCommGroup =
      prespectrumModTwoSteenrodCoactionTargetAddCommGroup T homologyPresentation
  /-- The multiplicative unit on the chosen tensor-product algebra is the tensor product of the
  units on `A_*` and `H_*(T)`. -/
  one_eq :
    (1 :
      modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)]
        homologyPresentation.HStar T.toPrespectrum) =
      (ModTwoSteenrodAlgebraDualAlgebra.one AStar ⊗ₜ[ZMod 2]
        (1 : homologyPresentation.HStar T.toPrespectrum))
  /-- Multiplication on the chosen tensor-product algebra is the tensor-product multiplication
  induced from `A_*` and `H_*(T)`. -/
  tmul_mul_tmul
      (a b : modTwoSteenrodAlgebraGradedDual)
      (x y : homologyPresentation.HStar T.toPrespectrum) :
      (a ⊗ₜ[ZMod 2] x :
          modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)]
            homologyPresentation.HStar T.toPrespectrum) *
        (b ⊗ₜ[ZMod 2] y) =
          AStar.toRing.mul a b ⊗ₜ[ZMod 2] (x * y)

/-- The chosen tensor-product algebra on `A_* ⊗[(ZMod 2)] H_*(T)` is compatible with the
preexisting additive structure and has the expected tensor-product unit and multiplication. -/
theorem prespectrumModTwoSteenrodCoactionTargetAlgebra_spec
    (T : RingPrespectrum.{u, w})
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    [targetAlgebra :
      PrespectrumModTwoSteenrodCoactionTargetAlgebra T homologyPresentation AStar] :
    (targetAlgebra.toRing.toAddCommGroup =
        prespectrumModTwoSteenrodCoactionTargetAddCommGroup T homologyPresentation) ∧
      (1 :
        modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)]
          homologyPresentation.HStar T.toPrespectrum) =
        (ModTwoSteenrodAlgebraDualAlgebra.one AStar ⊗ₜ[ZMod 2]
          (1 : homologyPresentation.HStar T.toPrespectrum)) ∧
      (∀ a b : modTwoSteenrodAlgebraGradedDual,
        ∀ x y : homologyPresentation.HStar T.toPrespectrum,
          (a ⊗ₜ[ZMod 2] x :
              modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)]
                homologyPresentation.HStar T.toPrespectrum) *
            (b ⊗ₜ[ZMod 2] y) =
              AStar.toRing.mul a b ⊗ₜ[ZMod 2] (x * y)) :=
  ⟨targetAlgebra.addCommGroup_eq, targetAlgebra.one_eq, targetAlgebra.tmul_mul_tmul⟩

/-- The coaction from Construction 25.4.9 sends `1` to `1` under the chosen algebra structures on
`H_*(T)` and `A_* ⊗[(ZMod 2)] H_*(T)`. -/
theorem prespectrumModTwoSteenrodCoaction_map_one
    (T : RingPrespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    [PrespectrumModTwoSteenrodCoactionTargetAlgebra T homologyPresentation AStar] :
    coaction.gamma T.toPrespectrum 1 = 1 := sorry

/-- The coaction from Construction 25.4.9 preserves multiplication on `H_*(T)` under the chosen
source and target algebra structures. -/
theorem prespectrumModTwoSteenrodCoaction_map_mul
    (T : RingPrespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    [PrespectrumModTwoSteenrodCoactionTargetAlgebra T homologyPresentation AStar]
    (x y : homologyPresentation.HStar T.toPrespectrum) :
    coaction.gamma T.toPrespectrum (x * y) =
      coaction.gamma T.toPrespectrum x * coaction.gamma T.toPrespectrum y := sorry

/-- The coaction from Construction 25.4.9 commutes with the `ZMod 2`-algebra maps on the chosen
source and target algebra structures. -/
theorem prespectrumModTwoSteenrodCoaction_commutes
    (T : RingPrespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    [PrespectrumModTwoSteenrodCoactionTargetAlgebra T homologyPresentation AStar]
    (r : ZMod 2) :
    coaction.gamma T.toPrespectrum
        (algebraMap (ZMod 2) (homologyPresentation.HStar T.toPrespectrum) r) =
      algebraMap
        (ZMod 2)
        (modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)]
          homologyPresentation.HStar T.toPrespectrum) r := sorry

/-- A companion package for Lemma 25.4.11 recording one chosen dual Steenrod algebra owner
`A_*` and one chosen compatible algebra structure on `A_* ⊗[(ZMod 2)] H_*(T)`, in the ambient
context of a chosen source-semantic algebra structure on `H_*(T)`. The resulting coaction
algebra homomorphism is recovered by the derived namespace API `datum.algHom`. -/
structure PrespectrumModTwoSteenrodCoactionAlgHomDatum
    (T : RingPrespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation] where
  /-- The chosen source-semantic dual Steenrod algebra owner on `A_*`. -/
  AStar : ModTwoSteenrodAlgebraDualAlgebra
  /-- The chosen target algebra owner on `A_* ⊗[(ZMod 2)] H_*(T)`. -/
  targetAlgebra :
    PrespectrumModTwoSteenrodCoactionTargetAlgebra T homologyPresentation AStar

/-- Lemma 25.4.11: if `T` is an associative ring prespectrum, then the coaction
`gamma : H_*(T) → A_* ⊗[(ZMod 2)] H_*(T)` from Construction 25.4.9 is an algebra homomorphism.
For a chosen dual Steenrod algebra owner `AStar : ModTwoSteenrodAlgebraDualAlgebra`, a chosen
source-semantic `ZMod 2`-algebra structure on `H_*(T)`, and a chosen source-semantic
`ZMod 2`-algebra structure on `A_* ⊗[(ZMod 2)] H_*(T)`, this declaration packages
`coaction.gamma T.toPrespectrum` itself as the corresponding `ZMod 2`-algebra homomorphism.
The auxiliary package `PrespectrumModTwoSteenrodCoactionAlgHomDatum` remains companion API. -/
noncomputable def prespectrumModTwoSteenrodCoactionAlgHom
    (T : RingPrespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    [homologyAlgebra : PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    [targetAlgebra : PrespectrumModTwoSteenrodCoactionTargetAlgebra
      T homologyPresentation AStar] :
    homologyPresentation.HStar T.toPrespectrum →ₐ[ZMod 2]
      modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)]
        homologyPresentation.HStar T.toPrespectrum :=
  { toFun := coaction.gamma T.toPrespectrum
    map_zero' := by
      sorry
    map_add' := by
      sorry
    map_one' := prespectrumModTwoSteenrodCoaction_map_one
      T cohomologyPresentation cohomologyAction homologyPresentation coaction AStar
    map_mul' := prespectrumModTwoSteenrodCoaction_map_mul
      T cohomologyPresentation cohomologyAction homologyPresentation coaction AStar
    commutes' := prespectrumModTwoSteenrodCoaction_commutes
      T cohomologyPresentation cohomologyAction homologyPresentation coaction AStar }

/-- Evaluating the algebra homomorphism from Lemma 25.4.11 recovers the coaction map from
Construction 25.4.9. -/
@[simp]
theorem prespectrumModTwoSteenrodCoactionAlgHom_apply
    (T : RingPrespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    [PrespectrumModTwoSteenrodCoactionTargetAlgebra T homologyPresentation AStar]
    (x : homologyPresentation.HStar T.toPrespectrum) :
    prespectrumModTwoSteenrodCoactionAlgHom
        T cohomologyPresentation cohomologyAction homologyPresentation
        coaction AStar x =
      coaction.gamma T.toPrespectrum x :=
  rfl

namespace PrespectrumModTwoSteenrodCoactionAlgHomDatum

/-- The tensor-product codomain determined by a companion datum. -/
abbrev Target
    {T : RingPrespectrum.{u, w}}
    {cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w}}
    {cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation}
    {homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w}}
    {coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation}
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    (_ :
      PrespectrumModTwoSteenrodCoactionAlgHomDatum
        T cohomologyPresentation cohomologyAction homologyPresentation coaction) : Type _ :=
  modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)]
    homologyPresentation.HStar T.toPrespectrum

instance instTargetRing
    {T : RingPrespectrum.{u, w}}
    {cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w}}
    {cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation}
    {homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w}}
    {coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation}
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    (datum :
      PrespectrumModTwoSteenrodCoactionAlgHomDatum
        T cohomologyPresentation cohomologyAction homologyPresentation coaction) :
    Ring (Target datum) :=
  datum.targetAlgebra.toRing

instance instTargetAlgebraZMod
    {T : RingPrespectrum.{u, w}}
    {cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w}}
    {cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation}
    {homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w}}
    {coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation}
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    (datum :
      PrespectrumModTwoSteenrodCoactionAlgHomDatum
        T cohomologyPresentation cohomologyAction homologyPresentation coaction) :
    Algebra (ZMod 2) (Target datum) :=
  datum.targetAlgebra.toAlgebra

instance instTargetAlgebra
    {T : RingPrespectrum.{u, w}}
    {cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w}}
    {cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation}
    {homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w}}
    {coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation}
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    (datum :
      PrespectrumModTwoSteenrodCoactionAlgHomDatum
        T cohomologyPresentation cohomologyAction homologyPresentation coaction) :
    PrespectrumModTwoSteenrodCoactionTargetAlgebra
      T homologyPresentation datum.AStar :=
  datum.targetAlgebra

/-- The companion datum canonically recovers the coaction algebra homomorphism from
Lemma 25.4.11. -/
noncomputable def algHom
    {T : RingPrespectrum.{u, w}}
    {cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w}}
    {cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation}
    {homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w}}
    {coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation}
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    (datum :
      PrespectrumModTwoSteenrodCoactionAlgHomDatum
        T cohomologyPresentation cohomologyAction homologyPresentation coaction) :
    homologyPresentation.HStar T.toPrespectrum →ₐ[ZMod 2] Target datum :=
  prespectrumModTwoSteenrodCoactionAlgHom
    T cohomologyPresentation cohomologyAction homologyPresentation coaction datum.AStar

/-- Evaluating the algebra homomorphism recovered from a companion datum gives the chosen
coaction map from Construction 25.4.9. -/
@[simp] theorem algHom_apply
    {T : RingPrespectrum.{u, w}}
    {cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w}}
    {cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation}
    {homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w}}
    {coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation}
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    (datum :
      PrespectrumModTwoSteenrodCoactionAlgHomDatum
        T cohomologyPresentation cohomologyAction homologyPresentation coaction)
    (x : homologyPresentation.HStar T.toPrespectrum) :
    datum.algHom x = coaction.gamma T.toPrespectrum x :=
  prespectrumModTwoSteenrodCoactionAlgHom_apply
    T cohomologyPresentation cohomologyAction homologyPresentation coaction datum.AStar x

end PrespectrumModTwoSteenrodCoactionAlgHomDatum

/-- The direct algebra homomorphism from Lemma 25.4.11 yields the companion datum recording the
chosen dual Steenrod algebra owner and the chosen source and target algebra structures. -/
noncomputable def prespectrumModTwoSteenrodCoaction_algHomDatum
    (T : RingPrespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    [homologyAlgebra : PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    [targetAlgebra : PrespectrumModTwoSteenrodCoactionTargetAlgebra
      T homologyPresentation AStar] :
    PrespectrumModTwoSteenrodCoactionAlgHomDatum
      T cohomologyPresentation cohomologyAction homologyPresentation coaction :=
  { AStar := AStar
    targetAlgebra := targetAlgebra }

/-- Evaluating the algebra homomorphism stored in a chosen companion datum recovers the coaction
map from Construction 25.4.9. -/
@[simp]
theorem prespectrumModTwoSteenrodCoactionAlgHomDatum_apply
    (T : RingPrespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (coaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    [PrespectrumModTwoHomologyAlgebra T homologyPresentation]
    (datum :
      PrespectrumModTwoSteenrodCoactionAlgHomDatum
        T cohomologyPresentation cohomologyAction homologyPresentation coaction)
    (x : homologyPresentation.HStar T.toPrespectrum) :
    datum.algHom x = coaction.gamma T.toPrespectrum x :=
  PrespectrumModTwoSteenrodCoactionAlgHomDatum.algHom_apply datum x
