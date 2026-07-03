import Mathlib
import StacksProject_2024.Chap20.Lemma_20_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "Cpx" => CochainComplex (RingedSpace.Modules X) ℤ

/-- A bounded-below flasque replacement of a complex together with the quasi-isomorphism from the
original complex and the pointwise homotopy-equivalence property after pullback to each one-point
ringed space. -/
structure BoundedBelowFlasqueReplacementWithPointwiseHomotopy
    (X : RingedSpace.{u}) (F : CochainComplex (RingedSpace.Modules X) ℤ) where
  /-- The replacement complex. -/
  G : CochainComplex (RingedSpace.Modules X) ℤ
  /-- The augmentation map from the original complex to the replacement. -/
  φ : F ⟶ G
  /-- The augmentation map is a quasi-isomorphism. -/
  quasiIso : QuasiIso φ
  /-- The replacement complex is bounded below. -/
  boundedBelow : ∃ m : ℤ, G.IsStrictlyGE m
  /-- Each term of the replacement complex is a flasque `\mathcal O_X`-module sheaf. -/
  termwise_flasque :
      ∀ n : ℤ,
        TopCat.Sheaf.IsFlasque
          ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj (G.X n))
  /-- After pullback to each one-point ringed space, the augmentation is a homotopy equivalence. -/
  pointwise_homotopy :
      ∀ x : X,
        HomologicalComplex.homotopyEquivalences
          (SheafOfModules (pointRingedSpace (RingedSpace.ringCatSheaf x)))
          (ComplexShape.up ℤ)
          (((RingedSpace.Hom.pullback (pointInclusion x)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)

-- Proof sketch: apply Lemma `20.30.1` in the abelian category of complexes of
-- `\mathcal O_X`-modules to obtain a termwise Godement resolution of `F`. Totalizing the resulting
-- double complex gives a bounded below complex `G` whose terms are finite direct sums of flasque
-- sheaves, hence flasque. The one-point pullback of the augmentation is a homotopy equivalence by
-- the stalkwise version of the Godement construction together with the totalization lemma
-- `12.25.5`, and therefore the augmentation is a quasi-isomorphism.
/-- Lemma 20.30.2: if `\mathcal F^\bullet` is a bounded below complex of `\mathcal O_X`-modules on
a ringed space `(X, \mathcal O_X)`, then there exists a quasi-isomorphism
`\mathcal F^\bullet \to \mathcal G^\bullet` with `\mathcal G^\bullet` bounded below and termwise
flasque. The final clause is stated in the canonical project form: after pullback to each one-point
ringed space `({x}, \mathcal O_{X, x})`, the induced map of complexes is a homotopy equivalence;
equivalently, the induced stalk map `\mathcal F^\bullet_x \to \mathcal G^\bullet_x` is a homotopy
equivalence in complexes of `\mathcal O_{X, x}`-modules. -/
theorem exists_quasiIso_to_termwise_flasque_of_boundedBelow_with_pointwise_homotopy
    (F : Cpx) (hF : ∃ m : ℤ, F.IsStrictlyGE m) :
    Nonempty (BoundedBelowFlasqueReplacementWithPointwiseHomotopy X F) := sorry

end AlgebraicGeometry.RingedSpace
