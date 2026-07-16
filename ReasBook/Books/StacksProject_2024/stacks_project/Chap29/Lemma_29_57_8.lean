import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_57_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.IsEtale` and the separable
-- closure API. Local Section 29.57 precedent fixes `degreesOfFibresBoundedBy`, and Chapter 29
-- uses `pullback f g` for field-valued base changes and `Y.fromSpecResidueField y` for the
-- residue-field point over `y`.

/-- Lemma 29.57.8: for an étale morphism `f : X ⟶ Y` and a natural number `n`, the following
are equivalent: `n` bounds the degrees of the fibres of `f`; every field-valued base change
`Spec(k) ×[Y] X` has at most `n` points; and after base change to every separable algebraic
closure of every residue field `κ(y)`, the resulting fibre has at most `n` points. -/
@[stacks 03WU]
theorem degreesOfFibresBoundedBy_tfae_card_le_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (n : ℕ) :
    List.TFAE
      [ degreesOfFibresBoundedBy f n
      , ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
          Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n
      , ∀ y : Y, ∀ (K : Type u) [Field K] [Algebra (Y.residueField y) K]
          [Algebra.IsAlgebraic (Y.residueField y) K]
          [Algebra.IsSeparable (Y.residueField y) K] [IsSepClosed K],
          let g : Spec (CommRingCat.of K) ⟶ Y :=
            Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
              Y.fromSpecResidueField y
          Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n
      ] := sorry

end Scheme.Hom
end AlgebraicGeometry
