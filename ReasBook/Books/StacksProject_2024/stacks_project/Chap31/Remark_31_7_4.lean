import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {S S' : Scheme.{u}}

-- Semantic recall: `lean_leansearch` recalled the canonical owners `LocallyQuasiFinite` and
-- `Scheme.Hom.residueFieldMap`. Local Chapter 31 precedent fixes the source-facing set as
-- `Scheme.Modules.relativeAssassin`; the algebraic residue-field condition below is the
-- source-visible hypothesis used with Algebra, Lemma 10.36.19.

/-- A morphism of schemes has algebraic residue-field extensions if each induced extension
`κ(g(s')) → κ(s')` is algebraic. -/
def HasAlgebraicResidueFieldExtensions (g : S' ⟶ S) : Prop :=
  ∀ s' : S',
    let _ : Algebra (S.residueField (g s')) (S'.residueField s') :=
      (Scheme.Hom.residueFieldMap g s').hom.toAlgebra
    Algebra.IsAlgebraic (S.residueField (g s')) (S'.residueField s')

/-- Unfold the algebraicity condition on residue-field extensions induced by a scheme morphism. -/
theorem hasAlgebraicResidueFieldExtensions_iff (g : S' ⟶ S) :
    HasAlgebraicResidueFieldExtensions g ↔
      ∀ s' : S',
        let _ : Algebra (S.residueField (g s')) (S'.residueField s') :=
          (Scheme.Hom.residueFieldMap g s').hom.toAlgebra
        Algebra.IsAlgebraic (S.residueField (g s')) (S'.residueField s') := sorry

/-- A locally quasi-finite morphism has algebraic residue-field extensions. -/
theorem hasAlgebraicResidueFieldExtensions_of_locallyQuasiFinite
    (g : S' ⟶ S) [LocallyQuasiFinite g] :
    HasAlgebraicResidueFieldExtensions g := sorry

end Scheme.Hom

namespace Scheme.Modules

/-- Remark 31.7.4 (1): with notation and assumptions as in Lemma 31.7.3, the inverse image of
the relative assassin on `X` always contains the relative assassin after base change. -/
@[stacks 05KL]
theorem relativeAssassin_pullback_subset_preimage_relativeAssassin_baseChange
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    relativeAssassin f' ((Scheme.Modules.pullback g').obj ℱ) ⊆
      g' ⁻¹' relativeAssassin f ℱ := sorry

/-- Remark 31.7.4 (2): if the base-change morphism `S' → S` is locally quasi-finite, then the
inverse image of the relative assassin on `X` equals the relative assassin after base change. -/
@[stacks 05KL]
theorem preimage_relativeAssassin_eq_relativeAssassin_pullback_of_locallyQuasiFinite
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    [LocallyQuasiFinite g] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    g' ⁻¹' relativeAssassin f ℱ =
      relativeAssassin f' ((Scheme.Modules.pullback g').obj ℱ) := sorry

/-- Remark 31.7.4 (3): the same equality holds more generally when all residue-field extensions
`κ(g(s')) → κ(s')` induced by `g : S' ⟶ S` are algebraic. -/
@[stacks 05KL]
theorem preimage_relativeAssassin_eq_relativeAssassin_pullback_of_hasAlgebraicResidueFieldExtensions
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (hg : Scheme.Hom.HasAlgebraicResidueFieldExtensions g)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    g' ⁻¹' relativeAssassin f ℱ =
      relativeAssassin f' ((Scheme.Modules.pullback g').obj ℱ) := sorry

end Scheme.Modules
end AlgebraicGeometry
