import Mathlib
import StacksProject_2024.Chap29.Definition_29_10_1
import StacksProject_2024.Chap29.Lemma_29_35_11

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- Every fiber of `f` is a disjoint union of spectra of finite separable extensions of the
corresponding residue field. -/
def FibersAreDisjointUnionOfSpecFiniteSeparable {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ s : S,
    Nonempty
      (SchemeAsDisjointUnionOfSpecFiniteSeparable (S.residueField s)
        (Over.mk (f.fiberToSpecResidueField s)))

end Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side fiber owners
  `Scheme.Hom.fiber`, `Scheme.Hom.fiberOverSpecResidueField`, and `Scheme.Hom.residueFieldMap`;
- the ring-level dependencies are the residue-field finiteness/separability criterion
  `Algebra.isUnramifiedAt_iff_map_eq` and its finite/separable consequences from
  `Lemma_10_151_5.lean` and `Lemma_10_151_7.lean`;
- the fiber hypothesis is therefore recorded through the Chapter 29 owner
  `Scheme.Hom.FibersAreDisjointUnionOfSpecFiniteSeparable`, which packages the Chapter 29 fiber
  owner `SchemeAsDisjointUnionOfSpecFiniteSeparable` applied to `f.fiberToSpecResidueField s`.
-/

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- An unramified morphism has fibers that are disjoint unions of spectra of finite separable
extensions of the corresponding residue fields. -/
theorem Scheme.Hom.fibersAreDisjointUnionOfSpecFiniteSeparable_of_unramified
    (f : X ⟶ S) [Unramified f] :
    f.FibersAreDisjointUnionOfSpecFiniteSeparable :=
  fiber_schemeAsDisjointUnionOfSpecFiniteSeparable_of_unramified f

/-- Lemma 29.35.12 (1): if `f` is unramified, then for every `x : X` the induced residue-field
extension `κ(f(x)) → κ(x)` is finite separable. -/
@[stacks 02G8]
theorem residueField_finite_separable_of_unramified
    (f : X ⟶ S) [Unramified f] (x : X) :
    FiniteDimensional (S.residueField (f x)) (X.residueField x) ∧
      Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) := sorry

/-- For an unramified morphism, the residue-field extension at every point is finite. -/
theorem finiteDimensional_residueField_of_unramified
    (f : X ⟶ S) [Unramified f] (x : X) :
    FiniteDimensional (S.residueField (f x)) (X.residueField x) :=
  (residueField_finite_separable_of_unramified f x).1

/-- For an unramified morphism, the residue-field extension at every point is separable. -/
theorem isSeparable_residueField_of_unramified
    (f : X ⟶ S) [Unramified f] (x : X) :
    Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) :=
  (residueField_finite_separable_of_unramified f x).2

/-- Lemma 29.35.12 (2): if `f` is locally of finite type and every fiber of `f` is explicitly a
disjoint union of spectra of finite separable extensions of the corresponding residue field, then
`f` is unramified. -/
@[stacks 02G8]
theorem unramified_of_fiber_schemeAsDisjointUnionOfSpecFiniteSeparable
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (hfiber : f.FibersAreDisjointUnionOfSpecFiniteSeparable) :
    Unramified f := sorry

/-- Lemma 29.35.12 (3): if `f` is locally of finite presentation and every fiber of `f` is
explicitly a disjoint union of spectra of finite separable extensions of the corresponding residue
field, then `f` is G-unramified. -/
@[stacks 02G8]
theorem gUnramified_of_fiber_schemeAsDisjointUnionOfSpecFiniteSeparable
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (hfiber : f.FibersAreDisjointUnionOfSpecFiniteSeparable) :
    GUnramified f := sorry

end AlgebraicGeometry
