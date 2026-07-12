import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` and the mathlib source point to the canonical owner
-- `Scheme.Hom.QuasiFiniteAt`, together with `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`.
-- This item keeps the textbook surface directly in terms of the point of the fiber and the residue
-- field extension.

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The canonical algebra structure on residue fields induced by a morphism of schemes at a point. -/
instance residueFieldAlgebraAtPoint (x : X) :
    Algebra (S.residueField (f x)) (X.residueField x) :=
  (f.residueFieldMap x).hom.toAlgebra

/-- Lemma 29.20.3: let `f : X ⟶ S` be a morphism of schemes and let `x : X` with image `f x`.
Assume `f` is locally of finite type. Then `x` is a closed point of its fiber if and only if the
residue field extension `κ(x) / κ(f(x))` is finite. -/
@[stacks 01TF]
theorem asFiber_mem_closedPoints_iff_moduleFinite_residueField
    [LocallyOfFiniteType f] (x : X) :
    f.asFiber x ∈ closedPoints (f.fiber (f x)) ↔
      Module.Finite (S.residueField (f x)) (X.residueField x) := sorry

end AlgebraicGeometry
