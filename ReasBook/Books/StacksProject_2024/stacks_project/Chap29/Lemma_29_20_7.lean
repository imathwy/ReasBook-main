import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)

/- Semantic recall:
- `lean_leansearch` surfaced the canonical scheme-theoretic fiber owner `Scheme.Hom.fiber`,
  the finite-morphism fiber instances, and the pointwise owner `Scheme.Hom.QuasiFiniteAt`.
- Local Chapter 29 precedent confirms that the fiber over `s : S` is written
  `Scheme.Hom.fiber f s` and quasi-finiteness at `x : X` is written `f.QuasiFiniteAt x`.
-/

/-- Lemma 29.20.7 (1): if `f : X ⟶ S` is locally of finite type and the inverse image of
`{s}` is finite, then the scheme-theoretic fiber `X_s` has finitely many points. -/
@[stacks 02NG]
theorem finite_fiber_of_locallyOfFiniteType_finite_preimage_singleton
    [LocallyOfFiniteType f]
    (hs : Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S))) :
    Finite (Scheme.Hom.fiber f s) := sorry

/-- Lemma 29.20.7 (2): if `f : X ⟶ S` is locally of finite type and the inverse image of
`{s}` is finite, then the scheme-theoretic fiber `X_s` is discrete. -/
@[stacks 02NG]
theorem discreteTopology_fiber_of_locallyOfFiniteType_finite_preimage_singleton
    [LocallyOfFiniteType f]
    (hs : Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S))) :
    DiscreteTopology (Scheme.Hom.fiber f s) := sorry

/-- Lemma 29.20.7 (3): if `f : X ⟶ S` is locally of finite type and the inverse image of
`{s}` is finite, then `f` is quasi-finite at every point of `X` lying over `s`. -/
@[stacks 02NG]
theorem quasiFiniteAt_of_locallyOfFiniteType_finite_preimage_singleton
    [LocallyOfFiniteType f]
    (hs : Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S)))
    {x : X} (hx : f x = s) :
    f.QuasiFiniteAt x := sorry

end AlgebraicGeometry
