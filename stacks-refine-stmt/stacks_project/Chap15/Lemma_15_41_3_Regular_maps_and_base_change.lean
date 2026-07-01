import stacks_project.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

namespace RingHom.IsRegularRingMap

universe u v w

section

variable {R : Type u} {R' : Type v} {Λ : Type w}
variable [CommRing R] [CommRing R'] [CommRing Λ]
variable [Algebra R Λ] [Algebra R R']
variable [Algebra.EssFiniteType R R']

/- Domain triage:
- primary domain: regular ring maps and tensor-product base change in commutative algebra;
- sampled owner declarations of the same kind:
  `RingHom.IsRegularRingMap`,
  `Algebra.IsGeometricallyRegular`,
  `Algebra.EssFiniteType`;
- best owner abstraction: the regularity datum already lives on the ring hom
  `algebraMap R Λ : R →+* Λ`, so the source-facing tensor-product statement should be exposed as a
  theorem in the owner namespace `RingHom.IsRegularRingMap` rather than through a parallel
  algebra-only wrapper namespace;
- primitive data: the algebra structures `R → Λ` and `R → R'`, together with
  `[Algebra.EssFiniteType R R']` and a proof `h : (algebraMap R Λ).IsRegularRingMap`;
- derived API: the regularity of the canonical base-change map
  `(algebraMap R' (R' ⊗[R] Λ)).IsRegularRingMap`, exposed by the exact owner theorem below with
  its essentially-finite-type hypothesis kept visible on the theorem surface.

Layering:
- `baseChange_of_essFiniteType` is `source-facing`;
- the core/canonical owner is `RingHom.IsRegularRingMap`;
- there is no additional bridge/view layer beyond the canonical tensor-product base change.
-/

-- Proof sketch: flatness is preserved by tensor base change along `R → R'`. For each prime
-- `p' : Spec R'`, compare the fiber of `R' → R' ⊗[R] Λ` over `p'` with the base change of the
-- fiber of `R → Λ` over the image prime in `R`, then use geometric regularity of fibers together
-- with the essentially-finite-type hypothesis on `R → R'`.
/-- Lemma 15.41.3 (Regular maps and base change): the base change of a regular ring map along a
essentially finite type ring map is again a regular ring map. -/
theorem baseChange_of_essFiniteType (h : (algebraMap R Λ).IsRegularRingMap) :
    (algebraMap R' (R' ⊗[R] Λ)).IsRegularRingMap := sorry

end

end RingHom.IsRegularRingMap
