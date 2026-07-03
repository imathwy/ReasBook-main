import Mathlib
import stacks_project.Chap15.Definition_15_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat

universe u v

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- A ring map is finite free if it is finite and its codomain is a free module over the source via
the induced algebra structure. -/
abbrev FiniteFree (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  RingHom.Finite f ∧ Module.Free R A

/-- An `R`-algebra map `f : R →+* A` is a filtered colimit of finite free `R`-algebras. This thin
source-facing wrapper hides the same-universe `ULift` presentation of the canonical owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.FiniteFree)`. -/
abbrev IsFilteredColimitOfFiniteFree (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift A) := ULift.algebra' R (ULift A)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty FiniteFree)
    (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift A)))

end

end RingHom

section

variable (A : Type u) [CommRing A]

/-
Domain-style sampling for Lemma 15.14.6:
- primary domain: commutative algebra of absolutely integrally closed extensions and filtered
  colimit presentations of ring maps;
- sampled owner-level declarations:
  `RingHom.Finite`,
  `RingHom.FiniteFree`,
  `RingHom.IsFilteredColimitOfFiniteFree`,
  `RingHom.toMorphismProperty`,
  `IsAbsolutelyIntegrallyClosed`,
  `IsAbsolutelyIntegrallyClosed.exists_root`,
  `RingHom.finite_algebraMap`;
- best owner abstraction: the theorem is `source-facing`, but its filtered-colimit hypothesis
  should use the chapter-style ring-hom owner `(algebraMap A B).IsFilteredColimitOfFiniteFree`,
  whose hidden core/canonical content is
  `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.FiniteFree)`;
  absolute integral closedness should use the chapter owner `IsAbsolutelyIntegrallyClosed B`;
- primitive data: an injective `A`-algebra structure on `B`, freeness of `B` over `A`, and the
  owner-level filtered-colimit predicate `(algebraMap A B).IsFilteredColimitOfFiniteFree`;
- derived API: root existence for monic polynomials over `B`, obtained from
  `IsAbsolutelyIntegrallyClosed B`.

Source/core/bridge triage:
- `source-facing`: `exists_absolutely_integrally_closed_free_extension`;
- `core/canonical`: `IsAbsolutelyIntegrallyClosed`, `RingHom.Finite`,
  `RingHom.FiniteFree`, `RingHom.IsFilteredColimitOfFiniteFree`;
- `bridge/view`: the hidden same-universe `ULift` presentation inside
  `RingHom.IsFilteredColimitOfFiniteFree`.
-/

-- Proof sketch: build the endofunctor `F(A)` adjoining roots of all monic polynomials over `A`,
-- note that each `F(A)` is free over `A` and a filtered colimit of finite free `A`-algebras, and
-- then take the directed colimit of the iterates `Fⁿ(A)`. Lemma `15.14.2` identifies the final
-- root-existence statement with `IsAbsolutelyIntegrallyClosed`.
/-- Lemma 15.14.6: for any commutative ring `A`, there exists an injective `A`-algebra `B` such
that `B` is free as an `A`-module, `B` is a filtered colimit of finite free `A`-algebras, and
`B` is absolutely integrally closed. -/
theorem exists_absolutely_integrally_closed_free_extension :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Function.Injective (algebraMap A B) ∧
      Module.Free A B ∧
      (algebraMap A B).IsFilteredColimitOfFiniteFree ∧
      IsAbsolutelyIntegrallyClosed B := by
  sorry

end
