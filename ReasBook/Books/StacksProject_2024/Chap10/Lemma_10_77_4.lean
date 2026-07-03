import Mathlib.Algebra.Module.Projective

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [Semiring R]
variable {ι : Type v} {M : ι → Type w}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module.Projective R (M i)]

/- Domain-style sampling in the projective-module owner API:
- primitive owner predicate: `Module.Projective R P`
- projective lifting characterization: `Module.projective_lifting_property`
- free modules are projective: `Module.Projective.of_free`
- direct-sum closure: the instance `Module.Projective R (Π₀ i, M i)` in
  `Mathlib.Algebra.Module.Projective`

Lemma 10.77.4 is a `core/canonical` recall item: the source statement is exactly the upstream
owner instance asserting that an arbitrary direct sum of projective modules is projective. The
primitive data is just the family `M`; projectivity of the direct sum is derived API supplied by
the owner abstraction, so no local wrapper or parallel theorem is introduced here.
-/
/- Lemma 10.77.4: a direct sum of projective `R`-modules is projective. In mathlib this is the
canonical owner instance `Module.Projective R (Π₀ i, M i)` attached to a family of projective
summands. -/
#check (inferInstance : Module.Projective R (Π₀ i, M i))

end
