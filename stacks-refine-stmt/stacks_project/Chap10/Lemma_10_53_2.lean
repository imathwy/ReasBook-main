import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain triage:
- primary domain: finite-dimensional algebras and Artinian rings;
- sampled owner declarations: `IsArtinianRing.of_finite`,
  `isArtinian_of_fg_of_artinian`, and `isArtinian_of_tower`;
- best owner abstraction: the canonical owner is the typeclass `IsArtinianRing A`;
- primitive data: the ambient field `k`, the `k`-algebra `A`, and the finite-dimensionality
  hypothesis;
- derived API: the Artinian-ring structure on `A`, obtained from the canonical bridge
  `FiniteDimensional k A → Module.Finite k A`.

Source/core/bridge triage:
- `source-facing`: the field-specialized statement that a finite-dimensional `k`-algebra is
  Artinian;
- `core/canonical`: `IsArtinianRing A`;
- `bridge/view`: the theorem `IsArtinianRing.of_finite`, which promotes finite module structure
  over an Artinian base ring to an Artinian target ring. -/

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/- Lemma 10.53.2: a finite-dimensional algebra over a field is an Artinian ring.

This is exactly the field-specialized source wording of the canonical mathlib theorem
`IsArtinianRing.of_finite`. -/
recall IsArtinianRing.of_finite
