import Mathlib
import stacks_project.Chap10.Definition_10_135_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

open PrimeSpectrum

/- Source/core/bridge triage:
* source-facing: `RingHom.Syntomic`, the textbook property of a ring map being flat, finitely
  presented, and having local-complete-intersection fibers;
* core/canonical: the owner predicate on the ring homomorphism itself, with the three defining
  ingredients as primitive fields;
* bridge/view: the separate fiberwise predicate `HasLocalCompleteIntersectionFibers`.

The primitive data for syntomicity are exactly those three ingredients. Flatness and finite
presentation are not separate wrapper declarations here; they are projections of the owner
abstraction, matching the surrounding chapter style and mathlib's `Smooth`/`Etale` owners.
-/

/-- A ring homomorphism has local complete intersection fibers if each fiber over a prime of the
source is a local complete intersection over the corresponding residue field. -/
def HasLocalCompleteIntersectionFibers (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  ∀ p : PrimeSpectrum R, IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S)

/-- Definition 10.136.1: a ring homomorphism is syntomic if it is flat, of finite presentation,
and all of its fibers are local complete intersections. -/
def Syntomic (f : R →+* S) : Prop :=
  f.Flat ∧ f.FinitePresentation ∧ f.HasLocalCompleteIntersectionFibers

namespace Syntomic

theorem flat {f : R →+* S} (hf : f.Syntomic) : f.Flat :=
  hf.1

theorem finitePresentation {f : R →+* S} (hf : f.Syntomic) : f.FinitePresentation :=
  hf.2.1

theorem hasLocalCompleteIntersectionFibers {f : R →+* S} (hf : f.Syntomic) :
    f.HasLocalCompleteIntersectionFibers :=
  hf.2.2

end Syntomic

end RingHom

end

namespace Algebra

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]

-- Proof sketch: over a field every module is flat, and a local complete intersection `k`-algebra
-- is finite type by definition, hence finite presentation over the Noetherian base field `k`. The
-- only fiber of `Spec A → Spec k` is the fiber over `(0)`, which is canonically `A` itself.
/-- A local complete intersection algebra over a field is syntomic. -/
theorem syntomic_of_isLocalCompleteIntersection [IsLocalCompleteIntersection k A] :
    (algebraMap k A).Syntomic := sorry

end

end Algebra
