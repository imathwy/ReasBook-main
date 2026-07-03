import Mathlib
import stacks_project.Chap15.Lemma_15_51_3
import stacks_project.Chap15.Lemma_15_51_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

section

variable (P : FieldAlgebraProperty)

variable {A : Type u} [CommRing A]
variable (I : Ideal A)
variable [P.HasPropertyB] [P.HasPropertyD]

/- Domain sampling pass:
- primary domain: Chapter 15 formal fibers of adic completion maps for `P`-rings in Noetherian
  commutative algebra;
- sampled owner declarations:
  `IsPRing`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyD`,
  `completed_localization_formalFibers_haveProperty_of_quasiFiniteAt`,
  `LocalFormalFibersHaveProperty`;
- best owner abstraction: the source-facing owner is still `IsPRing P A`; this lemma is not a new
  owner, but a `bridge/view` from the local formal-fiber owner to the concrete fiber algebra of
  the global completion map `A → AdicCompletion I A`;
- primitive data: the owner hypothesis `IsPRing P A` together with the transfer/descent axioms
  `(B)` and `(D)`;
- derived API: the specific fiberwise consequence for `p.asIdeal.Fiber (AdicCompletion I A)`.

Source/core/bridge triage:
- `source-facing`: `completion_fibers_have_property_of_pRing`;
- `core/canonical`: `IsPRing`, `P.HasPropertyB`, and `P.HasPropertyD`;
- `bridge/view`: the comparison between the global completion fiber over `p` and the relevant
  completed local fiber used in the descent argument.

Refinement note: the theorem should not expose `[IsNoetherianRing A]` as primitive public data,
because that structure is already part of the source-facing owner hypothesis `IsPRing P A`.
-/

-- Proof sketch: for each prime `p ⊂ A`, localize the completion map at a prime `p'` of
-- `AdicCompletion I A` above `p`. By property `(B)`, it suffices to treat the corresponding local
-- fiber ring. Compare the maximal-ideal completion of `A_p` with the completion of the localized
-- completed ring using Lemma `15.43.9`, then use faithful flatness of the completion map and
-- property `(D)` to descend `P` from the completed local fiber. Finally invoke the `P`-ring
-- hypothesis on `A`.
/-- Lemma 15.51.6: if `A` is a `P`-ring, where `P` satisfies `(B)` and `(D)`, then for every
prime `p` of `A` the fiber ring of the completion map `A → AdicCompletion I A` over `p` has
property `P` over `κ(p)`. -/
theorem completion_fibers_have_property_of_pRing
    (hA : IsPRing P A)
    (p : PrimeSpectrum A) :
    P p.asIdeal.ResidueField (p.asIdeal.Fiber (AdicCompletion I A)) := sorry

end

end Algebra
