import Mathlib
import stacks_project.Chap10.Definition_10_122_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain-style sampling for Lemma 10.122.10:
- primary domain: quasi-finite finite-type algebras at a prime in a tower;
- sampled owner declarations:
  `Algebra.FiniteType.QuasiFiniteAt`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.QuasiFinite.of_restrictScalars`,
  `Algebra.FiniteType.of_restrictScalars_finiteType`;
- best owner abstraction for the numbered lemma: the source-facing predicate
  `Algebra.FiniteType.QuasiFiniteAt A C r.asIdeal`;
- primitive data: the tower `A → B → C`, the prime `r : PrimeSpectrum C`, and the source-facing
  hypothesis that `A → C` is quasi-finite at `r`;
- derived API: the core local quasi-finite consequence for `B → C` and the finite-type component
  needed to reassemble the source-facing conclusion.

Source/core/bridge triage:
- `source-facing`: the textbook permanence lemma for quasi-finiteness at `r`, where Definition
  `10.122.3` includes both finite type and the local quasi-finite owner;
- `core/canonical`: `Algebra.QuasiFiniteAt` and `Algebra.FiniteType`;
- `bridge/view`: the restriction-of-scalars theorem for `Algebra.QuasiFiniteAt`.

Primitive data vs. derived API:
- primitive source-facing data: `hAC : Algebra.FiniteType.QuasiFiniteAt A C r.asIdeal`;
- derived core owner consequence: `Algebra.QuasiFiniteAt B r.asIdeal`;
- derived finite-type component: `Algebra.FiniteType B C`. -/

-- Proof sketch: first restrict scalars on `Localization.AtPrime r.asIdeal` to transport the core
-- owner `Algebra.QuasiFiniteAt` from `A → C` to `B → C`. Then recover the finite-type component
-- of `B → C` by restricting scalars on the finite-type algebra `C` over `A`.
/-- Core owner bridge for Lemma 10.122.10: quasi-finiteness at `r` is preserved under restriction
of scalars along a tower `A → B → C`. -/
theorem toQuasiFiniteAt_of_restrictScalars (r : PrimeSpectrum C)
    (hAC : Algebra.QuasiFiniteAt A r.asIdeal) : Algebra.QuasiFiniteAt B r.asIdeal := by
  letI : Algebra.QuasiFiniteAt A r.asIdeal := hAC
  change Algebra.QuasiFinite B (Localization.AtPrime r.asIdeal)
  exact Algebra.QuasiFinite.of_restrictScalars A B (Localization.AtPrime r.asIdeal)

/-- Lemma 10.122.10: in a tower `A → B → C`, if `A → C` is quasi-finite at the prime `r` in the
source-facing sense of Definition `10.122.3`, then `B → C` is also quasi-finite at `r`. -/
theorem quasiFiniteAt_of_restrictScalars (r : PrimeSpectrum C)
    (hAC : Algebra.FiniteType.QuasiFiniteAt A C r.asIdeal) :
    Algebra.FiniteType.QuasiFiniteAt B C r.asIdeal := by
  refine ⟨?_, ?_⟩
  · letI : Algebra.FiniteType A C := hAC.finiteType
    exact Algebra.FiniteType.of_restrictScalars_finiteType A B C
  · letI : Algebra.QuasiFiniteAt A r.asIdeal := hAC.toQuasiFiniteAt
    exact toQuasiFiniteAt_of_restrictScalars r hAC.toQuasiFiniteAt

end
