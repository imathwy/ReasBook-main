import StacksProject_2024.Chap15.Lemma_15_51_1

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct

universe u

namespace FieldAlgebraProperty

/- Domain sampling pass:
- primary domain: permanence of formal-fiber conditions for properties of Noetherian algebras over
  fields;
- sampled owner declarations:
  `Algebra.EssFiniteType`,
  `FieldAlgebraProperty`,
  `IsPRing`,
  `SatisfiesPPrimePairCondition`;
- best owner abstraction: `FieldAlgebraProperty`, with the transfer/locality axioms packaged by
  `HasPropertyA` and `HasPropertyB`, and the source-facing ring owner `IsPRing`; clause `(2)`
  should therefore be phrased on the theorem surface using the local `P`-ring owner
  `IsPRing P (Localization.AtPrime p.asIdeal)` rather than duplicating its prime-pair expansion;
- primitive data: the underlying predicate `P k A` together with the base-change and
  prime-localization laws;
- derived API: source-facing specializations and larger chapter packages built from those owner
  axioms.

Sampling note: the nearby local-fiber criterion `Lemma_15_51_2` is also phrased over the chapter
owner `FieldAlgebraProperty.HasPropertyB`. That owner is the right layer here as well, because
`FieldAlgebraProperty` depends on a chosen `k`-algebra structure, not just the underlying
commutative ring.

Source/core/bridge triage:
- `source-facing`: the quasi-finite transfer theorems for formal fibers and the resulting
  `isPRing_of_quasiFinite`;
- `core/canonical`: the owner classes `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`, and the ring owner `IsPRing`;
- `bridge/view`: the geometric-regularity specialization in `Lemma_15_50_3`.
-/

/-- A field-algebra property satisfies `(A)` if it is preserved by base change along finitely
generated extensions of the ground field. -/
class HasPropertyA (P : FieldAlgebraProperty) : Prop where
  /-- Base change of a Noetherian `k`-algebra along a finitely generated field extension preserves
  the property `P`. -/
  baseChange (k A K : Type u) [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
      [Field K] [Algebra k K] [Algebra.EssFiniteType k K] (hA : P k A) :
      P K (K ⊗[k] A)

/-- A field-algebra property satisfies `(B)` if for every ground field `k`, the induced ring
property on Noetherian `k`-algebras can be checked on prime localizations. -/
class HasPropertyB (P : FieldAlgebraProperty) : Prop where
  /-- The prime-local criterion for `P` over the fixed base field `k`. -/
  localizationCriterion (k A : Type u) [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A] :
      P k A ↔ ∀ p : PrimeSpectrum A, P k (Localization.AtPrime p.asIdeal)

end FieldAlgebraProperty

section

variable (P : FieldAlgebraProperty)
variable [P.HasPropertyA] [P.HasPropertyB]

section QuasiFiniteAtPrime

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable [IsNoetherianRing R] [Algebra.FiniteType R R']

-- Proof sketch: use quasi-finiteness at `p'` to identify `R̂_[p] ⊗[R] R'` with a product whose
-- first factor is `R̂_[p']`. After tensoring with `κ(q')`, the target formal fiber is therefore a
-- direct factor of the base change of the source formal fiber along `κ(q) → κ(q')`. Apply
-- property `(A)` to obtain `P` after base change and property `(B)` to descend `P` from the
-- product ring to the direct factor.
/-- Lemma 15.51.3 (1): for a finite type map of Noetherian rings `R → R'`, if `p'` lies over `p`,
`q' ⊆ p'` lies over `q`, the map is quasi-finite at `p'`, and the formal fibre
`(R_p)^∧ ⊗[R] κ(q)` has property `P`, then the formal fibre `(R'_(p'))^∧ ⊗[R'] κ(q')` also has
property `P`. -/
theorem completed_localization_formalFiber_hasProperty_of_quasiFiniteAt
    (p q : PrimeSpectrum R) (p' q' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p)
    (hq : PrimeSpectrum.comap (algebraMap R R') q' = q)
    (hqp' : q'.asIdeal ≤ p'.asIdeal)
    [Algebra.QuasiFiniteAt R p'.asIdeal]
    (hP : P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p]))) :
    P q'.asIdeal.ResidueField (q'.asIdeal.Fiber (R̂_[p'])) := sorry

-- Proof sketch: view the hypothesis as saying that the local ring `R_p` is a `P`-ring. For a
-- prime `q'` of `R'_(p')`, let `q` be its image in `R_p`, equivalently in `R`. The `P`-ring
-- hypothesis on `R_p` gives `P` on the source formal fiber over `q`, and clause (1) transfers
-- that property to the formal fiber over `q'`.
/-- Lemma 15.51.3 (2): for a finite type map of Noetherian rings `R → R'`, if `p'` lies over `p`,
the map is quasi-finite at `p'`, and every formal fibre of `R_p` has `P`, then every formal fibre
of `R'_(p')` has `P`. -/
theorem completed_localization_formalFibers_haveProperty_of_quasiFiniteAt
    (p : PrimeSpectrum R) (p' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p)
    [Algebra.QuasiFiniteAt R p'.asIdeal]
    (hP : IsPRing P (Localization.AtPrime p.asIdeal)) :
    IsPRing P (Localization.AtPrime p'.asIdeal) := sorry

end QuasiFiniteAtPrime

section QuasiFinite

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable [IsNoetherianRing R] [Algebra.FiniteType R R'] [Algebra.QuasiFinite R R']

-- Proof sketch: finite type over the Noetherian ring `R` makes `R'` Noetherian. For each prime
-- `p'` of `R'`, let `p` be its image in `R`. The hypothesis that `R` is a `P`-ring gives that
-- the local ring `R_p` is a `P`-ring, and clause (2) transfers that owner statement to the local
-- ring `R'_(p')`.
/-- Lemma 15.51.3 (3): if `R → R'` is quasi-finite and `R` satisfies the `P`-ring formal-fibre
condition, then `R'` also satisfies the `P`-ring formal-fibre condition. -/
theorem isPRing_of_quasiFinite
    (hP : IsPRing P R) :
    IsPRing P R' := sorry

end QuasiFinite

end
