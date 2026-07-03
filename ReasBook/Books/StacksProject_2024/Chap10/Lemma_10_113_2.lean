import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [Algebra A B] [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)]
  [FiniteDimensional (FractionRing A) (FractionRing B)]

/-
Domain triage:
* primary domain: finite-type maps of domains, the height-one fiber over a prime, and the induced
  fraction-ring extension;
* source-facing layer: the finite fiber `p.primesOver B` over a height-one prime and the height of
  each prime in that fiber;
* core/canonical owners sampled for this refinement:
  `FiniteDimensional (FractionRing A) (FractionRing B)`,
  `Algebra (FractionRing A) (FractionRing B)`,
  `IsScalarTower A (FractionRing A) (FractionRing B)`,
  `Ideal.primesOver`,
  `primeHeight_le_primeHeight_add_trdeg_sub_residueFieldTrdeg_of_finiteType`,
  `isMaximal_of_liesOver_of_isAlgebraic_residueField`;
* bridge/view: no extra wrapper is needed here, since the source statement already lives on the
  canonical owner set `p.primesOver B`.

Primitive data are the rings `A`, `B`, the canonical finite-dimensional fraction-field extension
`Frac(A) → Frac(B)`, and the height-one prime `p`. The injectivity of `A → B` is derived
internally from
`algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)` and the given
fraction-field tower. The public theorem is
derived API on the owner set `p.primesOver B`. -/

-- Proof sketch: first derive injectivity of `A → B` from the fraction-field tower via
-- `algebraMap_injective_of_field_isFractionRing`, then apply Lemma `10.113.1` with transcendence
-- degree `0`, since a finite extension of fraction fields is algebraic. For every `q` over `p`,
-- the dimension inequality forces
-- `primeHeight q = 1`, and the residue-field extension `κ(q) / κ(p)` is algebraic. Hence each such
-- `q` is a closed point of the fiber over `p` by Lemma `10.35.9`. The fiber is Noetherian because
-- `B` is finite type over the Noetherian ring `A`, so its prime spectrum is a Noetherian space;
-- a Noetherian space all of whose points are closed is finite, yielding finiteness of
-- `p.primesOver B`.
/-- Lemma 10.113.2: if `A → B` is a finite type map of domains, `A` is Noetherian, the induced
extension of fraction rings is finite, and `p` is a height-one prime of `A`, then there are only
finitely many prime ideals of `B` lying over `p`, and every such prime also has height one. Under
the fraction-field tower hypotheses, injectivity of `A → B` is automatic. -/
theorem finite_primesOver_and_primeHeight_eq_one_of_primeHeight_eq_one
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (p : Ideal A) [p.IsPrime] (hp : Ideal.primeHeight p = 1) :
    Finite (p.primesOver B) ∧ ∀ q : p.primesOver B, Ideal.primeHeight q.1 = 1 := sorry

end
