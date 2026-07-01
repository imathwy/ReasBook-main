import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CSA

open ConjAct

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)
variable {B : Type w} [Ring B] [Algebra k B] [IsSimpleRing B]

/- Domain-style sampling for Theorem 11.6.1:
- primary domain: Skolem-Noether theory for algebra homomorphisms into a finite central simple
  algebra, expressed through the canonical conjugation action of units;
- relevant owner declarations sampled:
  `ConjAct.toConjAct`,
  `MulSemiringAction.toAlgEquiv`,
  `CSA.isAzumaya`,
  `IsAzumaya.AlgHom.mulLeftRight_bij`;
- best owner abstraction: the core/canonical owner for the target-side symmetry is the conjugation
  action of `Aˣ` on `A`, viewed as `A ≃ₐ[k] A` via `MulSemiringAction.toAlgEquiv`;
- primitive data: `A : CSA k`, a simple `k`-algebra `B`, and algebra maps `f g : B →ₐ[k] A`;
- derived API: the source-facing Skolem-Noether conjugacy statement below, together with the
  pointwise inner-automorphism bridge in Lemma 11.6.2.

Layer triage:
- `source-facing`: the theorem that two `k`-algebra maps into a finite central simple algebra are
  conjugate by a unit;
- `core/canonical`: the conjugation action `toConjAct` transported to algebra automorphisms by
  `MulSemiringAction.toAlgEquiv`;
- `bridge/view`: the downstream specialization turning equality of algebra maps into the usual
  pointwise formula for automorphisms. -/

-- Proof sketch: choose a simple left `A`-module `M`, set `L := Module.End A M`, and give `M`
-- two compatible `B ⊗[k] Lᵐᵒᵖ`-module structures induced by `f` and `g`. The tensor product is
-- simple by the previous finite-central tensor-product lemma, so these module structures are
-- isomorphic; the intertwiner lies in the commutant of `L`, hence comes from a unit of `A`, and
-- the induced algebra automorphism of `A` is the canonical conjugation action by that unit.
/-- Theorem 11.6.1: if `A` is a finite central simple `k`-algebra, `B` is a simple `k`-algebra,
and `f g : B →ₐ[k] A` are `k`-algebra homomorphisms, then `f` and `g` are conjugate by a unit of
`A`. -/
theorem algHom_inner_conjugate (f g : B →ₐ[k] A) :
    ∃ x : Aˣ,
      f = (MulSemiringAction.toAlgEquiv k A (toConjAct x)).toAlgHom.comp g := sorry

end CSA
