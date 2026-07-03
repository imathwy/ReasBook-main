import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.85.3:
- primary domain: derived `R`-modules concentrated in `[-1, 0]`, represented by two-term
  cochain complexes;
- sampled owner declarations:
  `IsTwoTermRepresentative`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`,
  `Module.Free`,
  `Module.Finite`,
  `IsNoetherianRing`;
- best owner abstraction: the source-facing owner is `IsTwoTermRepresentative K P`, whose
  primitive data are that `P` represents `K` and is supported in degrees `-1` and `0`;
- primitive data: the representative complex together with the two-term owner predicate, while the
  module-theoretic conditions on the degree `0` and degree `-1` terms remain additional inputs;
- derived API: the existence theorems below and downstream predicates built from this owner.

Source/core/bridge triage:
- `source-facing`: the existence of a two-term representative with the stated free / finite
  properties;
- `core/canonical`: `IsTwoTermRepresentative`, together with `K.IsGE (-1)` and `K.IsLE 0`;
- `bridge/view`: the explicit isomorphism witness produced from the t-structure truncation API.

Accordingly, this file exposes direct existential statements over a cochain complex witness rather
than a parallel public wrapper structure carrying the same data. -/

/-- A cochain complex `P` is a two-term representative of `K` if it represents `K` and is
supported in degrees `-1` and `0`. -/
def IsTwoTermRepresentative (K : DMod) (P : Cpx) : Prop :=
  IsIsomorphic (DerivedCategory.Q.obj P) K ∧ P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0

-- Proof sketch: choose a cochain-complex representative of `K`, truncate above degree `0`, then
-- replace it by a quasi-isomorphic bounded-above free complex using Lemma `13.15.4`. Finally
-- truncate below degree `-1`; the homology vanishing outside `{-1, 0}` ensures that this
-- truncation still represents `K`, and the degree-zero term remains free.
/-- Lemma 15.85.3 (1): if an object `K` of `D(R)` has cohomology only in degrees `-1` and `0`,
then `K` is represented by a cochain complex supported in degrees `-1` and `0` whose degree-zero
term is a free `R`-module. -/
theorem exists_twoTermFreeRepresentative
    (K : DMod)
    (hGE : K.IsGE (-1))
    (hLE : K.IsLE 0) :
    ∃ P : Cpx, IsTwoTermRepresentative K P ∧ Module.Free R (P.X 0) := sorry

-- Proof sketch: choose a bounded-above finite-free representative of `K` from Lemma `15.65.5`,
-- using the Noetherian and finite-cohomology hypotheses. Truncating this complex below degree
-- `-1` preserves the represented derived object because the other cohomology groups vanish. The
-- resulting degree-zero term is finite free, and the degree `-1` term is finite because it is a
-- subquotient of finite modules in the original finite-free complex.
/-- Lemma 15.85.3 (2): under the Noetherian and finite-cohomology hypotheses, the two-term
representative can be chosen with finite free degree-zero term and finite degree `-1` term. -/
theorem exists_twoTermFiniteFreeRepresentative
    [IsNoetherianRing R]
    (K : DMod)
    (hGE : K.IsGE (-1))
    (hLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H (-1)).obj K))
    (hH0 : Module.Finite R ((H 0).obj K)) :
    ∃ P : Cpx,
      IsTwoTermRepresentative K P ∧
        Module.Free R (P.X 0) ∧
          Module.Finite R (P.X 0) ∧ Module.Finite R (P.X (-1)) := sorry

end

end CategoryTheory
