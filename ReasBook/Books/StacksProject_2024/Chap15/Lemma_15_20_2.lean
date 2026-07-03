import Mathlib
import StacksProject_2024.Chap15.Lemma_15_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')]
variable [IsNoetherianRing R']
variable [AddCommGroup M] [Module S M] [Module.Finite S M]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/- Domain triage:
- primary domain: closed-fiber flatness loci under local base change in commutative algebra;
- sampled owner declarations: `Ideal.IsClosedFiberFlatQuotient`, `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_of_baseChange`, and
  `exists_isLeast_quotient_primewise_flat_over_closed_point_ideal`;
- core/canonical owners: `Ideal.IsClosedFiberFlatQuotient` for the ideal-level source condition and
  `Module.flatOverBaseLocus` for its flatness clause;
- layer choice here: `source-facing`; the lemma keeps the Stacks iff, but phrases the least-ideal
  hypothesis through the chapter owner and the flatness side through the canonical
  closed-subset inclusion.
-/

-- Proof sketch: the forward implication applies Lemma `15.18.1` after base change and then uses
-- Artin-Rees in the Noetherian local ring `R'` to reduce vanishing of `I R'` to the Artinian
-- quotients `R' / (maximalIdeal R')^n`. For the converse, let `J = RingHom.ker (algebraMap R R')`;
-- the hypothesis implies the base-changed closed-fiber condition over `R'`, so after reducing to
-- the Artinian case one shows `M / J M` is flat over `R / J`, and the leastness of `I` forces
-- `I ≤ J`, equivalently `Ideal.map (algebraMap R R') I = ⊥`.
/-- Lemma 15.20.2: if `I` is the least ideal from Lemma `15.20.1`, then for a local homomorphism
`R → R'` with `R'` Noetherian, the base-changed triple `(R' → S', M')` satisfies the
closed-fiber flatness condition
`(15.18.0.1)` exactly when the image of `I` in `R'` is zero. -/
theorem baseChange_closedFiberFlat_iff_map_eq_bot_of_isLeast_closedFiberFlat_ideal
    {I : Ideal R}
    (hI : IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I) :
    zeroLocus (Ideal.map (algebraMap R' S') (maximalIdeal R') : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' ↔
      Ideal.map (algebraMap R R') I = ⊥ := sorry

end
