import stacks_project.Chap15.Lemma_15_20_2

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')]
variable [IsNoetherianRing R] [Algebra.FiniteType R S]
variable [AddCommGroup M] [Module S M] [Module.Finite S M]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/- Domain triage:
- primary domain: closed-fiber flatness loci under local base change in commutative algebra;
- sampled owner declarations:
  `Ideal.IsClosedFiberFlatQuotient`,
  `Module.flatOverBaseLocus`,
  `exists_stage_zeroLocus_subset_flatOverBaseLocus_of_direct_limit_base_change`,
  `baseChange_closedFiberFlat_iff_map_eq_bot_of_isLeast_closedFiberFlat_ideal`;
- best owner abstraction: the source-facing least-ideal predicate
  `Ideal.IsClosedFiberFlatQuotient S M`, with `Module.flatOverBaseLocus` as the flatness-locus
  owner and `baseChange_closedFiberFlat_iff_map_eq_bot_of_isLeast_closedFiberFlat_ideal` from
  `15.20.2` as the Noetherian-target bridge;
- primitive data: the least ideal `I` for `Ideal.IsClosedFiberFlatQuotient S M`, the local base
  change `R → R'`, and the finite type hypothesis on `R → S`;
- derived API: the elimination of the Noetherian target hypothesis by descending the base-changed
  closed-fiber flatness condition to an essentially finite type local `R`-subalgebra of `R'`.

Source/core/bridge triage:
- `source-facing`: the finite-type strengthening from the Stacks text, removing the Noetherian
  hypothesis on the target local ring;
- `core/canonical`: `Ideal.IsClosedFiberFlatQuotient S M` and `Module.flatOverBaseLocus`;
- `bridge/view`: Lemma `15.20.2`, used after descending along directed local approximations.
-/

-- Proof sketch: `(←)` is still Lemma `15.18.1`. For `(→)`, because `R` is Noetherian and
-- `R → S` is finite type, both `S` and the finite `S`-module `M` are finitely presented. Write
-- `R'` as a directed colimit of local `R`-subalgebras essentially of finite type over `R`; then
-- Lemma `15.18.3` descends the base-changed closed-fiber flatness condition to one stage `R_λ`.
-- Since `R_λ` is Noetherian, Lemma `15.20.2` shows that `I` maps to zero in `R_λ`, hence also in
-- `R'`.
/-- Lemma 15.20.3: if `I` is the least ideal from Lemma `15.20.1` and `R → S` is finite type,
then for any local homomorphism of local rings `R → R'` the base-changed triple
`(R' → S ⊗[R] R', (S ⊗[R] R') ⊗[S] M)` satisfies the closed-fiber flatness condition
`(15.18.0.1)` exactly when the image of `I` in `R'` is zero. -/
theorem baseChange_closedFiberFlat_iff_map_eq_bot_of_isLeast_closedFiberFlat_ideal_of_finiteType
    {I : Ideal R}
    (hI : IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I) :
    zeroLocus (Ideal.map (algebraMap R' S') (maximalIdeal R') : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' ↔
      Ideal.map (algebraMap R R') I = ⊥ := by
  sorry

end
