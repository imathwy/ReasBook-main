import stacks_project.Chap10.Lemma_10_39_9
import stacks_project.Chap10.Lemma_10_99_7_Local_criterion_for_flatness

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u v w x y

section

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x} {M : Type y}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
variable [IsScalarTower R S S'] [IsScalarTower R R' S']
variable [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S']
variable [IsLocalHom (algebraMap R' S')]
variable [IsNoetherianRing R'] [IsNoetherianRing S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/-
Domain-style sampling:
- primary domain: commutative algebra of flatness for finite modules over local homomorphisms,
  combined with tensor-product base change;
- sampled owner declarations of the same kind:
  `flat_baseChange_of_flat`,
  `flat_of_residueField_tor_one_vanishing`,
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`;
- best owner abstraction: the public conclusion is the canonical owner `Module.Flat`, while the
  ring-map flatness hypotheses are expressed by the canonical object-prefix owner predicate
  `f.Flat`;
- primitive data: the local base ring `R`, the local Noetherian target map `R' → S'`, the finite
  `S`-module `M`, the flatness of the two horizontal maps, and the maximal-ideal identification
  in `R'`;
- derived API: flatness of the base-changed module `S' ⊗[S] M` over `R'`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma below about base change of a finite flat module under the
  maximal-ideal hypothesis;
- `core/canonical`: `Module.Flat`, `RingHom.Flat`, and the local flatness criterion
  `flat_of_residueField_tor_one_vanishing`;
- `bridge/view`: tensor-product base change and the Tor/kernel comparison from
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`.
-/

-- Proof sketch: first use flatness of `S → S'` and Lemma `10.39.9` to see that `S' ⊗[S] M` is
-- still flat over `R`. Since `R → R'` is flat, the hypothesis on the maximal ideals identifies
-- `maximalIdeal R ⊗[R] R'` with `maximalIdeal R'`, so injectivity of
-- `maximalIdeal R ⊗[R] (S' ⊗[S] M) → S' ⊗[S] M` transfers to injectivity of
-- `maximalIdeal R' ⊗[R'] (S' ⊗[S] M) → S' ⊗[S] M`. Remark `10.75.9` then gives the vanishing of
-- `Tor₁^{R'}(ResidueField R', S' ⊗[S] M)`, and Lemma `10.99.7` yields flatness over `R'`; the
-- local hypotheses on `R → S`, `R → R'`, and `S → S'` are not used in this route.
/-- Lemma 10.100.2: if `R` is local, `R' → S'` is a local homomorphism of local Noetherian rings,
the horizontal maps `R → R'` and `S → S'` are flat, `M` is a finite `S`-module that is flat over
`R`, and the image of `maximalIdeal R` in `R'` is `maximalIdeal R'`, then the base change
`S' ⊗[S] M` is flat over `R'`. -/
theorem flat_baseChange_of_finite_of_flat_of_maximalIdeal_map_eq
    (hRR' : (algebraMap R R').Flat)
    (hSS' : (algebraMap S S').Flat)
    (hM : Module.Flat R M)
    (hmax : Ideal.map (algebraMap R R') (maximalIdeal R) = maximalIdeal R') :
    Module.Flat R' (S' ⊗[S] M) := sorry

end
