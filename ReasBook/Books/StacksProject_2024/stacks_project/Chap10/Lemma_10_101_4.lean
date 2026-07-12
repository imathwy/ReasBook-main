import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {I : Ideal R}

section

variable [Algebra R R']

local notation "I₂" => Ideal.comap (algebraMap R R') (Ideal.map (algebraMap R R') (I ^ 2))

/- Domain triage:
- primary domain: commutative algebra of flatness under base change and quotienting by ideals;
- sampled owner declarations of the same kind:
  `Module.Flat.iff_flat_tensorProduct`,
  `flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes`,
  `torOne_baseChangeMap_surjective_of_flat_baseChange`,
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`;
- best owner abstraction: the canonical owner predicates `Module.Flat` and the Chapter 10
  `Tor₁` base-change / quotient-flatness API;
- primitive data: the `R`-algebra `R'`, the ideal `I`, and the `R`-module `M`;
- derived API: the specific contracted-square ideal `I₂` and the resulting quotient-flatness
  statement.

Layering:
- this item stays `source-facing`: it is the textbook special-case quotient statement for the
  contracted extended square ideal;
- the proof should use the `core/canonical` owners above rather than introducing a parallel local
  flatness/Tor wrapper;
- no extra `bridge/view` owner is needed beyond the local notation for the contracted ideal.
-/

-- Proof sketch: replace `R`, `M`, and `R'` by the corresponding quotients so that `I₂ = 0` and
-- `I ^ 2 = 0`; then apply Lemma `10.99.8`, reducing flatness over `R / I₂` to vanishing of
-- `Tor₁^R(R / I, M)`, and prove that vanishing by comparing the kernel of `I ⊗[R] M → M` with its
-- image after base change to `R'`.
/-- Lemma 10.101.4: if `M / IM` is flat over `R / I` and the base change `R' ⊗[R] M` is flat over
`R'`, then `M / I₂M` is flat over `R / I₂`, where
`I₂ = Ideal.comap (algebraMap R R') (Ideal.map (algebraMap R R') (I ^ 2))`. -/
theorem flat_quotient_comap_map_sq_of_flat_mod_ideal_and_flat_baseChange
    (hflat_mod_ideal : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hflat_baseChange : Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat (R ⧸ I₂) (M ⧸ (I₂ • ⊤ : Submodule R M)) := sorry

end

end
