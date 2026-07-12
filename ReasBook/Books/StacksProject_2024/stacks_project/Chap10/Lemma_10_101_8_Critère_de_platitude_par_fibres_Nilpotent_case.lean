import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {I : Ideal R}
variable {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

local notation "IS" => Ideal.map (algebraMap R S) I

-- Proof sketch: tensor the short exact sequence `0 → I → R → R / I → 0` with the `R`-flat module
-- `M` to identify the kernel of `I ⊗[R] M → M` with zero. Compare this map with
-- `IS ⊗[S] M → M` to deduce `Tor₁^S(S / IS, M) = 0`, and then apply the nilpotent-ideal flatness
-- criterion from Lemma `10.99.8` over `S`.
/-- Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case): if `I` is nilpotent,
`M / ISM` is flat over `S / IS`, and `M` is flat over `R`, then `M` is flat over `S`. -/
theorem flat_over_target_of_nilpotent_of_flat_over_base_and_flat_mod_extended_ideal
    (hI : IsNilpotent I)
    (hflat_mod : Module.Flat (S ⧸ IS) (M ⧸ (IS • ⊤ : Submodule S M)))
    (hflat_R : Module.Flat R M) :
    Module.Flat S M := sorry

-- Proof sketch: localize at `q`. The fiber hypothesis makes the localized `S_q`-module obtained
-- from `M` faithfully flat over `S_q` by Lemma `10.39.15`, while flatness over `R` localizes.
-- Apply Lemma `10.39.10` to the localized module to conclude that `R → S_q` is flat.
/-- If `M` is flat over both `R` and `S`, then every prime `q` with nontrivial fiber
`M ⊗[S] κ(q)` has `S_q` flat over `R`. -/
theorem atPrime_flat_of_flat_module_and_nontrivial_fiber
    (q : PrimeSpectrum S) (hflat_R : Module.Flat R M) (hflat_S : Module.Flat S M)
    (hq : Nontrivial (M ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := sorry

end
