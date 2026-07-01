import stacks_project.Chap10.Lemma_10_126_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]
variable {M : Type v} [AddCommGroup M] [Module R M]

local notation "Rₚ" => Localization.AtPrime p
local notation "Mₚ" => LocalizedModule.AtPrime p M

-- Proof sketch: this is the prime-ideal specialization of Lemma `10.126.4 (1)`, obtained by
-- taking the multiplicative set `p.primeCompl`. The resulting finitely generated submodule has
-- full localization at `p`.
/-- Lemma 10.126.5 (1): if `M_p` is finite over `R_p`, then there exists a finitely generated
submodule of `M` whose localization at `p` is isomorphic to `M_p`. -/
theorem exists_finite_submodule_with_top_localized_atPrime
    [Module.Finite Rₚ Mₚ] :
    ∃ M' : Submodule R M,
      Module.Finite R M' ∧
        M'.localized p.primeCompl = ⊤ := by
  simpa using
    (exists_finite_submodule_with_top_localized p.primeCompl :
      ∃ M' : Submodule R M,
        Module.Finite R M' ∧
          M'.localized p.primeCompl = ⊤)

-- Proof sketch: this is the prime-ideal specialization of Lemma `10.126.4 (2)`, again with the
-- multiplicative set `p.primeCompl`. A finitely presented model of `M_p` over `R` is produced
-- together with a map to `M` whose localization at `p` is identified with a linear equivalence.
/-- Lemma 10.126.5 (2): if `M_p` is finitely presented over `R_p`, then there exists a finitely
presented `R`-module mapping to `M` whose localization at `p` is isomorphic to `M_p`. -/
theorem exists_finitePresentation_module_with_localizedLinearEquiv_atPrime
    [Module.FinitePresentation Rₚ Mₚ] :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M') (_ : Module.FinitePresentation R M')
      (f : M' →ₗ[R] M)
      (e : LocalizedModule.AtPrime p M' ≃ₗ[Rₚ] Mₚ),
      e.toLinearMap = LocalizedModule.map p.primeCompl f := by
  -- Specialize the finitely presented localization theorem to the prime-complement submonoid.
  simpa using
    (exists_finitePresentation_module_with_localizedLinearEquiv p.primeCompl :
      ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M')
        (_ : Module.FinitePresentation R M') (f : M' →ₗ[R] M)
        (e : LocalizedModule.AtPrime p M' ≃ₗ[Rₚ] Mₚ),
        e.toLinearMap = LocalizedModule.map p.primeCompl f)

end
