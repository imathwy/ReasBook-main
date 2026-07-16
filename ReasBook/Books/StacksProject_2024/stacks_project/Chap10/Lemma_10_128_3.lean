import StacksProject_2024.stacks_project.Chap10.Lemma_10_127_13

-- Declarations for this item will be appended below by the statement pipeline.
universe uR uS uM

open scoped TensorProduct

section

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable {f : R →+* S} [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

-- Proof sketch: for a fixed stage `λ`, Remark `10.75.9` identifies
-- `Tor₁^{R_λ}(M_λ, R_λ / 𝔪_λ)` with the kernel of `𝔪_λ ⊗[R_λ] M_λ → M_λ`, so this Tor module is
-- finite over `S_λ`. Because `M` is flat over `R`, the corresponding kernel vanishes after
-- passing to the colimit, hence finitely many generators die at some larger stage `λ'`. Applying
-- Lemma `10.99.14` to the local base-change square supplied by the approximation then yields
-- flatness of `M_{λ'}` over `R_{λ'}`.
namespace DirectedLocalEssFinitePresentationModuleApproximation

/-- Lemma 10.128.3: for explicit local approximation data as in Lemma `10.127.13`, if `M` is flat
over `R`, then some stage module `M_λ` is flat over the corresponding source ring `R_λ`. -/
theorem exists_flat_stage_of_flat
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M) :
    ∃ i : A.Λ, Module.Flat (A.RStage i) (A.moduleStage i) := sorry

end DirectedLocalEssFinitePresentationModuleApproximation

end
