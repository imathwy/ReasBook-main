import Mathlib
import stacks_project.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {Pbar : Type v} [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]

-- Proof sketch: use the direct-summand description of finite projective modules over `R ⧸ I`
-- to realize `Pbar` as the image of an idempotent matrix over the quotient. Lift that
-- idempotent across the locally nilpotent quotient and then take the image of the lifted
-- projector inside a finite free `R`-module.
/-- Lemma 10.77.6: if `I` is a locally nilpotent ideal and `Pbar` is a finite projective
`R ⧸ I`-module, then there exists a finite projective `R`-module whose reduction modulo `I` is
isomorphic to `Pbar`. -/
theorem exists_finite_projective_lift_of_isLocallyNilpotent
    [Module.Finite (R ⧸ I) Pbar] [Module.Projective (R ⧸ I) Pbar]
    (hI : I.IsLocallyNilpotent) :
    ∃ (P : Type v) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P)
      (_ : Module.Projective R P),
      Nonempty ((P ⧸ (I • ⊤ : Submodule R P)) ≃ₗ[R ⧸ I] Pbar) := sorry

end
