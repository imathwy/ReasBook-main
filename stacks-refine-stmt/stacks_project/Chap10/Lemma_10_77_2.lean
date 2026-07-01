import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

section

variable {R : Type u} [Ring R] [Small.{v} R]
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Lemma 10.77.2: for an `R`-module `P`, the following are equivalent: `P` is projective, `P`
is a direct summand of a free `R`-module, and `Ext^1_R(P, M) = 0` for every `R`-module `M`. -/
-- Proof sketch: use `Module.Projective.iff_split'` for the direct-summand characterization and
-- `IsProjective.iff_projective` to compare module-theoretic projectivity with projectivity in
-- `ModuleCat R`; then identify vanishing of every class in `Ext^1(P, M)` with the
-- `Subsingleton` criterion `projective_iff_subsingleton_ext_one`.
theorem module_projective_direct_summand_free_extOne_tfae :
    List.TFAE [
      Module.Projective R P,
      ∃ (F : Type v) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
        (i : P →ₗ[R] F) (s : F →ₗ[R] P), s.comp i = LinearMap.id,
      ∀ (M : Type v) (_ : AddCommGroup M) (_ : Module R M),
        Subsingleton (Abelian.Ext (ModuleCat.of R P) (ModuleCat.of R M) 1)
    ] := sorry

end
