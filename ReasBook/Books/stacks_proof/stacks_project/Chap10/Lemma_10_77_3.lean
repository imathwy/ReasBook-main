import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Finite R P]

-- Domain-style sampling:
-- * primary domain: finitely generated modules over a Noetherian ring, viewed in `ModuleCat R`
--   through the owner abstractions `Module.exists_finite_presentation`,
--   `ShortComplex.ShortExact.extClass`, and `Module.Projective.of_split`.
-- * inspected owner declarations: `Module.exists_finite_presentation`,
--   `ShortComplex.moduleCat_exact_iff_range_eq_ker`, `Ext.covariant_sequence_exact₃`, and
--   `Module.Projective.of_split`.
-- * best owner abstraction: the short exact sequence attached to a surjection from a finite free
--   module onto `P`, rather than an ad hoc kernel/package wrapper.
-- * layer: `source-facing`; this lemma is a finite-module criterion for projectivity, but its
--   proof should factor through the canonical short-complex and `Ext` owners.
-- * primitive data: the finite `R`-module `P`.
-- * derived API: the finite free presentation of `P`, the associated short exact sequence in
--   `ModuleCat R`, and the splitting that comes from the vanishing `Ext¹` class.
/-
Proof sketch: choose a surjection `π : F → P` from a finite free module `F`. The canonical short
complex `0 → ker π → F → P → 0` in `ModuleCat R` is short exact. Since `R` is Noetherian,
`ker π` is finite, so the hypothesis applies to `Ext¹_R(P, ker π)`. Exactness of the covariant
`Ext` sequence then produces a section of `π`, and `Module.Projective.of_split` shows that `P` is
projective as a direct summand of the finite free module `F`. -/
/-- Lemma 10.77.3: over a Noetherian ring, a finite `R`-module `P` is projective if
`Ext^1_R(P, M) = 0` for every finite `R`-module `M`. -/
@[stacks 0G8T]
theorem projective_of_extOne_vanishes_for_finite_modules
    (hExt :
      ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
        Subsingleton (Ext (ModuleCat.of R P) (ModuleCat.of R M) 1)) :
    Module.Projective R P := by
  obtain ⟨F, _, _, _, _, π, hπ⟩ := Module.exists_finite_presentation R P
  let S : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.ker π).subtype)
      (ModuleCat.ofHom π)
      (by
        ext x
        simp)
  have hS : S.ShortExact := by
    refine
      { exact := ?_
        mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker π).injective_subtype
        epi_g := (ModuleCat.epi_iff_surjective _).mpr hπ }
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      simp
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hExtKer : Subsingleton (Ext (ModuleCat.of R P) (ModuleCat.of R (LinearMap.ker π)) 1) :=
    hExt (LinearMap.ker π)
  have hzero : (mk₀ (𝟙 <| ModuleCat.of R P)).comp hS.extClass (zero_add 1) = 0 := by
    change (mk₀ (𝟙 <| ModuleCat.of R P)).comp hS.extClass (zero_add 1) = 0
    exact Subsingleton.elim _ _
  obtain ⟨σ, hσ⟩ :=
    covariant_sequence_exact₃ _ hS (mk₀ (𝟙 <| ModuleCat.of R P)) (zero_add 1) hzero
  obtain ⟨σ, rfl⟩ := homEquiv₀.symm.surjective σ
  have hsection : σ ≫ ModuleCat.ofHom π = 𝟙 (ModuleCat.of R P) := by
    apply homEquiv₀.symm.injective
    simpa using hσ
  exact Module.Projective.of_split σ.hom π (ModuleCat.hom_ext_iff.mp hsection)

end
