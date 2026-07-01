import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: choose finitely many elements of `M` whose images generate `LocalizedModule S M`
-- over `Localization S`, and let `M'` be the submodule they generate. Then the localized
-- submodule `M'.localized S` is all of `LocalizedModule S M`.
/-- Lemma 10.126.4 (1): if the localization `S⁻¹M` is finite over `S⁻¹R`, then some finitely
generated submodule of `M` has the same localization as `M`. -/
theorem exists_finite_submodule_with_top_localized
    [Module.Finite (Localization S) (LocalizedModule S M)] :
    ∃ M' : Submodule R M,
      Module.Finite R M' ∧
        M'.localized S = ⊤ := sorry

-- Proof sketch: choose generators `x₁, ..., xₙ` of `LocalizedModule S M`, let
-- `Rⁿ → M` send the standard basis to these elements, and localize its kernel. By the finite case,
-- replace that localized kernel by a finite submodule `K'` of the original kernel with the same
-- localization. Then take `M' := (Fin n → R) ⧸ K'`; this module is finitely presented and its map
-- to `M` becomes a linear equivalence after localizing at `S`.
/-- Lemma 10.126.4 (2): if the localization `S⁻¹M` is finitely presented over `S⁻¹R`, then it is
the localization of a finitely presented `R`-module mapping to `M`. -/
theorem exists_finitePresentation_module_with_localizedLinearEquiv
    [Module.FinitePresentation (Localization S) (LocalizedModule S M)] :
    ∃ (M' : Type w) (_ : AddCommGroup M') (_ : Module R M') (_ : Module.FinitePresentation R M')
      (f : M' →ₗ[R] M)
      (e : LocalizedModule S M' ≃ₗ[Localization S] LocalizedModule S M),
      e.toLinearMap = LocalizedModule.map S f := sorry

end
