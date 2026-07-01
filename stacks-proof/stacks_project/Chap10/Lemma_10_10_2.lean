import Mathlib
import Mathlib.Tactic.Recall
-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-
Lemma 10.10.2 is `source-facing` but bridge-shaped in the localization/Hom domain. The primitive
owner abstractions are `Module.FinitePresentation.linearEquivMapExtendScalars` for localizing
`Hom_R(M, N)` with `M` finitely presented and `LinearMap.extendScalarsOfIsLocalizationEquiv` for
forgetting no-longer-essential `Localization S`-linearity on already localized modules. The
textbook clauses are the `Localization S`-linear and away-localization specializations of those
owners. -/

/- Owner recall for clauses `(3)` and `(1)`: localizing `Hom_R(M, N)` commutes with `Hom` out of a
finitely presented module. -/
recall Module.FinitePresentation.linearEquivMapExtendScalars

section

variable [Module.FinitePresentation R M]

variable (S : Submonoid R)

/- Lemma 10.10.2 (3): for a finitely presented `R`-module `M` and any multiplicative subset
`S ⊆ R`, the localization of `Hom_R(M, N)` is canonically identified with the module of
`Localization S`-linear maps `S⁻¹M → S⁻¹N`. This is the `Localization S`-linear upgrade of the
owner comparison `Module.FinitePresentation.linearEquivMapExtendScalars`. -/
#check
  (LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
      (Module.FinitePresentation.linearEquivMapExtendScalars S) :
    LocalizedModule S (M →ₗ[R] N) ≃ₗ[Localization S]
      (LocalizedModule S M →ₗ[Localization S] LocalizedModule S N))

/- Lemma 10.10.2 (1): for `f ∈ R`, the localization of `Hom_R(M, N)` away from `f` is the away
specialization of the previous `Localization S`-linear comparison. -/
variable (f : R)

#check
  (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)
      (Module.FinitePresentation.linearEquivMapExtendScalars (Submonoid.powers f)) :
    LocalizedModule.Away f (M →ₗ[R] N) ≃ₗ[Localization.Away f]
      (LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f N))

end

/- Owner recall for clauses `(4)` and `(2)`: once source and target already carry the localized
module structure, `R`-linear maps and `Localization S`-linear maps are canonically equivalent. -/
recall LinearMap.extendScalarsOfIsLocalizationEquiv

/- Lemma 10.10.2 (4): `Localization S`-linear maps between localized modules are canonically the
same as `R`-linear maps between those localized modules. This is the inverse orientation of
`LinearMap.extendScalarsOfIsLocalizationEquiv`. -/
variable (S : Submonoid R)

#check
  ((LinearMap.extendScalarsOfIsLocalizationEquiv S (Localization S)).symm :
    (LocalizedModule S M →ₗ[Localization S] LocalizedModule S N) ≃ₗ[Localization S]
      (LocalizedModule S M →ₗ[R] LocalizedModule S N))

/- Lemma 10.10.2 (2): for `f ∈ R`, `R_f`-linear maps `M_f → N_f` are canonically the same as
`R`-linear maps `M_f → N_f`. This is the away-localization specialization of the previous
canonical equivalence. -/
variable (f : R)

#check
  ((LinearMap.extendScalarsOfIsLocalizationEquiv (Submonoid.powers f) (Localization.Away f)).symm :
    (LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f N) ≃ₗ[Localization.Away f]
      (LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away f N))

end
