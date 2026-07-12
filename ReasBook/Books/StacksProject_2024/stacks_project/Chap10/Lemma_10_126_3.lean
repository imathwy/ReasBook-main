import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.Submodule

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R) (S : Submonoid R)

local notation "Sbar" => Algebra.algebraMapSubmonoid (R ⧸ I) S
local notation "R'" => Localization Sbar

/- Domain triage:
* primary domain: localization of quotient modules over a commutative ring;
* sampled owner declarations in this domain:
  `localizedQuotientEquiv`,
  `Module.FinitePresentation.exists_lift_of_isLocalizedModule`,
  `exists_finitePresentation_module_with_localizedLinearEquiv`;
* owner abstraction for the comparison data: existence of a `LinearEquiv`;
* primitive data: an `R`-module `M`;
* derived API: the localized quotient `LocalizedModule Sbar (M ⧸ (I • ⊤))`.

This item remains `source-facing`: it asserts existence of an `R`-module whose quotient modulo `I`
localizes to the given `R'`-module. The refinement here is only to expose the two source clauses as
direct binder-style theorem statements with `Nonempty` linear-equivalence witnesses, with the
lifted module kept in the same universe as the target `R'`-module.
-/
-- Proof sketch: for clause (1), first realize the finite `R'`-module as the localization of a
-- finite `(R ⧸ I)`-module and then regard that quotient module as coming from an `R`-module modulo
-- `I`. For clause (2), choose a finite presentation matrix over `R'`, clear denominators to lift
-- it to a matrix over `R`, and compare the resulting quotient after modding out by `I` and
-- localizing.
/-- Lemma 10.126.3 (1): every finite `R'`-module, where
`R' = Localization (Submonoid.map (Ideal.Quotient.mk I) S) = S⁻¹(R ⧸ I)`, is obtained from a
finite `R`-module by reducing modulo `I` and localizing at `S`. -/
theorem exists_finite_module_with_localizedQuotientLinearEquiv
    (M' : Type v) [AddCommGroup M'] [Module R' M'] [Module.Finite R' M'] :
    ∃ (M : Type v) (_ : AddCommGroup M) (_ : Module R M) (_ : Module.Finite R M),
      Nonempty (LocalizedModule Sbar (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R'] M') := sorry

/-- Lemma 10.126.3 (2): every finitely presented `R'`-module is obtained from a finitely
presented `R`-module by reducing modulo `I` and localizing at `S`. -/
theorem exists_finitePresentation_module_with_localizedQuotientLinearEquiv
    (M' : Type v) [AddCommGroup M'] [Module R' M'] [Module.FinitePresentation R' M'] :
    ∃ (M : Type v) (_ : AddCommGroup M) (_ : Module R M)
      (_ : Module.FinitePresentation R M),
      Nonempty (LocalizedModule Sbar (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R'] M') := sorry

end
