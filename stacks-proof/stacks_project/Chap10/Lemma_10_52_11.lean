import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Length

open LocalizedModule

local notation "AtPrime" => LocalizedModule.AtPrime

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: finite-length modules and composition series of submodules;
- sampled owner API:
  `JordanHolderModule.instJordanHolderLattice`,
  `Module.length_compositionSeries`,
  `covBy_iff_quot_is_simple`,
  `IsSimpleModule.annihilator_isMaximal`;
- core/canonical owner: `CompositionSeries (Submodule R M)`;
- layer split: the quotient module `s.factor i` is a short reusable view of the owner quotient
  attached to the cover `s.step i`, while simplicity, annihilator, and localization statements are
  derived API.
-/

/- Lemma 10.52.11: for a maximal chain of submodules from `0` to `M`, the number of strict
inclusions is the length of `M`. This is exactly the canonical theorem
`Module.length_compositionSeries`. -/
recall Module.length_compositionSeries

namespace CompositionSeries

/-- The `i`-th successive quotient in a composition series of submodules. -/
abbrev factor (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :=
  s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype

-- Proof sketch: the step relation in a composition series says `s (Fin.castSucc i)` is maximal in
-- `s (Fin.succ i)`, and `covBy_iff_quot_is_simple` identifies such maximal submodule quotients with
-- simple modules.
/-- Each successive quotient in the chosen maximal chain is a simple `R`-module. -/
theorem factor_isSimpleModule (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    IsSimpleModule R (s.factor i) := by
  simpa [factor] using
    (covBy_iff_quot_is_simple (CovBy.le (s.step i))).mp (s.step i)

-- Proof sketch: apply clause (1) to see that the factor is simple. Over a commutative ring, a
-- simple module is canonically a quotient by its annihilator ideal, and that annihilator is
-- maximal.
/-- The annihilator of each successive factor is a maximal ideal. -/
theorem factor_annihilator_isMaximal (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    (Module.annihilator R (s.factor i)).IsMaximal := by
  let _ : IsSimpleModule R (s.factor i) := s.factor_isSimpleModule i
  exact IsSimpleModule.annihilator_isMaximal

/-- Each successive factor is linearly isomorphic to the quotient of `R` by its annihilator. -/
theorem factor_isomorphic_quotient_annihilator
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    Nonempty (s.factor i ≃ₗ[R] R ⧸ Module.annihilator R (s.factor i)) := by
  have hsimple : IsSimpleModule R (s.factor i) := s.factor_isSimpleModule i
  obtain ⟨I, _, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  have hAnn : Module.annihilator R (s.factor i) = I := by
    rw [e.annihilator_eq, I.annihilator_quotient]
  exact ⟨e.trans <| Submodule.quotEquivOfEq _ _ hAnn.symm⟩

-- Proof sketch: localize the composition series at `m`; exactness of localization turns the
-- successive quotients into the localizations of the factors, and the localized factor is nonzero
-- exactly when the corresponding simple factor has annihilator `m`.
/-- For a maximal ideal `m`, the number of successive quotients whose annihilator is `m` is the
length of the localization of `M` at `m`. -/
theorem factor_count_eq_length_localizedModule
    (s : CompositionSeries (Submodule R M)) (h₀ : s.head = ⊥) (h₁ : s.last = ⊤)
    (m : Ideal R) [m.IsMaximal] :
    ENat.card { i : Fin s.length // Module.annihilator R (s.factor i) = m } =
      Module.length (Localization.AtPrime m) (AtPrime m M) := sorry

end CompositionSeries

end Length
