import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {C : Type v}
variable [CommRing A] [CommRing C] [Algebra A C]

local notation:max "A[" f "]" => Localization.Away f
local notation:max "C[" f "]" => Localization.Away (algebraMap A C f)

noncomputable local instance localizedAwayAlgebra (f : A) : Algebra A[f] C[f] :=
  (Localization.awayMapₐ (Algebra.ofId A C) f).toAlgebra

/-
Domain-style sampling for Lemma 15.109.3:
- primary domain: commutative algebra of local product decompositions detected on principal opens
  by idempotent localizations;
- sampled owner declarations:
  `exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation`,
  `Localization.awayMapₐ`,
  `RingHom.prod_bijective_of_isIdempotentElem`,
  `quotient_isLocalization_Away_one_sub_of_idempotent_generator`;
- best owner abstraction: the public local comparison morphisms should stay at the canonical
  `Localization.awayMapₐ` surface; the local hypothesis is already the localized owner-level datum
  produced upstream by
  `exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation`, while the
  idempotent quotient/product decomposition and the finite-cover gluing argument are derived API
  rather than parallel owner declarations. The owner property on the comparison maps is still
  `Function.Bijective`; the local complementary splitting is supplied by
  `RingHom.prod_bijective_of_isIdempotentElem`, and the quotient-localization bridge by
  `quotient_isLocalization_Away_one_sub_of_idempotent_generator`;
- primitive vs. derived:
  primitive data are the finitely generated ideal `I` and, for each `f ∈ I`, an idempotent in
  `A_f` whose associated away localization identifies `C_f`;
  derived API is the complementary quotient ideal `J`, with local bijectivity of the canonical
  away maps into `C × A ⧸ J`.

Source/core/bridge triage:
- `source-facing`: the existence theorem below;
- `core/canonical`: `Localization.awayMapₐ` for the localized comparison maps and
  `RingHom.prod_bijective_of_isIdempotentElem` together with
  `quotient_isLocalization_Away_one_sub_of_idempotent_generator` for the idempotent splitting and
  quotient-localization bridge, with target property `Function.Bijective`;
- `bridge/view`: quotient/product decompositions produced from the local idempotents. -/

-- Proof sketch: choose generators of `I`, write each localized algebra `C_f` as a localization of
-- `A_f` away from an idempotent, construct the complementary quotient ideal `J` from the
-- corresponding idempotent data, and then use the finite gluing criterion for local isomorphisms
-- on the cover by the chosen generators to extend the local product decomposition to every
-- `f ∈ I`.
/-- Lemma 15.109.3: if `I` is finitely generated and for each `f ∈ I` the localized map
`A_f → C_f` is localization away from an idempotent of `A_f`, then there exists a quotient ideal
`J ⊂ A` such that for every `f ∈ I` the localized map `A_f → (C × A ⧸ J)_f` is bijective. This
is the canonical quotient-algebra form of the source’s surjective complementary factor. -/
theorem exists_quotient_factor_of_localizationAway_idempotent_on_fg_ideal
    (I : Ideal A)
    (hI : I.FG)
    (hAway :
      ∀ ⦃f : A⦄, f ∈ I → ∃ e : A[f],
        IsIdempotentElem e ∧ IsLocalization.Away e C[f]) :
    ∃ J : Ideal A, ∀ ⦃f : A⦄, f ∈ I →
      Function.Bijective (Localization.awayMapₐ (Algebra.ofId A (C × A ⧸ J)) f) := sorry

end
