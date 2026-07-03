import Mathlib
import StacksProject_2024.Chap15.Definition_15_81_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: relative finite presentation of modules under localization;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.FinitePresentation`,
  `Module.finitePresentation_of_finitePresentationRelativeTo`,
  `LocalizedModule.Away`,
  `IsLocalization.Away.finitePresentation`;
- best owner abstraction: the source-facing predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation of the ambient algebra together with
  finite presentation of the induced module over that polynomial ring;
- derived API: localization statements and ordinary finite presentation over the target algebra.

Source/core/bridge triage:
- `source-facing`: the localization theorem below for relative finite presentation;
- `core/canonical`: `Module.FinitePresentation`;
- `bridge/view`: passage from the localized source-facing owner over `Localization.Away f` to the
  localized target owner over `R`.

The raw existential in the original statement is exactly the primitive data already owned by
`Module.FinitePresentationRelativeTo`, so the theorem should use that owner directly rather than
repeat the witness package locally. -/

variable {R : Type u} [CommRing R]
variable {f : R}
variable {A : Type v} [CommRing A] [Algebra R A] [Algebra (Localization.Away f) A]
variable [IsScalarTower R (Localization.Away f) A]
variable {g : A}
variable {M : Type w} [AddCommGroup M] [Module A M]

-- Proof sketch: choose a polynomial presentation of `A` over `Localization.Away f`, rewrite
-- `Localization.Away f` as an `R`-algebra obtained by adjoining an inverse to `f`, then localize
-- the presentation further at `g` by adjoining an inverse to `g`; this gives a polynomial
-- presentation of `LocalizedModule.Away g M` over `R`.
/-- Lemma 15.81.4: if `M` is finitely presented relative to the localized base
`Localization.Away f` as an `A`-module, then the localized module `Away g M` is
finitely presented relative to `R` as a `Localization.Away g`-module. -/
theorem Module.finitePresentationRelativeTo_localizationAway_from_localizedBase
    (hM : Module.FinitePresentationRelativeTo (Localization.Away f) A M) :
    Module.FinitePresentationRelativeTo R (Localization.Away g) (Away g M) := sorry

end
