import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for Lemma 10.31.1:
- primary domain: commutative algebra, specifically canonical Noetherianity transfer theorems for
  finite type algebras and localizations;
- inspected owner declarations:
  `Algebra.FiniteType.isNoetherianRing`,
  `IsLocalization.isNoetherianRing`,
  `isNoetherianRing_iff_ideal_fg`,
  `Ideal.fg_of_isNoetherianRing`;
- best owner abstraction: `IsNoetherianRing` as the ambient owner predicate, with the two transfer
  theorems above providing the canonical constructions used in the textbook clauses;
- primitive data: a finite type algebra structure or a localization structure over a Noetherian
  base ring;
- derived API: the induced `IsNoetherianRing` instance/property on the target ring.

Source/core/bridge triage:
- `source-facing`: the two textbook permanence statements for Noetherian rings;
- `core/canonical`: `Algebra.FiniteType.isNoetherianRing` and
  `IsLocalization.isNoetherianRing`;
- `bridge/view`: ideal-theoretic reformulations such as `isNoetherianRing_iff_ideal_fg` and
  `Ideal.fg_of_isNoetherianRing`. -/

section FiniteTypeCase

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.FiniteType R A] [IsNoetherianRing R]

/- Lemma 10.31.1 (1) (Stacks tag `00FN`): any finite type algebra over a Noetherian ring is
Noetherian. This is the exact canonical theorem `Algebra.FiniteType.isNoetherianRing`. -/
#check (Algebra.FiniteType.isNoetherianRing R A : IsNoetherianRing A)

end FiniteTypeCase

section LocalizationCase

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Submonoid R} {S : Type v} [CommRing S] [Algebra R S] [IsLocalization M S]

/- Lemma 10.31.1 (2): any localization of a Noetherian ring is Noetherian. In mathlib this is the
canonical theorem `IsLocalization.isNoetherianRing`, stated more generally for localizations of
Noetherian commutative semirings. -/
recall IsLocalization.isNoetherianRing

end LocalizationCase
