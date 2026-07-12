import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/- Domain-style sampling:
- primary domain: formal unramifiedness of commutative algebras and its behavior under
  localization;
- sampled owner declarations:
  `Algebra.FormallyUnramified`,
  `Algebra.FormallyUnramified.of_isLocalization`,
  `Algebra.FormallyUnramified.localization_map`,
  the canonical localization instance
  `[Algebra.FormallyUnramified R A] → Algebra.FormallyUnramified R (Localization M)`;
- best owner abstraction: `Algebra.FormallyUnramified R A`;
- primitive data: the commutative rings, algebra structures, the source/target submonoids, and
  the localization data;
- derived API: formal unramifiedness of the source-and-target localization map, and of target
  localizations over the original base ring.

Source/core/bridge triage:
- `source-facing`: the textbook localization lemma;
- `core/canonical`: `Algebra.FormallyUnramified` and its localization API;
- `bridge/view`: this file is a direct recall/synthesis surface for those canonical owner facts,
  so it should not keep a conjunction-valued wrapper theorem.
-/

section SourceLocalization

variable {R : Type u} {A : Type v} {Rₘ : Type w} {Aₘ : Type x}
variable [CommRing R] [CommRing A] [CommRing Rₘ] [CommRing Aₘ]
variable [Algebra R A] [Algebra R Rₘ] [Algebra R Aₘ] [Algebra A Aₘ] [Algebra Rₘ Aₘ]
variable [IsScalarTower R Rₘ Aₘ] [IsScalarTower R A Aₘ]
variable (M : Submonoid R)
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R A)) Aₘ]

/- Lemma 10.148.5 (source localization): if `R → A` is formally unramified, then the induced map
`Rₘ → Aₘ` on localizations along a multiplicative subset `M ⊆ R` is formally unramified. This is
exactly the canonical theorem `Algebra.FormallyUnramified.localization_map`. -/
recall Algebra.FormallyUnramified.localization_map

end SourceLocalization

section TargetLocalization

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.FormallyUnramified R A] (M : Submonoid A)

/- Lemma 10.148.5 (target localization): if `R → A` is formally unramified, then every
localization `A_M` is formally unramified over `R`. This is the canonical localization instance on
`Localization M`. -/
#synth Algebra.FormallyUnramified R (Localization M)

end TargetLocalization
