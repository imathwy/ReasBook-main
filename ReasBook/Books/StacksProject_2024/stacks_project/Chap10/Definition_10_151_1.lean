import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.151.1: a ring map `R → S` is unramified exactly in the canonical mathlib
sense of `Algebra.Unramified R S`, i.e. finite type together with trivial Kähler differentials
`Ω[S⁄R]`. -/
recall Algebra.Unramified

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Definition 10.151.1: a ring map `R → S` is G-unramified if it is unramified and of finite
presentation; equivalently, it is finitely presented and `Ω[S⁄R]` is trivial. -/
class GUnramified : Prop extends Unramified R S, FinitePresentation R S

/-- Definition 10.151.1: `R → S` is unramified at the prime `q` when some basic open neighborhood
`S_g` with `g ∉ q` is unramified over `R`. -/
def UnramifiedAt (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ Unramified R (Localization.Away g)

/-- Definition 10.151.1: `R → S` is G-unramified at the prime `q` when some basic open
neighborhood `S_g` with `g ∉ q` is G-unramified over `R`. -/
def GUnramifiedAt (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ GUnramified R (Localization.Away g)

/-- A formally unramified finitely presented algebra is G-unramified. -/
instance [FormallyUnramified R S] [FinitePresentation R S] : GUnramified R S where
  toUnramified := {}
  toFinitePresentation := inferInstance

-- Proof sketch: this is the exact local/global bridge from the source-facing basic-open
-- neighborhood condition to the canonical owner predicate for the localization at `q`.
/-- For finite type algebras, the source-facing condition `UnramifiedAt R S q` is equivalent to
the canonical owner predicate `IsUnramifiedAt R q.asIdeal`. -/
theorem unramifiedAt_iff_isUnramifiedAt [FiniteType R S] (q : PrimeSpectrum S) :
    UnramifiedAt R S q ↔ IsUnramifiedAt R q.asIdeal := by
  constructor
  · rintro ⟨g, hgq, _⟩
    have hsubset : ↑(PrimeSpectrum.basicOpen g) ⊆ unramifiedLocus R S := by
      rw [basicOpen_subset_unramifiedLocus_iff]
      infer_instance
    exact hsubset (by simpa using hgq)
  · intro hq
    letI : IsUnramifiedAt R q.asIdeal := hq
    simpa [UnramifiedAt] using exists_unramified_of_isUnramifiedAt q.asIdeal

-- Proof sketch: the forward direction forgets from `GUnramifiedAt` to `UnramifiedAt`; conversely,
-- under finite presentation, every principal localization stays finitely presented, so an
-- unramified basic-open neighborhood is automatically G-unramified.
/-- For finitely presented algebras, the source-facing condition `GUnramifiedAt R S q` is
equivalent to the canonical owner predicate `IsUnramifiedAt R q.asIdeal`. -/
theorem gUnramifiedAt_iff_isUnramifiedAt [FinitePresentation R S] (q : PrimeSpectrum S) :
    GUnramifiedAt R S q ↔ IsUnramifiedAt R q.asIdeal := by
  constructor
  · rintro ⟨g, hgq, _⟩
    exact (unramifiedAt_iff_isUnramifiedAt R S q).mp
      ⟨g, hgq, inferInstance⟩
  · intro hq
    rcases (unramifiedAt_iff_isUnramifiedAt R S q).mpr hq with
      ⟨g, hgq, hg⟩
    letI : Unramified R (Localization.Away g) := hg
    letI : FinitePresentation S (Localization.Away g) := IsLocalization.Away.finitePresentation g
    letI : FinitePresentation R (Localization.Away g) :=
      FinitePresentation.trans R S (Localization.Away g)
    exact ⟨g, hgq, inferInstance⟩

end Algebra
