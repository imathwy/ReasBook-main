import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_151_1 (from Chap10) -/
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

/-! ### Lemma_10_151_2 (from Chap10) -/
universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: `Algebra.Unramified R S` is defined as the conjunction of the two typeclass facts
-- `Algebra.FormallyUnramified R S` and `Algebra.FiniteType R S`, so this is the direct
-- constructor/eliminator equivalence for that class.
/-- Lemma 10.151.2 (1): a ring map is unramified exactly when it is formally unramified and of
finite type. -/
theorem unramified_iff_formallyUnramified_and_finiteType :
    Unramified R S ↔ FormallyUnramified R S ∧ FiniteType R S := by
  constructor
  · intro h
    exact ⟨h.formallyUnramified, h.finiteType⟩
  · rintro ⟨hform, hft⟩
    exact ⟨hform, hft⟩

-- Proof sketch: by definition, `Algebra.GUnramified R S` extends the owner predicate
-- `Algebra.Unramified R S` together with `Algebra.FinitePresentation R S`; combine that with the
-- previous clause characterizing `Unramified R S` by formal unramifiedness and finite type.
/-- Lemma 10.151.2 (2): a ring map is G-unramified exactly when it is formally unramified and of
finite presentation. -/
theorem gUnramified_iff_formallyUnramified_and_finitePresentation :
    GUnramified R S ↔ FormallyUnramified R S ∧ FinitePresentation R S := by
  constructor
  · intro h
    exact ⟨h.toUnramified.formallyUnramified, h.toFinitePresentation⟩
  · rintro ⟨hform, hfp⟩
    letI : FormallyUnramified R S := hform
    letI : FinitePresentation R S := hfp
    exact inferInstance

end Algebra
