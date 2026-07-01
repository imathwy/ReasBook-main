import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.143.1 (1): the textbook notion that `R → S` is étale is the canonical typeclass
`Algebra.Etale R S`, i.e. finite presentation together with vanishing of `Ω[S⁄R]` and
`H1Cotangent R S`. -/
recall Algebra.Etale

/- Definition 10.143.1 (2): the textbook notion that `R → S` is étale at the prime `q` is the
canonical local notion `Algebra.IsEtaleAt R q.asIdeal`. -/
recall Algebra.IsEtaleAt

-- Proof sketch: if `S_q` is formally étale over `R`, apply
-- `Algebra.exists_etale_of_isEtaleAt` to obtain an element `g ∉ q` with `S_g` étale. Conversely,
-- if such a `g` exists, then the basic open `D(g)` lies in the étale locus by
-- `Algebra.basicOpen_subset_etaleLocus_iff_etale`, and since `q ∈ D(g)` this implies
-- `Algebra.IsEtaleAt R q.asIdeal`.
/-- Local étaleness at a prime is equivalent to the existence of an étale basic-open neighborhood
of that prime. -/
theorem isEtaleAt_iff_exists_etale_away [FinitePresentation R S] (q : PrimeSpectrum S) :
    IsEtaleAt R q.asIdeal ↔ ∃ g : S, g ∉ q.asIdeal ∧ Etale R (Localization.Away g) := by
  constructor
  · intro hq
    letI : IsEtaleAt R q.asIdeal := hq
    exact exists_etale_of_isEtaleAt q.asIdeal
  · rintro ⟨g, hg, hEtale⟩
    rw [← mem_etaleLocus_iff]
    have hsubset : ↑(PrimeSpectrum.basicOpen g) ⊆ etaleLocus R S :=
      basicOpen_subset_etaleLocus_iff_etale.2 hEtale
    exact hsubset <| (PrimeSpectrum.mem_basicOpen g q).2 hg

end Algebra
