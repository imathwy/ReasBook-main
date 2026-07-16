import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_137_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

open PrimeSpectrum

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for the local-global smoothness criterion:
- primary domain: smooth commutative `R`-algebras and the smooth locus on `Spec S`;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Algebra.smoothLocus_eq_univ`,
  `Algebra.smoothLocus_eq_univ_iff`,
  `Algebra.FinitePresentation.of_span_eq_top_target`,
  `PrimeSpectrum.iSup_basicOpen_eq_top_iff'`;
- best owner abstraction: the canonical global owner is the smooth locus `smoothLocus R S`
  together with the locality owner for finite presentation on a standard-open cover of `Spec S`;
- primitive data: the basic-open neighborhoods `D(g)` on which `Localization.Away g` is smooth;
- derived API: the source-facing predicate `SmoothAtPrime` and the global equivalence below.

Source/core/bridge triage:
- `source-facing`: the textbook statement `Smooth R S ↔ ∀ q, SmoothAtPrime R S q`;
- `core/canonical`: `smoothLocus R S`, `IsSmoothAt`, and
  `FinitePresentation.of_span_eq_top_target`;
- `bridge/view`: this theorem, which converts the primewise neighborhood condition into the
  canonical owner data `FormallySmooth R S` and `FinitePresentation R S`.
-/

-- Proof sketch: if `R → S` is smooth, then the smooth locus is all of `Spec S`, so every prime is
-- smooth via `smoothAtPrime_iff_isSmoothAt`. Conversely, let `s = { g | S_g is smooth over R }`.
-- The hypothesis says that the basic opens `D(g)` for `g ∈ s` cover `Spec S`, hence
-- `Ideal.span s = ⊤` by `PrimeSpectrum.iSup_basicOpen_eq_top_iff'`. The canonical locality theorem
-- `FinitePresentation.of_span_eq_top_target` yields finite presentation, while
-- `smoothLocus_eq_univ_iff` upgrades the primewise `IsSmoothAt` condition to formal smoothness.
/-- Lemma 10.137.12: the ring map `R → S` is smooth if and only if every prime of `S` admits a
basic open neighborhood on which the localized `R`-algebra is smooth, i.e. every prime satisfies
`SmoothAtPrime R S`. -/
@[stacks 00TC]
theorem smooth_iff_forall_smoothAtPrime :
    Smooth R S ↔ ∀ q : PrimeSpectrum S, SmoothAtPrime R S q := by
  constructor
  · intro hS q
    letI : Smooth R S := hS
    letI : FinitePresentation R S := hS.2
    have hsmoothLocus : smoothLocus R S = Set.univ := smoothLocus_eq_univ
    exact (smoothAtPrime_iff_isSmoothAt R S q).2 <|
      by
        simpa [smoothLocus] using
          (Set.eq_univ_iff_forall.mp hsmoothLocus) q
  · intro hq
    let s : Set S := { g | Smooth R (Localization.Away g) }
    have hscover : (⨆ g ∈ s, basicOpen g) = ⊤ := by
      apply SetLike.ext'
      change (↑(⨆ g ∈ s, basicOpen g) : Set (PrimeSpectrum S)) = Set.univ
      rw [Set.eq_univ_iff_forall]
      intro q
      rcases hq q with ⟨g, hgq, hg⟩
      have hgmem : q ∈ (basicOpen g : Set (PrimeSpectrum S)) := by
        simpa [mem_basicOpen] using hgq
      exact
        (show (basicOpen g : TopologicalSpace.Opens (PrimeSpectrum S)) ≤ ⨆ h ∈ s, basicOpen h from
          le_iSup_of_le g <| le_iSup_of_le hg le_rfl) hgmem
    have hsone : Ideal.span s = ⊤ :=
      iSup_basicOpen_eq_top_iff'.mp hscover
    have hfp : FinitePresentation R S :=
      FinitePresentation.of_span_eq_top_target s hsone fun g hg ↦ by
        letI : Smooth R (Localization.Away g) := hg
        infer_instance
    letI : FinitePresentation R S := hfp
    have hformallySmooth : FormallySmooth R S := by
      rw [← smoothLocus_eq_univ_iff]
      exact Set.eq_univ_iff_forall.mpr fun q ↦ by
        simpa [smoothLocus] using (smoothAtPrime_iff_isSmoothAt R S q).mp (hq q)
    exact ⟨hformallySmooth, hfp⟩

end Algebra
