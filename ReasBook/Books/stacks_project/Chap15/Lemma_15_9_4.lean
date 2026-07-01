import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Locally
import stacks_project.Chap10.Definition_10_143_1
import stacks_project.Chap15.Lemma_15_9_8

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum Topology
open scoped PrimeSpectrum

universe u

namespace Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling:
* primary domain: commutative algebra of the étale locus on `Spec(B)` and standard-open
  localizations `Localization.Away g`;
* sampled owner declarations:
  `Algebra.isEtaleAt_iff_exists_etale_away`,
  `Algebra.etaleLocus`,
  `Algebra.basicOpen_subset_etaleLocus_iff_etale`,
  `PrimeSpectrum.isCompact_isOpen_iff_ideal`;
* source/core/bridge triage:
  * source-facing: the main lemma takes the local neighborhood hypothesis that every point of
    `V(J)` lies in some basic open `D(f)` with `Localization.Away f` étale over `A`;
  * core/canonical: `Algebra.etaleLocus A B` packages the same local condition as a canonical
    subset of `Spec(B)`;
  * bridge/view: `Algebra.mem_etaleLocus_iff` and
    `Algebra.isEtaleAt_iff_exists_etale_away` recover the source-facing neighborhood hypothesis
    from the stronger owner-level inclusion `V(J) ⊆ etaleLocus A B`.
* best owner abstraction: keep the neighborhood supply on `V(J)` as primitive data for the main
  theorem, and treat the `etaleLocus` formulation as a stronger bridge companion;
* primitive data: the ideal `J` and the pointwise existence of étale basic-open neighborhoods on
  `V(J)`;
* derived API: the quotient-unit witness `IsUnit (Ideal.Quotient.mk J g)` and the resulting étale
  localization `Etale A (Localization.Away g)`.
-/

-- Proof sketch: cover the compact closed subset `V(J)` by basic opens `D(f)` on which
-- `Localization.Away f` is étale. A finite subcover gives a compact open subset `U` containing
-- `V(J)`. Writing `U` as the complement of `V(I)`, Lemma `15.9.8` produces `g ∈ I` whose image
-- in `B ⧸ J` is a unit. The inclusion `D(g) ⊆ U` yields a finite principal-open cover of
-- `Spec(B_g)` by the images of the chosen `D(f)`, and the canonical locality theorem
-- `RingHom.Etale.ofLocalizationSpanTarget` reconstructs `B_g` as an étale `A`-algebra.
/-- Lemma 15.9.4: if every point of `V(J)` admits an étale basic-open neighborhood, then there
exists `g : B` whose image in `B ⧸ J` is a unit and such that the localization `B_g` is étale
over `A`. -/
theorem exists_quotient_unit_and_etale_away_of_zeroLocus
    (J : Ideal B)
    (hJ : ∀ q ∈ V((J : Set B)), ∃ f : B, q ∈ D(f) ∧ Etale A (Localization.Away f)) :
    ∃ g : B, IsUnit (Ideal.Quotient.mk J g) ∧ Etale A (Localization.Away g) := by
  have hVCompact : IsCompact (V((J : Set B))) := by
    simpa using (isClosed_zeroLocus (J : Set B)).isCompact
  choose f hfmem hfetale using fun x : V((J : Set B)) ↦ hJ x.1 x.2
  obtain ⟨t, ht⟩ :=
    hVCompact.elim_finite_subcover
      (fun x : V((J : Set B)) ↦ (D(f x) : Set (PrimeSpectrum B)))
      (fun x ↦ (D(f x)).2)
      (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hfmem ⟨x, hx⟩⟩)
  let U : Set (PrimeSpectrum B) := ⋃ x : t, (D(f x.1) : Set (PrimeSpectrum B))
  have hUcompact : IsCompact U := by
    simpa [U] using isCompact_iUnion fun x : t ↦ isCompact_basicOpen (f x.1)
  have hUopen : IsOpen U := by
    simpa [U] using isOpen_iUnion fun x : t ↦ (D(f x.1)).2
  obtain ⟨I, -, hUeq⟩ :=
    isCompact_isOpen_iff_ideal.mp ⟨hUcompact, hUopen⟩
  have hVU : V((J : Set B)) ⊆ U := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (ht hx) with ⟨y, hyt, hy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hyt⟩, hy⟩
  have hZI : V((J : Set B)) ⊆ (zeroLocus (I : Set B))ᶜ := by
    simpa [hUeq] using hVU
  have hdisj :
      Disjoint
        (closure (comap (RingHom.id B) '' zeroLocus (I : Set B) : Set (PrimeSpectrum B)))
        (V((J : Set B))) := by
    rw [closure_image_comap_zeroLocus (RingHom.id B) I]
    exact Set.disjoint_left.2 fun x hxI hxJ ↦ (hZI hxJ) hxI
  obtain ⟨g, hgbar, hgI⟩ :=
    exists_eq_one_mod_ideal_and_image_mem_of_disjoint_closure_image_zeroLocus
      (RingHom.id B) J I hdisj
  have hDg : (D(g) : Set (PrimeSpectrum B)) ⊆ U := by
    rw [← hUeq, basicOpen_eq_zeroLocus_compl]
    simpa only [RingHom.id_apply] using
      Set.compl_subset_compl.mpr (zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hgI))
  let Bg := Localization.Away g
  have hspan :
      Ideal.span (Set.range fun y : t ↦ algebraMap B Bg (f y.1)) = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply TopologicalSpace.Opens.ext
    ext q
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion,
      Set.mem_univ, iff_true]
    have hqg : PrimeSpectrum.comap (algebraMap B Bg) q ∈ (D(g) : Set (PrimeSpectrum B)) := by
      rw [← PrimeSpectrum.localization_away_comap_range Bg g]
      exact ⟨q, rfl⟩
    rcases Set.mem_iUnion.mp (hDg hqg) with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change q ∈
      (TopologicalSpace.Opens.comap ⟨PrimeSpectrum.comap (algebraMap B Bg),
        PrimeSpectrum.continuous_comap (algebraMap B Bg)⟩ (PrimeSpectrum.basicOpen (f y.1)) :
        Set (PrimeSpectrum Bg))
    simpa [PrimeSpectrum.comap_basicOpen] using hy
  have hloc :
      RingHom.Locally RingHom.Etale (algebraMap A Bg) := by
    refine RingHom.locally_of_exists RingHom.Etale.respectsIso (algebraMap A Bg)
      (fun y : t ↦ algebraMap B Bg (f y.1)) hspan
      (fun y : t ↦ Localization.Away (algebraMap B Bg (f y.1))) ?_
    intro y
    let T₁ := Localization.Away (algebraMap B (Localization.Away (f y.1)) g)
    let T₂ := Localization.Away (algebraMap B Bg (f y.1))
    let e : T₁ ≃ₐ[A] T₂ :=
      (IsLocalization.algEquiv (Submonoid.powers (g * f y.1)) T₁ T₂).restrictScalars A
    have hT₁ : Etale A T₁ := by
      letI : Etale A (Localization.Away (f y.1)) := hfetale y.1
      infer_instance
    have hT₂ : Etale A T₂ := by
      letI : Etale A T₁ := hT₁
      exact Etale.of_equiv e
    have hEtaleT₂ : (algebraMap A T₂).Etale :=
      RingHom.etale_algebraMap.2 hT₂
    simpa [Bg, RingHom.algebraMap_toAlgebra, T₂] using hEtaleT₂
  have hEtaleBg : (algebraMap A Bg).Etale :=
    (RingHom.locally_iff_of_localizationSpanTarget RingHom.Etale.respectsIso
      RingHom.Etale.ofLocalizationSpanTarget (algebraMap A Bg)).mp hloc
  exact ⟨g, hgbar ▸ isUnit_one,
    RingHom.etale_algebraMap.mp hEtaleBg⟩

variable [FinitePresentation A B]

/-- Stronger bridge version of Lemma 15.9.4 obtained from the canonical owner
`Algebra.etaleLocus A B`. -/
theorem exists_quotient_unit_and_etale_away_of_zeroLocus_subset_etaleLocus
    (J : Ideal B) (hJ : V((J : Set B)) ⊆ etaleLocus A B) :
    ∃ g : B, IsUnit (Ideal.Quotient.mk J g) ∧ Etale A (Localization.Away g) := by
  apply exists_quotient_unit_and_etale_away_of_zeroLocus J
  intro q hq
  simpa [mem_basicOpen] using
    (isEtaleAt_iff_exists_etale_away A B q).mp (mem_etaleLocus_iff.mp (hJ hq))

end Algebra
