import Mathlib
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Lemma_10_161_4
import StacksProject_2024.Chap10.Lemma_10_23_2
import StacksProject_2024.Chap10.Proposition_10_162_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
- primary domain: locality of the chapter owners `UniversallyJapaneseRing` and `NagataRing`
  under a finite principal-open cover;
- sampled owner declarations of the same kind:
  - `UniversallyJapaneseRing` and `NagataRing` from `Definition_10_162_1`,
  - `isN2Ring_of_isN2Ring_localizationAway` from `Lemma_10_161_4`,
  - `AlgebraicGeometry.isNoetherianRing_of_away` from `Lemma_10_23_2`,
  - the bridge instance `[NagataRing R] → [UniversallyJapaneseRing R]` from
    `Proposition_10_162_16`.

Best owner abstraction:
- `UniversallyJapaneseRing` and `NagataRing` are already the correct source-facing owners;
- `IsN2Ring` is the core/canonical owner used to discharge both locality statements;
- the right bridge is a private helper proving `IsN2Ring A` for any finite type domain `A` over
  `R` from the localized universally-Japanese hypotheses on `R`.

Primitive data vs. derived API:
- primitive data for the helper: a finite type domain `A` over `R`, a finite cover `s`, and the
  localized owner hypotheses on `R_f`;
- derived API: the localized finite-type algebra structures `R_f → A_g`, the domain instances for
  the nonzero principal localizations of `A`, and the owner-level conclusions
  `UniversallyJapaneseRing R` and `NagataRing R`.

Source/core/bridge triage:
- `source-facing`: the two public locality theorems for `UniversallyJapaneseRing` and `NagataRing`;
- `core/canonical`: `IsN2Ring`, `UniversallyJapaneseRing`, `NagataRing`,
  `isN2Ring_of_isN2Ring_localizationAway`, and `AlgebraicGeometry.isNoetherianRing_of_away`;
- `bridge/view`: the private passage from `R_f` to the localization of a finite type domain
  `A_g`, expressed via the canonical away-localization algebra map and finite-type descent.
-/

section DomainBridge

variable {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A]

private noncomputable instance localizationAwayImageAlgebra (f : R) :
    Algebra (Localization.Away f) (Localization.Away (algebraMap R A f)) := by
  simpa [Algebra.ofId_apply] using
    (Localization.awayMapₐ (Algebra.ofId R A) f).toAlgebra

omit [IsDomain A] in
private theorem finiteType_localizationAwayImage (f : R) :
    Algebra.FiniteType (Localization.Away f) (Localization.Away (algebraMap R A f)) := by
  let φ : Localization.Away f →+* Localization.Away (algebraMap R A f) :=
    Localization.awayMap (algebraMap R A) f
  have hcomp : (φ.comp (algebraMap R (Localization.Away f))).FiniteType := by
    rw [show φ.comp (algebraMap R (Localization.Away f)) =
        algebraMap R (Localization.Away (algebraMap R A f)) by
          ext x
          simp [φ, IsLocalization.Away.map, IsLocalization.map,
            IsScalarTower.algebraMap_eq R A (Localization.Away (algebraMap R A f))]]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_comp_finiteType hcomp)

private theorem isN2Ring_of_span_eq_top_of_localizationAway_universallyJapanese (s : Finset R)
    (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, UniversallyJapaneseRing (Localization.Away f.1)) :
    IsN2Ring A := by
  let _ := (inferInstance : Algebra.FiniteType R A)
  classical
  let t : Finset A := (s.image fun f ↦ algebraMap R A f).erase 0
  have ht : Ideal.span (t : Set A) = ⊤ := by
    rw [show (t : Set A) = (((s.image fun f ↦ algebraMap R A f) : Finset A) : Set A) \ {0} by
          ext x
          simp [t]]
    rw [Ideal.span_sdiff_singleton_zero]
    rw [show ((((s.image fun f ↦ algebraMap R A f) : Finset A) : Set A)) =
        algebraMap R A '' (s : Set R) by
          ext x
          simp]
    rw [← Ideal.map_span, hs, Ideal.map_top]
  have hdom : ∀ g : t, IsDomain (Localization.Away g.1) := fun g ↦ by
    have hg_ne : g.1 ≠ 0 := by
      simpa [t] using Finset.mem_erase.mp g.2 |>.1
    exact
      IsLocalization.isDomain_of_le_nonZeroDivisors _
        (powers_le_nonZeroDivisors_of_noZeroDivisors hg_ne)
  refine isN2Ring_of_isN2Ring_localizationAway t ht hdom ?_
  rintro ⟨g, hg⟩
  have hg_ne : g ≠ 0 := by
    simpa [t] using Finset.mem_erase.mp hg |>.1
  have hg_mem : g ∈ s.image fun f ↦ algebraMap R A f := by
    exact Finset.mem_of_mem_erase hg
  obtain ⟨f, hf_mem, rfl⟩ := Finset.mem_image.mp hg_mem
  let Af : Type v := Localization.Away (algebraMap R A f)
  letI : IsDomain Af :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg_ne)
  letI : Algebra.FiniteType (Localization.Away f) Af :=
    finiteType_localizationAwayImage f
  have hUf : UniversallyJapaneseRing (Localization.Away f) := by
    simpa using h ⟨f, hf_mem⟩
  letI : UniversallyJapaneseRing (Localization.Away f) := hUf
  change IsN2Ring Af
  infer_instance

end DomainBridge

-- Proof sketch: to show `R` is universally Japanese, it suffices to check that every finite type
-- domain `A` over `R` is `N-2`. For such an `A`, remove the zero images from the principal-open
-- cover induced by `s`, so each localization `A_g` remains a domain. Each `A_g` is finite type
-- over the corresponding `R_f`, hence `N-2` by the localized universally-Japanese hypothesis; now
-- descend `N-2` along the finite cover using `isN2Ring_of_isN2Ring_localizationAway`.
/-- Lemma 10.162.7 (1): if the elements of `s` generate the unit ideal and each principal
localization `R_f` is universally Japanese, then `R` is universally Japanese. -/
theorem universallyJapaneseRing_of_localizationAway (s : Finset R)
    (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, UniversallyJapaneseRing (Localization.Away f.1)) :
    UniversallyJapaneseRing R := by
  refine ⟨fun {A} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A] ↦ ?_⟩
  exact
    isN2Ring_of_span_eq_top_of_localizationAway_universallyJapanese
      s hs h

-- Proof sketch: the Noetherian part descends from the cover via
-- `AlgebraicGeometry.isNoetherianRing_of_away`. For a prime ideal `p`, the quotient `R ⧸ p` is a
-- finite type domain over `R`; applying the previous private `IsN2Ring` bridge with the localized
-- Nagata hypotheses viewed through the canonical owner instance
-- `[NagataRing (R_f)] → [UniversallyJapaneseRing (R_f)]` proves `R ⧸ p` is `N-2`.
/-- Lemma 10.162.7 (2): if the elements of `s` generate the unit ideal and each principal
localization `R_f` is Nagata, then `R` is Nagata. -/
theorem nagataRing_of_localizationAway (s : Finset R)
    (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, NagataRing (Localization.Away f.1)) :
    NagataRing R := by
  let _ := h
  letI : IsNoetherianRing R :=
    AlgebraicGeometry.isNoetherianRing_of_away s hs fun f ↦ by
      letI : NagataRing (Localization.Away f.1) := h f
      infer_instance
  refine NagataRing.mk ?_
  intro p hp
  letI : p.IsPrime := hp
  let hU : ∀ f : s, UniversallyJapaneseRing.{u, u} (Localization.Away f.1) := fun f ↦ by
    letI : NagataRing (Localization.Away f.1) := h f
    infer_instance
  exact
    isN2Ring_of_span_eq_top_of_localizationAway_universallyJapanese
      s hs hU

end
