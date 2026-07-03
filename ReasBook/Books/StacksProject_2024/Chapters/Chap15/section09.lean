import Mathlib
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Locally

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_9_1 (from Chap15) -/
/-
Domain-style sampling:
* primary domain: commutative algebra of away localizations, quotient algebras, and étale
  morphisms;
* sampled owner declarations:
  `Localization.Away`,
  `Ideal.Quotient.mk_surjective`,
  `IsLocalization.atUnit`,
  `Algebra.Etale.of_isLocalizationAway`,
  `IsLocalization.Away.algebraMap_isUnit`;
* best owner abstraction: the lifted element `u : A` together with the canonical owner
  `Localization.Away u`; the primitive quotient datum is the canonical `(A ⧸ I)`-algebra map
  `A ⧸ I →ₐ[A ⧸ I] ((Localization.Away u) ⧸ Ideal.map (algebraMap A (Localization.Away u)) I)`;
  the quotient algebra equivalence is the canonical bridge/view `IsLocalization.atUnit`, while
  bijectivity, étaleness, and invertibility are owner-derived API for `Localization.Away u`;
* layer: clause `(1)` is `source-facing`, while clause `(2)` is the attached `bridge/view`
  exposing only the quotient algebra equivalence;
* primitive data: the lift `u` and the canonical quotient algebra equivalence from
  `IsLocalization.atUnit`;
* derived API from the owner `Localization.Away u`: `Algebra.Etale A (Localization.Away u)` and
  `IsUnit (algebraMap A (Localization.Away u) u)`.
-/

universe u

section

variable {A : Type u} [CommRing A] (I : Ideal A)

open Ideal.Quotient (eq_zero_iff_mem)

local notation:max "AwayQuot(" u ")" =>
  ((Localization.Away u) ⧸ Ideal.map (algebraMap A (Localization.Away u)) I)

private noncomputable def awayLiftToQuotient {u_bar : A ⧸ I} {u : A}
    (hu : Ideal.Quotient.mk I u = u_bar) (hu_bar : IsUnit u_bar) :
    Localization.Away u →ₐ[A] A ⧸ I :=
  let f : A →+* A ⧸ I := Ideal.Quotient.mk I
  let huLift : IsUnit (f u) := by
    simpa [f, hu] using hu_bar
  { toRingHom := IsLocalization.Away.lift u huLift
    commutes' := by
      intro a
      change IsLocalization.Away.lift u huLift (algebraMap A (Localization.Away u) a) = f a
      simpa [f] using IsLocalization.Away.lift_eq u huLift a }

private theorem awayLiftToQuotient_surjective {u_bar : A ⧸ I} {u : A}
    (hu : Ideal.Quotient.mk I u = u_bar) (hu_bar : IsUnit u_bar) :
    Function.Surjective (awayLiftToQuotient I hu hu_bar) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨algebraMap A (Localization.Away u) a, ?_⟩
  change awayLiftToQuotient I hu hu_bar (algebraMap A (Localization.Away u) a) = Ideal.Quotient.mk I a
  simp [awayLiftToQuotient]

private theorem awayQuotIdeal_le_ker_awayLiftToQuotient {u_bar : A ⧸ I} {u : A}
    (hu : Ideal.Quotient.mk I u = u_bar) (hu_bar : IsUnit u_bar) :
    Ideal.map (algebraMap A (Localization.Away u)) I ≤ RingHom.ker (awayLiftToQuotient I hu hu_bar) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change awayLiftToQuotient I hu hu_bar (algebraMap A (Localization.Away u) a) = 0
  rw [show awayLiftToQuotient I hu hu_bar (algebraMap A (Localization.Away u) a) =
      Ideal.Quotient.mk I a by simp [awayLiftToQuotient]]
  exact eq_zero_iff_mem.mpr ha

private theorem ker_awayLiftToQuotient_eq_awayQuotIdeal {u_bar : A ⧸ I} {u : A}
    (hu : Ideal.Quotient.mk I u = u_bar) (hu_bar : IsUnit u_bar) :
    RingHom.ker (awayLiftToQuotient I hu hu_bar) =
      Ideal.map (algebraMap A (Localization.Away u)) I := by
  ext z
  constructor
  · intro hz
    have hz0 : awayLiftToQuotient I hu hu_bar z = 0 := by
      exact RingHom.mem_ker.mp hz
    obtain ⟨n, a, hzsurj⟩ := IsLocalization.Away.surj u z
    have hza0 : Ideal.Quotient.mk I a = 0 := by
      have hmap : awayLiftToQuotient I hu hu_bar z * Ideal.Quotient.mk I u ^ n = Ideal.Quotient.mk I a := by
        simpa [awayLiftToQuotient, map_mul, map_pow] using
          congrArg (awayLiftToQuotient I hu hu_bar) hzsurj
      simpa [hz0, hu] using hmap.symm
    have haI : a ∈ I := eq_zero_iff_mem.mp hza0
    have hzmul : z * algebraMap A (Localization.Away u) u ^ n ∈
        Ideal.map (algebraMap A (Localization.Away u)) I := by
      simpa [hzsurj] using Ideal.mem_map_of_mem (algebraMap A (Localization.Away u)) haI
    have huPowUnit : IsUnit (algebraMap A (Localization.Away u) u ^ n) :=
      IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit u)
    rcases huPowUnit with ⟨w, hw⟩
    have hw_inv : algebraMap A (Localization.Away u) u ^ n * ↑w⁻¹ = 1 := by
      simpa [hw] using w.mul_inv
    have hz_eq : z = (z * algebraMap A (Localization.Away u) u ^ n) * ↑w⁻¹ := by
      calc
        z = z * 1 := by simp
        _ = z * (algebraMap A (Localization.Away u) u ^ n * ↑w⁻¹) := by rw [hw_inv]
        _ = (z * algebraMap A (Localization.Away u) u ^ n) * ↑w⁻¹ := by rw [mul_assoc]
    rw [hz_eq]
    exact (Ideal.map (algebraMap A (Localization.Away u)) I).mul_mem_right _ hzmul
  · intro hz
    exact awayQuotIdeal_le_ker_awayLiftToQuotient I hu hu_bar hz

private noncomputable def awayQuotAlgEquivQuotient {u_bar : A ⧸ I} {u : A}
    (hu : Ideal.Quotient.mk I u = u_bar) (hu_bar : IsUnit u_bar) :
    AwayQuot(u) ≃ₐ[A] A ⧸ I :=
  (Ideal.quotientEquivAlgOfEq A (ker_awayLiftToQuotient_eq_awayQuotIdeal I hu hu_bar).symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective (awayLiftToQuotient_surjective I hu hu_bar)

-- Proof sketch: choose a lift `u : A` of `u_bar` using surjectivity of `Ideal.Quotient.mk I`.
-- Because `u_bar` is already a unit in `A ⧸ I`, the canonical localization map
-- `Localization.Away u → A ⧸ I` descends across the quotient by the extended ideal and becomes an
-- equivalence. The bijectivity of the induced quotient algebra map is the source-facing shadow of
-- that owner equivalence. The étaleness of `A → Localization.Away u` and invertibility of the
-- image of `u` are canonical owner consequences handled separately below.
/-- Lemma 15.9.1 (1): if `u_bar : A ⧸ I` is a unit, then there exists a lift `u : A` whose
principal localization makes the canonical quotient algebra map bijective. The étaleness and
invertibility properties needed later are owner-derived consequences of `Localization.Away u`,
not primitive payload of this source-facing clause. -/
theorem exists_localizationAway_lift_of_isUnit_quotient
    {u_bar : A ⧸ I} (hu_bar : IsUnit u_bar) :
    ∃ u : A,
      Ideal.Quotient.mk I u = u_bar ∧
        Function.Bijective (algebraMap (A ⧸ I) AwayQuot(u)) := by
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective u_bar
  let e : AwayQuot(u) ≃ₐ[A] A ⧸ I := awayQuotAlgEquivQuotient I hu hu_bar
  have he : Function.LeftInverse e (algebraMap (A ⧸ I) AwayQuot(u)) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change e (Ideal.Quotient.mk _ (algebraMap A (Localization.Away u) a)) = Ideal.Quotient.mk I a
    simp [e, awayQuotAlgEquivQuotient, awayLiftToQuotient]
  have hinj : Function.Injective (algebraMap (A ⧸ I) AwayQuot(u)) := he.injective
  have hsurj : Function.Surjective (algebraMap (A ⧸ I) AwayQuot(u)) := by
    intro y
    refine ⟨e y, ?_⟩
    apply e.injective
    simpa using he (e y)
  exact ⟨u, hu, ⟨hinj, hsurj⟩⟩

-- Proof sketch: part `(1)` gives bijectivity of the canonical quotient algebra map, and
-- `AlgEquiv.ofBijective` upgrades that canonical owner map to the desired quotient algebra
-- equivalence.
/-- Lemma 15.9.1 (2): if `u_bar : A ⧸ I` is a unit, then some lift `u : A` induces an
`(A ⧸ I)`-algebra isomorphism from `A ⧸ I` to the quotient of `Localization.Away u` by the
extended ideal. This is the bridge/view clause attached to part `(1)`. -/
theorem exists_quotientAlgEquiv_localizationAway_of_isUnit_quotient
    {u_bar : A ⧸ I} (hu_bar : IsUnit u_bar) :
    ∃ (u : A) (_eIso : (A ⧸ I) ≃ₐ[A ⧸ I] AwayQuot(u)),
      Ideal.Quotient.mk I u = u_bar := by
  obtain ⟨u, hu, hbij⟩ := exists_localizationAway_lift_of_isUnit_quotient I hu_bar
  have hbij' : Function.Bijective (Algebra.ofId (A ⧸ I) AwayQuot(u)) := by
    simpa using hbij
  exact ⟨u, AlgEquiv.ofBijective (Algebra.ofId (A ⧸ I) AwayQuot(u)) hbij', hu⟩

-- Proof sketch: every quotient element has a lift by `Ideal.Quotient.mk_surjective`, and every
-- away-localization is étale by `Algebra.Etale.of_isLocalizationAway`, so the unit hypothesis is
-- redundant here.
/-- Lemma 15.9.1 (3): every `u_bar : A ⧸ I` admits a lift `u : A` such that
`A → Localization.Away u` is étale. The unit hypothesis from the source is redundant because
every away-localization is canonically étale. -/
theorem exists_etale_localizationAway_lift_of_quotient
    (u_bar : A ⧸ I) :
    ∃ u : A, Ideal.Quotient.mk I u = u_bar ∧
      Algebra.Etale A (Localization.Away u) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u_bar
  exact ⟨u, rfl, Algebra.Etale.of_isLocalizationAway u⟩

-- Proof sketch: every quotient element lifts, and its lift becomes a unit in the away-localization
-- by `IsLocalization.Away.algebraMap_isUnit`, so the unit hypothesis is redundant here.
/-- Lemma 15.9.1 (4): every `u_bar : A ⧸ I` admits a lift `u : A` whose image is a unit in
`Localization.Away u`. The unit hypothesis from the source is redundant because this is a
canonical property of away-localizations. -/
theorem exists_isUnit_localizationAway_lift_of_quotient
    (u_bar : A ⧸ I) :
    ∃ u : A, Ideal.Quotient.mk I u = u_bar ∧
      IsUnit (algebraMap A (Localization.Away u) u) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u_bar
  exact ⟨u, rfl, IsLocalization.Away.algebraMap_isUnit u⟩

end

/-! ### Lemma_15_9_2 (from Chap15) -/
universe u

namespace Algebra

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
* sampled owner declarations:
  `exists_etale_lift_to_quotient_of_smooth`,
  `IsIdempotentElem`,
  `Ideal.Quotient.mk`;
* `source-facing`: the étale-local lifting statement for one idempotent in `A ⧸ I`;
* `core/canonical`: the smooth lifting owner `exists_etale_lift_to_quotient_of_smooth`;
* `bridge/view`: this theorem is the idempotent-specialized consequence obtained from that owner
  by applying it to the standard smooth algebra carrying a universal idempotent section.

Primitive data: the quotient idempotent `ebar`.
Derived API: the quotient isomorphism `eIso` and the lifted idempotent `e'`.

To match the surrounding Chapter 15 owner surface, the quotient isomorphism is exposed as a primary
binder, not hidden inside a trailing nested existential after `e'`.
-/

-- Proof sketch: apply the smooth lifting owner theorem `exists_etale_lift_to_quotient_of_smooth`
-- to the standard smooth `A`-algebra representing an idempotent section reducing to `ebar`. The
-- resulting étale algebra `A'`, quotient isomorphism `eIso`, and lifted section `e'` give the
-- desired idempotent lift.
/-- Lemma 15.9.2: for an idempotent `ebar` in the quotient ring `A ⧸ I`, there exists an étale
`A`-algebra `A'` whose reduction modulo `I` is canonically isomorphic to `A ⧸ I`, together with an
idempotent `e' ∈ A'` mapping to `ebar` under that isomorphism. -/
theorem exists_etale_idempotent_lift_of_quotient (I : Ideal A) (ebar : A ⧸ I)
    (hebar : IsIdempotentElem ebar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I)) (e' : A'),
      IsIdempotentElem e' ∧
        eIso ebar = Ideal.Quotient.mk (Ideal.map (algebraMap A A') I) e' := by
  sorry

end

end Algebra

/-! ### Lemma_15_9_3 (from Chap15) -/
open PrimeSpectrum Set TopologicalSpace

universe u v

namespace Algebra

section

variable {A : Type u} [CommRing A]
variable {ι : Type v}

/- Domain-style sampling:
* primary domain: finite pairwise disjoint open covers of prime spectra and their étale lifting
  along quotient isomorphisms;
* sampled owner declarations:
  `TopologicalSpace.IsOpenCover`,
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`,
  `PrimeSpectrum.isIdempotentElemEquivClopens`,
  `exists_etale_idempotent_lift_of_quotient`;
* `source-facing`: a finite pairwise disjoint open cover of `Spec(A ⧸ I)` and its étale lift;
* `core/canonical`: clopen subsets of `Spec` classified by idempotents, together with the
  single-idempotent lifting theorem from Lemma `15.9.2`;
* `bridge/view`: the finite `Clopens`-valued lifting step used internally after upgrading each open
  piece of the source cover to a clopen.

Primitive data for the lifting argument: the quotient ideal `I`, a family
`Ubar : ι → Opens (PrimeSpectrum (A ⧸ I))` on a finite index type `[Finite ι]`, and the
hypotheses that these opens form a pairwise disjoint cover. Derived API: every member of such a
cover is automatically clopen, so the lifting step can run on the corresponding finite family in
`Clopens`. The output data are the lifted étale algebra `A'`, quotient isomorphism `eIso`, and
lifted clopen family `U' : ι → Clopens (PrimeSpectrum A')`.

This file keeps the textbook finite open-cover statement as the public `source-facing` theorem and
uses the finite `Clopens`-valued lifting step only as internal bridge data. No wrapper structure is
introduced. -/

private theorem isClopen_of_isOpenCover_of_pairwise_disjoint
    {X : Type*} [TopologicalSpace X] {U : ι → Opens X} (hCover : IsOpenCover U)
    (hDisjoint : Pairwise fun i j ↦ Disjoint (U i : Set X) (U j : Set X)) (j : ι) :
    IsClopen (U j : Set X) := by
  refine ⟨IsClosed.mk ?_, (U j).isOpen⟩
  have hCompl :
      (U j : Set X)ᶜ = ⋃ i ∈ {i | i ≠ j}, (U i : Set X) := by
    ext x
    constructor
    · intro hx
      have hxCover : x ∈ ⋃ i, (U i : Set X) := by
        simpa [hCover.iSup_set_eq_univ] using (Set.mem_univ x)
      rcases mem_iUnion.mp hxCover with ⟨i, hxi⟩
      have hij : i ≠ j := by
        intro hij
        subst hij
        exact hx hxi
      exact mem_iUnion₂.mpr ⟨i, hij, hxi⟩
    · intro hx hxj
      rcases mem_iUnion₂.mp hx with ⟨i, hij, hxi⟩
      exact (Set.disjoint_right.mp (hDisjoint hij) hxj) hxi
  rw [hCompl]
  exact isOpen_biUnion fun i _ ↦ (U i).isOpen

section

variable [Finite ι]

-- Internal bridge: once the finite source cover is presented by clopens, the lifting step is a
-- finite family of clopens on the same index type.
private theorem exists_etale_lift_of_finite_disjoint_clopen_cover_of_spec_quotient
    (I : Ideal A) (Ubar : ι → Clopens (PrimeSpectrum (A ⧸ I)))
    (hCover : IsOpenCover fun j ↦ (Ubar j).toOpens)
    (hDisjoint :
      Pairwise fun i j ↦ Disjoint
        (Ubar i : Set (PrimeSpectrum (A ⧸ I))) (Ubar j : Set (PrimeSpectrum (A ⧸ I)))) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ I.map (algebraMap A A')))
      (U' : ι → Clopens (PrimeSpectrum A')),
        (IsOpenCover fun j ↦ (U' j).toOpens) ∧
          (Pairwise fun i j ↦ Disjoint (U' i : Set (PrimeSpectrum A')) (U' j : Set (PrimeSpectrum A'))) ∧
          ∀ j,
            comap eIso.toRingHom ⁻¹' (Ubar j : Set (PrimeSpectrum (A ⧸ I))) =
              comap (Ideal.Quotient.mk (I.map (algebraMap A A'))) ⁻¹'
                (U' j : Set (PrimeSpectrum A')) := by
  sorry

-- Proof sketch: upgrade the finite open family `Ubar` to a `Clopens`-valued family using
-- `isClopen_of_isOpenCover_of_pairwise_disjoint`, apply the internal finite clopen-family lifting
-- theorem above, and then forget back to `Opens` in the source-facing conclusion.
/-- Lemma 15.9.3: a pairwise disjoint open cover of `Spec(A ⧸ I)` lifts, after an étale extension
`A → A'` inducing an isomorphism on the quotient by `I`, to a pairwise disjoint clopen cover of
`Spec(A')`. The source hypothesis is a finite indexed cover, exposed here by `[Finite ι]`. -/
theorem exists_etale_lift_of_finite_disjoint_open_cover_of_spec_quotient
    (I : Ideal A) (Ubar : ι → Opens (PrimeSpectrum (A ⧸ I))) (hCover : IsOpenCover Ubar)
    (hDisjoint :
      Pairwise fun i j ↦ Disjoint
        (Ubar i : Set (PrimeSpectrum (A ⧸ I))) (Ubar j : Set (PrimeSpectrum (A ⧸ I)))) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ I.map (algebraMap A A')))
      (U' : ι → Clopens (PrimeSpectrum A')),
        (IsOpenCover fun j ↦ (U' j).toOpens) ∧
          (Pairwise fun i j ↦ Disjoint (U' i : Set (PrimeSpectrum A')) (U' j : Set (PrimeSpectrum A'))) ∧
          ∀ j,
            comap eIso.toRingHom ⁻¹' (Ubar j : Set (PrimeSpectrum (A ⧸ I))) =
              comap (Ideal.Quotient.mk (I.map (algebraMap A A'))) ⁻¹'
                (U' j : Set (PrimeSpectrum A')) := by
  let UbarClopen : ι → Clopens (PrimeSpectrum (A ⧸ I)) := fun j ↦
    Clopens.mk (Ubar j) (isClopen_of_isOpenCover_of_pairwise_disjoint hCover hDisjoint j)
  have hCoverClopen : IsOpenCover fun j ↦ (UbarClopen j).toOpens := by
    simpa [UbarClopen]
  have hDisjointClopen :
      Pairwise fun i j ↦ Disjoint
        (UbarClopen i : Set (PrimeSpectrum (A ⧸ I)))
        (UbarClopen j : Set (PrimeSpectrum (A ⧸ I))) := by
    intro i j hij
    simpa [UbarClopen] using hDisjoint hij
  obtain ⟨A', hA'Ring, hA'Alg, hA'Etale, eIso, U', hCover', hDisjoint', hcomp⟩ :=
    exists_etale_lift_of_finite_disjoint_clopen_cover_of_spec_quotient
      I UbarClopen hCoverClopen hDisjointClopen
  refine ⟨A', hA'Ring, hA'Alg, hA'Etale, eIso, U', hCover', hDisjoint', ?_⟩
  intro j
  simpa [UbarClopen] using hcomp j

end

end

end Algebra

/-! ### Lemma_15_9_4 (from Chap15) -/
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

/-! ### Lemma_15_9_5 (from Chap15) -/
open Polynomial

universe u

namespace Algebra

section

variable {A : Type u} [CommRing A]

-- Proof sketch: use the universal coprime factorization algebra for the monic polynomial `f`. The
-- given factorization over `A ⧸ I` yields an `A`-algebra map from this universal algebra to
-- `A ⧸ I`. By Example `10.143.12` the universal algebra is étale at every point over the kernel of
-- that map; Lemma `15.9.4` gives a localization `B_g` that is étale over `A` and still maps onto
-- `A ⧸ I`. Applying Lemmas `10.143.8` and `10.143.9` to the induced quotient map produces an
-- idempotent localization whose reduction modulo `I` is isomorphic to `A ⧸ I`, and the universal
-- factorization descends to the required lifted monic factorization.
/-- Lemma 15.9.5: if a monic polynomial `f ∈ A[X]` has a factorization modulo `I` as a product of
monic coprime factors `ḡ * h̄`, then after an étale base change `A → A'` inducing an isomorphism
`A ⧸ I ≃ A' ⧸ IA'`, the polynomial `f` factors as a product of monic lifts `g' * h'` whose
reductions modulo `IA'` recover the given factorization. -/
theorem exists_etale_lift_factorization_of_monic_mod_ideal
    (I : Ideal A) (f : A[X]) (gbar hbar : (A ⧸ I)[X]) (hf : f.Monic) (hgbar : gbar.Monic)
    (hhbar : hbar.Monic) (hfactor : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (g' h' : A'[X]),
        g'.Monic ∧
          h'.Monic ∧
          f.map (algebraMap A A') = g' * h' ∧
          gbar.map quotientAlgEquiv.toRingHom =
            g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) ∧
          hbar.map quotientAlgEquiv.toRingHom =
            h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) :=
  sorry

end

end Algebra

/-! ### Lemma_15_9_6 (from Chap15) -/
open Polynomial

universe u

namespace Algebra

section

variable {A : Type u} [CommRing A]

-- Proof sketch: lift the unit leading coefficient of `gbar` to a unit after an étale localization
-- using Lemma `15.9.1`, rescale `gbar` and `hbar` so that both become monic modulo `I`, and then
-- apply the monic lifting statement of Lemma `15.9.5`. Finally rescale the lifted factors back by
-- the lifted unit to recover a lift of the original factorization.
/-- Lemma 15.9.6: if a monic polynomial `f` factors modulo `I` as `gbar * hbar`, with invertible
leading coefficient for `gbar` and with `gbar`, `hbar` generating the unit ideal in
`(A ⧸ I)[X]`, then after an étale base change `A → A'` inducing an isomorphism
`A ⧸ I ≃ A' ⧸ IA'`, the polynomial `f` admits a factorization `g' * h'` lifting the given
factorization over `A ⧸ I`. -/
theorem exists_etale_factorization_lift_of_isUnit_leadingCoeff
    (I : Ideal A) (f : A[X]) (gbar hbar : (A ⧸ I)[X]) (hf : f.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hunit : IsUnit gbar.leadingCoeff) (hcoprime : IsCoprime gbar hbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (g' h' : A'[X]),
        f.map (algebraMap A A') = g' * h' ∧
          gbar.map quotientAlgEquiv.toRingHom =
            g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) ∧
          hbar.map quotientAlgEquiv.toRingHom =
            h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) :=
  sorry

end

end Algebra

/-! ### Example_15_9_7 (from Chap15) -/
/-
Domain-style sampling for Example 15.9.7:
* primary domain: polynomial factorizations over quotient rings and their étale lifting in Chapter
  15;
* sampled owner declarations:
  `Algebra.exists_etale_factorization_lift_of_isUnit_leadingCoeff`,
  `Algebra.exists_etale_lift_factorization_of_monic_mod_ideal`,
  `Algebra.exists_quotientAlgEquiv_localizationAway_of_isUnit_quotient`;
* best owner abstraction: the chapter owner for the lifting problem is
  `Algebra.exists_etale_factorization_lift_of_isUnit_leadingCoeff`; this example should negate that
  specialized conclusion directly, rather than introduce a parallel local witness package;
* primitive data: the ideal `4ℤ` and the reduced polynomial `2X^2 + 2X + 1`;
* derived API: its square-equals-one relation, the resulting self-coprimeness, the failure of
  unit-leading-coefficient, and the failure of the specialized étale lifting conclusion;
* layer: the explicit ideal, polynomial, and counterexample are `source-facing`, while the Chapter
  15 lifting theorem is the relevant `core/canonical` owner.
-/

open Polynomial

universe u

/-- The ideal `4ℤ` used in the counterexample of Example 15.9.7. -/
def example1597Ideal : Ideal ℤ :=
  Ideal.span ({(4 : ℤ)} : Set ℤ)

/-- The polynomial `2X^2 + 2X + 1` over `ℤ / 4ℤ` used in Example 15.9.7. -/
noncomputable def example1597ReducedFactor : (ℤ ⧸ example1597Ideal)[X] :=
  2 * X ^ 2 + 2 * X + 1

-- Proof sketch: expand the square of `2X^2 + 2X + 1` in `(ℤ / 4ℤ)[X]`. Every cross term carries a
-- factor `4`, so it vanishes in the quotient, and the remaining constant term is `1`.
/-- The polynomial of Example 15.9.7 squares to `1` modulo `4`. -/
theorem example1597_reduction_factorization :
    example1597ReducedFactor ^ 2 = 1 := sorry

-- Proof sketch: since `example1597ReducedFactor ^ 2 = 1`, the polynomial is a unit in
-- `(ℤ / 4ℤ)[X]`; any unit is coprime to itself.
/-- The reduced factor in Example 15.9.7 is coprime to itself. -/
theorem example1597_reducedFactor_isCoprime :
    IsCoprime example1597ReducedFactor example1597ReducedFactor := sorry

-- Proof sketch: the leading coefficient is the image of `2` in `ℤ / 4ℤ`. If it were a unit, then
-- `2` would be invertible modulo `4`, which is impossible because `2` is a zerodivisor in `ℤ / 4ℤ`.
/-- The leading coefficient in Example 15.9.7 is not a unit. -/
theorem example1597_reducedFactor_leadingCoeff_not_isUnit :
    ¬ IsUnit example1597ReducedFactor.leadingCoeff := sorry

-- Proof sketch: argue by contradiction. Such lift data would produce an étale `ℤ`-algebra `A'`
-- with `A' / 4A' ≃ ℤ / 4ℤ` and polynomials `g'`, `h'` lifting `2X^2 + 2X + 1` whose product is
-- `1`. The source example identifies the `2`-adic completion of any such `A'` with `ℤ₂`, where no
-- polynomial congruent to `2X^2 + 2X + 1` modulo `4` is invertible in `ℤ₂[X]`, contradiction.
/-- Example 15.9.7: for `A = ℤ`, `I = 4ℤ`, `f = 1`, and
`ḡ = h̄ = 2X^2 + 2X + 1 ∈ (ℤ / 4ℤ)[X]`, the conclusion of Lemma `15.9.6` fails: there is no
étale lift of this factorization with quotient unchanged modulo `4`. This shows the hypothesis
that the leading coefficient of `ḡ` is a unit cannot be dropped. -/
theorem example1597_no_etale_factorization_lift :
    ¬ ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra ℤ A') (_ : Algebra.Etale ℤ A')
        (quotientAlgEquiv :
          (ℤ ⧸ example1597Ideal) ≃ₐ[ℤ ⧸ example1597Ideal]
            (A' ⧸ Ideal.map (algebraMap ℤ A') example1597Ideal))
        (g' h' : A'[X]),
        (1 : ℤ[X]).map (algebraMap ℤ A') = g' * h' ∧
          example1597ReducedFactor.map quotientAlgEquiv.toRingHom =
            g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap ℤ A') example1597Ideal)) ∧
          example1597ReducedFactor.map quotientAlgEquiv.toRingHom =
            h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap ℤ A') example1597Ideal)) := sorry

/-! ### Lemma_15_9_8 (from Chap15) -/
universe u v

open Topology PrimeSpectrum
open scoped PrimeSpectrum
open Ideal.Quotient (eq_zero_iff_mem)

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: commutative algebra on `PrimeSpectrum`, zero loci, contraction ideals, and
  quotient elements;
- sampled owner declarations: `PrimeSpectrum.closure_image_comap_zeroLocus`,
  `PrimeSpectrum.zeroLocus_sup`, `PrimeSpectrum.zeroLocus_empty_iff_eq_top`,
  `StacksProject_2024.Chap10.Definition_10_17_1`'s source-facing notation owner `V(-)`;
- source/core/bridge triage:
  * source-facing: this lemma extracts an element `r : R` from a disjointness statement on spectra;
  * core/canonical: the owner objects are `PrimeSpectrum.comap`, `PrimeSpectrum.zeroLocus`, and the
    ideal identity `I ⊔ J.comap φ = ⊤`;
  * bridge/view: `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mem_comap`, and quotienting the identity
    `g + r = 1` translate the ideal statement into the quotient and image conditions appearing in
    the source wording;
  * primitive data: `φ`, `I`, `J`, and the disjointness hypothesis;
  * derived API: the quotient equation and the membership condition on `φ r`, both recovered from the
    canonical ideal-top statement `I ⊔ J.comap φ = ⊤`.
-/
-- Proof sketch: by `PrimeSpectrum.closure_image_comap_zeroLocus`, the closure of the image of
-- `V(J)` in `Spec R` is `V(J.comap φ)`. Disjointness from `V(I)` then forces
-- `zeroLocus (I ⊔ J.comap φ)` to be empty, hence `I ⊔ J.comap φ = ⊤`. Writing
-- `1 = g + r` with `g ∈ I` and
-- `r ∈ J.comap φ`, the element `r` is `1` modulo `I` and its image lies in `J`.

/-- The owner-level ideal statement behind Lemma 15.9.8: disjointness of the closed subsets
`closure (comap φ '' V(J))` and `V(I)` forces the sum ideal `I ⊔ J.comap φ` to be the unit
ideal. -/
theorem sup_comap_eq_top_of_disjoint_closure_image_zeroLocus
    (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (hdisj : Disjoint (closure (comap φ '' V(J))) (V(I))) :
    I ⊔ J.comap φ = ⊤ := by
  rw [← zeroLocus_empty_iff_eq_top, zeroLocus_sup, Set.inter_comm,
    ← closure_image_comap_zeroLocus φ J]
  simpa [Set.disjoint_iff_inter_eq_empty] using hdisj

/-- Lemma 15.9.8: if the closure of the image of `V(J)` in `Spec(R)` is disjoint from `V(I)`,
then there exists `r : R` whose image in `R ⧸ I` is `1` and whose image in `S` lies in `J`. -/
theorem exists_eq_one_mod_ideal_and_image_mem_of_disjoint_closure_image_zeroLocus
    (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (hdisj : Disjoint (closure (comap φ '' V(J))) (V(I))) :
    ∃ r : R, Ideal.Quotient.mk I r = 1 ∧ φ r ∈ J := by
  have hone : (1 : R) ∈ I ⊔ J.comap φ := by
    simpa [sup_comap_eq_top_of_disjoint_closure_image_zeroLocus φ I J hdisj]
  rcases Submodule.mem_sup.mp hone with ⟨g, hg, r, hr, hgr⟩
  refine ⟨r, ?_, Ideal.mem_comap.mp hr⟩
  simpa [map_add, map_one, eq_zero_iff_mem.mpr hg] using
    congrArg (Ideal.Quotient.mk I) hgr

end

/-! ### Lemma_15_9_9 (from Chap15) -/
open Polynomial
open Ideal.Quotient (eq_zero_iff_mem)

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.IsIntegral A B]

/- 
Domain triage:
* `source-facing`: this theorem's specialized polynomial witness for an idempotent modulo `I B`.
* `core/canonical`: the Chapter 10 owner theorem
  `RingHom.isIntegralOverIdeal_of_mem_map`, built on
  `Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map`.
* `bridge/view`: composing an annihilating polynomial for `b ^ 2 - b` with `X * (X - 1)`.

Primitive data: the quotient idempotence hypothesis on `b`.
Derived API: first obtain the owner proposition
`(algebraMap A B).IsIntegralOverIdeal I (b ^ 2 - b)` from Chapter 10, then compose its
polynomial witness with `X * (X - 1)`.

The previous local helper only repackaged the owner theorem for this one use, so the public surface
keeps only the direct existential source statement.
-/

-- Proof sketch: apply the Chapter 10 owner theorem directly to `b ^ 2 - b`, obtaining a monic
-- polynomial `g` over `A` whose non-leading coefficients lie in `I` and with
-- `aeval (b ^ 2 - b) g = 0`. Then set `f := g.comp (X * (X - 1))`. This remains monic,
-- satisfies `aeval b f = 0`, and reduces modulo `I` to `X ^ d * (X - 1) ^ d` because `g` is
-- `I`-distinguished, so `(g mod I) = X ^ d` by the canonical owner theorem
-- `Polynomial.IsDistinguishedAt.map_eq_X_pow`.
/-- Lemma 15.9.9: if `b : B` becomes idempotent modulo the extended ideal `I B`, then there is a
monic polynomial over `A` vanishing at `b` whose reduction modulo `I` is `X ^ d * (X - 1) ^ d`
for some `d ≥ 1`. -/
theorem exists_monic_polynomial_of_isIdempotentElem_mod_map
    (I : Ideal A) (b : B)
    (hb :
      IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A B)) b : B ⧸ I.map (algebraMap A B))) :
    ∃ d : ℕ, 0 < d ∧ ∃ f : A[X],
      f.Monic ∧
        aeval b f = 0 ∧
          f.map (Ideal.Quotient.mk I) = (X ^ d * (X - 1) ^ d : (A ⧸ I)[X]) := by
  have hXMonic : (X * (X - 1) : A[X]).Monic := by
    simpa using (monic_X : (X : A[X]).Monic).mul (monic_X_sub_C (1 : A))
  by_cases hA : Subsingleton A
  · letI := hA
    have hA01 : (0 : A) = 1 := Subsingleton.elim _ _
    have hB01 : (0 : B) = 1 := by
      calc
        (0 : B) = algebraMap A B 0 := by simp
        _ = algebraMap A B 1 := by simpa using congrArg (algebraMap A B) hA01
        _ = 1 := by simp
    letI : Subsingleton B := by
      refine ⟨fun x y ↦ ?_⟩
      have hzero : ∀ z : B, z = 0 := fun z ↦ by
        calc
          z = 1 * z := by simp
          _ = 0 * z := by simpa [hB01]
          _ = 0 := by simp
      exact (hzero x).trans (hzero y).symm
    refine ⟨1, Nat.one_pos, 1, ?_, ?_, ?_⟩
    · change leadingCoeff (1 : A[X]) = 1
      exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  · letI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    by_cases hB : Subsingleton B
    · letI := hB
      refine ⟨1, Nat.one_pos, X * (X - 1), hXMonic, ?_, ?_⟩
      · have hb0 : b = 0 := Subsingleton.elim _ _
        simp [hb0]
      · simpa using (mul_pow (X : (A ⧸ I)[X]) (X - 1) 1)
    · letI : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
      let J : Ideal B := I.map (algebraMap A B)
      have hsq : b ^ 2 - b ∈ J := by
        rw [← eq_zero_iff_mem]
        change (Ideal.Quotient.mk J b) ^ 2 - Ideal.Quotient.mk J b = 0
        simpa [J, pow_two, sub_eq_zero] using hb.eq
      obtain ⟨g, hgM, hg0, hgI⟩ :
          (algebraMap A B).IsIntegralOverIdeal I (b ^ 2 - b) := by
        simpa [J] using
          RingHom.isIntegralOverIdeal_of_mem_map
            (algebraMap_isIntegral_iff.mpr inferInstance) hsq
      let d := g.natDegree
      have hd : d ≠ 0 := by
        intro hd0
        have hg1 : g = 1 := hgM.natDegree_eq_zero.mp hd0
        simpa [hg1] using hg0
      let f := g.comp (X * (X - 1))
      have hXEval : aeval b (X * (X - 1) : A[X]) = b ^ 2 - b := by
        simpa [pow_two] using (mul_sub b b (1 : B))
      have hXSubNatDegree : (X - C (1 : A) : A[X]).natDegree = 1 := by
        simpa using (natDegree_X_sub_C (1 : A))
      have hXLeadingCoeff :
          leadingCoeff (X : A[X]) * leadingCoeff (X - C (1 : A) : A[X]) ≠ 0 := by
        rw [leadingCoeff_X, leadingCoeff_X_sub_C]
        simpa using (one_ne_zero : (1 : A) ≠ 0)
      have hXNatDegree : (X * (X - 1) : A[X]).natDegree ≠ 0 := by
        change natDegree ((X : A[X]) * (X - C (1 : A))) ≠ 0
        rw [natDegree_mul' hXLeadingCoeff, natDegree_X, hXSubNatDegree]
        simp
      have hfM : f.Monic := hgM.comp hXMonic hXNatDegree
      have hf0 : aeval b f = 0 := by
        change aeval b (g.comp (X * (X - 1) : A[X])) = 0
        rw [aeval_comp, hXEval]
        simpa [aeval_def] using hg0
      have hgDistinguished : g.IsDistinguishedAt I := by
        refine ⟨⟨fun {i} hi ↦ ?_⟩, hgM⟩
        simpa [d] using Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hi) (hgI i)
      have hgMap : g.map (Ideal.Quotient.mk I) = (X ^ d : (A ⧸ I)[X]) := by
        simpa [d] using hgDistinguished.map_eq_X_pow
      have hfMap : f.map (Ideal.Quotient.mk I) = (X ^ d * (X - 1) ^ d : (A ⧸ I)[X]) := by
        calc
          f.map (Ideal.Quotient.mk I)
              = (g.map (Ideal.Quotient.mk I)).comp (X * (X - 1) : (A ⧸ I)[X]) := by
                  simp [f, Polynomial.map_comp]
          _ = ((X ^ d : (A ⧸ I)[X])).comp (X * (X - 1)) := by rw [hgMap]
          _ = (X * (X - 1) : (A ⧸ I)[X]) ^ d := by simp
          _ = (X ^ d * (X - 1) ^ d : (A ⧸ I)[X]) := by
                simpa using (mul_pow (X : (A ⧸ I)[X]) (X - 1) d)
      refine ⟨d, Nat.pos_iff_ne_zero.2 hd, f, hfM, hf0, hfMap⟩

end

end Algebra

/-! ### Lemma_15_9_10 (from Chap15) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.IsIntegral A B]

/- Domain-style sampling:
- primary domain: quotient comparison maps for extended ideals under tensor base change;
- sampled owner declarations: `Ideal.le_comap_map`, `Ideal.map_map`, `Ideal.quotientMapₐ`,
  `Algebra.TensorProduct.includeLeft`;
- best owner abstraction: the quotient algebra map induced by tensor base change is the canonical
  owner `Ideal.quotientMapₐ`; the extended-ideal containment is only proof data for that owner;
- primitive data: the ideal `I` and the algebra map `includeLeft : B →ₐ[A] B ⊗[A] A'`;
- derived API: the induced quotient map on `B / I B`.

Layer triage:
- `source-facing`: the idempotent-lifting existence theorem below;
- `core/canonical`: `Ideal.quotientMapₐ`;
- `bridge/view`: the extended-ideal containment used to instantiate that quotient map. -/

omit [Algebra.IsIntegral A B] in
private theorem extendedIdeal_le_comap_extendedIdeal
    (I : Ideal A) {C : Type*} [CommRing C] [Algebra A C] (f : B →ₐ[A] C) :
    I.map (algebraMap A B) ≤
      (Ideal.map (algebraMap A C) I).comap f := by
  simpa [Ideal.map_map] using
    (show Ideal.map (algebraMap A B) I ≤
        Ideal.comap (f : B →+* C)
          (Ideal.map (f : B →+* C) (Ideal.map (algebraMap A B) I)) from
      Ideal.le_comap_map)

-- Proof sketch: choose the polynomial witness for `ebar` from Lemma `15.9.9`, then apply the
-- étale factorization lift of Lemma `15.9.6` to split it modulo `I` into the factors `X^d` and
-- `(X - 1)^d` after an étale base change inducing `A / I ≃ A' / I A'`. Evaluating the lifted
-- factors at a chosen lift of `ebar` in the tensor product gives orthogonal elements whose
-- corresponding clopen decomposition of `Spec (B ⊗[A] A')` yields an idempotent lifting `ebar`.
/-- Lemma 15.9.10: if `A → B` is integral and `ebar` is an idempotent of `B / I B`, then after an
étale base change `A → A'` inducing an isomorphism `A / I ≃ A' / I A'`, there is an idempotent in
`B ⊗[A] A'` whose image in the quotient by the extended ideal `I` is the base-change of `ebar`. -/
theorem exists_etale_baseChange_idempotent_lift_of_isIdempotentElem_mod_map
    (I : Ideal A) (ebar : B ⧸ I.map (algebraMap A B)) (hebar : IsIdempotentElem ebar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (e' : B ⊗[A] A'),
      IsIdempotentElem e' ∧
        (Ideal.quotientMapₐ (Ideal.map (algebraMap A (B ⊗[A] A')) I)
          (includeLeft : B →ₐ[A] B ⊗[A] A')
          (extendedIdeal_le_comap_extendedIdeal I
            (includeLeft : B →ₐ[A] B ⊗[A] A'))) ebar =
          Ideal.Quotient.mk (Ideal.map (algebraMap A (B ⊗[A] A')) I) e' := sorry

end

end Algebra

/-! ### Lemma_15_9_11 (from Chap15) -/
universe u v

namespace Algebra

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)
variable {Pbar : Type v} [AddCommGroup Pbar] [Module (A ⧸ I) Pbar]

/- Domain-style sampling:
- primary domain: étale lifting of finite projective modules across quotient rings;
- sampled owner declarations:
  `Module.FiniteProjective`,
  `Module.Projective.iff_split`,
  `Algebra.exists_etale_baseChange_idempotent_lift_of_isIdempotentElem_mod_map`,
  `TensorProduct.tensorQuotMapSMulEquivTensorQuot`;
- best owner abstraction: the finite-projective owner is the canonical predicate
  `Module.FiniteProjective`, while the source-facing theorem here remains the étale lifting
  existence statement; the transported quotient-module structure on `Pbar` and the concrete
  quotient model of the reduction of `P'` are derived bridge data rather than primitive owners;
- primitive data: the ideal `I` and the finite projective `(A ⧸ I)`-module `Pbar`;
- derived API: the transported `A' ⧸ IA'`-module structure on `Pbar` via `eIso`, the reduction
  quotient `P' ⧸ IA' P'`, and the quotient/tensor identification supplied canonically by
  `TensorProduct.tensorQuotMapSMulEquivTensorQuot`.

Source/core/bridge triage:
- `source-facing`: the present étale lifting theorem for a finite projective quotient module;
- `core/canonical`: `Module.FiniteProjective`;
- `bridge/view`: the quotient-model identification of reduction modulo `IA'` and the transported
  scalar action on `Pbar`. -/

-- Proof sketch: choose an idempotent projector on a finite free `(A ⧸ I)`-module whose image is
-- `Pbar`, lift the corresponding characteristic-polynomial factorization to an étale extension as
-- in Lemma `15.9.10`, and take the image of the lifted idempotent on the free `A'`-module.
/-- Lemma 15.9.11: after an étale base change `A → A'` inducing `A ⧸ I ≃ A' ⧸ IA'`, a finite
projective `A ⧸ I`-module lifts to a finite projective `A'`-module whose reduction modulo `IA'` is
linearly equivalent to the original module after transporting scalars across the quotient-ring
isomorphism. -/
theorem exists_etale_finite_projective_lift_of_finite_projective_quotient
    (hPbar : Module.FiniteProjective (A ⧸ I) Pbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (P' : Type v) (_ : AddCommGroup P') (_ : Module A' P'),
      let J : Ideal A' := Ideal.map (algebraMap A A') I
      let Q : Type u := A' ⧸ J
      let _ : CommRing Q := inferInstance
      let _ : Module Q Pbar := Module.compHom Pbar eIso.symm.toRingHom
      ∃ eP : (P' ⧸ (J • (⊤ : Submodule A' P'))) ≃ₗ[Q] Pbar,
        Module.FiniteProjective A' P' := sorry

end

end Algebra

/-! ### Lemma_15_9_12 (from Chap15) -/
open scoped TensorProduct
open Algebra

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommMonoid M] [Module A M]
variable {m : ℕ}

local notation "C" => SymmetricAlgebra A M

variable (q : (Fin m →₀ A) →ₗ[A] M)

/- Domain-style sampling:
- primary domain: symmetric-algebra presentations, tensor base change, and the conormal/Kähler
  exact sequence;
- sampled owner declarations:
  `LinearMap.lTensor`,
  `LinearMap.lTensor_surjective`,
  `lTensor_exact`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`;
- best owner abstraction: the canonical tensorized presentation maps attached to the kernel
  inclusion `i : q.ker →ₗ[A] Fin m →₀ A`, namely `i.lTensor C` and `q.lTensor C`, with the
  right-exactness of tensor product as the owner for the tensor sequence; the Kähler map is the
  source-facing specialization obtained by composing `q.lTensor C`,
  `(SymmetricAlgebra.ι A M).lTensor C`, and `Derivation.tensorProductTo` for the universal
  derivation on `C`;
- primitive data: the surjective module map `q` and the kernel inclusion
  `i : q.ker →ₗ[A] Fin m →₀ A`;
- derived API: the source-facing description of that canonical Kähler map on the standard basis of
  `Fin m →₀ A`.

Layer triage:
- `source-facing`: the conormal/Kähler exact sequence attached to the presentation `q`;
- `core/canonical`: the tensorized presentation maps `i.baseChange C` and `q.baseChange C`,
  together with the generic right-exactness owners `lTensor_exact` and
  `LinearMap.lTensor_surjective`;
- `bridge/view`: the identification of `C ⊗[A] A^{⊕ m}` with `⨁_{j=1}^m C \, dy_j`. -/

-- Proof sketch: identify the polynomial presentation `A[y₁, \ldots, y_m] → Sym_A(M)` determined
-- by `q` with the standard free presentation on the images of the basis vectors. The degree-`1`
-- term of the conormal sequence is `C ⊗_A ker(q)` by Lemma `10.13.2`, the degree-`0` term is the
-- free `C`-module on the `dy_j`, and the conormal sequence for Kähler differentials gives the
-- exactness and surjectivity.
/-- Lemma 15.9.12: if `q : A^{⊕ m} → M` is surjective and `C = Sym_A(M)`, then the polynomial
presentation of `C` induced by `q` has naive cotangent differential
`C ⊗_A ker(q) → C ⊗_A A^{⊕ m}`, and after the canonical identification
`C ⊗_A A^{⊕ m} ≃ \bigoplus_j C \, dy_j` the resulting sequence
`C ⊗_A ker(q) → \bigoplus_j C \, dy_j → Ω_{C/A} → 0`
is exact. This is the textbook complex `NL(α) = (K ⊗_A C → \bigoplus_j C \, dy_j)` written in the
equivalent library-facing tensor order `C ⊗_A K`. -/
theorem symmetricAlgebra_presentation_conormal_sequence
    (hq : Function.Surjective q) :
    let i : q.ker →ₗ[A] (Fin m →₀ A) := q.ker.subtype
    let toKaehler :
        C ⊗[A] (Fin m →₀ A) →ₗ[C] Ω[C⁄A] :=
      (KaehlerDifferential.D A C).tensorProductTo ∘ₗ
        (SymmetricAlgebra.ι A M).baseChange C ∘ₗ
        q.baseChange C
    Function.Exact (i.baseChange C) toKaehler ∧
      Function.Surjective toKaehler :=
  sorry

end

/-! ### Lemma_15_9_13 (from Chap15) -/
universe u v

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommMonoid M] [Module A M]

/- Domain triage:
- primary domain: smooth commutative algebra maps and symmetric algebras;
- sampled owner declarations:
  `Algebra.Smooth`,
  `SymmetricAlgebra`,
  `SymmetricAlgebra.algebraMapInv`,
  `Module.FiniteProjective`;
- best owner abstraction: the source-facing statement should use the canonical smoothness owner
  `Algebra.Smooth A (SymmetricAlgebra A M)` and the project-level finite-projective owner
  `Module.FiniteProjective A M`;
- primitive data: the base ring `A` and the `A`-module `M`;
- derived API: the smoothness criterion for the symmetric algebra.

Source/core/bridge triage:
- `source-facing`: the smoothness criterion for `Sym_A^*(M)`;
- `core/canonical`: `Algebra.Smooth`, `SymmetricAlgebra`, and `Module.FiniteProjective`;
- `bridge/view`: the proof sketch passes through the augmentation
  `SymmetricAlgebra.algebraMapInv` and the conormal computation of Lemma `15.9.12`. -/

-- Proof sketch: for the forward implication, use the augmentation
-- `SymmetricAlgebra.algebraMapInv : SymmetricAlgebra A M →ₐ[A] A` and Lemma `10.139.4` to identify
-- the conormal module of its kernel with `M`, since the positive-degree ideal modulo its square is
-- the degree-one piece. For the reverse implication, choose a finite free presentation of the
-- finite projective module `M`, apply the conormal-sequence computation of Lemma `15.9.12`, and
-- conclude from the characterization of smoothness in Definition `10.137.1`.
/-- Lemma 15.9.13: the symmetric algebra `Sym_A^*(M)` is smooth over `A` if and only if `M` is a
finite `A`-module and a projective `A`-module. -/
theorem smooth_symmetricAlgebra_iff_finite_and_projective :
    Algebra.Smooth A (SymmetricAlgebra A M) ↔
      Module.FiniteProjective A M := sorry

end

/-! ### Lemma_15_9_14 (from Chap15) -/
universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling:
- primary domain: étale lifting for smooth commutative algebras over a quotient;
- sampled owner declarations:
  `Algebra.Smooth`,
  `Algebra.Etale`,
  `Ideal.Quotient.mkₐ`,
  `exists_etale_finite_projective_lift_of_finite_projective_quotient`;
- best owner abstraction: the source-facing owner here is the smooth lifting existence theorem
  itself, with the comparison to the quotient expressed through the canonical quotient algebra map
  `Ideal.Quotient.mkₐ`; the quotient isomorphism is bridge data, not a separate owner;
- primitive data: the ideal `I`, the smoothness hypothesis on `A → B`, and the quotient map
  `φ : B →ₐ[A] A ⧸ I`;
- derived API: the lifted étale `A`-algebra `A'`, the quotient equivalence `eIso`, and the lifted
  algebra map `φ' : B →ₐ[A] A'` satisfying the canonical quotient-map compatibility equation.

Source/core/bridge triage:
- `source-facing`: the present existence theorem lifting `φ` étale-locally;
- `core/canonical`: the owner predicates `Algebra.Smooth` and `Algebra.Etale`, together with the
  quotient algebra map `Ideal.Quotient.mkₐ`;
- `bridge/view`: the quotient equivalence `eIso`.
-/

-- Proof sketch: use the conormal exact sequence for the surjection `B → A ⧸ I` and smoothness of
-- `A → B` to see that the conormal module is finite projective over `A ⧸ I`. Lift a complement of
-- this module after an étale base change by Lemma `15.9.11`, add the corresponding symmetric
-- algebra factor to make the conormal module free, cut down by generators of the kernel, and then
-- localize at the étale locus as in Lemma `15.9.4` to obtain the desired étale algebra `A'` and
-- lift `B → A'`.
/-- Lemma 15.9.14: if `B` is a smooth `A`-algebra equipped with an `A`-algebra map
`φ : B → A ⧸ I`, then there exists an étale `A`-algebra `A'` whose reduction modulo `I` is
canonically isomorphic to `A ⧸ I`, together with an `A`-algebra map `φ' : B → A'` lifting `φ`
through that quotient isomorphism. -/
theorem exists_etale_lift_to_quotient_of_smooth
    (I : Ideal A) [Algebra.Smooth A B] (φ : B →ₐ[A] A ⧸ I) :
    ∃ (A' : Type (max u v)) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (φ' : B →ₐ[A] A'),
      ((Ideal.Quotient.mkₐ A' (Ideal.map (algebraMap A A') I)).restrictScalars A).comp φ' =
        (eIso.toAlgHom.restrictScalars A).comp φ := sorry

end

end Algebra
