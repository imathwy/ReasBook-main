import Mathlib
import StacksProject_2024.Chap15.Definition_15_107_1
import StacksProject_2024.Chap15.Lemma_15_107_7
import StacksProject_2024.Chap15.Lemma_15_107_8
import StacksProject_2024.Chap15.Lemma_15_51_11
import StacksProject_2024.Chap15.Lemma_15_108_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

/-
Domain-style sampling:
- primary domain: local commutative algebra of geometrically unibranch local domains, essential
  finite type local maps, and étale localization criteria;
- sampled owner declarations of the same kind:
  `IsLocalization`,
  `Algebra.Etale`,
  `exists_etale_localizationAway_of_geometricallyUnibranch_of_unramifiedAtPrime_of_injective_localRingHom`,
  `ideal_comap_ne_bot_of_cases`;
- best owner abstraction: the source-facing conclusion is an intermediate étale `A`-algebra `C`
  together with a localization witness `IsLocalization M B`; collapsing this to
  `Algebra.Etale A B` is too strong here, because a local ring obtained by localizing an étale
  `A`-algebra need not itself be finite presented over `A`;
- primitive data: the local domain `A`, the local `A`-algebra `B`, the injective local map,
  the maximal-ideal equality, the separable residue-field extension, and the essential finite type
  hypothesis;
- derived API: an étale `A`-algebra whose localization is `B`.

Source/core/bridge triage:
- `source-facing`: the theorem below, expressing Stacks Lemma `15.108.3` as a localization
  existence result;
- `core/canonical`: the owner predicate `Algebra.Etale A C` on an intermediate algebra `C` and
  the localization owner `IsLocalization M B`;
- `bridge/view`: the essential finite type presentation of `B` and the étale-localization
  neighborhood produced by Lemma `15.108.2`.
-/
variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsLocalRing A] [IsGeometricallyUnibranch A]
variable [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [Algebra.EssFiniteType A B]

/-- Helper for Lemma 15.108.3: a local ring is already the localization at the complement of its
maximal ideal. -/
lemma self_isLocalization_primeCompl_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R] :
    IsLocalization (maximalIdeal R).primeCompl R := by
  -- Every element outside the maximal ideal is a unit, so the identity map is the universal
  -- localization at the prime complement.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

/-- Helper for Lemma 15.108.3: any ring is the localization of itself at the trivial submonoid. -/
lemma self_isLocalization_bot
    (R : Type*) [CommRing R] :
    IsLocalization (⊥ : Submonoid R) R := by
  -- Localizing at the trivial submonoid does not invert any new elements.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rcases y with ⟨y, hy⟩
    simp only [Submonoid.mem_bot] at hy
    subst hy
    exact isUnit_one
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

/-- Helper for Lemma 15.108.3: localizing a local ring at the complement of its maximal ideal
does not change the ring. -/
noncomputable abbrev localizationAtMaximalIdeal_algEquiv_self
    (R : Type*) [CommRing R] [IsLocalRing R] :
    Localization.AtPrime (maximalIdeal R) ≃ₐ[R] R :=
  let _ : IsLocalization (maximalIdeal R).primeCompl R :=
    self_isLocalization_primeCompl_maximalIdeal R
  Localization.algEquiv (maximalIdeal R).primeCompl R

/-- Helper for Lemma 15.108.3: the localization of a geometrically unibranch local ring at its
maximal ideal is geometrically unibranch. -/
lemma localizationAtMaximalIdeal_isGeometricallyUnibranch :
    IsGeometricallyUnibranch (Localization.AtPrime (maximalIdeal A)) := by
  let A0 := Localization.AtPrime (maximalIdeal A)
  let _ : IsLocalHom (algebraMap A A0) := by infer_instance
  obtain ⟨Ash, _, _, hAsh⟩ := exists_strictHenselization A
  letI : CommRing Ash := inferInstance
  letI : Algebra A Ash := inferInstance
  letI : IsStrictHenselizationOf A Ash := hAsh
  obtain ⟨A0sh, _, _, hA0sh⟩ := exists_strictHenselization A0
  letI : CommRing A0sh := inferInstance
  letI : Algebra A0 A0sh := inferInstance
  letI : IsStrictHenselizationOf A0 A0sh := hA0sh
  have hsmooth : Algebra.SmoothAtPrime A A0 (closedPoint A0) := by
    rw [Algebra.smoothAtPrime_iff_isSmoothAt]
    infer_instance
  have hbranch :
      geometricBranchNumber A Ash = geometricBranchNumber A0 A0sh :=
    geometricBranchNumber_eq_of_smoothAtPrime_closedPoint
      (A := A) (B := A0) (Ash := Ash) (Bsh := A0sh) hsmooth
  have hA : geometricBranchNumber A Ash = 1 := by
    exact (geometricBranchNumber_eq_one_iff_isGeometricallyUnibranch
      (A := A) (Ash := Ash)).2 inferInstance
  exact
    (geometricBranchNumber_eq_one_iff_isGeometricallyUnibranch
      (A := A0) (Ash := A0sh)).1 <| by
        rw [← hbranch]
        exact hA

/-- Helper for Lemma 15.108.3: the closed point is unramified once the maximal ideal maps to the
closed-point maximal ideal and the residue-field extension is separable. -/
lemma closedPoint_unramifiedAt_of_map_eq_maximalIdeal
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B)) :
    Algebra.UnramifiedAt A B (closedPoint B) := by
  let q : Ideal B := (closedPoint B).asIdeal
  letI : q.IsPrime := (closedPoint B).2
  have hq : q = maximalIdeal B := rfl
  have hp :
      Ideal.comap (algebraMap A B) q = maximalIdeal A := by
    simpa [hq] using
      (((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 0 4).mp inferInstance).symm
  letI : q.LiesOver (maximalIdeal A) := hp.symm
  exact (Algebra.isUnramifiedAt_iff_map_eq A (maximalIdeal A) q).2
    ⟨by simpa [hq] using hsep, by simpa [hq] using hmax⟩

/-- Helper for Lemma 15.108.3: after localizing at the closed point, the canonical local map is
still injective. -/
lemma localized_closedPoint_map_injective_of_injective_localHom
    (hinj : Function.Injective (algebraMap A B)) :
    Function.Injective
      (Localization.localRingHom
        ((closedPoint B).asIdeal.under A) (closedPoint B).asIdeal (algebraMap A B) rfl) := by
  let p : Ideal A := (closedPoint B).asIdeal.under A
  let q : Ideal B := (closedPoint B).asIdeal
  have hp : p = maximalIdeal A := by
    simpa [q] using
      (((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 0 4).mp inferInstance).symm
  let eA :
      Localization.AtPrime p ≃ₐ[A] A :=
    Eq.ndrec
      (motive := fun I : Ideal A => Localization.AtPrime I ≃ₐ[A] A)
      (localizationAtMaximalIdeal_algEquiv_self A)
      hp.symm
  let eB : Localization.AtPrime q ≃ₐ[B] B :=
    localizationAtClosedPoint_algEquiv_self B
  let j : Localization.AtPrime p →+* Localization.AtPrime q :=
    (eB.symm.toRingHom.comp (algebraMap A B)).comp eA.toRingHom
  have hj :
      Localization.localRingHom p q (algebraMap A B) rfl = j := by
    refine Localization.localRingHom_unique p q (algebraMap A B) rfl ?_
    intro x
    dsimp [j]
    simp [eA, eB, Localization.localRingHom_to_map]
  rw [hj]
  exact eB.symm.injective.comp (hinj.comp eA.injective)

/-- Helper for Lemma 15.108.3: a ring equivalence identifies the target with the localization of
the source at the trivial submonoid. -/
lemma isLocalization_bot_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    let _ : Algebra R S := e.toRingHom.toAlgebra
    IsLocalization (⊥ : Submonoid R) S := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  let eAlg : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) (fun _ ↦ rfl)
  exact IsLocalization.isLocalization_of_algEquiv (⊥ : Submonoid R) eAlg <|
    self_isLocalization_bot R

-- Proof sketch: write `B` as a localization of a finite type `A`-algebra `C` at a prime over the
-- maximal ideal of `A`. Lemma `10.151.7` gives that `A → C` is unramified at that prime from the
-- maximal-ideal and separable-residue-field hypotheses, and Lemma `15.108.2` then produces an
-- étale `A`-algebra after shrinking around that prime. The geometric-unibranch hypotheses and
-- Lemmas `15.107.7`, `15.107.8`, and `15.108.1` show that the resulting local map into `B` is
-- injective, yielding an intermediate étale `A`-algebra whose localization identifies with `B`.
/-- Lemma 15.108.3: if `(A, 𝔪)` is a geometrically unibranch local domain and `A → B` is an
injective local homomorphism of local rings that is essentially of finite type, such that
`𝔪 B = maximalIdeal B` and the induced residue-field extension is separable, then `B` is the
localization of an étale `A`-algebra. -/
theorem exists_etale_localization_of_isGeometricallyUnibranch_of_injective_localHom
    (hinj : Function.Injective (algebraMap A B))
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (M : Submonoid C), Algebra.Etale A C ∧ IsLocalization M B := by
  let q : PrimeSpectrum B := closedPoint B
  have hgeo :
      IsGeometricallyUnibranch (Localization.AtPrime (q.asIdeal.under A)) := by
    have hp : q.asIdeal.under A = maximalIdeal A := by
      simpa [q] using
        (((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 0 4).mp inferInstance).symm
    simpa [hp, q] using
      (localizationAtMaximalIdeal_isGeometricallyUnibranch (A := A))
  letI : IsGeometricallyUnibranch (Localization.AtPrime (q.asIdeal.under A)) := hgeo
  have hunram : Algebra.UnramifiedAt A B q :=
    closedPoint_unramifiedAt_of_map_eq_maximalIdeal (A := A) (B := B) hmax hsep
  have hlocinj :
      Function.Injective
        (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl) :=
    localized_closedPoint_map_injective_of_injective_localHom (A := A) (B := B) hinj
  obtain ⟨g, hg, hEtale⟩ :=
    exists_etale_localizationAway_of_geometricallyUnibranch_of_unramifiedAtPrime_of_injective_localRingHom
      (A := A) (B := B) q hunram hlocinj
  have hg_unit : IsUnit g := IsLocalRing.notMem_maximalIdeal.mp <| by
    simpa [q] using hg
  let e : Localization.Away g ≃ₐ[A] B :=
    (IsLocalization.atUnit B (Localization.Away g) g hg_unit).symm
  refine ⟨Localization.Away g, inferInstance, inferInstance, e.toRingHom.toAlgebra, ?_, ⊥, hEtale, ?_⟩
  · let _ : Algebra A (Localization.Away g) := inferInstance
    exact IsScalarTower.of_algebraMap_eq fun x ↦ by
      change e (algebraMap (Localization.Away g) (Localization.Away g) x) =
        algebraMap A B x
      simpa using e.commutes x
  · simpa using isLocalization_bot_of_ringEquiv e.toRingEquiv

end
