import Mathlib
import StacksProject_2024.Chap10.Lemma_10_143_3
import StacksProject_2024.Chap15.Definition_15_50_1
import StacksProject_2024.Chap15.Lemma_15_43_9
import StacksProject_2024.Chap15.Lemma_15_50_14
import StacksProject_2024.Chap15.Proposition_15_50_12
import StacksProject_2024.Chap16.Theorem_16_13_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open Algebra
open MvPolynomial

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (p : PrimeSpectrum R)

local notation "Rₚ" => Localization.AtPrime p.asIdeal

/- Domain-style sampling:
- primary domain: Artin approximation over a localized Noetherian ring, descended back to an
  étale neighborhood over the original ring;
- sampled owner declarations in this domain:
  `IsGRing`,
  `CompletedLocalizationAtPrime`,
  `CompletedLocalizationAtPrime.map`,
  `RingHom.adicCompletionMap`,
  `Localization.localRingHom`,
  `IsRegularRingMap`,
  `(inferInstance : (algebraMap Rₚ (R̂_[p])).IsRegularRingMap)`,
  `Algebra.Etale`,
  `Ideal.ResidueField.map`;
- best owner abstraction: the main source-facing theorem should keep `IsGRing Rₚ` as the owner
  hypothesis for the localized ring `Rₚ`, while the regularity of the completion map
  `Rₚ → R̂_[p]` is a derived bridge supplied by the Chapter 15 owner instance on
  `(algebraMap Rₚ (R̂_[p])).IsRegularRingMap`; the completed local rings themselves
  should use the chapter owner `CompletedLocalizationAtPrime` and its notation `R̂_[p]`, while the
  primewise comparison map between completed localizations should use the owner-level bridge
  `CompletedLocalizationAtPrime.map`, and the residue-field comparison should use the canonical
  owner `Ideal.ResidueField.map` derived directly from the intrinsic condition
  `PrimeSpectrum.comap (algebraMap R R') p' = p`;
- primitive data: the étale `R`-algebra `R'`, the prime `p'` over `p`, and the solution `b`;
- derived API: the canonical map `R̂_[p] → R̂_[p']`, residue-field bijectivity, exact solvability
  of the polynomial system, and the congruence modulo the `N`-th power of the maximal ideal
  upstairs.

Source/core/bridge triage:
- `source-facing`: the existence theorem below;
- `core/canonical`: `IsGRing`, `CompletedLocalizationAtPrime`,
  `CompletedLocalizationAtPrime.map`, `RingHom.adicCompletionMap`, `Localization.localRingHom`,
  `IsRegularRingMap`, `Algebra.Etale`, and
  `Ideal.ResidueField.map`;
- `bridge/view`: the Chapter 15 owner instance
  `(inferInstance : (algebraMap Rₚ (R̂_[p])).IsRegularRingMap)` for the regular completion map;
  the theorem itself is the bridge from the localized version of the approximation theorem back to
  étale neighborhoods over `R`. -/

-- Proof sketch for the regular-completion bridge: apply Theorem `16.13.2` to the local ring
-- `R_𝔭` and the given formal solution in its completion. This yields an étale `R_𝔭`-algebra with
-- a solution approximating `a`. Then use localization descent for étale algebras to write that
-- local étale algebra as the localization of an étale `R`-algebra `R'` at a prime `𝔭'` over
-- `𝔭`, and transport the approximate solution through the identified completed local rings.
/-- Helper for Lemma 16.13.4: an étale `R_𝔭`-algebra is étale over `R` by composing with the
localization map `R → R_𝔭`. -/
private theorem etale_over_base_of_etale_over_localization
    {S : Type u} [CommRing S] [Algebra Rₚ S] [Algebra.Etale Rₚ S] :
    Algebra.Etale R S := by
  -- Proof comment: the localization map `R → R_𝔭` is étale, and étale maps compose.
  let _ : Algebra R S := (algebraMap R Rₚ).toAlgebra.comp (algebraMap Rₚ S)
  let _ : IsScalarTower R Rₚ S := IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.Etale.comp (R := R) (A := Rₚ) (B := S)

/-- Helper for Lemma 16.13.4: any ideal of an `R_𝔭`-algebra lying over the maximal ideal of
`R_𝔭` contracts to the original prime `p` along the composite map `R → R_𝔭 → S`. -/
private theorem comap_localMaximalIdeal_along_composite_eq
    {S : Type u} [CommRing S] [Algebra Rₚ S]
    (m : Ideal S) (hmOver : m.LiesOver (maximalIdeal Rₚ)) :
    Ideal.comap ((algebraMap Rₚ S).comp (algebraMap R Rₚ)) m = p.asIdeal := by
  -- Proof comment: contract first along `R_𝔭 → S`, then along `R → R_𝔭`.
  rw [Ideal.comap_comp]
  rw [hmOver.over_def _]
  simpa using (Localization.AtPrime.comap_maximalIdeal (R := R) (I := p.asIdeal))

/-- Helper for Lemma 16.13.4: the maximal-ideal residue-field equivalence of a local ring sends
the class of `a` to its usual residue class. -/
private theorem maximalIdeal_residueField_ringEquiv_apply_algebraMap
    (a : Rₚ) :
    maximalIdeal_residueField_ringEquiv Rₚ
        (algebraMap Rₚ (maximalIdeal Rₚ).ResidueField a) =
      algebraMap Rₚ (ResidueField Rₚ) a := by
  -- Proof comment: rewrite the target class through the inverse residue-field equivalence.
  rw [show algebraMap Rₚ (maximalIdeal Rₚ).ResidueField a =
      algebraMap (ResidueField Rₚ) (maximalIdeal Rₚ).ResidueField
        (algebraMap Rₚ (ResidueField Rₚ) a) by rfl]
  exact (maximalIdeal_residueField_ringEquiv Rₚ).apply_symm_apply _

/-- Helper for Lemma 16.13.4: the inverse of the prime-localization residue-field equivalence
acts on a class from `R` by first localizing to `R_𝔭`. -/
private theorem prime_localization_residueField_ringEquiv_symm_apply_algebraMap
    (x : R) :
    (prime_localization_residueField_ringEquiv (R := R) p).symm
        (algebraMap R p.asIdeal.ResidueField x) =
      algebraMap Rₚ (ResidueField Rₚ) (algebraMap R Rₚ x) := by
  -- Proof comment: after changing the codomain to the local-ring residue field, the statement is
  -- exactly the compatibility of the maximal-ideal residue-field equivalence with base elements.
  change
    (maximalIdeal_residueField_ringEquiv Rₚ).symm
      (algebraMap R p.asIdeal.ResidueField x) =
    algebraMap Rₚ (ResidueField Rₚ) (algebraMap R Rₚ x)
  apply (maximalIdeal_residueField_ringEquiv Rₚ).injective
  simp [maximalIdeal_residueField_ringEquiv_apply_algebraMap]

/-- Helper for Lemma 16.13.4: the prime-localization residue-field equivalence sends the residue
class of a base element to its ideal-residue-field class. -/
private theorem prime_localization_residueField_ringEquiv_apply_algebraMap
    {A : Type u} [CommRing A] (q : PrimeSpectrum A) (x : A) :
    prime_localization_residueField_ringEquiv (R := A) q
      (algebraMap (Localization.AtPrime q.asIdeal)
        (ResidueField (Localization.AtPrime q.asIdeal))
        (algebraMap A (Localization.AtPrime q.asIdeal) x)) =
      algebraMap A q.asIdeal.ResidueField x := by
  -- Proof comment: apply the inverse-direction compatibility and cancel the residue-field
  -- equivalence of the localization at `q`.
  exact
    (congrArg
      (prime_localization_residueField_ringEquiv (R := A) q)
      (by
        change
          (prime_localization_residueField_ringEquiv (R := A) q).symm
              (algebraMap A q.asIdeal.ResidueField x) =
            algebraMap (Localization.AtPrime q.asIdeal)
              (ResidueField (Localization.AtPrime q.asIdeal))
              (algebraMap A (Localization.AtPrime q.asIdeal) x)
        change
          (maximalIdeal_residueField_ringEquiv (Localization.AtPrime q.asIdeal)).symm
              (algebraMap A q.asIdeal.ResidueField x) =
            algebraMap (Localization.AtPrime q.asIdeal)
              (ResidueField (Localization.AtPrime q.asIdeal))
              (algebraMap A (Localization.AtPrime q.asIdeal) x)
        apply (maximalIdeal_residueField_ringEquiv (Localization.AtPrime q.asIdeal)).injective
        simp [maximalIdeal_residueField_ringEquiv_apply_algebraMap])).symm

/-- Helper for Lemma 16.13.4: localizing at `p` does not change the residue field `κ(p)`, written
in the ideal-residue-field model used by the local theorem. -/
private theorem localization_residueFieldMap_bijective :
    Function.Bijective
      (Ideal.ResidueField.map p.asIdeal (maximalIdeal Rₚ) (algebraMap R Rₚ)
        (by
          simpa using
            (Localization.AtPrime.comap_maximalIdeal (R := R) (I := p.asIdeal)).symm)) := by
  let k : p.asIdeal.ResidueField →+* (maximalIdeal Rₚ).ResidueField :=
    Ideal.ResidueField.map p.asIdeal (maximalIdeal Rₚ) (algebraMap R Rₚ)
      (by
        simpa using
          (Localization.AtPrime.comap_maximalIdeal (R := R) (I := p.asIdeal)).symm)
  have hk :
      (maximalIdeal_residueField_ringEquiv Rₚ).toRingHom.comp k =
        (prime_localization_residueField_ringEquiv (R := R) p).symm.toRingHom := by
    -- Proof comment: both maps out of `κ(p)` agree on residue classes of elements of `R`.
    apply Ideal.ResidueField.ringHom_ext
    ext x
    change
      maximalIdeal_residueField_ringEquiv Rₚ
          (k (algebraMap R p.asIdeal.ResidueField x)) =
        (prime_localization_residueField_ringEquiv (R := R) p).symm
          (algebraMap R p.asIdeal.ResidueField x)
    rw [Ideal.ResidueField.map_algebraMap,
      maximalIdeal_residueField_ringEquiv_apply_algebraMap,
      prime_localization_residueField_ringEquiv_symm_apply_algebraMap]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    -- Proof comment: compare images after transporting to `ResidueField R_𝔭`.
    apply (prime_localization_residueField_ringEquiv (R := R) p).symm.injective
    simpa [Function.comp, hk] using
      congrArg (maximalIdeal_residueField_ringEquiv Rₚ) hxy
  · intro y
    -- Proof comment: lift through the residue-field equivalence of the localization.
    obtain ⟨x, hx⟩ :=
      (prime_localization_residueField_ringEquiv (R := R) p).symm.surjective
        (maximalIdeal_residueField_ringEquiv Rₚ y)
    refine ⟨x, ?_⟩
    apply (maximalIdeal_residueField_ringEquiv Rₚ).injective
    simpa [Function.comp, hk] using hx

/-- Helper for Lemma 16.13.4: the residue-field bijection returned by the localized approximation
theorem is the same bijection required by the primewise statement over `R`. -/
private theorem residueFieldMapBijective_of_localResidueFieldMapAtPrime
    {S : Type u} [CommRing S] [Algebra Rₚ S] [Algebra R S] [IsScalarTower R Rₚ S]
    (m : Ideal S) [hmMax : m.IsMaximal] (hmOver : m.LiesOver (maximalIdeal Rₚ))
    (hresLocal :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal Rₚ) m (Algebra.ofId _ _) (m.over_def _))) :
    Function.Bijective
      (Ideal.ResidueField.map p.asIdeal m (algebraMap R S)
        (by
          simpa [show algebraMap R S = (algebraMap Rₚ S).comp (algebraMap R Rₚ) by rfl] using
            comap_localMaximalIdeal_along_composite_eq (R := R) (p := p) m hmOver)) := by
  let k : p.asIdeal.ResidueField →+* (maximalIdeal Rₚ).ResidueField :=
    Ideal.ResidueField.map p.asIdeal (maximalIdeal Rₚ) (algebraMap R Rₚ)
      (by
        simpa using
          (Localization.AtPrime.comap_maximalIdeal (R := R) (I := p.asIdeal)).symm)
  have hkbij : Function.Bijective k := localization_residueFieldMap_bijective (R := R) (p := p)
  have hcomp :
      (Ideal.ResidueField.mapₐ (maximalIdeal Rₚ) m (Algebra.ofId _ _) (m.over_def _)).toRingHom.comp
          k =
        Ideal.ResidueField.map p.asIdeal m (algebraMap R S)
          (by
            simpa [show algebraMap R S = (algebraMap Rₚ S).comp (algebraMap R Rₚ) by rfl] using
              comap_localMaximalIdeal_along_composite_eq (R := R) (p := p) m hmOver) := by
    -- Proof comment: both maps from `κ(p)` to `κ(m)` are induced by the same composite map
    -- `R → R_𝔭 → S`, so they agree on base residue classes.
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp [k, IsScalarTower.algebraMap_eq R Rₚ S]
  -- Proof comment: compose the local-theorem bijection with the canonical residue-field
  -- identification `κ(p) ≃ κ(R_𝔭)`.
  simpa [Function.comp, hcomp] using hresLocal.comp hkbij

/-- Helper for Lemma 16.13.4: the maximal-ideal residue-field equivalence commutes with local
ring maps. -/
private theorem maximalIdeal_residueField_ringEquiv_comp_residueFieldMap
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (maximalIdeal_residueField_ringEquiv B).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdeal_residueField_ringEquiv A).toRingHom := by
  -- Proof comment: both composites send the class of `a : A` to the residue class of `f a`.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdeal_residueField_ringEquiv B
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm
          (algebraMap A (maximalIdeal A).ResidueField a)) =
      ResidueField.map f
        (maximalIdeal_residueField_ringEquiv A
          (algebraMap A (maximalIdeal A).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap]
  rw [show maximalIdeal_residueField_ringEquiv A
      (algebraMap A (maximalIdeal A).ResidueField a) = residue A a by
        change
          maximalIdeal_residueField_ringEquiv A
              ((maximalIdeal_residueField_ringEquiv A).symm (residue A a)) =
            residue A a
        exact (maximalIdeal_residueField_ringEquiv A).apply_symm_apply (residue A a)]
  rw [show algebraMap B (maximalIdeal B).ResidueField (f a) =
      algebraMap (ResidueField B) (maximalIdeal B).ResidueField (residue B (f a)) by rfl]
  rw [show maximalIdeal_residueField_ringEquiv B
      (algebraMap (ResidueField B) (maximalIdeal B).ResidueField (residue B (f a))) =
      residue B (f a) by
        change
          maximalIdeal_residueField_ringEquiv B
              ((maximalIdeal_residueField_ringEquiv B).symm (residue B (f a))) =
            residue B (f a)
        exact (maximalIdeal_residueField_ringEquiv B).apply_symm_apply (residue B (f a))]
  exact IsLocalRing.ResidueField.map_residue f a

/-- Helper for Lemma 16.13.4: the local-theorem residue-field bijection on `m` is exactly the
residue-field bijection for the localized local map `R_𝔭 → S_m`. -/
private theorem localizedResidueFieldMap_bijective_of_localApproximationData
    {S : Type u} [CommRing S] [Algebra Rₚ S]
    (m : Ideal S) [hmMax : m.IsMaximal] (hmOver : m.LiesOver (maximalIdeal Rₚ))
    (hresLocal :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal Rₚ) m (Algebra.ofId _ _) (m.over_def _))) :
    Function.Bijective
      (ResidueField.map
        (Localization.localRingHom (maximalIdeal Rₚ) m (algebraMap Rₚ S) hmOver)) := by
  let pM : PrimeSpectrum S := ⟨m, hmMax.1⟩
  let localMap :
      Rₚ →+* Localization.AtPrime m :=
    Localization.localRingHom (maximalIdeal Rₚ) m (algebraMap Rₚ S) hmOver
  let localIdealMap :
      (maximalIdeal Rₚ).ResidueField →+* (maximalIdeal (Localization.AtPrime m)).ResidueField :=
    Ideal.ResidueField.map (maximalIdeal Rₚ) (maximalIdeal (Localization.AtPrime m))
      localMap
      (by
        simpa [Ideal.under_def] using
          (IsLocalRing.maximalIdeal_comap localMap).symm)
  have hlocalIdealComp :
      (prime_localization_residueField_ringEquiv (R := S) pM).toRingHom.comp localIdealMap =
        (Ideal.ResidueField.mapₐ (maximalIdeal Rₚ) m (Algebra.ofId _ _) (m.over_def _)).toRingHom := by
    -- Proof comment: localizing `S` at `m` does not change the target residue field, and the
    -- localized branch map still comes from the same composite `R_𝔭 → S → S_m`.
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap]
    rw [show localMap x = algebraMap S (Localization.AtPrime m) ((algebraMap Rₚ S) x) by
      simp [localMap, Localization.localRingHom_to_map]]
    simpa [pM]
      using
        prime_localization_residueField_ringEquiv_apply_algebraMap
          (A := S) pM ((algebraMap Rₚ S) x)
  have hlocalIdealBijective : Function.Bijective localIdealMap := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hresLocal.1
      simpa [Function.comp, hlocalIdealComp] using
        congrArg (prime_localization_residueField_ringEquiv (R := S) pM) hxy
    · intro y
      obtain ⟨x, hx⟩ :=
        hresLocal.2 ((prime_localization_residueField_ringEquiv (R := S) pM) y)
      refine ⟨x, ?_⟩
      apply (prime_localization_residueField_ringEquiv (R := S) pM).injective
      simpa [Function.comp, hlocalIdealComp] using hx
  have hresidueFieldComp :
      (maximalIdeal_residueField_ringEquiv (Localization.AtPrime m)).toRingHom.comp localIdealMap =
        (ResidueField.map localMap).comp
          (maximalIdeal_residueField_ringEquiv Rₚ).toRingHom :=
    maximalIdeal_residueField_ringEquiv_comp_residueFieldMap (f := localMap)
  have hresidueFieldCompBijective :
      Function.Bijective
        ((ResidueField.map localMap).comp
          (maximalIdeal_residueField_ringEquiv Rₚ).toRingHom) := by
    -- Proof comment: transport the ideal-residue-field bijection to the local-ring residue-field
    -- model on both source and target.
    simpa [Function.comp, hresidueFieldComp] using
      (maximalIdeal_residueField_ringEquiv (Localization.AtPrime m)).bijective.comp
        hlocalIdealBijective
  refine ⟨?_, ?_⟩
  · intro x y hxy
    -- Proof comment: compare `x` and `y` after moving them back to the ideal-residue-field model
    -- of `R_𝔭`.
    apply (maximalIdeal_residueField_ringEquiv Rₚ).symm.injective
    apply hresidueFieldCompBijective.1
    simpa [Function.comp] using hxy
  · intro y
    -- Proof comment: lift `y` through the transported composite bijection and then return to the
    -- ordinary residue field of `R_𝔭`.
    obtain ⟨x, hx⟩ := hresidueFieldCompBijective.2 y
    refine ⟨maximalIdeal_residueField_ringEquiv Rₚ x, ?_⟩
    simpa [Function.comp] using hx

/-- Helper for Lemma 16.13.4: the completed-local residue field is canonically identified with
the residue field of `R_𝔭`. -/
private theorem completionIdealResidueFieldMap_bijective :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal Rₚ) (maximalIdeal (R̂_[p]))
        (algebraMap Rₚ (R̂_[p]))
        (by
          simpa [Ideal.under_def] using
            (IsLocalRing.maximalIdeal_comap (algebraMap Rₚ (R̂_[p]))).symm)) := by
  let f :
      (maximalIdeal Rₚ).ResidueField →+* (maximalIdeal (R̂_[p])).ResidueField :=
    Ideal.ResidueField.map (maximalIdeal Rₚ) (maximalIdeal (R̂_[p]))
      (algebraMap Rₚ (R̂_[p]))
      (by
        simpa [Ideal.under_def] using
          (IsLocalRing.maximalIdeal_comap (algebraMap Rₚ (R̂_[p]))).symm)
  have hcomp :
      (maximalIdeal_residueField_ringEquiv (R̂_[p])).toRingHom.comp f =
        (ResidueField.map (algebraMap Rₚ (R̂_[p]))).comp
          (maximalIdeal_residueField_ringEquiv Rₚ).toRingHom :=
    maximalIdeal_residueField_ringEquiv_comp_residueFieldMap
      (f := algebraMap Rₚ (R̂_[p]))
  have hbijComp :
      Function.Bijective
        ((maximalIdeal_residueField_ringEquiv (R̂_[p])).toRingHom.comp f) := by
    exact
      (maximalIdealCompletion_residueField_bijective Rₚ).comp
        (maximalIdeal_residueField_ringEquiv Rₚ).bijective
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply (maximalIdeal_residueField_ringEquiv (R̂_[p])).injective
    simpa [Function.comp, hcomp] using congrArg ((maximalIdeal_residueField_ringEquiv (R̂_[p])).toRingHom) hxy
  · intro y
    obtain ⟨x, hx⟩ :=
      hbijComp.surjective ((maximalIdeal_residueField_ringEquiv (R̂_[p])) y)
    refine ⟨x, ?_⟩
    apply (maximalIdeal_residueField_ringEquiv (R̂_[p])).injective
    simpa [Function.comp, hcomp] using hx

/-- Helper for Lemma 16.13.4: an approximation map to the completed localization selects a prime
of `S` lying over the maximal ideal of `R_𝔭`. -/
private theorem approximationMapComapUnderAtPrime
    {S : Type u} [CommRing S] [Algebra Rₚ S] (φ : S →ₐ[Rₚ] R̂_[p]) :
    (Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))).under Rₚ = maximalIdeal Rₚ := by
  -- Proof comment: contract `maximalIdeal (R̂_[p])` along `φ`, then rewrite the composite with
  -- the `R_𝔭`-algebra structure on `φ`.
  change
    Ideal.comap ((φ : S →+* R̂_[p]).comp (algebraMap Rₚ S)) (maximalIdeal (R̂_[p])) =
      maximalIdeal Rₚ
  rw [show ((φ : S →+* R̂_[p]).comp (algebraMap Rₚ S)) = algebraMap Rₚ (R̂_[p]) by
    ext x
    simp [RingHom.comp_apply, φ.commutes x]]
  simpa [Ideal.under_def] using
    (IsLocalRing.maximalIdeal_comap (algebraMap Rₚ (R̂_[p])))

/-- Helper for Lemma 16.13.4: the approximation-map residue-field comparison agrees with the
completion residue-field map on the branch selected by that approximation map. -/
private theorem approximationMapResidueFieldMap_compAtPrime
    {S : Type u} [CommRing S] [Algebra Rₚ S] (φ : S →ₐ[Rₚ] R̂_[p]) :
    let q : Ideal S := Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))
    (Ideal.ResidueField.map q (maximalIdeal (R̂_[p])) φ.toRingHom rfl).comp
        (Ideal.ResidueField.map (q.under Rₚ) q (algebraMap Rₚ S) rfl) =
      Ideal.ResidueField.map (q.under Rₚ) (maximalIdeal (R̂_[p]))
        (algebraMap Rₚ (R̂_[p]))
        (by
          change
            Ideal.comap (((φ : S →+* R̂_[p]).comp (algebraMap Rₚ S)))
                (maximalIdeal (R̂_[p])) =
              Ideal.comap (algebraMap Rₚ (R̂_[p])) (maximalIdeal (R̂_[p]))
          rw [show ((φ : S →+* R̂_[p]).comp (algebraMap Rₚ S)) = algebraMap Rₚ (R̂_[p]) by
            ext x
            simp [RingHom.comp_apply, φ.commutes x]]) := by
  -- Proof comment: both composites are induced by the same base map `R_𝔭 → R̂_[p]`.
  apply Ideal.ResidueField.ringHom_ext
  ext x
  simp only [RingHom.comp_apply]
  rw [Ideal.ResidueField.map_algebraMap]
  have hright :
      (Ideal.ResidueField.map
          ((Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))).under Rₚ)
          (maximalIdeal (R̂_[p])) (algebraMap Rₚ (R̂_[p]))
          (by
            change
              Ideal.comap (((φ : S →+* R̂_[p]).comp (algebraMap Rₚ S)))
                  (maximalIdeal (R̂_[p])) =
                Ideal.comap (algebraMap Rₚ (R̂_[p])) (maximalIdeal (R̂_[p]))
            rw [show ((φ : S →+* R̂_[p]).comp (algebraMap Rₚ S)) = algebraMap Rₚ (R̂_[p]) by
              ext y
              simp [RingHom.comp_apply, φ.commutes y]])
          (algebraMap Rₚ ((Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))).under Rₚ).ResidueField
            x) =
      algebraMap (R̂_[p]) (maximalIdeal (R̂_[p])).ResidueField
        ((algebraMap Rₚ (R̂_[p])) x) := by
    simpa using
      (Ideal.ResidueField.map_algebraMap
        ((Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))).under Rₚ)
        (maximalIdeal (R̂_[p])) (algebraMap Rₚ (R̂_[p]))
        (by
          change
            Ideal.comap (((φ : S →+* R̂_[p]).comp (algebraMap Rₚ S)))
                (maximalIdeal (R̂_[p])) =
              Ideal.comap (algebraMap Rₚ (R̂_[p])) (maximalIdeal (R̂_[p]))
          rw [show ((φ : S →+* R̂_[p]).comp (algebraMap Rₚ S)) = algebraMap Rₚ (R̂_[p]) by
            ext y
            simp [RingHom.comp_apply, φ.commutes y]]) x)
  rw [hright]
  simpa using
    congrArg (algebraMap (R̂_[p]) (maximalIdeal (R̂_[p])).ResidueField) (φ.commutes x)

/-- Helper for Lemma 16.13.4: the prime cut out by an approximation map already has the correct
residue field over `R_𝔭`. -/
private theorem approximationPrimeResidueFieldMap_bijective
    {S : Type u} [CommRing S] [Algebra Rₚ S] (φ : S →ₐ[Rₚ] R̂_[p]) :
    let q : Ideal S := Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal Rₚ) q (algebraMap Rₚ S)
        (by
          simpa [q, Ideal.under_def] using
            approximationMapComapUnderAtPrime (p := p) φ)) := by
  let q : Ideal S := Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))
  let f : (maximalIdeal Rₚ).ResidueField →+* q.ResidueField :=
    Ideal.ResidueField.map (maximalIdeal Rₚ) q (algebraMap Rₚ S)
      (by
        simpa [q, Ideal.under_def] using
          approximationMapComapUnderAtPrime (p := p) φ)
  let g : q.ResidueField →+* (maximalIdeal (R̂_[p])).ResidueField :=
    Ideal.ResidueField.map q (maximalIdeal (R̂_[p])) φ.toRingHom rfl
  have hcomp :
      g.comp f =
        Ideal.ResidueField.map (maximalIdeal Rₚ) (maximalIdeal (R̂_[p]))
          (algebraMap Rₚ (R̂_[p]))
          (by
            simpa [Ideal.under_def] using
              (IsLocalRing.maximalIdeal_comap (algebraMap Rₚ (R̂_[p]))).symm) := by
    simpa [q, f, g, Ideal.under_def] using
      approximationMapResidueFieldMap_compAtPrime (p := p) φ
  have hcompletion :
      Function.Bijective
        (Ideal.ResidueField.map (maximalIdeal Rₚ) (maximalIdeal (R̂_[p]))
          (algebraMap Rₚ (R̂_[p]))
          (by
            simpa [Ideal.under_def] using
              (IsLocalRing.maximalIdeal_comap (algebraMap Rₚ (R̂_[p]))).symm)) :=
    completionIdealResidueFieldMap_bijective (R := R) (p := p)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply RingHom.injective g
    simpa [Function.comp, hcomp] using congrArg g hxy
  · intro y
    obtain ⟨x, hx⟩ := hcompletion.surjective (g y)
    refine ⟨x, ?_⟩
    apply RingHom.injective g
    simpa [Function.comp, hcomp] using hx

/-- Helper for Lemma 16.13.4: once a prime of an `R_𝔭`-algebra has the correct residue field over
`R_𝔭`, the corresponding prime over `R` has residue field `κ(p)`. -/
private theorem residueFieldMapBijective_of_localPrimeResidueFieldMapAtPrime
    {S : Type u} [CommRing S] [Algebra Rₚ S] [Algebra R S] [IsScalarTower R Rₚ S]
    (q : Ideal S) (hqOver : q.LiesOver (maximalIdeal Rₚ))
    (hresLocal :
      Function.Bijective
        (Ideal.ResidueField.map (maximalIdeal Rₚ) q (algebraMap Rₚ S)
          (q.over_def _))) :
    Function.Bijective
      (Ideal.ResidueField.map p.asIdeal q (algebraMap R S)
        (by
          simpa [show algebraMap R S = (algebraMap Rₚ S).comp (algebraMap R Rₚ) by rfl] using
            comap_localMaximalIdeal_along_composite_eq (R := R) (p := p) q hqOver)) := by
  let k : p.asIdeal.ResidueField →+* (maximalIdeal Rₚ).ResidueField :=
    Ideal.ResidueField.map p.asIdeal (maximalIdeal Rₚ) (algebraMap R Rₚ)
      (by
        simpa using
          (Localization.AtPrime.comap_maximalIdeal (R := R) (I := p.asIdeal)).symm)
  have hkbij : Function.Bijective k := localization_residueFieldMap_bijective (R := R) (p := p)
  have hcomp :
      (Ideal.ResidueField.map (maximalIdeal Rₚ) q (algebraMap Rₚ S)
          (q.over_def _)).comp k =
        Ideal.ResidueField.map p.asIdeal q (algebraMap R S)
          (by
            simpa [show algebraMap R S = (algebraMap Rₚ S).comp (algebraMap R Rₚ) by rfl] using
              comap_localMaximalIdeal_along_composite_eq (R := R) (p := p) q hqOver) := by
    -- Proof comment: both maps from `κ(p)` to `κ(q)` are induced by the same composite map
    -- `R → R_𝔭 → S`.
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp [k, IsScalarTower.algebraMap_eq R Rₚ S]
  -- Proof comment: compose the local residue-field bijection with the canonical identification
  -- `κ(p) ≃ κ(R_𝔭)`.
  simpa [Function.comp, hcomp] using hresLocal.comp hkbij

/-- Helper for Lemma 16.13.4: the prime cut out by an approximation map lies over the maximal
ideal of `R_𝔭`. -/
private theorem approximationPrime_liesOver_localMaximalIdeal
    {S : Type u} [CommRing S] [Algebra Rₚ S] (φ : S →ₐ[Rₚ] R̂_[p]) :
    let q : Ideal S := Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))
    q.LiesOver (maximalIdeal Rₚ) := by
  let q : Ideal S := Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))
  have hqUnder : q.under Rₚ = maximalIdeal Rₚ := by
    -- Proof comment: the approximation map is an `R_𝔭`-algebra map into a local ring, so its
    -- contracted prime sits over the unique maximal ideal of `R_𝔭`.
    simpa [q, Ideal.under_def] using approximationMapComapUnderAtPrime (p := p) φ
  simpa [q, hqUnder] using (Ideal.over_under q : q.LiesOver (q.under Rₚ))

/-- Helper for Lemma 16.13.4: the prime cut out by an approximation map contracts to the original
prime `p` over the base ring `R`. -/
private theorem approximationPrime_comap_eq_basePrime
    {S : Type u} [CommRing S] [Algebra Rₚ S] [Algebra R S] [IsScalarTower R Rₚ S]
    (φ : S →ₐ[Rₚ] R̂_[p]) :
    let q' : PrimeSpectrum S := ⟨Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p])),
      Ideal.comap_isPrime φ.toRingHom (maximalIdeal (R̂_[p]))⟩
    PrimeSpectrum.comap (algebraMap R S) q' = p := by
  let q : Ideal S := Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))
  let q' : PrimeSpectrum S := ⟨q, Ideal.comap_isPrime φ.toRingHom (maximalIdeal (R̂_[p]))⟩
  have hqOverLocal : q.LiesOver (maximalIdeal Rₚ) :=
    approximationPrime_liesOver_localMaximalIdeal (R := R) (p := p) φ
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R S) q = p.asIdeal
  -- Proof comment: after contracting first to `R_𝔭`, the approximation prime contracts further
  -- to the original prime `p`.
  simpa [q, show algebraMap R S = (algebraMap Rₚ S).comp (algebraMap R Rₚ) by rfl] using
    comap_localMaximalIdeal_along_composite_eq (R := R) (p := p) q hqOverLocal

/-- Helper for Lemma 16.13.4: the prime cut out by an approximation map already has residue field
`κ(p)` over the base ring `R`. -/
private theorem approximationPrime_residueFieldMap_bijective_over_base
    {S : Type u} [CommRing S] [Algebra Rₚ S] [Algebra R S] [IsScalarTower R Rₚ S]
    (φ : S →ₐ[Rₚ] R̂_[p]) :
    let q' : PrimeSpectrum S := ⟨Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p])),
      Ideal.comap_isPrime φ.toRingHom (maximalIdeal (R̂_[p]))⟩
    Function.Bijective
      (Ideal.ResidueField.map p.asIdeal q'.asIdeal (algebraMap R S)
        (by
          simpa [PrimeSpectrum.comap_asIdeal] using
            (congrArg PrimeSpectrum.asIdeal
              (approximationPrime_comap_eq_basePrime (R := R) (p := p) (S := S) φ)).symm)) := by
  let q : Ideal S := Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))
  let q' : PrimeSpectrum S := ⟨q, Ideal.comap_isPrime φ.toRingHom (maximalIdeal (R̂_[p]))⟩
  have hqOverLocal : q.LiesOver (maximalIdeal Rₚ) :=
    approximationPrime_liesOver_localMaximalIdeal (R := R) (p := p) φ
  have hq' : PrimeSpectrum.comap (algebraMap R S) q' = p :=
    approximationPrime_comap_eq_basePrime (R := R) (p := p) (S := S) φ
  -- Proof comment: the approximation prime already has the correct local residue field over
  -- `R_𝔭`, so the existing bridge upgrades it to the primewise residue-field map over `R`.
  simpa [q'] using
    residueFieldMapBijective_of_localPrimeResidueFieldMapAtPrime
      (R := R) (p := p) (q := q) hqOverLocal
      (approximationPrimeResidueFieldMap_bijective (R := R) (p := p) φ)

/-- Lemma 16.13.4, regular-completion bridge case: if the completion map
`R_𝔭 → (R_𝔭)^` is regular, then every finite polynomial system over `R` with a solution in
`((R_𝔭)^)^n` can, for each `N`, be approximated modulo `(𝔭')^N` by a solution in an étale
neighborhood of `R` above `𝔭`, with unchanged residue field. -/
@[stacks 0CAR]
theorem exists_etale_solution_at_prime_of_completed_local_solution_of_isRegularRingMap
    (hCompletion : (algebraMap Rₚ (R̂_[p])).IsRegularRingMap)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R) (a : Fin n → R̂_[p])
    (ha : ∀ j, aeval a (f j) = 0) (N : ℕ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : PrimeSpectrum R') (hp' : PrimeSpectrum.comap (algebraMap R R') p' = p)
      (b : Fin n → R'),
      Function.Bijective
        (Ideal.ResidueField.map p.asIdeal p'.asIdeal (algebraMap R R')
          (by
            simpa [PrimeSpectrum.comap_asIdeal] using
              (congrArg PrimeSpectrum.asIdeal hp').symm)) ∧
      (∀ j, aeval b (f j) = 0) ∧
      ∀ i,
        CompletedLocalizationAtPrime.map p p' hp' (a i) -
            algebraMap R' (R̂_[p']) (b i) ∈
          Ideal.map
            (algebraMap (Localization.AtPrime p'.asIdeal) (R̂_[p']))
            ((maximalIdeal (Localization.AtPrime p'.asIdeal)) ^ N) := by
  classical
  let fLocal : Fin m → MvPolynomial (Fin n) Rₚ := fun j ↦ (f j).map (algebraMap R Rₚ)
  have haLocal : ∀ j, aeval a (fLocal j) = 0 := by
    intro j
    -- Proof comment: rewrite the localized system as the coefficientwise image of the original
    -- polynomial system before applying the local approximation theorem.
    simpa [fLocal] using
      (MvPolynomial.aeval_map_algebraMap
        (R := R) (A := Rₚ) (B := R̂_[p]) (x := a) (f j)).trans (ha j)
  -- Proof comment: first apply Theorem `16.13.2` over the local ring `Rₚ`.
  rcases exists_etale_solution_of_adicCompletion_solution
      (R := Rₚ) hCompletion fLocal a haLocal N with
    ⟨S, _instSCommRing, _instSAlg, _instSEtale, m, hmMax, hmOver, φ, bLocal,
      hresLocal, hsolLocal, happroxLocal⟩
  let _ : Algebra R S := (algebraMap R Rₚ).toAlgebra.comp (algebraMap Rₚ S)
  let _ : IsScalarTower R Rₚ S := IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra.Etale R S := etale_over_base_of_etale_over_localization (R := R) (p := p)
  let p' : PrimeSpectrum S := ⟨m, hmMax.1⟩
  have hp' : PrimeSpectrum.comap (algebraMap R S) p' = p :=
    PrimeSpectrum.ext <| by
      change Ideal.comap (algebraMap R S) m = p.asIdeal
      simpa [show algebraMap R S = (algebraMap Rₚ S).comp (algebraMap R Rₚ) by rfl] using
        comap_localMaximalIdeal_along_composite_eq (R := R) (p := p) m hmOver
  have hsolBase : ∀ j, aeval bLocal (f j) = 0 := by
    intro j
    -- Proof comment: forgetting the intermediate coefficient localization recovers the original
    -- polynomial equations over `R`.
    exact
      (MvPolynomial.aeval_map_algebraMap
        (R := R) (A := Rₚ) (B := S) (x := bLocal) (f j)).symm.trans (hsolLocal j)
  have hresBase :
      Function.Bijective
        (Ideal.ResidueField.map p.asIdeal p'.asIdeal (algebraMap R S)
          (by
            simpa [PrimeSpectrum.comap_asIdeal] using
              (congrArg PrimeSpectrum.asIdeal hp').symm)) := by
    -- Proof comment: replace the local residue-field map `κ(R_𝔭) → κ(m)` by the equivalent
    -- primewise map `κ(p) → κ(p')`.
    simpa [p'] using
      residueFieldMapBijective_of_localResidueFieldMapAtPrime
        (R := R) (p := p) (m := m) hmOver hresLocal
  let q : Ideal S := Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))
  let q' : PrimeSpectrum S := ⟨q, Ideal.comap_isPrime φ.toRingHom (maximalIdeal (R̂_[p]))⟩
  have hq' : PrimeSpectrum.comap (algebraMap R S) q' = p :=
    approximationPrime_comap_eq_basePrime (R := R) (p := p) (S := S) φ
  have hresApprox :
      Function.Bijective
        (Ideal.ResidueField.map p.asIdeal q'.asIdeal (algebraMap R S)
          (by
            simpa [PrimeSpectrum.comap_asIdeal] using
              (congrArg PrimeSpectrum.asIdeal hq').symm)) := by
    -- Proof comment: the selected approximation prime already has the correct residue field over
    -- `R`, so only the final branch-locality transport remains.
    simpa [q'] using
      approximationPrime_residueFieldMap_bijective_over_base
        (R := R) (p := p) (S := S) φ
  -- Route correction: continuing to chase the auxiliary branch
  -- `q = Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))` inside this file does not solve the
  -- actual problem. The imported local theorem only returns an arbitrary maximal ideal `m` and an
  -- arbitrary approximation map `φ`, so this consumer cannot prove that `φ` is local at `m`.
  refine ⟨S, inferInstance, inferInstance, inferInstance, q', hq', bLocal, hresApprox, hsolBase, ?_⟩
  -- TODO: finish this by replacing the current prerequisite with a branch-aware companion theorem,
  -- e.g. `exists_etale_solution_of_adicCompletion_solution_at_closedBranch`, whose conclusion
  -- already lands in the completion of the chosen maximal branch. The present API only gives
  -- `a i - φ (bLocal i) ∈ Ideal.map φ.toRingHom (m ^ N)` for an unconstrained `φ : S →ₐ[Rₚ] R̂_[p]`,
  -- while the target here is the canonical `q`-adic completion map for
  -- `q = Ideal.comap φ.toRingHom (maximalIdeal (R̂_[p]))`. In an étale algebra there can be
  -- several maximal ideals over `maximalIdeal Rₚ`, so neither `q = m` nor an equivalent locality
  -- statement for `φ` at `m` follows from Theorem `16.13.2` as currently stated.
  sorry

-- Proof sketch for the source-facing statement: use the Chapter 15 owner instance on the
-- completion map `Rₚ → R̂_[p]` to convert the `G`-ring hypothesis on the local ring `R_𝔭` into
-- the regular-completion hypothesis above.
/-- Lemma 16.13.4: let `R` be a Noetherian ring and `𝔭 ⊂ R` a prime ideal. If a finite system of
polynomials over `R` has a solution in the completed local ring `((R_𝔭)^)^n`, and if the local
ring `R_𝔭` is a `G`-ring, then for every `N` there exists an étale `R`-algebra `R'`, a prime
`𝔭' ⊂ R'` with `PrimeSpectrum.comap (algebraMap R R') 𝔭' = 𝔭`, and a solution in `R'` whose
image in the completed localization at `𝔭'` under the canonical primewise map
`CompletedLocalizationAtPrime.map p p' hp' : R̂_[p] →+* R̂_[p']` agrees with the given formal
solution modulo `(𝔭')^N`, with unchanged residue field. -/
@[stacks 0CAR]
theorem exists_etale_solution_at_prime_of_completed_local_solution
    [IsGRing Rₚ]
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R) (a : Fin n → R̂_[p])
    (ha : ∀ j, aeval a (f j) = 0) (N : ℕ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : PrimeSpectrum R') (hp' : PrimeSpectrum.comap (algebraMap R R') p' = p)
      (b : Fin n → R'),
      Function.Bijective
        (Ideal.ResidueField.map p.asIdeal p'.asIdeal (algebraMap R R')
          (by
            simpa [PrimeSpectrum.comap_asIdeal] using
              (congrArg PrimeSpectrum.asIdeal hp').symm)) ∧
      (∀ j, aeval b (f j) = 0) ∧
      ∀ i,
        CompletedLocalizationAtPrime.map p p' hp' (a i) -
            algebraMap R' (R̂_[p']) (b i) ∈
          Ideal.map
            (algebraMap (Localization.AtPrime p'.asIdeal) (R̂_[p']))
            ((maximalIdeal (Localization.AtPrime p'.asIdeal)) ^ N) := by
  let hCompletion : (algebraMap Rₚ (R̂_[p])).IsRegularRingMap := inferInstance
  exact
    exists_etale_solution_at_prime_of_completed_local_solution_of_isRegularRingMap p
      hCompletion f a ha N

end
