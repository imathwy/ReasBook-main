import Mathlib
import StacksProject_2024.Chap10.Definition_10_125_1
import StacksProject_2024.Chap10.Lemma_10_115_6
import StacksProject_2024.Chap10.Lemma_10_125_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MvPolynomial

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain-style sampling:
- primary domain: relative fiber dimension, quasi-finite localizations, and the coordinate-ideal
  normal form for primes in polynomial algebras over residue fields;
- sampled owner declarations:
  `relativeDimensionAt`,
  `tailVariablesIdeal`,
  `exists_quasiFinite_polynomial_localizationAway_of_relativeDimensionAt_eq`,
  `exists_finite_selfAlgHom_comap_eq_tailVariablesIdeal`;
- best owner abstraction: the primewise owner `q : PrimeSpectrum S`, with the base prime recovered
  canonically as `q.asIdeal.under R`;
- primitive data: the prime `q`, the integer `n`, and the relative-dimension equality;
- derived API: the contracted base prime, its residue field, and the localized extension/tail ideal
  expressions appearing in the conclusion.

Source/core/bridge triage:
- `source-facing`: the existence of localizations `R_f` and `S_g` together with a quasi-finite
  polynomial presentation whose contracted prime is the extension of `q` with the expected tail
  variables;
- `core/canonical`: `relativeDimensionAt`, `tailVariablesIdeal`, and the quasi-finite owner on the
  witnessing ring homomorphism;
- `bridge/view`: the explicit ideal expressions
  `Ideal.map (algebraMap S (Localization.Away g)) q.asIdeal` and
  `Ideal.map (algebraMap R (MvPolynomial (Fin n) (Localization.Away f)))
    (q.asIdeal.under R) ⊔ tailVariablesIdeal _ _ _`.

The two deleted local wrappers were one-off bridges, not owner declarations. Keeping the theorem
indexed only by `q` matches the chapter's primewise API discipline and removes redundant primitive
data without changing the source mathematics.
-/

-- Proof sketch: first apply Lemma `10.125.2` to replace `S` near `q` by a quasi-finite
-- localization over a polynomial algebra in `n` variables. Then use Lemma `10.115.6` on the fiber
-- over `q ∩ R` to change coordinates so that the contracted prime becomes the tail coordinate
-- ideal,
-- lift the resulting coordinates from the fiber to a localization `R_f`, and finally shrink once
-- more using openness of the quasi-finite locus from Lemma `10.123.13`.
/-- Helper for Chap10 Lemma 10 125 3: powers of an element outside a prime ideal are disjoint from
that prime. -/
private lemma powers_disjoint_prime_of_not_mem
    {A : Type u} [CommRing A] (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    Disjoint (Submonoid.powers x : Set A) I := by
  -- A power in the prime would force the element itself into the prime.
  rw [Set.disjoint_left]
  rintro _ ⟨m, rfl⟩ hm
  exact hx ((inferInstance : I.IsPrime).mem_of_pow_mem m hm)

/-- Helper for Chap10 Lemma 10 125 3: localizing a prime away from an element outside it preserves
primality of the extended ideal. -/
private lemma localizedPrimeMap_isPrime
    {A : Type u} [CommRing A] (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    (Ideal.map (algebraMap A (Localization.Away x)) I).IsPrime := by
  -- The disjointness criterion for localization applies to the powers of the inverted element.
  exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x)
    (Localization.Away x) I inferInstance (powers_disjoint_prime_of_not_mem I hx)

/-- Helper for Chap10 Lemma 10 125 3: the extended localized prime contracts back to the original
prime. -/
private lemma localizedPrime_comap_map_eq
    {A : Type u} [CommRing A] (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    Ideal.comap (algebraMap A (Localization.Away x))
        (Ideal.map (algebraMap A (Localization.Away x)) I) =
      I := by
  -- Once the prime is disjoint from the localization submonoid, localization contraction is exact.
  exact IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers x)
    (Localization.Away x) inferInstance (powers_disjoint_prime_of_not_mem I hx)

/-- Helper for Chap10 Lemma 10 125 3: localizing away from an element outside a prime preserves
the residue-field transcendence degree over any compatible base field. -/
private lemma localizedTargetResidueTrdeg_eq
    {k : Type w} {A : Type u} [Field k] [CommRing A] [Algebra k A]
    (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    letI : (Ideal.map (algebraMap A (Localization.Away x)) I).IsPrime :=
      localizedPrimeMap_isPrime I hx
    Cardinal.toNat
        (Algebra.trdeg k
          (Ideal.map (algebraMap A (Localization.Away x)) I).ResidueField) =
      Cardinal.toNat (Algebra.trdeg k I.ResidueField) := by
  let J : Ideal (Localization.Away x) :=
    Ideal.map (algebraMap A (Localization.Away x)) I
  have hJ_prime : J.IsPrime := by
    -- The localized ideal is prime because the inverted powers are disjoint from `I`.
    exact localizedPrimeMap_isPrime I hx
  letI : J.IsPrime := hJ_prime
  have hcomap : I = J.comap (algebraMap A (Localization.Away x)) := by
    -- Contracting the localized prime recovers the original prime.
    exact (localizedPrime_comap_map_eq I hx).symm
  have hbij :
      Function.Bijective
        (Ideal.ResidueField.map I J (algebraMap A (Localization.Away x)) hcomap) := by
    -- Localization maps are surjective on stalks, hence induce bijections on matching residue
    -- fields.
    exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_isLocalization (Submonoid.powers x)
        (Localization.Away x))
      I J hcomap
  let e : I.ResidueField ≃ₐ[k] J.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ I J (IsScalarTower.toAlgHom k A (Localization.Away x)) hcomap)
      hbij
  -- Transport the transcendence degree through the residue-field algebra equivalence.
  simpa [J] using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq (R := k) e).symm

/-- Helper for Chap10 Lemma 10 125 3: if a localized target prime contracts to `q`, then its
residue-field transcendence degree over `κ(q ∩ R)` is the same as that of `q`. -/
private lemma localizedTargetResidueTrdeg_under_eq
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) {g : S}
    (J : Ideal (Localization.Away g)) [J.IsPrime]
    (p : Ideal R) [p.IsPrime] [q.asIdeal.LiesOver p] [J.LiesOver p]
    (hcomap : q.asIdeal = J.comap (algebraMap S (Localization.Away g))) :
    Cardinal.toNat (Algebra.trdeg p.ResidueField J.ResidueField) =
      Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := by
  have hbij :
      Function.Bijective
        (Ideal.ResidueField.map q.asIdeal J (algebraMap S (Localization.Away g)) hcomap) := by
    -- Localization maps are surjective on stalks, so they induce bijective residue-field maps.
    exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_isLocalization (Submonoid.powers g)
        (Localization.Away g))
      q.asIdeal J hcomap
  let eRing : q.asIdeal.ResidueField ≃+* J.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map q.asIdeal J (algebraMap S (Localization.Away g)) hcomap)
      hbij
  have hcomm_R (r : R) :
      eRing (algebraMap R q.asIdeal.ResidueField r) =
        algebraMap R J.ResidueField r := by
    -- The residue-field map respects the image of every source-ring element.
    simpa [eRing, IsScalarTower.algebraMap_apply R S q.asIdeal.ResidueField,
      IsScalarTower.algebraMap_apply R (Localization.Away g) J.ResidueField,
      IsScalarTower.algebraMap_apply R S (Localization.Away g)] using
      (Ideal.ResidueField.map_algebraMap q.asIdeal J (algebraMap S (Localization.Away g))
        hcomap ((algebraMap R S) r))
  have hcomm_hom :
      eRing.toRingHom.comp (algebraMap p.ResidueField q.asIdeal.ResidueField) =
        (algebraMap p.ResidueField J.ResidueField) := by
    -- Since `κ(p)` is a residue-field localization, it is enough to compare on `R`.
    apply Ideal.ResidueField.ringHom_ext (I := p)
    ext r
    simpa [RingHom.comp_apply,
      IsScalarTower.algebraMap_apply R p.ResidueField q.asIdeal.ResidueField,
      IsScalarTower.algebraMap_apply R p.ResidueField J.ResidueField] using hcomm_R r
  have hcomm (x : p.ResidueField) :
      eRing (algebraMap p.ResidueField q.asIdeal.ResidueField x) =
        algebraMap p.ResidueField J.ResidueField x := by
    exact RingHom.congr_fun hcomm_hom x
  let e : q.asIdeal.ResidueField ≃ₐ[p.ResidueField] J.ResidueField :=
    AlgEquiv.ofRingEquiv (f := eRing) hcomm
  -- Transport the transcendence degree through this `κ(p)`-algebra equivalence.
  simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq (R := p.ResidueField) e).symm

/-- Helper for Chap10 Lemma 10 125 3: the prime in the localized target pulled back to the
polynomial presentation is prime and lies over `q ∩ R`. -/
private lemma contractedPresentationPrime_liesOver_under
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (n : ℕ) (g₀ : S) (hg₀ : g₀ ∉ q.asIdeal)
    (π₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀) :
    let Q : Ideal (MvPolynomial (Fin n) R) :=
      Ideal.comap π₀.toRingHom
        (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal)
    Q.IsPrime ∧ Q.under R = q.asIdeal.under R := by
  -- Pull back the localized target prime along the presentation map.
  let Q : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.comap π₀.toRingHom
      (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal)
  have hloc_prime :
      (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal).IsPrime :=
    localizedPrimeMap_isPrime q.asIdeal hg₀
  have hQ_prime : Q.IsPrime := Ideal.comap_isPrime π₀.toRingHom _
  have hloc_comap :
      Ideal.comap (algebraMap S (Localization.Away g₀))
          (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal) =
        q.asIdeal :=
    localizedPrime_comap_map_eq q.asIdeal hg₀
  refine ⟨hQ_prime, ?_⟩
  -- The `R`-algebra compatibility of `π₀` identifies the contraction of `Q` with the contraction
  -- of the localized target prime, which is `q ∩ R`.
  ext r
  let J : Ideal (Localization.Away g₀) :=
    Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal
  have hmem :
      (algebraMap S (Localization.Away g₀)) ((algebraMap R S) r) ∈
          J ↔
        (algebraMap R S) r ∈ q.asIdeal := by
    -- This is exactly the membership form of localization contraction for the extended prime.
    have hmem_comap :
        (algebraMap S (Localization.Away g₀)) ((algebraMap R S) r) ∈ J ↔
          (algebraMap R S) r ∈ Ideal.comap (algebraMap S (Localization.Away g₀)) J :=
      Iff.rfl
    simpa [J, hloc_comap] using hmem_comap
  simpa [Q, Ideal.under_def, Ideal.comap_comap, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R S (Localization.Away g₀)] using hmem

/-- Helper for Chap10 Lemma 10 125 3: the coordinate-normalization theorem over a field may be
reindexed by any proven equality with the residue-field transcendence degree. -/
private lemma existsFiniteSelfAlgHom_comap_eq_tailVariablesIdeal_of_trdeg_toNat_eq
    {k : Type u} [Field k] (n r : ℕ) (Qκ : Ideal (MvPolynomial (Fin n) k)) [Qκ.IsPrime]
    (htr :
      Cardinal.toNat (Algebra.trdeg k Qκ.ResidueField) = r) :
    ∃ θκ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k,
      θκ.Finite ∧ Ideal.comap θκ Qκ = tailVariablesIdeal k n r := by
  -- First use Lemma 10.115.6 with its canonical transcendence-degree index.
  obtain ⟨θκ, hθκ_finite, hθκ_comap⟩ :=
    exists_finite_selfAlgHom_comap_eq_tailVariablesIdeal (k := k) (n := n) Qκ
  refine ⟨θκ, hθκ_finite, ?_⟩
  -- Then rewrite that canonical index to the prescribed target index.
  simpa [htr] using hθκ_comap

/-- Helper for Chap10 Lemma 10 125 3: once the transported fiber prime has the target residue
transcendence degree, it admits finite coordinates with the target tail ideal. -/
private lemma existsPresentationFiberCoordinateNormalization
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (n : ℕ) (Qκ : Ideal (MvPolynomial (Fin n) k)) [Qκ.IsPrime]
    (htr :
      Cardinal.toNat (Algebra.trdeg k Qκ.ResidueField) =
        Cardinal.toNat (Algebra.trdeg k L)) :
    ∃ θκ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k,
      θκ.Finite ∧
        Ideal.comap θκ Qκ =
          tailVariablesIdeal k n (Cardinal.toNat (Algebra.trdeg k L)) := by
  -- This packages the pure residue-field normal form needed before denominator clearing.
  exact existsFiniteSelfAlgHom_comap_eq_tailVariablesIdeal_of_trdeg_toNat_eq
    (n := n) (r := Cardinal.toNat (Algebra.trdeg k L)) Qκ htr

/-- Helper for Chap10 Lemma 10 125 3: a finite family in a residue field admits one common
nonzero denominator over the quotient by the prime. -/
private lemma existsCommonDenominatorResidueFieldQuotientFamily
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    {ι : Type*} [Finite ι] (x : ι → p.ResidueField) :
    ∃ s : A ⧸ p, s ≠ 0 ∧ ∃ num : ι → A ⧸ p,
      ∀ i, algebraMap (A ⧸ p) p.ResidueField (num i) =
        algebraMap (A ⧸ p) p.ResidueField s * x i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let frac : ι → (A ⧸ p) × nonZeroDivisors (A ⧸ p) := fun i ↦
    Classical.choose (IsLocalization.surj (nonZeroDivisors (A ⧸ p)) (x i))
  let den : ι → nonZeroDivisors (A ⧸ p) := fun i ↦ (frac i).2
  let sDen : nonZeroDivisors (A ⧸ p) := ∏ i, den i
  let num : ι → A ⧸ p := fun i ↦
    (frac i).1 * (Finset.univ.erase i).prod (fun j ↦ (den j : A ⧸ p))
  refine ⟨(sDen : A ⧸ p), ?_, num, ?_⟩
  · -- The common denominator is a product in the non-zero-divisor submonoid.
    exact mem_nonZeroDivisors_iff_ne_zero.mp sDen.2
  intro i
  have hfrac :
      x i * algebraMap (A ⧸ p) p.ResidueField (den i : A ⧸ p) =
        algebraMap (A ⧸ p) p.ResidueField (frac i).1 :=
    Classical.choose_spec (IsLocalization.surj (nonZeroDivisors (A ⧸ p)) (x i))
  have hprod :
      algebraMap (A ⧸ p) p.ResidueField (den i : A ⧸ p) *
          ((Finset.univ.erase i).prod fun j ↦
            algebraMap (A ⧸ p) p.ResidueField (den j : A ⧸ p)) =
        algebraMap (A ⧸ p) p.ResidueField (sDen : A ⧸ p) := by
    -- Reinsert the distinguished denominator into the product of all denominators.
    calc
      algebraMap (A ⧸ p) p.ResidueField (den i : A ⧸ p) *
          ((Finset.univ.erase i).prod fun j ↦
            algebraMap (A ⧸ p) p.ResidueField (den j : A ⧸ p))
          = ∏ j, algebraMap (A ⧸ p) p.ResidueField (den j : A ⧸ p) := by
              exact Finset.mul_prod_erase Finset.univ
                (fun j ↦ algebraMap (A ⧸ p) p.ResidueField (den j : A ⧸ p)) (by simp)
      _ = algebraMap (A ⧸ p) p.ResidueField (sDen : A ⧸ p) := by
            simp [sDen, map_prod]
  -- Multiply the individual fractional representation by the complementary denominator product.
  calc
    algebraMap (A ⧸ p) p.ResidueField (num i)
        = algebraMap (A ⧸ p) p.ResidueField (frac i).1 *
            ((Finset.univ.erase i).prod fun j ↦
              algebraMap (A ⧸ p) p.ResidueField (den j : A ⧸ p)) := by
              simp [num, map_prod]
    _ = (x i * algebraMap (A ⧸ p) p.ResidueField (den i : A ⧸ p)) *
            ((Finset.univ.erase i).prod fun j ↦
              algebraMap (A ⧸ p) p.ResidueField (den j : A ⧸ p)) := by
              rw [← hfrac]
    _ = x i * algebraMap (A ⧸ p) p.ResidueField (sDen : A ⧸ p) := by
          rw [mul_assoc, hprod]
    _ = algebraMap (A ⧸ p) p.ResidueField (sDen : A ⧸ p) * x i := by
          rw [mul_comm]

/-- Helper for Chap10 Lemma 10 125 3: an element outside a prime gives a specialization from
the corresponding away localization to the residue field. -/
private lemma existsResidueFieldSpecializationAway
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] {f : A} (hf : f ∉ p) :
    ∃ σf : Localization.Away f →+* p.ResidueField,
      σf.comp (algebraMap A (Localization.Away f)) = algebraMap A p.ResidueField := by
  -- The image of `f` in the residue field is nonzero, hence a unit, so the universal property of
  -- the away localization gives the specialization map.
  have hunit : IsUnit (algebraMap A p.ResidueField f) := by
    exact isUnit_iff_ne_zero.mpr (by simpa [Ideal.algebraMap_residueField_eq_zero] using hf)
  refine ⟨IsLocalization.Away.lift f hunit, ?_⟩
  exact IsLocalization.Away.lift_comp (S := Localization.Away f)
    (g := algebraMap A p.ResidueField) f hunit

/-- Helper for Chap10 Lemma 10 125 3: a finite family of residue-field elements lifts to one
away localization after choosing a common denominator outside the prime. -/
private lemma existsResidueFieldFiniteFamilyLiftAway
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    {ι : Type*} [Finite ι] (x : ι → p.ResidueField) :
    ∃ f : A, f ∉ p ∧
      ∃ σf : Localization.Away f →+* p.ResidueField,
        σf.comp (algebraMap A (Localization.Away f)) = algebraMap A p.ResidueField ∧
          ∃ xf : ι → Localization.Away f, ∀ i, σf (xf i) = x i := by
  classical
  -- First clear denominators in the quotient domain `A ⧸ p`.
  obtain ⟨s, hs_ne, num, hnum⟩ :=
    existsCommonDenominatorResidueFieldQuotientFamily (A := A) p x
  obtain ⟨f, hf_eq⟩ := Ideal.Quotient.mk_surjective s
  have hf_not_mem : f ∉ p := by
    intro hf
    exact hs_ne (by simpa [← hf_eq] using (Ideal.Quotient.eq_zero_iff_mem.mpr hf))
  obtain ⟨σf, hσf⟩ := existsResidueFieldSpecializationAway p hf_not_mem
  let numLift : ι → A := fun i ↦ Classical.choose (Ideal.Quotient.mk_surjective (num i))
  let xf : ι → Localization.Away f := fun i ↦
    algebraMap A (Localization.Away f) (numLift i) * IsLocalization.Away.invSelf f
  refine ⟨f, hf_not_mem, σf, hσf, xf, ?_⟩
  intro i
  -- The lifted numerator maps to the quotient numerator, and multiplying by the inverse of the
  -- common denominator recovers the original residue-field element.
  have hnumLift :
      algebraMap A p.ResidueField (numLift i) =
        algebraMap (A ⧸ p) p.ResidueField (num i) := by
    simpa [numLift] using congrArg (algebraMap (A ⧸ p) p.ResidueField)
      (Classical.choose_spec (Ideal.Quotient.mk_surjective (num i)))
  have hf_image :
      algebraMap A p.ResidueField f =
        algebraMap (A ⧸ p) p.ResidueField s := by
    simpa [hf_eq] using
      (Ideal.algebraMap_quotient_residueField_mk (I := p) f).symm
  have hden :
      σf (algebraMap A (Localization.Away f) f) * σf (IsLocalization.Away.invSelf f) = 1 := by
    have hden0 :
        σf (algebraMap A (Localization.Away f) f *
            IsLocalization.Away.invSelf (S := Localization.Away f) f) =
          σf (1 : Localization.Away f) :=
      congrArg σf
        (IsLocalization.Away.mul_invSelf (R := A) (S := Localization.Away f) f)
    rw [map_mul, map_one] at hden0
    simpa using hden0
  have hden' :
      algebraMap A p.ResidueField f * σf (IsLocalization.Away.invSelf f) = 1 := by
    simpa [← RingHom.comp_apply, hσf] using hden
  calc
    σf (xf i)
        = σf (algebraMap A (Localization.Away f) (numLift i)) *
            σf (IsLocalization.Away.invSelf f) := by
              simp [xf]
    _ = algebraMap A p.ResidueField (numLift i) *
            σf (IsLocalization.Away.invSelf f) := by
              rw [← RingHom.comp_apply, hσf]
    _ = (algebraMap A p.ResidueField f * x i) *
            σf (IsLocalization.Away.invSelf f) := by
              rw [hnumLift, hnum i, hf_image]
    _ = x i := by
          calc
            (algebraMap A p.ResidueField f * x i) * σf (IsLocalization.Away.invSelf f)
                = x i * (algebraMap A p.ResidueField f *
                    σf (IsLocalization.Away.invSelf f)) := by
                    ring
            _ = x i := by rw [hden', mul_one]

/-- Helper for Chap10 Lemma 10 125 3: a finite family of residue-field polynomials lifts
coefficientwise to one away localization. -/
private lemma existsResiduePolynomialFamilyLiftAway
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    {ι σ : Type*} [Finite ι] (Pκ : ι → MvPolynomial σ p.ResidueField) :
    ∃ f : A, f ∉ p ∧
      ∃ σf : Localization.Away f →+* p.ResidueField,
        σf.comp (algebraMap A (Localization.Away f)) = algebraMap A p.ResidueField ∧
          ∃ Pf : ι → MvPolynomial σ (Localization.Away f),
            ∀ i, MvPolynomial.map σf (Pf i) = Pκ i := by
  classical
  -- Lift the finite set of all coefficients appearing in the polynomial family.
  let α := Σ i : ι, {m : σ →₀ ℕ // m ∈ (Pκ i).support}
  haveI : Fintype α := Fintype.ofFinite α
  let coeffFamily : α → p.ResidueField := fun a ↦ (Pκ a.1).coeff a.2.1
  obtain ⟨f, hf, σf, hσf, coeffLift, hcoeffLift⟩ :=
    existsResidueFieldFiniteFamilyLiftAway (A := A) p coeffFamily
  let Pf : ι → MvPolynomial σ (Localization.Away f) := fun i ↦
    ∑ m ∈ (Pκ i).support,
      MvPolynomial.monomial m
        (if hm : m ∈ (Pκ i).support then coeffLift ⟨i, ⟨m, hm⟩⟩ else 0)
  refine ⟨f, hf, σf, hσf, Pf, ?_⟩
  intro i
  -- Mapping the lifted finite support term-by-term recovers the original coefficient expansion.
  calc
    MvPolynomial.map σf (Pf i)
        = ∑ m ∈ (Pκ i).support, MvPolynomial.monomial m ((Pκ i).coeff m) := by
            simp only [Pf, map_sum, MvPolynomial.map_monomial]
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [dif_pos hm, hcoeffLift]
    _ = Pκ i := by
          exact MvPolynomial.support_sum_monomial_coeff (Pκ i)

/-- Helper for Chap10 Lemma 10 125 3: a residue-field polynomial self-map lifts on coordinate
functions to one away localization. -/
private lemma existsLiftedCoordinateSelfMapAway
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] (n : ℕ)
    (θκ : MvPolynomial (Fin n) p.ResidueField →ₐ[p.ResidueField]
      MvPolynomial (Fin n) p.ResidueField) :
    ∃ f : A, f ∉ p ∧
      ∃ σf : Localization.Away f →+* p.ResidueField,
        σf.comp (algebraMap A (Localization.Away f)) = algebraMap A p.ResidueField ∧
          ∃ θf : MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
              MvPolynomial (Fin n) (Localization.Away f),
            ∀ i, MvPolynomial.map σf (θf (MvPolynomial.X i)) = θκ (MvPolynomial.X i) := by
  -- Lift the finite family of images of the coordinate variables, then use polynomial
  -- extensionality to assemble the lifted self-map.
  obtain ⟨f, hf, σf, hσf, Pvar, hPvar⟩ :=
    existsResiduePolynomialFamilyLiftAway (A := A) p
      (fun i : Fin n ↦ θκ (MvPolynomial.X i))
  let θf : MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
      MvPolynomial (Fin n) (Localization.Away f) :=
    MvPolynomial.aeval Pvar
  refine ⟨f, hf, σf, hσf, θf, ?_⟩
  intro i
  -- The chosen variable images are the computation rules for the lifted `aeval` map.
  simpa [θf] using hPvar i

/-- Helper for Chap10 Lemma 10 125 3: a lifted coordinate self-map specializes to the residue-field
self-map once it agrees on coordinate variables. -/
private lemma liftedCoordinate_specializes
    {A : Type u} {k : Type v} [CommRing A] [CommRing k]
    (n : ℕ) (σ : A →+* k)
    (θf : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin n) A)
    (θκ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k)
    (hX : ∀ i, MvPolynomial.map σ (θf (MvPolynomial.X i)) = θκ (MvPolynomial.X i)) :
    (MvPolynomial.map σ).comp θf.toRingHom =
      θκ.toRingHom.comp (MvPolynomial.map σ) := by
  -- Polynomial ring maps are determined by constants and coordinate variables.
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply]
  · intro i
    simpa [RingHom.comp_apply] using hX i

/-- Helper for Chap10 Lemma 10 125 3: an algebra equivalence from the transported fiber
prime's residue field to the target residue field supplies the target-index coordinate normal
form. -/
private lemma existsPresentationFiberCoordinateNormalization_of_algEquiv
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (n : ℕ) (Qκ : Ideal (MvPolynomial (Fin n) k)) [Qκ.IsPrime]
    (e : Qκ.ResidueField ≃ₐ[k] L) :
    ∃ θκ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k,
      θκ.Finite ∧
        Ideal.comap θκ Qκ =
          tailVariablesIdeal k n (Cardinal.toNat (Algebra.trdeg k L)) := by
  have htr :
      Cardinal.toNat (Algebra.trdeg k Qκ.ResidueField) =
        Cardinal.toNat (Algebra.trdeg k L) := by
    -- Transport the transcendence degree through the residue-field algebra equivalence.
    simpa only [Cardinal.toNat_lift] using
      congrArg Cardinal.toNat (AlgEquiv.lift_trdeg_eq (R := k) e)
  -- Feed the transported index equality into the coordinate-normalization helper.
  exact existsPresentationFiberCoordinateNormalization (n := n) Qκ htr

/-- Helper for Chap10 Lemma 10 125 3: equality after passing to the canonical fiber prime
identification determines the original prime lying over the base prime. -/
private lemma prime_eq_of_primesOverOrderIsoFiber_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (P₁ P₂ : p.primesOver B)
    (hfiber :
      (PrimeSpectrum.primesOverOrderIsoFiber A B p) P₁ =
        (PrimeSpectrum.primesOverOrderIsoFiber A B p) P₂) :
    P₁.1 = P₂.1 := by
  -- The order isomorphism is injective, so equality in the fiber descends to the primes over `p`.
  have hP : P₁ = P₂ :=
    (PrimeSpectrum.primesOverOrderIsoFiber A B p).injective hfiber
  simpa using congrArg Subtype.val hP

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 3: multiplying a target denominator outside `q` by the image
of a source denominator outside `q ∩ R` still gives a target denominator outside `q`. -/
private lemma mul_algebraMap_not_mem_prime_of_not_mem_under
    (q : PrimeSpectrum S) {g : S} {f : R}
    (hg : g ∉ q.asIdeal) (hf : f ∉ q.asIdeal.under R) :
    g * algebraMap R S f ∉ q.asIdeal := by
  -- Primality reduces membership of the product to one of the two forbidden factors.
  intro hmul
  rcases (inferInstance : q.asIdeal.IsPrime).mem_or_mem hmul with hgmem | hfmem
  · exact hg hgmem
  · exact hf hfmem

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 125 3: a source denominator outside `q ∩ R` determines the
standard target denominator used in the final shrink. -/
private lemma existsTargetDenominatorForSourceDenominator
    (q : PrimeSpectrum S) (g₀ : S) (hg₀ : g₀ ∉ q.asIdeal) {f : R}
    (hf : f ∉ q.asIdeal.under R) :
    ∃ g : S, g ∉ q.asIdeal ∧ g = g₀ * algebraMap R S f := by
  -- Package the planned target shrink and discharge its side condition once by primality.
  refine ⟨g₀ * algebraMap R S f, ?_, rfl⟩
  exact mul_algebraMap_not_mem_prime_of_not_mem_under q hg₀ hf

/-- Helper for Chap10 Lemma 10 125 3: a polynomial self-map is finite once all coordinate
variables are integral over the algebra structure induced by that self-map. -/
private lemma finiteSelfAlgHom_of_integral_variables
    {A : Type u} [CommRing A] (n : ℕ)
    (θ : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin n) A)
    (hX : ∀ i : Fin n,
      @IsIntegral (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A) _ _
        θ.toRingHom.toAlgebra (MvPolynomial.X i)) :
    θ.Finite := by
  let B := MvPolynomial (Fin n) A
  letI : Algebra B B := θ.toRingHom.toAlgebra
  let T : Subalgebra B B := Algebra.adjoin B (Set.range (MvPolynomial.X : Fin n → B))
  have hmem_all : ∀ P : B, P ∈ T := by
    intro P
    -- Constants come from the source through `θ`, while the variables are the chosen generators.
    induction P using MvPolynomial.induction_on with
    | C a =>
        have hconst : algebraMap B B (MvPolynomial.C a) = (MvPolynomial.C a : B) := by
          change θ (MvPolynomial.C a) = (MvPolynomial.C a : B)
          exact θ.commutes a
        rw [← hconst]
        exact Subalgebra.algebraMap_mem T (MvPolynomial.C a)
    | add P Q hP hQ =>
        exact add_mem hP hQ
    | mul_X P i hP =>
        exact mul_mem hP (Algebra.subset_adjoin ⟨i, rfl⟩)
  have htop : T = ⊤ := by
    -- The preceding induction identifies the target polynomial ring with the algebra generated by
    -- its coordinate variables over the `θ`-source.
    rw [eq_top_iff]
    intro P _
    exact hmem_all P
  have hIntegral : θ.toRingHom.IsIntegral := by
    intro P
    change @IsIntegral B B _ _ θ.toRingHom.toAlgebra P
    -- Integral variables and source constants make every polynomial integral by induction.
    induction P using MvPolynomial.induction_on with
    | C a =>
        have hconst : algebraMap B B (MvPolynomial.C a) = (MvPolynomial.C a : B) := by
          change θ (MvPolynomial.C a) = (MvPolynomial.C a : B)
          exact θ.commutes a
        rw [← hconst]
        exact isIntegral_algebraMap
    | add P Q hP hQ =>
        exact hP.add hQ
    | mul_X P i hP =>
        exact hP.mul (hX i)
  have hFiniteType : θ.toRingHom.FiniteType := by
    have hfg : (⊤ : Subalgebra B B).FG := by
      rw [← htop]
      exact (Subalgebra.fg_def).2
        ⟨Set.range (MvPolynomial.X : Fin n → B), Set.finite_range _, rfl⟩
    exact Algebra.FiniteType.mk hfg
  -- A finite-type integral ring hom is finite, giving the required finite self-map.
  simpa [AlgHom.Finite] using
    (RingHom.Finite.of_isIntegral_of_finiteType hIntegral hFiniteType)

/-- Helper for Chap10 Lemma 10 125 3: the fiber of a polynomial algebra over a prime is the
polynomial algebra over the residue field. -/
private noncomputable def fiberMvPolynomialAlgEquiv
    (p : Ideal R) [p.IsPrime] (n : ℕ) :
    p.Fiber (MvPolynomial (Fin n) R) ≃ₐ[p.ResidueField]
      MvPolynomial (Fin n) p.ResidueField :=
  MvPolynomial.algebraTensorAlgEquiv R p.ResidueField

/-- Helper for Chap10 Lemma 10 125 3: transporting a prime through a residue-field algebra
equivalence preserves its residue-field transcendence degree. -/
private lemma comap_algEquiv_residueTrdeg_toNat_eq
    {k : Type w} {A : Type u} {B : Type v}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (J : Ideal B) [J.IsPrime] :
    let I : Ideal A := Ideal.comap e.toRingHom J
    Cardinal.toNat (Algebra.trdeg k I.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k J.ResidueField) := by
  let I : Ideal A := Ideal.comap e.toRingHom J
  have hI_prime : I.IsPrime := Ideal.comap_isPrime e.toRingHom J
  letI : I.IsPrime := hI_prime
  have hcomap : I = J.comap e.toRingHom := rfl
  have hbij :
      Function.Bijective (Ideal.ResidueField.map I J e.toRingHom hcomap) := by
    -- A surjective algebra equivalence is surjective on stalks, hence on the two residue fields.
    exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_surjective e.surjective) I J hcomap
  let eResidue : I.ResidueField ≃ₐ[k] J.ResidueField :=
    AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ I J e hcomap) hbij
  -- The residue-field algebra equivalence transports transcendence degree.
  simpa [I] using congrArg Cardinal.toNat (AlgEquiv.lift_trdeg_eq (R := k) eResidue)

/-- Helper for Chap10 Lemma 10 125 3: for a quasi-finite algebra, passing from a prime to a
lying-over prime only changes the residue field by an algebraic extension, so the transcendence
degree over any compatible base field is unchanged. -/
private lemma quasiFinite_liesOver_residueTrdeg_toNat_eq
    {k : Type w} {A : Type u} {B : Type v}
    [Field k] [CommRing A] [CommRing B] [Algebra A B] [Algebra.QuasiFinite A B]
    (Q : Ideal A) [Q.IsPrime] (J : Ideal B) [J.IsPrime] [J.LiesOver Q]
    [Algebra k Q.ResidueField] [Algebra k J.ResidueField]
    [IsScalarTower k Q.ResidueField J.ResidueField] :
    Cardinal.toNat (Algebra.trdeg k Q.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k J.ResidueField) := by
  have htrdeg_add :=
    lift_trdeg_add_eq (R := k) (S := Q.ResidueField) (A := J.ResidueField)
  have htrdeg_zero : Algebra.trdeg Q.ResidueField J.ResidueField = 0 := by
    letI : Module.Finite Q.ResidueField J.ResidueField := inferInstance
    letI : Algebra.IsAlgebraic Q.ResidueField J.ResidueField :=
      Algebra.IsAlgebraic.of_finite (R := Q.ResidueField) (A := J.ResidueField)
    -- The quasi-finite residue extension is finite, hence algebraic.
    exact trdeg_eq_zero (R := Q.ResidueField) (A := J.ResidueField)
  -- Remove the algebraic top term from the trdeg tower formula and compare `toNat`s.
  rw [htrdeg_zero, Cardinal.lift_zero, add_zero] at htrdeg_add
  simpa [Cardinal.toNat_lift] using congrArg Cardinal.toNat htrdeg_add

/-- Helper for Chap10 Lemma 10 125 3: the canonical prime in the tensor fiber has the same
residue-field transcendence degree as the original prime lying over the base prime. -/
private lemma primesOverFiber_residueTrdeg_toNat_eq
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (Qover : p.primesOver B) :
    let Qfiber : PrimeSpectrum (p.Fiber B) :=
      (PrimeSpectrum.primesOverOrderIsoFiber R B p) Qover
    Cardinal.toNat (Algebra.trdeg p.ResidueField Qfiber.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg p.ResidueField Qover.1.ResidueField) := by
  let Qfiber : PrimeSpectrum (p.Fiber B) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R B p) Qover
  have hcomap :
      Qover.1 = Qfiber.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom := by
    -- The inverse direction of `primesOverOrderIsoFiber` says exactly that the fiber prime
    -- contracts along the tensor-fiber right inclusion to the original lying-over prime.
    have h := congrArg Subtype.val
      ((PrimeSpectrum.primesOverOrderIsoFiber R B p).symm_apply_apply Qover)
    simpa [Qfiber, PrimeSpectrum.primesOverOrderIsoFiber, PrimeSpectrum.preimageOrderIsoFiber,
      PrimeSpectrum.preimageEquivFiber] using h.symm
  have hbij :
      Function.Bijective
        (Ideal.ResidueField.map Qover.1 Qfiber.asIdeal
          Algebra.TensorProduct.includeRight.toRingHom hcomap) := by
    -- The residue-field map for this contraction is bijective because `κ(p) → κ(p) ⊗ B` is
    -- surjective on stalks after base change.
    exact RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (p.surjectiveOnStalks_residueField.baseChange')
      Qover.1 Qfiber.asIdeal hcomap
  let eRing : Qover.1.ResidueField ≃+* Qfiber.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map Qover.1 Qfiber.asIdeal
        Algebra.TensorProduct.includeRight.toRingHom hcomap)
      hbij
  have hcomm_R (r : R) :
      eRing (algebraMap R Qover.1.ResidueField r) =
        algebraMap R Qfiber.asIdeal.ResidueField r := by
    -- The residue-field map respects the image of the original base ring.
    simpa [eRing, IsScalarTower.algebraMap_apply R B Qover.1.ResidueField,
      IsScalarTower.algebraMap_apply R (p.Fiber B) Qfiber.asIdeal.ResidueField] using
      (Ideal.ResidueField.map_algebraMap Qover.1 Qfiber.asIdeal
        Algebra.TensorProduct.includeRight.toRingHom hcomap ((algebraMap R B) r))
  have hcomm_hom :
      eRing.toRingHom.comp (algebraMap p.ResidueField Qover.1.ResidueField) =
        (algebraMap p.ResidueField Qfiber.asIdeal.ResidueField) := by
    -- Since `κ(p)` is the localization of `R/p`, compatibility on `R` determines the whole
    -- `κ(p)`-algebra structure.
    apply Ideal.ResidueField.ringHom_ext (I := p)
    ext r
    simpa [RingHom.comp_apply,
      IsScalarTower.algebraMap_apply R p.ResidueField Qover.1.ResidueField,
      IsScalarTower.algebraMap_apply R p.ResidueField Qfiber.asIdeal.ResidueField] using
      hcomm_R r
  have hcomm (x : p.ResidueField) :
      eRing (algebraMap p.ResidueField Qover.1.ResidueField x) =
        algebraMap p.ResidueField Qfiber.asIdeal.ResidueField x := by
    exact RingHom.congr_fun hcomm_hom x
  let e : Qover.1.ResidueField ≃ₐ[p.ResidueField] Qfiber.asIdeal.ResidueField :=
    AlgEquiv.ofRingEquiv (f := eRing) hcomm
  -- Transport transcendence degree across the residue-field algebra equivalence.
  simpa [Qfiber, Cardinal.toNat_lift] using
    congrArg Cardinal.toNat (AlgEquiv.lift_trdeg_eq (R := p.ResidueField) e).symm

/-- Helper for Chap10 Lemma 10 125 3: a tail-coordinate comap normal form can be reindexed by a
plain equality of natural-number indices. -/
private lemma comap_eq_tailVariablesIdeal_of_index_eq
    {A : Type u} [CommRing A] (n : ℕ) {r s : ℕ}
    {B : Type v} [CommRing B] (θ : MvPolynomial (Fin n) A →+* B) (I : Ideal B)
    (hcomap : Ideal.comap θ I = tailVariablesIdeal A n r) (hrs : r = s) :
    Ideal.comap θ I = tailVariablesIdeal A n s := by
  -- The adapter deliberately changes only the numeric tail index, avoiding any residue-field
  -- algebra transport.
  simpa [hrs] using hcomap

/-- Helper for Chap10 Lemma 10 125 3: after the contracted presentation prime has been identified
over `q ∩ R`, the remaining geometric step is to normalize fiber coordinates, clear
denominators, and shrink the target once more. -/
private theorem existsSpreadCoordinateNormalizedPresentationFromContraction
    (q : PrimeSpectrum S) (n : ℕ) (g₀ : S) (hg₀ : g₀ ∉ q.asIdeal)
    (π₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀) (hπ₀ : π₀.QuasiFinite)
    (Q : Ideal (MvPolynomial (Fin n) R))
    (_hQ_def :
      Q =
        Ideal.comap π₀.toRingHom
          (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal))
    (_hQ_prime : Q.IsPrime) (_hQ_under : Q.under R = q.asIdeal.under R) :
    ∃ f : R, f ∉ q.asIdeal.under R ∧
      ∃ g : S, g ∉ q.asIdeal ∧
        ∃ φ : MvPolynomial (Fin n) (Localization.Away f) →+* Localization.Away g,
          φ.QuasiFinite ∧
            Ideal.comap φ (Ideal.map (algebraMap S (Localization.Away g)) q.asIdeal) =
                Ideal.map
                  (algebraMap R (MvPolynomial (Fin n) (Localization.Away f)))
                  (q.asIdeal.under R) ⊔
                tailVariablesIdeal (Localization.Away f) n
                  (Cardinal.toNat
                    (Algebra.trdeg (q.asIdeal.under R).ResidueField
                      q.asIdeal.ResidueField)) := by
  -- Route correction: the residue-field normal-form and fiber-injectivity pieces are now isolated
  -- in the preceding helpers. The remaining gap is the actual spreading step: compare the
  -- transported fiber prime with `q`, clear denominators for the finite coordinate map, and shrink
  -- the target localization so equality of fiber primes gives the displayed contraction equality.
  let p : Ideal R := q.asIdeal.under R
  have hQ_def :
      Q =
        Ideal.comap π₀.toRingHom
          (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal) :=
    _hQ_def
  have hQ_under : Q.under R = p := by
    -- Record the contracted-prime equality in the spelling used by the fiber API.
    simpa [p] using _hQ_under
  letI : Q.IsPrime := _hQ_prime
  have hQ_lies : Q.LiesOver p := by
    -- Package the contraction equality as the canonical `LiesOver` instance.
    rw [Ideal.liesOver_iff]
    exact hQ_under.symm
  letI : Q.LiesOver p := hQ_lies
  have hp_eq : p = q.asIdeal.under R := rfl
  have hQ_def' :
      Q =
        Ideal.comap π₀.toRingHom
          (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal) := hQ_def
  have hq_lies : q.asIdeal.LiesOver p := by
    -- The target prime itself lies over its contraction `p`.
    exact ⟨rfl⟩
  letI : q.asIdeal.LiesOver p := hq_lies
  have htarget_denom {f : R} (hf : f ∉ p) :
      ∃ g : S, g ∉ q.asIdeal ∧ g = g₀ * algebraMap R S f := by
    -- Once denominator clearing has produced `f ∉ p`, the target denominator is fixed and valid.
    exact existsTargetDenominatorForSourceDenominator q g₀ hg₀ (by simpa [p] using hf)
  let J₀ : Ideal (Localization.Away g₀) :=
    Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal
  have hJ₀_prime : J₀.IsPrime := by
    -- The first localized target prime is valid because `g₀` was chosen outside `q`.
    exact localizedPrimeMap_isPrime q.asIdeal hg₀
  letI : J₀.IsPrime := hJ₀_prime
  have hJ₀_comap : q.asIdeal = J₀.comap (algebraMap S (Localization.Away g₀)) := by
    -- This is the residue-field comparison's contraction hypothesis.
    exact (localizedPrime_comap_map_eq q.asIdeal hg₀).symm
  have hJ₀_lies : J₀.LiesOver p := by
    -- Its contraction to `R` is the same base prime `p = q ∩ R`.
    rw [Ideal.liesOver_iff]
    ext r
    have hmem :
        (algebraMap S (Localization.Away g₀)) ((algebraMap R S) r) ∈ J₀ ↔
          (algebraMap R S) r ∈ q.asIdeal := by
      simpa [hJ₀_comap] using
        (Iff.rfl :
          (algebraMap S (Localization.Away g₀)) ((algebraMap R S) r) ∈ J₀ ↔
            (algebraMap R S) r ∈
              J₀.comap (algebraMap S (Localization.Away g₀)))
    simpa [J₀, p, Ideal.under_def,
      IsScalarTower.algebraMap_apply R S (Localization.Away g₀)] using hmem.symm
  letI : J₀.LiesOver p := hJ₀_lies
  have hJ₀_trdeg :
      Cardinal.toNat (Algebra.trdeg p.ResidueField J₀.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := by
    -- The harmless target localization preserves the residue-field trdeg over `κ(p)`.
    exact localizedTargetResidueTrdeg_under_eq q J₀ p hJ₀_comap
  let Qover : p.primesOver (MvPolynomial (Fin n) R) := ⟨Q, _hQ_prime, hQ_lies⟩
  let Qfiber : PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R)) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R (MvPolynomial (Fin n) R) p) Qover
  let efiber := fiberMvPolynomialAlgEquiv (R := R) p n
  let Qκ : Ideal (MvPolynomial (Fin n) p.ResidueField) :=
    Ideal.comap efiber.symm.toRingHom Qfiber.asIdeal
  have hQκ_prime : Qκ.IsPrime := by
    -- Transport the canonical fiber prime through the polynomial/residue-field equivalence.
    exact Ideal.comap_isPrime efiber.symm.toRingHom Qfiber.asIdeal
  letI : Qκ.IsPrime := hQκ_prime
  have hQκ_Qfiber_trdeg := by
    -- Move the transported polynomial prime back through the fiber equivalence.
    simpa [Qκ, efiber] using
      (comap_algEquiv_residueTrdeg_toNat_eq
        (e := (fiberMvPolynomialAlgEquiv (R := R) p n).symm) Qfiber.asIdeal)
  letI : Algebra (MvPolynomial (Fin n) R) (Localization.Away g₀) :=
    π₀.toRingHom.toAlgebra
  letI : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away g₀) := by
    -- The presentation map is an `R`-algebra map, so its induced algebra structure forms the
    -- expected tower over the polynomial algebra.
    exact IsScalarTower.of_algebraMap_eq' π₀.comp_algebraMap.symm
  have hJ₀_lies_Q : J₀.LiesOver Q := by
    -- The definition of `Q` is exactly contraction of `J₀` along the presentation map.
    rw [Ideal.liesOver_iff]
    ext x
    simpa [J₀, hQ_def, Ideal.under_def, RingHom.algebraMap_toAlgebra]
  letI : J₀.LiesOver Q := hJ₀_lies_Q
  letI : Algebra.QuasiFinite (MvPolynomial (Fin n) R) (Localization.Away g₀) :=
    RingHom.QuasiFinite.toAlgebra hπ₀
  have hQ_J₀_trdeg :
      Cardinal.toNat (Algebra.trdeg p.ResidueField Q.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField J₀.ResidueField) := by
    -- Quasi-finiteness makes the residue-field extension from `Q` to `J₀` algebraic.
    exact quasiFinite_liesOver_residueTrdeg_toNat_eq (k := p.ResidueField) Q J₀
  have hQ_q_trdeg :
      Cardinal.toNat (Algebra.trdeg p.ResidueField Q.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := by
    -- Chain the quasi-finite presentation comparison with the harmless target localization.
    exact hQ_J₀_trdeg.trans hJ₀_trdeg
  have hQfiber_Q_trdeg :
      Cardinal.toNat (Algebra.trdeg p.ResidueField Qfiber.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField Q.ResidueField) := by
    -- The canonical tensor-fiber prime and the original lying-over prime have equivalent residue
    -- fields over `κ(p)`.
    simpa [Qfiber] using
      primesOverFiber_residueTrdeg_toNat_eq
        (p := p) (Qover := Qover)
  have hQfiber_q_trdeg :
      Cardinal.toNat (Algebra.trdeg p.ResidueField Qfiber.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := by
    -- Chain the fiber comparison with the quasi-finite presentation and target localization
    -- comparisons; this is the trdeg index needed for coordinate normalization.
    exact hQfiber_Q_trdeg.trans hQ_q_trdeg
  obtain ⟨θκ, hθκ_finite, hθκ_comap⟩ :=
    exists_finite_selfAlgHom_comap_eq_tailVariablesIdeal
      (k := p.ResidueField) (n := n) Qκ
  obtain ⟨f, hf, σf, hσf, θf, hθfX⟩ :=
    existsLiftedCoordinateSelfMapAway (A := R) p n θκ
  have hθf_specializes :
      (MvPolynomial.map σf).comp θf.toRingHom =
        θκ.toRingHom.comp (MvPolynomial.map σf) := by
    -- The lifted coordinate map specializes to the finite fiber coordinate map on generators.
    exact liftedCoordinate_specializes n σf θf θκ hθfX
  obtain ⟨g, hg, hg_def⟩ := htarget_denom hf
  -- TODO: finish the remaining spreading step. The established frontier is:
  -- `θκ` is finite and has canonical fiber comap `hθκ_comap`, `θf` is a lift over `R_f`, and
  -- `hθf_specializes` identifies its fiber specialization. Directly naming the `Qκ` residue-field
  -- trdeg still triggers the old instance-search timeout, so the remaining helper should consume
  -- the canonical-index normal form without asking Lean to synthesize that algebra instance again.
  sorry

/-- Helper for Chap10 Lemma 10 125 3: a quasi-finite polynomial presentation can be shrunk and
changed by fiber coordinates so that the localized prime contracts to the base prime plus the
expected tail-coordinate ideal. -/
private theorem existsCoordinateNormalizedLocalizedPresentation
    (q : PrimeSpectrum S) (n : ℕ) (g₀ : S) (hg₀ : g₀ ∉ q.asIdeal)
    (π₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g₀) (hπ₀ : π₀.QuasiFinite) :
    ∃ f : R, f ∉ q.asIdeal.under R ∧
      ∃ g : S, g ∉ q.asIdeal ∧
        ∃ φ : MvPolynomial (Fin n) (Localization.Away f) →+* Localization.Away g,
          φ.QuasiFinite ∧
            Ideal.comap φ (Ideal.map (algebraMap S (Localization.Away g)) q.asIdeal) =
                Ideal.map
                  (algebraMap R (MvPolynomial (Fin n) (Localization.Away f)))
                  (q.asIdeal.under R) ⊔
                tailVariablesIdeal (Localization.Away f) n
                  (Cardinal.toNat
                    (Algebra.trdeg (q.asIdeal.under R).ResidueField
                      q.asIdeal.ResidueField)) := by
  -- Route correction: split off the executable contraction/lies-over setup before invoking the
  -- still-missing spreading step.
  let Q : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.comap π₀.toRingHom
      (Ideal.map (algebraMap S (Localization.Away g₀)) q.asIdeal)
  have hQ :=
    contractedPresentationPrime_liesOver_under
      (q := q) (n := n) (g₀ := g₀) hg₀ π₀
  exact
    existsSpreadCoordinateNormalizedPresentationFromContraction
      q n g₀ hg₀ π₀ hπ₀ Q rfl hQ.1 hQ.2

/-- Lemma 10.125.3: let `R → S` be a finite type ring map, let `q : Spec(S)`, and assume
`relativeDimensionAt R S q = n`. Then after inverting some `f ∉ q ∩ R` and some `g ∉ q`, there
exists a quasi-finite ring map from the polynomial ring
`(Localization.Away f)[x₁, …, xₙ]` to `Localization.Away g` whose inverse image of the localized
prime `qS_g` is exactly the ideal generated by the extension of `q ∩ R` together with the tail
variables `x_{r+1}, …, xₙ`, where
`r = trdeg_{κ(q ∩ R)} κ(q)`. -/
@[stacks 0520]
theorem exists_quasiFinite_localizedPolynomial_ringHom_comap_eq_localizedPrimeAndTailIdeal
    (q : PrimeSpectrum S) (n : ℕ)
    (hdim : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ f : R, f ∉ q.asIdeal.under R ∧
      ∃ g : S, g ∉ q.asIdeal ∧
        ∃ φ : MvPolynomial (Fin n) (Localization.Away f) →+* Localization.Away g,
          φ.QuasiFinite ∧
            Ideal.comap φ (Ideal.map (algebraMap S (Localization.Away g)) q.asIdeal) =
                Ideal.map
                  (algebraMap R (MvPolynomial (Fin n) (Localization.Away f)))
                  (q.asIdeal.under R) ⊔
                tailVariablesIdeal (Localization.Away f) n
                  (Cardinal.toNat
                    (Algebra.trdeg (q.asIdeal.under R).ResidueField
                      q.asIdeal.ResidueField)) := by
  -- First use Lemma 10.125.2 to get a quasi-finite polynomial presentation after shrinking around
  -- `q`.
  obtain ⟨g₀, hg₀, π₀, hπ₀⟩ :=
    exists_quasiFinite_polynomial_localizationAway_of_relativeDimensionAt_eq
      (R := R) (S := S) n q hdim
  -- The remaining geometric step is the coordinate-normalization and denominator-clearing helper.
  exact existsCoordinateNormalizedLocalizedPresentation q n g₀ hg₀ π₀ hπ₀

end
