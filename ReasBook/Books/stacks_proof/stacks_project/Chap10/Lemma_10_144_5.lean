import Mathlib
import StacksProject_2024.Chap10.Lemma_10_136_14

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsStandardEtale R S]

/- Domain-style sampling:
* primary domain: standard étale morphisms and prime lifting after finite flat base change in
  commutative algebra;
* sampled declarations:
  `IsStandardEtale`,
  `StandardEtalePresentation`,
  `Ideal.primesOver`,
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`,
  `Polynomial.exists_syntomic_finiteFree_faithfullyFlat_split_extension_of_monic`,
  `Algebra.HasGoingDown.of_flat`;
* best owner abstraction:
  the source algebra is controlled by the canonical owner `IsStandardEtale R S`, while the
  auxiliary extension should expose the existing owner predicates `Module.Finite`,
  `Algebra.FinitePresentation`, and `(algebraMap R S').FaithfullyFlat` directly, while primes over
  `p` should be indexed by the canonical owner fibers `p.asIdeal.primesOver _` instead of by raw
  spectrum points plus equalities;
* source/core/bridge triage:
  this lemma is `source-facing`; the extra localized prime-lifting clause is genuine new source
  content, while finiteness / finite presentation / faithful flatness are derived owner data on
  the chosen extension `S'`;
* primitive-vs-derived split:
  primitive existential data are only the extension ring `S'` and its `R`-algebra structure;
  the canonical algebraic properties above should remain separate owner witnesses, not primitive
  public fields of a new packaged predicate.
-/

-- Proof sketch: choose a standard étale presentation `S ≃ R[x, 1 / g]/(f)` with `f` monic.
-- Apply Lemma `10.136.14` to `f` to obtain a finite free faithfully flat extension `R → S'`
-- splitting `f`; this gives finite presentation and the canonical faithfully flat owner, from
-- which spectrum-surjectivity is derived by
-- `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`. For primes
-- `q ⊂ S` and `q' ⊂ S'` in the owner fibers over the same `p ⊂ R`, pick a root of the split polynomial over
-- `κ(q')` that lies on the irreducible factor corresponding to `q` and does not vanish on the
-- chosen denominator, yielding `g' ∉ q'` and an `R`-algebra map `S → S'_{g'}` whose inverse image
-- of the localized prime over `q'` is `q`.
omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: a standard étale algebra admits a finite, finitely
presented, faithfully flat extension after a single universe lift of the splitting extension from
Lemma `10.136.14`. -/
private lemma exists_finitePresentationFaithfullyFlat_split_extension
    (P : StandardEtalePresentation R S) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat), (P.f.map (algebraMap R S')).Splits := by
  -- The polynomial from the standard étale presentation becomes split after the finite free
  -- faithfully flat syntomic extension from Lemma `10.136.14`.
  obtain ⟨A, hAcomm, hAalg, hSyn, _hFree, hFinite, hff, hsplit⟩ :=
    Polynomial.exists_syntomic_finiteFree_faithfullyFlat_split_extension_of_monic P.f P.P.monic_f
  let A' : Type (max u v) := ULift.{v} A
  letI : CommRing A := hAcomm
  letI : Algebra R A := hAalg
  letI : CommRing A' := inferInstance
  letI : Algebra R A' := inferInstance
  have hmap :
      (ULift.ringEquiv.symm.toRingHom : A →+* A').comp (algebraMap R A) =
        algebraMap R A' := by
    ext r
    rfl
  have hfpRing : (algebraMap R A).FinitePresentation := RingHom.Syntomic.finitePresentation hSyn
  letI : Module.Finite R A' := inferInstance
  have hfpA'Ring : (algebraMap R A').FinitePresentation := by
    rw [← hmap]
    exact RingHom.FinitePresentation.comp
      (RingHom.FinitePresentation.of_bijective ULift.ringEquiv.symm.bijective) hfpRing
  have hfpA' : Algebra.FinitePresentation R A' :=
    RingHom.finitePresentation_algebraMap.mp hfpA'Ring
  letI : Module.FaithfullyFlat R A' := by
    letI : Module.FaithfullyFlat R A := (RingHom.faithfullyFlat_algebraMap_iff).mp hff
    exact Module.FaithfullyFlat.of_linearEquiv (R := R) (M := A)
      (ULift.moduleEquiv (R := R) (M := A))
  have hffA' : (algebraMap R A').FaithfullyFlat :=
    (RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance
  have hsplitA' : (P.f.map (algebraMap R A')).Splits := by
    -- The splitting polynomial is transported through the universe-lift equivalence.
    have hsplitMap :
        (P.f.map ((ULift.ringEquiv.symm.toRingHom : A →+* A').comp
          (algebraMap R A))).Splits := by
      simpa [Polynomial.map_map] using hsplit.map (ULift.ringEquiv.symm.toRingHom : A →+* A')
    simpa [hmap] using hsplitMap
  -- The lifted witness now has the target universe while preserving the module-theoretic owners.
  exact ⟨A', inferInstance, inferInstance, inferInstance, hfpA', hffA', hsplitA'⟩

/-- Helper for Chap10 Lemma 10 144 5: over a field extension where `f` splits, an irreducible
factor `f1` of `f` that does not divide `g` contributes a root of `f` on which `g` stays
nonzero. -/
private lemma existsResidueRootMatchingFactorAvoidingDenominator
    {k : Type*} [Field k] {L : Type*} [Field L] [Algebra k L]
    {f g f1 : k[X]} (hfmonic : f.Monic) (hf1monic : f1.Monic)
    (hf1_irr : Irreducible f1) (hf1_dvd : f1 ∣ f) (hg_not_dvd : ¬ f1 ∣ g)
    (hf_split : (f.map (algebraMap k L)).Splits) :
    ∃ α : L, aeval α f1 = 0 ∧ aeval α f = 0 ∧ aeval α g ≠ 0 := by
  -- Proof comment: first transfer splitness from `f` to the chosen irreducible factor `f1`.
  have hf_map_ne_zero : f.map (algebraMap k L) ≠ 0 := (hfmonic.map (algebraMap k L)).ne_zero
  have hf1_split : (f1.map (algebraMap k L)).Splits := by
    refine Polynomial.Splits.of_dvd hf_split hf_map_ne_zero ?_
    obtain ⟨h, rfl⟩ := hf1_dvd
    exact ⟨h.map (algebraMap k L), by simp [Polynomial.map_mul]⟩
  -- Proof comment: the nonconstant monic factor `f1` therefore has a root in the splitting field.
  have hf1_degree_ne_zero : (f1.map (algebraMap k L)).degree ≠ 0 := by
    have hdeg_map :
        (f1.map (algebraMap k L)).degree = f1.degree :=
      Polynomial.degree_map_eq_of_leadingCoeff_ne_zero _ (by
        simpa [hf1monic.leadingCoeff] using (one_ne_zero : (1 : L) ≠ 0))
    have hdeg_pos : 0 < f1.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp
        (hf1monic.natDegree_pos_of_not_isUnit hf1_irr.1)
    rw [hdeg_map]
    exact ne_of_gt hdeg_pos
  obtain ⟨α, hα⟩ := Polynomial.Splits.exists_eval_eq_zero hf1_split hf1_degree_ne_zero
  have hαf1 : aeval α f1 = 0 := by
    simpa [Polynomial.aeval_def] using hα
  refine ⟨α, hαf1, ?_, ?_⟩
  · -- Proof comment: divisibility `f1 ∣ f` pushes the chosen root from `f1` to `f`.
    obtain ⟨h, rfl⟩ := hf1_dvd
    simp [hαf1]
  · intro hgα
    -- Proof comment: if `g(α)=0`, then the minimal polynomial of `α` equals `f1`, forcing the
    -- forbidden divisibility `f1 ∣ g`.
    have hα_integral : IsIntegral k α := ⟨f1, hf1monic, hαf1⟩
    have hminpoly_dvd_f1 : minpoly k α ∣ f1 := minpoly.dvd k α hαf1
    have hminpoly_eq_f1 : minpoly k α = f1 := by
      apply Polynomial.eq_of_monic_of_associated (minpoly.monic hα_integral) hf1monic
      exact associated_of_dvd_dvd hminpoly_dvd_f1
        ((minpoly.irreducible hα_integral).dvd_symm hf1_irr hminpoly_dvd_f1)
    have hminpoly_dvd_g : minpoly k α ∣ g := minpoly.dvd k α hgα
    exact hg_not_dvd (by simpa [hminpoly_eq_f1] using hminpoly_dvd_g)

/-- Helper for Chap10 Lemma 10 144 5: a residue-field root of a monic polynomial that already
splits in `A` lifts to an actual root in `A`. -/
private lemma existsSplitRootAboveResidueRoot
    {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {L : Type*} [Field L] [Algebra k L] (ρ : A →ₐ[k] L)
    {f : k[X]} (hfmonic : f.Monic) (hf_split : (f.map (algebraMap k A)).Splits)
    {α : L} (hα : aeval α f = 0) :
    ∃ a : A, aeval a f = 0 ∧ ρ a = α := by
  classical
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf_split
  -- Proof comment: map the split factorization to `L` and evaluate it at the chosen residue root.
  have hα_eval : eval α ((f.map (algebraMap k A)).map (ρ : A →+* L)) = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.map_map, ρ.comp_algebraMap] using hα
  have hprod_zero : (m.map (fun a ↦ α + ρ a)).prod = 0 := by
    rw [hm, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, Polynomial.map_multiset_prod,
      eval_multiset_prod, (hfmonic.map (algebraMap k A)).leadingCoeff, map_one, one_mul] at hα_eval
    simpa using hα_eval
  have hzero : 0 ∈ m.map (fun a ↦ α + ρ a) := by
    rw [← Multiset.prod_eq_zero_iff]
    exact hprod_zero
  rw [Multiset.mem_map] at hzero
  obtain ⟨a, ha, ha_zero⟩ := hzero
  refine ⟨-a, ?_, ?_⟩
  · -- Proof comment: the vanishing linear factor `X + C a` gives an actual root `-a` of `f`.
    have hroot_eval : eval (-a) (f.map (algebraMap k A)) = 0 := by
      rw [hm, eval_mul, eval_C, (hfmonic.map (algebraMap k A)).leadingCoeff, one_mul,
        eval_multiset_prod]
      refine Multiset.prod_eq_zero ?_
      have hmem :
          eval (-a) (X + C a) ∈
            Multiset.map (eval (-a)) (Multiset.map (fun x ↦ X + C x) m) :=
        Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ ha)
      simpa using hmem
    simpa [Polynomial.aeval_def] using hroot_eval
  · -- Proof comment: the same vanishing factor identifies the image of `-a` with the chosen root.
    calc
      ρ (-a) = -ρ a := by simp
      _ = α := (eq_neg_of_add_eq_zero_left ha_zero).symm

/-- Helper for Chap10 Lemma 10 144 5: a residue-field root of a monic polynomial over an
arbitrary base ring lifts to an actual root in any algebra where the polynomial splits. -/
private lemma existsSplitRootAboveResidueRoot_of_splits
    {A : Type*} [CommRing A] [Algebra R A]
    {L : Type*} [Field L] [Algebra R L] (ρ : A →ₐ[R] L)
    {f : R[X]} (hfmonic : f.Monic) (hf_split : (f.map (algebraMap R A)).Splits)
    {α : L} (hα : aeval α f = 0) :
    ∃ a : A, aeval a f = 0 ∧ ρ a = α := by
  classical
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf_split
  -- Proof comment: map the split linear-factor decomposition to the residue field and evaluate
  -- it at the given root.
  have hα_eval : eval α ((f.map (algebraMap R A)).map (ρ : A →+* L)) = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.map_map, ρ.comp_algebraMap] using hα
  have hprod_zero : (m.map (fun a ↦ α + ρ a)).prod = 0 := by
    rw [hm, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, Polynomial.map_multiset_prod,
      eval_multiset_prod, (hfmonic.map (algebraMap R A)).leadingCoeff, map_one, one_mul] at hα_eval
    simpa using hα_eval
  have hzero : 0 ∈ m.map (fun a ↦ α + ρ a) := by
    rw [← Multiset.prod_eq_zero_iff]
    exact hprod_zero
  rw [Multiset.mem_map] at hzero
  obtain ⟨a, ha, ha_zero⟩ := hzero
  refine ⟨-a, ?_, ?_⟩
  · -- Proof comment: the zero linear factor supplies the required root in the splitting algebra.
    have hroot_eval : eval (-a) (f.map (algebraMap R A)) = 0 := by
      rw [hm, eval_mul, eval_C, (hfmonic.map (algebraMap R A)).leadingCoeff, one_mul,
        eval_multiset_prod]
      refine Multiset.prod_eq_zero ?_
      have hmem :
          eval (-a) (X + C a) ∈
            Multiset.map (eval (-a)) (Multiset.map (fun x ↦ X + C x) m) :=
        Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ ha)
      simpa using hmem
    simpa [Polynomial.aeval_def] using hroot_eval
  · -- Proof comment: the same factor records that the lifted root maps to the chosen residue root.
    calc
      ρ (-a) = -ρ a := by simp
      _ = α := (eq_neg_of_add_eq_zero_left ha_zero).symm

/-- Helper for Chap10 Lemma 10 144 5: after choosing the irreducible fiber factor attached to a
prime of the standard-étale fiber, one can lift a residue-field root back to the split extension
ring without making the denominator vanish. -/
private lemma existsSplitRootAvoidingDenominator
    {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {L : Type*} [Field L] [Algebra k L] (ρ : A →ₐ[k] L)
    {f g f1 : k[X]} (hfmonic : f.Monic) (hf1monic : f1.Monic)
    (hf1_irr : Irreducible f1) (hf1_dvd : f1 ∣ f) (hg_not_dvd : ¬ f1 ∣ g)
    (hf_split : (f.map (algebraMap k A)).Splits) :
    ∃ a : A, aeval a f = 0 ∧ aeval (ρ a) f1 = 0 ∧ aeval (ρ a) g ≠ 0 := by
  -- Proof comment: first choose the desired root in the residue field, then lift that root back
  -- to the split extension ring via the root-set image theorem.
  have hf_split_L : (f.map (algebraMap k L)).Splits := by
    simpa [Polynomial.map_map, ρ.comp_algebraMap] using hf_split.map (ρ : A →+* L)
  obtain ⟨α, hαf1, hαf, hαg⟩ :=
    existsResidueRootMatchingFactorAvoidingDenominator
      (hfmonic := hfmonic) (hf1monic := hf1monic) hf1_irr hf1_dvd hg_not_dvd hf_split_L
  obtain ⟨a, haf, hρa⟩ :=
    existsSplitRootAboveResidueRoot (ρ := ρ) (hfmonic := hfmonic) hf_split hαf
  refine ⟨a, haf, ?_, ?_⟩
  · simpa [hρa] using hαf1
  · simpa [hρa] using hαg

/-- Helper for Chap10 Lemma 10 144 5: if `α` is a root of `f`, then evaluation at `α` vanishes
on the principal ideal generated by `f`. -/
private lemma aeval_eq_zero_of_mem_span_singleton
    {k : Type*} [CommRing k] {L : Type*} [CommRing L] [Algebra k L]
    {f p : Polynomial k} {α : L} (hf : aeval α f = 0)
    (hp : p ∈ Ideal.span ({f} : Set (Polynomial k))) :
    aeval α p = 0 := by
  -- Proof comment: membership in a principal ideal rewrites `p` as a multiple of `f`, and
  -- evaluation preserves multiplication.
  rw [Ideal.mem_span_singleton] at hp
  obtain ⟨q, rfl⟩ := hp
  simp [hf]

/-- Helper for Chap10 Lemma 10 144 5: divisibility transports a chosen evaluation root from the
divisor to the dividend. -/
private lemma aeval_eq_zero_of_dvd_of_aeval_eq_zero
    {k : Type*} [CommRing k] {L : Type*} [CommRing L] [Algebra k L]
    {f g : Polynomial k} {α : L} (hfg : f ∣ g) (hf : aeval α f = 0) :
    aeval α g = 0 := by
  -- Proof comment: once `g = f * q`, the vanishing of `f(α)` kills the product `g(α)`.
  obtain ⟨q, rfl⟩ := hfg
  simp [hf]

/-- Helper for Chap10 Lemma 10 144 5: evaluation at a chosen root of `f` descends to the quotient
`k[X] ⧸ (f)`. -/
private noncomputable def quotientAeval
    {k : Type*} [CommRing k] {L : Type*} [CommRing L] [Algebra k L]
    (f : Polynomial k) (α : L) (hf : aeval α f = 0) :
    (Polynomial k) ⧸ Ideal.span ({f} : Set (Polynomial k)) →ₐ[k] L :=
  Ideal.Quotient.liftₐ (Ideal.span ({f} : Set (Polynomial k))) (Polynomial.aeval α)
    (fun _ hp ↦ aeval_eq_zero_of_mem_span_singleton (α := α) hf hp)

/-- Helper for Chap10 Lemma 10 144 5: over a field, evaluating at a root of a monic irreducible
polynomial has exactly the principal ideal generated by that polynomial as kernel. -/
private lemma kerAeval_eq_span_of_irreducible_root
    {k : Type*} [Field k] {L : Type*} [Field L] [Algebra k L]
    {f1 : k[X]} (hf1monic : f1.Monic) (hf1_irr : Irreducible f1)
    {α : L} (hα : aeval α f1 = 0) :
    RingHom.ker (Polynomial.aeval α).toRingHom = Ideal.span ({f1} : Set k[X]) := by
  -- Proof comment: compare `f1` with the minimal polynomial of `α`; both are monic irreducibles
  -- vanishing at `α`, so they coincide.
  have hα_integral : IsIntegral k α := ⟨f1, hf1monic, hα⟩
  have hminpoly_dvd_f1 : minpoly k α ∣ f1 := minpoly.dvd k α hα
  have hminpoly_eq_f1 : minpoly k α = f1 := by
    apply Polynomial.eq_of_monic_of_associated (minpoly.monic hα_integral) hf1monic
    exact associated_of_dvd_dvd hminpoly_dvd_f1
      ((minpoly.irreducible hα_integral).dvd_symm hf1_irr hminpoly_dvd_f1)
  change RingHom.ker (Polynomial.aeval α).toRingHom = k[X] ∙ f1
  rw [← hminpoly_eq_f1]
  exact minpoly.ker_aeval_eq_span_minpoly (A := k) (x := α)

/-- Helper for Chap10 Lemma 10 144 5: after descending evaluation to `k[X] ⧸ (f)`, the kernel is
the image of the irreducible factor ideal cutting out the chosen residue root. -/
private lemma kerEvalQuotient_eq_factorPrime
    {k : Type*} [Field k] {L : Type*} [Field L] [Algebra k L]
    {f f1 : k[X]} {α : L} (hf : aeval α f = 0)
    (hf1monic : f1.Monic) (hf1_irr : Irreducible f1) (hα : aeval α f1 = 0) :
    RingHom.ker (quotientAeval f α hf).toRingHom =
      Ideal.map (Ideal.Quotient.mk (Ideal.span ({f} : Set k[X]))) (Ideal.span ({f1} : Set k[X])) := by
  -- Proof comment: quotienting by `(f)` replaces the original evaluation kernel by its image in
  -- the quotient, and the previous lemma identifies that original kernel as `(f1)`.
  change RingHom.ker
      (Ideal.Quotient.lift (Ideal.span ({f} : Set k[X])) (Polynomial.aeval α).toRingHom
        (fun p hp ↦ aeval_eq_zero_of_mem_span_singleton (α := α) hf hp)) =
    _
  rw [Ideal.ker_quotient_lift]
  rw [kerAeval_eq_span_of_irreducible_root (α := α) hf1monic hf1_irr hα]

/-- Helper for Chap10 Lemma 10 144 5: powers of an element outside a prime ideal are disjoint
from that prime. -/
private lemma powers_disjoint_prime_of_not_mem
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    Disjoint (Submonoid.powers x : Set A) I := by
  -- Proof comment: any positive power in the prime forces the element itself into the prime.
  rw [Set.disjoint_left]
  rintro _ ⟨m, rfl⟩ hm
  exact hx ((inferInstance : I.IsPrime).mem_of_pow_mem m hm)

/-- Helper for Chap10 Lemma 10 144 5: extending a prime ideal to an away localization remains
prime when the inverted element is not in the prime. -/
private lemma localizedPrimeMap_isPrime
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    (Ideal.map (algebraMap A (Localization.Away x)) I).IsPrime := by
  -- Proof comment: exactness of localization applies after recording disjointness from powers.
  exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x)
    (Localization.Away x) I inferInstance (powers_disjoint_prime_of_not_mem I hx)

/-- Helper for Chap10 Lemma 10 144 5: the localized extension of a prime contracts back to the
original prime when the localized element avoids it. -/
private lemma localizedPrime_comap_map_eq
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    Ideal.comap (algebraMap A (Localization.Away x))
        (Ideal.map (algebraMap A (Localization.Away x)) I) =
      I := by
  -- Proof comment: this is the localization contraction identity for a prime disjoint from the
  -- inverted powers; it will be the final kernel/comap bridge in the split-presentation proof.
  exact IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers x)
    (Localization.Away x) inferInstance (powers_disjoint_prime_of_not_mem I hx)

/-- Helper for Chap10 Lemma 10 144 5: when the inverted element avoids a prime, the residue-field
map from the away localization has kernel exactly the localized prime. -/
private lemma existsAwayResidueMap_ker_eq_map_prime
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    ∃ ρ : Localization.Away x →ₐ[R] I.ResidueField,
      ρ.comp (IsScalarTower.toAlgHom R A (Localization.Away x)) =
        IsScalarTower.toAlgHom R A I.ResidueField ∧
      RingHom.ker ρ.toRingHom = Ideal.map (algebraMap A (Localization.Away x)) I := by
  -- Proof comment: because `x` is not in `I`, its residue is nonzero and hence invertible in
  -- the residue field, so the universal property of the away localization gives the map.
  let L := I.ResidueField
  have hxunit : IsUnit (algebraMap A L x) := by
    have hx_ne : algebraMap A L x ≠ 0 := by
      rw [ne_eq, Ideal.algebraMap_residueField_eq_zero]
      exact hx
    exact isUnit_iff_ne_zero.mpr hx_ne
  let ρRing : Localization.Away x →+* L :=
    IsLocalization.Away.lift x (S := Localization.Away x) (g := algebraMap A L) hxunit
  let ρ : Localization.Away x →ₐ[R] L :=
    { ρRing with
      commutes' := by
        intro r
        change ρRing (algebraMap A (Localization.Away x) (algebraMap R A r)) =
          algebraMap R L r
        simp [ρRing, IsScalarTower.algebraMap_apply R A L] }
  refine ⟨ρ, ?_, ?_⟩
  · -- Proof comment: on elements coming from `A`, the lifted map is the usual residue map.
    ext a
    change ρRing (algebraMap A (Localization.Away x) a) = algebraMap A L a
    simp [ρRing]
  · -- Proof comment: compare membership in the localized ideal with vanishing under `ρ` by
    -- clearing a power of the inverted element.
    ext z
    constructor
    · intro hz
      obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers x) z
      rw [RingHom.mem_ker] at hz
      change ρ (IsLocalization.mk' (Localization.Away x) a s) = 0 at hz
      rw [IsLocalization.mk'_mem_map_algebraMap_iff]
      refine ⟨1, Submonoid.one_mem _, ?_⟩
      have hazero : algebraMap A L a = 0 := by
        have hprod :
            ρ (algebraMap A (Localization.Away x) s.1 *
                IsLocalization.mk' (Localization.Away x) a s) = 0 := by
          rw [map_mul, hz, mul_zero]
        rw [IsLocalization.mk'_spec'] at hprod
        simpa [ρ, ρRing] using hprod
      simpa using Ideal.algebraMap_residueField_eq_zero.mp hazero
    · intro hz
      rw [RingHom.mem_ker]
      change ρ z = 0
      rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers x) (Localization.Away x)] at hz
      obtain ⟨y, hy⟩ := hz
      let a : A := y.1.1
      let s : Submonoid.powers x := y.2
      have haI : a ∈ I := y.1.2
      have hmul : ρ z * ρ (algebraMap A (Localization.Away x) s.1) = 0 := by
        have hcongr := congrArg ρ hy
        rw [map_mul] at hcongr
        have hazero₀ : algebraMap A L a = 0 := Ideal.algebraMap_residueField_eq_zero.mpr haI
        have hazero : ρ (algebraMap A (Localization.Away x) a) = 0 := by
          simpa [ρ, ρRing, a] using hazero₀
        simpa [a, s] using hcongr.trans hazero
      have hsunit : IsUnit (ρ (algebraMap A (Localization.Away x) s.1)) :=
        IsUnit.map ρ (IsLocalization.map_units (Localization.Away x) s)
      obtain ⟨u, hu⟩ := hsunit
      rw [← hu] at hmul
      exact (mul_eq_zero.mp hmul).resolve_right u.ne_zero

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: polynomial values in the standard-etale coordinate map
into the residue-field subfield generated by that coordinate. -/
private lemma standardEtalePresentation_residuePolynomial_mem_adjoin_x
    (P : StandardEtalePresentation R S) (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S)
    (a : R[X]) :
    algebraMap S q.1.ResidueField (aeval P.x a) ∈
      IntermediateField.adjoin p.asIdeal.ResidueField
        ({algebraMap S q.1.ResidueField P.x} : Set q.1.ResidueField) := by
  -- Proof comment: realize polynomial values as the range of evaluation in the algebra adjoin,
  -- then compare the two coefficient maps through the residue-field scalar tower.
  let ξ : q.1.ResidueField := algebraMap S q.1.ResidueField P.x
  let K : IntermediateField p.asIdeal.ResidueField q.1.ResidueField :=
    IntermediateField.adjoin p.asIdeal.ResidueField ({ξ} : Set q.1.ResidueField)
  have hpoly : aeval ξ (a.map (algebraMap R p.asIdeal.ResidueField)) ∈ K := by
    have hsub :
        Algebra.adjoin p.asIdeal.ResidueField ({ξ} : Set q.1.ResidueField) ≤
          K.toSubalgebra :=
      IntermediateField.algebra_adjoin_le_adjoin (F := p.asIdeal.ResidueField)
        (E := q.1.ResidueField) ({ξ} : Set q.1.ResidueField)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hsub
    exact hsub ⟨a.map (algebraMap R p.asIdeal.ResidueField), rfl⟩
  have heval :
      aeval ξ (a.map (algebraMap R p.asIdeal.ResidueField)) =
        algebraMap S q.1.ResidueField (aeval P.x a) := by
    rw [Polynomial.aeval_map_algebraMap]
    simpa [ξ] using
      (aeval_algHom_apply (IsScalarTower.toAlgHom R S q.1.ResidueField) P.x a)
  simpa [K, ξ, heval] using hpoly

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: every residue image from the standard-etale algebra lies in
the subfield generated by the standard-etale coordinate. -/
private lemma standardEtalePresentation_residueImage_mem_adjoin_x
    (P : StandardEtalePresentation R S) (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S)
    (s : S) :
    algebraMap S q.1.ResidueField s ∈
      IntermediateField.adjoin p.asIdeal.ResidueField
        ({algebraMap S q.1.ResidueField P.x} : Set q.1.ResidueField) := by
  -- Proof comment: clear denominators in `S` using the standard-etale presentation, then invert
  -- the nonzero residue of `g(P.x)` inside the generated intermediate field.
  let ξ : q.1.ResidueField := algebraMap S q.1.ResidueField P.x
  let K : IntermediateField p.asIdeal.ResidueField q.1.ResidueField :=
    IntermediateField.adjoin p.asIdeal.ResidueField ({ξ} : Set q.1.ResidueField)
  obtain ⟨a, n, ha⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
  let d : q.1.ResidueField := algebraMap S q.1.ResidueField (aeval P.x P.g)
  have hnum : algebraMap S q.1.ResidueField (aeval P.x a) ∈ K := by
    simpa [K, ξ] using standardEtalePresentation_residuePolynomial_mem_adjoin_x P p q a
  have hden : d ∈ K := by
    simpa [K, ξ, d] using standardEtalePresentation_residuePolynomial_mem_adjoin_x P p q P.g
  have hd_ne : d ≠ 0 := by
    have hunit : IsUnit d := by
      simpa [d] using P.hasMap.2.map (algebraMap S q.1.ResidueField)
    exact hunit.ne_zero
  have hpow_ne : d ^ n ≠ 0 := pow_ne_zero n hd_ne
  have heq :
      algebraMap S q.1.ResidueField s * d ^ n =
        algebraMap S q.1.ResidueField (aeval P.x a) := by
    simpa [d, map_mul, map_pow] using congrArg (algebraMap S q.1.ResidueField) ha
  have hquot : algebraMap S q.1.ResidueField (aeval P.x a) * (d ^ n)⁻¹ ∈ K :=
    K.mul_mem hnum (K.inv_mem (pow_mem hden n))
  have hy_eq :
      algebraMap S q.1.ResidueField s =
        algebraMap S q.1.ResidueField (aeval P.x a) * (d ^ n)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hpow_ne]
    exact heq
  simpa [K, ξ, hy_eq] using hquot

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: the residue field of a prime in a standard-etale
presentation is generated over the base residue field by the standard-etale coordinate. -/
private lemma standardEtalePresentation_residueField_adjoin_x_eq_top
    (P : StandardEtalePresentation R S) (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) :
    IntermediateField.adjoin p.asIdeal.ResidueField
        ({algebraMap S q.1.ResidueField P.x} : Set q.1.ResidueField) = ⊤ := by
  -- Proof comment: write an arbitrary residue-field element as a fraction from `S ⧸ q`; both
  -- numerator and denominator come from `S`, hence lie in the generated intermediate field.
  let ξ : q.1.ResidueField := algebraMap S q.1.ResidueField P.x
  let K : IntermediateField p.asIdeal.ResidueField q.1.ResidueField :=
    IntermediateField.adjoin p.asIdeal.ResidueField ({ξ} : Set q.1.ResidueField)
  change K = ⊤
  refine le_antisymm le_top ?_
  intro y _hy
  obtain ⟨z, hz⟩ := IsLocalization.surj (nonZeroDivisors (S ⧸ q.1)) y
  rcases z with ⟨num, den⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective num
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective den.1
  have hnumK : algebraMap (S ⧸ q.1) q.1.ResidueField (Ideal.Quotient.mk q.1 s) ∈ K := by
    simpa [K, ξ] using standardEtalePresentation_residueImage_mem_adjoin_x P p q s
  have hdenK : algebraMap (S ⧸ q.1) q.1.ResidueField den.1 ∈ K := by
    rw [← ht]
    simpa [K, ξ] using standardEtalePresentation_residueImage_mem_adjoin_x P p q t
  have hden_ne : algebraMap (S ⧸ q.1) q.1.ResidueField den.1 ≠ 0 := by
    have hunit : IsUnit (algebraMap (S ⧸ q.1) q.1.ResidueField den.1) :=
      IsLocalization.map_units q.1.ResidueField den
    exact hunit.ne_zero
  have hquot :
      algebraMap (S ⧸ q.1) q.1.ResidueField (Ideal.Quotient.mk q.1 s) *
          (algebraMap (S ⧸ q.1) q.1.ResidueField den.1)⁻¹ ∈ K :=
    K.mul_mem hnumK (K.inv_mem hdenK)
  have hy_eq :
      y =
        algebraMap (S ⧸ q.1) q.1.ResidueField (Ideal.Quotient.mk q.1 s) *
          (algebraMap (S ⧸ q.1) q.1.ResidueField den.1)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hden_ne]
    simpa using hz
  simpa [K, ξ, hy_eq] using hquot

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: the standard-etale coordinate is integral over the base
residue field. -/
private lemma standardEtalePresentation_residue_x_isIntegral
    (P : StandardEtalePresentation R S) (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) :
    IsIntegral p.asIdeal.ResidueField (algebraMap S q.1.ResidueField P.x) := by
  -- Proof comment: map the defining equation `f(P.x)=0` to the residue field and view it over
  -- `κ(p)`; monicity is preserved by the coefficient map.
  let ξ : q.1.ResidueField := algebraMap S q.1.ResidueField P.x
  refine ⟨P.f.map (algebraMap R p.asIdeal.ResidueField), P.P.monic_f.map _, ?_⟩
  have hzero : algebraMap S q.1.ResidueField (aeval P.x P.f) = 0 := by
    rw [P.hasMap.1, map_zero]
  have heval :
      aeval ξ (P.f.map (algebraMap R p.asIdeal.ResidueField)) =
        algebraMap S q.1.ResidueField (aeval P.x P.f) := by
    rw [Polynomial.aeval_map_algebraMap]
    simpa [ξ] using
      (aeval_algHom_apply (IsScalarTower.toAlgHom R S q.1.ResidueField) P.x P.f)
  exact heval.trans hzero

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: evaluation at the residue coordinate surjects onto the
whole residue field. -/
private lemma standardEtalePresentation_aeval_residue_x_surjective
    (P : StandardEtalePresentation R S) (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) :
    Function.Surjective (Polynomial.aeval (algebraMap S q.1.ResidueField P.x) :
      p.asIdeal.ResidueField[X] →ₐ[p.asIdeal.ResidueField] q.1.ResidueField) := by
  -- Proof comment: convert the field-generation result to polynomial-range generation using
  -- algebraicity of the residue coordinate.
  let ξ : q.1.ResidueField := algebraMap S q.1.ResidueField P.x
  have hξ_alg : IsAlgebraic p.asIdeal.ResidueField ξ :=
    (standardEtalePresentation_residue_x_isIntegral P p q).isAlgebraic
  rw [← AlgHom.range_eq_top]
  rw [← Algebra.adjoin_singleton_eq_range_aeval]
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hξ_alg]
  rw [standardEtalePresentation_residueField_adjoin_x_eq_top P p q]
  rfl

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: the minimal polynomial of the residue coordinate is the
irreducible factor of `f` that avoids the denominator `g`. -/
private lemma standardEtalePresentation_residue_minpoly_data
    (P : StandardEtalePresentation R S) (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) :
    let k := p.asIdeal.ResidueField
    let ξ : q.1.ResidueField := algebraMap S q.1.ResidueField P.x
    let f1 := minpoly k ξ
    f1.Monic ∧ Irreducible f1 ∧ f1 ∣ P.f.map (algebraMap R k) ∧
      ¬ f1 ∣ P.g.map (algebraMap R k) := by
  -- Proof comment: package the monic irreducible minimal polynomial, its divisibility in `f`,
  -- and the denominator-avoidance contradiction from the unit `g(P.x)`.
  dsimp only
  let ξ : q.1.ResidueField := algebraMap S q.1.ResidueField P.x
  have hξ_int : IsIntegral p.asIdeal.ResidueField ξ :=
    standardEtalePresentation_residue_x_isIntegral P p q
  have hf_eval : aeval ξ (P.f.map (algebraMap R p.asIdeal.ResidueField)) = 0 := by
    have hzero : algebraMap S q.1.ResidueField (aeval P.x P.f) = 0 := by
      rw [P.hasMap.1, map_zero]
    have heval :
        aeval ξ (P.f.map (algebraMap R p.asIdeal.ResidueField)) =
          algebraMap S q.1.ResidueField (aeval P.x P.f) := by
      rw [Polynomial.aeval_map_algebraMap]
      simpa [ξ] using
        (aeval_algHom_apply (IsScalarTower.toAlgHom R S q.1.ResidueField) P.x P.f)
    exact heval.trans hzero
  have hg_ne : aeval ξ (P.g.map (algebraMap R p.asIdeal.ResidueField)) ≠ 0 := by
    have hunit : IsUnit (algebraMap S q.1.ResidueField (aeval P.x P.g)) :=
      P.hasMap.2.map (algebraMap S q.1.ResidueField)
    have heval :
        aeval ξ (P.g.map (algebraMap R p.asIdeal.ResidueField)) =
          algebraMap S q.1.ResidueField (aeval P.x P.g) := by
      rw [Polynomial.aeval_map_algebraMap]
      simpa [ξ] using
        (aeval_algHom_apply (IsScalarTower.toAlgHom R S q.1.ResidueField) P.x P.g)
    exact fun h ↦ hunit.ne_zero (heval ▸ h)
  refine ⟨minpoly.monic hξ_int, minpoly.irreducible hξ_int, minpoly.dvd _ _ hf_eval, ?_⟩
  intro hdiv
  have hg_zero : aeval ξ (P.g.map (algebraMap R p.asIdeal.ResidueField)) = 0 := by
    rcases hdiv with ⟨h, hh⟩
    rw [hh, map_mul, minpoly.aeval, zero_mul]
  exact hg_ne hg_zero

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: two roots of the same minimal polynomial over a field
annihilate exactly the same polynomials over that field. -/
private lemma aeval_eq_zero_iff_of_aeval_minpoly_eq_zero
    {k K L : Type*} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
    {ξ : K} {α : L} (hξ : IsIntegral k ξ) (hα : aeval α (minpoly k ξ) = 0)
    (a : k[X]) :
    aeval α a = 0 ↔ aeval ξ a = 0 := by
  -- Proof comment: identify both evaluation kernels with the principal ideal generated by the
  -- same minimal polynomial, then translate membership in those kernels back to vanishing.
  have hkerα : RingHom.ker (Polynomial.aeval α).toRingHom =
      Ideal.span ({minpoly k ξ} : Set k[X]) := by
    have hα_integral : IsIntegral k α := ⟨minpoly k ξ, minpoly.monic hξ, hα⟩
    have hminpoly_dvd : minpoly k α ∣ minpoly k ξ := minpoly.dvd k α hα
    have hminpoly_eq : minpoly k α = minpoly k ξ := by
      apply Polynomial.eq_of_monic_of_associated (minpoly.monic hα_integral) (minpoly.monic hξ)
      exact associated_of_dvd_dvd hminpoly_dvd
        ((minpoly.irreducible hα_integral).dvd_symm (minpoly.irreducible hξ) hminpoly_dvd)
    change RingHom.ker (Polynomial.aeval α).toRingHom = k[X] ∙ minpoly k ξ
    rw [← hminpoly_eq]
    exact minpoly.ker_aeval_eq_span_minpoly (A := k) (x := α)
  have hkerξ : RingHom.ker (Polynomial.aeval ξ).toRingHom =
      Ideal.span ({minpoly k ξ} : Set k[X]) :=
    minpoly.ker_aeval_eq_span_minpoly (A := k) (x := ξ)
  constructor
  · intro ha
    have hmem : a ∈ RingHom.ker (Polynomial.aeval α).toRingHom := by
      simpa [RingHom.mem_ker] using ha
    rw [hkerα] at hmem
    have hmemξ : a ∈ RingHom.ker (Polynomial.aeval ξ).toRingHom := by
      rwa [hkerξ]
    simpa [RingHom.mem_ker] using hmemξ
  · intro ha
    have hmem : a ∈ RingHom.ker (Polynomial.aeval ξ).toRingHom := by
      simpa [RingHom.mem_ker] using ha
    rw [hkerξ] at hmem
    have hmemα : a ∈ RingHom.ker (Polynomial.aeval α).toRingHom := by
      rwa [hkerα]
    simpa [RingHom.mem_ker] using hmemα

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: a field-valued point of a standard-etale presentation
whose coordinate satisfies the residue-coordinate minimal polynomial has the same vanishing
elements as the original residue point. -/
private lemma standardEtalePresentation_fieldPoint_zero_iff_residue_zero
    (P : StandardEtalePresentation R S) (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S)
    {L : Type*} [Field L] [Algebra R L] [Algebra p.asIdeal.ResidueField L]
    [IsScalarTower R p.asIdeal.ResidueField L] (ψ : S →ₐ[R] L)
    (hψmin : aeval (ψ P.x)
      (minpoly p.asIdeal.ResidueField (algebraMap S q.1.ResidueField P.x)) = 0)
    (hψg : ψ (aeval P.x P.g) ≠ 0) (s : S) :
    ψ s = 0 ↔ algebraMap S q.1.ResidueField s = 0 := by
  -- Proof comment: clear the standard-etale denominator in `S`; nonvanishing of the denominator
  -- reduces both sides to the same polynomial numerator evaluated at two roots of one minpoly.
  let k := p.asIdeal.ResidueField
  let ξ : q.1.ResidueField := algebraMap S q.1.ResidueField P.x
  obtain ⟨a, n, ha⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
  let dψ : L := ψ (aeval P.x P.g)
  let dq : q.1.ResidueField := algebraMap S q.1.ResidueField (aeval P.x P.g)
  have hdq_ne : dq ≠ 0 := by
    have hunit : IsUnit dq := by
      simpa [dq] using P.hasMap.2.map (algebraMap S q.1.ResidueField)
    exact hunit.ne_zero
  have hdψ_pow_ne : dψ ^ n ≠ 0 := pow_ne_zero n (by simpa [dψ] using hψg)
  have hdq_pow_ne : dq ^ n ≠ 0 := pow_ne_zero n hdq_ne
  have hψ_num :
      ψ s * dψ ^ n = aeval (ψ P.x) (a.map (algebraMap R k)) := by
    have hmap := congrArg ψ ha
    have hright :
        ψ (aeval P.x a) = aeval (ψ P.x) (a.map (algebraMap R k)) := by
      calc
        ψ (aeval P.x a) = aeval (ψ P.x) a := by
          simpa using (aeval_algHom_apply ψ P.x a).symm
        _ = aeval (ψ P.x) (a.map (algebraMap R k)) := by
          rw [Polynomial.aeval_map_algebraMap]
    simpa [dψ, hright, map_mul, map_pow] using hmap
  have hq_num :
      algebraMap S q.1.ResidueField s * dq ^ n = aeval ξ (a.map (algebraMap R k)) := by
    have hmap := congrArg (algebraMap S q.1.ResidueField) ha
    have hright :
        algebraMap S q.1.ResidueField (aeval P.x a) =
          aeval ξ (a.map (algebraMap R k)) := by
      calc
        algebraMap S q.1.ResidueField (aeval P.x a) = aeval ξ a := by
          simpa [ξ] using
            (aeval_algHom_apply (IsScalarTower.toAlgHom R S q.1.ResidueField) P.x a).symm
        _ = aeval ξ (a.map (algebraMap R k)) := by
          rw [Polynomial.aeval_map_algebraMap]
    simpa [dq, hright, map_mul, map_pow] using hmap
  have hnum_iff :
      aeval (ψ P.x) (a.map (algebraMap R k)) = 0 ↔
        aeval ξ (a.map (algebraMap R k)) = 0 := by
    simpa [k, ξ] using
      aeval_eq_zero_iff_of_aeval_minpoly_eq_zero
        (standardEtalePresentation_residue_x_isIntegral P p q) hψmin
        (a.map (algebraMap R k))
  constructor
  · intro hψs
    have hψ_num_zero : aeval (ψ P.x) (a.map (algebraMap R k)) = 0 := by
      rw [← hψ_num, hψs, zero_mul]
    have hq_num_zero : aeval ξ (a.map (algebraMap R k)) = 0 := hnum_iff.mp hψ_num_zero
    have hq_mul_zero : algebraMap S q.1.ResidueField s * dq ^ n = 0 :=
      hq_num.trans hq_num_zero
    exact (mul_eq_zero.mp hq_mul_zero).resolve_right hdq_pow_ne
  · intro hqs
    have hq_num_zero : aeval ξ (a.map (algebraMap R k)) = 0 := by
      rw [← hq_num, hqs, zero_mul]
    have hψ_num_zero : aeval (ψ P.x) (a.map (algebraMap R k)) = 0 :=
      hnum_iff.mpr hq_num_zero
    have hψ_mul_zero : ψ s * dψ ^ n = 0 := hψ_num.trans hψ_num_zero
    exact (mul_eq_zero.mp hψ_mul_zero).resolve_right hdψ_pow_ne

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: the kernel of a standard-etale field-valued point is the
given fiber prime once the coordinate satisfies the residue minimal polynomial and the denominator
is nonzero. -/
private lemma standardEtalePresentation_ker_eq_prime_of_coordinate_minpoly
    (P : StandardEtalePresentation R S) (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S)
    {L : Type*} [Field L] [Algebra R L] [Algebra p.asIdeal.ResidueField L]
    [IsScalarTower R p.asIdeal.ResidueField L] (ψ : S →ₐ[R] L)
    (hψmin : aeval (ψ P.x)
      (minpoly p.asIdeal.ResidueField (algebraMap S q.1.ResidueField P.x)) = 0)
    (hψg : ψ (aeval P.x P.g) ≠ 0) :
    RingHom.ker ψ.toRingHom = q.1 := by
  -- Proof comment: convert equality of ideals to elementwise vanishing and use the residue-field
  -- zero criterion for membership in the prime.
  ext s
  constructor
  · intro hs
    rw [RingHom.mem_ker] at hs
    exact Ideal.algebraMap_residueField_eq_zero.mp
      ((standardEtalePresentation_fieldPoint_zero_iff_residue_zero P p q ψ hψmin hψg s).mp hs)
  · intro hs
    rw [RingHom.mem_ker]
    exact (standardEtalePresentation_fieldPoint_zero_iff_residue_zero P p q ψ hψmin hψg s).mpr
      (Ideal.algebraMap_residueField_eq_zero.mpr hs)

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: after choosing the irreducible fiber factor attached to
`q`, a split extension contains a root whose image in the residue field of `q'` lies on that
factor and avoids the denominator. -/
private lemma existsLiftedSplitRootAvoidingPrime
    (P : StandardEtalePresentation R S) {S' : Type (max u v)} [CommRing S'] [Algebra R S']
    (hsplit : (P.f.map (algebraMap R S')).Splits)
    (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) (q' : p.asIdeal.primesOver S') :
    let k := p.asIdeal.ResidueField
    let ξ : q.1.ResidueField := algebraMap S q.1.ResidueField P.x
    let f1 := minpoly k ξ
    ∃ a : S', aeval a P.f = 0 ∧
      aeval (algebraMap S' q'.1.ResidueField a) f1 = 0 ∧
      aeval (algebraMap S' q'.1.ResidueField a) (P.g.map (algebraMap R k)) ≠ 0 := by
  -- Proof comment: use the minimal-polynomial factor attached to `q` as the invariant that will
  -- identify the desired point after base change to the residue field of `q'`.
  dsimp only
  let k := p.asIdeal.ResidueField
  let L := q'.1.ResidueField
  let ξ : q.1.ResidueField := algebraMap S q.1.ResidueField P.x
  let f1 : k[X] := minpoly k ξ
  obtain ⟨hf1monic, hf1_irr, hf1_dvd, hg_not_dvd⟩ :=
    standardEtalePresentation_residue_minpoly_data P p q
  have hf_split_L : ((P.f.map (algebraMap R k)).map (algebraMap k L)).Splits := by
    -- Proof comment: splitness over `S'` transports to the residue field of `q'`; the two
    -- coefficient maps from `R` to `L` agree by the scalar tower associated to the primes-over
    -- relation.
    have hcoeff :
        (algebraMap k L).comp (algebraMap R k) =
          (algebraMap S' L).comp (algebraMap R S') := by
      ext r
      change (algebraMap k L) ((algebraMap R k) r) =
        (algebraMap S' L) ((algebraMap R S') r)
      rw [← Ideal.ResidueField.map_algebraMap p.asIdeal q'.1
        (algebraMap R S') (q'.1.over_def p.asIdeal) r]
      rfl
    simpa [k, L, Polynomial.map_map, hcoeff] using
      hsplit.map (algebraMap S' L : S' →+* L)
  obtain ⟨α, hαf1, hαf, hαg⟩ :=
    existsResidueRootMatchingFactorAvoidingDenominator
      (f := P.f.map (algebraMap R k)) (g := P.g.map (algebraMap R k)) (f1 := f1)
      (hfmonic := P.P.monic_f.map (algebraMap R k)) (hf1monic := hf1monic)
      hf1_irr hf1_dvd hg_not_dvd hf_split_L
  have hαf_R : aeval α P.f = 0 := by
    -- Proof comment: view the same root equation as an equation for the original polynomial over
    -- `R`, so that the root-lifting lemma can be applied over the original base.
    simpa [k, L, Polynomial.aeval_map_algebraMap] using hαf
  obtain ⟨a, haf, haα⟩ :=
    existsSplitRootAboveResidueRoot_of_splits
      (ρ := IsScalarTower.toAlgHom R S' L) (hfmonic := P.P.monic_f) hsplit hαf_R
  have haα' : algebraMap S' L a = α := haα
  refine ⟨a, haf, ?_, ?_⟩
  · -- Proof comment: the lifted root has the chosen residue coordinate, hence satisfies the same
    -- minimal-polynomial factor.
    simpa [k, L, f1, haα'] using hαf1
  · -- Proof comment: the same residue-coordinate equality carries the denominator nonvanishing.
    simpa [k, L, haα'] using hαg

omit [IsStandardEtale R S] in
/-- Helper for Chap10 Lemma 10 144 5: a split standard-étale presentation gives the required
localized factorization at every pair of primes over the same base prime. -/
private lemma standardEtalePresentation_exists_lift_away_comap_eq_of_splits
    (P : StandardEtalePresentation R S) {S' : Type (max u v)} [CommRing S'] [Algebra R S']
    (hsplit : (P.f.map (algebraMap R S')).Splits)
    (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) (q' : p.asIdeal.primesOver S') :
    ∃ (g' : S') (_ : g' ∉ q'.1) (φ : S →ₐ[R] Localization.Away g'),
      Ideal.comap φ.toRingHom (Ideal.map (algebraMap S' (Localization.Away g')) q'.1) =
        q.1 := by
  -- Route correction: the earlier direct transport through `P.equivRing` and
  -- `P.P.equivAwayAdjoinRoot` leaves a brittle localized-prime normal-form goal. The stable
  -- route should first construct the residue-field point over `q'` corresponding to `q`, then
  -- compare kernels of the two maps out of `S`.
  -- Proof comment: choose a split root in `S'` whose residue lies on the same minpoly factor as
  -- the coordinate of `q`, and set the inverted element to the denominator value at that root.
  let k := p.asIdeal.ResidueField
  let L := q'.1.ResidueField
  obtain ⟨a, haf, haf1, hag⟩ :=
    existsLiftedSplitRootAvoidingPrime P hsplit p q q'
  let g' : S' := aeval a P.g
  have hg' : g' ∉ q'.1 := by
    intro hgmem
    have hg_nonzero : aeval (algebraMap S' L a) P.g ≠ 0 := by
      simpa [k, L, Polynomial.aeval_map_algebraMap] using hag
    have hgzero : algebraMap S' L g' = 0 := by
      rw [Ideal.algebraMap_residueField_eq_zero]
      exact hgmem
    have hgeval :
        algebraMap S' L g' = aeval (algebraMap S' L a) P.g := by
      simpa [g', L] using
        (aeval_algHom_apply (IsScalarTower.toAlgHom R S' L) a P.g).symm
    exact hg_nonzero (hgeval ▸ hgzero)
  let xloc : Localization.Away g' := algebraMap S' (Localization.Away g') a
  have hxloc : P.P.HasMap xloc := by
    -- Proof comment: the root equation maps to the localization, while the denominator value is
    -- exactly the element inverted in `Localization.Away g'`.
    constructor
    · have hroot :
          algebraMap S' (Localization.Away g') (aeval a P.f) = 0 := by
        rw [haf, map_zero]
      have hroot_eval :
          algebraMap S' (Localization.Away g') (aeval a P.f) = aeval xloc P.f := by
        simpa [xloc] using
          (aeval_algHom_apply
            (IsScalarTower.toAlgHom R S' (Localization.Away g')) a P.f).symm
      exact hroot_eval ▸ hroot
    · have hden :
          aeval xloc P.g = algebraMap S' (Localization.Away g') g' := by
        simpa [xloc, g'] using
          (aeval_algHom_apply
            (IsScalarTower.toAlgHom R S' (Localization.Away g')) a P.g)
      rw [hden]
      exact IsLocalization.Away.algebraMap_isUnit g'
  let φ : S →ₐ[R] Localization.Away g' := (P.P.lift xloc hxloc).comp P.equivRing.toAlgHom
  obtain ⟨ρ, _hρcomp, hρker⟩ :=
    existsAwayResidueMap_ker_eq_map_prime (R := R) q'.1 hg'
  refine ⟨g', hg', φ, ?_⟩
  -- Proof comment: after the localized-prime kernel rewrite, it remains to show that the
  -- field-valued point `ρ.comp φ` cuts out the same fiber prime as `q`. Its coordinate is the
  -- chosen split root, so the minpoly/denominator kernel helper applies.
  have hφx : φ P.x = xloc := by
    calc
      φ P.x = (P.P.lift xloc hxloc) (P.equivRing P.x) := rfl
      _ = (P.P.lift xloc hxloc) P.P.X := by rw [P.equivRing_x]
      _ = xloc := P.P.lift_X xloc hxloc
  have hρa : ρ xloc = algebraMap S' L a := by
    have h := congrArg (fun η : S' →ₐ[R] L ↦ η a) _hρcomp
    simpa [xloc] using h
  have hψx : (ρ.comp φ) P.x = algebraMap S' L a := by
    calc
      (ρ.comp φ) P.x = ρ (φ P.x) := rfl
      _ = ρ xloc := congrArg ρ hφx
      _ = algebraMap S' L a := hρa
  have hψmin :
      aeval ((ρ.comp φ) P.x)
        (minpoly p.asIdeal.ResidueField (algebraMap S q.1.ResidueField P.x)) = 0 := by
    simpa [hψx, k, L] using haf1
  have hψg : (ρ.comp φ) (aeval P.x P.g) ≠ 0 := by
    intro hzero
    have hcompare :
        aeval (algebraMap S' L a) (P.g.map (algebraMap R k)) =
          (ρ.comp φ) (aeval P.x P.g) := by
      calc
        aeval (algebraMap S' L a) (P.g.map (algebraMap R k)) =
            aeval (algebraMap S' L a) P.g := by
          rw [Polynomial.aeval_map_algebraMap]
        _ = aeval ((ρ.comp φ) P.x) P.g := by rw [hψx]
        _ = (ρ.comp φ) (aeval P.x P.g) := by
          simpa using aeval_algHom_apply (ρ.comp φ) P.x P.g
    exact hag (hcompare.trans hzero)
  rw [← hρker, RingHom.comap_ker]
  exact standardEtalePresentation_ker_eq_prime_of_coordinate_minpoly P p q (ρ.comp φ) hψmin hψg

/-- Chap10 Lemma 10 144 5: for a standard étale morphism `R → S`, there exists an `R`-algebra
`S'` that is finite, finitely presented, and faithfully flat over `R`, hence has surjective
spectrum map, and such that for every prime `p` of `R`, every prime `q` of `S` over `p`, and
every prime `q'` of `S'` over `p`, one can localize `S'` away from an element outside `q'` so that
the resulting map `R → S'_{g'}` factors through an `R`-algebra map `S → S'_{g'}` carrying the
localized prime over `q'` back to `q`. -/
@[stacks 00UF]
theorem exists_finitePresentation_flat_surjective_extension_lifting_primes :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat),
        ∀ (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) (q' : p.asIdeal.primesOver S'),
          ∃ (g' : S') (_ : g' ∉ q'.1) (φ : S →ₐ[R] Localization.Away g'),
            Ideal.comap φ.toRingHom (Ideal.map (algebraMap S' (Localization.Away g')) q'.1) =
              q.1 := by
  -- First package the finite faithfully flat splitting extension supplied by the polynomial
  -- splitting lemma applied to a standard étale presentation of `S`.
  let P : StandardEtalePresentation R S := IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨S', hS'comm, hS'alg, hFinite, hfp, hff, hsplit⟩ :=
    exists_finitePresentationFaithfullyFlat_split_extension (R := R) (S := S) P
  letI : CommRing S' := hS'comm
  letI : Algebra R S' := hS'alg
  refine ⟨S', hS'comm, hS'alg, hFinite, hfp, hff, ?_⟩
  intro p q q'
  -- The remaining geometric step is isolated in the split-presentation lifting lemma; the public
  -- theorem now only performs the finite faithfully flat setup and forwards the split witness.
  exact standardEtalePresentation_exists_lift_away_comap_eq_of_splits P hsplit p q q'

end

end Algebra
