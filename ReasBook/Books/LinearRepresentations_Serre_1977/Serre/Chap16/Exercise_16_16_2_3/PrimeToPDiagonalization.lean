import Mathlib

open scoped MonoidAlgebra Classical
open Polynomial

universe u

/-! Prime-to-`p` diagonalization kernel for Swan's exercise 16-16.2-3 (see header below). -/

-- === INFRA: local p-group algebra is local + local extension with roots of unity ===
/-- If `f : R →+* T` is surjective with kernel contained in the Jacobson radical of `R`, then `f`
reflects units, i.e. `f` is a local ring homomorphism. -/
theorem isLocalHom_of_surjective_of_ker_le_jacobson_bot
    {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) (hf : Function.Surjective f)
    (h : RingHom.ker f ≤ Ideal.jacobson (⊥ : Ideal R)) : IsLocalHom f where
  map_nonunit a ha := by
    obtain ⟨b', hb'⟩ := isUnit_iff_exists_inv.mp ha
    obtain ⟨b, rfl⟩ := hf b'
    have hmem : a * b - 1 ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, hb', sub_self]
    have hu : IsUnit (a * b) :=
      Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (h hmem)
    exact isUnit_of_mul_isUnit_left hu

/-- If `f : R →+* T` is surjective with kernel contained in the Jacobson radical of `R`, and `T` is
a local ring, then `R` is a local ring. -/
theorem isLocalRing_of_surjective_of_ker_le_jacobson_bot
    {R T : Type*} [CommRing R] [CommRing T] [IsLocalRing T] (f : R →+* T)
    (hf : Function.Surjective f) (h : RingHom.ker f ≤ Ideal.jacobson (⊥ : Ideal R)) :
    IsLocalRing R :=
  haveI : IsLocalHom f := isLocalHom_of_surjective_of_ker_le_jacobson_bot f hf h
  f.domain_isLocalRing

section FieldBase

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
variable {P : Type u} [CommGroup P] [Finite P]

/-- The augmentation algebra homomorphism `k[P] →ₐ[k] k`, sending each `single g 1` to `1`. -/
private noncomputable def augHom : MonoidAlgebra k P →ₐ[k] k :=
  MonoidAlgebra.lift k k P (1 : P →* k)

@[simp] private theorem augHom_single (g : P) (r : k) :
    augHom (MonoidAlgebra.single g r) = r := by
  simp [augHom, MonoidAlgebra.lift_single]

omit [Finite P] in
private theorem isNilpotent_single_sub_one (hP : IsPGroup p P) (g : P) :
    IsNilpotent (MonoidAlgebra.single g (1 : k) - 1) := by
  haveI : CharP (MonoidAlgebra k P) p := by
    have hinj : Function.Injective
        (MonoidAlgebra.singleOneRingHom (R := k) (M := P)) := by
      intro a b hab
      simpa [MonoidAlgebra.singleOneRingHom_apply] using
        (Finsupp.single_injective (1 : P)) hab
    exact charP_of_injective_ringHom hinj p
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf (p := p)).mp hP g
  refine ⟨p ^ n, ?_⟩
  have hcomm : Commute (MonoidAlgebra.single g (1 : k)) 1 := Commute.one_right _
  rw [sub_pow_char_pow_of_commute p n hcomm, one_pow]
  have hpow : MonoidAlgebra.single g (1 : k) ^ p ^ n = 1 := by
    rw [MonoidAlgebra.single_pow, one_pow, ← hn, pow_orderOf_eq_one, MonoidAlgebra.one_def]
  rw [hpow, sub_self]

private theorem sub_aug_smul_mem_nilradical (hP : IsPGroup p P) (x : MonoidAlgebra k P) :
    x - augHom x • (1 : MonoidAlgebra k P) ∈ nilradical (MonoidAlgebra k P) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      have : (x + y) - augHom (x + y) • (1 : MonoidAlgebra k P)
          = (x - augHom x • 1) + (y - augHom y • 1) := by
        simp only [map_add, add_smul]; abel
      rw [this]
      exact Ideal.add_mem _ hx hy
  | single g r =>
      have : MonoidAlgebra.single g r - augHom (MonoidAlgebra.single g r) • (1 : MonoidAlgebra k P)
          = r • (MonoidAlgebra.single g (1 : k) - 1) := by
        rw [augHom_single, smul_sub]
        congr 1
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [this, Algebra.smul_def]
      refine Ideal.mul_mem_left _ _ ?_
      rw [mem_nilradical]
      exact isNilpotent_single_sub_one hP g

/-- The group algebra of a finite `p`-group over a field of characteristic `p` is a local ring. -/
theorem isLocalRing_monoidAlgebra_field_of_isPGroup (hP : IsPGroup p P) :
    IsLocalRing (MonoidAlgebra k P) := by
  refine isLocalRing_of_surjective_of_ker_le_jacobson_bot
    (augHom (k := k) (P := P)).toRingHom ?_ ?_
  · intro r
    exact ⟨MonoidAlgebra.single 1 r, by simp⟩
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have hxnil : x ∈ nilradical (MonoidAlgebra k P) := by
      have := sub_aug_smul_mem_nilradical hP x
      simpa [show (augHom (k := k) (P := P)) x = 0 from hx] using this
    exact (Ideal.jacobson_bot (R := MonoidAlgebra k P) ▸ nilradical_le_jacobson _) hxnil

end FieldBase

/-- A finite `p`-group algebra over a local ring with residue characteristic `p` is local. -/
theorem isLocalRing_monoidAlgebra_of_isPGroup
    {B : Type u} [CommRing B] [IsLocalRing B] {p : ℕ} [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p]
    {P : Type u} [CommGroup P] [Finite P] (hP : IsPGroup p P) :
    IsLocalRing (MonoidAlgebra B P) := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  set k := IsLocalRing.ResidueField B with hk
  -- the coefficient-reduction ring hom `B[P] → k[P]`
  set φ : MonoidAlgebra B P →+* MonoidAlgebra k P :=
    MonoidAlgebra.mapRingHom P (IsLocalRing.residue B) with hφ
  haveI : IsLocalRing (MonoidAlgebra k P) := isLocalRing_monoidAlgebra_field_of_isPGroup hP
  haveI : Module.Finite B (MonoidAlgebra B P) := Module.Finite.of_basis (MonoidAlgebra.basis P B)
  haveI : Algebra.IsIntegral B (MonoidAlgebra B P) := Algebra.IsIntegral.of_finite B _
  refine isLocalRing_of_surjective_of_ker_le_jacobson_bot φ ?_ ?_
  · -- surjectivity
    intro z
    induction z using MonoidAlgebra.induction_on with
    | hM g =>
        refine ⟨MonoidAlgebra.single g 1, ?_⟩
        rw [hφ, MonoidAlgebra.mapRingHom_single, map_one]
        rfl
    | hadd x y hx hy =>
        obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by rw [map_add, ha, hb]⟩
    | hsmul r x hx =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective r
        refine ⟨b • a, ?_⟩
        rw [Algebra.smul_def, map_mul, ha]
        have hb1 : φ (algebraMap B (MonoidAlgebra B P) b) = algebraMap k (MonoidAlgebra k P) r := by
          rw [hφ, MonoidAlgebra.coe_algebraMap, MonoidAlgebra.coe_algebraMap]
          simp [Function.comp, hb]
        rw [hb1, ← Algebra.smul_def]
  · -- `ker φ ≤ jacobson ⊥`
    rw [Ideal.jacobson]
    refine le_sInf ?_
    rintro M ⟨-, hM⟩
    haveI : M.IsMaximal := hM
    have hcomapM : M.comap (algebraMap B (MonoidAlgebra B P)) = IsLocalRing.maximalIdeal B :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
    intro y hy
    rw [RingHom.mem_ker] at hy
    have hcoeff : ∀ g, y g ∈ IsLocalRing.maximalIdeal B := by
      intro g
      have hzero : IsLocalRing.residue B (y g) = 0 := by
        have hap : (φ y) g = IsLocalRing.residue B (y g) := by
          rw [hφ, MonoidAlgebra.mapRingHom_apply]
        rw [← hap, hy]; rfl
      rwa [IsLocalRing.residue_eq_zero_iff] at hzero
    rw [← MonoidAlgebra.sum_single y, Finsupp.sum]
    refine Ideal.sum_mem _ (fun g _ => ?_)
    have halg : algebraMap B (MonoidAlgebra B P) (y g) = MonoidAlgebra.single 1 (y g) := by
      rw [MonoidAlgebra.coe_algebraMap]; simp
    have hsingle : MonoidAlgebra.single g (y g)
        = algebraMap B (MonoidAlgebra B P) (y g) * MonoidAlgebra.single g 1 := by
      rw [halg, MonoidAlgebra.single_mul_single, one_mul, mul_one]
    rw [hsingle]
    refine Ideal.mul_mem_right _ _ ?_
    rw [← Ideal.mem_comap, hcomapM]
    exact hcoeff g

-- === INFRA: cyclotomic local extension with a primitive root ===
theorem exists_local_extension_with_primitiveRoot
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    {m : ℕ} (hm : Nat.Coprime p m) (hm0 : 0 < m) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra A B),
      Function.Injective (algebraMap A B) ∧
      CharP (IsLocalRing.ResidueField B) p ∧
      ∃ ζ : B, IsPrimitiveRoot ζ m := by
  -- Step 1: monicity of the m-th cyclotomic polynomial over A
  have hmonic : (Polynomial.cyclotomic m A).Monic := Polynomial.cyclotomic.monic m A
  -- Step 2: degree ≠ 0
  have hdeg : (Polynomial.cyclotomic m A).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic m A]
    have : 0 < Nat.totient m := Nat.totient_pos.mpr hm0
    intro h
    rw [Nat.cast_eq_zero] at h
    omega
  -- Step 3: build C = AdjoinRoot (cyclotomic m A) and its instances
  set C := AdjoinRoot (Polynomial.cyclotomic m A) with hC
  haveI : Module.Finite A C := hmonic.finite_adjoinRoot
  haveI : Module.Free A C := hmonic.free_adjoinRoot
  haveI : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  have hAC_inj : Function.Injective (algebraMap A C) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg
  -- Step 4: lying over
  haveI : (IsLocalRing.maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  obtain ⟨𝔮, h𝔮max, h𝔮over⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := C) (IsLocalRing.maximalIdeal A)
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hAC_inj]; exact bot_le)
  haveI : 𝔮.IsPrime := h𝔮max.isPrime
  -- Step 5: B = Localization.AtPrime 𝔮
  set B := Localization.AtPrime 𝔮 with hB
  haveI : IsLocalRing B := Localization.AtPrime.isLocalRing 𝔮
  -- Step 6: Algebra A B via composite
  letI : Algebra A B := ((algebraMap C B).comp (algebraMap A C)).toAlgebra
  have hAB_eq : (algebraMap A B) = (algebraMap C B).comp (algebraMap A C) :=
    RingHom.algebraMap_toAlgebra _
  -- Step 7: injectivity of algebraMap A B
  have hAB_inj : Function.Injective (algebraMap A B) := by
    rw [injective_iff_map_eq_zero]
    intro a hzero
    rw [hAB_eq, RingHom.comp_apply] at hzero
    -- algebraMap C B (algebraMap A C a) = 0
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff 𝔮.primeCompl B _).mp hzero
    -- (t : C) * algebraMap A C a = 0
    have ht' : a • (t : C) = 0 := by
      rw [Algebra.smul_def, mul_comm]
      exact ht
    rcases smul_eq_zero.1 ht' with h | h
    · exact h
    · -- t ≠ 0 since t ∈ primeCompl
      exfalso
      have htmem : (t : C) ∈ 𝔮.primeCompl := t.2
      rw [h] at htmem
      exact htmem (𝔮.zero_mem)
  -- Step 8: comap of maximal ideal
  have hcomap : (IsLocalRing.maximalIdeal B).comap (algebraMap A B)
      = IsLocalRing.maximalIdeal A := by
    rw [hAB_eq, ← Ideal.comap_comap]
    rw [Localization.AtPrime.comap_maximalIdeal]
    exact h𝔮over
  -- Step 9: IsLocalHom
  haveI hloc : IsLocalHom (algebraMap A B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 4 0 rfl rfl).mp hcomap
  -- Step 10: CharP of residue field B
  haveI hcharB : CharP (IsLocalRing.ResidueField B) p := by
    have hinj : Function.Injective
        (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :=
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).injective
    exact charP_of_injective_algebraMap hinj p
  -- Step 11: primitive root
  -- r ∈ C is the adjoined root
  set r : C := AdjoinRoot.root (Polynomial.cyclotomic m A) with hr
  set ζ : B := algebraMap C B r with hζ
  -- ζ ^ m = 1
  have hr_cyc : (Polynomial.aeval r) (Polynomial.cyclotomic m A) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hr_m : r ^ m = 1 := by
    obtain ⟨q, hq⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one m A
    have key : (Polynomial.aeval r) (X ^ m - 1 : A[X]) = 0 := by
      rw [hq, map_mul, hr_cyc, zero_mul]
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at key
    exact key
  have hζm : ζ ^ m = 1 := by
    rw [hζ, ← map_pow, hr_m, map_one]
  -- Now compute orderOf ζ via the residue field
  set κ := IsLocalRing.ResidueField B with hκ
  -- NeZero (m : κ) since p ∤ m
  haveI hNeZero : NeZero ((m : ℕ) : κ) := by
    apply NeZero.of_not_dvd κ (p := p)
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out] at hm
    exact hm
  -- residue map and ζ̄
  set ψ : C →+* κ := (IsLocalRing.residue B).comp (algebraMap C B) with hψ
  set ζbar : κ := IsLocalRing.residue B ζ with hζbar
  have hψr : ψ r = ζbar := by
    rw [hψ, RingHom.comp_apply, hζbar, hζ]
  -- ζ̄ is a root of cyclotomic m κ
  have hroot : (Polynomial.cyclotomic m κ).IsRoot ζbar := by
    have h0 : ψ ((Polynomial.aeval r) (Polynomial.cyclotomic m A)) = 0 := by
      rw [hr_cyc, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hψr] at h0
    -- h0 : eval₂ (ψ.comp (algebraMap A C)) ζbar (cyclotomic m A) = 0
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] at h0
    exact h0
  -- IsPrimitiveRoot ζbar m
  have hprimbar : IsPrimitiveRoot ζbar m := (Polynomial.isRoot_cyclotomic_iff).mp hroot
  -- orderOf ζbar = m
  have horderbar : orderOf ζbar = m := (hprimbar.eq_orderOf).symm
  -- m ∣ orderOf ζ  via orderOf_map_dvd of the ring hom (as MonoidHom)
  have hdvd1 : m ∣ orderOf ζ := by
    have : orderOf ζbar ∣ orderOf ζ := by
      have := orderOf_map_dvd (IsLocalRing.residue B : B →+* κ).toMonoidHom ζ
      simpa [hζbar] using this
    rwa [horderbar] at this
  -- orderOf ζ ∣ m  via ζ^m = 1
  have hdvd2 : orderOf ζ ∣ m := orderOf_dvd_of_pow_eq_one hζm
  have horder : orderOf ζ = m := Nat.dvd_antisymm hdvd2 hdvd1
  -- build IsPrimitiveRoot ζ m
  have hprim : IsPrimitiveRoot ζ m := by
    refine ⟨hζm, fun l hl => ?_⟩
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hl
  -- Step 12: assemble
  exact ⟨B, inferInstance, inferInstance, inferInstance, hAB_inj, hcharB, ζ, hprim⟩

-- === INFRA: Chinese-Remainder eigen-idempotent decomposition ===
/-- Orthogonal idempotents summing to `1` give an internal direct sum of their ranges. -/
theorem isInternal_range_of_orthogonal_idempotents
    {S : Type u} [CommRing S] {W : Type u} [AddCommGroup W] [Module S W]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : ι → Module.End S W)
    (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ i, e i = 1) :
    DirectSum.IsInternal (fun i => LinearMap.range (e i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · -- independence
    rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hxi hxsup
    -- `e i` acts as identity on `range (e i)`
    obtain ⟨y, rfl⟩ := hxi
    -- `e i` kills the supremum of the other ranges
    have hker : (⨆ j, ⨆ (_ : j ≠ i), LinearMap.range (e j)) ≤ LinearMap.ker (e i) := by
      refine iSup_le fun j => iSup_le fun hji => ?_
      rintro _ ⟨z, rfl⟩
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, horth i j (Ne.symm hji),
        LinearMap.zero_apply]
    have hzero : e i (e i y) = 0 := by
      have := hker hxsup
      rwa [LinearMap.mem_ker] at this
    -- but `e i (e i y) = e i y` by idempotence
    have hidemy : e i (e i y) = e i y := by
      have := hidem i
      rw [IsIdempotentElem] at this
      rw [← Module.End.mul_apply, this]
    rw [hidemy] at hzero
    exact hzero
  · -- the ranges span everything
    rw [eq_top_iff]
    intro w _
    have hw : w = (∑ i, e i) w := by rw [hsum, Module.End.one_apply]
    rw [hw, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self (e i) w)

/-- A monic divisor of a nonzero polynomial cannot have larger degree;
contrapositive form: a polynomial divisible by a monic polynomial of strictly larger
degree must be zero. Works over an arbitrary commutative ring. -/
theorem eq_zero_of_monic_dvd_of_degree_lt {S : Type u} [CommRing S]
    {g f : S[X]} (hg : g.Monic) (hdvd : g ∣ f) (hlt : f.degree < g.degree) : f = 0 := by
  obtain ⟨q, rfl⟩ := hdvd
  by_contra hne
  have hq : q ≠ 0 := by
    rintro rfl; rw [mul_zero] at hne; exact hne rfl
  have hdeg : (q * g).degree = q.degree + g.degree := hg.degree_mul
  rw [mul_comm, hdeg] at hlt
  have hq0 : (0 : WithBot ℕ) ≤ q.degree := by
    rw [Polynomial.degree_eq_natDegree hq]
    exact_mod_cast Nat.zero_le _
  have : g.degree ≤ q.degree + g.degree := le_add_of_nonneg_left hq0
  exact absurd hlt (not_lt.mpr this)

/-- The product `∏ (X - ζ^i)` equals `X^m - 1` over a commutative ring, when `ζ^m = 1`
and the power-differences `ζ^i - ζ^j` are units (so the roots are "separated"). -/
theorem prod_X_sub_C_pow_eq_X_pow_sub_one {S : Type u} [CommRing S]
    {m : ℕ} (hm0 : 0 < m) (ζ : S) (hζ : ζ ^ m = 1)
    (hunit : ∀ i j : Fin m, (i : ℕ) ≠ (j : ℕ) → IsUnit (ζ ^ (i : ℕ) - ζ ^ (j : ℕ))) :
    (∏ i : Fin m, (X - C (ζ ^ (i : ℕ))) : S[X]) = X ^ m - 1 := by
  -- handle the trivial ring
  rcases subsingleton_or_nontrivial S with hsub | hnt
  · exact Subsingleton.elim _ _
  set g : S[X] := ∏ i : Fin m, (X - C (ζ ^ (i : ℕ))) with hg_def
  have hg_monic : g.Monic := by
    apply monic_prod_of_monic
    intro i _; exact monic_X_sub_C _
  -- the difference `f`
  set f : S[X] := (X ^ m - 1) - g with hf_def
  -- each ζ^j is a root of `f`
  have hroots : ∀ j : Fin m, f.IsRoot (ζ ^ (j : ℕ)) := by
    intro j
    have hg_root : g.eval (ζ ^ (j : ℕ)) = 0 := by
      rw [hg_def, eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [eval_sub, eval_X, eval_C]
    have hxm_root : (X ^ m - (1 : S[X])).eval (ζ ^ (j : ℕ)) = 0 := by
      rw [eval_sub, eval_pow, eval_X, eval_one, ← pow_mul, mul_comm, pow_mul, hζ, one_pow,
        sub_self]
    rw [Polynomial.IsRoot, hf_def, eval_sub, hxm_root, hg_root, sub_zero]
  -- hence each (X - ζ^j) divides f, and these are pairwise coprime, so g ∣ f
  have hcoprime : Pairwise (Function.onFun IsCoprime (fun i : Fin m => X - C (ζ ^ (i : ℕ)))) := by
    intro i j hij
    exact isCoprime_X_sub_C_of_isUnit_sub (hunit i j (fun h => hij (Fin.ext h)))
  have hg_dvd_f : g ∣ f := by
    rw [hg_def]
    apply Fintype.prod_dvd_of_coprime hcoprime
    intro j
    rw [dvd_iff_isRoot]
    exact hroots j
  -- degree of f is < degree of g = m
  have hdeg_g : g.degree = (m : ℕ) := by
    rw [hg_def]
    rw [Polynomial.degree_eq_natDegree hg_monic.ne_zero, natDegree_prod_of_monic]
    · simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    · intro i _; exact monic_X_sub_C _
  have hdeg_f : f.degree < (m : WithBot ℕ) := by
    rw [hf_def]
    have hd_eq : (X ^ m - (1 : S[X])).degree = (m : WithBot ℕ) := by
      have h := degree_X_pow_sub_C (R := S) hm0 (1 : S)
      rwa [map_one] at h
    -- `X^m - 1` is monic of degree m
    have hmon : (X ^ m - (1 : S[X])).Monic := by
      have h : (X ^ m - C (1 : S)).Monic := monic_X_pow_sub (by
        rw [map_one, degree_one]
        exact_mod_cast hm0)
      rwa [map_one] at h
    -- both have degree m and the same leading coeff 1, so the difference has smaller degree
    have hsub_lt := Polynomial.degree_sub_lt (p := X ^ m - (1 : S[X])) (q := g)
      (by rw [hd_eq, hdeg_g])
      (by rw [Ne, ← degree_eq_bot, hd_eq]; exact (WithBot.natCast_ne_bot m))
      (by rw [hmon.leadingCoeff, hg_monic.leadingCoeff])
    rwa [hd_eq] at hsub_lt
  -- conclude f = 0
  have hf0 : f = 0 :=
    eq_zero_of_monic_dvd_of_degree_lt hg_monic hg_dvd_f (by rw [hdeg_g]; exact_mod_cast hdeg_f)
  rw [hf_def, sub_eq_zero] at hf0
  exact hf0.symm

theorem exists_orthogonal_idempotents_of_pow_eq_one
    {S : Type u} [CommRing S] {W : Type u} [AddCommGroup W] [Module S W]
    (φ : Module.End S W) {m : ℕ} (hm0 : 0 < m) (ζ : S)
    (hφ : φ ^ m = 1) (hζ : ζ ^ m = 1)
    (hunit : ∀ i j : Fin m, (i : ℕ) ≠ (j : ℕ) → IsUnit (ζ ^ (i : ℕ) - ζ ^ (j : ℕ))) :
    ∃ e : Fin m → Module.End S W,
      (∀ i, IsIdempotentElem (e i)) ∧
      (∀ i j, i ≠ j → e i * e j = 0) ∧
      (∑ i, e i = 1) ∧
      (∀ i, φ * e i = (ζ ^ (i : ℕ)) • e i) := by
  classical
  -- the linear factors and their spans
  set L : Fin m → S[X] := fun i => X - C (ζ ^ (i : ℕ)) with hL
  set I : Fin m → Ideal S[X] := fun i => Ideal.span {L i} with hI
  -- pairwise coprime
  have hcoprime : ∀ i j : Fin m, i ≠ j → IsCoprime (L i) (L j) := by
    intro i j hij
    exact isCoprime_X_sub_C_of_isUnit_sub (hunit i j (fun h => hij (Fin.ext h)))
  -- the intersection of the ideals is span {X^m - 1}
  have hfact : (∏ i, L i) = (X ^ m - 1 : S[X]) :=
    prod_X_sub_C_pow_eq_X_pow_sub_one hm0 ζ hζ hunit
  have hinf : (⨅ i, I i) = Ideal.span {(X ^ m - 1 : S[X])} := by
    rw [hI]
    rw [Ideal.iInf_span_singleton hcoprime, hfact]
  -- the bridge: aeval φ kills span {X^m - 1}
  have haeval_pow : (Polynomial.aeval φ) (X ^ m - 1 : S[X]) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hφ, sub_self]
  have hbridge : ∀ r : S[X], r ∈ (⨅ i, I i) → (Polynomial.aeval φ) r = 0 := by
    intro r hr
    rw [hinf, Ideal.mem_span_singleton] at hr
    obtain ⟨t, rfl⟩ := hr
    rw [map_mul, haeval_pow, zero_mul]
  -- helper: if r - s ∈ ⨅ I, then aeval φ r = aeval φ s
  have hbridge2 : ∀ r s : S[X], r - s ∈ (⨅ i, I i) →
      (Polynomial.aeval φ) r = (Polynomial.aeval φ) s := by
    intro r s hrs
    have := hbridge (r - s) hrs
    rw [map_sub, sub_eq_zero] at this
    exact this
  -- membership characterization in each I j
  have hmemI : ∀ (j : Fin m) (p : S[X]), p ∈ I j ↔ (L j ∣ p) := by
    intro j p
    rw [hI, Ideal.mem_span_singleton]
  -- CRT: obtain the idempotent polynomials g i with g i ≡ δ_{ij} mod I j
  have hCRT : ∀ i : Fin m, ∃ g : S[X],
      (g - 1 ∈ I i) ∧ (∀ j, j ≠ i → g ∈ I j) := by
    intro i
    have hpw : Pairwise (Function.onFun IsCoprime I) := by
      intro a b hab
      rw [hI]
      exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcoprime a b hab)
    obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hpw
      (fun j => if j = i then (1 : S[X]) else 0)
    refine ⟨r, ?_, ?_⟩
    · have := hr i
      simpa using this
    · intro j hji
      have := hr j
      rw [if_neg hji, sub_zero] at this
      exact this
  -- choose the idempotent polynomials
  choose g hg1 hg0 using hCRT
  -- define the idempotents
  refine ⟨fun i => (Polynomial.aeval φ) (g i), ?_, ?_, ?_, ?_⟩
  · -- idempotence
    intro i
    rw [IsIdempotentElem]
    rw [← map_mul]
    apply hbridge2
    -- g i * g i - g i ∈ ⨅ I j
    rw [Ideal.mem_iInf]
    intro j
    by_cases hji : j = i
    · subst hji
      -- mod I i: g i ≡ 1, so g i * g i - g i ≡ 1 - 1 = 0
      have h1 : g j - 1 ∈ I j := hg1 j
      -- g i * g i - g i = (g i - 1) * g i ... actually = g i * (g i - 1)
      have : g j * g j - g j = g j * (g j - 1) := by ring
      rw [this]
      exact Ideal.mul_mem_left (I j) (g j) h1
    · -- mod I j (j ≠ i): g i ≡ 0
      have h0 : g i ∈ I j := hg0 i j hji
      have : g i * g i - g i = (g i * g i - g i) := rfl
      have hmem : g i * g i - g i ∈ I j := by
        apply Ideal.sub_mem
        · exact Ideal.mul_mem_left (I j) (g i) h0
        · exact h0
      exact hmem
  · -- orthogonality
    intro i j hij
    rw [← map_mul]
    have hmem0 : g i * g j ∈ (⨅ k, I k) := by
      rw [Ideal.mem_iInf]
      intro k
      by_cases hki : k = i
      · -- mod I k=i: g j ≡ 0 since j ≠ i = k
        have hkj : k ≠ j := by rw [hki]; exact hij
        have h0 : g j ∈ I k := hg0 j k hkj
        exact Ideal.mul_mem_left (I k) (g i) h0
      · -- k ≠ i: g i ≡ 0
        have h0 : g i ∈ I k := hg0 i k hki
        exact Ideal.mul_mem_right (g j) (I k) h0
    rw [hbridge _ hmem0]
  · -- sum = 1
    rw [← map_sum]
    have hsum1 : (∑ i, g i) - (1 : S[X]) ∈ (⨅ k, I k) := by
      rw [Ideal.mem_iInf]
      intro k
      -- mod I k: ∑ g i ≡ 1 (only the k-th term is ≡ 1, rest ≡ 0)
      have hsumk : (∑ i, g i) - 1 = (g k - 1) + ∑ i ∈ Finset.univ.erase k, g i := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
        ring
      rw [hsumk]
      apply Ideal.add_mem
      · exact hg1 k
      · apply Ideal.sum_mem
        intro i hi
        have hik : i ≠ k := Finset.ne_of_mem_erase hi
        exact hg0 i k hik.symm
    have heq1 : (Polynomial.aeval φ) (∑ i, g i) = (Polynomial.aeval φ) (1 : S[X]) :=
      hbridge2 _ _ hsum1
    rw [heq1, map_one]
  · -- scalar action
    intro i
    show φ * (Polynomial.aeval φ) (g i) = (ζ ^ (i : ℕ)) • (Polynomial.aeval φ) (g i)
    -- the congruence  X * g i ≡ C(ζ^i) * g i  mod ⨅ I
    have hsmul : (Polynomial.aeval φ) (X * g i) = (Polynomial.aeval φ) (C (ζ ^ (i : ℕ)) * g i) := by
      apply hbridge2
      -- X * g i - C(ζ^i) * g i = (X - C ζ^i) * g i = L i * g i
      have heq : X * g i - C (ζ ^ (i : ℕ)) * g i = L i * g i := by
        rw [hL]; ring
      rw [heq, Ideal.mem_iInf]
      intro k
      by_cases hki : k = i
      · subst hki
        -- L k ∈ I k
        have hLk : L k ∈ I k := by
          rw [hmemI]
        exact Ideal.mul_mem_right (g k) (I k) hLk
      · -- g i ∈ I k since i ≠ k
        have h0 : g i ∈ I k := hg0 i k hki
        exact Ideal.mul_mem_left (I k) (L i) h0
    -- rewrite both sides through aeval
    rw [map_mul, Polynomial.aeval_X, map_mul, Polynomial.aeval_C] at hsmul
    rw [Algebra.smul_def]
    exact hsmul

-- === Helper lemmas + the Swan local trace kernel ===

/-- The trace of an idempotent over a local ring is the (cast of the) rank of its range. -/
theorem trace_idempotent_eq_natCast_finrank_of_local
    {S : Type u} [CommRing S] [IsLocalRing S] {N : Type u} [AddCommGroup N] [Module S N]
    [Module.Finite S N] [Module.Free S N]
    (e : Module.End S N) (he : IsIdempotentElem e) :
    LinearMap.trace S N e = (Module.finrank S (LinearMap.range e) : S) := by
  classical
  have hfree_range : ∀ (f : Module.End S N), IsIdempotentElem f →
      Module.Finite S (LinearMap.range f) ∧ Module.Free S (LinearMap.range f) := by
    intro f hf
    have hsplit : f.rangeRestrict ∘ₗ (LinearMap.range f).subtype = LinearMap.id := by
      ext y
      obtain ⟨z, hz⟩ := y.2
      have hyfix : f (y : N) = (y : N) := by rw [← hz, ← Module.End.mul_apply, hf]
      simpa [LinearMap.rangeRestrict, LinearMap.codRestrict_apply] using hyfix
    haveI : Module.Finite S (LinearMap.range f) :=
      Module.Finite.of_surjective f.rangeRestrict (LinearMap.surjective_rangeRestrict f)
    haveI : Module.Projective S (LinearMap.range f) :=
      Module.Projective.of_split (LinearMap.range f).subtype f.rangeRestrict hsplit
    haveI : Module.Flat S (LinearMap.range f) := Module.Flat.of_projective
    exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩
  obtain ⟨hfin_r, hfree_r⟩ := hfree_range e he
  obtain ⟨hfin_k, hfree_k⟩ := hfree_range (1 - e) (IsIdempotentElem.one_sub he)
  letI : Module.Finite S (LinearMap.range e) := hfin_r
  letI : Module.Free S (LinearMap.range e) := hfree_r
  letI : Module.Finite S (LinearMap.ker e) := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub he]; exact hfin_k
  letI : Module.Free S (LinearMap.ker e) := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub he]; exact hfree_k
  exact ((LinearMap.isProj_range_iff_isIdempotentElem e).mpr he).trace

/-- If `x ≡ 1` modulo the maximal ideal of a local ring with residue characteristic `p` and
`x ^ d = 1` for some `d` prime to `p`, then `x = 1`. -/
theorem eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one
    {B : Type u} [CommRing B] [IsLocalRing B] {p : ℕ} [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p]
    {x : B} (hx : x - 1 ∈ IsLocalRing.maximalIdeal B)
    {d : ℕ} (hd : Nat.Coprime p d) (hxd : x ^ d = 1) : x = 1 := by
  classical
  set G : B := ∑ i ∈ Finset.range d, x ^ i with hG
  have hmul : G * (x - 1) = 0 := by rw [hG, geom_sum_mul, hxd, sub_self]
  have hpd : ¬ p ∣ d := ((Fact.out : p.Prime).coprime_iff_not_dvd).mp hd
  have hdunit : IsUnit (d : B) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact fun h => hpd ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField B) p d).mp h)
  have hGd : G - (d : B) ∈ IsLocalRing.maximalIdeal B := by
    have heq : G - (d : B) = ∑ i ∈ Finset.range d, (x ^ i - 1) := by
      rw [hG, Finset.sum_sub_distrib]; simp
    rw [heq]
    apply Ideal.sum_mem
    intro i _
    have hdvd : (x - 1) ∣ (x ^ i - 1) :=
      ⟨∑ j ∈ Finset.range i, x ^ j, by rw [mul_comm, geom_sum_mul]⟩
    exact Ideal.mem_of_dvd _ hdvd hx
  have hGunit : IsUnit G := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hGmem
    apply IsLocalRing.notMem_maximalIdeal.mpr hdunit
    have hd_eq : (d : B) = G - (G - (d : B)) := by ring
    rw [hd_eq]
    exact Ideal.sub_mem _ hGmem hGd
  have hsub : x - 1 = 0 := (hGunit.mul_right_eq_zero).mp hmul
  exact sub_eq_zero.mp hsub

/-- Over a local ring with residue characteristic `p`, if `ζ` is a primitive `m`-th root of unity
with `m` prime to `p`, then `ζ ^ k - 1` is a unit whenever `m ∤ k`. -/
theorem isUnit_pow_sub_one_of_not_dvd
    {B : Type u} [CommRing B] [IsLocalRing B] {p : ℕ} [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p]
    {m : ℕ} (hm : Nat.Coprime p m) {ζ : B} (hζ : IsPrimitiveRoot ζ m)
    {k : ℕ} (hk : ¬ m ∣ k) : IsUnit (ζ ^ k - 1) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  have hpow : (ζ ^ k) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hx1 : ζ ^ k = 1 :=
    eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one (x := ζ ^ k) hmem hm hpow
  exact hk ((hζ.pow_eq_one_iff_dvd k).mp hx1)

/-- Power-differences of a primitive `m`-th root of unity (with `m` prime to the residue
characteristic) are units of a local ring. -/
theorem isUnit_pow_sub_pow_of_ne
    {B : Type u} [CommRing B] [IsLocalRing B] {p : ℕ} [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p]
    {m : ℕ} (hm : Nat.Coprime p m) (hm0 : 0 < m) {ζ : B} (hζ : IsPrimitiveRoot ζ m)
    {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i ≠ j) :
    IsUnit (ζ ^ i - ζ ^ j) := by
  have hζunit : IsUnit ζ := hζ.isUnit hm0.ne'
  rcases lt_or_gt_of_ne hij with h | h
  · have hkpos : 0 < j - i := Nat.sub_pos_of_lt h
    have hkdvd : ¬ m ∣ (j - i) := fun hd => by
      have := Nat.le_of_dvd hkpos hd; omega
    have hfac : ζ ^ j - ζ ^ i = ζ ^ i * (ζ ^ (j - i) - 1) := by
      rw [mul_sub, ← pow_add, mul_one, Nat.add_sub_cancel' (le_of_lt h)]
    have hu : IsUnit (ζ ^ j - ζ ^ i) := by
      rw [hfac]; exact (hζunit.pow i).mul (isUnit_pow_sub_one_of_not_dvd hm hζ hkdvd)
    simpa using hu.neg
  · have hkpos : 0 < i - j := Nat.sub_pos_of_lt h
    have hkdvd : ¬ m ∣ (i - j) := fun hd => by
      have := Nat.le_of_dvd hkpos hd; omega
    have hfac : ζ ^ i - ζ ^ j = ζ ^ j * (ζ ^ (i - j) - 1) := by
      rw [mul_sub, ← pow_add, mul_one, Nat.add_sub_cancel' (le_of_lt h)]
    rw [hfac]; exact (hζunit.pow j).mul (isUnit_pow_sub_one_of_not_dvd hm hζ hkdvd)

-- ===========================================================================================
-- Kernel over a local ring `B` that already contains the roots of unity
-- ===========================================================================================

/-- Over a local ring `B` (residue characteristic `p`) containing a primitive `m`-th root of unity,
for a finite projective module `N` over the commutative local group algebra `B[P]` of a finite
abelian `p`-group `P`, the `B[P]`-trace of any `B[P]`-linear operator `w` with `w ^ m = 1`
(`m` prime to `p`) is supported at the identity. -/
theorem trace_mem_algebraMap_range_of_pow_eq_one_local
    {B : Type u} [CommRing B] [IsLocalRing B] {p : ℕ} [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField B) p]
    {P : Type u} [CommGroup P] [Finite P] (hP : IsPGroup p P)
    {N : Type u} [AddCommGroup N] [Module (MonoidAlgebra B P) N]
    [Module.Finite (MonoidAlgebra B P) N] [Module.Projective (MonoidAlgebra B P) N]
    {m : ℕ} (hm : Nat.Coprime p m) (hm0 : 0 < m)
    (w : N →ₗ[MonoidAlgebra B P] N) (hw : w ^ m = 1)
    {ζ : B} (hζ : IsPrimitiveRoot ζ m) :
    ∃ b0 : B, LinearMap.trace (MonoidAlgebra B P) N w
        = algebraMap B (MonoidAlgebra B P) b0 := by
  classical
  haveI : IsLocalRing (MonoidAlgebra B P) := isLocalRing_monoidAlgebra_of_isPGroup hP
  haveI : Module.Flat (MonoidAlgebra B P) N := Module.Flat.of_projective
  haveI : Module.Free (MonoidAlgebra B P) N := Module.free_of_flat_of_isLocalRing
  set ζP : MonoidAlgebra B P := algebraMap B (MonoidAlgebra B P) ζ with hζP
  have hζPpow : ζP ^ m = 1 := by rw [hζP, ← map_pow, hζ.pow_eq_one, map_one]
  have hunit : ∀ i j : Fin m, (i : ℕ) ≠ (j : ℕ) → IsUnit (ζP ^ (i : ℕ) - ζP ^ (j : ℕ)) := by
    intro i j hij
    have hbase := isUnit_pow_sub_pow_of_ne hm hm0 hζ i.2 j.2 hij
    rw [hζP, ← map_pow, ← map_pow, ← map_sub]
    exact hbase.map (algebraMap B (MonoidAlgebra B P))
  obtain ⟨e, hidem, _horth, hsum, hscalar⟩ :=
    exists_orthogonal_idempotents_of_pow_eq_one (S := MonoidAlgebra B P) (W := N)
      w hm0 ζP hw hζPpow hunit
  have hw_eq : w = ∑ i : Fin m, ζP ^ (i : ℕ) • e i := by
    calc w = w * 1 := (mul_one w).symm
      _ = w * ∑ i, e i := by rw [hsum]
      _ = ∑ i, w * e i := by rw [Finset.mul_sum]
      _ = ∑ i : Fin m, ζP ^ (i : ℕ) • e i := Finset.sum_congr rfl (fun i _ => hscalar i)
  have htr : LinearMap.trace (MonoidAlgebra B P) N w
      = ∑ i : Fin m, ζP ^ (i : ℕ) • LinearMap.trace (MonoidAlgebra B P) N (e i) := by
    rw [hw_eq, map_sum]
    exact Finset.sum_congr rfl (fun i _ => map_smul _ _ _)
  refine ⟨∑ i : Fin m, ζ ^ (i : ℕ) *
      (Module.finrank (MonoidAlgebra B P) (LinearMap.range (e i)) : B), ?_⟩
  rw [htr, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [trace_idempotent_eq_natCast_finrank_of_local (e i) (hidem i), smul_eq_mul, map_mul,
    map_natCast, hζP, ← map_pow]

-- ===========================================================================================
-- Kernel over the base local DVR `A` (via base change)
-- ===========================================================================================

/-- **Swan local trace kernel.** For a finite projective module `V` over the group algebra `A[P]`
of a finite abelian `p`-group `P` over a local DVR `A` with residue characteristic `p`, the
`A[P]`-trace of any `A[P]`-linear operator `u` of order `m` prime to `p` is supported at the
identity, i.e. equals `algebraMap A A[P] a` for some `a : A`. -/
theorem trace_pSubgroupLinear_mem_algebraMap_range
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    {P : Type u} [CommGroup P] [Finite P] (hP : IsPGroup p P)
    {V : Type u} [AddCommGroup V] [Module (MonoidAlgebra A P) V]
    [Module.Finite (MonoidAlgebra A P) V] [Module.Projective (MonoidAlgebra A P) V]
    (u : V →ₗ[MonoidAlgebra A P] V) {m : ℕ} (hm : Nat.Coprime p m) (hu : u ^ m = 1) :
    ∃ a : A, LinearMap.trace (MonoidAlgebra A P) V u
        = algebraMap A (MonoidAlgebra A P) a := by
  classical
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by
    rintro rfl
    exact (Fact.out : p.Prime).ne_one ((Nat.coprime_zero_right p).mp hm))
  haveI : IsLocalRing (MonoidAlgebra A P) := isLocalRing_monoidAlgebra_of_isPGroup hP
  haveI : Module.Flat (MonoidAlgebra A P) V := Module.Flat.of_projective
  haveI : Module.Free (MonoidAlgebra A P) V := Module.free_of_flat_of_isLocalRing
  obtain ⟨B, instCRB, instLocalB, instAlgAB, hinj, hcharB, ζ, hζ⟩ :=
    exists_local_extension_with_primitiveRoot (A := A) (p := p) hm hm0
  letI : CommRing B := instCRB
  letI : IsLocalRing B := instLocalB
  letI : Algebra A B := instAlgAB
  haveI : CharP (IsLocalRing.ResidueField B) p := hcharB
  -- the coefficient ring map `A[P] → B[P]`
  letI algAPBP : Algebra (MonoidAlgebra A P) (MonoidAlgebra B P) :=
    (MonoidAlgebra.mapRingHom P (algebraMap A B)).toAlgebra
  -- base-changed module and operator
  haveI : Module.Finite (MonoidAlgebra B P)
      (TensorProduct (MonoidAlgebra A P) (MonoidAlgebra B P) V) := inferInstance
  haveI : Module.Projective (MonoidAlgebra B P)
      (TensorProduct (MonoidAlgebra A P) (MonoidAlgebra B P) V) := inferInstance
  have hwpow : (u.baseChange (MonoidAlgebra B P)) ^ m = 1 := by
    rw [← LinearMap.baseChange_pow, hu, LinearMap.baseChange_one]
  obtain ⟨b0, hb0⟩ :=
    trace_mem_algebraMap_range_of_pow_eq_one_local (B := B) (p := p) (P := P) hP
      (N := TensorProduct (MonoidAlgebra A P) (MonoidAlgebra B P) V) hm hm0
      (u.baseChange (MonoidAlgebra B P)) hwpow (ζ := ζ) hζ
  have htbc : LinearMap.trace (MonoidAlgebra B P) _ (u.baseChange (MonoidAlgebra B P))
      = algebraMap (MonoidAlgebra A P) (MonoidAlgebra B P)
          (LinearMap.trace (MonoidAlgebra A P) V u) :=
    LinearMap.trace_baseChange u (MonoidAlgebra B P)
  set τ : MonoidAlgebra A P := LinearMap.trace (MonoidAlgebra A P) V u with hτ
  have hcomb : algebraMap (MonoidAlgebra A P) (MonoidAlgebra B P) τ
      = algebraMap B (MonoidAlgebra B P) b0 := by rw [← htbc]; exact hb0
  refine ⟨τ 1, ?_⟩
  apply Finsupp.ext
  intro g
  by_cases hg : g = 1
  · subst hg
    rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self_apply,
      MonoidAlgebra.single_apply, if_pos rfl]
  · -- `τ g = 0` for `g ≠ 1`, then both sides are `0`
    have hcg : (algebraMap (MonoidAlgebra A P) (MonoidAlgebra B P) τ) g
        = (algebraMap B (MonoidAlgebra B P) b0) g := by rw [hcomb]
    have hL : (algebraMap (MonoidAlgebra A P) (MonoidAlgebra B P) τ) g
        = algebraMap A B (τ g) := by
      rw [RingHom.algebraMap_toAlgebra, MonoidAlgebra.mapRingHom_apply]
    have hR : (algebraMap B (MonoidAlgebra B P) b0) g = 0 := by
      rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self_apply,
        MonoidAlgebra.single_apply, if_neg (Ne.symm hg)]
    have hτg : τ g = 0 := hinj (by rw [map_zero, ← hL, hcg, hR])
    rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self_apply,
      MonoidAlgebra.single_apply, if_neg (Ne.symm hg), hτg]
