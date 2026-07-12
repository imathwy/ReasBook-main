import StacksProject_2024.Chap10.Lemma_10_161_16_Tate.BasicN2AndRoots
universe u

open Ideal
open IntermediateField Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.161.16 (Tate): a homeomorphism on prime spectra makes the fiber over a
fixed prime ideal a singleton. -/
lemma existsUnique_primesOver_of_isHomeomorph_comap
    {S : Type*} [CommRing S] [Algebra R S]
    {p : Ideal R} [p.IsPrime]
    (hhomeo : IsHomeomorph (PrimeSpectrum.comap (algebraMap R S))) :
    ∃! _q : p.primesOver S, True := by
  let pSpec : PrimeSpectrum R := ⟨p, inferInstance⟩
  obtain ⟨qSpec, hqSpec⟩ := hhomeo.surjective pSpec
  have hq_liesOver : qSpec.asIdeal.LiesOver p := by
    -- Transport the spectral preimage equality back to the contraction equality on ideals.
    refine (Ideal.liesOver_iff _ _).2 ?_
    simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hqSpec).symm
  refine ⟨Ideal.primesOver.mk p qSpec.asIdeal, trivial, ?_⟩
  intro q _
  apply Subtype.ext
  have hq : PrimeSpectrum.comap (algebraMap R S) ⟨q.1, inferInstance⟩ = pSpec := by
    -- Every prime in the fiber contracts back to the distinguished base prime `p`.
    apply PrimeSpectrum.ext
    simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using (q.1.over_def p).symm
  -- Injectivity of the spectral homeomorphism identifies any other point in the fiber with `qSpec`.
  exact congrArg PrimeSpectrum.asIdeal <|
    hhomeo.injective (hq.trans hqSpec.symm)

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): if a fixed power of every overfield element comes from the
fraction field, then the same power of every normalization element already comes from `R`. -/
lemma power_mem_range_of_integralClosure
    {n : ℕ}
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M]
    (hpow : ∀ z : M, z ^ n ∈ Set.range (algebraMap (FractionRing R) M)) :
    ∀ z : integralClosure R M, z ^ n ∈ Set.range (algebraMap R (integralClosure R M)) := by
  intro z
  rcases hpow (z : M) with ⟨a, ha⟩
  have ha_image_integral : IsIntegral R (algebraMap (FractionRing R) M a) := by
    -- The chosen power is integral because it is a power of a normalization element.
    rw [ha]
    exact z.2.pow n
  have ha_integral : IsIntegral R a := by
    -- Compare integrality on the source fraction field using injectivity of the scalar map.
    exact
      (isIntegral_algebraMap_iff (algebraMap (FractionRing R) M).injective).mp
        ha_image_integral
  obtain ⟨r, hr⟩ :=
    IsIntegrallyClosed.algebraMap_eq_of_integral (K := FractionRing R) ha_integral
  refine ⟨r, ?_⟩
  apply Subtype.ext
  -- Reinterpret the equality inside the ambient field `M`.
  change algebraMap R M r = (z : M) ^ n
  calc
    algebraMap R M r = algebraMap (FractionRing R) M a := by
      rw [← hr, IsScalarTower.algebraMap_apply R (FractionRing R) M]
    _ = (z : M) ^ n := ha

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.161.16 (Tate): for a prime over `(x)`, membership is equivalent to the
chosen power landing in the mapped principal ideal `(x)S`. -/
lemma mem_prime_over_span_singleton_iff_pow_mem_map
    {S : Type*} [CommRing S] [Algebra R S]
    {x : R} {n : ℕ} (hn : 0 < n)
    (q : (Ideal.span ({x} : Set R)).primesOver S)
    (hpow : ∀ z : S, z ^ n ∈ Set.range (algebraMap R S))
    (z : S) :
    z ∈ q.1 ↔ z ^ n ∈ Ideal.map (algebraMap R S) (Ideal.span ({x} : Set R)) := by
  constructor
  · intro hz
    rcases hpow z with ⟨r, hr⟩
    have hzpow : z ^ n ∈ q.1 := q.1.pow_mem_of_mem hz n hn
    have hr_mem : r ∈ Ideal.span ({x} : Set R) := by
      -- Contract the prime-membership statement back to the base ring.
      have hr_under : r ∈ q.1.under R := by
        simpa [Ideal.mem_comap, hr] using hzpow
      simpa [Ideal.under_def, q.2.2.over] using hr_under
    exact hr ▸ Ideal.mem_map_of_mem (algebraMap R S) hr_mem
  · intro hzpow
    have hmap_le_q :
        Ideal.map (algebraMap R S) (Ideal.span ({x} : Set R)) ≤ q.1 := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [Ideal.under_def] using le_of_eq q.2.2.over
    -- Primeness lets us recover `z ∈ q` from the powered membership.
    exact q.2.1.mem_of_pow_mem n (hmap_le_q hzpow)

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.161.16 (Tate): the chosen root generates an ideal contained in any prime
of the normalization lying over `(x)`. -/
lemma span_singleton_le_prime_over_span_singleton_of_pow_eq
    {S : Type*} [CommRing S] [Algebra R S]
    {x : R} {n : ℕ}
    (q : (Ideal.span ({x} : Set R)).primesOver S)
    {y : S} (hy : y ^ n = algebraMap R S x) :
    Ideal.span ({y} : Set S) ≤ q.1 := by
  refine (Ideal.span_singleton_le_iff_mem (I := q.1)).2 ?_
  have hy_pow_mem :
      y ^ n ∈ Ideal.map (algebraMap R S) (Ideal.span ({x} : Set R)) := by
    rw [hy]
    exact Ideal.mem_map_of_mem (algebraMap R S) (Ideal.mem_span_singleton_self x)
  have hmap_le_q :
      Ideal.map (algebraMap R S) (Ideal.span ({x} : Set R)) ≤ q.1 := by
    rw [Ideal.map_le_iff_le_comap]
    simpa [Ideal.under_def] using le_of_eq q.2.2.over
  -- Move the powered relation into `q`, then use primeness once.
  exact q.2.1.mem_of_pow_mem n (hmap_le_q hy_pow_mem)

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): in the normalization inside a field, if `z ^ n` lies in
the principal ideal generated by `y ^ n`, then `z` already lies in the principal ideal generated
by `y`. -/
lemma mem_span_singleton_of_pow_mem_span_singleton_pow
    {M : Type u} [Field M] [Algebra R M]
    {n : ℕ} (hn : 0 < n)
    {y z : integralClosure R M} (hy0 : (y : M) ≠ 0)
    (hz : z ^ n ∈ Ideal.span ({y ^ n} : Set (integralClosure R M))) :
    z ∈ Ideal.span ({y} : Set (integralClosure R M)) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz
  have hcM : (c : M) * (y : M) ^ n = (z : M) ^ n := by
    -- Proof comment: forget the normalization carrier and read the principal-ideal relation in
    -- the ambient field `M`.
    exact congrArg (fun s : integralClosure R M => (s : M)) hc
  have hy0n : (y : M) ^ n ≠ 0 := pow_ne_zero n hy0
  have hdiv : ((z : M) / y) * y = (z : M) := by
    field_simp [hy0]
  have hpow_eq : ((z : M) / y) ^ n = c := by
    apply mul_right_cancel₀ hy0n
    -- Proof comment: compare both sides after multiplying by `y ^ n`, where the field relation
    -- collapses to the given ideal-membership witness.
    calc
      ((z : M) / y) ^ n * (y : M) ^ n = (((z : M) / y) * y) ^ n := by
        rw [mul_pow]
      _ = (z : M) ^ n := by rw [hdiv]
      _ = (c : M) * (y : M) ^ n := by simpa [mul_comm] using hcM.symm
  have hpow_integral : IsIntegral R (((z : M) / y) ^ n) := by
    have hc_integral : IsIntegral R (c : M) := c.2
    simpa [hpow_eq] using hc_integral
  have hdiv_integral : IsIntegral R ((z : M) / y) :=
    IsIntegral.of_pow hn hpow_integral
  let w : integralClosure R M := ⟨(z : M) / y, hdiv_integral⟩
  refine Ideal.mem_span_singleton'.mpr ⟨w, ?_⟩
  apply Subtype.ext
  -- Proof comment: the integral quotient `w = z / y` gives the required factorization `z = w * y`.
  simpa [w, mul_comm] using hdiv

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.16 (Tate): the unique prime of the normalization over `(x)` is the
principal ideal generated by the chosen `p ^ e`-th root of `x`. -/
lemma prime_over_span_singleton_eq_span_root
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M]
    {x : R} (hx : x ≠ 0) (p : ℕ) [Fact p.Prime] (e : ℕ)
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M))
    (hpow : ∀ z : integralClosure R M, z ^ (p ^ e) ∈ Set.range (algebraMap R (integralClosure R M)))
    {y : integralClosure R M}
    (hy : y ^ (p ^ e) = algebraMap R (integralClosure R M) x) :
    q.1 = Ideal.span ({y} : Set (integralClosure R M)) := by
  have hy0 : (y : M) ≠ 0 := by
    intro hy0
    have hx0M : algebraMap R M x = 0 := by
      have hpow_pos : 0 < p ^ e := pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _
      have hyM : (y : M) ^ (p ^ e) = algebraMap R M x := by
        exact congrArg (fun z : integralClosure R M => (z : M)) hy
      -- Proof comment: if the chosen root vanished in the ambient field, the root equation would
      -- force `x` itself to vanish in `M`.
      rw [hy0, zero_pow hpow_pos.ne'] at hyM
      exact hyM.symm
    apply hx
    apply IsFractionRing.injective R (FractionRing R)
    apply (algebraMap (FractionRing R) M).injective
    simpa [IsScalarTower.algebraMap_apply R (FractionRing R) M] using hx0M
  have hspan_le :
      Ideal.span ({y} : Set (integralClosure R M)) ≤ q.1 := by
    -- Proof comment: the root equation gives the forward inclusion `(y) ⊆ q` exactly as in the
    -- source proof.
    exact
      span_singleton_le_prime_over_span_singleton_of_pow_eq
        (R := R) (S := integralClosure R M) (x := x) (n := p ^ e) q hy
  have hq_le :
      q.1 ≤ Ideal.span ({y} : Set (integralClosure R M)) := by
    intro z hz
    have hzpow_map :
        z ^ (p ^ e) ∈ Ideal.map (algebraMap R (integralClosure R M))
          (Ideal.span ({x} : Set R)) := by
      -- Proof comment: first rewrite membership in `q` as a powered membership in the mapped
      -- principal ideal `(x)S`.
      exact
        (mem_prime_over_span_singleton_iff_pow_mem_map
          (R := R) (S := integralClosure R M) (x := x) (n := p ^ e)
          (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) q hpow z).mp hz
    have hzpow_span :
        z ^ (p ^ e) ∈ Ideal.span ({y ^ (p ^ e)} : Set (integralClosure R M)) := by
      -- Proof comment: replace the mapped ideal `(x)S` by the principal ideal generated by the
      -- chosen root power `y ^ (p ^ e)`.
      simpa [Ideal.map_span, Set.image_singleton, hy] using hzpow_map
    exact
      mem_span_singleton_of_pow_mem_span_singleton_pow
        (R := R) (M := M) (n := p ^ e)
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hy0 hzpow_span
  exact le_antisymm hq_le hspan_le

end
