import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.ThompsonSmithNormalForm

noncomputable section

open LinearMap (BilinForm)
open scoped Pointwise TensorProduct

universe u v w

open LinearMap.BilinForm

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

/-- Helper for Exercise 15-15.2-6: if every Smith coefficient of a full-rank submodule is
divisible by `q`, then every element of the submodule is an explicit `q`-multiple in the ambient
free module. -/
theorem smithSubmodule_le_smul_top_of_coeff_dvd
    {n : ℕ} (N : Submodule ℤ (Fin n → ℤ))
    (hNrank : Module.finrank ℤ N = Module.finrank ℤ (Fin n → ℤ))
    (q : ℤ)
    (hcoeff_dvd :
      ∀ i : Fin n,
        q ∣
          Submodule.smithNormalFormCoeffs
            (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i)
    {x : Fin n → ℤ} (hx : x ∈ N) :
    ∃ w : Fin n → ℤ, x = q • w := by
  classical
  let u : Module.Basis (Fin n) ℤ (Fin n → ℤ) :=
    Submodule.smithNormalFormTopBasis (N := N) (Pi.basisFun ℤ (Fin n)) hNrank
  have hmap := smithNormalFormMapEqPiSpanCoeffs
    (N := N) (b := Pi.basisFun ℤ (Fin n)) (h := hNrank)
  have hxmap :
      u.equivFun x ∈
        Submodule.pi Set.univ
          (fun i : Fin n ↦
            Submodule.span ℤ
              ({Submodule.smithNormalFormCoeffs
                (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i} : Set ℤ)) := by
    have hxmap' : u.equivFun x ∈ N.map u.equivFun.toLinearMap :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hxmap'
    simpa [u] using hxmap'
  have hcoord_dvd : ∀ i : Fin n, q ∣ u.equivFun x i := by
    rw [Submodule.mem_pi] at hxmap
    intro i
    have hi :
        u.equivFun x i ∈
          Submodule.span ℤ
            ({Submodule.smithNormalFormCoeffs
              (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i} : Set ℤ) := by
      exact hxmap i (by simp)
    rcases Submodule.mem_span_singleton.mp hi with ⟨c, hc⟩
    rcases hcoeff_dvd i with ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    calc
      u.equivFun x i =
          c • Submodule.smithNormalFormCoeffs
            (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i := by
            simpa using hc.symm
      _ = c * (q * d) := by simp [hd]
      _ = q * (c * d) := by ring
  let wCoords : Fin n → ℤ := fun i ↦ Classical.choose (hcoord_dvd i)
  have hwCoords : ∀ i : Fin n, u.equivFun x i = q * wCoords i := by
    intro i
    simpa [wCoords] using Classical.choose_spec (hcoord_dvd i)
  refine ⟨u.equivFun.symm wCoords, ?_⟩
  apply u.equivFun.injective
  ext i
  calc
    u.equivFun x i = q * wCoords i := hwCoords i
    _ = (u.equivFun (q • u.equivFun.symm wCoords)) i := by
          symm
          rw [map_smul]
          rw [u.equivFun.apply_symm_apply]
          simp [smul_eq_mul]

/-- Helper for Exercise 15-15.2-6: if the coordinate pairing vector of `x` is a `q`-multiple,
then every pairing value against the lattice is divisible by `q`. -/
theorem pairing_values_dvd_of_pairingMap_eq_smul
    (B : BilinForm ℤ E)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (q : ℤ) {x : E} {w : Fin n → ℤ}
    (hw : pairingMap x = q • w) :
    ∀ y : E, q ∣ B x y := by
  intro y
  have hcoord : ∀ i : Fin n, B x (b i) = q * w i := by
    intro i
    have hi := congrArg (fun f : Fin n → ℤ ↦ f i) hw
    simpa [hpairing x i, smul_eq_mul] using hi
  rw [dvd_def]
  refine ⟨∑ i, (b.repr y i : ℤ) * w i, ?_⟩
  calc
    B x y = ∑ i, (b.repr y i : ℤ) * B x (b i) := by
      simpa using basisLinearForm_sum_repr (E := E) b (B x) y
    _ = ∑ i, (b.repr y i : ℤ) * (q * w i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hcoord i]
    _ = q * ∑ i, (b.repr y i : ℤ) * w i := by
          symm
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring

/-- Helper for Exercise 15-15.2-6: if the whole pairing image lies in `q` times the coordinate
lattice, then every value of the bilinear form is divisible by `q`. -/
theorem pairing_values_dvd_of_pairingImage_le_smul_top
    (B : BilinForm ℤ E)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (q : ℤ)
    (himage : ∀ x : E, ∃ w : Fin n → ℤ, pairingMap x = q • w) :
    ∀ x y : E, q ∣ B x y := by
  intro x y
  rcases himage x with ⟨w, hw⟩
  exact
    pairing_values_dvd_of_pairingMap_eq_smul
      (B := B) (b := b) pairingMap hpairing q hw y

/-- Helper for Exercise 15-15.2-6: a `p`-adic lower bound on all Smith coefficients makes all
pairing values divisible by the corresponding power of `p`. -/
theorem pairing_values_dvd_of_smithCoeffPadicVal_le
    (B : BilinForm ℤ E)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (hNrank : Module.finrank ℤ pairingMap.range = Module.finrank ℤ (Fin n → ℤ))
    (p k : ℕ) [Fact p.Prime]
    (hle :
      ∀ i : Fin n,
        k ≤
          padicValNat p
            (Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i))) :
    ∀ x y : E, ((p ^ k : ℕ) : ℤ) ∣ B x y := by
  have hcoeff_dvd :
      ∀ i : Fin n,
        ((p ^ k : ℕ) : ℤ) ∣
          Submodule.smithNormalFormCoeffs
            (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i := by
    intro i
    let a :=
      Submodule.smithNormalFormCoeffs
        (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i
    have ha_ne : Int.natAbs a ≠ 0 := by
      exact
        Int.natAbs_ne_zero.mpr
          (Submodule.smithNormalFormCoeffs_ne_zero
            (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i)
    have hnat : p ^ k ∣ Int.natAbs a :=
      (padicValNat_dvd_iff_le (p := p) (a := Int.natAbs a) (n := k) ha_ne).2
        (by simpa [a] using hle i)
    exact
      (Int.natAbs_dvd_natAbs
        (a := ((p ^ k : ℕ) : ℤ)) (b := a)).1 (by simpa using hnat)
  have himage :
      ∀ x : E, ∃ w : Fin n → ℤ, pairingMap x = ((p ^ k : ℕ) : ℤ) • w := by
    intro x
    exact
      smithSubmodule_le_smul_top_of_coeff_dvd
        (N := pairingMap.range) hNrank ((p ^ k : ℕ) : ℤ) hcoeff_dvd
        (LinearMap.mem_range_self pairingMap x)
  exact
    pairing_values_dvd_of_pairingImage_le_smul_top
      (B := B) (b := b) pairingMap hpairing ((p ^ k : ℕ) : ℤ) himage

/-- Helper for Exercise 15-15.2-6: if `p^k` divides an integer, then `p^(k+1)` divides its
`p`-multiple. -/
theorem int_prime_pow_succ_dvd_mul_of_pow_dvd
    (p k : ℕ) (a : ℤ)
    (h : ((p ^ k : ℕ) : ℤ) ∣ a) :
    ((p ^ (k + 1) : ℕ) : ℤ) ∣ (p : ℤ) * a := by
  rcases h with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hpows : ((p ^ (k + 1) : ℕ) : ℤ) = (p : ℤ) * ((p ^ k : ℕ) : ℤ) := by
    norm_num [pow_succ']
  calc
    (p : ℤ) * a = (p : ℤ) * (((p ^ k : ℕ) : ℤ) * c) := by rw [hc]
    _ = ((p ^ (k + 1) : ℕ) : ℤ) * c := by rw [hpows]; ring

/-- Helper for Exercise 15-15.2-6: a basis vector of a free integral module is not a `p`-multiple
when `p` is prime. -/
theorem basis_vector_not_mem_prime_mul
    {n : ℕ} (bE : Module.Basis (Fin n) ℤ E)
    (p : ℕ) [Fact p.Prime] (i : Fin n) :
    bE i ∉ (p •ℤ E) := by
  intro hi
  rw [show (p •ℤ E) = Representation.primeIdeal p • (⊤ : Submodule ℤ E) by rfl,
    Representation.primeIdeal, Submodule.ideal_span_singleton_smul] at hi
  rcases hi with ⟨y, hy, hy_eq⟩
  have hy : bE i = (p : ℤ) • y := by
    rw [← hy_eq]
    rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (p : ℤ)) (b := y)]
    simp [LinearMap.lsmul_apply]
  have hcoord := congrArg (fun z : E ↦ bE.coord i z) hy
  have hp_dvd_one : (p : ℤ) ∣ (1 : ℤ) := by
    refine ⟨bE.coord i y, ?_⟩
    simpa [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      map_smul, smul_eq_mul] using hcoord
  have hp_unit : IsUnit (p : ℤ) := isUnit_iff_dvd_one.mpr hp_dvd_one
  have hp_abs : Int.natAbs (p : ℤ) = 1 := Int.isUnit_iff_natAbs_eq.mp hp_unit
  have hp_one : p = 1 := by
    exact_mod_cast hp_abs
  exact (Fact.out : Nat.Prime p).ne_one hp_one

/-- Helper for Exercise 15-15.2-6: membership in `pE` can be represented by an explicit integral
`p`-multiple. This local copy avoids depending on a freshly-added bridge declaration through a
stale imported `.olean`. -/
theorem mem_prime_mul_iff_exists_prime_smul_for_fixedRange
    (p : ℕ) [Fact p.Prime] (x : E) :
    x ∈ (p •ℤ E) ↔ ∃ y : E, x = (p : ℤ) • y := by
  constructor
  · intro hx
    let primeRange : Submodule ℤ E :=
      Submodule.map ((LinearMap.lsmul ℤ E) (p : ℤ)) ⊤
    have hprime :
        (p •ℤ E) ≤ primeRange := by
      rw [show (p •ℤ E) = Representation.primeIdeal p • (⊤ : Submodule ℤ E) by rfl]
      rw [Submodule.smul_eq_map₂, Submodule.map₂]
      refine iSup_le ?_
      intro r
      intro z hz
      rcases hz with ⟨y, -, rfl⟩
      have hr : (r : ℤ) ∈ Representation.primeIdeal p := r.property
      change (r : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) at hr
      rw [Ideal.mem_span_singleton] at hr
      rcases hr with ⟨c, hc⟩
      refine ⟨c • y, by trivial, ?_⟩
      calc
        ((LinearMap.lsmul ℤ E) (p : ℤ)) (c • y)
            = c • (((LinearMap.lsmul ℤ E) (p : ℤ)) y) := by
                simpa only [LinearMap.map_smul_of_tower]
        _ = c • ((p : ℤ) • y) := by
              congr 1
              rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (p : ℤ)) (b := y)]
              simp [LinearMap.lsmul_apply]
        _ = (c * (p : ℤ)) • y := by
              simpa using (mul_zsmul y c (p : ℤ)).symm
        _ = (r : ℤ) • y := by
              rw [hc, mul_comm]
        _ = ((LinearMap.lsmul ℤ E) (r : ℤ)) y := by
              rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := r) (b := y)]
              simp [LinearMap.lsmul_apply]
    have hx_prime : x ∈ primeRange := hprime hx
    rcases hx_prime with ⟨y, -, hy⟩
    refine ⟨y, ?_⟩
    rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (p : ℤ)) (b := y)]
    simpa [primeRange, LinearMap.lsmul_apply] using hy.symm
  · rintro ⟨y, rfl⟩
    rw [show (p •ℤ E) = Representation.primeIdeal p • (⊤ : Submodule ℤ E) by rfl,
      Representation.primeIdeal, Submodule.ideal_span_singleton_smul]
    refine ⟨y, by simp, ?_⟩
    rw [← Int.cast_smul_eq_zsmul (R := ℤ) (n := (p : ℤ)) (b := y)]
    simp [LinearMap.lsmul_apply]

/-- Helper for Exercise 15-15.2-6: residue-field scalar multiplication on an integral reduction
class has an integral representative. This is the scalar-closure bridge needed for the radical
subrepresentation in the fixed-range argument. -/
theorem prime_reduction_class_residue_smul_exists_int_for_fixedRange
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime]
    (c : IsLocalRing.ResidueField (Localization.AtPrime (Representation.primeIdeal p)))
    (x : E) :
    ∃ m : ℤ,
      c • prime_reduction_class (ρ := ρ) p x =
        prime_reduction_class (ρ := ρ) p (m • x) := by
  let e :
      ℤ ⧸ Representation.primeIdeal p ≃+*
        Localization.AtPrime (Representation.primeIdeal p) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p)) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal (Representation.primeIdeal p)
      (Localization.AtPrime (Representation.primeIdeal p))
  obtain ⟨m, hm⟩ := Ideal.Quotient.mk_surjective (I := Representation.primeIdeal p) (e.symm c)
  refine ⟨m, ?_⟩
  let z : (ρ.primeStableLattice p).toSubmodule :=
    ⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1,
      Submodule.mem_top⟩
  have hc :
      c =
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p))))
          (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m) := by
    calc
      c = e (e.symm c) := by simp [e]
      _ = e (Ideal.Quotient.mk (Representation.primeIdeal p) m) := by rw [hm]
      _ =
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p))))
            (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m) := by
            simp [e]
  have hsmul :=
    (StableLattice.reduction_smul_mk
      (L := ρ.primeStableLattice p)
      (a := algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m)
      (y := z))
  change c • (Submodule.Quotient.mk z : (ρ.primeStableLattice p).reduction) =
    prime_reduction_class (ρ := ρ) p (m • x)
  rw [hc]
  refine hsmul.trans ?_
  unfold prime_reduction_class
  congr 1
  ext
  change
    (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m) •
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1 =
      LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) (m • x) 1
  change
    Localization.mk m (1 : (Representation.primeIdeal p).primeCompl) •
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1 =
      LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) (m • x) 1
  rw [← int_smul_eq_zsmul (h := (inferInstance : Module ℤ E)) (n := m) (x := x)]
  simpa using
    (LocalizedModule.mk_smul_mk (S := (Representation.primeIdeal p).primeCompl)
      (r := m) (m := x) (s := (1 : (Representation.primeIdeal p).primeCompl))
      (t := (1 : (Representation.primeIdeal p).primeCompl)))

/-- Helper for Exercise 15-15.2-6: two distinct basis vectors remain linearly independent after
passing to the canonical prime reduction. This is the concrete rank witness needed to recover
Serre's source hypothesis `n ≥ 2` from the stable-lattice reduction owner. -/
theorem prime_reduction_basis_class_not_mem_span
    {n : ℕ} (bE : Module.Basis (Fin n) ℤ E)
    (ρ : Representation ℤ G E) (p : ℕ) [Fact p.Prime] {i j : Fin n} (hij : i ≠ j) :
    prime_reduction_class (ρ := ρ) p (bE i) ∉
      Submodule.span
        (IsLocalRing.ResidueField (Localization.AtPrime (Representation.primeIdeal p)))
        ({prime_reduction_class (ρ := ρ) p (bE j)} :
          Set (ρ.primeStableLattice p).reduction) := by
  intro hmem
  rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
  obtain ⟨m, hm⟩ :=
    prime_reduction_class_residue_smul_exists_int_for_fixedRange
      (ρ := ρ) p c (bE j)
  have hclass :
      prime_reduction_class (ρ := ρ) p (m • bE j) =
        prime_reduction_class (ρ := ρ) p (bE i) :=
    hm.symm.trans hc
  have hdiff_mem : m • bE j - bE i ∈ (p •ℤ E) :=
    (prime_reduction_class_eq_iff_sub_mem_prime_mul
      (ρ := ρ) p (m • bE j) (bE i)).1 hclass
  rcases (mem_prime_mul_iff_exists_prime_smul_for_fixedRange
      (E := E) p (m • bE j - bE i)).1 hdiff_mem with ⟨y, hy⟩
  have hcoord := congrArg (fun z : E ↦ bE.coord i z) hy
  have hneg_one : (-1 : ℤ) = (p : ℤ) * bE.coord i y := by
    -- The `i`-th coordinate of `m e_j - e_i` is `-1`, while a `p`-multiple has
    -- `i`-th coordinate divisible by `p`.
    simpa [map_sub, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij, smul_eq_mul] using hcoord
  have hp_dvd_one : (p : ℤ) ∣ (1 : ℤ) := by
    refine ⟨-(bE.coord i y), ?_⟩
    calc
      (1 : ℤ) = -(-1 : ℤ) := by ring
      _ = -((p : ℤ) * bE.coord i y) := by rw [hneg_one]
      _ = (p : ℤ) * (-(bE.coord i y)) := by ring
  exact (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.1 hp_dvd_one)

/-- Helper for Exercise 15-15.2-6: Serre's rank hypothesis `n ≥ 2` rules out a trivial
prime-`2` reduction. -/
theorem hasNontrivialPrimeReduction_two_of_two_le_finrank
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions)
    (hE_rank : 2 ≤ Module.finrank ℤ E) :
    ρ.HasNontrivialPrimeReduction 2 := by
  intro htrivial
  let n := Module.finrank ℤ E
  let bE : Module.Basis (Fin n) ℤ E := Module.finBasis ℤ E
  let F₂ := IsLocalRing.ResidueField (Localization.AtPrime (Representation.primeIdeal 2))
  let V₂ := (ρ.primeStableLattice 2).reduction
  let σ := (ρ.primeStableLattice 2).reductionRepresentation
  let v0 : V₂ := prime_reduction_class (ρ := ρ) 2 (bE ⟨0, by omega⟩)
  let v1 : V₂ := prime_reduction_class (ρ := ρ) 2 (bE ⟨1, by omega⟩)
  let U : Subrepresentation σ :=
    { toSubmodule := Submodule.span F₂ ({v1} : Set V₂)
      apply_mem_toSubmodule := by
        intro g x hx
        have hfix : σ g x = x := by
          simpa [σ] using congrArg (fun f : Module.End F₂ V₂ ↦ f x) (htrivial.out g)
        simpa [hfix] using hx }
  have hv1_ne_zero : v1 ≠ 0 := by
    intro hv1
    exact
      basis_vector_not_mem_prime_mul (E := E) bE 2 ⟨1, by omega⟩
        ((prime_reduction_class_eq_zero_iff_mem_prime_mul
          (ρ := ρ) 2 (bE ⟨1, by omega⟩)).1 hv1)
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    have hv1_mem : v1 ∈ U.toSubmodule :=
      Submodule.subset_span (by simp [U, v1])
    have hv1_zero : v1 = 0 := by
      simpa [hU] using hv1_mem
    exact hv1_ne_zero hv1_zero
  have hU_top : U = ⊤ := by
    letI : σ.IsIrreducible := hρ.irreducible 2
    exact (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  have hv0_mem : v0 ∈ Submodule.span F₂ ({v1} : Set V₂) := by
    have : v0 ∈ U.toSubmodule := by
      simpa [hU_top] using (Submodule.mem_top : v0 ∈ (⊤ : Submodule F₂ V₂))
    simpa [U] using this
  exact
    (prime_reduction_basis_class_not_mem_span
      (E := E) bE ρ 2
      (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by
        intro h
        exact zero_ne_one (congrArg Fin.val h))) hv0_mem

/-- Helper for Exercise 15-15.2-6: every integral linear form on the coordinate pairing image is
represented by pairing against an integral vector built from the chosen basis. -/
theorem exists_pairing_testVector_for_linearForm
    (B : BilinForm ℤ E)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (φ : (Fin n → ℤ) →ₗ[ℤ] ℤ) :
    ∃ y : E, ∀ x : E, B x y = φ (pairingMap x) := by
  let c : Fin n → ℤ := fun i ↦ φ (Pi.basisFun ℤ (Fin n) i)
  let y : E := b.equivFun.symm c
  refine ⟨y, ?_⟩
  intro x
  have hycoord : ∀ i : Fin n, b.repr y i = c i := by
    intro i
    change b.coord i y = c i
    change b.coord i (b.equivFun.symm c) = c i
    exact Module.Basis.coord_equivFun_symm b i c
  calc
    B x y = ∑ i, (b.repr y i : ℤ) * B x (b i) := by
      simpa using basisLinearForm_sum_repr (E := E) b (B x) y
    _ = ∑ i, c i * pairingMap x i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hycoord i, hpairing x i]
    _ = φ (pairingMap x) := by
          simpa [c, mul_comm] using
            (basisLinearForm_sum_repr
              (E := Fin n → ℤ) (Pi.basisFun ℤ (Fin n)) φ (pairingMap x)).symm

/-- Helper for Exercise 15-15.2-6: divisibility of one Smith coefficient controls all pairings
against the matching Smith-domain basis vector. -/
theorem pairing_values_dvd_of_smithCoeff_dvd_at
    (B : BilinForm ℤ E)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (hpairing_injective : Function.Injective pairingMap)
    (hNrank : Module.finrank ℤ pairingMap.range = Module.finrank ℤ (Fin n → ℤ))
    (r : Fin n) (q : ℤ)
    (hdvd :
      q ∣
        Submodule.smithNormalFormCoeffs
          (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank r) :
    let u : Module.Basis (Fin n) ℤ (Fin n → ℤ) :=
      Submodule.smithNormalFormTopBasis
        (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank
    let ab : Module.Basis (Fin n) ℤ pairingMap.range :=
      Submodule.smithNormalFormBotBasis
        (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank
    let ePair : E ≃ₗ[ℤ] pairingMap.range :=
      LinearEquiv.ofInjective pairingMap hpairing_injective
    let xB : Module.Basis (Fin n) ℤ E := ab.map ePair.symm
    ∀ y : E, q ∣ B (xB r) y := by
  intro u ab ePair xB y
  let a : Fin n → ℤ :=
    Submodule.smithNormalFormCoeffs
      (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank
  have hpairingMap :
      pairingMap (xB r) = a r • u r := by
    change ((ePair (xB r) : pairingMap.range) : Fin n → ℤ) = a r • u r
    rw [show ePair (xB r) = ab r by simp [xB]]
    simpa [a, u, ab] using
      Submodule.smithNormalFormBotBasis_def
        (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank r
  rcases hdvd with ⟨d, hd⟩
  have hsmul : pairingMap (xB r) = q • (d • u r) := by
    calc
      pairingMap (xB r) = a r • u r := hpairingMap
      _ = (q * d) • u r := by rw [show a r = q * d by simpa [a] using hd]
      _ = q • (d • u r) := by simp [mul_smul]
  exact
    pairing_values_dvd_of_pairingMap_eq_smul
      (B := B) (b := b) pairingMap hpairing q hsmul y

/-- Helper for Exercise 15-15.2-6: the matching Smith-domain and Smith-test vectors pair to the
corresponding Smith coefficient. -/
theorem smithDomainBasis_pairing_testVector_eq_coeff
    (B : BilinForm ℤ E)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (hpairing_injective : Function.Injective pairingMap)
    (hNrank : Module.finrank ℤ pairingMap.range = Module.finrank ℤ (Fin n → ℤ))
    (r : Fin n) :
    let u : Module.Basis (Fin n) ℤ (Fin n → ℤ) :=
      Submodule.smithNormalFormTopBasis
        (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank
    let ab : Module.Basis (Fin n) ℤ pairingMap.range :=
      Submodule.smithNormalFormBotBasis
        (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank
    let ePair : E ≃ₗ[ℤ] pairingMap.range :=
      LinearEquiv.ofInjective pairingMap hpairing_injective
    let xB : Module.Basis (Fin n) ℤ E := ab.map ePair.symm
    ∃ y : E,
      B (xB r) y =
        Submodule.smithNormalFormCoeffs
          (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank r := by
  intro u ab ePair xB
  let φ : (Fin n → ℤ) →ₗ[ℤ] ℤ := u.coord r
  obtain ⟨y, hy⟩ :=
    exists_pairing_testVector_for_linearForm
      (B := B) (b := b) pairingMap hpairing φ
  refine ⟨y, ?_⟩
  let a : Fin n → ℤ :=
    Submodule.smithNormalFormCoeffs
      (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank
  have hpairingMap :
      pairingMap (xB r) = a r • u r := by
    change ((ePair (xB r) : pairingMap.range) : Fin n → ℤ) = a r • u r
    rw [show ePair (xB r) = ab r by simp [xB]]
    simpa [a, u, ab] using
      Submodule.smithNormalFormBotBasis_def
        (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank r
  calc
    B (xB r) y = φ (pairingMap (xB r)) := hy (xB r)
    _ = φ (a r • u r) := by rw [hpairingMap]
    _ = a r := by
          change (u.repr ((a r) • u r)) r = a r
          have hrepr :
              u.repr ((a r) • u r) = (a r) • Finsupp.single r (1 : ℤ) := by
            rw [map_smul, Module.Basis.repr_self]
          rw [hrepr]
          simp [Finsupp.smul_single, smul_eq_mul]

/-- Helper for Exercise 15-15.2-6: the fixed-range prime-local argument should force the
`p`-adic valuations of the Smith coefficients of the pairing image to agree. -/
theorem pairingImageSmithCoeffPadicVal_eq_fixedRange
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions)
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (hB_invariant : B.IsInvariantUnder ρ)
    (hB_pos : B.toQuadraticMap.PosDef)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (hpairing_injective : Function.Injective pairingMap)
    (p : ℕ) [Fact p.Prime] (i j : Fin n) :
    padicValNat p
        (Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := pairingMap.range) (Pi.basisFun ℤ (Fin n))
            (by
              simpa [Module.finrank_eq_card_basis b] using
                (LinearMap.finrank_range_of_inj
                  (R := ℤ) (f := pairingMap) hpairing_injective)) i)) =
      padicValNat p
        (Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := pairingMap.range) (Pi.basisFun ℤ (Fin n))
            (by
              simpa [Module.finrank_eq_card_basis b] using
                (LinearMap.finrank_range_of_inj
                  (R := ℤ) (f := pairingMap) hpairing_injective)) j)) := by
  classical
  let hNrank : Module.finrank ℤ pairingMap.range = Module.finrank ℤ (Fin n → ℤ) := by
    simpa [Module.finrank_eq_card_basis b] using
      (LinearMap.finrank_range_of_inj (R := ℤ) (f := pairingMap) hpairing_injective)
  let a : Fin n → ℤ :=
    Submodule.smithNormalFormCoeffs
      (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank
  let val : Fin n → ℕ := fun t ↦ padicValNat p (Int.natAbs (a t))
  obtain ⟨r, _hrmem, hrmin⟩ :
      ∃ r ∈ (Finset.univ : Finset (Fin n)),
        ∀ t ∈ (Finset.univ : Finset (Fin n)), val r ≤ val t :=
    Finset.exists_min_image (s := (Finset.univ : Finset (Fin n))) val
      ⟨i, by simp⟩
  let k : ℕ := val r
  have hle_min : ∀ t : Fin n, k ≤ val t := by
    intro t
    simpa [k] using hrmin t (by simp)
  let u : Module.Basis (Fin n) ℤ (Fin n → ℤ) :=
    Submodule.smithNormalFormTopBasis
      (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank
  let ab : Module.Basis (Fin n) ℤ pairingMap.range :=
    Submodule.smithNormalFormBotBasis
      (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank
  let ePair : E ≃ₗ[ℤ] pairingMap.range :=
    LinearEquiv.ofInjective pairingMap hpairing_injective
  let xB : Module.Basis (Fin n) ℤ E := ab.map ePair.symm
  have hB_dvd_k :
      ∀ x y : E, ((p ^ k : ℕ) : ℤ) ∣ B x y := by
    exact
      pairing_values_dvd_of_smithCoeffPadicVal_le
        (B := B) (b := b) pairingMap hpairing hNrank p k hle_min
  have hnot_lt : ∀ s : Fin n, ¬ k < val s := by
    intro s hs
    let qk : ℤ := ((p ^ k : ℕ) : ℤ)
    let qks : ℤ := ((p ^ (k + 1) : ℕ) : ℤ)
    have hs_succ : k + 1 ≤ val s := Nat.succ_le_of_lt hs
    have hs_coeff_dvd : qks ∣ a s := by
      have has_ne : Int.natAbs (a s) ≠ 0 := by
        exact
          Int.natAbs_ne_zero.mpr
            (Submodule.smithNormalFormCoeffs_ne_zero
              (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank s)
      have hnat : p ^ (k + 1) ∣ Int.natAbs (a s) :=
        (padicValNat_dvd_iff_le (p := p) (a := Int.natAbs (a s)) (n := k + 1)
          has_ne).2 (by simpa [val] using hs_succ)
      exact
        (Int.natAbs_dvd_natAbs
          (a := qks) (b := a s)).1 (by simpa [qks] using hnat)
    have hxs_dvd : ∀ y : E, qks ∣ B (xB s) y := by
      simpa [qks, u, ab, ePair, xB, a] using
        pairing_values_dvd_of_smithCoeff_dvd_at
          (B := B) (b := b) pairingMap hpairing hpairing_injective hNrank
          s qks hs_coeff_dvd
    let Fp := IsLocalRing.ResidueField (Localization.AtPrime (Representation.primeIdeal p))
    let σ := (ρ.primeStableLattice p).reductionRepresentation
    let Rad : Submodule Fp (ρ.primeStableLattice p).reduction :=
      { carrier := {ξ | ∃ x : E,
            ξ = prime_reduction_class (ρ := ρ) p x ∧
              ∀ y : E, qks ∣ B x y}
        zero_mem' := by
          refine ⟨0, ?_, ?_⟩
          · exact
              ((prime_reduction_class_eq_zero_iff_mem_prime_mul
                (ρ := ρ) p (0 : E)).2 (Submodule.zero_mem _)).symm
          · intro y
            simp [qks]
        add_mem' := by
          intro ξ η hξ hη
          rcases hξ with ⟨x, hx, hxdvd⟩
          rcases hη with ⟨z, hz, hzdvd⟩
          refine ⟨x + z, ?_, ?_⟩
          · rw [hx, hz, prime_reduction_class_add]
          · intro y
            rw [map_add]
            exact dvd_add (hxdvd y) (hzdvd y)
        smul_mem' := by
          intro c ξ hξ
          rcases hξ with ⟨x, hx, hxdvd⟩
          obtain ⟨m, hm⟩ :=
            prime_reduction_class_residue_smul_exists_int_for_fixedRange
              (ρ := ρ) p c x
          refine ⟨m • x, ?_, ?_⟩
          · rw [hx, hm]
          · intro y
            simpa [map_smul, smul_eq_mul] using dvd_mul_of_dvd_right (hxdvd y) m }
    let U : Subrepresentation σ :=
      { toSubmodule := Rad
        apply_mem_toSubmodule := by
          intro g ξ hξ
          rcases hξ with ⟨x, hx, hxdvd⟩
          refine ⟨ρ g x, ?_, ?_⟩
          · rw [hx, prime_reduction_class_map]
          · intro y
            have hB_pointwise := (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB_invariant
            have hgy : ρ g (ρ g⁻¹ y) = y := by
              have h := congrArg (fun f : E →ₗ[ℤ] E ↦ f y) (map_mul ρ g g⁻¹)
              simpa using h.symm
            have hpair : B (ρ g x) y = B x (ρ g⁻¹ y) := by
              simpa [hgy] using hB_pointwise g x (ρ g⁻¹ y)
            simpa [hpair] using hxdvd (ρ g⁻¹ y) }
    have hclass_s_mem : prime_reduction_class (ρ := ρ) p (xB s) ∈ U.toSubmodule := by
      exact ⟨xB s, rfl, hxs_dvd⟩
    have hclass_s_ne_zero : prime_reduction_class (ρ := ρ) p (xB s) ≠ 0 := by
      intro hzero
      have hx_mem :
          xB s ∈ (p •ℤ E) :=
        (prime_reduction_class_eq_zero_iff_mem_prime_mul (ρ := ρ) p (xB s)).1 hzero
      exact basis_vector_not_mem_prime_mul (E := E) xB p s hx_mem
    have hU_ne_bot : U ≠ ⊥ := by
      intro hU
      have hbotmem :
          prime_reduction_class (ρ := ρ) p (xB s) ∈
            (⊥ : Subrepresentation σ).toSubmodule := by
        simpa [hU] using hclass_s_mem
      exact hclass_s_ne_zero (by simpa using hbotmem)
    have hU_top : U = ⊤ := by
      letI : σ.IsIrreducible := hρ.irreducible p
      exact (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
    have hclass_r_not_mem :
        prime_reduction_class (ρ := ρ) p (xB r) ∉ U.toSubmodule := by
      intro hmem
      rcases hmem with ⟨z, hzclass, hzdvd⟩
      obtain ⟨y₀, hy₀⟩ :=
        smithDomainBasis_pairing_testVector_eq_coeff
          (B := B) (b := b) pairingMap hpairing hpairing_injective hNrank r
      have hdiff_mem :
          xB r - z ∈ (p •ℤ E) := by
        exact
          (prime_reduction_class_eq_iff_sub_mem_prime_mul
            (ρ := ρ) p (xB r) z).1 hzclass
      rcases (mem_prime_mul_iff_exists_prime_smul_for_fixedRange
          (E := E) p (xB r - z)).1 hdiff_mem with ⟨w, hw⟩
      have hw_dvd_k : qk ∣ B w y₀ := hB_dvd_k w y₀
      have hdiff_dvd : qks ∣ B (xB r - z) y₀ := by
        have hpw :
            qks ∣ B ((p : ℤ) • w) y₀ := by
          simpa [qk, qks, map_smul, smul_eq_mul] using
            int_prime_pow_succ_dvd_mul_of_pow_dvd p k (B w y₀) hw_dvd_k
        simpa [hw] using hpw
      have hxr_dvd : qks ∣ B (xB r) y₀ := by
        rw [show B (xB r) y₀ = B (xB r - z) y₀ + B z y₀ by
          calc
            B (xB r) y₀ = B ((xB r - z) + z) y₀ := by rw [sub_add_cancel]
            _ = B (xB r - z) y₀ + B z y₀ := by simp]
        exact dvd_add hdiff_dvd (hzdvd y₀)
      have har_dvd : qks ∣ a r := by
        simpa [u, ab, ePair, xB, a] using hy₀ ▸ hxr_dvd
      have har_nat_dvd : p ^ (k + 1) ∣ Int.natAbs (a r) := by
        have h := (Int.natAbs_dvd_natAbs (a := qks) (b := a r)).2 har_dvd
        simpa [qks] using h
      have har_ne : Int.natAbs (a r) ≠ 0 := by
        exact
          Int.natAbs_ne_zero.mpr
            (Submodule.smithNormalFormCoeffs_ne_zero
              (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank r)
      have hnot_dvd :
          ¬ p ^ (k + 1) ∣ Int.natAbs (a r) := by
        simpa [k, val] using
          (pow_succ_padicValNat_not_dvd (p := p) (n := Int.natAbs (a r)) har_ne)
      exact hnot_dvd har_nat_dvd
    exact
      hclass_r_not_mem
        (by
          have htopmem :
              prime_reduction_class (ρ := ρ) p (xB r) ∈
                (⊤ : Subrepresentation σ).toSubmodule := by
            exact Submodule.mem_top
          simpa [hU_top] using htopmem)
  have hval_eq : ∀ t : Fin n, val t = k := by
    intro t
    exact le_antisymm (le_of_not_gt (hnot_lt t)) (hle_min t)
  change val i = val j
  rw [hval_eq i, hval_eq j]

/-- Helper for Exercise 15-15.2-6: the prime-local flip-dual rigidity forces the fixed pairing
image to be the literal diagonal lattice `mℤ^n` for one positive integer `m`. -/
theorem pairingImage_eq_diagonal_of_primeLocalFlipDual
    (ρ : Representation ℤ G E) (hρ : ρ.HasSimplePrimeReductions)
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (hB_invariant : B.IsInvariantUnder ρ)
    (hB_pos : B.toQuadraticMap.PosDef)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (hpairing_injective : Function.Injective pairingMap) :
    ∃ m : ℕ,
      0 < m ∧
        pairingMap.range =
          Submodule.pi Set.univ
            (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ)) := by
  let hNrank : Module.finrank ℤ pairingMap.range = Module.finrank ℤ (Fin n → ℤ) := by
    -- Freeze the full-rank pairing image once so the primewise rigidity data can be globalized.
    simpa [Module.finrank_eq_card_basis b] using
      (LinearMap.finrank_range_of_inj (R := ℤ) (f := pairingMap) hpairing_injective)
  have hpadic :
      ∀ (p : ℕ) [Fact p.Prime] (i j : Fin n),
        padicValNat p
            (Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i)) =
          padicValNat p
            (Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank j)) := by
    -- Route correction: keep the prime-local Smith-valuation comparison private to this direct
    -- diagonal-range theorem; the main theorem only needs the resulting literal range equality.
    intro p _ i j
    exact
      pairingImageSmithCoeffPadicVal_eq_fixedRange
        (ρ := ρ) (hρ := hρ) (B := B) hB_symm hB_invariant hB_pos
        (b := b) pairingMap hpairing hpairing_injective p i j
  obtain ⟨m, hm, hcoeff⟩ :=
    pairingImageSmithCoeffs_constantNatAbs pairingMap.range hNrank hpadic
  refine ⟨m, hm, ?_⟩
  -- Once the Smith coefficients are constant, the in-file Smith-diagonal API gives the exact
  -- coordinatewise range description needed by the later divisibility/rescaling package.
  exact
    pairingImage_eq_diagonal_of_constantSmithCoeffs
      (N := pairingMap.range) hNrank m hcoeff

/-- Helper for Exercise 15-15.2-6: if the pairing image is the literal diagonal lattice `mℤ^n`,
then every pairing value is divisible by `m`. -/
theorem pairingValue_dvd_of_pairingImage_eq_diagonal
    (B : BilinForm ℤ E)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (m : ℕ)
    (hrange :
      pairingMap.range =
        Submodule.pi Set.univ
          (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ)))
    (x y : E) :
    (m : ℤ) ∣ B x y := by
  let M : Submodule ℤ (Fin n → ℤ) :=
    Submodule.pi Set.univ
      (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ))
  have hxmem : pairingMap x ∈ M := by
    -- The pairing coordinates of `x` lie in the explicit diagonal range by construction.
    have hxrange : pairingMap x ∈ pairingMap.range := LinearMap.mem_range_self pairingMap x
    simpa [M, hrange] using hxrange
  have hbasis_dvd : ∀ i : Fin n, (m : ℤ) ∣ B x (b i) := by
    intro i
    have hi_mem : pairingMap x i ∈ Submodule.span ℤ ({(m : ℤ)} : Set ℤ) := by
      -- Membership in the diagonal range reads coordinatewise as divisibility by `m`.
      rw [Submodule.mem_pi] at hxmem
      simpa [M] using hxmem i (by simp)
    rw [Submodule.mem_span_singleton] at hi_mem
    rcases hi_mem with ⟨a, ha⟩
    rw [dvd_def]
    refine ⟨a, ?_⟩
    simpa [hpairing x i, smul_eq_mul, mul_comm] using ha.symm
  let c : Fin n → ℤ := fun i ↦ Classical.choose (hbasis_dvd i)
  have hc : ∀ i : Fin n, B x (b i) = (m : ℤ) * c i := by
    intro i
    simpa [c] using Classical.choose_spec (hbasis_dvd i)
  rw [dvd_def]
  refine ⟨∑ i, (b.repr y i : ℤ) * c i, ?_⟩
  -- Expand the second argument in the chosen basis and factor out the common divisor `m`.
  calc
    B x y = ∑ i, (b.repr y i : ℤ) * B x (b i) := by
      simpa using basisLinearForm_sum_repr (E := E) b (B x) y
    _ = ∑ i, (b.repr y i : ℤ) * ((m : ℤ) * c i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hc i]
    _ = (m : ℤ) * ∑ i, (b.repr y i : ℤ) * c i := by
          symm
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring

end IntegralLatticeAmbient

end ThompsonExercise
