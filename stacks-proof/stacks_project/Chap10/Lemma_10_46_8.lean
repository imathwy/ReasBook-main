import Mathlib
import stacks_project.Chap10.Remark_10_18_5
import stacks_project.Chap10.Lemma_10_46_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open TensorProduct Algebra.TensorProduct
open PrimeSpectrum

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

/-- A ring homomorphism induces purely inseparable extensions on all residue fields. -/
def RingHom.HasPurelyInseparableResidueFieldExtensions (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S,
    let p : PrimeSpectrum R := comap f q
    let fκ := Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
    IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField

variable [Algebra R S]

local notation "f" => algebraMap R S

/-- Helper for Lemma 10.46.8: the fiber of the base-changed map over `p'` is the base change of
the original fiber over the contracted prime. -/
noncomputable def baseChange_fiber_algEquiv
    {R' : Type w} [CommRing R'] [Algebra R R']
    (p' : PrimeSpectrum R') :
    p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField]
      p'.asIdeal.ResidueField ⊗[(comap (algebraMap R R') p').asIdeal.ResidueField]
        ((comap (algebraMap R R') p').asIdeal.Fiber S) :=
  -- Proof comment: the new fiber is the scalar extension of the old fiber from `κ(p)` to
  -- `κ(p')`, so the canonical comparison is the standard `cancelBaseChange` composite.
  (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm

/-- Helper for Lemma 10.46.8: the residue field of the zero prime of a field is canonically the
field itself. -/
noncomputable def bot_residueField_algEquiv
    (K : Type*) [Field K] :
    ((⊥ : Ideal K).ResidueField) ≃ₐ[K] K :=
  let eQuot :
      (K ⧸ (⊥ : Ideal K)) ≃ₐ[K] ((⊥ : Ideal K).ResidueField) :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom K (K ⧸ (⊥ : Ideal K)) ((⊥ : Ideal K).ResidueField))
      (Ideal.bijective_algebraMap_quotient_residueField (⊥ : Ideal K))
  -- Replace the zero-prime residue field by the ordinary quotient `K ⧸ ⊥`.
  eQuot.symm.trans (AlgEquiv.quotientBot K K)

set_option maxHeartbeats 400000 in
/-- Helper for Lemma 10.46.8: tensoring a purely inseparable field extension with an arbitrary
field and then passing to a prime residue field still gives a purely inseparable extension of the
left field. -/
lemma tensor_prime_residueField_isPurelyInseparable
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [IsPurelyInseparable k K]
    (q : PrimeSpectrum (L ⊗[k] K)) :
    IsPurelyInseparable L q.asIdeal.ResidueField := by
  let qexp : ℕ := ringExpChar k
  letI : Nontrivial ((L ⊗[k] K) ⧸ q.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.2 q.2.1
  letI : ExpChar L qexp :=
    expChar_of_injective_ringHom (algebraMap k L).injective qexp
  -- Proof comment: use the power criterion for pure inseparability over `L`, and represent an
  -- element of the residue field as a fraction from the quotient domain `D`.
  rw [isPurelyInseparable_iff_pow_mem L qexp]
  intro y
  obtain ⟨a, b, hb, hfrac⟩ :=
    IsFractionRing.div_surjective ((L ⊗[k] K) ⧸ q.asIdeal) y
  have hpow_quotient :
      ∀ z : (L ⊗[k] K) ⧸ q.asIdeal,
        ∃ n : ℕ, z ^ qexp ^ n ∈ (algebraMap L ((L ⊗[k] K) ⧸ q.asIdeal)).range := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨n, hn⟩ :=
      IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
        (k := k) (K := K) (R := L) qexp x
    rcases hn with ⟨ℓ, hℓ⟩
    refine ⟨n, ?_⟩
    refine ⟨ℓ, ?_⟩
    -- Proof comment: push the tensor-product power witness through the quotient map.
    simpa [Ideal.Quotient.mk_algebraMap, map_pow] using
      congrArg (Ideal.Quotient.mk q.asIdeal) hℓ
  rcases hpow_quotient a with ⟨na, ha⟩
  rcases hpow_quotient b with ⟨nb, hbpow⟩
  rcases ha with ⟨a₀, ha₀⟩
  rcases hbpow with ⟨b₀, hb₀⟩
  refine ⟨na + nb, ?_⟩
  refine ⟨a₀ ^ qexp ^ nb / b₀ ^ qexp ^ na, ?_⟩
  have ha_map :
      algebraMap L q.asIdeal.ResidueField (a₀ ^ qexp ^ nb) =
        algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField
          (a ^ qexp ^ (na + nb)) := by
    -- Proof comment: raise the quotient witness for `a` to the complementary exponent.
    calc
      algebraMap L q.asIdeal.ResidueField (a₀ ^ qexp ^ nb)
          = (algebraMap L q.asIdeal.ResidueField a₀) ^ qexp ^ nb := by simp
      _ = (algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField
            (algebraMap L ((L ⊗[k] K) ⧸ q.asIdeal) a₀)) ^ qexp ^ nb := by
            rw [IsScalarTower.algebraMap_apply L ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField]
      _ = (algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField (a ^ qexp ^ na)) ^ qexp ^ nb := by
            rw [ha₀]
      _ = algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField
            ((a ^ qexp ^ na) ^ qexp ^ nb) := by simp
      _ = algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField
            (a ^ qexp ^ (na + nb)) := by
            rw [Nat.pow_add, pow_mul]
  have hb_map :
      algebraMap L q.asIdeal.ResidueField (b₀ ^ qexp ^ na) =
        algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField
          (b ^ qexp ^ (na + nb)) := by
    -- Proof comment: the same exponent synchronization works for the denominator.
    calc
      algebraMap L q.asIdeal.ResidueField (b₀ ^ qexp ^ na)
          = (algebraMap L q.asIdeal.ResidueField b₀) ^ qexp ^ na := by simp
      _ = (algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField
            (algebraMap L ((L ⊗[k] K) ⧸ q.asIdeal) b₀)) ^ qexp ^ na := by
            rw [IsScalarTower.algebraMap_apply L ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField]
      _ = (algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField (b ^ qexp ^ nb)) ^ qexp ^ na := by
            rw [hb₀]
      _ = algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField
            ((b ^ qexp ^ nb) ^ qexp ^ na) := by simp
      _ = algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField
            (b ^ qexp ^ (nb + na)) := by
            rw [Nat.pow_add, pow_mul]
      _ = algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField
            (b ^ qexp ^ (na + nb)) := by
            simp [Nat.add_comm]
  have hb_res_ne_zero :
      algebraMap L q.asIdeal.ResidueField (b₀ ^ qexp ^ na) ≠ 0 := by
    have hbD_ne_zero :
        algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField
          (b ^ qexp ^ (na + nb)) ≠ 0 := by
      have hbpow_ne_zero : b ^ qexp ^ (na + nb) ≠ 0 := by
        exact pow_ne_zero (qexp ^ (na + nb)) (mem_nonZeroDivisors_iff_ne_zero.mp hb)
      exact fun hbzero ↦ hbpow_ne_zero <|
        (IsFractionRing.to_map_eq_zero_iff
          (R := ((L ⊗[k] K) ⧸ q.asIdeal)) (K := q.asIdeal.ResidueField)).1 hbzero
    rw [hb_map]
    exact hbD_ne_zero
  -- Proof comment: after synchronizing exponents, the fraction power is the image of a quotient
  -- of two elements of `L`, so it lies in the base field image.
  calc
    algebraMap L q.asIdeal.ResidueField (a₀ ^ qexp ^ nb / b₀ ^ qexp ^ na)
        = algebraMap L q.asIdeal.ResidueField (a₀ ^ qexp ^ nb) /
            algebraMap L q.asIdeal.ResidueField (b₀ ^ qexp ^ na) := by simp
    _ = algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField (a ^ qexp ^ (na + nb)) /
          algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField (b ^ qexp ^ (na + nb)) := by
            rw [ha_map, hb_map]
    _ = (algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField a /
          algebraMap ((L ⊗[k] K) ⧸ q.asIdeal) q.asIdeal.ResidueField b) ^ qexp ^ (na + nb) := by
            rw [div_pow]
            simp [map_pow]
    _ = y ^ qexp ^ (na + nb) := by rw [hfrac]

/-- Helper for Lemma 10.46.8: a singleton fiber has locally nilpotent prime ideal because every
element of that prime belongs to all primes, hence to the nilradical. -/
lemma fiber_unique_prime_isLocallyNilpotent
    {F : Type*} [CommRing F] (r : PrimeSpectrum F)
    (hsub : Subsingleton (PrimeSpectrum F)) :
    r.asIdeal.IsLocallyNilpotent := by
  -- Proof comment: elementwise local nilpotence is enough, so test membership in every prime.
  rw [Ideal.isLocallyNilpotent_iff]
  intro x hx
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  let j : PrimeSpectrum F := ⟨J, hJ⟩
  have hj : j = r := hsub.elim j r
  have hJ : J = r.asIdeal := by
    simpa [j] using congrArg PrimeSpectrum.asIdeal hj
  simpa [hJ] using hx

/-- Helper for Lemma 10.46.8: in a ring with subsingleton prime spectrum, every prime ideal is
maximal. -/
lemma prime_isMaximal_of_subsingleton_primeSpectrum
    {F : Type*} [CommRing F] (r : PrimeSpectrum F)
    (hsub : Subsingleton (PrimeSpectrum F)) :
    r.asIdeal.IsMaximal := by
  -- Proof comment: any maximal ideal containing `r` is also a prime, so subsingleton-ness forces
  -- it to equal `r`.
  obtain ⟨m, hmMax, hrm⟩ := Ideal.exists_le_maximal r.asIdeal r.2.1
  let rm : PrimeSpectrum F := ⟨m, hmMax.isPrime⟩
  have hrm_eq : rm = r := hsub.elim rm r
  have hm : m = r.asIdeal := by
    simpa [rm] using congrArg PrimeSpectrum.asIdeal hrm_eq
  exact hm ▸ hmMax

/-- Helper for Lemma 10.46.8: if the prime spectrum of `F` is subsingleton, then the canonical
map from `F` to the residue field at the unique prime is surjective. -/
lemma algebraMap_residueField_surjective_of_subsingleton_primeSpectrum
    {F : Type*} [CommRing F] (r : PrimeSpectrum F)
    (hsub : Subsingleton (PrimeSpectrum F)) :
    Function.Surjective (algebraMap F r.asIdeal.ResidueField) := by
  -- Proof comment: subsingleton prime spectrum makes `r` maximal, and maximal ideals have
  -- surjective residue maps.
  letI : r.asIdeal.IsMaximal :=
    prime_isMaximal_of_subsingleton_primeSpectrum (F := F) r hsub
  simpa using Ideal.algebraMap_residueField_surjective (R := F) r.asIdeal

/-- Helper for Lemma 10.46.8: if `Spec(S) → Spec(R)` is injective, then every fiber ring
`κ(p) ⊗[R] S` has subsingleton prime spectrum. -/
lemma fiber_subsingleton_of_injective_comap
    (hinj : Function.Injective (comap f))
    (p : PrimeSpectrum R) :
    Subsingleton (PrimeSpectrum (p.asIdeal.Fiber S)) := by
  let e := PrimeSpectrum.preimageEquivFiber R S p
  refine ⟨fun r₁ r₂ ↦ ?_⟩
  apply e.symm.injective
  apply Subtype.ext
  -- Proof comment: two primes in the fiber contract to the same `p`, so injectivity forces
  -- equality upstairs.
  exact hinj <| by
    simpa using (e.symm r₁).2.trans (e.symm r₂).2.symm

/-- Helper for Lemma 10.46.8: the canonical tensor-lift to the upstairs residue field restricts to
the ordinary residue-field map on the `S`-factor. -/
lemma fiber_prime_tensor_lift_comp_includeRight
    (p : PrimeSpectrum R) (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
    let q : PrimeSpectrum S := qover.1
    let pToQ :
        p.asIdeal.ResidueField →ₐ[R] q.asIdeal.ResidueField :=
      Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S)
        (by simpa [q] using (congrArg PrimeSpectrum.asIdeal qover.2).symm)
    let liftR : p.asIdeal.Fiber S →+* q.asIdeal.ResidueField :=
      (Algebra.TensorProduct.lift pToQ (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)
        fun _ _ ↦ .all _ _).toRingHom
    liftR.comp (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom =
      algebraMap S q.asIdeal.ResidueField := by
  let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
  let q : PrimeSpectrum S := qover.1
  let pToQ :
      p.asIdeal.ResidueField →ₐ[R] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S)
      (by simpa [q] using (congrArg PrimeSpectrum.asIdeal qover.2).symm)
  let liftR : p.asIdeal.Fiber S →+* q.asIdeal.ResidueField :=
    (Algebra.TensorProduct.lift pToQ (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)
      fun _ _ ↦ .all _ _).toRingHom
  -- Proof comment: evaluate the tensor-lift on `1 ⊗ s`.
  ext s
  change (Algebra.TensorProduct.lift pToQ (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)
    (fun _ _ ↦ .all _ _)) (1 ⊗ₜ[R] s) = _
  rw [Algebra.TensorProduct.lift_tmul]
  change (pToQ 1) * (algebraMap S q.asIdeal.ResidueField s) =
    algebraMap S q.asIdeal.ResidueField s
  simp [pToQ]

/-- Helper for Lemma 10.46.8: the canonical tensor-lift to the upstairs residue field has kernel
equal to the chosen fiber prime. -/
lemma fiber_prime_tensor_lift_ker
    (p : PrimeSpectrum R) (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
    let q : PrimeSpectrum S := qover.1
    let pToQ :
        p.asIdeal.ResidueField →ₐ[R] q.asIdeal.ResidueField :=
      Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S)
        (by simpa [q] using (congrArg PrimeSpectrum.asIdeal qover.2).symm)
    let liftR : p.asIdeal.Fiber S →+* q.asIdeal.ResidueField :=
      (Algebra.TensorProduct.lift pToQ (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)
        fun _ _ ↦ .all _ _).toRingHom
    RingHom.ker liftR = r.asIdeal := by
  let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
  let q : PrimeSpectrum S := qover.1
  let pToQ :
      p.asIdeal.ResidueField →ₐ[R] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S)
      (by simpa [q] using (congrArg PrimeSpectrum.asIdeal qover.2).symm)
  let liftR : p.asIdeal.Fiber S →+* q.asIdeal.ResidueField :=
    (Algebra.TensorProduct.lift pToQ (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)
      fun _ _ ↦ .all _ _).toRingHom
  let e := PrimeSpectrum.preimageEquivFiber R S p
  have hEq : e qover = r := e.apply_symm_apply r
  -- Proof comment: `preimageEquivFiber` defines the corresponding fiber prime as this kernel.
  exact (congrArg PrimeSpectrum.asIdeal hEq).trans <| by
    simpa [qover, q, liftR] using
      (PrimeSpectrum.preimageEquivFiber_apply_asIdeal (R := R) (S := S) (p := p) qover)

/-- Helper for Lemma 10.46.8: contracting a fiber prime along `S → κ(p) ⊗[R] S` recovers the
corresponding prime of `S`. -/
lemma fiber_prime_comap_asIdeal
    (p : PrimeSpectrum R) (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
    let q : PrimeSpectrum S := qover.1
    Ideal.comap Algebra.TensorProduct.includeRight.toRingHom r.asIdeal = q.asIdeal := by
  let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
  let q : PrimeSpectrum S := qover.1
  -- Proof comment: `preimageEquivFiber` was defined using contraction along `includeRight`.
  change Ideal.comap Algebra.TensorProduct.includeRight.toRingHom r.asIdeal = q.asIdeal
  rfl

/-- Helper for Lemma 10.46.8: the canonical residue-field map from the upstairs prime to the
corresponding fiber prime is bijective. -/
lemma fiber_prime_residueField_map_bijective
    (p : PrimeSpectrum R) (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
    let q : PrimeSpectrum S := qover.1
    Function.Bijective
      (Ideal.ResidueField.mapₐ q.asIdeal r.asIdeal
        (Algebra.ofId S (p.asIdeal.Fiber S))
        (fiber_prime_comap_asIdeal (R := R) (S := S) p r).symm) := by
  let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
  let q : PrimeSpectrum S := qover.1
  -- Proof comment: this is the canonical base-change residue-field comparison from
  -- `Ideal.surjectiveOnStalks_residueField`.
  simpa using
    (p.asIdeal.surjectiveOnStalks_residueField.baseChange'.residueFieldMap_bijective
      q.asIdeal r.asIdeal
      (fiber_prime_comap_asIdeal (R := R) (S := S) p r).symm)

/-- Helper for Lemma 10.46.8: the geometric residue-field map from the upstairs prime to the
fiber prime is compatible with the base residue-field map from `κ(p)`. -/
lemma fiber_prime_residueField_map_comp_base_residueFieldMap
    (p : PrimeSpectrum R) (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
    let q : PrimeSpectrum S := qover.1
    (Ideal.ResidueField.map q.asIdeal r.asIdeal
      (Algebra.ofId S (p.asIdeal.Fiber S))
      (fiber_prime_comap_asIdeal (R := R) (S := S) p r).symm).comp
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S)
        (by simpa [q] using (congrArg PrimeSpectrum.asIdeal qover.2).symm)) =
      algebraMap p.asIdeal.ResidueField r.asIdeal.ResidueField := by
  let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
  let q : PrimeSpectrum S := qover.1
  -- Proof comment: both maps agree on the image of `R`, so `κ(p)`-extensionality closes the
  -- residue-field comparison.
  apply Ideal.ResidueField.ringHom_ext
  ext x
  simp only [RingHom.comp_apply]
  rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap]
  change algebraMap S r.asIdeal.ResidueField (f x) =
    algebraMap p.asIdeal.ResidueField r.asIdeal.ResidueField
      (algebraMap R p.asIdeal.ResidueField x)
  calc
    algebraMap S r.asIdeal.ResidueField (f x) = algebraMap R r.asIdeal.ResidueField x := by
      simpa [RingHom.comp_apply] using
        (RingHom.congr_fun (IsScalarTower.algebraMap_eq R S r.asIdeal.ResidueField) x).symm
    _ = algebraMap p.asIdeal.ResidueField r.asIdeal.ResidueField
        (algebraMap R p.asIdeal.ResidueField x) := by
      rw [IsScalarTower.algebraMap_apply R p.asIdeal.ResidueField r.asIdeal.ResidueField]

/-- Helper for Lemma 10.46.8: the residue field of a fiber prime is canonically the residue field
of the corresponding prime of `S` lying over `p`. -/
noncomputable def fiber_prime_residueField_algEquiv
    (p : PrimeSpectrum R) (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
    let q : PrimeSpectrum S := qover.1
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S)
        (by simpa [q] using (congrArg PrimeSpectrum.asIdeal qover.2).symm)).toAlgebra
    r.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] q.asIdeal.ResidueField := by
  let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
  let q : PrimeSpectrum S := qover.1
  let pToQ :
      p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S)
      (by simpa [q] using (congrArg PrimeSpectrum.asIdeal qover.2).symm)
  let qToR :
      q.asIdeal.ResidueField →+* r.asIdeal.ResidueField :=
    Ideal.ResidueField.map q.asIdeal r.asIdeal
      (Algebra.ofId S (p.asIdeal.Fiber S))
      (fiber_prime_comap_asIdeal (R := R) (S := S) p r).symm
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := pToQ.toAlgebra
  have hcomp :
      qToR.comp pToQ = algebraMap p.asIdeal.ResidueField r.asIdeal.ResidueField := by
    -- Proof comment: reuse the previous owner equality in the specialized notation of this proof.
    simpa [pToQ, qToR, q] using
      fiber_prime_residueField_map_comp_base_residueFieldMap (R := R) (S := S) p r
  let qToRₐ :
      q.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField] r.asIdeal.ResidueField :=
    { __ := qToR
      commutes' := fun x ↦ by
        -- Proof comment: the new composition identity is exactly the `κ(p)`-linearity witness.
        change qToR (pToQ x) = algebraMap p.asIdeal.ResidueField r.asIdeal.ResidueField x
        simpa [RingHom.comp_apply] using RingHom.congr_fun hcomp x }
  have hbij : Function.Bijective qToRₐ := by
    -- Proof comment: the algebra structure adds no new content; the underlying ring map is the
    -- already-bijective geometric residue-field comparison.
    simpa [qToRₐ, qToR] using fiber_prime_residueField_map_bijective (R := R) (S := S) p r
  -- Route correction: package the owner residue-field bijection directly as a `κ(p)`-algebra
  -- equivalence instead of comparing it to the tensor-lift presentation.
  exact (AlgEquiv.ofBijective qToRₐ hbij).symm

/-- Helper for Lemma 10.46.8: the tensor fiber maps canonically to the residue field of the
corresponding prime of `S` lying over `p`. -/
noncomputable def fiber_prime_residueField_algHom
    (p : PrimeSpectrum R) (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    let _ : Algebra p.asIdeal.ResidueField r.asIdeal.ResidueField :=
      ((algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField).comp
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))).toAlgebra
    p.asIdeal.Fiber S →ₐ[p.asIdeal.ResidueField] r.asIdeal.ResidueField :=
  let _ : Algebra p.asIdeal.ResidueField r.asIdeal.ResidueField :=
    ((algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField).comp
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))).toAlgebra
  { __ := algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField
    -- Proof comment: by construction the chosen `κ(p)`-algebra structure on `κ(r)` is the
    -- composite `κ(p) → F → κ(r)`, so linearity is definitional.
    commutes' := fun _ ↦ rfl }

/-- Helper for Lemma 10.46.8: after tensoring the residue-field map of a fiber prime, the
composite with the left algebra map is still the canonical left algebra map. -/
lemma fiber_prime_tensor_map_comp_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R']
    (p' : PrimeSpectrum R')
    (r : PrimeSpectrum ((PrimeSpectrum.comap (algebraMap R R') p').asIdeal.Fiber S)) :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
    let _ : Algebra p.asIdeal.ResidueField r.asIdeal.ResidueField :=
      ((algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField).comp
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))).toAlgebra
    let ψ := fiber_prime_residueField_algHom (R := R) (S := S) p r
    let g₂ :
        p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S →+*
          p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField :=
      (Algebra.TensorProduct.map
        (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).toRingHom
    g₂.comp
        (algebraMap p'.asIdeal.ResidueField
          (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S)) =
      algebraMap p'.asIdeal.ResidueField
        (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  let _ : Algebra p.asIdeal.ResidueField r.asIdeal.ResidueField :=
    ((algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField).comp
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))).toAlgebra
  let ψ := fiber_prime_residueField_algHom (R := R) (S := S) p r
  let g₂ :
      p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S →+*
        p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField :=
    (Algebra.TensorProduct.map
      (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).toRingHom
  -- Proof comment: `map_comp_includeLeft` already identifies the composite with the left tensor
  -- inclusion on the target, and that inclusion is the algebra map for the tensor product.
  change ((Algebra.TensorProduct.map
      (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).comp
        (Algebra.TensorProduct.includeLeft :
          p'.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
            p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S)).toRingHom =
    algebraMap p'.asIdeal.ResidueField
      (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField)
  rw [show ((Algebra.TensorProduct.map
      (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).comp
        (Algebra.TensorProduct.includeLeft :
          p'.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
            p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S)).toRingHom =
      ((Algebra.TensorProduct.includeLeft :
        p'.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
          p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField).comp
        (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField)).toRingHom by
        exact congrArg AlgHom.toRingHom
          (Algebra.TensorProduct.map_comp_includeLeft
            (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ)]
  ext x
  rfl

/-- Helper for Lemma 10.46.8: using the default tower map `κ(p) → F → κ(r)` in the tensor model,
the composite with the left algebra map is still the canonical left algebra map. -/
lemma fiber_prime_default_tensor_map_comp_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R']
    (p' : PrimeSpectrum R')
    (r : PrimeSpectrum ((PrimeSpectrum.comap (algebraMap R R') p').asIdeal.Fiber S)) :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
    let _ : Algebra p.asIdeal.ResidueField r.asIdeal.ResidueField :=
      ((algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField).comp
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))).toAlgebra
    let ψ :
        p.asIdeal.Fiber S →ₐ[p.asIdeal.ResidueField] r.asIdeal.ResidueField :=
      { __ := algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField
        commutes' := fun _ ↦ rfl }
    let g₂ :
        p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S →+*
          p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField :=
      (Algebra.TensorProduct.map
        (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).toRingHom
    g₂.comp
        (algebraMap p'.asIdeal.ResidueField
          (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S)) =
      algebraMap p'.asIdeal.ResidueField
        (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  let _ : Algebra p.asIdeal.ResidueField r.asIdeal.ResidueField :=
    ((algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField).comp
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))).toAlgebra
  let ψ :
      p.asIdeal.Fiber S →ₐ[p.asIdeal.ResidueField] r.asIdeal.ResidueField :=
    { __ := algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField
      commutes' := fun _ ↦ rfl }
  let g₂ :
      p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S →+*
        p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField :=
    (Algebra.TensorProduct.map
      (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).toRingHom
  -- Route correction: use the default tower map `κ(p) → F → κ(r)` directly, so the tensor
  -- composite is proved by a plain `map_comp_includeLeft` rewrite instead of algebra transport.
  change ((Algebra.TensorProduct.map
      (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).comp
        (Algebra.TensorProduct.includeLeft :
          p'.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
            p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S)).toRingHom =
    algebraMap p'.asIdeal.ResidueField
      (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField)
  rw [show ((Algebra.TensorProduct.map
      (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).comp
        (Algebra.TensorProduct.includeLeft :
          p'.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
            p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S)).toRingHom =
      ((Algebra.TensorProduct.includeLeft :
        p'.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
          p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField).comp
        (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField)).toRingHom by
        exact congrArg AlgHom.toRingHom
          (Algebra.TensorProduct.map_comp_includeLeft
            (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ)]
  ext x
  rfl

/-- Helper for Lemma 10.46.8: after rewriting the contracted prime to `p`, the owner residue-field
hypothesis for `q` is already the desired `κ(p)`-purely inseparable statement. -/
lemma residueField_isPurelyInseparable_of_comap_eq
    (hres : RingHom.HasPurelyInseparableResidueFieldExtensions f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : comap f q = p) :
    let fκ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
      Ideal.ResidueField.map p.asIdeal q.asIdeal f
        (by simpa using (congrArg PrimeSpectrum.asIdeal hq).symm)
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
    IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField := by
  subst p
  -- Proof comment: once the contracted prime is literally `comap f q`, this is exactly `hres q`.
  simpa using hres q

/-- Helper for Lemma 10.46.8: the purely inseparable residue-field hypothesis on `R → S`
transfers from the prime of `S` lying over `p` to the corresponding fiber prime. -/
lemma fiber_prime_isPurelyInseparable_of_hasPurelyInseparableResidueFieldExtensions
    (hres : RingHom.HasPurelyInseparableResidueFieldExtensions f)
    (p : PrimeSpectrum R) (r : PrimeSpectrum (p.asIdeal.Fiber S)) :
    let _ : Algebra p.asIdeal.ResidueField r.asIdeal.ResidueField :=
      ((algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField).comp
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))).toAlgebra
    IsPurelyInseparable p.asIdeal.ResidueField r.asIdeal.ResidueField := by
  let qover := (PrimeSpectrum.preimageEquivFiber R S p).symm r
  let q : PrimeSpectrum S := qover.1
  let fκ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal f
      (by simpa [q] using (congrArg PrimeSpectrum.asIdeal qover.2).symm)
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
  have hq :
      IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField := by
    -- Proof comment: rewrite the contracted prime in the source residue-field hypothesis.
    simpa [q, fκ] using
      (residueField_isPurelyInseparable_of_comap_eq
        (R := R) (S := S) (hres := hres) (p := p) (q := q) qover.2)
  let qToR :
      q.asIdeal.ResidueField →+* r.asIdeal.ResidueField :=
    Ideal.ResidueField.map q.asIdeal r.asIdeal
      (Algebra.ofId S (p.asIdeal.Fiber S))
      (fiber_prime_comap_asIdeal (R := R) (S := S) p r).symm
  letI : Algebra p.asIdeal.ResidueField r.asIdeal.ResidueField :=
    ((algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField).comp
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))).toAlgebra
  have hcomp :
      qToR.comp fκ = algebraMap p.asIdeal.ResidueField r.asIdeal.ResidueField := by
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp only [RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap]
    change algebraMap S r.asIdeal.ResidueField (f x) =
      algebraMap p.asIdeal.ResidueField r.asIdeal.ResidueField
        (algebraMap R p.asIdeal.ResidueField x)
    calc
      algebraMap S r.asIdeal.ResidueField (f x) = algebraMap R r.asIdeal.ResidueField x := by
        simpa [RingHom.comp_apply] using
          (RingHom.congr_fun (IsScalarTower.algebraMap_eq R S r.asIdeal.ResidueField) x).symm
      _ = algebraMap p.asIdeal.ResidueField r.asIdeal.ResidueField
          (algebraMap R p.asIdeal.ResidueField x) := by
        rfl
  let qToRₐ :
      q.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField] r.asIdeal.ResidueField :=
    { __ := qToR
      commutes' := fun x ↦ by
        -- Proof comment: the base residue-field map factors through the fiber residue field map.
        change qToR (fκ x) = algebraMap p.asIdeal.ResidueField r.asIdeal.ResidueField x
        simpa [RingHom.comp_apply] using RingHom.congr_fun hcomp x }
  have hbij : Function.Bijective qToRₐ := by
    simpa [qToRₐ, qToR] using fiber_prime_residueField_map_bijective (R := R) (S := S) p r
  let e : r.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] q.asIdeal.ResidueField :=
    (AlgEquiv.ofBijective qToRₐ hbij).symm
  -- Proof comment: transfer pure inseparability across the canonical residue-field equivalence
  -- between the upstairs prime and the fiber prime.
  exact e.isPurelyInseparable_iff.2 hq

/-- Helper for Lemma 10.46.8: an algebra equivalence identifies the residue fields of
corresponding primes. -/
noncomputable def residueField_algEquiv_of_algEquiv_for_corresponding_primes
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (q : PrimeSpectrum B) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap e.toRingHom q
    p.asIdeal.ResidueField ≃ₐ[K] q.asIdeal.ResidueField := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap e.toRingHom q
  let _ : Algebra K p.asIdeal.ResidueField := inferInstance
  let fκ : p.asIdeal.ResidueField →ₐ[K] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal e.toAlgHom rfl
  have hsurjStalks : e.toRingHom.SurjectiveOnStalks := e.toRingEquiv.surjectiveOnStalks
  have hbij : Function.Bijective fκ := by
    -- Proof comment: a ring equivalence is surjective on stalks, so the induced residue-field map
    -- at corresponding primes is bijective.
    simpa [fκ] using hsurjStalks.residueFieldMap_bijective p.asIdeal q.asIdeal rfl
  simpa [p, fκ] using AlgEquiv.ofBijective fκ hbij

/-- Helper for Lemma 10.46.8: tensoring a purely inseparable field extension with an arbitrary
field preserves bijectivity on spectra and purely inseparable residue-field extensions. -/
lemma tensor_purelyInseparableField_bijective_comap_and_hasPurelyInseparableResidueFieldExtensions
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [IsPurelyInseparable k K] :
    let g : L →+* L ⊗[k] K := algebraMap L (L ⊗[k] K)
    Function.Bijective (PrimeSpectrum.comap g) ∧
      g.HasPurelyInseparableResidueFieldExtensions := by
  let g : L →+* L ⊗[k] K := algebraMap L (L ⊗[k] K)
  have hhomeo : IsHomeomorph (PrimeSpectrum.comap g) := by
    simpa [g] using PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable
      (k := k) (K := K) (R := L)
  refine ⟨⟨hhomeo.injective, hhomeo.surjective⟩, ?_⟩
  intro q
  let p : PrimeSpectrum L := comap g q
  let fκ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal g rfl
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
  let _ : Algebra L q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (R := Localization.AtPrime q.asIdeal)
  have hp : p.asIdeal = (⊥ : Ideal L) := Ideal.eq_bot_of_prime (I := p.asIdeal)
  have hp' : p = (⟨⊥, inferInstance⟩ : PrimeSpectrum L) := by
    exact PrimeSpectrum.ext hp
  have hq :
      IsPurelyInseparable L q.asIdeal.ResidueField :=
    tensor_prime_residueField_isPurelyInseparable (k := k) (K := K) (L := L) q
  let eSource :
      p.asIdeal.ResidueField ≃ₐ[L] ((⊥ : Ideal L).ResidueField) :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ p.asIdeal (⊥ : Ideal L) (Algebra.ofId _ _) (by simpa using hp))
      ((RingHom.surjectiveOnStalks_of_surjective (fun x ↦ ⟨x, rfl⟩)).residueFieldMap_bijective
        p.asIdeal (⊥ : Ideal L) (by simpa using hp))
  have hp_source :
      IsPurelyInseparable L p.asIdeal.ResidueField := by
    -- Replace the contracted residue field by the zero-prime residue field of the base field.
    exact ((bot_residueField_algEquiv L).symm.trans eSource.symm).isPurelyInseparable
  have hfκ_comp :
      algebraMap L q.asIdeal.ResidueField =
        fκ.comp (algebraMap L p.asIdeal.ResidueField) := by
    ext a
    rw [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    rw [IsScalarTower.algebraMap_apply L (L ⊗[k] K) q.asIdeal.ResidueField]
  letI : IsScalarTower L p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' hfκ_comp
  have hpure :
      IsPurelyInseparable p.asIdeal.ResidueField q.asIdeal.ResidueField := by
    letI : IsPurelyInseparable L p.asIdeal.ResidueField := hp_source
    letI : IsPurelyInseparable L q.asIdeal.ResidueField := hq
    exact
      IsPurelyInseparable.tower_top L p.asIdeal.ResidueField
        q.asIdeal.ResidueField
  -- The contracted prime downstairs is the zero prime of the field `L`.
  simpa [p, hp'] using hpure

/-- Helper for Lemma 10.46.8: the prime spectrum of a field is a singleton. -/
lemma primeSpectrum_subsingleton_of_field
    (K : Type*) [Field K] :
    Subsingleton (PrimeSpectrum K) := by
  -- Proof comment: every prime ideal in a field is `⊥`, so the spectrum has one point.
  refine ⟨fun x y ↦ ?_⟩
  ext z
  simp [Ideal.eq_bot_of_prime (I := x.asIdeal), Ideal.eq_bot_of_prime (I := y.asIdeal)]

/-- Helper for Lemma 10.46.8: if `Spec(A) → Spec(K)` is bijective for a `K`-algebra `A`, then
`Spec(A)` is a singleton because `Spec(K)` is. -/
lemma primeSpectrum_subsingleton_of_bijective_comap_from_field
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (hbij : Function.Bijective (PrimeSpectrum.comap (algebraMap K A))) :
    Subsingleton (PrimeSpectrum A) := by
  let eK : Subsingleton (PrimeSpectrum K) := primeSpectrum_subsingleton_of_field K
  -- Proof comment: compare two primes after contracting them to the unique prime of the field.
  refine ⟨fun q₁ q₂ ↦ hbij.injective (eK.elim _ _)⟩

/-- Helper for Lemma 10.46.8: for a ring map out of a field, purely inseparable residue-field
extensions can be read directly over the base field rather than over the contracted residue field.
-/
lemma isPurelyInseparable_of_hasPurelyInseparableResidueFieldExtensions_from_field
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (q : PrimeSpectrum A)
    (hres :
      RingHom.HasPurelyInseparableResidueFieldExtensions (R := K) (S := A) (algebraMap K A)) :
    IsPurelyInseparable K q.asIdeal.ResidueField := by
  let p : PrimeSpectrum K := PrimeSpectrum.comap (algebraMap K A) q
  have hp :
      p = (⟨⊥, inferInstance⟩ : PrimeSpectrum K) := by
    exact (primeSpectrum_subsingleton_of_field K).elim _ _
  let fκ :
      ((⊥ : Ideal K).ResidueField) →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map (⊥ : Ideal K) q.asIdeal (algebraMap K A)
      (by simpa using (congrArg PrimeSpectrum.asIdeal hp).symm)
  let _ : Algebra ((⊥ : Ideal K).ResidueField) q.asIdeal.ResidueField := fκ.toAlgebra
  letI : IsScalarTower K ((⊥ : Ideal K).ResidueField) q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext x
      rw [RingHom.comp_apply]
      symm
      exact Ideal.ResidueField.map_algebraMap _ _ _ _ _
  letI : IsPurelyInseparable K ((⊥ : Ideal K).ResidueField) :=
    (bot_residueField_algEquiv K).symm.isPurelyInseparable
  letI : IsPurelyInseparable ((⊥ : Ideal K).ResidueField) q.asIdeal.ResidueField := by
    simpa [p, hp, fκ] using
      (residueField_isPurelyInseparable_of_comap_eq
        (R := K) (S := A) (hres := hres)
        (p := (⟨⊥, inferInstance⟩ : PrimeSpectrum K)) (q := q) hp)
  exact IsPurelyInseparable.trans K ((⊥ : Ideal K).ResidueField) q.asIdeal.ResidueField

/-- Helper for Lemma 10.46.8: for a ring map out of a field, pointwise pure inseparability of the
residue fields repackages into the owner predicate
`RingHom.HasPurelyInseparableResidueFieldExtensions`. -/
lemma hasPurelyInseparableResidueFieldExtensions_from_field_of_forall
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (hres : ∀ q : PrimeSpectrum A, IsPurelyInseparable K q.asIdeal.ResidueField) :
    RingHom.HasPurelyInseparableResidueFieldExtensions (R := K) (S := A) (algebraMap K A) := by
  intro q
  let p : PrimeSpectrum K := PrimeSpectrum.comap (algebraMap K A) q
  have hp : p.asIdeal = (⊥ : Ideal K) := Ideal.eq_bot_of_prime (I := p.asIdeal)
  let fκ :
      p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap K A) rfl
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := fκ.toAlgebra
  letI : IsScalarTower K p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext x
      rw [RingHom.comp_apply]
      symm
      exact Ideal.ResidueField.map_algebraMap _ _ _ _ _
  let eSource :
      p.asIdeal.ResidueField ≃ₐ[K] ((⊥ : Ideal K).ResidueField) :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ p.asIdeal (⊥ : Ideal K) (Algebra.ofId _ _) (by simpa using hp))
      ((RingHom.surjectiveOnStalks_of_surjective (fun x ↦ ⟨x, rfl⟩)).residueFieldMap_bijective
        p.asIdeal (⊥ : Ideal K) (by simpa using hp))
  have hpure_source :
      IsPurelyInseparable K p.asIdeal.ResidueField := by
    -- Proof comment: the contracted residue field is the zero-prime residue field of the field `K`.
    exact ((bot_residueField_algEquiv K).symm.trans eSource.symm).isPurelyInseparable
  letI : IsPurelyInseparable K p.asIdeal.ResidueField := hpure_source
  letI : IsPurelyInseparable K q.asIdeal.ResidueField := hres q
  -- Proof comment: once both residue fields are viewed as extensions of `K`, pure inseparability
  -- for `κ(p) → κ(q)` follows from the tower criterion.
  exact IsPurelyInseparable.tower_top K p.asIdeal.ResidueField q.asIdeal.ResidueField

/-- Helper for Lemma 10.46.8: the residue-field quotient map at a prime has kernel equal to that
prime ideal. -/
lemma ker_algebraMap_residueField_eq_prime
    {A : Type*} [CommRing A] (q : PrimeSpectrum A) :
    RingHom.ker (algebraMap A q.asIdeal.ResidueField) = q.asIdeal := by
  -- Proof comment: this is the canonical description of the kernel of the residue-field map.
  exact Ideal.ker_algebraMap_residueField (R := A) (I := q.asIdeal)

/-- Helper for Lemma 10.46.8: base-changing a surjective map with locally nilpotent kernel along a
field extension still gives bijective contraction on prime spectra and bijective residue-field
maps. -/
lemma fiber_tensor_map_bijective_comap_and_residueFieldMap_bijective_of_surjective_locallyNilpotent
    {k L F E : Type*} [Field k] [Field L] [CommRing F] [CommRing E]
    [Algebra k F] [Algebra k E] [Algebra k L]
    (ψ : F →ₐ[k] E)
    (hψsurj : Function.Surjective ψ)
    (hker : (RingHom.ker ψ.toRingHom).IsLocallyNilpotent) :
    let g₂ : L ⊗[k] F →+* L ⊗[k] E := (Algebra.TensorProduct.map (AlgHom.id k L) ψ).toRingHom
    Function.Bijective (PrimeSpectrum.comap g₂) ∧
      ∀ q₂ : PrimeSpectrum (L ⊗[k] E),
        Function.Bijective
          (Ideal.ResidueField.map (PrimeSpectrum.comap g₂ q₂).asIdeal q₂.asIdeal g₂ rfl) := by
  dsimp
  let g₂ : L ⊗[k] F →+* L ⊗[k] E :=
    (Algebra.TensorProduct.map (AlgHom.id k L) ψ).toRingHom
  have hidSurj : Function.Surjective (AlgHom.id k L) := fun x ↦ ⟨x, rfl⟩
  have hg₂surjAlg : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id k L) ψ) := by
    exact Algebra.TensorProduct.map_surjective (AlgHom.id k L) ψ hidSurj hψsurj
  have hg₂surj : Function.Surjective g₂ := by
    -- Proof comment: tensoring the identity on `L` with a surjective algebra map stays surjective.
    simpa [g₂] using hg₂surjAlg
  have hg₂ker : (RingHom.ker g₂).IsLocallyNilpotent := by
    -- Proof comment: the kernel is the extension of `ker ψ` along `includeRight`, so local
    -- nilpotence survives by the base-change kernel formula.
    rw [show RingHom.ker g₂ =
        Ideal.map
          (Algebra.TensorProduct.includeRight
            (R := k) (A := L) (B := F)).toRingHom
          (RingHom.ker ψ.toRingHom) by
        simpa [g₂] using
          (Algebra.TensorProduct.lTensor_ker (A := L) (g := ψ) hψsurj)]
    simpa using
      Ideal.map_isLocallyNilpotent
        (Algebra.TensorProduct.includeRight
          (R := k) (A := L) (B := F)).toRingHom hker
  have hhomeo : IsHomeomorph (PrimeSpectrum.comap g₂) := by
    -- Proof comment: surjectivity gives the power-in-range hypothesis with exponent `1`, and the
    -- locally nilpotent kernel is exactly the nilradical bound needed by `isHomeomorph_comap`.
    refine PrimeSpectrum.isHomeomorph_comap g₂ ?_ ?_
    · intro x
      obtain ⟨y, rfl⟩ := hg₂surj x
      refine ⟨1, Nat.one_pos, ?_⟩
      exact ⟨y, by simp⟩
    · simpa [Ideal.IsLocallyNilpotent] using hg₂ker
  have hsurjStalks : g₂.SurjectiveOnStalks :=
    RingHom.surjectiveOnStalks_of_surjective hg₂surj
  refine ⟨hhomeo.bijective, ?_⟩
  intro q₂
  -- Proof comment: surjective maps are surjective on stalks, so their residue-field maps are
  -- bijective at corresponding primes.
  exact hsurjStalks.residueFieldMap_bijective (PrimeSpectrum.comap g₂ q₂).asIdeal q₂.asIdeal rfl

/-- Helper for Lemma 10.46.8: if the middle map is bijective on spectra with bijective
residue-field maps, then the properties of bijective contraction and purely inseparable residue
field extensions descend from the composite to the first map. -/
lemma bijective_comap_and_hasPurelyInseparableResidueFieldExtensions_of_comp_bijective_middle
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (g₁ : A →+* B) (g₂ : B →+* C)
    (hmidBij : Function.Bijective (PrimeSpectrum.comap g₂))
    (hmidRes :
      ∀ q : PrimeSpectrum C,
        Function.Bijective
          (Ideal.ResidueField.map (PrimeSpectrum.comap g₂ q).asIdeal q.asIdeal g₂ rfl))
    (hcompBij : Function.Bijective (PrimeSpectrum.comap (g₂.comp g₁)))
    (hcompRes : (g₂.comp g₁).HasPurelyInseparableResidueFieldExtensions) :
    Function.Bijective (PrimeSpectrum.comap g₁) ∧
      g₁.HasPurelyInseparableResidueFieldExtensions := by
  have hg₁Bij : Function.Bijective (PrimeSpectrum.comap g₁) := by
    refine ⟨?_, ?_⟩
    · intro q₁ q₂ hq
      obtain ⟨q₁', hq₁'⟩ := hmidBij.2 q₁
      obtain ⟨q₂', hq₂'⟩ := hmidBij.2 q₂
      have hcompEq :
          PrimeSpectrum.comap (g₂.comp g₁) q₁' =
            PrimeSpectrum.comap (g₂.comp g₁) q₂' := by
        -- Proof comment: lift both primes through the bijective middle comap and compare them via
        -- the composite.
        calc
          PrimeSpectrum.comap (g₂.comp g₁) q₁'
              = PrimeSpectrum.comap g₁ q₁ := by
                rw [PrimeSpectrum.comap_comp_apply]
                simpa [hq₁']
          _ = PrimeSpectrum.comap g₁ q₂ := hq
          _ = PrimeSpectrum.comap (g₂.comp g₁) q₂' := by
                rw [PrimeSpectrum.comap_comp_apply]
                simpa [hq₂']
      have hq' : q₁' = q₂' := hcompBij.1 hcompEq
      -- Proof comment: once the chosen lifts agree, contracting them back along `g₂` recovers
      -- the original primes `q₁` and `q₂`.
      calc
        q₁ = PrimeSpectrum.comap g₂ q₁' := hq₁'.symm
        _ = PrimeSpectrum.comap g₂ q₂' := by simpa [hq']
        _ = q₂ := hq₂'
    · intro p
      obtain ⟨q₂, hq₂⟩ := hcompBij.2 p
      -- Proof comment: any prime in the image of the composite contracts through the middle to a
      -- prime in the image of `g₁`.
      refine ⟨PrimeSpectrum.comap g₂ q₂, ?_⟩
      simpa [PrimeSpectrum.comap_comp_apply] using hq₂
  refine ⟨hg₁Bij, ?_⟩
  intro q
  obtain ⟨q₂, hq₂⟩ := hmidBij.2 q
  let p : PrimeSpectrum A := PrimeSpectrum.comap g₁ q
  let pToQ :
      p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q.asIdeal g₁ rfl
  let pToQ₂ :
      p.asIdeal.ResidueField →+* q₂.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal q₂.asIdeal (g₂.comp g₁)
      (by
        cases hq₂
        rfl)
  let qToQ₂ :
      q.asIdeal.ResidueField →+* q₂.asIdeal.ResidueField :=
    Ideal.ResidueField.map q.asIdeal q₂.asIdeal g₂
      (by
        cases hq₂
        rfl)
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := pToQ.toAlgebra
  let _ : Algebra p.asIdeal.ResidueField q₂.asIdeal.ResidueField := pToQ₂.toAlgebra
  have hcomp :
      qToQ₂.comp pToQ = pToQ₂ := by
    -- Proof comment: both residue-field maps are induced from the same composite ring map
    -- `A → C`, so they agree on the image of `A`.
    apply Ideal.ResidueField.ringHom_ext
    ext x
    simp [pToQ, pToQ₂, qToQ₂, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
  let qToQ₂ₐ :
      q.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField] q₂.asIdeal.ResidueField :=
    { __ := qToQ₂
      commutes' := fun x ↦ by
        change qToQ₂ (pToQ x) = algebraMap p.asIdeal.ResidueField q₂.asIdeal.ResidueField x
        simpa [RingHom.comp_apply, pToQ₂] using RingHom.congr_fun hcomp x }
  have hqToQ₂_bij : Function.Bijective qToQ₂ₐ := by
    -- Proof comment: the middle residue-field map is bijective by hypothesis at the chosen prime
    -- `q₂` lying over `q`.
    cases hq₂
    simpa [qToQ₂ₐ, qToQ₂] using hmidRes q₂
  have hcompPure :
      IsPurelyInseparable p.asIdeal.ResidueField q₂.asIdeal.ResidueField := by
    -- Proof comment: after identifying the contracted prime of `q₂` with `p`, the composite
    -- hypothesis is exactly the pure-inseparability statement for `κ(p) → κ(q₂)`.
    cases hq₂
    simpa [p, pToQ₂, PrimeSpectrum.comap_comp_apply] using hcompRes q₂
  letI : IsPurelyInseparable p.asIdeal.ResidueField q₂.asIdeal.ResidueField := hcompPure
  -- Proof comment: transport pure inseparability back across the residue-field equivalence coming
  -- from the bijective middle map.
  exact (AlgEquiv.ofBijective qToQ₂ₐ hqToQ₂_bij).symm.isPurelyInseparable

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 400000 in
/-- Helper for Lemma 10.46.8: when the original fiber over `p` is nonempty, scalar extension from
`κ(p)` to `κ(p')` preserves the singleton-fiber and purely inseparable residue-field package. -/
lemma fiber_baseChange_bijective_comap_and_hasPurelyInseparableResidueFieldExtensions_of_nonempty
    {R' : Type w} [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (PrimeSpectrum.comap f))
    (hres : RingHom.HasPurelyInseparableResidueFieldExtensions f)
    (p' : PrimeSpectrum R')
    (hnonempty :
      Nonempty (PrimeSpectrum ((PrimeSpectrum.comap (algebraMap R R') p').asIdeal.Fiber S))) :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
    let B : Type _ := p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S
    let _ : CommRing B := inferInstance
    let g₁ : p'.asIdeal.ResidueField →+*
        B :=
      algebraMap _ _
    Function.Bijective (PrimeSpectrum.comap g₁) ∧
      RingHom.HasPurelyInseparableResidueFieldExtensions g₁ := by
  classical
  dsimp
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  let r : PrimeSpectrum (p.asIdeal.Fiber S) := Classical.choice hnonempty
  let hsub : Subsingleton (PrimeSpectrum (p.asIdeal.Fiber S)) :=
    fiber_subsingleton_of_injective_comap (R := R) (S := S) hinj p
  letI : Algebra p.asIdeal.ResidueField r.asIdeal.ResidueField :=
    ((algebraMap (p.asIdeal.Fiber S) r.asIdeal.ResidueField).comp
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))).toAlgebra
  let ψ := fiber_prime_residueField_algHom (R := R) (S := S) p r
  let g₁ :
      p'.asIdeal.ResidueField →+*
        p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S :=
    algebraMap _ _
  let g₂ :
      p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S →+*
        p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField :=
    (Algebra.TensorProduct.map
      (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).toRingHom
  have hψsurj : Function.Surjective ψ := by
    -- Proof comment: the unique old fiber prime is maximal, so its residue-field quotient map is
    -- surjective.
    simpa [ψ] using
      algebraMap_residueField_surjective_of_subsingleton_primeSpectrum
        (F := p.asIdeal.Fiber S) r hsub
  have hψker :
      (RingHom.ker ψ.toRingHom).IsLocallyNilpotent := by
    -- Proof comment: singleton prime spectrum identifies the kernel with the unique prime, which
    -- is locally nilpotent by Remark 10.18.5/Lemma 10.25.1 on the fiber side.
    simpa [ψ, fiber_prime_residueField_algHom, ker_algebraMap_residueField_eq_prime]
      using fiber_unique_prime_isLocallyNilpotent
        (F := p.asIdeal.Fiber S) r hsub
  have hmid :
      Function.Bijective (PrimeSpectrum.comap g₂) ∧
        ∀ q₂ :
            PrimeSpectrum
              (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField),
          Function.Bijective
            (Ideal.ResidueField.map (PrimeSpectrum.comap g₂ q₂).asIdeal q₂.asIdeal g₂ rfl) := by
    -- Proof comment: tensoring the surjective locally nilpotent quotient map `F → κ(r)` gives
    -- the middle morphism in the source proof.
    have hmid' :=
      fiber_tensor_map_bijective_comap_and_residueFieldMap_bijective_of_surjective_locallyNilpotent
        (k := p.asIdeal.ResidueField) (L := p'.asIdeal.ResidueField)
        (F := p.asIdeal.Fiber S) (E := r.asIdeal.ResidueField) ψ hψsurj hψker
    dsimp only at hmid'
    rcases hmid' with ⟨hbij, hresMap⟩
    refine ⟨?_, ?_⟩
    · change Function.Bijective
          (PrimeSpectrum.comap
            ((Algebra.TensorProduct.map
              (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).toRingHom))
      exact hbij
    · intro q₂
      change Function.Bijective
        (Ideal.ResidueField.map
          (PrimeSpectrum.comap
            ((Algebra.TensorProduct.map
              (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).toRingHom) q₂).asIdeal
          q₂.asIdeal
          ((Algebra.TensorProduct.map
            (AlgHom.id p.asIdeal.ResidueField p'.asIdeal.ResidueField) ψ).toRingHom)
          rfl)
      exact hresMap q₂
  have hrPure :=
    fiber_prime_isPurelyInseparable_of_hasPurelyInseparableResidueFieldExtensions
      (R := R) (S := S) (hres := hres) p r
  letI : IsPurelyInseparable p.asIdeal.ResidueField r.asIdeal.ResidueField := by
    simpa using hrPure
  have hcompTensor :
      Function.Bijective
          (PrimeSpectrum.comap
            (algebraMap p'.asIdeal.ResidueField
              (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField))) ∧
        RingHom.HasPurelyInseparableResidueFieldExtensions
          (algebraMap p'.asIdeal.ResidueField
            (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField)) := by
    -- Proof comment: once `κ(p) → κ(r)` is purely inseparable, the field case applies after
    -- extending scalars from `κ(p)` to `κ(p')`.
    exact
      tensor_purelyInseparableField_bijective_comap_and_hasPurelyInseparableResidueFieldExtensions
        (k := p.asIdeal.ResidueField) (K := r.asIdeal.ResidueField)
        (L := p'.asIdeal.ResidueField)
  have hcompEq :
      g₂.comp g₁ =
        algebraMap p'.asIdeal.ResidueField
          (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] r.asIdeal.ResidueField) := by
    -- Proof comment: the tensor comparison `g₂` still sends the left factor through the canonical
    -- tensor inclusion, so the composite is the usual base field map.
    simpa [p, g₁, g₂, ψ] using
      fiber_prime_default_tensor_map_comp_algebraMap
        (R := R) (S := S) p' r
  have hcompBij :
      Function.Bijective (PrimeSpectrum.comap (g₂.comp g₁)) := by
    rw [hcompEq]
    exact hcompTensor.1
  have hcompRes :
      RingHom.HasPurelyInseparableResidueFieldExtensions (g₂.comp g₁) := by
    rw [hcompEq]
    exact hcompTensor.2
  -- Proof comment: descend the fiber package from the composite `κ(p') → κ(p') ⊗ κ(r)` across
  -- the middle map `κ(p') ⊗ F → κ(p') ⊗ κ(r)`.
  exact
    bijective_comap_and_hasPurelyInseparableResidueFieldExtensions_of_comp_bijective_middle
      g₁ g₂ hmid.1 hmid.2 hcompBij hcompRes

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 400000 in
/-- Helper for Lemma 10.46.8: every fiber of the base-changed map is a singleton, and the residue
field of each fiber prime is purely inseparable over the downstairs residue field. -/
lemma baseChange_fiber_subsingleton_and_residueFieldPure
    {R' : Type w} [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (PrimeSpectrum.comap f))
    (hres : RingHom.HasPurelyInseparableResidueFieldExtensions f)
    (p' : PrimeSpectrum R') :
    let B : Type _ := p'.asIdeal.Fiber (R' ⊗[R] S)
    let _ : CommRing B := inferInstance
    let g : p'.asIdeal.ResidueField →+* B := algebraMap _ _
    Subsingleton (PrimeSpectrum B) ∧
      RingHom.HasPurelyInseparableResidueFieldExtensions g := by
  classical
  dsimp
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  let C : Type _ :=
    p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S
  let _ : CommRing C := inferInstance
  let gC : p'.asIdeal.ResidueField →+* C := algebraMap _ _
  let e :
      p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField] C :=
    baseChange_fiber_algEquiv (R := R) (S := S) p'
  let eSpec :
      PrimeSpectrum (p'.asIdeal.Fiber (R' ⊗[R] S)) ≃ PrimeSpectrum C :=
    PrimeSpectrum.comapEquiv e.toRingEquiv
  by_cases hnonempty : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S))
  · have hC :
        Function.Bijective (PrimeSpectrum.comap gC) ∧
          RingHom.HasPurelyInseparableResidueFieldExtensions gC := by
      simpa [p, C, gC] using
        fiber_baseChange_bijective_comap_and_hasPurelyInseparableResidueFieldExtensions_of_nonempty
          (R := R) (S := S) (R' := R') hinj hres p' hnonempty
    have hsubC : Subsingleton (PrimeSpectrum C) :=
      primeSpectrum_subsingleton_of_bijective_comap_from_field
        (K := p'.asIdeal.ResidueField) (A := C) hC.1
    refine ⟨?_, ?_⟩
    · -- Proof comment: transport the singleton-spectrum statement back across the base-change
      -- fiber equivalence.
      refine ⟨fun q₁ q₂ ↦ ?_⟩
      exact eSpec.injective (hsubC.elim (eSpec q₁) (eSpec q₂))
    · -- Proof comment: over the field `κ(p')`, pointwise pure inseparability repackages into the
      -- owner predicate for the base-changed fiber map.
      refine hasPurelyInseparableResidueFieldExtensions_from_field_of_forall ?_
      intro qB
      let qC : PrimeSpectrum C := eSpec qB
      letI : Algebra p'.asIdeal.ResidueField qC.asIdeal.ResidueField :=
        IsLocalRing.ResidueField.algebra (R := Localization.AtPrime qC.asIdeal)
      have hqC :
          IsPurelyInseparable p'.asIdeal.ResidueField qC.asIdeal.ResidueField := by
        simpa using
          isPurelyInseparable_of_hasPurelyInseparableResidueFieldExtensions_from_field qC hC.2
      have hqB :
          PrimeSpectrum.comap e.toRingHom qC = qB :=
        eSpec.symm_apply_apply qB
      let pB : PrimeSpectrum (p'.asIdeal.Fiber (R' ⊗[R] S)) :=
        PrimeSpectrum.comap e.toRingHom qC
      have hpB : pB = qB := by
        simpa [pB] using hqB
      letI : Algebra p'.asIdeal.ResidueField pB.asIdeal.ResidueField :=
        IsLocalRing.ResidueField.algebra (R := Localization.AtPrime pB.asIdeal)
      have eRF0 :
          pB.asIdeal.ResidueField ≃ₐ[p'.asIdeal.ResidueField] qC.asIdeal.ResidueField := by
        -- Proof comment: `qB` and `qC` are corresponding primes under the fiber algebra equivalence.
        simpa [pB] using
          (residueField_algEquiv_of_algEquiv_for_corresponding_primes
            (K := p'.asIdeal.ResidueField)
            (A := p'.asIdeal.Fiber (R' ⊗[R] S)) (B := C) e qC)
      -- Proof comment: corresponding primes under the fiber algebra equivalence have equivalent
      -- residue fields, so pure inseparability transfers back to the original base-changed fiber.
      have hpBPure :
          IsPurelyInseparable p'.asIdeal.ResidueField pB.asIdeal.ResidueField := by
        exact eRF0.isPurelyInseparable_iff.2 hqC
      exact Eq.mp (by rw [← hpB]) hpBPure
  · refine ⟨?_, ?_⟩
    · -- Proof comment: if the original fiber were empty, any prime in the base-changed fiber
      -- would contract to a prime in the old fiber, contradiction.
      refine ⟨fun q₁ _ ↦ ?_⟩
      let qC : PrimeSpectrum C := eSpec q₁
      have : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) := by
        exact ⟨PrimeSpectrum.comap (algebraMap (p.asIdeal.Fiber S) C) qC⟩
      exact (hnonempty this).elim
    · intro qB
      let qC : PrimeSpectrum C := eSpec qB
      have : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) := by
        exact ⟨PrimeSpectrum.comap (algebraMap (p.asIdeal.Fiber S) C) qC⟩
      exact (hnonempty this).elim

/-
Layering for this item:
* source-facing: the base-change stability of injectivity on `Spec` together with purely
  inseparable residue-field extensions;
* core/canonical owner: the spectral map `PrimeSpectrum.comap f` and the predicate
  `RingHom.HasPurelyInseparableResidueFieldExtensions f`;
* bridge/view: the induced residue-field maps
  `Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl`.
-/

-- Proof sketch: inspect each fiber of `Spec (R' ⊗[R] S) → Spec R'` via
-- `PrimeSpectrum.preimageHomeomorphFiber`. For a prime `p'` over `p`, the fiber ring of the
-- base-changed map is `κ(p') ⊗[κ(p)] (κ(p) ⊗[R] S)`. The original injectivity and purely
-- inseparable residue-field hypotheses imply that `κ(p) → κ(r)` has singleton spectrum and is
-- purely inseparable for the unique prime `r` of the original fiber. Purely inseparable base
-- change preserves these two properties, so the new fiber is again a singleton and its residue
-- extensions remain purely inseparable.
/-- Lemma 10.46.8: if `R → S` induces an injective map on prime spectra and purely inseparable
extensions on residue fields, then after any base change `R → R'` the canonical map
`R' → R' ⊗[R] S` has the same two properties. -/
theorem baseChange_injective_comap_and_hasPurelyInseparableResidueFieldExtensions
    (R' : Type w) [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (comap f))
    (hres : RingHom.HasPurelyInseparableResidueFieldExtensions f) :
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    Function.Injective (comap f') ∧ f'.HasPurelyInseparableResidueFieldExtensions := by
  classical
  dsimp
  let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
  have hfiber :
      ∀ p' : PrimeSpectrum R',
        Subsingleton (PrimeSpectrum (p'.asIdeal.Fiber (R' ⊗[R] S))) ∧
          RingHom.HasPurelyInseparableResidueFieldExtensions
            (algebraMap p'.asIdeal.ResidueField (p'.asIdeal.Fiber (R' ⊗[R] S))) := by
    intro p'
    simpa using
      baseChange_fiber_subsingleton_and_residueFieldPure
        (R := R) (S := S) (R' := R') hinj hres p'
  refine ⟨?_, ?_⟩
  · intro q₁ q₂ hq
    let p' : PrimeSpectrum R' := PrimeSpectrum.comap f' q₁
    let e := PrimeSpectrum.preimageEquivFiber R' (R' ⊗[R] S) p'
    have hq₂' : PrimeSpectrum.comap f' q₂ = p' := by
      simpa [p'] using hq.symm
    have hr :
        e ⟨q₁, rfl⟩ = e ⟨q₂, hq₂'⟩ := by
      exact (hfiber p').1.elim _ _
    have hsubeq :
        (⟨q₁, rfl⟩ : { q : PrimeSpectrum (R' ⊗[R] S) // PrimeSpectrum.comap f' q = p' }) =
          ⟨q₂, hq₂'⟩ :=
      e.injective hr
    exact congrArg Subtype.val hsubeq
  · intro q
    let p' : PrimeSpectrum R' := PrimeSpectrum.comap f' q
    let e := PrimeSpectrum.preimageEquivFiber R' (R' ⊗[R] S) p'
    let r : PrimeSpectrum (p'.asIdeal.Fiber (R' ⊗[R] S)) := e ⟨q, rfl⟩
    let qover := (PrimeSpectrum.preimageEquivFiber R' (R' ⊗[R] S) p').symm r
    letI : Algebra p'.asIdeal.ResidueField r.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebra (R := Localization.AtPrime r.asIdeal)
    have hrPure :=
      isPurelyInseparable_of_hasPurelyInseparableResidueFieldExtensions_from_field r
        ((hfiber p').2)
    have hrPure' :
        IsPurelyInseparable p'.asIdeal.ResidueField r.asIdeal.ResidueField := by
      simpa [p'] using hrPure
    have hqover :
        (PrimeSpectrum.preimageEquivFiber R' (R' ⊗[R] S) p').symm r = ⟨q, rfl⟩ := by
      simpa [e, r] using e.symm_apply_apply r
    let qFiber : PrimeSpectrum (R' ⊗[R] S) :=
      ((PrimeSpectrum.preimageEquivFiber R' (R' ⊗[R] S) p').symm r).1
    have hqFiber : qFiber = q := by
      simpa [qFiber] using congrArg Subtype.val hqover
    have hqFiberComap : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom r.asIdeal = q.asIdeal := by
      simpa [qFiber, hqFiber] using
        (fiber_prime_comap_asIdeal (R := R') (S := R' ⊗[R] S) p' r)
    let fκ :
        p'.asIdeal.ResidueField →+* qFiber.asIdeal.ResidueField :=
      Ideal.ResidueField.map p'.asIdeal qFiber.asIdeal f'
        (by
          simpa [qFiber, PrimeSpectrum.comap_asIdeal] using
            (congrArg PrimeSpectrum.asIdeal
              ((PrimeSpectrum.preimageEquivFiber R' (R' ⊗[R] S) p').symm r).2).symm)
    letI : Algebra p'.asIdeal.ResidueField qFiber.asIdeal.ResidueField := fκ.toAlgebra
    let qToR :
        qFiber.asIdeal.ResidueField →+* r.asIdeal.ResidueField :=
      Ideal.ResidueField.map qFiber.asIdeal r.asIdeal
        (Algebra.ofId (R' ⊗[R] S) (p'.asIdeal.Fiber (R' ⊗[R] S)))
        (fiber_prime_comap_asIdeal (R := R') (S := R' ⊗[R] S) p' r).symm
    have hcomp :
        qToR.comp fκ = algebraMap p'.asIdeal.ResidueField r.asIdeal.ResidueField := by
      apply Ideal.ResidueField.ringHom_ext
      ext x
      simp only [RingHom.comp_apply]
      rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap]
      change algebraMap (R' ⊗[R] S) r.asIdeal.ResidueField (f' x) =
        algebraMap p'.asIdeal.ResidueField r.asIdeal.ResidueField
          (algebraMap R' p'.asIdeal.ResidueField x)
      calc
        algebraMap (R' ⊗[R] S) r.asIdeal.ResidueField (f' x) =
            algebraMap R' r.asIdeal.ResidueField x := by
          simpa [f', RingHom.comp_apply] using
            (RingHom.congr_fun
              (IsScalarTower.algebraMap_eq R' (R' ⊗[R] S) r.asIdeal.ResidueField) x).symm
        _ = algebraMap p'.asIdeal.ResidueField r.asIdeal.ResidueField
            (algebraMap R' p'.asIdeal.ResidueField x) := by
          rw [IsScalarTower.algebraMap_apply R' p'.asIdeal.ResidueField r.asIdeal.ResidueField]
    let qToRₐ :
        qFiber.asIdeal.ResidueField →ₐ[p'.asIdeal.ResidueField] r.asIdeal.ResidueField :=
      { __ := qToR
        commutes' := fun x ↦ by
          change qToR (fκ x) = algebraMap p'.asIdeal.ResidueField r.asIdeal.ResidueField x
          simpa [RingHom.comp_apply] using RingHom.congr_fun hcomp x }
    have hbij : Function.Bijective qToRₐ := by
      simpa [qToRₐ, qToR, qFiber] using
        fiber_prime_residueField_map_bijective (R := R') (S := R' ⊗[R] S) p' r
    have eRF0 :
        r.asIdeal.ResidueField ≃ₐ[p'.asIdeal.ResidueField] qFiber.asIdeal.ResidueField := by
      exact (AlgEquiv.ofBijective qToRₐ hbij).symm
    -- Proof comment: the base-changed prime `q` and its fiber avatar `r` have canonically
    -- equivalent residue fields, so pure inseparability transfers from the fiber package to `q`.
    have hqFiberPure :
        IsPurelyInseparable p'.asIdeal.ResidueField qFiber.asIdeal.ResidueField := by
      exact eRF0.isPurelyInseparable_iff.1 hrPure'
    let fκq :
        p'.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
      Ideal.ResidueField.map p'.asIdeal q.asIdeal f' rfl
    letI : Algebra p'.asIdeal.ResidueField q.asIdeal.ResidueField := fκq.toAlgebra
    have hqIdeal : q.asIdeal = qFiber.asIdeal := by
      simpa using congrArg PrimeSpectrum.asIdeal hqFiber.symm
    let eqToQₐ :
        qFiber.asIdeal.ResidueField →ₐ[p'.asIdeal.ResidueField] q.asIdeal.ResidueField :=
      { toRingHom :=
          Ideal.ResidueField.map qFiber.asIdeal q.asIdeal
            (Algebra.ofId (R' ⊗[R] S) (R' ⊗[R] S))
            (by simpa using hqIdeal.symm)
        commutes' := fun x ↦ by
          change
            Ideal.ResidueField.map qFiber.asIdeal q.asIdeal
              (Algebra.ofId (R' ⊗[R] S) (R' ⊗[R] S))
              (by simpa using hqIdeal.symm)
              (fκ x) = fκq x
          have hcompEq :
              (Ideal.ResidueField.map qFiber.asIdeal q.asIdeal
                (Algebra.ofId (R' ⊗[R] S) (R' ⊗[R] S))
                (by simpa using hqIdeal.symm)).comp fκ = fκq := by
            apply Ideal.ResidueField.ringHom_ext
            ext y
            simp only [RingHom.comp_apply]
            rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap]
            change algebraMap (R' ⊗[R] S) q.asIdeal.ResidueField (f' y) =
              Ideal.ResidueField.map p'.asIdeal q.asIdeal f' rfl
                (algebraMap R' p'.asIdeal.ResidueField y)
            simpa [fκq] using (Ideal.ResidueField.map_algebraMap p'.asIdeal q.asIdeal f' rfl y).symm
          simpa [RingHom.comp_apply] using RingHom.congr_fun hcompEq x }
    have hEqBij : Function.Bijective eqToQₐ := by
      simpa [eqToQₐ] using
        ((RingHom.surjectiveOnStalks_of_surjective (fun x ↦ ⟨x, rfl⟩)).residueFieldMap_bijective
          qFiber.asIdeal q.asIdeal (by simpa using hqIdeal.symm))
    let eQ :
        qFiber.asIdeal.ResidueField ≃ₐ[p'.asIdeal.ResidueField] q.asIdeal.ResidueField :=
      AlgEquiv.ofBijective eqToQₐ hEqBij
    have hqPure :
        IsPurelyInseparable p'.asIdeal.ResidueField q.asIdeal.ResidueField := by
      exact eQ.isPurelyInseparable_iff.1 hqFiberPure
    simpa [p', f', fκq] using hqPure

end
