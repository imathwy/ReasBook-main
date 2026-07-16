import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_46_8
import stacks_proof.stacks_project.Chap10.Lemma_10_144_3
import stacks_proof.stacks_project.Chap10.Lemma_10_145_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- Helper for Chap10 Lemma 10 145 4: the quasi-finite locus in the fiber over a prime is finite. -/
private theorem finiteQuasiFiniteAtFiberPrimesForPure (p : PrimeSpectrum R) :
    Set.Finite { Q : PrimeSpectrum (p.asIdeal.Fiber S) |
      Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal } := by
  -- The fiber is finite type over a field, so it is noetherian and the selected locus is compact.
  let T : Set (PrimeSpectrum (p.asIdeal.Fiber S)) :=
    { Q | Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal }
  have hnoeth : IsNoetherianRing (p.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  letI : IsNoetherianRing (p.asIdeal.Fiber S) := hnoeth
  have hcompact : IsCompact T := TopologicalSpace.NoetherianSpace.isCompact T
  -- Quasi-finite points are open singletons, making the compact locus discrete and hence finite.
  have hdiscrete : IsDiscrete T := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro Q hQ
    letI : Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal := hQ
    refine ⟨{Q}, ?_, ?_⟩
    · exact (Algebra.QuasiFiniteAt.isClopen_singleton
        (R := p.asIdeal.ResidueField) Q).isOpen
    · ext Q'
      constructor
      · intro h
        exact h.1
      · intro h
        subst Q'
        exact ⟨rfl, hQ⟩
  simpa [T] using hcompact.finite hdiscrete

/-- Helper for Chap10 Lemma 10 145 4: only finitely many primes over a fixed base prime are
quasi-finite. -/
private theorem finiteQuasiFinitePrimesOverForPure (p : Ideal R) [p.IsPrime] :
    Set.Finite { q : p.primesOver S | Algebra.QuasiFiniteAt R q.1 } := by
  -- Transfer the finite fiber locus across the canonical equivalence between primes over `p` and
  -- primes of the fiber algebra.
  let e := PrimeSpectrum.primesOverOrderIsoFiber R S p
  let T : Set (p.primesOver S) := { q | Algebra.QuasiFiniteAt R q.1 }
  have hImage : Set.Finite (e '' T) := by
    refine (finiteQuasiFiniteAtFiberPrimesForPure (S := S) (p := ⟨p, inferInstance⟩)).subset ?_
    intro Q hQ
    rcases hQ with ⟨q, hqT, rfl⟩
    have hcomap : (e q).asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q.1 := by
      change ((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm (e q)).1 = q.1
      simp [e]
    letI : Algebra.QuasiFiniteAt R q.1 := hqT
    exact Algebra.QuasiFiniteAt.baseChange q.1 (e q).asIdeal hcomap.symm
  exact hImage.of_finite_image (by
    intro x _ y _ hxy
    exact e.injective hxy)

/-- Helper for Chap10 Lemma 10 145 4: a prime in a finite algebra factor has finite-dimensional
residue field over the residue field of the base prime. -/
private theorem finiteDimensional_residueField_of_moduleFinite
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) [Module.Finite A B] :
    FiniteDimensional p.ResidueField q.1.ResidueField := by
  -- The `primesOver` structure supplies the residue-field algebra, and module finiteness of the
  -- ambient algebra descends to the residue field.
  infer_instance

/-- Helper for Chap10 Lemma 10 145 4: a quasi-finite prime in a finite-type algebra has
finite-dimensional residue field over the base residue field. -/
private theorem finiteDimensional_residueField_of_quasiFiniteAt
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (p : Ideal A) [p.IsPrime] (q : p.primesOver B)
    [Algebra.QuasiFiniteAt A q.1] :
    FiniteDimensional p.ResidueField q.1.ResidueField := by
  -- Quasi-finiteness is precisely the local finiteness condition needed for the residue
  -- extension; mathlib exposes it through typeclass inference.
  infer_instance

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: a finite field extension is purely inseparable over its
separable closure. -/
private theorem residueField_isPurelyInseparable_over_separableClosure
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    IsPurelyInseparable (separableClosure K L) L := by
  -- The separable closure carries the maximal separable part, so the remaining extension is
  -- purely inseparable.
  infer_instance

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: the purified-base tensor product is canonically the
original base change, in the direction needed to transport a decomposition back to the target. -/
private noncomputable def tensorProduct_purifiedBaseChangeEquiv
    {R0 R1 : Type u} [CommRing R0] [CommRing R1]
    [Algebra R R0] [Algebra R0 R1] [Algebra R R1] [IsScalarTower R R0 R1] :
    R1 ⊗[R] S ≃ₐ[R1] R1 ⊗[R0] (R0 ⊗[R] S) :=
  (Algebra.TensorProduct.cancelBaseChange R R0 R1 R1 S).symm

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: the tensor adapter sends a pure tensor to the tensor with
the unit on the intermediate base. -/
private theorem tensorProduct_purifiedBaseChangeEquiv_tmul
    {R0 R1 : Type u} [CommRing R0] [CommRing R1]
    [Algebra R R0] [Algebra R0 R1] [Algebra R R1] [IsScalarTower R R0 R1]
    (x : R1) (s : S) :
    tensorProduct_purifiedBaseChangeEquiv (R := R) (S := S) (R0 := R0) (R1 := R1)
        (x ⊗ₜ[R] s) =
      x ⊗ₜ[R0] (1 ⊗ₜ[R] s) := by
  -- Unfold once to the mathlib cancel-base-change equivalence, then use its computation rule.
  simp [tensorProduct_purifiedBaseChangeEquiv]

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: the inverse tensor adapter multiplies the intermediate-base
scalar into the left tensor factor. -/
private theorem tensorProduct_purifiedBaseChangeEquiv_symm_tmul
    {R0 R1 : Type u} [CommRing R0] [CommRing R1]
    [Algebra R R0] [Algebra R0 R1] [Algebra R R1] [IsScalarTower R R0 R1]
    (x : R1) (y : R0) (s : S) :
    (tensorProduct_purifiedBaseChangeEquiv (R := R) (S := S) (R0 := R0) (R1 := R1)).symm
        (x ⊗ₜ[R0] (y ⊗ₜ[R] s)) =
      (y • x) ⊗ₜ[R] s := by
  -- The inverse is exactly `Algebra.TensorProduct.cancelBaseChange`, whose `tmul` rule is stable.
  simp [tensorProduct_purifiedBaseChangeEquiv]

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: pure inseparability is invariant under an algebra
equivalence of residue fields over the same base residue field. -/
private theorem isPurelyInseparable_of_algEquiv
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] (e : L ≃ₐ[K] M)
    [IsPurelyInseparable K L] :
    IsPurelyInseparable K M := by
  -- Convert the target across the equivalence instead of rebuilding p-power witnesses.
  exact (AlgEquiv.isPurelyInseparable_iff e).1 inferInstance

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: a field quotient of a tensor product by a purely
inseparable extension is purely inseparable over the left field. -/
private theorem isPurelyInseparable_of_surjective_tensorProduct
    {k K L M : Type*} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra L M] [Algebra k M]
    [IsScalarTower k L M] [IsPurelyInseparable k K]
    (φ : L ⊗[k] K →ₐ[L] M) (hφ : Function.Surjective φ) :
    IsPurelyInseparable L M := by
  -- Work with the exponential characteristic transported from `k` to `L`, so the tensor-product
  -- p-power lemma and the target pure-inseparability criterion use the same exponent.
  let q := ringExpChar k
  haveI : ExpChar L q := expChar_of_injective_algebraMap (algebraMap k L).injective q
  rw [isPurelyInseparable_iff_pow_mem L q]
  intro x
  -- Lift the element to the tensor product, take the p-power supplied by pure inseparability of
  -- `K / k`, and push the resulting left-field element through the quotient map.
  obtain ⟨y, rfl⟩ := hφ x
  obtain ⟨n, ⟨z, hz⟩⟩ :=
    IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
      (k := k) (K := K) (R := L) q y
  refine ⟨n, ⟨z, ?_⟩⟩
  calc
    algebraMap L M z = φ (algebraMap L (L ⊗[k] K) z) := (φ.commutes z).symm
    _ = φ (y ^ q ^ n) := by rw [hz]
    _ = (φ y) ^ q ^ n := by simp

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: the separable closure inside a finite field extension is
finite-dimensional over the base field. -/
private theorem finiteDimensional_separableClosure_of_finiteDimensional
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    FiniteDimensional K (separableClosure K L) := by
  -- View the separable closure as an intermediate field of the finite extension `L / K`.
  exact FiniteDimensional.left K (separableClosure K L) L

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: the separable closure of a field extension is separable
over the base field. -/
private theorem isSeparable_separableClosure
    {K L : Type*} [Field K] [Field L] [Algebra K L] :
    Algebra.IsSeparable K (separableClosure K L) := by
  -- This records the canonical instance used by the finite common-purification construction.
  infer_instance

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: after a base change of a map whose spectrum map is
injective and whose residue fields are purely inseparable, each prime in a fiber has purely
inseparable residue field over the new base residue field. -/
private theorem baseChange_primesOver_residueFieldPure_of_hasPurelyInseparableResidueFieldExtensions
    {R₀ : Type u} {T : Type v} {R₁ : Type u}
    [CommRing R₀] [CommRing T] [CommRing R₁] [Algebra R₀ T] [Algebra R₀ R₁]
    (hinj : Function.Injective (PrimeSpectrum.comap (algebraMap R₀ T)))
    (hres : RingHom.HasPurelyInseparableResidueFieldExtensions (algebraMap R₀ T))
    (p₁ : Ideal R₁) [p₁.IsPrime] (q : p₁.primesOver (R₁ ⊗[R₀] T)) :
    let fκ : p₁.ResidueField →+* q.1.ResidueField :=
      Ideal.ResidueField.map p₁ q.1 (algebraMap R₁ (R₁ ⊗[R₀] T)) (Ideal.over_def q.1 p₁)
    let _ : Algebra p₁.ResidueField q.1.ResidueField := fκ.toAlgebra
    IsPurelyInseparable p₁.ResidueField q.1.ResidueField := by
  -- Use Lemma `10.46.8` to transport the pure-residue package to the whole base-changed map.
  let f' : R₁ →+* R₁ ⊗[R₀] T := algebraMap R₁ (R₁ ⊗[R₀] T)
  have hbase :=
    baseChange_injective_comap_and_hasPurelyInseparableResidueFieldExtensions
      (R := R₀) (S := T) R₁ hinj hres
  have hres' : RingHom.HasPurelyInseparableResidueFieldExtensions f' := by
    simpa [f'] using hbase.2
  let qSpec : PrimeSpectrum (R₁ ⊗[R₀] T) := ⟨q.1, inferInstance⟩
  let pSpec : PrimeSpectrum R₁ := ⟨p₁, inferInstance⟩
  have hqcomap : PrimeSpectrum.comap f' qSpec = pSpec := by
    -- The `primesOver` proof is exactly the contraction equality for this fiber prime.
    apply PrimeSpectrum.ext
    letI : q.1.LiesOver p₁ := q.2.2
    simpa [pSpec, qSpec, f', Ideal.under] using (Ideal.over_def q.1 p₁).symm
  -- Rewrite the owner predicate at the contracted prime `p₁`.
  have hpure :=
    residueField_isPurelyInseparable_of_comap_eq
      (R := R₁) (S := R₁ ⊗[R₀] T) (hres := hres') (p := pSpec) (q := qSpec)
      hqcomap
  simpa [pSpec, qSpec, f'] using hpure

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: if the fiber has no quasi-finite prime, the pure
decomposition has the empty finite-product part and the original algebra as the remainder. -/
private theorem existsEmptyPureProductDecomposition_of_forall_not_quasiFiniteAt
    (p : Ideal R) [p.IsPrime]
    (hnot : ∀ q : p.primesOver S, ¬ Algebra.QuasiFiniteAt R q.1) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
      ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i)) (instAAlg : ∀ i, Algebra R' (A i))
        (B : Type (max u v)) (instBComm : CommRing B) (instBAlg : Algebra R' B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R' (A i) := instAAlg
      letI : CommRing B := instBComm
      letI : Algebra R' B := instBAlg
      ∃ _ : R' ⊗[R] S ≃ₐ[R'] ((i : ι) → A i) × B,
      ∃ _ : ∀ i, Module.Finite R' (A i),
      ∃ r : ∀ i, p'.primesOver (A i),
      ∃ _ : ∀ i, Subsingleton (p'.primesOver (A i)),
      ∃ _ :
        ∀ i,
          FiniteDimensional p'.ResidueField (r i).1.ResidueField ∧
            IsPurelyInseparable p'.ResidueField (r i).1.ResidueField,
      ∀ q : p'.primesOver B, ¬ Algebra.QuasiFiniteAt R' q.1 := by
  classical
  -- Use the identity etale neighborhood; the base prime itself lies over `p`.
  have hLie : (p : Ideal R).LiesOver p := by
    constructor
    rfl
  refine ⟨R, inferInstance, inferInstance, inferInstance, p, inferInstance, hLie, ?_⟩
  let B := ULift.{max u v, v} S
  refine ⟨PEmpty.{max u v + 1}, inferInstance, (fun _ ↦ PUnit.{max u v + 1}), ?_, ?_,
    B, inferInstance, inferInstance, ?_⟩
  · intro i
    cases i
  · intro i
    cases i
  -- Normalize the tensor product to the lifted remainder and use the empty product on the left.
  refine ⟨(Algebra.TensorProduct.lid R S).trans
      ((ULift.algEquiv (R := R) (A := S)).symm.trans
        (AlgEquiv.uniqueProd (R := R) (A := B)
          (B := ((i : PEmpty.{max u v + 1}) → PUnit.{max u v + 1}))).symm), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases i
  · intro i
    cases i
  · intro i
    cases i
  · intro i
    cases i
  · intro q hqf
    let eUS : S ≃ₐ[R] B := (ULift.algEquiv (R := R) (A := S)).symm
    -- Transport a quasi-finite prime of the lifted remainder back to the original fiber.
    have hqLie : (q.1.comap eUS.toRingHom).LiesOver p := by
      constructor
      rw [Ideal.under, Ideal.comap_comap]
      have hcomp : eUS.toRingHom.comp (algebraMap R S) = algebraMap R B := by
        ext x
        rfl
      rw [hcomp]
      letI : q.1.LiesOver p := q.2.2
      simpa [Ideal.under] using (Ideal.over_def q.1 p)
    let qS : p.primesOver S := ⟨q.1.comap eUS.toRingHom, inferInstance, hqLie⟩
    exact hnot qS (by
      dsimp [qS]
      letI : Algebra.QuasiFiniteAt R q.1 := hqf
      exact Algebra.QuasiFiniteAt.comap_algEquiv q.1 eUS)

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: quotienting an idempotent algebra by `1 - e`
preserves the finite-module property supplied for the localization away from `e`. -/
private theorem finite_quotient_span_one_sub_of_isIdempotentElem_forPure
    {A : Type*} [CommRing A] [Algebra R A] (e : A) (he : IsIdempotentElem e)
    [Module.Finite R (Localization.Away e)] :
    Module.Finite R (A ⧸ Ideal.span ({1 - e} : Set A)) := by
  -- Put the finite one-point factor into the quotient normal form used by the strengthened
  -- induction, then transport finite generation across the localization equivalence.
  letI : IsLocalization.Away e (A ⧸ Ideal.span ({1 - e} : Set A)) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  let E : Localization.Away e ≃ₐ[A] (A ⧸ Ideal.span ({1 - e} : Set A)) :=
    IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e)
      (A ⧸ Ideal.span ({1 - e} : Set A))
  exact Module.Finite.equiv (E.restrictScalars R).toLinearEquiv

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: an idempotent gives the quotient-product normal form
with the `1 - e` quotient first and the `e` quotient as the complementary factor. -/
private noncomputable def idempotentQuotientProductEquivForPure
    {A : Type*} [CommRing A] [Algebra R A] (e : A) (he : IsIdempotentElem e) :
    A ≃ₐ[R] (A ⧸ Ideal.span ({1 - e} : Set A)) × (A ⧸ Ideal.span ({e} : Set A)) :=
  AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
    (sub_add_cancel 1 e) (IsIdempotentElem.one_sub_mul_self he)

/-- Helper for Chap10 Lemma 10 145 4: an embedding into a finite type with one point removed
forces a strict cardinal decrease. -/
private theorem card_lt_of_embedding_ne_forPure {α β : Type*} [Fintype α] [Fintype β]
    (a : α) (f : β ↪ {x : α // x ≠ a}) : Fintype.card β < Fintype.card α := by
  classical
  -- Bound the source by the erased subtype, then use that the erased subtype omits `a`.
  exact (Fintype.card_le_of_embedding f).trans_lt
    (Fintype.card_subtype_lt (p := fun x : α => x ≠ a) (x := a) (by simp))

/-- Helper for Chap10 Lemma 10 145 4: the generator killed by a singleton quotient belongs to
the comap of every quotient ideal. -/
private theorem quotient_span_singleton_mem_comap_forPure
    {A : Type*} [CommRing A] (e : A) (Q : Ideal (A ⧸ Ideal.span ({e} : Set A))) :
    e ∈ Q.comap (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) := by
  -- The quotient map sends the generator to zero, and every ideal contains zero.
  rw [Ideal.mem_comap]
  have hzero : (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) e = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton e))
  rw [hzero]
  exact Q.zero_mem

/-- Helper for Chap10 Lemma 10 145 4: a prime of the quotient by `1 - e` pulls back to a
prime not containing `e`. -/
private theorem notMem_comap_quotient_span_one_sub_of_isPrime_forPure
    {A : Type*} [CommRing A] (e : A)
    (Q : Ideal (A ⧸ Ideal.span ({1 - e} : Set A))) [Q.IsPrime] :
    e ∉ Q.comap (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) := by
  -- If both complementary summands lie in the pulled-back prime, then so does `1`.
  intro he_mem
  have honeSub_mem : 1 - e ∈ Q.comap (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) :=
    quotient_span_singleton_mem_comap_forPure (1 - e) Q
  have hone_mem : (1 : A) ∈ Q.comap (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) := by
    simpa [sub_add_cancel] using
      (Q.comap (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A)))).add_mem
        honeSub_mem he_mem
  have hprime : (Q.comap (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A)))).IsPrime :=
    inferInstance
  exact hprime.ne_top ((Ideal.eq_top_iff_one _).mpr hone_mem)

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: the quotient by `1 - e` inherits the owner theorem's
uniqueness of the prime lying over the selected base prime. -/
private theorem subsingletonPrimesOverQuotientOneSubIdempotentForPure
    {A : Type*} [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (e : A) (P : Ideal A) [P.IsPrime] [P.LiesOver p]
    (hunique : ∀ P'' : Ideal A, P''.IsPrime → P''.LiesOver p → e ∉ P'' → P'' = P) :
    Subsingleton (p.primesOver (A ⧸ Ideal.span ({1 - e} : Set A))) := by
  constructor
  intro Q₁ Q₂
  apply Subtype.ext
  let π : A →+* A ⧸ Ideal.span ({1 - e} : Set A) := Ideal.Quotient.mk _
  -- Pull primes in the quotient back to primes over the same base prime.
  have liesOver_comap (Q : p.primesOver (A ⧸ Ideal.span ({1 - e} : Set A))) :
      (Q.1.comap π).LiesOver p := by
    constructor
    rw [Ideal.under, Ideal.comap_comap]
    have hcomp : π.comp (algebraMap R A) =
        algebraMap R (A ⧸ Ideal.span ({1 - e} : Set A)) := by
      ext x
      rfl
    rw [hcomp]
    letI : Q.1.LiesOver p := Q.2.2
    simpa [Ideal.under] using (Ideal.over_def Q.1 p)
  have comap_eq (Q : p.primesOver (A ⧸ Ideal.span ({1 - e} : Set A))) :
      Q.1.comap π = P := by
    exact hunique (Q.1.comap π) inferInstance (liesOver_comap Q)
      (notMem_comap_quotient_span_one_sub_of_isPrime_forPure e Q.1)
  -- The quotient map is surjective, hence equality after comap descends to equality upstairs.
  exact Ideal.comap_injective_of_surjective π Ideal.Quotient.mk_surjective
    ((comap_eq Q₁).trans (comap_eq Q₂).symm)

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: a selected prime avoiding an idempotent gives a prime in
the quotient by the complementary idempotent. -/
private theorem nonemptyPrimesOverQuotientOneSubIdempotentForPure
    {A : Type*} [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (e : A) (he : IsIdempotentElem e)
    (P : Ideal A) [P.IsPrime] [P.LiesOver p] (heP : e ∉ P) :
    Nonempty (p.primesOver (A ⧸ Ideal.span ({1 - e} : Set A))) := by
  let π : A →+* A ⧸ Ideal.span ({1 - e} : Set A) := Ideal.Quotient.mk _
  -- Since `e(1-e)=0` and the selected prime does not contain `e`, the complementary
  -- idempotent lies in the selected prime and can be quotiented out.
  have honeSub_mem : 1 - e ∈ P := by
    have hmul : e * (1 - e) = 0 := he.mul_one_sub_self
    exact ((Ideal.IsPrime.mem_or_mem_of_mul_eq_zero (I := P) inferInstance hmul).resolve_left heP)
  have hspan_le : Ideal.span ({1 - e} : Set A) ≤ P := by
    exact Ideal.span_le.mpr (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact honeSub_mem)
  let Q : Ideal (A ⧸ Ideal.span ({1 - e} : Set A)) := P.map π
  have hQprime : Q.IsPrime := by
    dsimp [Q, π]
    exact Ideal.isPrime_map_quotientMk_of_isPrime hspan_le
  have hQover : Q.LiesOver p := by
    constructor
    rw [Ideal.under]
    have hcomp : π.comp (algebraMap R A) =
        algebraMap R (A ⧸ Ideal.span ({1 - e} : Set A)) := by
      ext x
      rfl
    rw [← hcomp, ← Ideal.comap_comap]
    have hcomapQ : Q.comap π = P := by
      dsimp [Q, π]
      exact Ideal.comap_map_mk hspan_le
    rw [hcomapQ]
    letI : P.LiesOver p := inferInstance
    simpa [Ideal.under] using (Ideal.over_def P p)
  -- Package the mapped prime as an element of the quotient fiber.
  exact ⟨⟨Q, hQprime, hQover⟩⟩

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: a bijective residue-field map transports uniqueness of
primes in a fiber after base change. -/
private theorem subsingletonPrimesOverTensorProductOfBijectiveResidueFieldForPure
    {R₁ : Type u} {R₂ : Type v} {F : Type*}
    [CommRing R₁] [CommRing R₂] [CommRing F] [Algebra R₁ R₂] [Algebra R₁ F]
    (p₁ : Ideal R₁) [p₁.IsPrime] (p₂ : Ideal R₂) [p₂.IsPrime] [p₂.LiesOver p₁]
    (hκ : Function.Bijective
      (Ideal.ResidueField.mapₐ p₁ p₂ (Algebra.ofId _ _) (p₂.over_def p₁)))
    [Subsingleton (p₁.primesOver F)] :
    Subsingleton (p₂.primesOver (R₂ ⊗[R₁] F)) := by
  -- The fiber equivalence from the residue-field bijection is injective, so equality in the
  -- original fiber pulls back to equality in the base-changed fiber.
  constructor
  intro Q₁ Q₂
  exact (Ideal.fiberIsoOfBijectiveResidueField (S := F) hκ).injective (Subsingleton.elim _ _)

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 4: primes of the quotient by a selected idempotent embed
into the old fiber with the selected prime removed. -/
private lemma existsPrimesOverQuotientSpanEmbeddingErasedForPure
    {R₀ : Type u} {R₁ : Type v} {T : Type*}
    [CommRing R₀] [CommRing R₁] [CommRing T] [Algebra R₀ R₁] [Algebra R₀ T]
    (p₀ : Ideal R₀) [p₀.IsPrime] (p₁ : Ideal R₁) [p₁.IsPrime] [p₁.LiesOver p₀]
    (hκ : Function.Bijective
      (Ideal.ResidueField.mapₐ p₀ p₁ (Algebra.ofId _ _) (p₁.over_def p₀)))
    (e : R₁ ⊗[R₀] T)
    (P : Ideal (R₁ ⊗[R₀] T)) [P.IsPrime] [P.LiesOver p₁]
    (q₀ : p₀.primesOver T)
    (hPq₀ : P.comap Algebra.TensorProduct.includeRight.toRingHom = q₀.1)
    (heP : e ∉ P) :
    ∃ _ : p₁.primesOver
        ((R₁ ⊗[R₀] T) ⧸ Ideal.span ({e} : Set (R₁ ⊗[R₀] T))) ↪
      {x : p₀.primesOver T // x ≠ q₀}, True := by
  let A := R₁ ⊗[R₀] T
  let π : A →+* A ⧸ Ideal.span ({e} : Set A) := Ideal.Quotient.mk _
  -- Pull a quotient prime back to the tensor product and keep its lies-over proof explicit.
  have liesOver_comap (Q : p₁.primesOver (A ⧸ Ideal.span ({e} : Set A))) :
      (Q.1.comap π).LiesOver p₁ := by
    constructor
    rw [Ideal.under, Ideal.comap_comap]
    have hcomp : π.comp (algebraMap R₁ A) =
        algebraMap R₁ (A ⧸ Ideal.span ({e} : Set A)) := by
      ext x
      rfl
    rw [hcomp]
    letI : Q.1.LiesOver p₁ := Q.2.2
    simpa [Ideal.under] using (Ideal.over_def Q.1 p₁)
  let toOld (Q : p₁.primesOver (A ⧸ Ideal.span ({e} : Set A))) : p₀.primesOver T :=
    Ideal.fiberIsoOfBijectiveResidueField (S := T) hκ
      ⟨Q.1.comap π, inferInstance, liesOver_comap Q⟩
  refine ⟨⟨fun Q ↦ ⟨toOld Q, ?_⟩, ?_⟩, trivial⟩
  · -- The quotient pullback contains `e`; equality with the selected point would identify it
    -- with `P`, contradicting the one-point split's avoidance of `e`.
    intro hEq
    have hx : (toOld Q).1 = q₀.1 := congrArg Subtype.val hEq
    have hcomapQ : (Q.1.comap π).comap Algebra.TensorProduct.includeRight.toRingHom =
        q₀.1 := by
      simpa [toOld] using hx
    have hcomap : (Q.1.comap π).comap Algebra.TensorProduct.includeRight.toRingHom =
        P.comap Algebra.TensorProduct.includeRight.toRingHom :=
      hcomapQ.trans hPq₀.symm
    letI : (Q.1.comap π).LiesOver p₁ := liesOver_comap Q
    have hQP : Q.1.comap π = P :=
      Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap (S := T) hκ
        (Q.1.comap π) P hcomap
    exact heP (hQP ▸ quotient_span_singleton_mem_comap_forPure e Q.1)
  · -- Injectivity follows by the fiber equivalence and then by surjectivity of the quotient map.
    intro Q₁ Q₂ hQ
    apply Subtype.ext
    apply Ideal.comap_injective_of_surjective π Ideal.Quotient.mk_surjective
    have hOld : toOld Q₁ = toOld Q₂ := congrArg Subtype.val hQ
    have hSubtype :
        (⟨Q₁.1.comap π, inferInstance, liesOver_comap Q₁⟩ : p₁.primesOver A) =
          ⟨Q₂.1.comap π, inferInstance, liesOver_comap Q₂⟩ :=
      (Ideal.fiberIsoOfBijectiveResidueField (S := T) hκ).injective hOld
    exact congrArg Subtype.val hSubtype

/- Domain-style sampling:
* primary domain: quasi-finite finite-type algebra maps, étale neighborhoods, and residue-field
  control on the resulting fiber factors;
* sampled owner declarations:
  `exists_etale_liesOver_with_residueField_equiv`,
  `exists_etale_finite_product_decomposition_with_nonQuasiFinite_remainder`,
  `Ideal.primesOver`,
  `Ideal.ResidueField.mapₐ`;
* best owner abstraction:
  the chapter-local decomposition theorem
  `exists_etale_finite_product_decomposition_with_nonQuasiFinite_remainder`, with the fiber owner
  `Ideal.primesOver` and the canonical residue-field bridge supplied by the lies-over relation;
* layer triage:
  - `source-facing`: the present theorem, which keeps the decomposition from Lemma `10.145.3` and
    adds the purely inseparable residue-field conclusion;
  - `core/canonical`: `Ideal.primesOver` for the distinguished primes and the induced
    `κ(p')`-algebra structure on `κ(rᵢ)`;
  - `bridge/view`: `Ideal.ResidueField.mapₐ`, expressing the residue-field extension attached to a
    prime lying over `p'`;
* primitive data:
  a finite-type `R`-algebra `S` and a prime `p ⊂ R`;
* derived API:
  the étale neighborhood `R → R'`, the finite family of finite factors indexed by a canonical
  finite type `ι`, their distinguished primes in `p'.primesOver (A i)`, the finite purely
  inseparable residue-field extensions over `κ(p')`, and the non-quasi-finite remainder over `p'`.
-/

-- Proof sketch: first enlarge the residue field at `p` by a finite separable extension using
-- Lemma `10.144.3` so that every quasi-finite prime in the fiber acquires purely inseparable
-- residue field over the new base point. Then apply the product decomposition of Lemma `10.145.3`
-- to the resulting étale neighborhood; the distinguished primes in the finite factors keep the
-- same residue fields, while the remaining factor is not quasi-finite over the chosen prime.
/-- Lemma 10.145.4: for a finite type ring map `R → S` and a prime `p ⊂ R`, there exists an étale
neighborhood `R → R'` with a prime `p'` over `p` such that `R' ⊗[R] S` decomposes as a finite
product of finite `R'`-algebras `Aᵢ` and a remainder `B`, where each `Aᵢ` comes with its unique
prime `rᵢ` over `p'`, the corresponding residue field extension over `κ(p')` is finite and purely
inseparable, and `R' → B` is not quasi-finite at any prime over `p'`. -/
@[stacks 00UL]
theorem exists_etale_finite_product_decomposition_with_purelyInseparable_residueFields_and_nonQuasiFinite_remainder
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
      ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i)) (instAAlg : ∀ i, Algebra R' (A i))
        (B : Type (max u v)) (instBComm : CommRing B) (instBAlg : Algebra R' B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R' (A i) := instAAlg
      letI : CommRing B := instBComm
      letI : Algebra R' B := instBAlg
      ∃ e : R' ⊗[R] S ≃ₐ[R'] ((i : ι) → A i) × B,
      ∃ hfinite : ∀ i, Module.Finite R' (A i),
      ∃ r : ∀ i, p'.primesOver (A i),
      ∃ hsubsingleton : ∀ i, Subsingleton (p'.primesOver (A i)),
      ∃ hres :
        ∀ i,
          FiniteDimensional p'.ResidueField (r i).1.ResidueField ∧
            IsPurelyInseparable p'.ResidueField (r i).1.ResidueField,
      ∀ q : p'.primesOver B, ¬ Algebra.QuasiFiniteAt R' q.1 := by
  classical
  by_cases hnoQuasiFinite : ∀ q : p.primesOver S, ¬ Algebra.QuasiFiniteAt R q.1
  · -- With empty quasi-finite frontier, the empty-product construction makes the residue-field
    -- condition vacuous and transports the non-quasi-finite remainder condition back to `S`.
    exact existsEmptyPureProductDecomposition_of_forall_not_quasiFiniteAt (S := S) p hnoQuasiFinite
  -- Route correction: applying Lemma `10.145.3` directly over `R` leaves no source of pure
  -- inseparability for the finite factors.  The solved empty-frontier branch above is the base
  -- case; the remaining nonempty branch needs the planned preliminary finite separable
  -- residue-field enlargement before the product decomposition is created.
  have hfiniteFrontier := finiteQuasiFinitePrimesOverForPure (S := S) p
  have hfrontierResiduesFinite :
      ∀ q : { q : p.primesOver S | Algebra.QuasiFiniteAt R q.1 },
        FiniteDimensional p.ResidueField q.1.1.ResidueField := by
    -- The finite frontier can be purified only after recording that each visible residue field is
    -- a finite extension of the original residue field.
    intro q
    letI : Algebra.QuasiFiniteAt R q.1.1 := q.2
    exact finiteDimensional_residueField_of_quasiFiniteAt p q.1
  obtain ⟨R', instR', instAlgR', instEtaleR', p', hp', hp'over, hκ, ι, instι, A,
      instAComm, instAAlg, B, instBComm, instBAlg, e, hfinite, r, hsubsingleton,
      hnonQuasiFinite⟩ :=
    exists_etale_finite_product_decomposition_with_nonQuasiFinite_remainder (R := R) (S := S) p
  -- Assemble the target around the decomposition of Lemma `10.145.3`; the only missing source
  -- step is the preliminary finite separable residue-field enlargement that makes the selected
  -- residue extensions purely inseparable.
  refine ⟨R', instR', instAlgR', instEtaleR', p', hp', hp'over, ι, instι, A, instAComm,
    instAAlg, B, instBComm, instBAlg, e, hfinite, r, hsubsingleton, ?_, hnonQuasiFinite⟩
  intro i
  -- The finite frontier is explicitly available for the missing purification construction.
  have _ := hfiniteFrontier
  refine ⟨?_, ?_⟩
  · -- The finite-dimensional part follows from the finite algebra factor and the lies-over prime.
    letI : Module.Finite R' (A i) := hfinite i
    exact finiteDimensional_residueField_of_moduleFinite p' (r i)
  · have _ := hfrontierResiduesFinite
    -- TODO: replace this direct post-decomposition branch by first applying
    -- `exists_etale_liesOver_with_residueField_equiv` to one common finite separable extension
    -- containing the separable closures of the finite frontier residue fields, then run Lemma
    -- `10.145.3` after that base change and transport purity to the resulting finite factors.
    -- The remaining bridge must identify each final factor prime with a residue field quotient of
    -- the purified tensor fiber; the direct factors from Lemma `10.145.3` over `R` do not carry
    -- pure inseparability by themselves.
    sorry

end
