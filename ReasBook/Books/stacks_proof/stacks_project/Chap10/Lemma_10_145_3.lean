import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- Helper for Chap10 Lemma 10 145 3: the quasi-finite locus inside a finite type fiber over a
field is finite. -/
private theorem finiteQuasiFiniteAtFiberPrimes (p : PrimeSpectrum R) :
    Set.Finite { Q : PrimeSpectrum (p.asIdeal.Fiber S) |
      Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal } := by
  -- Work on the fiber over `p`, which is finite type over the field `κ(p)`, hence noetherian.
  let T : Set (PrimeSpectrum (p.asIdeal.Fiber S)) :=
    { Q | Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal }
  have hnoeth : IsNoetherianRing (p.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  letI : IsNoetherianRing (p.asIdeal.Fiber S) := hnoeth
  have hcompact : IsCompact T := TopologicalSpace.NoetherianSpace.isCompact T
  -- Each quasi-finite point is an open singleton in the fiber, so the selected locus is discrete.
  have hdiscrete : IsDiscrete T := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro Q hQ
    letI : Algebra.QuasiFiniteAt p.asIdeal.ResidueField Q.asIdeal := hQ
    refine ⟨{Q}, ?_, ?_⟩
    · exact (Algebra.QuasiFiniteAt.isClopen_singleton (R := p.asIdeal.ResidueField) Q).isOpen
    · ext Q'
      constructor
      · intro h
        exact h.1
      · intro h
        subst Q'
        exact ⟨rfl, hQ⟩
  -- A compact discrete subspace is finite.
  simpa [T] using hcompact.finite hdiscrete

/-- Helper for Chap10 Lemma 10 145 3: only finitely many primes over a fixed base prime are
quasi-finite. -/
private theorem finiteQuasiFinitePrimesOver (p : Ideal R) [p.IsPrime] :
    Set.Finite { q : p.primesOver S | Algebra.QuasiFiniteAt R q.1 } := by
  -- Transfer the finite fiber locus across the canonical primes-over/fiber equivalence.
  let e := PrimeSpectrum.primesOverOrderIsoFiber R S p
  let T : Set (p.primesOver S) := { q | Algebra.QuasiFiniteAt R q.1 }
  have hImage : Set.Finite (e '' T) := by
    refine (finiteQuasiFiniteAtFiberPrimes (S := S) (p := ⟨p, inferInstance⟩)).subset ?_
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

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 3: if no prime in the fiber is quasi-finite, the required
finite-product decomposition is the empty product with the original algebra as the remainder. -/
private theorem existsEmptyProductDecomposition_of_forall_not_quasiFiniteAt
    (p : Ideal R) [p.IsPrime]
    (hnot : ∀ q : p.primesOver S, ¬ Algebra.QuasiFiniteAt R q.1) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
      ∃ _ : Function.Bijective
        (Ideal.ResidueField.mapₐ p p' (Algebra.ofId _ _) (p'.over_def p)),
      ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i)) (instAAlg : ∀ i, Algebra R' (A i))
        (B : Type (max u v)) (instBComm : CommRing B) (instBAlg : Algebra R' B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R' (A i) := instAAlg
      letI : CommRing B := instBComm
      letI : Algebra R' B := instBAlg
      ∃ _ : R' ⊗[R] S ≃ₐ[R'] ((i : ι) → A i) × B,
      ∃ _ : ∀ i, Module.Finite R' (A i),
      ∃ _ : ∀ i, p'.primesOver (A i),
      ∃ _ : ∀ i, Subsingleton (p'.primesOver (A i)),
      ∀ q : p'.primesOver B, ¬ Algebra.QuasiFiniteAt R' q.1 := by
  classical
  -- Use the identity etale neighborhood and the same base prime.
  have hLie : (p : Ideal R).LiesOver p := by
    constructor
    rfl
  refine ⟨R, inferInstance, inferInstance, inferInstance, p, inferInstance, hLie, ?_⟩
  letI : (p : Ideal R).LiesOver p := hLie
  -- The residue-field map for the identity neighborhood is bijective.
  have hκ : Function.Bijective
      (Ideal.ResidueField.mapₐ p p (Algebra.ofId R R) (p.over_def p)) := by
    exact (RingHom.surjectiveOnStalks_of_surjective
      (fun x ↦ ⟨x, rfl⟩)).residueFieldMap_bijective p p rfl
  let B := ULift.{max u v, v} S
  refine ⟨hκ, PEmpty.{max u v + 1}, inferInstance, (fun _ ↦ PUnit.{max u v + 1}), ?_, ?_,
    B, inferInstance, inferInstance, ?_⟩
  · intro i
    cases i
  · intro i
    cases i
  · -- Normalize `R ⊗[R] S` to the lifted remainder, then prepend the empty product factor.
    refine ⟨(Algebra.TensorProduct.lid R S).trans
        ((ULift.algEquiv (R := R) (A := S)).symm.trans
          (AlgEquiv.uniqueProd (R := R) (A := B)
            (B := ((i : PEmpty.{max u v + 1}) → PUnit.{max u v + 1}))).symm), ?_⟩
    refine ⟨?_, ?_⟩
    · intro i
      cases i
    · refine ⟨?_, ?_⟩
      · intro i
        cases i
      · refine ⟨?_, ?_⟩
        · intro i
          cases i
        · intro q hqf
          let eUS : S ≃ₐ[R] B := (ULift.algEquiv (R := R) (A := S)).symm
          -- Transport a quasi-finite lifted remainder prime back to the original fiber.
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
/-- Helper for Chap10 Lemma 10 145 3: quotienting an idempotent algebra by `1 - e`
preserves the finite-module property supplied for the localization away from `e`. -/
private theorem finite_quotient_span_one_sub_of_isIdempotentElem
    {A : Type*} [CommRing A] [Algebra R A] (e : A) (he : IsIdempotentElem e)
    [Module.Finite R (Localization.Away e)] :
    Module.Finite R (A ⧸ Ideal.span ({1 - e} : Set A)) := by
  -- The quotient by `1 - e` is the canonical localization away from an idempotent element.
  letI : IsLocalization.Away e (A ⧸ Ideal.span ({1 - e} : Set A)) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  let E : Localization.Away e ≃ₐ[A] (A ⧸ Ideal.span ({1 - e} : Set A)) :=
    IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e)
      (A ⧸ Ideal.span ({1 - e} : Set A))
  -- Restrict the equivalence back to the base ring and transport finite generation.
  exact Module.Finite.equiv (E.restrictScalars R).toLinearEquiv

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 3: an idempotent gives the quotient-product normal form
with the `1 - e` quotient first and the `e` quotient as the complementary factor. -/
private noncomputable def idempotentQuotientProductEquiv
    {A : Type*} [CommRing A] [Algebra R A] (e : A) (he : IsIdempotentElem e) :
    A ≃ₐ[R] (A ⧸ Ideal.span ({1 - e} : Set A)) × (A ⧸ Ideal.span ({e} : Set A)) :=
  AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
    (sub_add_cancel 1 e) (IsIdempotentElem.one_sub_mul_self he)

/-- Helper for Chap10 Lemma 10 145 3: an embedding into a finite type with one point removed
forces a strict cardinal decrease. -/
private theorem card_lt_of_embedding_ne {α β : Type*} [Fintype α] [Fintype β]
    (a : α) (f : β ↪ {x : α // x ≠ a}) : Fintype.card β < Fintype.card α := by
  classical
  -- Bound the source by the erased subtype, then use that the erased subtype omits `a`.
  exact (Fintype.card_le_of_embedding f).trans_lt
    (Fintype.card_subtype_lt (p := fun x : α => x ≠ a) (x := a) (by simp))

/-- Helper for Chap10 Lemma 10 145 3: the generator killed by a singleton quotient belongs to
the comap of every quotient ideal. -/
private theorem quotient_span_singleton_mem_comap
    {A : Type*} [CommRing A] (e : A) (Q : Ideal (A ⧸ Ideal.span ({e} : Set A))) :
    e ∈ Q.comap (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) := by
  -- The quotient map sends the generator to zero, and every ideal contains zero.
  rw [Ideal.mem_comap]
  have hzero : (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) e = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton e))
  rw [hzero]
  exact Q.zero_mem

/-- Helper for Chap10 Lemma 10 145 3: the image of the quotient spectrum by an idempotent is
the complementary basic open subset. -/
private theorem isOpen_range_comap_quotient_span_idempotent
    {A : Type*} [CommRing A] (e : A) (he : IsIdempotentElem e) :
    IsOpen (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span ({e} : Set A))))) := by
  -- Identify the quotient map's range with `V(e)`, then use the idempotent equality
  -- `V(e) = D(1 - e)` to get openness.
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  convert (PrimeSpectrum.isOpen_basicOpen (a := 1 - e)) using 1
  rw [← PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem e he]
  ext P
  constructor
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    apply h
    change (Ideal.Quotient.mk (Ideal.span ({e} : Set A)) e = 0)
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton e))
  · intro h x hx
    have hspan : Ideal.span ({e} : Set A) ≤ P.asIdeal := by
      refine Ideal.span_le.mpr ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact h (Set.mem_singleton e)
    change (Ideal.Quotient.mk (Ideal.span ({e} : Set A)) x = 0) at hx
    exact hspan (Ideal.Quotient.eq_zero_iff_mem.mp hx)

/-- Helper for Chap10 Lemma 10 145 3: the quotient spectrum map attached to an idempotent is
an open embedding. -/
private theorem isOpenEmbedding_comap_quotient_span_idempotent
    {A : Type*} [CommRing A] (e : A) (he : IsIdempotentElem e) :
    Topology.IsOpenEmbedding
      (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span ({e} : Set A)))) := by
  -- Combine the usual closed embedding for a surjective ring map with the open image just
  -- identified from the idempotent normal form.
  refine Topology.IsOpenEmbedding.mk ?_ (isOpen_range_comap_quotient_span_idempotent e he)
  exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).toIsEmbedding

/-- Helper for Chap10 Lemma 10 145 3: an open singleton in the quotient spectrum remains an
open singleton after pulling back along the idempotent quotient map. -/
private theorem isOpen_singleton_comap_quotient_span_idempotent
    {A : Type*} [CommRing A] (e : A) (he : IsIdempotentElem e)
    (Q : PrimeSpectrum (A ⧸ Ideal.span ({e} : Set A)))
    (hQ : IsOpen ({Q} : Set (PrimeSpectrum (A ⧸ Ideal.span ({e} : Set A))))) :
    IsOpen ({PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) Q} :
      Set (PrimeSpectrum A)) := by
  -- The open embedding transports open sets, and the image of a singleton is the pulled-back
  -- singleton because the quotient-spectrum map is a function.
  have hOpenEmbedding := isOpenEmbedding_comap_quotient_span_idempotent e he
  have hImage : IsOpen
      ((PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span ({e} : Set A)))) ''
        ({Q} : Set (PrimeSpectrum (A ⧸ Ideal.span ({e} : Set A))))) :=
    hOpenEmbedding.isOpen_iff_image_isOpen.mp hQ
  simpa only [Set.image_singleton] using hImage

/-- Helper for Chap10 Lemma 10 145 3: a prime of the quotient by `1 - e` pulls back to a
prime not containing `e`. -/
private theorem notMem_comap_quotient_span_one_sub_of_isPrime
    {A : Type*} [CommRing A] (e : A)
    (Q : Ideal (A ⧸ Ideal.span ({1 - e} : Set A))) [Q.IsPrime] :
    e ∉ Q.comap (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) := by
  intro he_mem
  have honeSub_mem : 1 - e ∈ Q.comap (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) :=
    quotient_span_singleton_mem_comap (1 - e) Q
  -- If both complementary summands lie in the pulled-back prime, then so does `1`.
  have hone_mem : (1 : A) ∈ Q.comap (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) := by
    simpa [sub_add_cancel] using
      (Q.comap (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A)))).add_mem
        honeSub_mem he_mem
  have hprime : (Q.comap (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A)))).IsPrime :=
    inferInstance
  exact hprime.ne_top ((Ideal.eq_top_iff_one _).mpr hone_mem)

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 3: the quotient by `1 - e` inherits the owner theorem's
uniqueness of the prime lying over the selected base prime. -/
private theorem subsingletonPrimesOverQuotientOneSubIdempotent
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
  -- The pulled-back prime avoids `e`, so the uniqueness hypothesis identifies it with `P`.
  have comap_eq (Q : p.primesOver (A ⧸ Ideal.span ({1 - e} : Set A))) :
      Q.1.comap π = P := by
    exact hunique (Q.1.comap π) inferInstance (liesOver_comap Q)
      (notMem_comap_quotient_span_one_sub_of_isPrime e Q.1)
  -- The quotient map is surjective, hence equality after comap descends to equality upstairs.
  exact Ideal.comap_injective_of_surjective π Ideal.Quotient.mk_surjective
    ((comap_eq Q₁).trans (comap_eq Q₂).symm)

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 3: a selected prime avoiding an idempotent gives a prime in
the quotient by the complementary idempotent. -/
private theorem nonemptyPrimesOverQuotientOneSubIdempotent
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
/-- Helper for Chap10 Lemma 10 145 3: a bijective residue-field map transports uniqueness of
primes in a fiber after base change. -/
private theorem subsingletonPrimesOverTensorProductOfBijectiveResidueField
    {R₁ : Type u} {R₂ : Type v} {F : Type w}
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
/-- Helper for Chap10 Lemma 10 145 3: a bijective residue-field map transports nonemptiness of
primes in a fiber after base change. -/
private theorem nonemptyPrimesOverTensorProductOfBijectiveResidueField
    {R₁ : Type u} {R₂ : Type v} {F : Type w}
    [CommRing R₁] [CommRing R₂] [CommRing F] [Algebra R₁ R₂] [Algebra R₁ F]
    (p₁ : Ideal R₁) [p₁.IsPrime] (p₂ : Ideal R₂) [p₂.IsPrime] [p₂.LiesOver p₁]
    (hκ : Function.Bijective
      (Ideal.ResidueField.mapₐ p₁ p₂ (Algebra.ofId _ _) (p₂.over_def p₁)))
    [Nonempty (p₁.primesOver F)] :
    Nonempty (p₂.primesOver (R₂ ⊗[R₁] F)) := by
  -- Pull a chosen old-fiber prime back through the canonical fiber equivalence.
  obtain ⟨Q⟩ := (inferInstance : Nonempty (p₁.primesOver F))
  exact ⟨(Ideal.fiberIsoOfBijectiveResidueField (S := F) hκ).symm Q⟩

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 3: primes of the quotient by a selected idempotent embed
into the old fiber with the selected prime removed. -/
private lemma existsPrimesOverQuotientSpanEmbeddingErased
    {R₀ : Type u} {R₁ : Type v} {T : Type w}
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
    exact heP (hQP ▸ quotient_span_singleton_mem_comap e Q.1)
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

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 3: the target-shaped decomposition predicate for a fixed
base prime. -/
private abbrev HasEtaleFiniteProductDecomposition
    {R₀ : Type u} {T : Type w} [CommRing R₀] [CommRing T] [Algebra R₀ T]
    (p₀ : Ideal R₀) [p₀.IsPrime] : Prop :=
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R₀ R') (_ : Algebra.Etale R₀ R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p₀),
      ∃ _ : Function.Bijective
        (Ideal.ResidueField.mapₐ p₀ p' (Algebra.ofId _ _) (p'.over_def p₀)),
      ∃ (ι : Type (max u w)) (_ : Fintype ι) (A : ι → Type (max u w))
        (instAComm : ∀ i, CommRing (A i)) (instAAlg : ∀ i, Algebra R' (A i))
        (B : Type (max u w)) (instBComm : CommRing B) (instBAlg : Algebra R' B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R' (A i) := instAAlg
      letI : CommRing B := instBComm
      letI : Algebra R' B := instBAlg
      ∃ _ : R' ⊗[R₀] T ≃ₐ[R'] ((i : ι) → A i) × B,
      ∃ _ : ∀ i, Module.Finite R' (A i),
      ∃ _ : ∀ i, p'.primesOver (A i),
      ∃ _ : ∀ i, Subsingleton (p'.primesOver (A i)),
      ∀ q : p'.primesOver B, ¬ Algebra.QuasiFiniteAt R' q.1

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 145 3: the target-shaped predicate is closed by the already
proved empty-frontier construction. -/
private theorem hasEtaleFiniteProductDecomposition_of_forall_not_quasiFiniteAt
    {R₀ : Type u} {T : Type w} [CommRing R₀] [CommRing T] [Algebra R₀ T]
    (p₀ : Ideal R₀) [p₀.IsPrime]
    (hnot : ∀ q : p₀.primesOver T, ¬ Algebra.QuasiFiniteAt R₀ q.1) :
    HasEtaleFiniteProductDecomposition (R₀ := R₀) (T := T) p₀ := by
  -- Unfold the target-shaped abbreviation and reuse the empty-product construction.
  exact existsEmptyProductDecomposition_of_forall_not_quasiFiniteAt (R := R₀) (S := T) p₀ hnot

/-- Helper for Chap10 Lemma 10 145 3: induction skeleton on the finite quasi-finite frontier.
The remaining frontier-drop and append transports are isolated in the nonempty branch. -/
private theorem existsEtaleFiniteProductDecompositionByFrontierCard
    {R₀ : Type u} {T : Type w} [CommRing R₀] [CommRing T] [Algebra R₀ T]
    [Algebra.FiniteType R₀ T] (p₀ : Ideal R₀) [p₀.IsPrime] :
    HasEtaleFiniteProductDecomposition (R₀ := R₀) (T := T) p₀ := by
  classical
  by_cases hnoQuasiFinite : ∀ q : p₀.primesOver T, ¬ Algebra.QuasiFiniteAt R₀ q.1
  · -- The zero-rank branch is exactly the empty-product decomposition.
    exact hasEtaleFiniteProductDecomposition_of_forall_not_quasiFiniteAt
      (R₀ := R₀) (T := T) p₀ hnoQuasiFinite
  · -- Route correction: the previous proof tried to perform the rank drop, recursive étale
    -- refinement, and product append in one final transport-heavy step.  This helper keeps the
    -- one-point split in normal form and leaves only the recursive append/rank-drop engine open.
    have hfiniteFrontier := finiteQuasiFinitePrimesOver (R := R₀) (S := T) p₀
    push Not at hnoQuasiFinite
    obtain ⟨q₀, hq₀⟩ := hnoQuasiFinite
    letI : q₀.1.IsPrime := q₀.2.1
    letI : q₀.1.LiesOver p₀ := q₀.2.2
    letI : Algebra.QuasiFiniteAt R₀ q₀.1 := hq₀
    -- The one-point theorem supplies the first finite quotient factor and the complementary
    -- quotient.  The missing structural lemma must show the complement has strictly smaller
    -- quasi-finite frontier, recursively decompose it, and append this first factor.
    obtain ⟨R₁, _, _, _, p₁, _, _, e₁, he₁, P₁, _, _, hP₁q₀, heP₁, hκ₁, hfiniteA₁,
      hunique₁⟩ := Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p₀ q₀.1
    have hfiniteOnePointFactor :
        Module.Finite R₁ ((R₁ ⊗[R₀] T) ⧸ Ideal.span ({1 - e₁} : Set (R₁ ⊗[R₀] T))) := by
      -- Put the first finite factor into quotient normal form.
      exact finite_quotient_span_one_sub_of_isIdempotentElem (R := R₁) e₁ he₁
    let firstSplit :
        R₁ ⊗[R₀] T ≃ₐ[R₁]
          ((R₁ ⊗[R₀] T) ⧸ Ideal.span ({1 - e₁} : Set (R₁ ⊗[R₀] T))) ×
            ((R₁ ⊗[R₀] T) ⧸ Ideal.span ({e₁} : Set (R₁ ⊗[R₀] T))) :=
      idempotentQuotientProductEquiv (R := R₁) e₁ he₁
    have hsubsingletonOnePointFactor :
        Subsingleton
          (p₁.primesOver
            ((R₁ ⊗[R₀] T) ⧸ Ideal.span ({1 - e₁} : Set (R₁ ⊗[R₀] T)))) := by
      -- The uniqueness clause from the one-point theorem descends to the first quotient factor.
      exact subsingletonPrimesOverQuotientOneSubIdempotent p₁ e₁ P₁ hunique₁
    have hnonemptyOnePointFactor :
        Nonempty
          (p₁.primesOver
            ((R₁ ⊗[R₀] T) ⧸ Ideal.span ({1 - e₁} : Set (R₁ ⊗[R₀] T)))) := by
      -- The selected prime itself maps to the first quotient because it avoids `e₁`.
      exact nonemptyPrimesOverQuotientOneSubIdempotent p₁ e₁ he₁ P₁ heP₁
    obtain ⟨erasedPrimeEmbedding, _⟩ :=
      existsPrimesOverQuotientSpanEmbeddingErased (p₀ := p₀) (p₁ := p₁) hκ₁ e₁ P₁ q₀
        hP₁q₀ heP₁
    -- The quotient-prime embedding verifies the selected point is genuinely removed. The
    -- remaining missing bridge is the quasi-finite version of this embedding, followed by the
    -- recursive product append and outer étale refinement.
    have _ := erasedPrimeEmbedding
    have _ := hnonemptyOnePointFactor
    -- TODO: prove the cardinal drop for the complementary quotient by `e₁`, recursively apply
    -- this theorem there, append the quotient by `1 - e₁` as the `Option.none` factor, and
    -- compose the two étale neighborhoods and residue-field bijections.
    sorry

/- Domain-style sampling:
* primary domain: quasi-finite finite-type algebra maps and their étale-local splitting over a
  chosen fiber prime;
* sampled owner declarations:
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`,
  `Ideal.fiberIsoOfBijectiveResidueField`,
  `Ideal.primesOver`,
  `Algebra.QuasiFiniteAt`;
* best owner abstraction:
  the one-factor splitting owner theorem
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`, together with the fiber owner
  `Ideal.primesOver` and the local property owner `Algebra.QuasiFiniteAt`;
* layer:
  this numbered item is `source-facing`: it upgrades the one-factor owner theorem to a finite
  family decomposition, so it should stay a theorem rather than a new wrapper owner;
* primitive data:
  a finite-type `R`-algebra `S` and a prime `p ⊂ R`;
* derived API:
  the étale neighborhood, the residue-field bijection, the finite-indexed family of finite
  factors with their distinguished primes in the owner fibers `p'.primesOver (A i)`, and the
  non-quasi-finite remainder over `p'`.
-/

-- Proof sketch: induct on the number of isolated closed points of the fiber
-- `S ⊗[R] κ(p)`. If there are none, take no finite factors and keep the whole base change as the
-- remainder. Otherwise choose an isolated closed point, apply the one-factor splitting theorem of
-- Lemma `10.145.2`, identify the new fiber with the old one via the residue-field bijection, and
-- iterate on the complementary factor.
/-- Lemma 10.145.3: for a finite type ring map `R → S` and a prime `p ⊂ R`, there exists an
étale neighborhood `R → R'` with a prime `p'` over `p` and `κ(p') = κ(p)` such that the base
change `R' ⊗[R] S` decomposes as a finite product of finite `R'`-algebras, each equipped with its
unique prime `rᵢ` over `p'`, together with a remaining factor having no prime over `p'` at which
`R' → B` is quasi-finite. -/
@[stacks 00UK]
theorem exists_etale_finite_product_decomposition_with_nonQuasiFinite_remainder
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
      ∃ hκ : Function.Bijective
        (Ideal.ResidueField.mapₐ p p' (Algebra.ofId _ _) (p'.over_def p)),
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
      ∀ q : p'.primesOver B, ¬ Algebra.QuasiFiniteAt R' q.1 := by
  classical
  -- The public theorem is exactly the target-shaped decomposition predicate specialized to `S`.
  exact existsEtaleFiniteProductDecompositionByFrontierCard (R₀ := R) (T := S) p

end
