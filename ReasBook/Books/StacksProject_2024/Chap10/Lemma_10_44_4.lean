import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_25_1
import StacksProject_2024.Chap10.Lemma_10_42_4
import StacksProject_2024.Chap10.Lemma_10_44_2
import StacksProject_2024.Chap10.Lemma_10_43_7
import StacksProject_2024.Chap10.Lemma_10_45_4
import StacksProject_2024.Chap10.Lemma_10_45_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v w

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

local instance (q : minimalPrimes S) : q.1.IsPrime :=
  Ideal.minimalPrimes_isPrime q.2

/-- Helper for Lemma 10.44.4: reducedness descends along an injective map on the left tensor
factor. -/
lemma isReduced_tensorProduct_of_injective_leftAlgHom
    {E : Type*} {L : Type*} [CommRing E] [CommRing L] [Algebra k E] [Algebra k L]
    (i : E →ₐ[k] L) (hi : Function.Injective i)
    (hred : IsReduced (L ⊗[k] S)) :
    IsReduced (E ⊗[k] S) := by
  let φ : E ⊗[k] S →+* L ⊗[k] S :=
    Algebra.TensorProduct.map i (AlgHom.id k S)
  have hφ : Function.Injective φ := by
    -- Tensoring an injective map of `k`-vector spaces with the identity on `S` stays injective.
    simpa [φ] using
      TensorProduct.map_injective_of_flat_flat
        i.toLinearMap
        (LinearMap.id : S →ₗ[k] S)
        hi
        (fun _ _ h ↦ h)
  letI : IsReduced (L ⊗[k] S) := hred
  exact isReduced_of_injective φ hφ

/-- Helper for Lemma 10.44.4: a purely inseparable extension of `k` embeds into the chosen
relative perfect closure inside `AlgebraicClosure k`. -/
lemma exists_algHom_to_perfectClosure_of_purelyInseparable
    (k' : Type (max u v)) [Field k'] [Algebra k k'] [IsPurelyInseparable k k'] :
    ∃ f : k' →ₐ[k] perfectClosure k (AlgebraicClosure k), Function.Injective f := by
  let f₀ : k' →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let e : k' ≃ₐ[k] f₀.fieldRange := AlgEquiv.ofInjectiveField f₀
  letI : IsPurelyInseparable k f₀.fieldRange := e.isPurelyInseparable
  have hle : f₀.fieldRange ≤ perfectClosure k (AlgebraicClosure k) :=
    le_perfectClosure k (AlgebraicClosure k) f₀.fieldRange
  refine ⟨(IntermediateField.inclusion hle).comp e.toAlgHom, ?_⟩
  exact (IntermediateField.inclusion hle).injective.comp e.injective

/-- Helper for Lemma 10.44.4: the chosen model `k^{1/p}` sits inside the relative perfect closure
inside `AlgebraicClosure k`. -/
lemma onePthRootExtension_le_perfectClosure :
    onePthRootExtension k p ≤ perfectClosure k (AlgebraicClosure k) := by
  refine
    (le_perfectClosure_iff
      (F := k) (E := AlgebraicClosure k) (L := onePthRootExtension k p)).2 ?_
  rw [isPurelyInseparable_iff_pow_mem k p]
  intro x
  -- The defining property of `onePthRootExtension` already gives the required `p`-power relation.
  refine ⟨1, ?_⟩
  rcases (mem_onePthRootExtension_iff (k := k) (p := p) (x := (x : AlgebraicClosure k))).1 x.2 with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  simpa using hc

/-- Helper for Lemma 10.44.4: after passing to a purely inseparable lift whose top extension is
separably generated, reducedness of the lifted base tensor forces reducedness over the original
field. -/
lemma isReduced_tensorProduct_of_purelyInseparable_lift
    {K : Type u} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    {k' : Type (max u v)} [Field k'] [Algebra k k']
    {K' : Type (max u v)} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K']
    (hlift : IsPurelyInseparableLiftWithSeparablyGenerated k K k' K')
    (hbase : IsReduced (k' ⊗[k] S)) :
    IsReduced (K ⊗[k] S) := by
  letI : FiniteDimensional K K' := hlift.finiteDimensional_top
  letI : IsPurelyInseparable K K' := hlift.purelyInseparable_top
  letI : FiniteDimensional k k' := hlift.finiteDimensional_base
  letI : IsPurelyInseparable k k' := hlift.purelyInseparable_base
  letI : IsSeparablyGenerated k' K' := hlift.separablyGenerated_top
  have hgeomK' : IsGeometricallyReduced k' K' := by
    letI : Algebra.EssFiniteType K K' := inferInstance
    letI : Algebra.EssFiniteType k K' := Algebra.EssFiniteType.comp k K K'
    letI : Algebra.EssFiniteType k' K' := Algebra.EssFiniteType.of_comp k k' K'
    exact
      isGeometricallyReduced_of_essFiniteType_isSeparablyGenerated
        (k := k') (L := K')
  let T := k' ⊗[k] S
  letI : IsReduced T := hbase
  have hredK' : IsReduced (K' ⊗[k] S) := by
    letI : IsGeometricallyReduced k' K' := hgeomK'
    have hredBaseChange : IsReduced (K' ⊗[k'] T) := by
      -- First apply the geometrically reduced field criterion over the lifted base field `k'`.
      exact
        isReduced_tensorProduct_of_geometricallyReduced_field
          (k := k') (K := K') (S := T)
    let e : K' ⊗[k'] T ≃+* K' ⊗[k] S :=
      (Algebra.TensorProduct.cancelBaseChange k k' K' K' S).toRingEquiv
    -- Then rewrite the iterated tensor product by the canonical base-change cancellation map.
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  -- Finally descend reducedness along the injective top map `K → K'`.
  exact
    isReduced_tensorProduct_of_injective_leftAlgHom
      (IsScalarTower.toAlgHom k K K')
      (IsScalarTower.toAlgHom k K K').injective
      hredK'

/-- Helper for Lemma 10.44.4: the finite purely inseparable test implies reducedness after base
change to every essentially finite type field extension. -/
lemma isReduced_tensorProduct_of_essFiniteType_field_of_finitePurelyInseparable_tests
    (hfinite :
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (k' ⊗[k] S))
    {K : Type u} [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    IsReduced (K ⊗[k] S) := by
  obtain ⟨k', hk'Field, hk'Alg, K', hK'Field, hkK', hKK', hk'K', hkKK', hkk'K',
    hlift⟩ :=
    exists_purelyInseparable_lift_with_separablyGenerated (k := k) (K := K)
  letI : Field k' := hk'Field
  letI : Algebra k k' := hk'Alg
  letI : Field K' := hK'Field
  letI : Algebra k K' := hkK'
  letI : Algebra K K' := hKK'
  letI : Algebra k' K' := hk'K'
  letI : IsScalarTower k K K' := hkKK'
  letI : IsScalarTower k k' K' := hkk'K'
  letI : FiniteDimensional k k' := hlift.finiteDimensional_base
  letI : IsPurelyInseparable k k' := hlift.purelyInseparable_base
  have hbase : IsReduced (k' ⊗[k] S) := hfinite k'
  -- The source proof now applies the reducedness bridge attached to the purely inseparable lift.
  exact
    isReduced_tensorProduct_of_purelyInseparable_lift
      (k := k) (S := S) (K := K) (k' := k') (K' := K') hlift hbase

/-- Helper for Lemma 10.44.4: reducedness is invariant under commuting the two tensor factors. -/
lemma isReduced_tensorProduct_comm_iff
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] :
    IsReduced (A ⊗[k] B) ↔ IsReduced (B ⊗[k] A) := by
  constructor
  · intro hAB
    let e : A ⊗[k] B ≃ₐ[k] B ⊗[k] A := Algebra.TensorProduct.comm k A B
    -- Proof comment: transport reducedness across the tensor-product commutativity equivalence.
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  · intro hBA
    let e : B ⊗[k] A ≃ₐ[k] A ⊗[k] B := Algebra.TensorProduct.comm k B A
    -- Proof comment: the reverse implication is the same transport after swapping the factors.
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- Helper for Lemma 10.44.4: if every finite purely inseparable extension of `k` yields a
reduced tensor product with `S`, then `S` is geometrically reduced over `k`. -/
lemma isGeometricallyReduced_of_finitePurelyInseparable_tests
    (hfinite :
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (k' ⊗[k] S)) :
    IsGeometricallyReduced k S := by
  -- Route correction: instead of rebuilding the arbitrary-field descent ad hoc, reduce to
  -- finitely generated `k`-subalgebras of the test field and use the new tensor-commutation bridge.
  rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
  intro K _ _
  have hSK : IsReduced (S ⊗[k] K) := by
    -- Proof comment: `IsReduced.tensorProduct_of_flat_of_forall_fg` reduces the arbitrary field
    -- extension to finitely generated `k`-subalgebras of `K`.
    refine IsReduced.tensorProduct_of_flat_of_forall_fg ?_
    intro B hB
    letI : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).1 hB
    letI : Algebra.EssFiniteType B (FractionRing B) := inferInstance
    letI : Algebra.EssFiniteType k (FractionRing B) := Algebra.EssFiniteType.comp k B (FractionRing B)
    have hFrac : IsReduced (FractionRing B ⊗[k] S) :=
      isReduced_tensorProduct_of_essFiniteType_field_of_finitePurelyInseparable_tests
        (k := k) (S := S) hfinite
    have hBS : IsReduced (B ⊗[k] S) := by
      -- Proof comment: descend reducedness from the fraction field back to the finitely generated
      -- subalgebra using injectivity of the canonical localization map.
      exact
        isReduced_tensorProduct_of_injective_leftAlgHom
          (k := k) (S := S)
          (IsScalarTower.toAlgHom k B (FractionRing B))
          (IsFractionRing.injective B (FractionRing B))
          hFrac
    -- Proof comment: rewrite the finite-stage result into the tensor order required by the flatness theorem.
    exact (isReduced_tensorProduct_comm_iff (k := k) (A := B) (B := S)).mp hBS
  -- Proof comment: commute once more to return to the statement form `K ⊗[k] S`.
  exact (isReduced_tensorProduct_comm_iff (k := k) (A := S) (B := K)).mp hSK

/-- Helper for Lemma 10.44.4: localizing a reduced base change at a minimal prime of `S` keeps the
tensor product reduced. -/
lemma isReduced_tensorProduct_localizationAtPrime_of_reduced_baseChange
    {K : Type*} [Field K] [Algebra k K]
    (q : minimalPrimes S)
    (hbase : IsReduced (K ⊗[k] S)) :
    IsReduced (Localization.AtPrime q.1 ⊗[k] K) := by
  let M : Submonoid S := q.1.primeCompl
  have hSK : IsReduced (S ⊗[k] K) :=
    (isReduced_tensorProduct_comm_iff (k := k) (A := K) (B := S)).mp hbase
  let φ : S ⊗[k] K →ₐ[S] Localization.AtPrime q.1 ⊗[k] K :=
    Algebra.TensorProduct.map (Algebra.ofId S (Localization.AtPrime q.1)) (AlgHom.id k K)
  letI : Algebra (S ⊗[k] K) (Localization.AtPrime q.1 ⊗[k] K) := φ.toAlgebra
  letI : IsScalarTower S (S ⊗[k] K) (Localization.AtPrime q.1 ⊗[k] K) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let _ : IsReduced (S ⊗[k] K) := hSK
  -- Proof comment: identify the localized tensor product with the localization of `S ⊗[k] K`
  -- along the image of the prime-complement submonoid, then use preservation of reducedness.
  let _ :
      IsLocalization
        (Algebra.algebraMapSubmonoid (S ⊗[k] K) M)
        (Localization.AtPrime q.1 ⊗[k] K) := by
    refine IsLocalization.tensorProduct_tensorProduct k K M (Localization.AtPrime q.1) ?_
    ext
    simp [RingHom.algebraMap_toAlgebra, φ]
  exact
    isReduced_localizationPreserves
      (Algebra.algebraMapSubmonoid (S ⊗[k] K) M)
      (Localization.AtPrime q.1 ⊗[k] K) inferInstance

/-- Helper for Lemma 10.44.4: localizing the reduced tensor product with `k^{1/p}` at a minimal
prime of `S` keeps the tensor product reduced. -/
lemma isReduced_tensorProduct_onePthRoot_localizationAtPrime
    (q : minimalPrimes S)
    (hroot : IsReduced (onePthRootExtension k p ⊗[k] S)) :
    IsReduced (Localization.AtPrime q.1 ⊗[k] onePthRootExtension k p) := by
  -- Proof comment: this is the generic localization transport specialized to `K = k^{1/p}`.
  exact
    isReduced_tensorProduct_localizationAtPrime_of_reduced_baseChange
      (k := k) (S := S) (K := onePthRootExtension k p) q hroot

/-- Helper for Lemma 10.44.4: reducedness after base change to `k^{1/p}` implies geometric
reducedness. -/
lemma isGeometricallyReduced_of_reduced_onePthRoot_baseChange
    (hroot : IsReduced (onePthRootExtension k p ⊗[k] S)) :
    IsGeometricallyReduced k S := by
  -- Route correction: follow the source proof through minimal-prime localizations instead of
  -- trying to prove geometric reducedness directly on `S`.
  have hkTensor : IsReduced (k ⊗[k] S) := by
    -- Proof comment: descend reducedness along the canonical inclusion `k → k^{1/p}`.
    exact
      isReduced_tensorProduct_of_injective_leftAlgHom
        (k := k) (S := S)
        (Algebra.ofId k (onePthRootExtension k p))
        (Algebra.ofId k (onePthRootExtension k p)).injective
        hroot
  have hS : IsReduced S := by
    let e : k ⊗[k] S ≃ₐ[k] S := Algebra.TensorProduct.lid k S
    let _ : IsReduced (k ⊗[k] S) := hkTensor
    -- Proof comment: cancel the trivial left tensor factor.
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  -- Proof comment: each minimal-prime localization is a field, and the localized one-`p`th-root
  -- tensor is reduced; Lemma `10.44.2` upgrades that field-level test to geometric reducedness.
  refine
    isGeometricallyReduced_of_forall_minimalPrime_localization
      (k := k) (S := S) hS ?_
  intro q
  letI : IsReduced S := hS
  let hField : IsField (Localization.AtPrime q.1) :=
    isField_localizationAtPrime_of_minimalPrime (R := S) q
  letI : Field (Localization.AtPrime q.1) := hField.toField
  have hloc :
      IsReduced (Localization.AtPrime q.1 ⊗[k] onePthRootExtension k p) :=
    isReduced_tensorProduct_onePthRoot_localizationAtPrime
      (k := k) (S := S) (p := p) q hroot
  have hsep : IsSeparableOver k (Localization.AtPrime q.1) :=
    (isSeparableOver_iff_isReduced_tensorProduct_onePthRootExtension
      (k := k) (K := Localization.AtPrime q.1) (p := p)).2 hloc
  exact
    (isSeparableOver_iff_isGeometricallyReduced_of_charP
      (k := k) (K := Localization.AtPrime q.1) (p := p)).1 hsep

-- Proof sketch: the implications from algebraic closure to perfect closure to `k^{1/p}` and from
-- the perfect closure to arbitrary finite purely inseparable extensions follow from the canonical
-- embeddings among these extensions. For `(1) → (5)`, reduce an arbitrary field extension to a
-- finitely generated one and use the purely inseparable lift from Lemma `10.42.4` together with
-- reducedness under separably generated extensions from Lemma `10.43.6`. For `(2) → (5)`, first
-- deduce that `S` is reduced, then check geometric reducedness on localizations at minimal primes
-- using Lemma `10.44.2`, and finally apply Lemma `10.43.7`.
/-- Lemma 10.44.4: for a field `k` of characteristic `p`, the following are equivalent for a
commutative `k`-algebra `S`: every finite purely inseparable extension `k' / k` yields a reduced
base change `k' ⊗[k] S`, the base change to the chosen model `onePthRootExtension k p` of
`k^{1/p}` is reduced, the base change to the relative perfect closure
`perfectClosure k (AlgebraicClosure k)` modeling `k^{perf}` is reduced, the base change to
`AlgebraicClosure k` is reduced, and `S` is geometrically reduced over `k`. -/
theorem isReduced_tensorProduct_tfae_finitePurelyInseparable_onePthRoot_perfectClosure_algebraicClosure_geometricallyReduced :
    List.TFAE [
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (k' ⊗[k] S),
      IsReduced (onePthRootExtension k p ⊗[k] S),
      IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S),
      IsReduced (AlgebraicClosure k ⊗[k] S),
      IsGeometricallyReduced k S
    ] := by
  tfae_have 1 → 5 := by
    intro hfinite
    -- The finite purely inseparable tests imply geometric reducedness by the source field-reduction argument.
    exact
      isGeometricallyReduced_of_finitePurelyInseparable_tests
        (k := k) (S := S) hfinite
  tfae_have 2 → 5 := by
    intro hroot
    -- The `k^(1/p)` test is handled via minimal-prime localizations.
    exact
      isGeometricallyReduced_of_reduced_onePthRoot_baseChange
        (k := k) (S := S) (p := p) hroot
  tfae_have 5 → 4 := by
    intro hgeom
    letI : IsGeometricallyReduced k S := hgeom
    infer_instance
  tfae_have 4 → 3 := by
    intro halg
    -- Reducedness descends from `\bar{k}` to the relative perfect closure.
    exact
      isReduced_tensorProduct_of_injective_leftAlgHom
        (perfectClosure k (AlgebraicClosure k)).val
        Subtype.val_injective
        halg
  tfae_have 3 → 2 := by
    intro hperf
    -- Then descend further from `k^{perf}` to the chosen `k^{1/p}` subfield.
    exact
      isReduced_tensorProduct_of_injective_leftAlgHom
        (IntermediateField.inclusion onePthRootExtension_le_perfectClosure)
        (IntermediateField.inclusion onePthRootExtension_le_perfectClosure).injective
        hperf
  tfae_have 3 → 1 := by
    intro hperf k' _ _ _ _
    obtain ⟨f, hf⟩ :=
      exists_algHom_to_perfectClosure_of_purelyInseparable
        (k := k) (k' := k')
    -- Every finite purely inseparable extension embeds into the chosen perfect closure.
    exact
      isReduced_tensorProduct_of_injective_leftAlgHom
        (k := k) (S := S) f hf hperf
  tfae_finish

/-- Lemma 10.44.4, clause `(2) ↔ (5)`: geometric reducedness is equivalent to reducedness after
base change to the chosen model `onePthRootExtension k p` of `k^{1/p}`. -/
theorem isGeometricallyReduced_iff_isReduced_tensorProduct_onePthRootExtension
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    IsGeometricallyReduced k S ↔ IsReduced (onePthRootExtension k p ⊗[k] S) :=
  by
    let l : List Prop := [
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (k' ⊗[k] S),
      IsReduced (onePthRootExtension k p ⊗[k] S),
      IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S),
      IsReduced (AlgebraicClosure k ⊗[k] S),
      IsGeometricallyReduced k S
    ]
    have htfae : List.TFAE l := by
      simpa [l] using
        isReduced_tensorProduct_tfae_finitePurelyInseparable_onePthRoot_perfectClosure_algebraicClosure_geometricallyReduced
    constructor
    · intro h
      letI : IsGeometricallyReduced k S := h
      infer_instance
    · intro h
      exact (htfae.out 1 4 (by simp [l]) (by simp [l])).mp h

end

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

/-- Lemma 10.44.4, clause `(3) ↔ (5)`: geometric reducedness is equivalent to reducedness after
base change to the canonical perfect closure `perfectClosure k (AlgebraicClosure k)`. -/
theorem isGeometricallyReduced_iff_isReduced_tensorProduct_perfectClosure :
    IsGeometricallyReduced k S ↔
      IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S) :=
  by
    constructor
    · intro h
      letI : IsGeometricallyReduced k S := h
      infer_instance
    · intro h
      by_cases h0 : ringChar k = 0
      · haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp h0
        letI : PerfectField k := PerfectField.ofCharZero
        let kperf := perfectClosure k (AlgebraicClosure k)
        obtain ⟨e, -⟩ := perfectClosure_algebraicClosure_existsUnique_algEquiv k k
        let e' : kperf ⊗[k] S ≃ₐ[k] S :=
          (Algebra.TensorProduct.congr e (AlgEquiv.refl : S ≃ₐ[k] S)).trans
            (Algebra.TensorProduct.lid k S)
        letI : IsReduced (kperf ⊗[k] S) := h
        letI : IsReduced S := isReduced_of_injective e'.symm.toRingHom e'.symm.injective
        infer_instance
      · letI : CharP k (ringChar k) := inferInstance
        have hprime : (ringChar k).Prime := CharP.char_prime_of_ne_zero k h0
        letI : Fact (ringChar k).Prime := ⟨hprime⟩
        let l : List Prop := [
          ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
            [IsPurelyInseparable k k'],
            IsReduced (k' ⊗[k] S),
          IsReduced (onePthRootExtension k (ringChar k) ⊗[k] S),
          IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S),
          IsReduced (AlgebraicClosure k ⊗[k] S),
          IsGeometricallyReduced k S
        ]
        have htfae : List.TFAE l := by
          simpa [l] using
            isReduced_tensorProduct_tfae_finitePurelyInseparable_onePthRoot_perfectClosure_algebraicClosure_geometricallyReduced
        exact (htfae.out 2 4 (by simp [l]) (by simp [l])).mp h

/-- Lemma 10.44.4, clause `(1) ↔ (5)`: a commutative `k`-algebra `S` is geometrically reduced
iff every finite purely inseparable extension `k' / k` yields a reduced base change
`k' ⊗[k] S`. -/
theorem isGeometricallyReduced_iff_isReduced_tensorProduct_finitePurelyInseparable :
    IsGeometricallyReduced k S ↔
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (k' ⊗[k] S) := by
  constructor
  · intro h k' _ _ _ _
    letI : IsGeometricallyReduced k S := h
    infer_instance
  · intro h
    by_cases h0 : ringChar k = 0
    · haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp h0
      let ek : ULift.{v} k ≃ₐ[k] k := ULift.algEquiv
      letI : IsPurelyInseparable k (ULift.{v} k) :=
        ek.symm.isPurelyInseparable
      have hk : IsReduced (ULift.{v} k ⊗[k] S) := h (ULift.{v} k)
      let e : ULift.{v} k ⊗[k] S ≃ₐ[k] S :=
        (Algebra.TensorProduct.congr ek (AlgEquiv.refl : S ≃ₐ[k] S)).trans
          (Algebra.TensorProduct.lid k S)
      letI : IsReduced (ULift.{v} k ⊗[k] S) := hk
      letI : IsReduced S := isReduced_of_injective e.symm.toRingHom e.symm.injective
      letI : PerfectField k := PerfectField.ofCharZero
      infer_instance
    · letI : CharP k (ringChar k) := inferInstance
      have hprime : (ringChar k).Prime := CharP.char_prime_of_ne_zero k h0
      letI : Fact (ringChar k).Prime := ⟨hprime⟩
      let l : List Prop := [
        ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'],
          IsReduced (k' ⊗[k] S),
        IsReduced (onePthRootExtension k (ringChar k) ⊗[k] S),
        IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S),
        IsReduced (AlgebraicClosure k ⊗[k] S),
        IsGeometricallyReduced k S
      ]
      have htfae : List.TFAE l := by
        simpa [l] using
          isReduced_tensorProduct_tfae_finitePurelyInseparable_onePthRoot_perfectClosure_algebraicClosure_geometricallyReduced
      exact (htfae.out 0 4 (by simp [l]) (by simp [l])).mp h

/- Lemma 10.44.4, clause `(4) ↔ (5)`: this is exactly the owner-class characterization
`isGeometricallyReduced_iff`. -/
recall isGeometricallyReduced_iff

end
