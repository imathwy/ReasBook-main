import Mathlib
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_45_1 (from Chap10) -/
universe u v

section

variable {k : Type u} [Field k]

/- Definition 10.45.1: the canonical owner abstraction for a perfect field is the mathlib class
`PerfectField`. -/
recall PerfectField

/-- Definition 10.45.1, source-facing bridge: a field `k` is perfect if and only if every field
extension `K / k` is separable in the Stacks Project sense of Definition `10.42.1 (2)`. -/
theorem perfectField_iff_forall_isSeparableOver :
    PerfectField k ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K], Algebra.IsSeparableOver k K := by
  constructor
  · intro hk K _ _
    letI : PerfectField k := hk
    infer_instance
  · intro h
    have hClosure : Algebra.IsSeparableOver k (ULift.{v} (AlgebraicClosure k)) := h _
    have hClosure' : Algebra.IsSeparableOver k (AlgebraicClosure k) :=
      hClosure.of_algEquiv ULift.algEquiv
    exact (perfectField_iff_isSeparable_algebraicClosure k (AlgebraicClosure k)).2
      hClosure'.isSeparable

end

/-! ### Lemma_10_45_2 (from Chap10) -/
universe u

section

variable {k : Type u} [Field k]

/- Domain triage:
- primary domain: perfect fields and perfect rings in characteristic `ringExpChar k`;
- `source-facing`: the textbook `iff` below in terms of characteristic `0` or existence of `p`-th
  roots;
- `core/canonical`: the mathlib owners `PerfectField`, `PerfectField.toPerfectRing`, and
  `PerfectRing.toPerfectField`;
- `bridge/view`: the source-facing criterion is proved by passing through Frobenius surjectivity,
  so no extra local comparison theorem between the owner abstractions is needed.

Primitive data vs. derived API: the owner abstractions are already upstream, and the textbook
criterion is a derived bridge statement. This file should therefore reuse the existing owners
directly instead of keeping a parallel local `PerfectField ↔ PerfectRing` wrapper theorem.
-/

/- Lemma 10.45.2, owner-level forward bridge: a perfect field is a perfect ring at exponential
characteristic via the canonical instance `PerfectField.toPerfectRing`. -/
recall PerfectField.toPerfectRing

/- Lemma 10.45.2, owner-level reverse bridge: a field that is perfect as a ring is a perfect
field via `PerfectRing.toPerfectField`. -/
recall PerfectRing.toPerfectField

/-- Lemma 10.45.2, source-facing textbook form: a field is perfect if and only if either it has
characteristic `0`, or it has characteristic `p > 0` and every element admits a `p`-th root. -/
theorem perfectField_iff_charZero_or_exists_pth_root :
    PerfectField k ↔
      CharZero k ∨
        ∃ p : { n : ℕ // n.Prime }, CharP k p.1 ∧ ∀ x : k, ∃ y : k, y ^ p.1 = x := by
  constructor
  · intro hk
    obtain h0 | ⟨p, hp, hpchar⟩ := CharP.exists' k
    · exact Or.inl h0
    · letI := hk
      letI := hp
      letI := hpchar
      refine Or.inr ⟨⟨p, hp.out⟩, hpchar, fun x ↦ ?_⟩
      simpa using surjective_frobenius k p x
  · rintro (h0 | ⟨p, hp, hroot⟩)
    · letI := h0
      infer_instance
    · letI : Fact p.1.Prime := ⟨p.2⟩
      letI := hp
      haveI : PerfectRing k p.1 := PerfectRing.ofSurjective k p.1 hroot
      exact PerfectRing.toPerfectField k p.1

end

/-! ### Lemma_10_45_3 (from Chap10) -/
open scoped TensorProduct
open Algebra
open Algebra.TensorProduct

universe u v w x

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain triage:
- primary domain: finitely generated field extensions, purely inseparable lifts, and reduced tensor
  products over fields;
- core/canonical owner: `Algebra.IsSeparableOver` for the separability side of the lifted
  extension;
- layer split: the lifted fields and tower maps are the source-facing primitive data, while the
  tensor-product map is a bridge/view used only to express the reduced presentation.
-/

-- Proof sketch: apply Lemma `10.42.4` to obtain finite purely inseparable extensions
-- `K' / K` and `k' / k` with `K' / k'` separably generated, then use Lemma `10.44.3` to upgrade
-- separably generatedness to the owner predicate `IsSeparableOver k' K'`.
/-- Lemma 10.45.3 (1): for a finitely generated field extension `K / k`, there exist a finite
purely inseparable extension `K' / K` and a finite purely inseparable extension `k' / k`
equipped with compatible maps into `K'` such that `K' / k'` is separable in the sense of
Definition `10.42.1 (2)`. -/
theorem exists_purelyInseparable_lift_with_separable_over
    [EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K')
      (_ : FiniteDimensional K K') (_ : IsPurelyInseparable K K')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
        IsSeparableOver k' K' := by
  -- Proof comment: reuse the purely inseparable lift with separably generated top from
  -- Lemma `10.42.4`; only the owner predicate on the top field needs to be upgraded.
  obtain ⟨k', hk'Field, hk'Alg, K', hK'Field, hkK'Alg, hKK'Alg, hk'K'Alg, hkKK', hkk'K', hLift⟩ :=
    exists_purelyInseparable_lift_with_separablyGenerated (k := k) (K := K)
  letI : Field k' := hk'Field
  letI : Algebra k k' := hk'Alg
  letI : Field K' := hK'Field
  letI : Algebra k K' := hkK'Alg
  letI : Algebra K K' := hKK'Alg
  letI : Algebra k' K' := hk'K'Alg
  letI : IsScalarTower k K K' := hkKK'
  letI : IsScalarTower k k' K' := hkk'K'
  refine ⟨k', hk'Field, hk'Alg, K', hK'Field, hkK'Alg, hKK'Alg, hk'K'Alg, hkKK', hkk'K',
    hLift.finiteDimensional_top, hLift.purelyInseparable_top, hLift.finiteDimensional_base,
    hLift.purelyInseparable_base, ?_⟩
  -- Proof comment: Lemma `10.44.3` converts the separably generated top extension into the Stacks
  -- separability owner used in this file.
  exact Algebra.Lemma_10_44_3 hLift.separablyGenerated_top

/-- Helper for Lemma 10.45.3: if the images of the two tensor factors already generate the whole
target field, then the canonical tensor-product map is surjective. -/
lemma tensor_product_map_fieldRange_sup_eq_top_of_compositum_top
    {k' : Type w} {K' : Type x}
    [Field k'] [Field K'] [Algebra k k'] [Algebra k K']
    [FiniteDimensional k k']
    (f : k' →ₐ[k] K') (g : K →ₐ[k] K')
    (hsup : f.fieldRange ⊔ g.fieldRange = ⊤) :
    Function.Surjective (Algebra.TensorProduct.productMap f g) := by
  let eLeft : k' ≃ₐ[k] f.fieldRange := AlgEquiv.ofInjectiveField f
  let eRight : K ≃ₐ[k] g.fieldRange := AlgEquiv.ofInjectiveField g
  let eTensor :
      k' ⊗[k] K ≃ₐ[k] f.fieldRange ⊗[k] g.fieldRange :=
    Algebra.TensorProduct.congr eLeft eRight
  haveI : FiniteDimensional k f.fieldRange :=
    finiteDimensional_fieldRange_of_finiteDimensional f
  have hRangeTop :
      (Algebra.TensorProduct.productMap f.fieldRange.val g.fieldRange.val).range =
        (⊤ : Subalgebra k K') := by
    -- Proof comment: `productMap_range` computes the image as the compositum of the two ranges.
    rw [Algebra.TensorProduct.productMap_range, IntermediateField.range_val,
      IntermediateField.range_val,
      ← IntermediateField.sup_toSubalgebra_of_left (E1 := f.fieldRange) (E2 := g.fieldRange)]
    simpa [hsup]
  have hSurjRange :
      Function.Surjective
        (Algebra.TensorProduct.productMap f.fieldRange.val g.fieldRange.val) :=
    (AlgHom.range_eq_top _).mp hRangeTop
  have hComp :
      (Algebra.TensorProduct.productMap f.fieldRange.val g.fieldRange.val).comp eTensor.toAlgHom =
        Algebra.TensorProduct.productMap f g := by
    -- Proof comment: after identifying each factor with its field range, the tensor product map
    -- becomes the original product map on the nose.
    refine Algebra.TensorProduct.ext' ?_
    intro a b
    rfl
  intro z
  obtain ⟨y, hy⟩ := hSurjRange z
  obtain ⟨x, rfl⟩ := eTensor.surjective y
  -- Proof comment: transport the range-level surjectivity back along the tensor equivalence.
  have hEval :
      (Algebra.TensorProduct.productMap f.fieldRange.val g.fieldRange.val) (eTensor x) =
        (Algebra.TensorProduct.productMap f g) x := by
    simpa using congrArg (fun φ : k' ⊗[k] K →ₐ[k] K' => φ x) hComp
  exact ⟨x, hEval.symm.trans hy⟩

/-- Helper for Lemma 10.45.3: the compositum of the embedded lifted base and the embedded source
field is finitely generated over the embedded lifted base. -/
lemma compositum_fg_of_fieldRange_base_and_source
    {k' : Type w} {K' : Type x}
    [Field k'] [Field K'] [Algebra k k'] [Algebra k K']
    [FiniteDimensional k k']
    [EssFiniteType k K]
    (f : k' →ₐ[k] K') (g : K →ₐ[k] K') :
    (IntermediateField.extendScalars (E := f.fieldRange ⊔ g.fieldRange)
      (show f.fieldRange ≤ f.fieldRange ⊔ g.fieldRange by exact le_sup_left)).FG := by
  let A : IntermediateField k K' := f.fieldRange
  let B : IntermediateField k K' := g.fieldRange
  have hAfg : A.FG := by
    -- Proof comment: the lifted base image is finite-dimensional over `k`, hence essentially
    -- finite type and therefore finitely generated as an intermediate field.
    haveI : FiniteDimensional k A := finiteDimensional_fieldRange_of_finiteDimensional f
    exact (IntermediateField.essFiniteType_iff).mp inferInstance
  have hBfg : B.FG := by
    -- Proof comment: transport the source field's essentially finite type structure across the
    -- canonical equivalence with its image inside `K'`.
    let eB : K ≃ₐ[k] B := AlgEquiv.ofInjectiveField g
    letI : EssFiniteType k B := (Algebra.EssFiniteType.iff_of_algEquiv eB).mp inferInstance
    exact (IntermediateField.essFiniteType_iff).mp inferInstance
  have hSupfg : (A ⊔ B).FG := IntermediateField.fg_sup hAfg hBfg
  let M : IntermediateField A K' :=
    IntermediateField.extendScalars (E := A ⊔ B)
      (show A ≤ A ⊔ B by exact le_sup_left)
  have hRestrictFg : (M.restrictScalars k).FG := by
    -- Proof comment: after restricting scalars from `A` back to `k`, this is exactly the
    -- compositum already proved finitely generated above.
    simpa [A, B, M] using hSupfg
  -- Proof comment: the `A`-intermediate field is just the same carrier viewed after extending
  -- scalars from `k` to `A`.
  simpa [A, B, M] using (IntermediateField.FG.of_restrictScalars (K := k) hRestrictFg)

/-- Helper for Lemma 10.45.3: after quotienting by the nilradical, the tensor product over a
purely inseparable base change has prime nilradical, hence is a domain. -/
lemma tensor_nilradical_quotient_isDomain_of_purelyInseparable_base
    {k' : Type w}
    [Field k'] [Algebra k k'] [IsPurelyInseparable k k'] :
    IsDomain ((k' ⊗[k] K) ⧸ nilradical (k' ⊗[k] K)) := by
  let eComm : k' ⊗[k] K ≃ₐ[k] K ⊗[k] k' := Algebra.TensorProduct.comm k k' K
  have hComm :
      IsHomeomorph (PrimeSpectrum.comap eComm.toRingEquiv.toRingHom) :=
    PrimeSpectrum.isHomeomorph_comap_of_bijective eComm.toRingEquiv.bijective
  have hTensor :
      IsHomeomorph (PrimeSpectrum.comap (algebraMap K (K ⊗[k] k'))) :=
    PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k k' K
  let eSpecTensor : PrimeSpectrum (K ⊗[k] k') ≃ₜ PrimeSpectrum K := hTensor.homeomorph
  let eSpecComm : PrimeSpectrum (K ⊗[k] k') ≃ₜ PrimeSpectrum (k' ⊗[k] K) := hComm.homeomorph
  letI : Unique (PrimeSpectrum (K ⊗[k] k')) :=
    { default := eSpecTensor.symm default
      uniq := fun x ↦ by
        apply eSpecTensor.injective
        exact Subsingleton.elim _ _ }
  letI : Unique (PrimeSpectrum (k' ⊗[k] K)) :=
    { default := eSpecComm default
      uniq := fun x ↦ by
        have hx : eSpecComm.symm x = default := Subsingleton.elim _ _
        simpa using congrArg eSpecComm hx }
  have hIrreducible : IrreducibleSpace (PrimeSpectrum (k' ⊗[k] K)) := by
    rw [irreducibleSpace_def]
    exact ⟨Set.univ_nonempty, PreirreducibleSpace.isPreirreducible_univ⟩
  have hPrime : (nilradical (k' ⊗[k] K)).IsPrime :=
    (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical).mp hIrreducible
  -- Proof comment: a quotient by a prime ideal is a domain, so the reduced quotient is a domain.
  exact (Ideal.Quotient.isDomain_iff_prime (I := nilradical (k' ⊗[k] K))).2 hPrime

/-- Helper for Lemma 10.45.3: the reduced tensor product over a purely inseparable base change is
already a field because it is a domain integral over the source field `K`. -/
lemma tensor_nilradical_quotient_isField_of_purelyInseparable_base
    {k' : Type w}
    [Field k'] [Algebra k k'] [IsPurelyInseparable k k'] :
    IsField ((k' ⊗[k] K) ⧸ nilradical (k' ⊗[k] K)) := by
  letI : Algebra K (k' ⊗[k] K) :=
    (Algebra.TensorProduct.includeRight : K →ₐ[k] k' ⊗[k] K).toRingHom.toAlgebra
  let eCommK : k' ⊗[k] K ≃ₐ[K] K ⊗[k] k' :=
    { toRingEquiv := (Algebra.TensorProduct.comm k k' K).toRingEquiv
      commutes' := fun x ↦ by
        rw [show algebraMap K (k' ⊗[k] K) x = (1 : k') ⊗ₜ[k] x by rfl]
        simpa using
          (Algebra.TensorProduct.comm_tmul (R := k) (A := k') (B := K) (1 : k') x) }
  have hIntegralComm : Algebra.IsIntegral K (K ⊗[k] k') := by
    -- Proof comment: the purely inseparable base field is integral over `k`, so the tensor
    -- product is integral over the source field `K`.
    infer_instance
  have hIntegral :
      Algebra.IsIntegral K (k' ⊗[k] K) :=
    (AlgEquiv.isIntegral_iff (R := K) eCommK).2 hIntegralComm
  letI : Algebra.IsIntegral K (k' ⊗[k] K) := hIntegral
  letI : IsDomain ((k' ⊗[k] K) ⧸ nilradical (k' ⊗[k] K)) :=
    tensor_nilradical_quotient_isDomain_of_purelyInseparable_base (k := k) (K := K)
  letI : Algebra.IsIntegral K ((k' ⊗[k] K) ⧸ nilradical (k' ⊗[k] K)) := by
    infer_instance
  -- Proof comment: apply the chapter's integral-over-a-field criterion to the reduced quotient.
  exact isField_of_isIntegral_of_isField' (Field.toIsField K)

-- Proof sketch: apply Lemma `10.42.4` to obtain the purely inseparable lifts, then invoke
-- Lemma `10.42.2` to identify `K'` with the compositum of the images of `k'` and `K`.
/-- Lemma 10.45.3 (2): for a finitely generated field extension `K / k`, there exist a finite
purely inseparable extension `K' / K` and a finite purely inseparable extension `k' / k`
equipped with compatible maps into `K'` such that `K'` is the compositum of the images of `k'`
and `K`. -/
theorem exists_purelyInseparable_lift_with_compositum_top
    [EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K')
      (_ : FiniteDimensional K K') (_ : IsPurelyInseparable K K')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
        (IsScalarTower.toAlgHom k k' K').fieldRange ⊔
          (IsScalarTower.toAlgHom k K K').fieldRange = ⊤ := by
  obtain ⟨k', hk'Field, hk'Alg, K'', hK''Field, hkK''Alg, hKK''Alg, hk'K''Alg, hkKK'', hkk'K'',
      hfinTop, hpiTop, hfinBase, hpiBase, _hsepOver⟩ :=
    exists_purelyInseparable_lift_with_separable_over (k := k) (K := K)
  letI : Field k' := hk'Field
  letI : Algebra k k' := hk'Alg
  letI : Field K'' := hK''Field
  letI : Algebra k K'' := hkK''Alg
  letI : Algebra K K'' := hKK''Alg
  letI : Algebra k' K'' := hk'K''Alg
  letI : IsScalarTower k K K'' := hkKK''
  letI : IsScalarTower k k' K'' := hkk'K''
  let f : k' →ₐ[k] K'' := IsScalarTower.toAlgHom k k' K''
  let g : K →ₐ[k] K'' := IsScalarTower.toAlgHom k K K''
  let M₀ : IntermediateField k K'' := f.fieldRange ⊔ g.fieldRange
  let K' : Type (max v (max u w)) := M₀
  letI : Field K' := inferInstance
  let fK' : k' →ₐ[k] K' :=
    (IntermediateField.inclusion (show f.fieldRange ≤ M₀ by exact le_sup_left)).comp
      (AlgEquiv.ofInjectiveField f).toAlgHom
  let gK' : K →ₐ[k] K' :=
    (IntermediateField.inclusion (show g.fieldRange ≤ M₀ by exact le_sup_right)).comp
      (AlgEquiv.ofInjectiveField g).toAlgHom
  letI : Algebra k' K' := fK'.toRingHom.toAlgebra
  letI : Algebra K K' := gK'.toRingHom.toAlgebra
  letI : IsScalarTower k k' K' := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    -- Proof comment: the chosen `k'`-algebra on the compositum is exactly the old embedding into
    -- the ambient top field, restricted to the subfield `M₀`.
    exact (fK'.commutes x).symm
  letI : IsScalarTower k K K' := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    -- Proof comment: the chosen `K`-algebra on the compositum is the restricted old top map.
    exact (gK'.commutes x).symm
  letI : Algebra K' K'' := M₀.val.toRingHom.toAlgebra
  letI : IsScalarTower k K' K'' := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  letI : IsScalarTower K K' K'' := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rfl
  let iKK'' : K' →ₐ[K] K'' :=
    { toRingHom := algebraMap K' K''
      commutes' := fun x ↦ by rfl }
  letI : FiniteDimensional K K' := FiniteDimensional.left K K' K''
  letI : IsPurelyInseparable K K' := by
    refine ⟨⟨fun x ↦ ?_⟩, fun x hx ↦ ?_⟩
    · -- Proof comment: integrality descends from the ambient purely inseparable top field to the
      -- chosen compositum subfield.
      exact
        (isIntegral_algHom_iff iKK'' iKK''.injective).mp
          (Algebra.IsIntegral.isIntegral (R := K) (algebraMap K' K'' x))
    · -- Proof comment: separable elements of the compositum already come from the source field
      -- because they do so after viewing them in the ambient purely inseparable top field.
      have hsepx : IsSeparable K ((algebraMap K' K'') x) := by
        exact hx.map iKK'' iKK''.injective
      obtain ⟨y, hy⟩ := IsPurelyInseparable.inseparable K (algebraMap K' K'' x) hsepx
      refine ⟨y, ?_⟩
      exact (algebraMap K' K'').injective <| by
        change (algebraMap K K'') y = (algebraMap K' K'') x
        simpa using hy
  refine ⟨k', hk'Field, hk'Alg, K', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hfinBase, hpiBase, ?_⟩
  apply (IntermediateField.lift_injective M₀)
  rw [IntermediateField.lift_top]
  -- Proof comment: after lifting the new field ranges back into the old ambient field `K''`,
  -- they recover the original two images whose supremum defined `M₀`.
  rw [IntermediateField.lift_sup]
  have hLiftBase :
      IntermediateField.lift
          ((IsScalarTower.toAlgHom k k' K').fieldRange : IntermediateField k K') =
        f.fieldRange := by
    rw [IntermediateField.lift, AlgHom.map_fieldRange]
    have hCompBase : M₀.val.comp (IsScalarTower.toAlgHom k k' K') = f := by
      ext x
      rfl
    rw [hCompBase]
  have hLiftSource :
      IntermediateField.lift
          ((IsScalarTower.toAlgHom k K K').fieldRange : IntermediateField k K') =
        g.fieldRange := by
    rw [IntermediateField.lift, AlgHom.map_fieldRange]
    have hCompSource : M₀.val.comp (IsScalarTower.toAlgHom k K K') = g := by
      ext x
      rfl
    rw [hCompSource]
  -- Proof comment: the lifted compositum is exactly the original subfield `M₀`.
  rw [hLiftBase, hLiftSource]

-- Proof sketch: apply Lemma `10.42.4` and the compositum description from Lemma `10.42.2`,
-- then use Lemma `10.36.19` to identify the reduced tensor product with a field. The canonical
-- tensor map is surjective onto the compositum, and its kernel is exactly the nilradical.
/-- Lemma 10.45.3 (3): for a finitely generated field extension `K / k`, there exist a finite
purely inseparable extension `K' / K` and a finite purely inseparable extension `k' / k`
equipped with compatible maps into `K'` such that the canonical `k'`-algebra map
`k' ⊗[k] K → K'` has kernel the nilradical and is surjective. -/
theorem exists_purelyInseparable_lift_with_reduced_tensor_presentation
    [EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K')
      (_ : FiniteDimensional K K') (_ : IsPurelyInseparable K K')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
        let φ : k' ⊗[k] K →ₐ[k'] K' :=
          productLeftAlgHom (ofId k' K') (IsScalarTower.toAlgHom k K K')
        RingHom.ker φ.toRingHom = nilradical (k' ⊗[k] K) ∧ Function.Surjective φ := by
  -- Proof comment: reuse part (2) for the compositum-top witness, then factor the tensor map
  -- through the reduced quotient and use the field structure of that quotient to identify the
  -- kernel with the nilradical.
  obtain ⟨k', hk'Field, hk'Alg, K', hK'Field, hkK'Alg, hKK'Alg, hk'K'Alg, hkKK', hkk'K',
      hfinTop, hpiTop, hfinBase, hpiBase, hsup⟩ :=
    exists_purelyInseparable_lift_with_compositum_top (k := k) (K := K)
  letI : Field k' := hk'Field
  letI : Algebra k k' := hk'Alg
  letI : Field K' := hK'Field
  letI : Algebra k K' := hkK'Alg
  letI : Algebra K K' := hKK'Alg
  letI : Algebra k' K' := hk'K'Alg
  letI : IsScalarTower k K K' := hkKK'
  letI : IsScalarTower k k' K' := hkk'K'
  refine ⟨k', hk'Field, hk'Alg, K', hK'Field, hkK'Alg, hKK'Alg, hk'K'Alg, hkKK', hkk'K',
    hfinTop, hpiTop, hfinBase, hpiBase, ?_⟩
  dsimp
  let φ : k' ⊗[k] K →ₐ[k'] K' :=
    productLeftAlgHom (ofId k' K') (IsScalarTower.toAlgHom k K K')
  let I : Ideal (k' ⊗[k] K) := nilradical (k' ⊗[k] K)
  have hφsurj : Function.Surjective φ := by
    let f : k' →ₐ[k] K' := IsScalarTower.toAlgHom k k' K'
    let g : K →ₐ[k] K' := IsScalarTower.toAlgHom k K K'
    have hSurjProduct :
        Function.Surjective (Algebra.TensorProduct.productMap f g) :=
      tensor_product_map_fieldRange_sup_eq_top_of_compositum_top
        (k := k) (K := K) (f := f) (g := g) hsup
    intro z
    obtain ⟨x, hx⟩ := hSurjProduct z
    -- Proof comment: `productMap` and the displayed `k'`-algebra tensor map have the same
    -- underlying function.
    exact ⟨x, by simpa [φ, f, g] using hx⟩
  have hIleKer : I ≤ RingHom.ker φ.toRingHom := by
    intro x hx
    rw [RingHom.mem_ker]
    exact IsNilpotent.eq_zero ((mem_nilradical.mp hx).map φ.toRingHom)
  let φbar : (k' ⊗[k] K) ⧸ I →ₐ[k'] K' := Ideal.Quotient.liftₐ I φ hIleKer
  have hφbar_surj : Function.Surjective φbar := by
    intro z
    obtain ⟨x, rfl⟩ := hφsurj z
    refine ⟨Ideal.Quotient.mk I x, ?_⟩
    -- Proof comment: the lift agrees with the original tensor map after composing with the
    -- quotient map.
    simpa [φbar] using Ideal.Quotient.lift_mk I (φ : k' ⊗[k] K →+* K') hIleKer x
  have hFieldQ : IsField ((k' ⊗[k] K) ⧸ I) :=
    tensor_nilradical_quotient_isField_of_purelyInseparable_base (k := k) (K := K)
  letI : Field ((k' ⊗[k] K) ⧸ I) := hFieldQ.toField
  have hφbar_inj : Function.Injective φbar := by
    exact φbar.toRingHom.injective
  have hKerLe : RingHom.ker φ.toRingHom ≤ I := by
    intro x hx
    have hxbar : φbar (Ideal.Quotient.mk I x) = 0 := by
      rw [RingHom.mem_ker] at hx
      have hcompEval :
          φbar (Ideal.Quotient.mk I x) = φ x := by
        simpa [φbar] using Ideal.Quotient.lift_mk I (φ : k' ⊗[k] K →+* K') hIleKer x
      exact hcompEval.trans hx
    have hzero : Ideal.Quotient.mk I x = 0 := by
      apply hφbar_inj
      rw [map_zero]
      exact hxbar
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  refine ⟨le_antisymm hKerLe hIleKer, hφsurj⟩

end

/-! ### Lemma_10_45_4 (from Chap10) -/
universe u v

section

variable (k : Type u) [Field k]

/- The canonical subextension `perfectClosure k (AlgebraicClosure k)` of an algebraic closure is
purely inseparable over `k`. -/
recall perfectClosure.isPurelyInseparable

/- The canonical subextension `perfectClosure k (AlgebraicClosure k)` is a perfect field. -/
recall perfectClosure.perfectField

-- Proof sketch: the canonical field `perfectClosure k (AlgebraicClosure k)` is a perfect closure
-- of `k`, and any perfect purely inseparable extension of `k` is also a perfect closure in the
-- sense of `IsPerfectClosure`. Existence of the `k`-algebra isomorphism comes from the owner
-- equivalence `IsPerfectClosure.equiv`, while uniqueness follows from the uniqueness of lifts from
-- a purely inseparable extension into a reduced `k`-algebra.

/-- Lemma 10.45.4: any perfect purely inseparable extension of `k` is uniquely `k`-isomorphic
to the canonical perfect closure `perfectClosure k (AlgebraicClosure k)`. -/
theorem perfectClosure_algebraicClosure_existsUnique_algEquiv
    (k' : Type v) [Field k'] [Algebra k k'] [PerfectField k'] [IsPurelyInseparable k k'] :
    ∃ e : perfectClosure k (AlgebraicClosure k) ≃ₐ[k] k', ∀ e', e' = e := by
  let p := ringExpChar k
  let kperf := perfectClosure k (AlgebraicClosure k)
  letI : ExpChar k' p := expChar_of_injective_algebraMap (algebraMap k k').injective p
  let e : kperf ≃ₐ[k] k' :=
    { IsPerfectClosure.equiv (algebraMap k kperf) (algebraMap k k') p with
      commutes' := IsPerfectClosure.equiv_comp_apply
        (algebraMap k kperf) (algebraMap k k') p }
  refine ⟨e, ?_⟩
  intro e'
  exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun (Subsingleton.elim e'.toAlgHom e.toAlgHom) x

end

/-! ### Definition_10_45_5 (from Chap10) -/
universe u v

namespace PerfectClosure

/- Textbook notation for the perfect closure `k^{perf}` of a field `k`. -/
scoped notation:max K "^{" "perf" "}" => perfectClosure K (AlgebraicClosure K)

end PerfectClosure

open scoped PerfectClosure

section

variable (k : Type u) [Field k]

/-
Definition 10.45.5: the perfect closure `k^{perf}` of `k` is the canonical intermediate field
`perfectClosure k (AlgebraicClosure k)` inside a chosen algebraic closure.
-/
#check k^{perf}

end

/- Companion recall: `perfectClosure k E` is the owner-level relative perfect closure attached to
any field extension `E/k`, and `k^{perf}` is its specialization to `E = AlgebraicClosure k`.
-/
recall perfectClosure

/-! ### Lemma_10_45_6 (from Chap10) -/
open scoped TensorProduct
open Algebra

universe u v w

/-
Domain triage:
- `source-facing`: clause `(1)` promotes reduced `k`-algebras over a perfect field to the owner
  class `Algebra.IsGeometricallyReduced`.
- `core/canonical`: the owner abstraction is `IsGeometricallyReduced k R`, and the tensor-product
  statement in clause `(2)` is already owned by `isReduced_tensorProduct_of_geometricallyReduced`.
- `bridge/view`: the perfect-field hypothesis supplies the owner instance in clause `(1)`; clause
  `(2)` is then recovered by specialization of the owner theorem, so no parallel wrapper API is
  needed.
-/

section

variable {k : Type u} [Field k]

/-- Lemma 10.45.6 (1): over a perfect field, every reduced commutative algebra is geometrically
reduced. This is the owner-level `IsGeometricallyReduced` instance. -/
-- Proof sketch: by the canonical definition of geometric reducedness, it suffices to show that
-- `AlgebraicClosure k ⊗[k] R` is reduced. Over a perfect field, `AlgebraicClosure k / k` is
-- separable, so Lemma `10.43.6` applies to the reduced algebra `R`.
instance perfectField_isGeometricallyReduced
    {R : Type v} [PerfectField k] [CommRing R] [Algebra k R] [IsReduced R] :
    IsGeometricallyReduced k R :=
  ⟨Lemma_10_43_6⟩

attribute [instance low] perfectField_isGeometricallyReduced

/- Clause (2): if `R` and `S` are reduced `k`-algebras over a perfect field `k`, then
their tensor product `R ⊗[k] S` is reduced. With clause `(1)` installed as the owner-level
instance above, this is exactly the canonical theorem
`isReduced_tensorProduct_of_geometricallyReduced`. -/
recall isReduced_tensorProduct_of_geometricallyReduced

end
