import Mathlib
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap10.Lemma_10_36_19
import StacksProject_2024.Chap10.Lemma_10_42_2
import StacksProject_2024.Chap10.Lemma_10_42_4
import StacksProject_2024.Chap10.Lemma_10_44_3

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 030R]
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
@[stacks 030R]
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
@[stacks 030R]
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
