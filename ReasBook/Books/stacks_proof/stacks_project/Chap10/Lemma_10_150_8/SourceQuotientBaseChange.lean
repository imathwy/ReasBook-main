import Mathlib
import StacksProject_2024.Chap10.Definition_10_133_1
import StacksProject_2024.Chap10.Lemma_10_133_9
import StacksProject_2024.Chap10.Lemma_10_150_7
import StacksProject_2024.Chap10.Lemma_10_150_8.DiagonalTensorModels

open scoped PrincipalParts TensorProduct
open LinearMap
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

section

variable {R S S' M N X : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

open scoped PrincipalParts

/-- Helper for Lemma 10.150.8: the source principal-parts module, after base change to `S'`, is
identified with the literal tensor-product quotient that comes from the quotient model of Lemma
`10.133.9`. This packages the first two steps of the source-faithful quotient-model route. -/
noncomputable def principalPartsFormallyEtaleSourceTensorQuotientEquiv
    (k : ℕ) :
    S' ⊗[S] P^{k}_{S⁄R}(M) ≃ₗ[S']
      ((S' ⊗[S] (S ⊗[R] M)) ⧸
        LinearMap.range
          (((TensorProduct.AlgebraTensorModule.lTensor S' S')
            (((Submodule.restrictScalars S
              (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
                (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))).subtype).restrictScalars S)))) :=
  let epp := principal_parts_module_equiv_tensor_quotient
    (R := R) (S := S) (M := M) k
  let ebase := epp.baseChange S S' _ _
  let eqt := TensorProduct.AlgebraTensorModule.tensorQuotientEquiv
    (R := S) (A := S') (B := S) (M := S')
    (n := Submodule.restrictScalars S
      (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
        (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))))
  -- Proof comment: first identify principal parts with the quotient model from Lemma `10.133.9`,
  -- then tensor that quotient over `S` and rewrite it as the quotient of the tensor product.
  ebase.trans eqt

/-- Helper for Lemma 10.150.8: after base changing the quotient model of Lemma `10.133.9` and then
applying the general tensor-quotient equivalence, the source generator `1 ⊗ [m]` becomes the
intermediate quotient class of `1 ⊗ (1 ⊗ m)`. -/
theorem source_baseChange_tensor_quotient_apply_tmul_universal_differential
    (k : ℕ) (m : M) :
    let epp := principal_parts_module_equiv_tensor_quotient
      (R := R) (S := S) (M := M) k
    let ebase := epp.baseChange S S' _ _
    let eqt := TensorProduct.AlgebraTensorModule.tensorQuotientEquiv
      (R := S) (A := S') (B := S) (M := S') (N := S ⊗[R] M) _
    eqt (ebase ((1 : S') ⊗ₜ[S]
      principal_parts_universal_differential (R := R) (S := S) (M := M) k m)) =
      Submodule.Quotient.mk ((1 : S') ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)) := by
  -- Unfold the base-changed quotient model and evaluate it on the source generator.
  dsimp
  rw [principal_parts_module_equiv_tensor_quotient_universal_differential
    (R := R) (S := S) (M := M) k m]
  simpa using
    (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv_apply_tmul
      (R := S) (A := S') (B := S) (M := S') (N := S ⊗[R] M)
      (n := _) (x := (1 : S')) (y := ((1 : S) ⊗ₜ[R] m)))

/-- Helper for Lemma 10.150.8: the source denominator coming from
`tensorQuotientEquiv` is exactly the range of the base-changed inclusion of the source principal
parts denominator. This isolates the literal `lTensor`-vs-`baseChange` rewrite needed before
applying `cancelBaseChange`. -/
theorem source_tensor_quotient_range_eq_baseChange_range
    (k : ℕ) :
    LinearMap.range
        (((TensorProduct.AlgebraTensorModule.lTensor S' S')
          (((Submodule.restrictScalars S
            (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
              (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))).subtype).restrictScalars S))) =
      LinearMap.range
        (((Submodule.restrictScalars S
          (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
            (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))).subtype).baseChange S') := by
  -- Proof comment: `tensorQuotientEquiv` records the denominator using the heterobasic tensor
  -- map `lTensor`, while the later `cancelBaseChange` step is naturally expressed using
  -- `LinearMap.baseChange`; these are the same map after forgetting scalars.
  ext x
  change x ∈
      (LinearMap.range
        ((((TensorProduct.AlgebraTensorModule.lTensor S' S')
          (((Submodule.restrictScalars S
            (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
              (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))).subtype).restrictScalars S))).restrictScalars S) :
          Submodule S (S' ⊗[S] (S ⊗[R] M))) ↔
    x ∈
      (LinearMap.range
        ((((Submodule.restrictScalars S
          (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
            (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))).subtype).baseChange S').restrictScalars S) :
          Submodule S (S' ⊗[S] (S ⊗[R] M)))
  simpa [TensorProduct.AlgebraTensorModule.coe_lTensor, LinearMap.baseChange_eq_ltensor]

/-- Helper for Lemma 10.150.8: after base changing the source quotient model, the denominator can
be rewritten as the range of the base-changed source inclusion. This packages the stabilized
source-side quotient model just before the `cancelBaseChange` step. -/
noncomputable def principalPartsFormallyEtaleSourceBaseChangeEquiv
    (k : ℕ) :
    S' ⊗[S] P^{k}_{S⁄R}(M) ≃ₗ[S']
      ((S' ⊗[S] (S ⊗[R] M)) ⧸
        LinearMap.range
          (((Submodule.restrictScalars S
            (((KaehlerDifferential.ideal R S) ^ (k + 1)) •
              (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M)))).subtype).baseChange S')) :=
  -- Proof comment: the first comparison is `principalPartsFormallyEtaleSourceTensorQuotientEquiv`;
  -- then `quotEquivOfEq` replaces the literal tensor-quotient denominator by the matching
  -- base-changed source denominator.
  (principalPartsFormallyEtaleSourceTensorQuotientEquiv
    (R := R) (S := S) (S' := S') (M := M) k).trans <|
    Submodule.quotEquivOfEq _ _
      (source_tensor_quotient_range_eq_baseChange_range
        (R := R) (S := S) (S' := S') (M := M) k)

/-- Helper for Lemma 10.150.8: under the stabilized source-side quotient comparison, the source
generator `1 ⊗ [m]` still maps to the quotient class of `1 ⊗ (1 ⊗ m)`. -/
theorem principalPartsFormallyEtaleSourceBaseChangeEquiv_apply_tmul_universal_differential
    (k : ℕ) (m : M) :
    principalPartsFormallyEtaleSourceBaseChangeEquiv
      (R := R) (S := S) (S' := S') (M := M) k
      ((1 : S') ⊗ₜ[S]
        principal_parts_universal_differential (R := R) (S := S) (M := M) k m) =
      Submodule.Quotient.mk ((1 : S') ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)) := by
  -- Proof comment: the extra quotient rewrite is transport along an equality of denominators, so
  -- the generator computation from `source_baseChange_tensor_quotient_apply_tmul_universal_differential`
  -- carries over unchanged.
  rw [principalPartsFormallyEtaleSourceBaseChangeEquiv, LinearEquiv.trans_apply]
  exact congrArg
    (Submodule.quotEquivOfEq _ _
      (source_tensor_quotient_range_eq_baseChange_range
        (R := R) (S := S) (S' := S') (M := M) k))
    (source_baseChange_tensor_quotient_apply_tmul_universal_differential
      (R := R) (S := S) (S' := S') (M := M) k m
    )

/-- Helper for Lemma 10.150.8: once the source denominator has been transported through
`cancelBaseChange`, the descended quotient equivalence sends the intermediate source generator
`1 ⊗ (1 ⊗ m)` to the class of `1 ⊗ m`. -/
theorem source_intermediate_quotient_cancelBaseChange_equiv_apply_generator
    {nsrc : Submodule S' (S' ⊗[S] (S ⊗[R] M))}
    {nI : Submodule S' (S' ⊗[R] M)}
    (hmap :
      nsrc.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M).toLinearMap =
        nI)
    (m : M) :
    (Submodule.Quotient.equiv nsrc nI
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M) hmap)
      (Submodule.Quotient.mk ((1 : S') ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m))) =
        Submodule.Quotient.mk ((1 : S') ⊗ₜ[R] m) := by
  -- Proof comment: `Submodule.Quotient.equiv` is induced by `cancelBaseChange`, so it is enough
  -- to evaluate that equivalence on the displayed pure tensor.
  change
    Submodule.Quotient.mk
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M)
          ((1 : S') ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m))) =
      Submodule.Quotient.mk ((1 : S') ⊗ₜ[R] m)
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  simp

/-- Helper for Lemma 10.150.8: cancelling the redundant source-side base change on the acting ring
turns the right tensor inclusion into the left-factor base-change map
`S ⊗[R] S → S' ⊗[R] S`. -/
theorem source_cancelBaseChangeAlg_comp_includeRight :
    ((Algebra.TensorProduct.cancelBaseChange
        (R := R) (S := S) (T := S') (A := S') (B := S)).toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := S) (A := S') (B := S ⊗[R] S)).toRingHom) =
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom := by
  apply RingHom.ext
  intro z
  -- Proof comment: both ring maps are determined on pure tensors `s₁ ⊗ s₂`, where
  -- `cancelBaseChange` sends `1 ⊗ (s₁ ⊗ s₂)` to `algebraMap S S' s₁ ⊗ s₂`.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro s₁ s₂
    change
      (Algebra.TensorProduct.cancelBaseChange
        (R := R) (S := S) (T := S') (A := S') (B := S))
        ((1 : S') ⊗ₜ[S] ((s₁ : S) ⊗ₜ[R] s₂)) =
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S))
        ((s₁ : S) ⊗ₜ[R] s₂)
    simp [Algebra.smul_def]
  · intro z₁ z₂ hz₁ hz₂
    have hz₁' :
        (Algebra.TensorProduct.cancelBaseChange
          (R := R) (S := S) (T := S') (A := S') (B := S))
          ((1 : S') ⊗ₜ[S] z₁) =
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)) z₁ := by
      simpa using hz₁
    have hz₂' :
        (Algebra.TensorProduct.cancelBaseChange
          (R := R) (S := S) (T := S') (A := S') (B := S))
          ((1 : S') ⊗ₜ[S] z₂) =
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)) z₂ := by
      simpa using hz₂
    calc
      (Algebra.TensorProduct.cancelBaseChange
          (R := R) (S := S) (T := S') (A := S') (B := S))
          ((1 : S') ⊗ₜ[S] (z₁ + z₂)) =
        (Algebra.TensorProduct.cancelBaseChange
          (R := R) (S := S) (T := S') (A := S') (B := S))
          ((1 : S') ⊗ₜ[S] z₁) +
          (Algebra.TensorProduct.cancelBaseChange
            (R := R) (S := S) (T := S') (A := S') (B := S))
            ((1 : S') ⊗ₜ[S] z₂) := by
              rw [TensorProduct.tmul_add, map_add]
      _ =
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)) z₁ +
          (Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)) z₂ := by
              rw [hz₁', hz₂']
      _ =
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)) (z₁ + z₂) := by
              rw [map_add]

/-- Helper for Lemma 10.150.8: the base-changed source diagonal ideal is contained in the
`Icomap` ideal appearing in Lemma `10.150.7`. -/
theorem source_baseChange_diagonalIdeal_map_le_iComap :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map
        (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
    let Icomap : Ideal (S' ⊗[R] S) :=
      Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
    Ideal.map sourceMap (KaehlerDifferential.ideal R S) ≤ Icomap := by
  dsimp
  -- Proof comment: rewrite the source diagonal ideal as the span of the standard generators
  -- `1 ⊗ s - s ⊗ 1`, map those generators across the left-factor base change, and then check that
  -- their images land in the target diagonal ideal after applying `tensorComparison`.
  rw [← KaehlerDifferential.span_range_eq_ideal (R := R) (S := S), Ideal.map_span]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with ⟨s, rfl⟩
  change
    (Algebra.TensorProduct.map
      (AlgHom.id R S') (IsScalarTower.toAlgHom R S S'))
      ((Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S))
        (((1 : S) ⊗ₜ[R] s) - (s ⊗ₜ[R] (1 : S)))) ∈
      KaehlerDifferential.ideal R S'
  simpa using
    (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := R)
      (algebraMap S S' s))

/-- Helper for Lemma 10.150.8: every element of `S' ⊗[R] S` differs from the tensor of its
product image by an element of the mapped source diagonal ideal. -/
theorem source_baseChange_sub_includeLeft_productMap_mem_mapped_diagonalIdeal
    (x : S' ⊗[R] S) :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let includeLeftS' : S' →ₐ[R] S' ⊗[R] S := Algebra.TensorProduct.includeLeft
    let sourceProduct : S' ⊗[R] S →ₐ[R] S' :=
      Algebra.TensorProduct.productMap (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')
    x - includeLeftS' (sourceProduct x) ∈
      Ideal.map sourceMap (KaehlerDifferential.ideal R S) := by
  dsimp
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a s
    have hgen :
        ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) ∈ KaehlerDifferential.ideal R S := by
      -- Proof comment: the source diagonal ideal is generated by the standard differences
      -- `1 ⊗ s - s ⊗ 1`.
      exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := R) s
    have hmap :
        ((1 : S') ⊗ₜ[R] s - (algebraMap S S' s : S') ⊗ₜ[R] (1 : S)) ∈
          Ideal.map
            ((Algebra.TensorProduct.map
              (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom)
            (KaehlerDifferential.ideal R S) := by
      -- Proof comment: base changing the standard generator gives the corresponding difference
      -- in `S' ⊗[R] S`.
      simpa using
        Ideal.mem_map_of_mem
          ((Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom)
          hgen
    have hsmul :
        (((Algebra.TensorProduct.includeLeft : S' →ₐ[R] S' ⊗[R] S) a) *
          (((1 : S') ⊗ₜ[R] s) - ((algebraMap S S' s : S') ⊗ₜ[R] (1 : S))) : S' ⊗[R] S) ∈
          Ideal.map
            ((Algebra.TensorProduct.map
              (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom)
            (KaehlerDifferential.ideal R S) := by
      -- Proof comment: multiplying the mapped diagonal generator by `a` produces the displayed
      -- pure-tensor difference.
      exact Ideal.mul_mem_left _ _ hmap
    simpa [Algebra.TensorProduct.productMap_apply_tmul, sub_eq_add_neg,
      mul_add, add_mul, Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.tmul_mul_tmul,
      mul_assoc, mul_left_comm, mul_comm] using hsmul
  · intro y z hy hz
    -- Proof comment: the product map and `includeLeft` are additive, so the desired difference
    -- term is additive as well.
    have hrewrite :
        y + z -
            (Algebra.TensorProduct.productMap
              (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')) (y + z) ⊗ₜ[R] (1 : S) =
          (y -
              (Algebra.TensorProduct.productMap
                (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')) y ⊗ₜ[R] (1 : S)) +
            (z -
              (Algebra.TensorProduct.productMap
                (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')) z ⊗ₜ[R] (1 : S)) := by
      rw [map_add, TensorProduct.add_tmul, sub_eq_add_neg, sub_eq_add_neg, neg_add]
      abel
    rw [hrewrite]
    exact Ideal.add_mem _ hy hz

/-- Helper for Lemma 10.150.8: the mapped source diagonal ideal is exactly the pulled-back target
diagonal ideal on `S' ⊗[R] S`. -/
theorem source_baseChange_diagonalIdeal_eq_iComap :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map
        (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
    let Icomap : Ideal (S' ⊗[R] S) :=
      Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
    Ideal.map sourceMap (KaehlerDifferential.ideal R S) = Icomap := by
  dsimp
  apply le_antisymm
  · exact source_baseChange_diagonalIdeal_map_le_iComap
      (R := R) (S := S) (S' := S')
  · intro x hx
    let includeLeftS' : S' →ₐ[R] S' ⊗[R] S := Algebra.TensorProduct.includeLeft
    let sourceProduct : S' ⊗[R] S →ₐ[R] S' :=
      Algebra.TensorProduct.productMap (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')
    have hdiff :
        x - includeLeftS' (sourceProduct x) ∈
          Ideal.map
            ((Algebra.TensorProduct.map
              (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom)
            (KaehlerDifferential.ideal R S) :=
      source_baseChange_sub_includeLeft_productMap_mem_mapped_diagonalIdeal
        (R := R) (S := S) (S' := S') x
    have hxker :
        ((Algebra.TensorProduct.map
          (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')) x) ∈
          RingHom.ker (Algebra.TensorProduct.lmul' (S := S') R) := by
      -- Proof comment: membership in the pulled-back target diagonal ideal means exactly that the
      -- tensor-comparison image lands in the kernel of multiplication.
      simpa [KaehlerDifferential.ideal] using hx
    have hprod : sourceProduct x = 0 := by
      have hcomp :
          ((Algebra.TensorProduct.lmul' (S := S') R).comp
            (Algebra.TensorProduct.map
              (AlgHom.id R S') (IsScalarTower.toAlgHom R S S'))) x = 0 := by
        simpa [RingHom.mem_ker] using hxker
      -- Proof comment: the source product map is the multiplication map after tensor comparison.
      simpa [sourceProduct, Algebra.TensorProduct.productMap_eq_comp_map] using hcomp
    simpa [sourceProduct, hprod] using hdiff

/-- Helper for Lemma 10.150.8: the identified source and target diagonal ideals remain equal after
taking the `(k + 1)`st power. -/
theorem source_baseChange_diagonalIdeal_pow_eq_iComap_pow
    (k : ℕ) :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map
        (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
    let Icomap : Ideal (S' ⊗[R] S) :=
      Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
    Ideal.map sourceMap ((KaehlerDifferential.ideal R S) ^ (k + 1)) =
      Icomap ^ (k + 1) := by
  -- Proof comment: once the degree-one diagonal ideals agree, functoriality of `Ideal.map` on
  -- powers upgrades the comparison to the powered denominators used in principal parts.
  dsimp
  let J : Ideal (S ⊗[R] S) := KaehlerDifferential.ideal R S
  let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
  let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
    (Algebra.TensorProduct.map
      (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
  let Icomap : Ideal (S' ⊗[R] S) :=
    Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
  have hdiag : Ideal.map sourceMap J = Icomap := by
    simpa [J, sourceMap, tensorComparison, Icomap] using
      source_baseChange_diagonalIdeal_eq_iComap (R := R) (S := S) (S' := S')
  calc
    Ideal.map sourceMap (J ^ (k + 1)) = (Ideal.map sourceMap J) ^ (k + 1) := by
      rw [Ideal.map_pow]
    _ = Icomap ^ (k + 1) := by
      simpa using congrArg (fun I : Ideal (S' ⊗[R] S) ↦ I ^ (k + 1)) hdiag

/-- Helper for Lemma 10.150.8: on the regular module `S' ⊗[R] S`, the powered transported source
denominator is exactly the powered pulled-back target denominator. -/
theorem source_baseChange_diagonalIdeal_pow_smul_top_eq_iComap_pow_smul_top
    (k : ℕ) :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map
        (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
    let Icomap : Ideal (S' ⊗[R] S) :=
      Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
    (Ideal.map sourceMap ((KaehlerDifferential.ideal R S) ^ (k + 1))) •
        (⊤ : Submodule (S' ⊗[R] S) (S' ⊗[R] S)) =
      (Icomap ^ (k + 1)) • (⊤ : Submodule (S' ⊗[R] S) (S' ⊗[R] S)) := by
  -- Proof comment: the regular module denominator is obtained by smearing the ideal over `⊤`, so
  -- the powered ideal equality lifts immediately to the corresponding submodules.
  dsimp
  exact congrArg
    (fun I : Ideal (S' ⊗[R] S) ↦
      I • (⊤ : Submodule (S' ⊗[R] S) (S' ⊗[R] S)))
    (source_baseChange_diagonalIdeal_pow_eq_iComap_pow
      (R := R) (S := S) (S' := S') k)

/-- Helper for Lemma 10.150.8: base changing the source quotient ring
`(S ⊗[R] S) / J^(k + 1)` along `S → S'` identifies it with the quotient of `S' ⊗[R] S`
by the mapped diagonal ideal. This is the ring-level source-proof step preceding the tensor with
`M`. -/
noncomputable def source_ring_quotient_baseChange_equiv_map
    (k : ℕ) :
    S' ⊗[S] (((S ⊗[R] S) ⧸ ((KaehlerDifferential.ideal R S) ^ (k + 1))) : Type u) ≃ₗ[S']
      ((S' ⊗[R] S) ⧸
        Ideal.map
          ((Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom)
          ((KaehlerDifferential.ideal R S) ^ (k + 1))) := by
  let Jpow : Ideal (S ⊗[R] S) := (KaehlerDifferential.ideal R S) ^ (k + 1)
  let includeRightS :
      S ⊗[R] S →+* S' ⊗[S] (S ⊗[R] S) :=
    (Algebra.TensorProduct.includeRight
      (R := S) (A := S') (B := S ⊗[R] S)).toRingHom
  let _ : (Ideal.map includeRightS Jpow).IsTwoSided := by infer_instance
  let sourceMap :
      S ⊗[R] S →+* S' ⊗[R] S :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
  let _ : (Ideal.map sourceMap Jpow).IsTwoSided := by infer_instance
  let eTensor :
      S' ⊗[S] ((S ⊗[R] S) ⧸ Jpow) ≃ₗ[S']
        ((S' ⊗[S] (S ⊗[R] S)) ⧸ Ideal.map includeRightS Jpow) :=
    (Algebra.TensorProduct.tensorQuotientEquiv
      (R := S) (S := S') (T := S ⊗[R] S) (A := S') Jpow).toLinearEquiv
  let eCancel :
      (S' ⊗[S] (S ⊗[R] S)) ≃ₐ[S'] (S' ⊗[R] S) :=
    Algebra.TensorProduct.cancelBaseChange
      (R := R) (S := S) (T := S') (A := S') (B := S)
  have hcomp : eCancel.toRingHom.comp includeRightS = sourceMap := by
    -- Proof comment: after unfolding the local abbreviations, this is the pure ring-level
    -- `cancelBaseChange` computation proved earlier in the file.
    simpa [eCancel, includeRightS, sourceMap] using
      source_cancelBaseChangeAlg_comp_includeRight
        (R := R) (S := S) (S' := S')
  have hmap :
      Ideal.map eCancel.toRingHom (Ideal.map includeRightS Jpow) = Ideal.map sourceMap Jpow := by
    -- Proof comment: the ring-level `cancelBaseChange` map turns the right tensor inclusion into
    -- the left-factor base-change map from `S ⊗[R] S` to `S' ⊗[R] S`.
    rw [Ideal.map_map]
    rw [hcomp]
  -- Proof comment: first tensor the source quotient ring with `S'`, then transport the quotient
  -- along the ring `cancelBaseChange` equivalence.
  exact eTensor.trans
    (Ideal.quotientEquivAlg (Ideal.map includeRightS Jpow) (Ideal.map sourceMap Jpow)
      eCancel (by simpa using hmap.symm)).toLinearEquiv

/-- Helper for Lemma 10.150.8: after rewriting the mapped denominator by
`source_baseChange_diagonalIdeal_pow_eq_iComap_pow`, the source quotient-ring base change lands in
the pulled-back target quotient ring appearing in Lemma `10.150.7`. -/
noncomputable def source_ring_quotient_baseChange_equiv
    (k : ℕ) :
    S' ⊗[S] (((S ⊗[R] S) ⧸ ((KaehlerDifferential.ideal R S) ^ (k + 1))) : Type u) ≃ₗ[S']
      ((S' ⊗[R] S) ⧸
        ((Ideal.comap
            ((Algebra.TensorProduct.map
              (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom)
            (KaehlerDifferential.ideal R S')) ^
          (k + 1))) := by
  -- Proof comment: the previous equivalence computes the denominator as the image of the source
  -- diagonal ideal; this step rewrites that image as the textbook pulled-back target ideal.
  exact
    (source_ring_quotient_baseChange_equiv_map
      (R := R) (S := S) (S' := S') k).trans
      (Ideal.quotientEquivAlgOfEq S'
        (source_baseChange_diagonalIdeal_pow_eq_iComap_pow
          (R := R) (S := S) (S' := S') k)).toLinearEquiv

/-- Helper for Lemma 10.150.8: after reassociating the outer tensor, the source quotient-ring
base change extends to the tensor-product model with `M`. This is the middle equality
`S' ⊗_S (((S ⊗_R S) / J^(k + 1)) ⊗_S M) = (((S' ⊗_R S) / Icomap^(k + 1)) ⊗_S M)` from the source
proof. -/
noncomputable def source_ring_quotient_tensor_baseChange_equiv
    (k : ℕ) :
    S' ⊗[S] ((((S ⊗[R] S) ⧸ ((KaehlerDifferential.ideal R S) ^ (k + 1))) ⊗[S] M) : Type u) ≃ₗ[S']
      ((((S' ⊗[R] S) ⧸
          ((Ideal.comap
              ((Algebra.TensorProduct.map
                (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom)
              (KaehlerDifferential.ideal R S')) ^
            (k + 1))) ⊗[S] M) : Type u) := by
  let Jquot : Type u :=
    ((S ⊗[R] S) ⧸ ((KaehlerDifferential.ideal R S) ^ (k + 1)))
  let Iquot : Type u :=
    ((S' ⊗[R] S) ⧸
      ((Ideal.comap
          ((Algebra.TensorProduct.map
            (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom)
          (KaehlerDifferential.ideal R S')) ^
        (k + 1)))
  let eAssoc :
      S' ⊗[S] (Jquot ⊗[S] M) ≃ₗ[S'] (S' ⊗[S] Jquot) ⊗[S] M :=
    (TensorProduct.AlgebraTensorModule.assoc S S S' S' Jquot M).symm
  -- Proof comment: `assoc` exposes the quotient-ring factor, and `congr` tensors the ring-level
  -- base-change comparison with the identity on `M`.
  exact eAssoc.trans <|
    TensorProduct.AlgebraTensorModule.congr
      (source_ring_quotient_baseChange_equiv
        (R := R) (S := S) (S' := S') k)
      (LinearEquiv.refl S M)

/-- Helper for Lemma 10.150.8: for any module over `S' ⊗[R] S`, the powered transported source
denominator agrees with the powered pulled-back target denominator after smearing over `⊤`. This
separates the formal ideal rewrite from the still-missing canonical action on the specific source
module `S' ⊗[R] M`. -/
theorem source_baseChange_sourceMap_pow_smul_top_eq_iComap_pow_smul_top_module
    {X : Type u} [AddCommGroup X] [Module (S' ⊗[R] S) X]
    (k : ℕ) :
    let sourceMap : S ⊗[R] S →+* S' ⊗[R] S :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R S S') (AlgHom.id R S)).toRingHom
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map
        (AlgHom.id R S') (IsScalarTower.toAlgHom R S S')).toRingHom
    let Icomap : Ideal (S' ⊗[R] S) :=
      Ideal.comap tensorComparison (KaehlerDifferential.ideal R S')
    (Ideal.map sourceMap ((KaehlerDifferential.ideal R S) ^ (k + 1))) •
        (⊤ : Submodule (S' ⊗[R] S) X) =
      (Icomap ^ (k + 1)) • (⊤ : Submodule (S' ⊗[R] S) X) := by
  -- Proof comment: this is the same powered ideal comparison as above, now smeared over the
  -- chosen `(S' ⊗[R] S)`-module.
  dsimp
  exact congrArg
    (fun I : Ideal (S' ⊗[R] S) ↦
      I • (⊤ : Submodule (S' ⊗[R] S) X))
    (source_baseChange_diagonalIdeal_pow_eq_iComap_pow
      (R := R) (S := S) (S' := S') k)

/-- Helper for Lemma 10.150.8: after cancelling the redundant source-side base change, the
diagonal action of a pure tensor `a ⊗ b` on a pure tensor `s ⊗ m` becomes the expected
base-changed pure tensor `algebraMap (as) ⊗ (b • m)`. This is the generator-level transport used
in the remaining denominator-image calculation. -/
theorem source_cancelBaseChange_diagonal_action_tmul_tmul
    (a b s : S) (m : M) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M)
      ((1 : S') ⊗ₜ[S]
        (diagonal_tensor_action (R := R) (S := S) (M := M)
          (((a : S) ⊗ₜ[R] b) : S ⊗[R] S)
          (((s : S) ⊗ₜ[R] m) : S ⊗[R] M))) =
      ((algebraMap S S' (a * s) : S') ⊗ₜ[R] (b • m)) := by
  -- Proof comment: first evaluate the source diagonal action on the pure tensor, then apply the
  -- pure-tensor formula for `cancelBaseChange`.
  rw [diagonal_tensor_action_tmul_tmul]
  simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, map_mul]

/-- Helper for Lemma 10.150.8: on the universal source tensor `1 ⊗ m`, cancelling the redundant
base change sends the diagonal action of `a ⊗ b` to the pure tensor
`algebraMap a ⊗ (b • m)`. This isolates the special case used when the denominator acts on source
generators. -/
theorem source_cancelBaseChange_diagonal_action_universal_tmul
    (a b : S) (m : M) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M)
      ((1 : S') ⊗ₜ[S]
        (diagonal_tensor_action (R := R) (S := S) (M := M)
          (((a : S) ⊗ₜ[R] b) : S ⊗[R] S)
          (((1 : S) ⊗ₜ[R] m) : S ⊗[R] M))) =
      ((algebraMap S S' a : S') ⊗ₜ[R] (b • m)) := by
  -- Proof comment: this is the `s = 1` specialization of the previous pure-tensor transport
  -- formula.
  simpa using
    source_cancelBaseChange_diagonal_action_tmul_tmul
      (R := R) (S := S) (S' := S') (M := M) a b 1 m

end
