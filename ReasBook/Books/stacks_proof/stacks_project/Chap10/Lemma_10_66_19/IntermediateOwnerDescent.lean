import StacksProject_2024.Chap10.Lemma_10_66_19.OwnerDirectSumDescent

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w x

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type x} [AddCommGroup M] [Module R M]

local notation "Rₖ" => R ⊗[k] K
local notation "Mₖ" => Rₖ ⊗[R] M

local instance : Module Rₖ Mₖ :=
  TensorProduct.leftModule

/-- Helper for Lemma 10.66.19: the canonical map on the field tensor factor equips
`R ⊗[k] K` with its natural `R ⊗[k] L`-algebra structure. -/
instance ringTensorToTopAlgebra (L : IntermediateField k K) :
    Algebra (R ⊗[k] L) Rₖ :=
  (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K)).toAlgebra

/-- Helper for Lemma 10.66.19: the canonical tensor-factor algebra maps from `R` to
`R ⊗[k] L` and then to `R ⊗[k] K` compose to the usual map `R → R ⊗[k] K`. -/
instance ringTensorToTopIsScalarTower (L : IntermediateField k K) :
    IsScalarTower R (R ⊗[k] L) Rₖ :=
  by
    refine IsScalarTower.of_algebraMap_eq' (R := R) (S := R ⊗[k] L) (A := Rₖ) ?_
    ext r
    simp [RingHom.algebraMap_toAlgebra]

/-- Helper for Lemma 10.66.19: transport across an `R`-linear equivalence preserves the torsion
ideal of an element. -/
theorem torsionOf_linearEquiv_eq
    {A : Type*} {N : Type*} {N' : Type*} [CommRing A]
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') (x : N) :
    Ideal.torsionOf A N' (e x) = Ideal.torsionOf A N x := by
  -- Compare the annihilator condition pointwise and pull equality back along the equivalence.
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro ha
    apply e.injective
    simpa using ha
  · intro ha
    simpa using congrArg e ha

/-- Helper for Lemma 10.66.19: transporting a tensor from a smaller intermediate field stage into
a larger one does not change its image in `R ⊗[k] K`. -/
theorem ringTensor_map_comp_inclusion
    {L L' : IntermediateField k K} (hLL' : L ≤ L') (x : R ⊗[k] L) :
    Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L' K)
      (Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion hLL') x) =
        Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) x := by
  -- Check the transport identity on pure tensors and extend additively.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r a
    simp [IntermediateField.coe_inclusion]
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Lemma 10.66.19: every element of `R ⊗[k] K` is already defined over a finitely
generated intermediate field of `K / k`. -/
theorem exists_finitely_generated_intermediate_field_ringTensor
    (x : Rₖ) :
    ∃ (L : IntermediateField k K) (_ : L.FG) (xL : R ⊗[k] L),
      Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) xL = x := by
  classical
  -- Build the stage recursively from a tensor decomposition and enlarge intermediate fields by
  -- taking suprema in the additive case.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · refine ⟨⊥, IntermediateField.fg_bot, 0, ?_⟩
    simp
  · intro r a
    let L : IntermediateField k K := IntermediateField.adjoin k ({a} : Set K)
    have haL : a ∈ L := IntermediateField.subset_adjoin k ({a} : Set K) (by simp)
    refine
      ⟨L, IntermediateField.fg_adjoin_of_finite (F := k) (E := K) (Set.finite_singleton a),
        r ⊗ₜ[k] ⟨a, haL⟩, ?_⟩
    simp [L]
  · intro x y hx hy
    rcases hx with ⟨Lx, hLx, xL, hxL⟩
    rcases hy with ⟨Ly, hLy, yL, hyL⟩
    let L : IntermediateField k K := Lx ⊔ Ly
    let xL' : R ⊗[k] L :=
      Algebra.TensorProduct.map (AlgHom.id k R)
        (IntermediateField.inclusion (show Lx ≤ L from le_sup_left)) xL
    let yL' : R ⊗[k] L :=
      Algebra.TensorProduct.map (AlgHom.id k R)
        (IntermediateField.inclusion (show Ly ≤ L from le_sup_right)) yL
    refine ⟨L, IntermediateField.fg_sup hLx hLy, xL' + yL', ?_⟩
    -- After transporting both stages into the union stage, the ambient tensor is just the sum of
    -- the original two ambient images.
    calc
      Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) (xL' + yL') =
          Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) xL' +
            Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) yL' := by
              simp [xL', yL']
      _ =
          Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k Lx K) xL +
            Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k Ly K) yL := by
              rw [ringTensor_map_comp_inclusion (k := k) (K := K) (R := R)
                    (show Lx ≤ L from le_sup_left) xL,
                ringTensor_map_comp_inclusion (k := k) (K := K) (R := R)
                    (show Ly ≤ L from le_sup_right) yL]
      _ = x + y := by
          simpa [hxL, hyL]

/-- Helper for Lemma 10.66.19: the left-factor map `R ⊗[k] L → R ⊗[k] K` is `R`-linear because
it fixes the `R`-coefficient and only changes the field factor. -/
theorem ringTensor_map_to_top_smul
    (L : IntermediateField k K) (r : R) (x : R ⊗[k] L) :
    Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) (r • x) =
      r • Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K) x := by
  -- Verify `R`-linearity on pure tensors and extend additively.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r' a
    change
      (Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K))
          ((r * r') ⊗ₜ[k] a) =
        (r * r') ⊗ₜ[k] ↑a
    simp
  · intro x y hx hy
    simp [smul_add, map_add, hx, hy]

/-- Helper for Lemma 10.66.19: the canonical map `R ⊗[k] L → R ⊗[k] K` viewed as an `R`-linear
map on the left tensor factor. -/
abbrev ringTensorToTopLinearMap (L : IntermediateField k K) :
    (R ⊗[k] L) →ₗ[R] Rₖ :=
  { toFun := Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K)
    map_add' := by
      intro x y
      simp [map_add]
    map_smul' := ringTensor_map_to_top_smul (k := k) (K := K) (R := R) L }

/-- Helper for Lemma 10.66.19: the canonical owner-stage map from an intermediate field `L`
into the final `K`-stage is tensoring the left factor along `R ⊗[k] L → R ⊗[k] K`. -/
abbrev ownerStageMap (L : IntermediateField k K) :
    ((R ⊗[k] L) ⊗[R] M) →ₗ[R] Mₖ :=
  TensorProduct.map
    (ringTensorToTopLinearMap (k := k) (K := K) (R := R) L)
    (LinearMap.id : M →ₗ[R] M)

/-- Helper for Lemma 10.66.19: after rewriting the two-step tensor base change by
`cancelBaseChange`, the universal element `1 ⊗ zL` is exactly the owner witness obtained by
transporting `zL` from the `L`-stage to the final `K`-stage. -/
theorem ownerStageMap_eq_cancelBaseChange_one_tmul
    (L : IntermediateField k K) (zL : ((R ⊗[k] L) ⊗[R] M)) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R (R ⊗[k] L) Rₖ Rₖ M)
      ((1 : Rₖ) ⊗ₜ[(R ⊗[k] L)] zL) =
        ownerStageMap (k := k) (K := K) (R := R) (M := M) L zL := by
  -- Compare both sides on pure tensors, where `cancelBaseChange_tmul` and the scalar action on
  -- `1 : R ⊗[k] K` both reduce to the canonical map on the left tensor factor.
  refine TensorProduct.induction_on zL ?_ ?_ ?_
  · rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  · intro x m
    simpa [ownerStageMap, ringTensorToTopLinearMap, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, TensorProduct.map_tmul] using
      (TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul
        R (R ⊗[k] L) Rₖ (1 : Rₖ) m x)
  · intro x y hx hy
    rw [TensorProduct.tmul_add, LinearEquiv.map_add, hx, hy, LinearMap.map_add]

/-- Helper for Lemma 10.66.19: the canonical map `R ⊗[k] L → R ⊗[k] K` is flat because it is
obtained by tensoring the flat field extension `L → K` with `R`. -/
theorem ringTensorToTop_moduleFlat (L : IntermediateField k K) :
    Module.Flat (R ⊗[k] L) Rₖ := by
  -- The source proof uses this flatness twice: once for annihilator base change and once for
  -- going down along the intermediate-field stage.
  have hflatL :
      RingHom.Flat ((IsScalarTower.toAlgHom k L K).toRingHom) := by
    simpa using
      (RingHom.Flat.of_isField (R := L) (S := K) (Field.toIsField L)
        ((IsScalarTower.toAlgHom k L K).toRingHom))
  have hflatTensor :
      RingHom.Flat
        ((Algebra.TensorProduct.map (AlgHom.id k R) (IsScalarTower.toAlgHom k L K)).toRingHom) := by
    simpa using
      (RingHom.Flat.tensorProductMap (R := k) (S := k) (A := R) (B := L) (C := R) (D := K)
        (f := AlgHom.id k R) (g := IsScalarTower.toAlgHom k L K)
        (by simpa using (RingHom.Flat.id R)) hflatL)
  simpa [RingHom.flat_algebraMap_iff, ringTensorToTopAlgebra, RingHom.algebraMap_toAlgebra]
    using hflatTensor

/-- Helper for Lemma 10.66.19: the left-factor map `R ⊗[k] L → R ⊗[k] L'` is `R`-linear for the
same reason: only the field component changes. -/
theorem ringTensor_map_inclusion_smul
    {L L' : IntermediateField k K} (hLL' : L ≤ L') (r : R) (x : R ⊗[k] L) :
    Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion hLL') (r • x) =
      r • Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion hLL') x := by
  -- Again reduce to pure tensors, where the `R`-coefficient is untouched by inclusion.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro r' a
    change
      (Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion hLL'))
          ((r * r') ⊗ₜ[k] a) =
        (r * r') ⊗ₜ[k] (IntermediateField.inclusion hLL' a)
    simp
  · intro x y hx hy
    simp [smul_add, map_add, hx, hy]

/-- Helper for Lemma 10.66.19: the canonical `R`-linear map on the left tensor factor induced by
an inclusion of intermediate fields. -/
abbrev ringTensorInclusionLinearMap
    {L L' : IntermediateField k K} (hLL' : L ≤ L') :
    (R ⊗[k] L) →ₗ[R] (R ⊗[k] L') :=
  { toFun := Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion hLL')
    map_add' := by
      intro x y
      simp [map_add]
    map_smul' := ringTensor_map_inclusion_smul (k := k) (K := K) (R := R) hLL' }

/-- Helper for Lemma 10.66.19: moving an owner witness from `L` to a larger intermediate field
`L'` only tensors the left factor along the induced ring map `R ⊗[k] L → R ⊗[k] L'`. -/
abbrev ownerInclusionMap
    {L L' : IntermediateField k K} (hLL' : L ≤ L') :
    ((R ⊗[k] L) ⊗[R] M) →ₗ[R] ((R ⊗[k] L') ⊗[R] M) :=
  TensorProduct.map
    (ringTensorInclusionLinearMap (k := k) (K := K) (R := R) hLL')
    (LinearMap.id : M →ₗ[R] M)

/-- Helper for Lemma 10.66.19: transporting an owner witness from `L` to a larger intermediate
field `L'` and then to `K` agrees with transporting it directly from `L` to `K`. -/
theorem ownerStageMap_comp_inclusion
    {L L' : IntermediateField k K} (hLL' : L ≤ L')
    (z : ((R ⊗[k] L) ⊗[R] M)) :
    ownerStageMap (k := k) (K := K) (R := R) (M := M) L'
        (ownerInclusionMap (k := k) (K := K) (R := R) (M := M) hLL' z) =
      ownerStageMap (k := k) (K := K) (R := R) (M := M) L z := by
  -- Check the compatibility first on pure tensors, then extend additively across the owner tensor.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [ownerStageMap]
  · intro x m
    simpa [ownerStageMap, TensorProduct.map_tmul] using
      congrArg (fun t : Rₖ ↦ t ⊗ₜ[R] m)
        (ringTensor_map_comp_inclusion (k := k) (K := K) (R := R) hLL' x)
  · intro x y hx hy
    simp [ownerStageMap, hx, hy]

/-- Helper for Lemma 10.66.19: every owner witness in `((R ⊗[k] K) ⊗[R] M)` is already defined
over a finitely generated intermediate field stage. -/
theorem exists_finitely_generated_intermediate_owner_witness
    (z : Mₖ) :
    ∃ (L : IntermediateField k K) (_ : L.FG) (zL : ((R ⊗[k] L) ⊗[R] M)),
      ownerStageMap (k := k) (K := K) (R := R) (M := M) L zL = z := by
  classical
  -- Follow the source proof literally: descend each left tensor coefficient and enlarge stages by
  -- taking suprema in the additive step.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · refine ⟨⊥, IntermediateField.fg_bot, 0, ?_⟩
    simp [ownerStageMap]
  · intro x m
    rcases
      exists_finitely_generated_intermediate_field_ringTensor
        (k := k) (K := K) (R := R) x with
      ⟨L, hLfg, xL, hxL⟩
    refine ⟨L, hLfg, xL ⊗ₜ[R] m, ?_⟩
    -- A pure owner tensor descends once its coefficient in `R ⊗[k] K` does.
    simpa [ownerStageMap, TensorProduct.map_tmul] using
      congrArg (fun t : Rₖ ↦ t ⊗ₜ[R] m) hxL
  · intro x y hx hy
    rcases hx with ⟨Lx, hLx, xL, hxL⟩
    rcases hy with ⟨Ly, hLy, yL, hyL⟩
    let L : IntermediateField k K := Lx ⊔ Ly
    let xL' : ((R ⊗[k] L) ⊗[R] M) :=
      ownerInclusionMap (k := k) (K := K) (R := R) (M := M)
        (show Lx ≤ L from le_sup_left) xL
    let yL' : ((R ⊗[k] L) ⊗[R] M) :=
      ownerInclusionMap (k := k) (K := K) (R := R) (M := M)
        (show Ly ≤ L from le_sup_right) yL
    refine ⟨L, IntermediateField.fg_sup hLx hLy, xL' + yL', ?_⟩
    -- Once both witnesses are moved to the common stage `L`, the ambient owner witness is their
    -- sum, exactly as in the source descent on finitely many coefficients.
    calc
      ownerStageMap (k := k) (K := K) (R := R) (M := M) L (xL' + yL') =
          ownerStageMap (k := k) (K := K) (R := R) (M := M) L xL' +
            ownerStageMap (k := k) (K := K) (R := R) (M := M) L yL' := by
              simp [ownerStageMap]
      _ =
          ownerStageMap (k := k) (K := K) (R := R) (M := M) Lx xL +
            ownerStageMap (k := k) (K := K) (R := R) (M := M) Ly yL := by
              rw [ownerStageMap_comp_inclusion (k := k) (K := K) (R := R) (M := M)
                    (show Lx ≤ L from le_sup_left) xL,
                ownerStageMap_comp_inclusion (k := k) (K := K) (R := R) (M := M)
                    (show Ly ≤ L from le_sup_right) yL]
      _ = x + y := by
          simpa [hxL, hyL]

/-- Helper for Lemma 10.66.19: the annihilator of a descended owner witness transports to the
ambient `K`-stage by extending ideals along `R ⊗[k] L → R ⊗[k] K`. -/
theorem ownerStageMap_torsionOf_eq_map
    (L : IntermediateField k K) (zL : ((R ⊗[k] L) ⊗[R] M)) :
    Ideal.torsionOf Rₖ Mₖ
        (ownerStageMap (k := k) (K := K) (R := R) (M := M) L zL) =
      Ideal.map (algebraMap (R ⊗[k] L) Rₖ)
        (Ideal.torsionOf (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) zL) := by
  -- Route correction: instead of postulating a global flatness theorem for
  -- `R ⊗[k] L → R ⊗[k] K`, derive flatness locally from the field map `L → K`, tensor it with
  -- `R`, and then compare the transported witness with `ownerStageMap`.
  letI : Module.Flat (R ⊗[k] L) Rₖ :=
    ringTensorToTop_moduleFlat (k := k) (K := K) (R := R) L
  -- First identify the ambient annihilator as the annihilator of the universal tensor `1 ⊗ zL`,
  -- then apply the flat base-change theorem from Lemma `10.40.4`.
  calc
    Ideal.torsionOf Rₖ Mₖ
        (ownerStageMap (k := k) (K := K) (R := R) (M := M) L zL) =
      Ideal.torsionOf Rₖ (Rₖ ⊗[(R ⊗[k] L)] (((R ⊗[k] L) ⊗[R] M)))
        ((1 : Rₖ) ⊗ₜ[(R ⊗[k] L)] zL) := by
          simpa [ownerStageMap_eq_cancelBaseChange_one_tmul (k := k) (K := K) (R := R)
            (M := M) L zL] using
            (torsionOf_linearEquiv_eq
              (A := Rₖ)
              (e := TensorProduct.AlgebraTensorModule.cancelBaseChange
                R (R ⊗[k] L) Rₖ Rₖ M)
              ((1 : Rₖ) ⊗ₜ[(R ⊗[k] L)] zL))
    _ =
      Ideal.map (algebraMap (R ⊗[k] L) Rₖ)
        (Ideal.torsionOf (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) zL) := by
          symm
          simpa using
            (Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat
              (R := R ⊗[k] L) (S := Rₖ) (M := ((R ⊗[k] L) ⊗[R] M)) zL)

/-- Helper for Lemma 10.66.19: once the annihilator upstairs has been rewritten as an ideal map,
any minimal prime above it contracts to a minimal prime above the downstairs annihilator. -/
theorem under_mem_minimalPrimes_of_mem_minimalPrimes_map
    (L : IntermediateField k K) (I : Ideal (R ⊗[k] L)) {q : Ideal Rₖ}
    (hq : q ∈ (Ideal.map (algebraMap (R ⊗[k] L) Rₖ) I).minimalPrimes) :
    q.under (R ⊗[k] L) ∈ I.minimalPrimes := by
  haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  let qL : Ideal (R ⊗[k] L) := q.under (R ⊗[k] L)
  haveI : qL.IsPrime := by
    dsimp [qL]
    infer_instance
  letI : Module.Flat (R ⊗[k] L) Rₖ :=
    ringTensorToTop_moduleFlat (k := k) (K := K) (R := R) L
  -- Prove minimality downstairs by contradiction: a strictly smaller prime under `qL` lifts by
  -- going down to a strictly smaller prime under `q`, contradicting minimality upstairs.
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · exact (Ideal.map_le_iff_le_comap).mp hq.1.2
  · intro p hp hpqL
    letI : p.IsPrime := hp.1
    by_contra hpne
    have hpLt : p < qL := lt_of_le_of_ne hpqL fun hEq ↦ hpne hEq.ge
    haveI : q.LiesOver qL := by
      dsimp [qL]
      infer_instance
    obtain ⟨q', hq'Lt, hq'Prime, hq'Over⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt
        (R := R ⊗[k] L) (S := Rₖ) (p := p) (q := qL) q hpLt
    haveI : q'.IsPrime := hq'Prime
    haveI : q'.LiesOver p := hq'Over
    have hmapLe : Ideal.map (algebraMap (R ⊗[k] L) Rₖ) I ≤ q' := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [q'.over_def p] using hp.2
    have hqLe : q ≤ q' := hq.2 ⟨inferInstance, hmapLe⟩ hq'Lt.le
    exact hq'Lt.not_ge hqLe

/-- Helper for Lemma 10.66.19: once the annihilator-minimal-prime witness has been transported
downstairs, the first source step packages it as a weakly associated prime over a finitely
generated intermediate field. -/
theorem exists_finitely_generated_intermediate_weakAss_descent_owner
    (q : Ideal Rₖ) (hq : q ∈ weaklyAssociatedPrimes Rₖ Mₖ) :
    ∃ (L : IntermediateField k K) (_ : L.FG) (qL : Ideal (R ⊗[k] L)),
      qL ∈ weaklyAssociatedPrimes (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) ∧
        qL.under R = q.under R := by
  rcases hq with ⟨z, hz⟩
  rcases
    exists_finitely_generated_intermediate_owner_witness
      (k := k) (K := K) (R := R) (M := M) z with
    ⟨L, hLfg, zL, hzL⟩
  let I : Ideal (R ⊗[k] L) := Ideal.torsionOf (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) zL
  let qL : Ideal (R ⊗[k] L) := q.under (R ⊗[k] L)
  have hz' :
      q ∈ (Ideal.torsionOf Rₖ Mₖ
        (ownerStageMap (k := k) (K := K) (R := R) (M := M) L zL)).minimalPrimes := by
    simpa [hzL] using hz
  have hminimal_upstairs :
      q ∈ (Ideal.map (algebraMap (R ⊗[k] L) Rₖ) I).minimalPrimes := by
    -- Rewrite the upstairs annihilator using the descended witness `zL`.
    simpa [I, ownerStageMap_torsionOf_eq_map (k := k) (K := K) (R := R) (M := M) L zL]
      using hz'
  have hminimal_downstairs : qL ∈ I.minimalPrimes := by
    -- Contract the minimal-prime witness along the flat intermediate-field base change.
    simpa [qL] using
      under_mem_minimalPrimes_of_mem_minimalPrimes_map
        (k := k) (K := K) (R := R) L I hminimal_upstairs
  refine ⟨L, hLfg, qL, ?_, ?_⟩
  · -- The contracted prime is weakly associated to the descended witness `zL`.
    exact ⟨zL, hminimal_downstairs⟩
  · -- Contracting first to `R ⊗[k] L` and then to `R` is the same as contracting directly to `R`.
    change Ideal.comap (algebraMap R (R ⊗[k] L)) (Ideal.comap (algebraMap (R ⊗[k] L) Rₖ) q) =
      Ideal.comap (algebraMap R Rₖ) q
    rw [Ideal.comap_comap]
    rfl

/-- Helper for Lemma 10.66.19: a finitely generated intermediate field admits a purely
transcendental subextension over which it is finite-dimensional. -/
theorem exists_purely_transcendental_subextension_finiteDimensional
    (L : IntermediateField k K) (hLfg : L.FG) :
    ∃ x : Fin (Cardinal.toNat (Algebra.trdeg k L)) → L,
      IsTranscendenceBasis k x ∧
        FiniteDimensional (IntermediateField.adjoin k (Set.range x)) L := by
  letI : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hLfg
  -- Choose a transcendence basis of the finitely generated field and reindex it by a finite set.
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  obtain ⟨x, hx, hxAdjoin⟩ :=
    exists_fin_reindexed_transcendence_basis (k := k) (K := L) hs
  refine ⟨x, hx, ?_⟩
  -- The generated rational-function stage is then finite-dimensional inside `L`.
  simpa [hxAdjoin] using
    (finiteDimensional_over_adjoin_of_isTranscendenceBasis (k := k) (K := L) hx)

end
