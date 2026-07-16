import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_51_4_Krull_s_intersection_theorem
import stacks_proof.stacks_project.Chap10.Lemma_10_75_2
import stacks_proof.stacks_project.Chap10.Lemma_10_75_8
import stacks_proof.stacks_project.Chap10.Lemma_10_39_12
import stacks_proof.stacks_project.Chap10.Lemma_10_79_4
import stacks_proof.stacks_project.Chap10.Lemma_10_82_13
import stacks_proof.stacks_project.Chap10.Lemma_10_82_7
import stacks_proof.stacks_project.Chap10.Lemma_10_96_1
import stacks_proof.stacks_project.Chap10.Lemma_10_77_5

open IsLocalRing
open CategoryTheory
open CategoryTheory.ShortComplex
open scoped TensorProduct

section CriteriaForFlatness

universe u v w

variable {R : Type u} {S : Type v} {M : Type w} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Flat R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]

omit [IsLocalRing R] in
/-- Helper for Lemma 10.99.1: flatness descends to the quotient module after base change to
`R ⧸ I`. -/
lemma flat_quotient_module_of_flat
    (I : Ideal R) :
    Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
  -- Base change gives flatness of the tensor model `(R ⧸ I) ⊗[R] M`.
  have hTensor : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    Module.Flat.baseChange (R := R) (S := R ⧸ I) (M := M)
  -- Transport the owner statement across the standard quotient-tensor comparison.
  let e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] M) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).symm.extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  letI : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) := hTensor
  exact Module.Flat.of_linearEquiv e

/-- Helper for Lemma 10.99.1: if `I ≤ J`, then quotienting first by `I` and then by the image of
`J` in `R ⧸ I` identifies with quotienting directly by `J`. -/
noncomputable def quotient_closed_fiber_module_equiv_of_le
    {P : Type*} [AddCommGroup P] [Module R P]
    (I J : Ideal R) (hIJ : I ≤ J) :
    ((P ⧸ (I • (⊤ : Submodule R P))) ⧸
      (((Ideal.map (Ideal.Quotient.mk I) J) •
        (⊤ : Submodule (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))))).restrictScalars R)) ≃ₗ[R]
      P ⧸ (J • (⊤ : Submodule R P)) := by
  let IM : Submodule R P := I • (⊤ : Submodule R P)
  let JM : Submodule R P := J • (⊤ : Submodule R P)
  let K : Ideal (R ⧸ I) := Ideal.map (Ideal.Quotient.mk I) J
  have hIM_le_JM : IM ≤ JM := by
    -- The denominator grows functorially with the ideal inclusion `I ≤ J`.
    dsimp [IM, JM]
    exact Submodule.smul_mono hIJ le_rfl
  have hmap :
      JM.map (Submodule.mkQ IM) =
        ((K • (⊤ : Submodule (R ⧸ I) (P ⧸ IM))).restrictScalars R) := by
    -- First rewrite the image of `J • P` in the quotient by `I • P`, then identify it with the
    -- quotient-ring ideal action.
    calc
      JM.map (Submodule.mkQ IM) = J • (⊤ : Submodule R (P ⧸ IM)) := by
        simp [JM, IM, Submodule.map_smul'', Submodule.range_mkQ]
      _ =
          ((Ideal.map (algebraMap R (R ⧸ I)) J) •
            (⊤ : Submodule (R ⧸ I) (P ⧸ IM))).restrictScalars R := by
              symm
              simpa using
                (Ideal.smul_restrictScalars
                  (R := R) (S := R ⧸ I) (M := P ⧸ IM) J
                  (⊤ : Submodule (R ⧸ I) (P ⧸ IM)))
      _ = ((K • (⊤ : Submodule (R ⧸ I) (P ⧸ IM))).restrictScalars R) := by
            rw [Ideal.Quotient.algebraMap_eq]
  let eDenom :
      ((P ⧸ IM) ⧸ (((K • (⊤ : Submodule (R ⧸ I) (P ⧸ IM))).restrictScalars R))) ≃ₗ[R]
        ((P ⧸ IM) ⧸ JM.map (Submodule.mkQ IM)) :=
    Submodule.quotEquivOfEq
      (((K • (⊤ : Submodule (R ⧸ I) (P ⧸ IM))).restrictScalars R))
      (JM.map (Submodule.mkQ IM))
      hmap.symm
  -- The final step is the module-theoretic third isomorphism theorem.
  exact eDenom.trans (Submodule.quotientQuotientEquivQuotient IM JM hIM_le_JM)

omit [IsLocalRing R] in
/-- Helper for Lemma 10.99.1: the iterated-quotient comparison sends the double class of `x` to
its direct class modulo the larger ideal. -/
lemma quotient_closed_fiber_module_equiv_of_le_apply_mk_mk
    {P : Type*} [AddCommGroup P] [Module R P]
    (I J : Ideal R) (hIJ : I ≤ J) (x : P) :
    quotient_closed_fiber_module_equiv_of_le (P := P) I J hIJ
      (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk x := by
  -- Unfold the comparison into the denominator rewrite followed by the third-isomorphism map.
  dsimp [quotient_closed_fiber_module_equiv_of_le]
  -- The denominator rewrite disappears on this representative, leaving only the third isomorphism.
  rfl

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] in
/-- Helper for Lemma 10.99.1: once the first part is transported to quotient local rings, every
finitely generated quotient map of `u` is injective. -/
lemma smul_top_eq_map_restrictScalars
    {P : Type*} [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
    (I : Ideal R) :
    (I • (⊤ : Submodule R P)) =
      (((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S P)).restrictScalars R) := by
  -- This is the owner rewrite needed whenever quotient modules must be viewed over `S ⧸ IS`.
  simpa using
    (Ideal.smul_restrictScalars (R := R) (S := S) (M := P) I
      (⊤ : Submodule S P)).symm

/-- Helper for Lemma 10.99.1: as an `R`-module quotient, dividing by `IS • N` is the same as
dividing by `I • N`. -/
noncomputable def quotient_source_over_mapped_ideal_equiv
    (I : Ideal R) :
    (N ⧸ (((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S N)).restrictScalars R)) ≃ₗ[R]
      N ⧸ (I • (⊤ : Submodule R N)) :=
  Submodule.quotEquivOfEq
    (((Ideal.map (algebraMap R S) I) • (⊤ : Submodule S N)).restrictScalars R)
    (I • (⊤ : Submodule R N))
    (smul_top_eq_map_restrictScalars (R := R) (S := S) (P := N) I).symm

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
  [Module.Finite S N] in
/-- Helper for Lemma 10.99.1: the mapped-ideal quotient comparison sends the class of `x` to the
same class modulo `I • N`. -/
lemma quotient_source_over_mapped_ideal_equiv_apply_mk
    (I : Ideal R) (x : N) :
    quotient_source_over_mapped_ideal_equiv (R := R) (S := S) (N := N) I
      (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk x := by
  -- This quotient rewrite is definitionally the identity on representatives.
  rw [quotient_source_over_mapped_ideal_equiv]
  rw [Submodule.quotEquivOfEq_mk]

/-- Helper for Lemma 10.99.1: the quotient `N / ISN` carries the induced `R ⧸ I`-module
structure coming from `S ⧸ IS`. -/
instance quotient_source_over_mapped_ideal_module (I : Ideal R) :
    Module (R ⧸ I) (N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let T : Type v := S ⧸ J
  letI : Algebra (R ⧸ I) T :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R) (A := S) (p := I) (P := J) Ideal.le_comap_map
  exact Module.compHom _ (algebraMap (R ⧸ I) T)

omit [Module.Flat R M] in
/-- Helper for Lemma 10.99.1: once the first part is transported to quotient local rings, every
finitely generated quotient map of `u` is injective. -/
lemma closed_fiber_quotientMapByIdeal_congr
    (u : N →ₗ[R] M) {I : Ideal R} (hI : I ≤ maximalIdeal R) :
    let K : Ideal (R ⧸ I) := Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)
    let eN := quotient_closed_fiber_module_equiv_of_le (P := N) I (maximalIdeal R) hI
    let eM := quotient_closed_fiber_module_equiv_of_le (P := M) I (maximalIdeal R) hI
    eM.toLinearMap.comp (((u.reduceModIdeal I).reduceModIdeal K).restrictScalars R) =
      (u.quotientMapByIdeal (maximalIdeal R)).comp eN.toLinearMap := by
  -- Route correction: the blocker was only the representative-level normal form for the iterated
  -- quotient equivalence, which is now isolated in
  -- `quotient_closed_fiber_module_equiv_of_le_apply_mk_mk`.
  dsimp
  apply DFunLike.ext
  intro z
  -- Every class in the double quotient is represented by a double quotient element coming from `N`.
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    ((((Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)) •
      (⊤ : Submodule (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N))))).restrictScalars R)) z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) y
  -- Evaluate both composites on the same double representative and compare the resulting class.
  change
    (quotient_closed_fiber_module_equiv_of_le (P := M) I (maximalIdeal R) hI).toLinearMap
        ((((u.reduceModIdeal I).reduceModIdeal
          (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R))).restrictScalars R)
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))) =
      ((u.quotientMapByIdeal (maximalIdeal R)).comp
        (quotient_closed_fiber_module_equiv_of_le (P := N) I (maximalIdeal R) hI).toLinearMap)
        (Submodule.Quotient.mk (Submodule.Quotient.mk x))
  calc
    (quotient_closed_fiber_module_equiv_of_le (P := M) I (maximalIdeal R) hI).toLinearMap
        ((((u.reduceModIdeal I).reduceModIdeal
          (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R))).restrictScalars R)
          (Submodule.Quotient.mk (Submodule.Quotient.mk x)))
        = (quotient_closed_fiber_module_equiv_of_le (P := M) I (maximalIdeal R) hI).toLinearMap
            (Submodule.Quotient.mk (Submodule.Quotient.mk (u x))) := by
              rfl
    _ = Submodule.Quotient.mk (u x) := by
          simpa using
            quotient_closed_fiber_module_equiv_of_le_apply_mk_mk
              (P := M) I (maximalIdeal R) hI (u x)
    _ = (u.quotientMapByIdeal (maximalIdeal R))
          ((quotient_closed_fiber_module_equiv_of_le (P := N) I (maximalIdeal R) hI).toLinearMap
            (Submodule.Quotient.mk (Submodule.Quotient.mk x))) := by
              have hqx :
                  (quotient_closed_fiber_module_equiv_of_le
                      (P := N) I (maximalIdeal R) hI).toLinearMap
                    (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
                    Submodule.Quotient.mk x := by
                simpa using
                  quotient_closed_fiber_module_equiv_of_le_apply_mk_mk
                    (P := N) I (maximalIdeal R) hI x
              rw [hqx]
              rfl
    _ =
        ((u.quotientMapByIdeal (maximalIdeal R)).comp
          (quotient_closed_fiber_module_equiv_of_le (P := N) I (maximalIdeal R) hI).toLinearMap)
          (Submodule.Quotient.mk (Submodule.Quotient.mk x)) := by
            rfl

omit [IsLocalRing R] in
/-- Helper for Lemma 10.99.1: injectivity of a quotient map modulo `I` transports to injectivity
after tensoring with `R ⧸ I`. -/
lemma injective_rTensor_quotient_of_injective_quotientMapByIdeal
    {P Q : Type w} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    (φ : P →ₗ[R] Q) (I : Ideal R)
    (hφ : Function.Injective (φ.quotientMapByIdeal I)) :
    Function.Injective (φ.rTensor (R ⧸ I)) := by
  -- Rewrite the quotient module as a tensor product and compare the two induced maps.
  let eP := TensorProduct.quotTensorEquivQuotSMul P I
  let eQ := TensorProduct.quotTensorEquivQuotSMul Q I
  have hSquare :
      (φ.lTensor (R ⧸ I)).comp eP.symm.toLinearMap =
        eQ.symm.toLinearMap.comp (φ.quotientMapByIdeal I) := by
    apply DFunLike.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) z
    simp [eP, eQ, LinearMap.quotientMapByIdeal]
  have hTensor : Function.Injective (φ.lTensor (R ⧸ I)) :=
    injective_of_ladder_linearEquiv (R := R) hSquare hφ
  simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using hTensor

omit [IsLocalRing R] in
/-- Helper for Lemma 10.99.1: injectivity after tensoring with `R ⧸ I` transports back to the
quotient map modulo `I`. -/
lemma injective_quotientMapByIdeal_of_injective_rTensor_quotient
    {P Q : Type w} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    (φ : P →ₗ[R] Q) (I : Ideal R)
    (hφ : Function.Injective (φ.rTensor (R ⧸ I))) :
    Function.Injective (φ.quotientMapByIdeal I) := by
  -- Convert the tensor injectivity to the left-tensor square used by the quotient comparison.
  have hTensor : Function.Injective (φ.lTensor (R ⧸ I)) := by
    simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using hφ
  have hSquare :
      φ.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul P I =
        TensorProduct.quotTensorEquivQuotSMul Q I ∘ₗ φ.lTensor (R ⧸ I) := by
    simpa using quotientMapByIdeal_lTensor_naturality (R := R) (P := P) (Q := Q) I φ
  exact injective_of_ladder_linearEquiv (R := R) hSquare hTensor

omit [IsLocalRing R] in
/-- Helper for Lemma 10.99.1: injectivity of `φ ⊗ Q₁` and `φ ⊗ Q₃` propagates to `φ ⊗ Q₂`
across a short exact sequence `Q₁ → Q₂ → Q₃ → 0` when the target module is flat. -/
lemma rTensor_injective_of_shortExact_step
    {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [Module.Flat R Q]
    (φ : P →ₗ[R] Q)
    {Q₁ Q₂ Q₃ : Type*}
    [AddCommGroup Q₁] [Module R Q₁]
    [AddCommGroup Q₂] [Module R Q₂]
    [AddCommGroup Q₃] [Module R Q₃]
    {i : Q₁ →ₗ[R] Q₂} {π : Q₂ →ₗ[R] Q₃}
    (hi : Function.Injective i) (hExact : Function.Exact i π) (hπ : Function.Surjective π)
    (hQ₁ : Function.Injective (φ.rTensor Q₁))
    (hQ₃ : Function.Injective (φ.rTensor Q₃)) :
    Function.Injective (φ.rTensor Q₂) := by
  -- Follow the short-exact tensor chase on the difference `x - y`.
  intro x y hxy
  let d : TensorProduct R P Q₂ := x - y
  have hdQ₃ : (π.lTensor P) d = 0 := by
    apply hQ₃
    calc
      (φ.rTensor Q₃) ((π.lTensor P) d)
          = ((π.lTensor Q).comp (φ.rTensor Q₂)) d := by
              rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
                LinearMap.lTensor_comp_rTensor]
      _ = 0 := by
            change ((π.lTensor Q).comp (φ.rTensor Q₂)) (x - y) = 0
            rw [LinearMap.comp_apply, map_sub, hxy, sub_self]
            simp
  -- Exactness on the left tensor row produces a preimage in `Q₁`.
  obtain ⟨z, hz⟩ := ((lTensor_exact P hExact hπ) d).mp hdQ₃
  have hiTensor : Function.Injective (i.lTensor Q) := by
    -- Flatness of the target keeps the left arrow injective after tensoring.
    exact Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hφd : (φ.rTensor Q₂) d = 0 := by
    change (φ.rTensor Q₂) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hzTensor : (φ.rTensor Q₁) z = 0 := by
    apply hiTensor
    calc
      (i.lTensor Q) ((φ.rTensor Q₁) z)
          = ((φ.rTensor Q₂).comp (i.lTensor P)) z := by
              change ((i.lTensor Q).comp (φ.rTensor Q₁)) z =
                ((φ.rTensor Q₂).comp (i.lTensor P)) z
              rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
      _ = (φ.rTensor Q₂) d := by
            rw [LinearMap.comp_apply, hz]
      _ = 0 := hφd
  have hzZero : z = 0 := hQ₁ hzTensor
  have hdZero : d = 0 := by
    simpa [hzZero] using hz.symm
  simpa [d, sub_eq_zero] using hdZero

/-- Helper for Lemma 10.99.1: tensoring with a module over the residue field only depends on the
closed-fiber quotient of the source module. -/
noncomputable def closed_fiber_tensor_linearEquiv
    {P : Type*} [AddCommGroup P] [Module R P]
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    [Module (R ⧸ maximalIdeal R) Q] [IsScalarTower R (R ⧸ maximalIdeal R) Q] :
    TensorProduct R Q P ≃ₗ[R]
      TensorProduct (R ⧸ maximalIdeal R) Q
        (P ⧸ ((maximalIdeal R) • (⊤ : Submodule R P))) :=
  let eQuot :
      TensorProduct R (R ⧸ maximalIdeal R) P ≃ₗ[R ⧸ maximalIdeal R]
        (P ⧸ ((maximalIdeal R) • (⊤ : Submodule R P))) :=
    (TensorProduct.quotTensorEquivQuotSMul P (maximalIdeal R)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let eTensor :
      TensorProduct (R ⧸ maximalIdeal R) Q
          (TensorProduct R (R ⧸ maximalIdeal R) P) ≃ₗ[R ⧸ maximalIdeal R]
        TensorProduct (R ⧸ maximalIdeal R) Q
          (P ⧸ ((maximalIdeal R) • (⊤ : Submodule R P))) :=
    eQuot.lTensor Q
  -- First cancel the base change `(R ⧸ 𝔪) ⊗[R] P`, then apply the quotient-tensor comparison.
  (((TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ maximalIdeal R)
      (R ⧸ maximalIdeal R) Q P).symm.trans eTensor)).restrictScalars R

/-- Helper for Lemma 10.99.1: the closed-fiber tensor comparison sends a pure tensor to the pure
tensor of the quotient class. -/
@[simp] lemma closed_fiber_tensor_linearEquiv_tmul
    {P : Type*} [AddCommGroup P] [Module R P]
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    [Module (R ⧸ maximalIdeal R) Q] [IsScalarTower R (R ⧸ maximalIdeal R) Q]
    (q : Q) (x : P) :
    closed_fiber_tensor_linearEquiv (R := R) (P := P) Q (q ⊗ₜ[R] x) =
      q ⊗ₜ[R ⧸ maximalIdeal R] (Submodule.Quotient.mk x) := by
  -- Evaluate the two comparison steps on the generating pure tensor `q ⊗ x`.
  simp [closed_fiber_tensor_linearEquiv]

/-- Helper for Lemma 10.99.1: after the closed-fiber tensor comparison, tensoring `φ` with a
residue-field module is exactly tensoring the reduced map `φ mod maximalIdeal R`. -/
lemma closed_fiber_tensor_linearEquiv_symm_naturality
    {P P' : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P']
    (φ : P →ₗ[R] P')
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    [Module (R ⧸ maximalIdeal R) Q] [IsScalarTower R (R ⧸ maximalIdeal R) Q] :
    (φ.lTensor Q).comp
        (closed_fiber_tensor_linearEquiv (R := R) (P := P) Q).symm.toLinearMap =
      (closed_fiber_tensor_linearEquiv (R := R) (P := P') Q).symm.toLinearMap.comp
        ((((φ.reduceModIdeal (maximalIdeal R)).lTensor Q)).restrictScalars R) := by
  -- Check the ladder on pure tensors `q ⊗ [x]`, which generate the source tensor product.
  apply DFunLike.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro q xbar
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((maximalIdeal R) • (⊤ : Submodule R P)) xbar
    simp [closed_fiber_tensor_linearEquiv]
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Lemma 10.99.1: if `φ mod maximalIdeal R` is injective, then tensoring `φ` with any
module over the residue field is injective. -/
lemma rTensor_residueFieldModule_injective_of_mod_maximalIdeal_injective
    {P P' : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P']
    (φ : P →ₗ[R] P')
    (hφ : Function.Injective (φ.quotientMapByIdeal (maximalIdeal R)))
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    [Module (R ⧸ maximalIdeal R) Q] [IsScalarTower R (R ⧸ maximalIdeal R) Q] :
    Function.Injective (φ.rTensor Q) := by
  -- Rewrite the closed-fiber hypothesis as injectivity of the reduced map itself.
  have hReduce :
      Function.Injective (((φ.reduceModIdeal (maximalIdeal R))).restrictScalars R) := by
    simpa [quotientMapByIdeal_eq_reduceModIdeal_restrictScalars
      (R := R) (P := P) (Q := P') (J := maximalIdeal R) φ] using hφ
  have hTensorReduce :
      Function.Injective
        ((((φ.reduceModIdeal (maximalIdeal R)).lTensor Q)).restrictScalars R) := by
    -- Over the residue field, every module is flat, so tensoring preserves injectivity.
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
    letI : Module.Free (R ⧸ maximalIdeal R) Q :=
      Module.Free.of_divisionRing (R ⧸ maximalIdeal R) Q
    letI : Module.Flat (R ⧸ maximalIdeal R) Q := Module.Flat.of_free
    exact Module.Flat.lTensor_preserves_injective_linearMap
      ((φ.reduceModIdeal (maximalIdeal R))) hReduce
  -- Transport that injectivity back across the closed-fiber tensor comparison.
  have hTensor : Function.Injective (φ.lTensor Q) :=
    injective_of_ladder_linearEquiv (R := R)
      (closed_fiber_tensor_linearEquiv_symm_naturality
        (R := R) (P := P) (P' := P') φ Q)
      hTensorReduce
  simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using hTensor

/-- Helper for Lemma 10.99.1: the canonical row
`(maximalIdeal R)^n / (maximalIdeal R)^(n+1) → R / (maximalIdeal R)^(n+1) → R / (maximalIdeal R)^n`
is exact and ends in a surjection. -/
lemma maximalIdeal_pow_successor_ring_row
    (n : ℕ) :
    let m : Ideal R := maximalIdeal R
    let K : Ideal (R ⧸ (m ^ (n + 1))) := Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) (m ^ n)
    let Q₁ : Type u := ((m ^ n : Ideal R) ⧸ (m • (⊤ : Submodule R (m ^ n : Ideal R))))
    let i : Q₁ →ₗ[R] R ⧸ (m ^ (n + 1)) :=
      (((K.restrictScalars R).subtype).comp
        (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow m n).toLinearMap
      : Q₁ →ₗ[R] R ⧸ (m ^ (n + 1)))
    let π : R ⧸ (m ^ (n + 1)) →ₗ[R] R ⧸ (m ^ n) :=
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ)).toLinearMap
    Function.Injective i ∧ Function.Exact i π ∧ Function.Surjective π := by
  let m : Ideal R := maximalIdeal R
  let K : Ideal (R ⧸ (m ^ (n + 1))) := Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) (m ^ n)
  let Q₁ : Type u := ((m ^ n : Ideal R) ⧸ (m • (⊤ : Submodule R (m ^ n : Ideal R))))
  let Ksub : Submodule R (R ⧸ (m ^ (n + 1))) :=
    (K : Submodule (R ⧸ (m ^ (n + 1))) (R ⧸ (m ^ (n + 1)))).restrictScalars R
  let e : Q₁ ≃ₗ[R] K := Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow m n
  let i : Q₁ →ₗ[R] R ⧸ (m ^ (n + 1)) := (Ksub.subtype).comp e.toLinearMap
  let π : R ⧸ (m ^ (n + 1)) →ₗ[R] R ⧸ (m ^ n) :=
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ)).toLinearMap
  dsimp only
  constructor
  · -- The left arrow is the quotient-piece equivalence followed by the ideal inclusion.
    exact Ksub.subtype_injective.comp e.injective
  constructor
  · have hkerIdeal :
      RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ)) = K := by
      -- The transition map `R / 𝔪^(n+1) → R / 𝔪^n` has kernel exactly the image of `𝔪^n`.
      simpa [K] using
        (Ideal.Quotient.factor_ker (I := m ^ (n + 1)) (J := m ^ n)
          (Ideal.pow_le_pow_right n.le_succ))
    have hker : Ksub = LinearMap.ker π := by
      -- Rewrite the ring-hom kernel equality as the corresponding `R`-linear kernel equality.
      ext x
      change x ∈ K ↔ π x = 0
      have hk :
          x ∈ K ↔ x ∈ RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ)) := by
        rw [← hkerIdeal]
      simpa [π, RingHom.mem_ker] using hk
    have heRange : LinearMap.range e.toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr e.surjective
    -- Exactness is the standard `range = ker` statement after transporting the left source by `e`.
    rw [LinearMap.exact_iff]
    symm
    calc
      LinearMap.range i = Submodule.map Ksub.subtype (LinearMap.range e.toLinearMap) := by
        rw [LinearMap.range_comp]
      _ = Submodule.map Ksub.subtype ⊤ := congrArg (Submodule.map Ksub.subtype) heRange
      _ = LinearMap.range Ksub.subtype := by rw [Submodule.map_top]
      _ = Ksub := Submodule.range_subtype _
      _ = LinearMap.ker π := hker
  · -- The quotient transition map is surjective by construction.
    intro y
    rcases Ideal.Quotient.factor_surjective
        (S := m ^ (n + 1)) (T := m ^ n) (Ideal.pow_le_pow_right n.le_succ) y with ⟨x, hx⟩
    exact ⟨x, by simpa [π, Ideal.Quotient.factorₐ] using hx⟩

/-- Helper for Lemma 10.99.1: once the first part is transported to quotient local rings, every
finitely generated quotient map of `u` is injective. -/
lemma maximalIdeal_pow_stage_injective
    (u : N →ₗ[R] M)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    ∀ n : ℕ, 1 ≤ n → Function.Injective (u.quotientMapByIdeal ((maximalIdeal R) ^ n)) := by
  have hsucc :
      ∀ n : ℕ, Function.Injective (u.quotientMapByIdeal ((maximalIdeal R) ^ (n + 1))) := by
    intro n
    induction n with
    | zero =>
        rw [pow_one]
        exact hmod
    | succ n ih =>
        let m : Ideal R := maximalIdeal R
        let K : Ideal (R ⧸ (m ^ (n + 2))) :=
          Ideal.map (Ideal.Quotient.mk (m ^ (n + 2))) (m ^ (n + 1))
        let Q₁ : Type u :=
          ((m ^ (n + 1) : Ideal R) ⧸ (m • (⊤ : Submodule R (m ^ (n + 1) : Ideal R))))
        let i : Q₁ →ₗ[R] R ⧸ (m ^ (n + 2)) :=
          ((((K.restrictScalars R).subtype).comp
              (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow m (n + 1)).toLinearMap)
            : Q₁ →ₗ[R] R ⧸ (m ^ (n + 2)))
        let π : R ⧸ (m ^ (n + 2)) →ₗ[R] R ⧸ (m ^ (n + 1)) :=
          (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).toLinearMap
        have hrow :
            Function.Injective i ∧ Function.Exact i π ∧ Function.Surjective π := by
          simpa [m, K, Q₁, i, π, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            maximalIdeal_pow_successor_ring_row (R := R) (n + 1)
        rcases hrow with ⟨hi, hExact, hπ⟩
        have hQ₁ : Function.Injective (u.rTensor Q₁) :=
          rTensor_residueFieldModule_injective_of_mod_maximalIdeal_injective
            (R := R) (P := N) (P' := M) u hmod Q₁
        have hQ₃ : Function.Injective (u.rTensor (R ⧸ (m ^ (n + 1)))) :=
          injective_rTensor_quotient_of_injective_quotientMapByIdeal
            (R := R) (P := N) (Q := M) u (m ^ (n + 1)) ih
        have hQ₂ : Function.Injective (u.rTensor (R ⧸ (m ^ (n + 2)))) :=
          rTensor_injective_of_shortExact_step
            (R := R) (P := N) (Q := M) u hi hExact hπ hQ₁ hQ₃
        exact
          injective_quotientMapByIdeal_of_injective_rTensor_quotient
            (R := R) (P := N) (Q := M) u (m ^ (n + 2)) hQ₂
  intro n hn
  cases n with
  | zero =>
      cases hn
  | succ k =>
      simpa using hsucc k

omit [Module.Flat R M] in
/-- Helper for Lemma 10.99.1: once injectivity is known modulo every positive power of
`maximalIdeal R`, Krull intersection on the finite source module gives injectivity upstairs. -/
lemma injective_of_maximalIdeal_pow_stage_injective
    (u : N →ₗ[R] M)
    (hpow :
      ∀ n : ℕ, 1 ≤ n → Function.Injective (u.quotientMapByIdeal ((maximalIdeal R) ^ n)))
    (hinter :
      (⨅ n : ℕ,
        ((((Ideal.map (algebraMap R S) (maximalIdeal R)) ^ n) •
          (⊤ : Submodule S N)) : Submodule S N)) = ⊥ :=
        Ideal.iInf_pow_smul_eq_bot_of_isLocalRing
          (R := S) (M := N) (I := Ideal.map (algebraMap R S) (maximalIdeal R))
          (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne) :
    Function.Injective u := by
  -- Proof comment: a kernel element of `u` maps to zero in every quotient `N / 𝔪^n N` once the
  -- stagewise injectivity `hpow` is available, so it lies in every `𝔪^n N`. Rewriting these
  -- stages via `Ideal.map (algebraMap R S) (maximalIdeal R)` and applying `hinter` then forces the
  -- kernel element to vanish.
  intro x y hxy
  have hmem_pow (n : ℕ) (hn : 1 ≤ n) :
      x - y ∈ ((((Ideal.map (algebraMap R S) (maximalIdeal R)) ^ n) •
        (⊤ : Submodule S N)) : Submodule S N) := by
    -- First descend the equality `u x = u y` to the quotient by `𝔪^n`.
    have hxyQ :
        (Submodule.Quotient.mk (u x) :
          M ⧸ (((maximalIdeal R) ^ n) • (⊤ : Submodule R M))) =
        Submodule.Quotient.mk (u y) := by
      simpa [hxy]
    have hmk :
        (Submodule.Quotient.mk x :
          N ⧸ (((maximalIdeal R) ^ n) • (⊤ : Submodule R N))) =
        Submodule.Quotient.mk y :=
      hpow n hn <| by
        simpa [LinearMap.quotientMapByIdeal] using hxyQ
    have hpow_mem :
        x - y ∈ (((maximalIdeal R) ^ n) • (⊤ : Submodule R N) : Submodule R N) :=
      (Submodule.Quotient.eq (((maximalIdeal R) ^ n) • (⊤ : Submodule R N))).mp hmk
    -- Then transport that membership to the `S`-module filtration used by Krull intersection.
    have hmap_mem :
        x - y ∈ ((((Ideal.map (algebraMap R S) ((maximalIdeal R) ^ n)) •
          (⊤ : Submodule S N)).restrictScalars R) : Submodule R N) := by
      simpa [smul_top_eq_map_restrictScalars (R := R) (S := S) (P := N) ((maximalIdeal R) ^ n)]
        using hpow_mem
    simpa [Ideal.map_pow] using hmap_mem
  have hmem_iInf :
      x - y ∈ (⨅ n : ℕ,
        ((((Ideal.map (algebraMap R S) (maximalIdeal R)) ^ n) •
          (⊤ : Submodule S N)) : Submodule S N)) := by
    rw [Submodule.mem_iInf]
    intro n
    cases n with
    | zero =>
        simp
    | succ k =>
        exact hmem_pow (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  have hzero : x - y ∈ (⊥ : Submodule S N) := by
    simpa [hinter] using hmem_iInf
  simpa [sub_eq_zero] using hzero

include S
omit S [Module.Flat R M] [CommRing S] [Algebra R S] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [Module S N] [IsScalarTower R S N]
  [Module.Finite S N] in
/-- Helper for Lemma 10.99.1: the closed-fiber injectivity hypothesis descends to every proper
quotient local ring. -/
lemma quotient_local_closed_fiber_injective_of_hmod
    (u : N →ₗ[R] M) {I : Ideal R} (htop : I ≠ ⊤)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective ((((u.reduceModIdeal I).reduceModIdeal
      (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R))).restrictScalars R)) := by
  let K : Ideal (R ⧸ I) := Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)
  have hI : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal htop
  let eN := quotient_closed_fiber_module_equiv_of_le (P := N) I (maximalIdeal R) hI
  let eM := quotient_closed_fiber_module_equiv_of_le (P := M) I (maximalIdeal R) hI
  have hcompare :
      ((((u.reduceModIdeal I).reduceModIdeal K).restrictScalars R)).comp eN.symm.toLinearMap =
        eM.symm.toLinearMap.comp (u.quotientMapByIdeal (maximalIdeal R)) := by
    -- Pull the already-proved closed-fiber comparison back through the iterated-quotient
    -- equivalences so the injectivity ladder can be applied directly.
    apply DFunLike.ext
    intro x
    have hx :
        eM ((((u.reduceModIdeal I).reduceModIdeal K).restrictScalars R) (eN.symm x)) =
          ((u.quotientMapByIdeal (maximalIdeal R)).comp eN.toLinearMap) (eN.symm x) := by
      change
        (quotient_closed_fiber_module_equiv_of_le
            (P := M) I (maximalIdeal R) hI)
          ((((u.reduceModIdeal I).reduceModIdeal
              (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R))).restrictScalars R)
            (eN.symm x)) =
        ((u.quotientMapByIdeal (maximalIdeal R)).comp
          (quotient_closed_fiber_module_equiv_of_le
            (P := N) I (maximalIdeal R) hI).toLinearMap)
          (eN.symm x)
      exact LinearMap.congr_fun
        (closed_fiber_quotientMapByIdeal_congr (u := u) (I := I) hI)
        (eN.symm x)
    apply eM.injective
    calc
      eM ((((u.reduceModIdeal I).reduceModIdeal K).restrictScalars R) (eN.symm x))
          = ((u.quotientMapByIdeal (maximalIdeal R)).comp eN.toLinearMap) (eN.symm x) := hx
      _ = (u.quotientMapByIdeal (maximalIdeal R)) x := by
            simp [LinearMap.comp_apply]
      _ = eM (eM.symm ((u.quotientMapByIdeal (maximalIdeal R)) x)) := by
            simp [eM]
  -- The transported square now matches the injectivity-transfer lemma exactly.
  exact injective_of_ladder_linearEquiv (R := R) hcompare hmod

omit [IsNoetherianRing S] in
/-- Helper for Lemma 10.99.1: the algebra map on proper quotients of a local homomorphism is again
a local homomorphism. -/
lemma quotient_algebraMap_isLocalHom
    {I : Ideal R} (htop : I ≠ ⊤) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    IsLocalHom (algebraMap (R ⧸ I) (S ⧸ J)) := by
  let Q : Type u := R ⧸ I
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let T : Type v := S ⧸ J
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr htop
  have hI_le : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal htop
  have hJ_lt_top : J < ⊤ := by
    exact lt_of_le_of_lt (Ideal.map_mono hI_le)
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S))
  letI : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr hJ_lt_top.ne
  letI : IsLocalRing Q :=
    IsLocalRing.of_surjective' (algebraMap R Q)
      (by simpa [Q] using Ideal.Quotient.mk_surjective)
  letI : IsLocalRing T :=
    IsLocalRing.of_surjective' (algebraMap S T)
      (by simpa [T, J] using Ideal.Quotient.mk_surjective)
  letI : IsLocalHom (algebraMap R Q) :=
    IsLocalHom.of_surjective (algebraMap R Q)
      (by simpa [Q] using Ideal.Quotient.mk_surjective)
  letI : IsLocalHom (algebraMap S T) :=
    IsLocalHom.of_surjective (algebraMap S T)
      (by simpa [T, J] using Ideal.Quotient.mk_surjective)
  letI : IsLocalHom (algebraMap R T) := by
    -- The composite `R → S → S / IS` is local because both factors are.
    change IsLocalHom ((algebraMap S T).comp (algebraMap R S))
    infer_instance
  refine ⟨?_⟩
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- Reflect units back through the two quotient maps to recover a unit in `R`.
  have hrT : IsUnit (algebraMap R T r) := by
    simpa [Q, T, J] using hx
  have hrR : IsUnit r := (isUnit_map_iff (algebraMap R T) r).mp hrT
  simpa [Q] using (isUnit_map_iff (algebraMap R Q) r).mpr hrR

/-- Lemma 10.99.1 (1): if the reduction of an `R`-linear map `u : N → M` modulo the maximal ideal
of `R` is injective, then `u` itself is injective. -/
-- Route correction: the file now packages the quotient-of-quotient comparison needed for the
-- source-faithful `𝔪`-adic filtration proof now sits directly in the theorem, and the only
-- structural blocker left is the stagewise injectivity induction packaged above.
@[stacks 00ME]
theorem injective_of_mod_maximalIdeal_injective
    (u : N →ₗ[R] M)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective u := by
  -- First propagate the closed-fiber injectivity to all positive `𝔪`-power quotients, then apply
  -- the Krull-intersection helper on the finite source module. This restores the source proof's
  -- dependency direction: the main theorem is just the composition of those two packaged steps.
  have hpow :
      ∀ n : ℕ, 1 ≤ n → Function.Injective (u.quotientMapByIdeal ((maximalIdeal R) ^ n)) :=
    maximalIdeal_pow_stage_injective (R := R) (M := M) (N := N) u hmod
  have hinter :
      (⨅ n : ℕ,
        ((((Ideal.map (algebraMap R S) (maximalIdeal R)) ^ n) •
          (⊤ : Submodule S N)) : Submodule S N)) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing
      (R := S) (M := N) (I := Ideal.map (algebraMap R S) (maximalIdeal R))
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
  exact injective_of_maximalIdeal_pow_stage_injective
    (R := R) (S := S) (M := M) (N := N) u hpow hinter

/-- Helper for Lemma 10.99.1: over `R ⧸ I`, the canonical quotient owner `N / ISN` agrees with
`N / IN`. -/
noncomputable def quotient_source_owner_over_quotient_local_ring
    (I : Ideal R) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let Q : Type u := R ⧸ I
    ((N ⧸ (J • (⊤ : Submodule S N))) : Type w) ≃ₗ[Q]
      (N ⧸ (I • (⊤ : Submodule R N))) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let Q : Type u := R ⧸ I
  let eR :
      ((N ⧸ (J • (⊤ : Submodule S N))) : Type w) ≃ₗ[R]
        (N ⧸ (I • (⊤ : Submodule R N))) :=
    quotient_source_over_mapped_ideal_equiv (R := R) (S := S) (N := N) I
  let T : Type v := S ⧸ J
  letI : Algebra Q T :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R) (A := S) (p := I) (P := J) Ideal.le_comap_map
  letI : Module Q (N ⧸ (J • (⊤ : Submodule S N))) :=
    quotient_source_over_mapped_ideal_module (I := I)
  refine
    { toFun := eR
      invFun := eR.symm
      left_inv := eR.left_inv
      right_inv := eR.right_inv
      map_add' := eR.map_add
      map_smul' := ?_ }
  intro r x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule S N)) x
  calc
    eR (((Ideal.Quotient.mk I) a : Q) •
        ((J • (⊤ : Submodule S N)).mkQ y : N ⧸ (J • (⊤ : Submodule S N))))
        = eR (a • ((J • (⊤ : Submodule S N)).mkQ y : N ⧸ (J • (⊤ : Submodule S N)))) := by
            congr 1
            dsimp [quotient_source_over_mapped_ideal_module]
            calc
              (Ideal.Quotient.mk J (algebraMap R S a) : T) •
                  (Submodule.Quotient.mk y : N ⧸ (J • (⊤ : Submodule S N)))
                  = Submodule.Quotient.mk ((algebraMap R S a) • y) := by
                      rw [Module.Quotient.mk_smul_mk (M := N) (I := J)]
              _ = Submodule.Quotient.mk (a • y) := by
                    congr 1
                    exact IsScalarTower.algebraMap_smul (R := R) (A := S) a y
              _ = a • (Submodule.Quotient.mk y : N ⧸ (J • (⊤ : Submodule S N))) := by
                    rw [Submodule.Quotient.mk_smul]
    _ = a • eR ((J • (⊤ : Submodule S N)).mkQ y) := by
          exact eR.map_smul a ((J • (⊤ : Submodule S N)).mkQ y)
    _ = ((Ideal.Quotient.mk I) a : Q) • eR ((J • (⊤ : Submodule S N)).mkQ y) := by
          change a • (Submodule.Quotient.mk y : N ⧸ (I • (⊤ : Submodule R N))) =
            ((Ideal.Quotient.mk I) a : Q) •
              (Submodule.Quotient.mk y : N ⧸ (I • (⊤ : Submodule R N)))
          rw [← Submodule.Quotient.mk_smul, Module.Quotient.mk_smul_mk (M := N) (I := I)]

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
  [Module.Finite S N] in
/-- Helper for Lemma 10.99.1: the quotient-owner comparison is the identity on quotient
representatives. -/
lemma quotient_source_owner_over_quotient_local_ring_apply_mk
    (I : Ideal R) (x : N) :
    quotient_source_owner_over_quotient_local_ring (R := R) (S := S) (N := N) I
      (Submodule.Quotient.mk x :
        N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))) =
        (Submodule.Quotient.mk x : N ⧸ (I • (⊤ : Submodule R N))) := by
  simpa [quotient_source_owner_over_quotient_local_ring] using
    (quotient_source_over_mapped_ideal_equiv_apply_mk (R := R) (S := S) (N := N) I x)

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
  [Module.Finite S N] in
/-- Helper for Lemma 10.99.1: the inverse quotient-owner comparison is also the identity on
quotient representatives. -/
lemma quotient_source_owner_over_quotient_local_ring_symm_apply_mk
    (I : Ideal R) (x : N) :
    (quotient_source_owner_over_quotient_local_ring (R := R) (S := S) (N := N) I).symm
      (Submodule.Quotient.mk x : N ⧸ (I • (⊤ : Submodule R N))) =
        (Submodule.Quotient.mk x :
          N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))) := by
  let eR := quotient_source_over_mapped_ideal_equiv (R := R) (S := S) (N := N) I
  simpa [quotient_source_owner_over_quotient_local_ring] using
    (eR.symm_apply_eq.2
      (quotient_source_over_mapped_ideal_equiv_apply_mk
        (R := R) (S := S) (N := N) I x).symm)

/-- Helper for Lemma 10.99.1: after quotienting by the maximal ideal of `R ⧸ I`, the canonical
owner `N / ISN` still agrees with `N / IN`. -/
noncomputable def quotient_source_owner_closed_fiber_over_quotient_local_ring
    (I : Ideal R) [Nontrivial (R ⧸ I)] [IsLocalRing (R ⧸ I)] :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let Q : Type u := R ⧸ I
    (((N ⧸ (J • (⊤ : Submodule S N))) : Type w) ⧸
      ((maximalIdeal Q) •
        (⊤ : Submodule Q ((N ⧸ (J • (⊤ : Submodule S N))) : Type w)))) ≃ₗ[Q]
      ((N ⧸ (I • (⊤ : Submodule R N))) ⧸
        ((maximalIdeal Q) •
          (⊤ : Submodule Q (N ⧸ (I • (⊤ : Submodule R N)))))) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let Q : Type u := R ⧸ I
  let T : Type v := S ⧸ J
  letI : Algebra Q T :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R) (A := S) (p := I) (P := J) Ideal.le_comap_map
  let eQ :=
    quotient_source_owner_over_quotient_local_ring (R := R) (S := S) (N := N) I
  let Psrc :
      Submodule Q ((N ⧸ (J • (⊤ : Submodule S N))) : Type w) :=
    (maximalIdeal Q) • (⊤ : Submodule Q ((N ⧸ (J • (⊤ : Submodule S N))) : Type w))
  let Ptgt :
      Submodule Q (N ⧸ (I • (⊤ : Submodule R N))) :=
    (maximalIdeal Q) • (⊤ : Submodule Q (N ⧸ (I • (⊤ : Submodule R N))))
  have hmap : Psrc.map eQ.toLinearMap = Ptgt := by
    -- A linear equivalence carries the `𝔪_Q`-multiple of the whole module to the same ideal
    -- multiple on the target side.
    simpa [Psrc, Ptgt, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  exact Submodule.Quotient.equiv Psrc Ptgt eQ hmap

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
  [Module.Finite S N] in
/-- Helper for Lemma 10.99.1: the closed-fiber owner comparison is the identity on double quotient
representatives. -/
lemma quotient_source_owner_closed_fiber_over_quotient_local_ring_apply_mk_mk
    (I : Ideal R) [Nontrivial (R ⧸ I)] [IsLocalRing (R ⧸ I)] (x : N) :
    quotient_source_owner_closed_fiber_over_quotient_local_ring
        (R := R) (S := S) (N := N) I
      (Submodule.Quotient.mk
          (Submodule.Quotient.mk x :
            N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))) :
        ((N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))) ⧸
          ((maximalIdeal (R ⧸ I)) •
            (⊤ : Submodule (R ⧸ I)
              (N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))))))) =
        (Submodule.Quotient.mk
          (Submodule.Quotient.mk x :
            N ⧸ (I • (⊤ : Submodule R N))) :
        ((N ⧸ (I • (⊤ : Submodule R N))) ⧸
          ((maximalIdeal (R ⧸ I)) •
            (⊤ : Submodule (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N))))))) := by
  -- The induced closed-fiber map is obtained by quotienting the previous owner comparison.
  dsimp [quotient_source_owner_closed_fiber_over_quotient_local_ring]
  simp [quotient_source_owner_over_quotient_local_ring_apply_mk]

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
  [Module.Finite S N] in
/-- Helper for Lemma 10.99.1: the inverse closed-fiber owner comparison also fixes double quotient
representatives. -/
lemma quotient_source_owner_closed_fiber_over_quotient_local_ring_symm_apply_mk_mk
    (I : Ideal R) [Nontrivial (R ⧸ I)] [IsLocalRing (R ⧸ I)] (x : N) :
    (quotient_source_owner_closed_fiber_over_quotient_local_ring
        (R := R) (S := S) (N := N) I).symm
      (Submodule.Quotient.mk
          (Submodule.Quotient.mk x :
            N ⧸ (I • (⊤ : Submodule R N))) :
        ((N ⧸ (I • (⊤ : Submodule R N))) ⧸
          ((maximalIdeal (R ⧸ I)) •
            (⊤ : Submodule (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N))))))) =
        (Submodule.Quotient.mk
          (Submodule.Quotient.mk x :
            N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))) :
        ((N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))) ⧸
          ((maximalIdeal (R ⧸ I)) •
            (⊤ : Submodule (R ⧸ I)
              (N ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S N))))))) := by
  -- The inverse equivalence is again identity-on-representatives because the forward map is.
  dsimp [quotient_source_owner_closed_fiber_over_quotient_local_ring]
  simp [quotient_source_owner_over_quotient_local_ring_symm_apply_mk]

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [Module.Flat R M]
  [Module.Finite S N] in
/-- Helper for Lemma 10.99.1: the conjugated map from the canonical quotient owner has injective
closed fiber over `R ⧸ I`. -/
lemma canonical_source_mod_maximalIdeal_injective
    (u : N →ₗ[R] M) {I : Ideal R} [Nontrivial (R ⧸ I)] [IsLocalRing (R ⧸ I)] (htop : I ≠ ⊤)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let Q : Type u := R ⧸ I
    let eQ := quotient_source_owner_over_quotient_local_ring (R := R) (S := S) (N := N) I
    let v : ((N ⧸ (J • (⊤ : Submodule S N))) : Type w) →ₗ[Q]
        (M ⧸ (I • (⊤ : Submodule R M))) :=
      (u.reduceModIdeal I).comp eQ.toLinearMap
    Function.Injective (v.quotientMapByIdeal (maximalIdeal Q)) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let Q : Type u := R ⧸ I
  let T : Type v := S ⧸ J
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr htop
  letI : IsLocalRing Q :=
    IsLocalRing.of_surjective' (algebraMap R Q) (by simpa [Q] using Ideal.Quotient.mk_surjective)
  letI : Algebra Q T :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R) (A := S) (p := I) (P := J) Ideal.le_comap_map
  let eQ :=
    quotient_source_owner_over_quotient_local_ring (R := R) (S := S) (N := N) I
  let eClosed :=
    quotient_source_owner_closed_fiber_over_quotient_local_ring
      (R := R) (S := S) (N := N) I
  let v : ((N ⧸ (J • (⊤ : Submodule S N))) : Type w) →ₗ[Q]
      (M ⧸ (I • (⊤ : Submodule R M))) :=
    (u.reduceModIdeal I).comp eQ.toLinearMap
  have hmax :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal Q := by
    -- The maximal ideal of the quotient ring is exactly the image of the original maximal ideal.
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hu_closed :
      Function.Injective ((u.reduceModIdeal I).quotientMapByIdeal (maximalIdeal Q)) := by
    -- Rewrite the known quotient-local closed-fiber injectivity using the quotient-ring maximal
    -- ideal and the standard quotient-vs-reduction comparison.
    rw [← hmax]
    simpa [quotientMapByIdeal_eq_reduceModIdeal_restrictScalars
      (R := Q) (P := N ⧸ (I • (⊤ : Submodule R N)))
      (Q := M ⧸ (I • (⊤ : Submodule R M)))
      (J := Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R))
      (u.reduceModIdeal I)] using
      (quotient_local_closed_fiber_injective_of_hmod
        (R := R) (M := M) (N := N) u (I := I) htop hmod)
  let eTarget :
      ((M ⧸ (I • (⊤ : Submodule R M))) ⧸
        ((maximalIdeal Q) •
          (⊤ : Submodule Q (M ⧸ (I • (⊤ : Submodule R M)))))) ≃ₗ[Q]
        ((M ⧸ (I • (⊤ : Submodule R M))) ⧸
          ((maximalIdeal Q) •
            (⊤ : Submodule Q (M ⧸ (I • (⊤ : Submodule R M)))))) :=
    LinearEquiv.refl Q _
  have hcompare :
      (v.quotientMapByIdeal (maximalIdeal Q)).comp eClosed.symm.toLinearMap =
        eTarget.toLinearMap.comp ((u.reduceModIdeal I).quotientMapByIdeal (maximalIdeal Q)) := by
    -- Evaluate both sides on double quotient representatives; the owner comparisons are identity
    -- there, so the two maps reduce to the same explicit formula.
    apply DFunLike.ext
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
      ((maximalIdeal Q) • (⊤ : Submodule Q (N ⧸ (I • (⊤ : Submodule R N))))) z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) y
    change
      (v.quotientMapByIdeal (maximalIdeal Q))
        ((quotient_source_owner_closed_fiber_over_quotient_local_ring
            (R := R) (S := S) (N := N) I).symm
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))) =
        (eTarget.toLinearMap.comp ((u.reduceModIdeal I).quotientMapByIdeal (maximalIdeal Q)))
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))
    rw [quotient_source_owner_closed_fiber_over_quotient_local_ring_symm_apply_mk_mk]
    change
      Submodule.Quotient.mk
          (v (Submodule.Quotient.mk x)) =
        (eTarget.toLinearMap.comp ((u.reduceModIdeal I).quotientMapByIdeal (maximalIdeal Q)))
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))
    change
      Submodule.Quotient.mk
          ((u.reduceModIdeal I)
            ((quotient_source_owner_over_quotient_local_ring
                (R := R) (S := S) (N := N) I)
              (Submodule.Quotient.mk x))) =
        (eTarget.toLinearMap.comp ((u.reduceModIdeal I).quotientMapByIdeal (maximalIdeal Q)))
          (Submodule.Quotient.mk (Submodule.Quotient.mk x))
    rw [quotient_source_owner_over_quotient_local_ring_apply_mk]
    rfl
  -- The closed-fiber injectivity transfers across the quotient-owner equivalence.
  exact injective_of_ladder_linearEquiv (R := Q) hcompare hu_closed

/-- Helper for Lemma 10.99.1: for a proper ideal `I`, replaying part (1) over the quotient local
homomorphism `R ⧸ I → S ⧸ IS` shows that `u mod I` is injective. -/
lemma reduceModIdeal_injective_of_mod_maximalIdeal_injective_proper
    (u : N →ₗ[R] M) {I : Ideal R} (htop : I ≠ ⊤)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective (u.reduceModIdeal I) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let Q : Type u := R ⧸ I
  let T : Type v := S ⧸ J
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr htop
  letI : IsLocalRing Q :=
    IsLocalRing.of_surjective' (algebraMap R Q) (by simpa [Q] using Ideal.Quotient.mk_surjective)
  have hI_le : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal htop
  have hJ_lt_top : J < ⊤ := by
    -- The mapped ideal stays proper inside the local target ring.
    exact lt_of_le_of_lt (Ideal.map_mono hI_le)
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S))
  letI : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr hJ_lt_top.ne
  letI : IsLocalRing T :=
    IsLocalRing.of_surjective' (algebraMap S T) (by simpa [T, J] using Ideal.Quotient.mk_surjective)
  letI : Algebra Q T :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := R) (A := S) (p := I) (P := J) Ideal.le_comap_map
  letI : IsLocalHom (algebraMap Q T) := by
    -- The quotient map `R ⧸ I → S ⧸ IS` is local by the earlier quotient-local lemma.
    simpa [Q, T, J] using
      (quotient_algebraMap_isLocalHom (R := R) (S := S) (I := I) htop)
  let eQ :=
    quotient_source_owner_over_quotient_local_ring (R := R) (S := S) (N := N) I
  let v : ((N ⧸ (J • (⊤ : Submodule S N))) : Type w) →ₗ[Q]
      (M ⧸ (I • (⊤ : Submodule R M))) :=
    (u.reduceModIdeal I).comp eQ.toLinearMap
  have hv_closed :
      Function.Injective (v.quotientMapByIdeal (maximalIdeal Q)) :=
    canonical_source_mod_maximalIdeal_injective
      (R := R) (S := S) (M := M) (N := N) u (I := I) htop hmod
  letI : Module.Flat Q (M ⧸ (I • (⊤ : Submodule R M))) :=
    flat_quotient_module_of_flat (R := R) (M := M) I
  letI : Module.Finite S ((N ⧸ (J • (⊤ : Submodule S N))) : Type w) := by
    infer_instance
  letI : Module.Finite T ((N ⧸ (J • (⊤ : Submodule S N))) : Type w) :=
    Module.Finite.of_restrictScalars_finite S T
      ((N ⧸ (J • (⊤ : Submodule S N))) : Type w)
  letI : IsScalarTower Q T ((N ⧸ (J • (⊤ : Submodule S N))) : Type w) :=
    IsScalarTower.of_compHom Q T ((N ⧸ (J • (⊤ : Submodule S N))) : Type w)
  have hv_inj : Function.Injective v := by
    -- Route correction: apply part (1) over the quotient local homomorphism to the canonical
    -- owner `N / ISN`, not to the transported owner `N / IN`.
    exact injective_of_mod_maximalIdeal_injective
      (R := Q) (S := T)
      (M := M ⧸ (I • (⊤ : Submodule R M)))
      (N := ((N ⧸ (J • (⊤ : Submodule S N))) : Type w))
      v hv_closed
  -- Finally transfer injectivity back along the single owner equivalence `N / ISN ≃ N / IN`.
  intro x y hxy
  exact eQ.symm.injective <| hv_inj <| by
    simpa [v, hxy]

/-- Helper for Lemma 10.99.1: once the first part is transported to quotient local rings, every
finitely generated quotient map of `u` is injective. -/
lemma quotientMapByIdeal_injective_of_mod_maximalIdeal_injective_fg
    (u : N →ₗ[R] M)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    ∀ I : Ideal R, I.FG → Function.Injective (u.quotientMapByIdeal I) := by
  intro I hI
  by_cases htop : I = ⊤
  · -- The top-ideal quotient is the zero map between zero modules, hence injective.
    subst htop
    intro x y _
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective (⊤ • (⊤ : Submodule R N)) x
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective (⊤ • (⊤ : Submodule R N)) y
    exact (Submodule.Quotient.eq (⊤ • (⊤ : Submodule R N))).2 (by simp)
  · -- Route correction: the quotient-local source denominator is now packaged explicitly by
    -- `quotient_source_over_mapped_ideal_equiv`; the remaining work is only to transfer the
    -- canonical `S ⧸ IS`-module structure from `N / ISN` onto `N / IN`, then replay part (1)
    -- over `R ⧸ I → S ⧸ IS`.
    have hreduce :
        Function.Injective (u.reduceModIdeal I) :=
      reduceModIdeal_injective_of_mod_maximalIdeal_injective_proper
        (R := R) (S := S) (M := M) (N := N) u htop hmod
    -- Finally identify the quotient map `u mod I` with `u.quotientMapByIdeal I`.
    simpa [quotientMapByIdeal_eq_reduceModIdeal_restrictScalars
      (R := R) (P := N) (Q := M) (J := I) u] using hreduce

/-- Lemma 10.99.1 (2): under the same hypothesis, the quotient of `M` by the image of `u` is flat
over `R`. -/
-- Proof sketch: use the injectivity from part (1) to obtain a short exact sequence
-- `0 → N → M → M / range u → 0`; then promote the closed-fiber hypothesis to injectivity modulo
-- every finitely generated ideal, use Lemma `10.82.13` to get universal injectivity of `u`, and
-- finally apply the universally exact flat-cokernel theorem.
@[stacks 00ME]
theorem flat_quotient_of_mod_maximalIdeal_injective
    (u : N →ₗ[R] M)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    Module.Flat R (M ⧸ LinearMap.range u) := by
  have hu : Function.Injective u :=
    injective_of_mod_maximalIdeal_injective (R := R) (S := S) (M := M) (N := N) u hmod
  have hfg :
      ∀ I : Ideal R, I.FG → Function.Injective (u.quotientMapByIdeal I) :=
    quotientMapByIdeal_injective_of_mod_maximalIdeal_injective_fg
      (R := R) (S := S) (M := M) (N := N) u hmod
  have hUnivMax :
      LinearMap.UniversallyInjective.{u, w, w, max u w} u :=
    (LinearMap.universallyInjective_iff_injective_mod_finite_ideal
      (R := R) (M := N) (M' := M) u).2 hfg
  -- Use the flatness criterion and the same three-row tensor chase as in the universally exact
  -- cokernel lemma, with universal injectivity supplied by `hUnivMax`.
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ i hi
  let Q' : Type (max u w) := Q ⧸ LinearMap.range i
  let π : Q →ₗ[R] Q' := Submodule.mkQ (LinearMap.range i)
  have hExactCol : Function.Exact i π := LinearMap.exact_map_mkQ_range i
  have hSurjCol : Function.Surjective π := Submodule.mkQ_surjective _
  have hExactRow : Function.Exact u (LinearMap.range u).mkQ := LinearMap.exact_map_mkQ_range u
  have hSurjRow : Function.Surjective ((LinearMap.range u).mkQ) := Submodule.mkQ_surjective _
  have hRightInj : Function.Injective (u.rTensor Q') := hUnivMax Q' inferInstance inferInstance
  have hMiddleInj : Function.Injective (i.lTensor M) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    hExactRow hSurjRow hExactCol hSurjCol hRightInj hMiddleInj

omit S

end CriteriaForFlatness
