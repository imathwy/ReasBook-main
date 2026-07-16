import stacks_proof.stacks_project.Chap10.Definition_10_54_1
import stacks_proof.stacks_project.Chap10.Lemma_10_99_1
import stacks_proof.stacks_project.Chap10.Lemma_10_127_13
import Mathlib.Tactic.StacksAttribute

open IsLocalRing
open scoped TensorProduct

universe u v w x y

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/- Domain-style sampling for Lemma 10.128.4:
- primary domain: the local flatness criterion for finitely presented modules over a local
  homomorphism, with the closed-fiber injectivity hypothesis on the quotient map modulo the
  maximal ideal and a standard residue-field tensor reformulation;
- sampled owner declarations:
  `LinearMap.quotientMapByIdeal`,
  `TensorProduct.quotTensorEquivQuotSMul`,
  `injective_of_mod_maximalIdeal_injective`,
  `flat_quotient_of_mod_maximalIdeal_injective`;
- best owner abstraction: the source-facing closed-fiber map is the reduction map
  `LinearMap.quotientMapByIdeal (maximalIdeal R)`; the residue-field tensor formulation is only a
  bridge to this owner via `TensorProduct.quotTensorEquivQuotSMul`;
- primitive data: the local map `R → S`, the essentially finitely presented `R`-algebra structure
  on `S`, canonically exposed in Chapter 10 as
  `RingHom.EssFinitePresentation (algebraMap R S)`, the finitely presented `S`-modules `M` and
  `N`, the `R`-flatness of `N`, and the injectivity of the closed-fiber map of `u`;
- derived API: injectivity of `u` and `R`-flatness of the quotient by its image.

Source/core/bridge triage:
- `source-facing`: Lemma 10.128.4 itself, phrased with injectivity of
  `M / maximalIdeal R • M → N / maximalIdeal R • N`;
- `core/canonical`: `Function.Injective`, `Module.Flat`, and the Chapter 10 owner theorems
  `injective_of_mod_maximalIdeal_injective` and
  `flat_quotient_of_mod_maximalIdeal_injective`;
- `bridge/view`: the standard closed-fiber identification
  `(R ⧸ maximalIdeal R) ⊗[R] M ≃ M ⧸ maximalIdeal R • ⊤`, implemented by
  `TensorProduct.quotTensorEquivQuotSMul`, converts the source-facing hypothesis to the quotient
  criterion used by the core owner theorems.
-/

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 4: the quotient map modulo an ideal is compatible with the
standard identification of quotient modules with tensor products over the quotient ring. -/
private theorem quotientMapByIdeal_lTensor_naturality_anyUniverse
    {P Q : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (J : Ideal R) (φ : P →ₗ[R] Q) :
    φ.quotientMapByIdeal J ∘ₗ TensorProduct.quotTensorEquivQuotSMul P J =
      TensorProduct.quotTensorEquivQuotSMul Q J ∘ₗ φ.lTensor (R ⧸ J) := by
  -- It is enough to check the square on pure tensors; every quotient scalar has a representative
  -- in `R`, and the defining formula for `quotientMapByIdeal` then matches both sides.
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 4: injectivity transfers across a commuting square whose
vertical arrows are linear equivalences. -/
private theorem injective_of_ladder_linearEquiv_anyUniverse
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {eA : A ≃ₗ[R] A'} {eB : B ≃ₗ[R] B'}
    (h : g ∘ₗ eA = eB ∘ₗ f) (hf : Function.Injective f) :
    Function.Injective g := by
  -- Pull two equal outputs back through the vertical equivalences and use injectivity of the
  -- source horizontal map.
  intro x y hxy
  apply eA.symm.injective
  apply hf
  apply eB.injective
  calc
    eB (f (eA.symm x)) = g x := by
      simpa using (LinearMap.congr_fun h (eA.symm x)).symm
    _ = g y := hxy
    _ = eB (f (eA.symm y)) := by
      simpa using LinearMap.congr_fun h (eA.symm y)

-- Proof sketch: use the canonical closed-fiber identification
-- `(R ⧸ maximalIdeal R) ⊗[R] M ≃ M / maximalIdeal R • M` to convert the source-facing residue-field
-- injectivity hypothesis into injectivity of the quotient reduction map
-- `M / maximalIdeal R • M → N / maximalIdeal R • N`. Then apply the owner theorems from Lemma
-- `10.99.1` to obtain injectivity of `u` and flatness of its quotient.
/-- Bridge theorem: injectivity after tensoring with the residue field implies injectivity of the
reduction map modulo `maximalIdeal R`, which is the canonical quotient criterion used by Lemma
`10.99.1`. -/
theorem injective_mod_maximalIdeal_of_lTensor_residueField_injective
    (u : M →ₗ[S] N)
    (hbar : Function.Injective ((u.restrictScalars R).lTensor (ResidueField R))) :
    Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := by
  -- View the residue-field tensor hypothesis in the quotient-ring spelling required by
  -- `TensorProduct.quotTensorEquivQuotSMul`.
  have hTensor :
      Function.Injective ((u.restrictScalars R).lTensor (R ⧸ maximalIdeal R)) := by
    exact hbar
  -- The quotient/tensor comparison square transports this injectivity to the reduction map.
  exact injective_of_ladder_linearEquiv_anyUniverse
    (quotientMapByIdeal_lTensor_naturality_anyUniverse (J := maximalIdeal R)
      (φ := u.restrictScalars R)) hTensor

/-- Helper for Chap10 Lemma 10 128 4: the quotient-form conclusion follows directly from the
Noetherian local criterion when the source and target modules live in one universe. -/
private theorem noetherian_injective_and_flat_quotient_of_mod_maximalIdeal_injective
    {P Q : Type w}
    [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
    [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [Module.FinitePresentation S P] [Module.FinitePresentation S Q] [Module.Flat R Q]
    (u : P →ₗ[S] Q)
    (hmod : Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective u ∧ Module.Flat R (Q ⧸ LinearMap.range u) := by
  -- The Noetherian owner criterion is stated for an `R`-linear map into the flat target.
  -- Restrict scalars on `u`, apply both parts of Lemma `10.99.1`, and then rewrite the range
  -- back to the original `S`-linear range.
  constructor
  · exact injective_of_mod_maximalIdeal_injective
      (R := R) (S := S) (M := Q) (N := P) (u.restrictScalars R) hmod
  · simpa [LinearMap.range_restrictScalars] using
      (flat_quotient_of_mod_maximalIdeal_injective
        (R := R) (S := S) (M := Q) (N := P) (u.restrictScalars R) hmod)

/-- Helper for Chap10 Lemma 10 128 4: the Noetherian local criterion can also be consumed from
the residue-field tensor formulation of the closed-fiber injectivity hypothesis. -/
private theorem noetherian_injective_and_flat_quotient_of_lTensor_residueField_injective
    {P Q : Type w}
    [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
    [AddCommGroup Q] [Module S Q] [Module R Q] [IsScalarTower R S Q]
    [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [Module.FinitePresentation S P] [Module.FinitePresentation S Q] [Module.Flat R Q]
    (u : P →ₗ[S] Q)
    (hbar : Function.Injective ((u.restrictScalars R).lTensor (ResidueField R))) :
    Function.Injective u ∧ Module.Flat R (Q ⧸ LinearMap.range u) := by
  -- First convert the residue-field tensor hypothesis to the quotient-map hypothesis used by
  -- the Noetherian owner criterion.
  have hmod : Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R)) :=
    injective_mod_maximalIdeal_of_lTensor_residueField_injective (R := R) (S := S) u hbar
  -- The already-proved quotient-form helper then gives both injectivity and flatness.
  exact noetherian_injective_and_flat_quotient_of_mod_maximalIdeal_injective
    (R := R) (S := S) (u := u) hmod

/-- Helper for Chap10 Lemma 10 128 4: an essentially finitely presented local map and a
finitely presented target module admit the directed local finite-presentation approximation used
for the finite-stage descent route. -/
private theorem nonemptyModuleApproximation_of_essFinitePresentation
    {P : Type y} [AddCommGroup P] [Module S P] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.FinitePresentation S P]
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) :
    Nonempty
      (DirectedLocalEssFinitePresentationModuleApproximation.{u, v, y, v, max u v}
        (algebraMap R S) P) := by
  -- This packages the first source step: approximate the local homomorphism together with one
  -- finitely presented module over the target ring.
  exact exists_localEssFinitePresentationModuleApproximation
    (f := algebraMap R S) (M := P) hess

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 128 4: flatness is unchanged when the `R`-module structure is
spelled as restriction along the algebra map. -/
private theorem flat_compHom_of_flat
    {P : Type y} [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
    [Module.Flat R P] :
    let _ : Module R P := Module.compHom P (algebraMap R S)
    Module.Flat R P := by
  -- This adapter fixes the scalar-instance spelling expected by the finite-stage flatness API.
  have hmodule :
      Module.compHom P (algebraMap R S) = (inferInstance : Module R P) := by
    ext r p
    exact IsScalarTower.algebraMap_smul S r p
  rw [hmodule]
  infer_instance

/-- Helper for Chap10 Lemma 10 128 4: the final base-change equivalence for the target
approximation can be read over the literal target direct-limit ring. -/
private theorem targetFinalBaseChangeOverTargetColimit
    (AN : DirectedLocalEssFinitePresentationModuleApproximation
        (algebraMap R S) N)
    (i : AN.Λ) :
    let D := Ring.DirectLimit AN.SStage (fun i j h ↦ AN.targetMap i j h)
    let _ : Algebra (AN.SStage i) D :=
      (Ring.DirectLimit.of AN.SStage (fun i j h ↦ AN.targetMap i j h) i).toAlgebra
    let _ : Module D N := Module.compHom N AN.targetColimit.toRingHom
    Nonempty (D ⊗[AN.SStage i] AN.moduleStage i ≃ₗ[D] N) := by
  -- Transport the target's known `S`-linear final base-change equivalence back across the
  -- target-colimit ring equivalence, keeping later map descent in the direct-limit spelling.
  let D := Ring.DirectLimit AN.SStage (fun i j h ↦ AN.targetMap i j h)
  letI : Algebra (AN.SStage i) D :=
    (Ring.DirectLimit.of AN.SStage (fun i j h ↦ AN.targetMap i j h) i).toAlgebra
  letI : Algebra (AN.SStage i) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom
      AN.toDirectedLocalHomApproximation i).toAlgebra
  letI : Algebra D S := AN.targetColimit.toRingHom.toAlgebra
  letI : Module D N := Module.compHom N AN.targetColimit.toRingHom
  letI : Module D (S ⊗[AN.SStage i] AN.moduleStage i) :=
    Module.compHom (S ⊗[AN.SStage i] AN.moduleStage i) (algebraMap D S)
  letI : IsScalarTower (AN.SStage i) D S := by
    -- The stage-to-limit map is the canonical stage map into the direct limit followed by the
    -- target-colimit equivalence.
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    simp [RingHom.algebraMap_toAlgebra,
      DirectedLocalHomApproximation.targetStageToLimitHom]
  letI : IsScalarTower D S N := IsScalarTower.of_compHom (A := S) D N
  letI : IsScalarTower D S (S ⊗[AN.SStage i] AN.moduleStage i) :=
    IsScalarTower.of_compHom (A := S) D (S ⊗[AN.SStage i] AN.moduleStage i)
  have hCompatible :
      LinearMap.CompatibleSMul (S ⊗[AN.SStage i] AN.moduleStage i) N D S :=
    { map_smul := fun f d z ↦ by
        change f ((algebraMap D S d) • z) = (algebraMap D S d) • f z
        exact map_smul f (algebraMap D S d) z }
  let eDS : D ≃ₐ[D] S :=
    { toRingEquiv := AN.targetColimit
      commutes' := by
        intro x
        simp [RingHom.algebraMap_toAlgebra] }
  let eTensor :
      D ⊗[AN.SStage i] AN.moduleStage i ≃ₗ[D]
        S ⊗[AN.SStage i] AN.moduleStage i :=
    TensorProduct.AlgebraTensorModule.congr eDS.toLinearEquiv
      (LinearEquiv.refl (AN.SStage i) (AN.moduleStage i))
  let eFinal :
      S ⊗[AN.SStage i] AN.moduleStage i ≃ₗ[D] N :=
    @LinearEquiv.restrictScalars D S
      (S ⊗[AN.SStage i] AN.moduleStage i) N
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      hCompatible (AN.finalBaseChange i)
  exact ⟨eTensor.trans eFinal⟩

/-- Helper for Chap10 Lemma 10 128 4: a target-owned finite stage records a descended source
module, a descended map into the target approximation, and the final base-change square
identifying that descended map with the original map. -/
private structure TargetStageMapData
    (AN : DirectedLocalEssFinitePresentationModuleApproximation
        (algebraMap R S) N)
    (u : M →ₗ[S] N) where
  i : AN.Λ
  MStage : Type v
  instAddCommGroupMStage : AddCommGroup MStage
  instModuleMStage : Module (AN.SStage i) MStage
  instFinitePresentationMStage : Module.FinitePresentation (AN.SStage i) MStage
  uStage : MStage →ₗ[AN.SStage i] AN.moduleStage i
  finalBaseChangeSource :
    let _ : Algebra (AN.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        AN.toDirectedLocalHomApproximation i).toAlgebra
    S ⊗[AN.SStage i] MStage ≃ₗ[S] M
  finalBaseChange_comm :
    let _ : Algebra (AN.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        AN.toDirectedLocalHomApproximation i).toAlgebra
    ∀ x : S ⊗[AN.SStage i] MStage,
      AN.finalBaseChange i ((uStage.lTensor S) x) =
        u (finalBaseChangeSource x)

/-- Helper for Chap10 Lemma 10 128 4: the finite-stage descent construction before imposing the
final base-change square. -/
private structure TargetStageMapPredata
    (AN : DirectedLocalEssFinitePresentationModuleApproximation
        (algebraMap R S) N)
    (u : M →ₗ[S] N) where
  i : AN.Λ
  MStage : Type v
  instAddCommGroupMStage : AddCommGroup MStage
  instModuleMStage : Module (AN.SStage i) MStage
  instFinitePresentationMStage : Module.FinitePresentation (AN.SStage i) MStage
  uStage : MStage →ₗ[AN.SStage i] AN.moduleStage i
  finalBaseChangeSource :
    let _ : Algebra (AN.SStage i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        AN.toDirectedLocalHomApproximation i).toAlgebra
    S ⊗[AN.SStage i] MStage ≃ₗ[S] M

/-- Helper for Chap10 Lemma 10 128 4: a square-carrying finite stage is predata together with
the final base-change square identifying the descended map with the original map. -/
private structure TargetStageMapSquareData
    (AN : DirectedLocalEssFinitePresentationModuleApproximation
        (algebraMap R S) N)
    (u : M →ₗ[S] N) where
  predata : TargetStageMapPredata AN u
  finalBaseChange_comm :
    let _ : AddCommGroup predata.MStage := predata.instAddCommGroupMStage
    let _ : Module (AN.SStage predata.i) predata.MStage := predata.instModuleMStage
    let _ : Algebra (AN.SStage predata.i) S :=
      (DirectedLocalHomApproximation.targetStageToLimitHom
        AN.toDirectedLocalHomApproximation predata.i).toAlgebra
    ∀ x : S ⊗[AN.SStage predata.i] predata.MStage,
      AN.finalBaseChange predata.i ((predata.uStage.lTensor S) x) =
        u (predata.finalBaseChangeSource x)

/-- Helper for Chap10 Lemma 10 128 4: a finitely presented source map into a fixed target
approximation descends to finite target-stage predata after passing to the target direct limit. -/
private theorem existsTargetStageMapPredata
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M]
    (AN : DirectedLocalEssFinitePresentationModuleApproximation
        (algebraMap R S) N)
    (u : M →ₗ[S] N) :
    Nonempty (TargetStageMapPredata AN u) := by
  -- First descend the finitely presented source module over the target-system direct limit.
  let A := AN.toDirectedLocalHomApproximation
  let D := Ring.DirectLimit AN.SStage (fun i j h ↦ AN.targetMap i j h)
  letI : Algebra D S := AN.targetColimit.toRingHom.toAlgebra
  letI : Module D M := Module.compHom M AN.targetColimit.toRingHom
  letI : Module D N := Module.compHom N AN.targetColimit.toRingHom
  obtain ⟨i, MStage, instAdd, instModule, instFinitePresentation, ⟨eM⟩⟩ :=
    descend_module_to_target_stage
      (f := algebraMap R S) (A := A) (M := M)
  letI : AddCommGroup MStage := instAdd
  letI : Module (AN.SStage i) MStage := instModule
  letI : Module.FinitePresentation (AN.SStage i) MStage := instFinitePresentation
  -- The target approximation itself supplies the matching target direct-limit equivalence.
  obtain ⟨eN⟩ := targetFinalBaseChangeOverTargetColimit (R := R) (S := S) AN i
  have hCompatible : LinearMap.CompatibleSMul M N D S :=
    { map_smul := fun f d m ↦ by
        change f ((algebraMap D S d) • m) = (algebraMap D S d) • f m
        exact map_smul f (algebraMap D S d) m }
  let uD : M →ₗ[D] N :=
    @LinearMap.restrictScalars D S M N
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      hCompatible u
  let φ : D ⊗[AN.SStage i] MStage →ₗ[D]
      D ⊗[AN.SStage i] AN.moduleStage i :=
    eN.symm.toLinearMap.comp (uD.comp eM.toLinearMap)
  -- The owner descent theorem now produces a later-stage map whose base change is `φ`.
  obtain ⟨j, hij, φj, hφj⟩ :=
    finitelyPresented_baseChange_map_descends
      (R := AN.SStage) (f := fun i j h ↦ AN.targetMap i j h)
      (i := i) (M_i := MStage) (N_i := AN.moduleStage i) φ
  -- Package the descended map at the later target stage, with the source obtained by scalar
  -- extension from the descended source module at stage `i`.
  obtain ⟨eMS⟩ :=
    targetColimit_transport_descended_module_equiv
      (f := algebraMap R S) (M := M) A i eM
  letI : Algebra (AN.SStage i) (AN.SStage j) := (AN.targetMap i j hij).toAlgebra
  letI : Module (AN.SStage i) (AN.SStage j) := inferInstance
  letI : Algebra (AN.SStage i) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom A i).toAlgebra
  letI : Algebra (AN.SStage j) S :=
    (DirectedLocalHomApproximation.targetStageToLimitHom A j).toAlgebra
  letI : IsScalarTower (AN.SStage i) (AN.SStage j) S :=
    target_stage_limit_isScalarTower (f := algebraMap R S) A i ⟨j, hij⟩
  let finalSource :
      S ⊗[AN.SStage j] (AN.SStage j ⊗[AN.SStage i] MStage) ≃ₗ[S] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (AN.SStage i) (AN.SStage j) S S MStage).trans eMS
  let uStage :
      AN.SStage j ⊗[AN.SStage i] MStage →ₗ[AN.SStage j] AN.moduleStage j :=
    (AN.transitionBaseChange hij).toLinearMap.comp φj
  -- The construction prefix is now packaged separately; the later commuting-square helper will
  -- add the final compatibility with the original map `u`.
  exact ⟨
    { i := j
      MStage := AN.SStage j ⊗[AN.SStage i] MStage
      instAddCommGroupMStage := inferInstance
      instModuleMStage := inferInstance
      instFinitePresentationMStage := inferInstance
      uStage := uStage
      finalBaseChangeSource := finalSource }⟩

/-- Helper for Chap10 Lemma 10 128 4: a finitely presented source map into a fixed target
approximation descends together with the direct-limit square that proves its final base-change
compatibility. -/
private theorem existsTargetStageMapSquareData
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M]
    (AN : DirectedLocalEssFinitePresentationModuleApproximation
        (algebraMap R S) N)
    (u : M →ₗ[S] N) :
    Nonempty (TargetStageMapSquareData AN u) := by
  -- The predata construction already descends the source module and map. The remaining planned
  -- step is to keep the direct-limit equivalences and the descended map square from
  -- `finitelyPresented_baseChange_map_descends`, then use them to fill the inherited
  -- `finalBaseChange_comm` field.
  -- TODO: refactor `existsTargetStageMapPredata` so it returns the retained direct-limit source
  -- equivalence, target equivalence, descended stage map, and descent equality; then prove the
  -- inherited final-base-change square by rewriting both sides to that stored equality.
  sorry

/-- Helper for Chap10 Lemma 10 128 4: a finitely presented source map into a fixed target
approximation descends to a finite target stage after passing to the target direct limit. -/
private theorem existsTargetStageMapData
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M]
    (AN : DirectedLocalEssFinitePresentationModuleApproximation
        (algebraMap R S) N)
    (u : M →ₗ[S] N) :
    Nonempty (TargetStageMapData AN u) := by
  -- Project the public finite-stage data from the stronger square package, so the transport-heavy
  -- commuting-square proof is owned in one place instead of being reconstructed here.
  obtain ⟨sq⟩ := existsTargetStageMapSquareData (R := R) (S := S) (M := M) (N := N) AN u
  exact ⟨
    { i := sq.predata.i
      MStage := sq.predata.MStage
      instAddCommGroupMStage := sq.predata.instAddCommGroupMStage
      instModuleMStage := sq.predata.instModuleMStage
      instFinitePresentationMStage := sq.predata.instFinitePresentationMStage
      uStage := sq.predata.uStage
      finalBaseChangeSource := sq.predata.finalBaseChangeSource
      finalBaseChange_comm := sq.finalBaseChange_comm }⟩

-- Proof sketch: apply the owner theorems from Lemma `10.99.1` directly to the closed-fiber map
-- modulo `maximalIdeal R`; the quotient by the `R`-linear range of `u.restrictScalars R` is
-- definitionally the same module as the quotient by the `S`-linear range of `u`, viewed by
-- restriction of scalars.
/-- Lemma 10.128.4: for a local homomorphism `R → S` with `S` essentially of finite presentation
over `R`, if `M` and `N` are finitely presented `S`-modules, `N` is flat over `R`, and the
induced map `M / maximalIdeal R • M → N / maximalIdeal R • N` is injective, then `u` is injective
and its quotient is flat over `R`. -/
@[stacks 046Y]
theorem injective_and_flat_quotient_of_mod_maximalIdeal_injective
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (u : M →ₗ[S] N)
    (hmod : Function.Injective ((u.restrictScalars R).quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range u) := by
  -- Route correction: the earlier owner route through Lemma `10.99.1` requires
  -- `[IsNoetherianRing S]` and a same-universe source/target pair, while this theorem has neither
  -- requirement in its public API. A replacement proof needs the actual Lemma `10.128.4` argument
  -- under the essentially-finite-presentation and finite-presentation hypotheses.
  -- The corrected finite-stage route fixes the target approximation as the owner system, then
  -- descends the source module and the map into that same system.
  obtain ⟨AN⟩ := nonemptyModuleApproximation_of_essFinitePresentation (P := N) hess
  -- The source module and the map have now been descended into the fixed target approximation;
  -- the remaining work is to combine this datum with a flat target stage and descend the
  -- closed-fiber injectivity hypothesis to a common finite stage.
  obtain ⟨Dmap⟩ := existsTargetStageMapData (R := R) (S := S) (M := M) (N := N) AN u
  -- TODO: prove the finite-stage owner API: existence of a flat target stage, transition `Dmap`
  -- to a common upper bound, transport `hmod` to a sufficiently late closed-fiber quotient map,
  -- apply the Noetherian helper at that stage, and transport injectivity and quotient flatness
  -- back through the final base-change equivalences.
  sorry

-- Proof sketch: bridge the residue-field injectivity hypothesis to injectivity of the closed-fiber
-- quotient map, then apply Lemma `10.128.4` in its source-facing quotient form.
/-- Companion reformulation of Lemma 10.128.4: the residue-field tensor criterion implies the
source-facing closed-fiber injectivity hypothesis, hence the same injectivity and flat-quotient
conclusion. -/
theorem injective_and_flat_quotient_of_lTensor_residueField_injective
    [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N] [Module.Flat R N]
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (u : M →ₗ[S] N)
    (hbar : Function.Injective ((u.restrictScalars R).lTensor (ResidueField R))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range u) := by
  exact
    injective_and_flat_quotient_of_mod_maximalIdeal_injective hess u
      (injective_mod_maximalIdeal_of_lTensor_residueField_injective u hbar)

end
