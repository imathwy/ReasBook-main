import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Adjunction.Limits
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_71_1
import StacksProject_2024.stacks_project.Chap10.Remark_10_75_9
import StacksProject_2024.stacks_project.Chap12.Lemma_12_31_4
import StacksProject_2024.stacks_project.Chap12.Lemma_12_31_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_27_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory
open OrderDual
open ModuleCat.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- Domain triage:
* `source-facing`: Lemma `15.27.4` studies a sequential inverse system of `A`-modules over `ℕ+`
  and the canonical comparison map from tensoring after inverse limit to the inverse limit of the
  tensorized system.
* `core/canonical` owners: the inverse system itself as a functor `OrderDual ℕ+ ⥤ ModuleCat A`,
  its transition maps coming from `Functor.map`, the canonical comparison morphism
  `CategoryTheory.Limits.limit.post`, and the flatness owner `Module.Flat`.
* `bridge/view`: bijectivity of the comparison morphism for finite modules, then flatness of the
  inverse limit deduced from that bijectivity criterion.

Relevant owner declarations sampled for this refinement:
* `CategoryTheory.SequentialInverseSystem.stepMap`
* `CategoryTheory.Functor.map`
* `CategoryTheory.Limits.limit.post`
* `CategoryTheory.Limits.limit.post_π`
* `Module.Flat.iff_preservesFiniteLimits_tensorLeft`

Primitive data are only the inverse system `M_`, the stagewise quotient-flat hypotheses, and the
surjectivity of the successive transition maps. The tensor-limit comparison itself is canonical
derived API, so the public statement uses `limit.post` directly rather than a local wrapper.
Because the system is indexed by `OrderDual ℕ+` rather than the chapter owner `ℕᵒᵖ`, the
successor map is kept only as a private `stepMap` helper mirroring the canonical owner vocabulary. -/

private theorem pnat_le_succ (n : ℕ+) : n ≤ n + 1 := by
  exact_mod_cast Nat.le_succ (n : ℕ)

/-- The successor map `M_{n + 1} → M_n` in a positive-index inverse system of `A`-modules. -/
private abbrev stepMap (M_ : OrderDual ℕ+ ⥤ ModuleCat A) (n : ℕ+) :
    M_.obj (toDual (n + 1)) ⟶ M_.obj (toDual n) :=
  M_.map (homOfLE (pnat_le_succ n))

variable (I : Ideal A) (M_ : OrderDual ℕ+ ⥤ ModuleCat A)
variable [∀ n : ℕ+, Module (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n))]
variable [∀ n : ℕ+, IsScalarTower A (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n))]

/-- Helper for Lemma 15.27.4: tensoring with the monoidal unit is naturally the identity
endofunctor on `ModuleCat A`. -/
private noncomputable def tensor_unit_iso :
    tensorLeft (𝟙_ (ModuleCat A)) ≅ 𝟭 (ModuleCat A) :=
  NatIso.ofComponents
    (fun X ↦ λ_ X)
    (fun {X Y} f ↦ by
      -- Proof comment: this is exactly the naturality of the left unitor.
      simpa using (λ_ Y).hom.naturality f)

/-- Helper for Lemma 15.27.4: the canonical comparison map is bijective for the free rank-one
module because tensoring with the monoidal unit preserves all limits. -/
private theorem tensor_unit_limit_post_bijective :
    Function.Bijective (limit.post M_ (tensorLeft (𝟙_ (ModuleCat A)))) := by
  -- Proof comment: transport the identity functor's limit preservation across the unit isomorphism.
  let e := tensor_unit_iso (A := A)
  letI : PreservesLimits (𝟭 (ModuleCat A)) := by
    infer_instance
  letI : PreservesLimit M_ (tensorLeft (𝟙_ (ModuleCat A))) :=
    preservesLimit_of_natIso M_ e.symm
  let epost : (tensorLeft (𝟙_ (ModuleCat A))).obj (limit M_) ≅
      limit (M_ ⋙ tensorLeft (𝟙_ (ModuleCat A))) :=
    asIso (limit.post M_ (tensorLeft (𝟙_ (ModuleCat A))))
  refine ⟨?_, ?_⟩
  · intro x x' hxx'
    change epost.hom x = epost.hom x' at hxx'
    calc
      x = epost.inv (epost.hom x) := by
        simpa using (epost.hom_inv_id_apply x).symm
      _ = epost.inv (epost.hom x') := by
        simpa using congrArg epost.inv hxx'
      _ = x' := by
        simpa using epost.hom_inv_id_apply x'
  intro y
  refine ⟨epost.inv y, ?_⟩
  change epost.hom (epost.inv y) = y
  simpa using epost.inv_hom_id_apply y

/-- Helper for Lemma 15.27.4: tensoring with the finite free module `A^r` is canonically the
`Fin r`-indexed product functor on `ModuleCat A`. -/
private noncomputable def tensor_free_iso (r : ℕ) (X : ModuleCat A) :
    (tensorLeft (ModuleCat.of A (Fin r → A))).obj X ≅ ModuleCat.of A (Fin r → X) :=
  ((TensorProduct.comm A (Fin r → A) X).trans (TensorProduct.piScalarRight A A X (Fin r))).toModuleIso

/-- Helper for Lemma 15.27.4: tensoring a linear map on the right acts on pure tensors by
applying the map to the second factor. -/
private theorem tensorLeft_map_apply_tmul {M N P : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (φ : N →ₗ[A] P) (x : M) (y : N) :
    (((tensorLeft (ModuleCat.of A M)).map (ModuleCat.ofHom φ)).hom) (x ⊗ₜ[A] y) =
      x ⊗ₜ[A] φ y :=
  rfl

/-- Helper for Lemma 15.27.4: after identifying `A^r ⊗ X` and `A^r ⊗ Y` with finite products,
the tensor map induced by `f : X ⟶ Y` is coordinatewise postcomposition by `f`. -/
private theorem tensor_free_iso_naturality_proj
    (r : ℕ) {X Y : ModuleCat A} (f : X ⟶ Y) (i : Fin r) :
    (tensorLeft (ModuleCat.of A (Fin r → A))).map f ≫
        (tensor_free_iso (A := A) r Y).hom ≫
        ModuleCat.ofHom (LinearMap.proj i) =
      (tensor_free_iso (A := A) r X).hom ≫
        ModuleCat.ofHom (LinearMap.proj i) ≫ f := by
  -- Proof comment: both composites send a pure tensor `a ⊗ x` to `a i • f x`, so extensionality
  -- on the tensor product closes the comparison.
  apply ModuleCat.hom_ext
  ext a x
  simp [tensor_free_iso, tensorLeft_map_apply_tmul]

/-- Helper for Lemma 15.27.4: inverse limits commute with tensoring by the finite free module
`A^r`. This is the free-module comparison used in the source finite free resolution argument. -/
private theorem finite_free_limit_post_bijective (r : ℕ) :
    Function.Bijective (limit.post M_ (tensorLeft (ModuleCat.of A (Fin r → A)))) := by
  let F := tensorLeft (ModuleCat.of A (Fin r → A))
  let e0 := tensor_free_iso (A := A) r (limit M_)
  let c : Fin r → Cone M_ := fun i ↦
    { pt := limit (M_ ⋙ F)
      π :=
        { app := fun n ↦
            limit.π (M_ ⋙ F) n ≫
              (tensor_free_iso (A := A) r (M_.obj n)).hom ≫
                ModuleCat.ofHom (LinearMap.proj i)
          naturality := by
            intro n n' f
            -- Proof comment: the coordinate projections of the stagewise product model are
            -- compatible because `limit.π` is natural and `tensor_free_iso` is natural in the
            -- module variable.
            simp only [Category.assoc]
            rw [limit.w (M_ ⋙ F) f]
            simpa using
              tensor_free_iso_naturality_proj
                (A := A) (r := r) (f := M_.map f) i } }
  let η : Fin r → limit (M_ ⋙ F) ⟶ limit M_ := fun i ↦ limit.lift M_ (c i)
  let gToPi : limit (M_ ⋙ F) ⟶ ModuleCat.of A (Fin r → limit M_) :=
    ModuleCat.ofHom
      { toFun := fun x i ↦ (η i).hom x
        map_add' := by
          intro x y
          ext i
          simp
        map_smul' := by
          intro a x
          ext i
          simp }
  let g : limit (M_ ⋙ F) ⟶ F.obj (limit M_) := gToPi ≫ e0.inv
  refine ⟨?_, ?_⟩
  · intro x x' hxx'
    have hproj :
        g ≫ e0.hom = gToPi := by
      simp [g, gToPi, e0]
    have hpi :
        limit.post M_ F ≫ gToPi = e0.hom := by
      -- Proof comment: check the comparison after projecting to each factor of `Fin r → limit M_`.
      apply ModuleCat.hom_ext
      ext x i
      apply (limit.hom_ext _ _)
      intro n
      simp only [Category.assoc, hproj]
      rw [limit.lift_π, limit.post_π]
      simpa using
        tensor_free_iso_naturality_proj
          (A := A) (r := r) (f := limit.π M_ n) i
    have hleft : limit.post M_ F ≫ g = 𝟙 _ := by
      apply (cancel_mono e0.hom).1
      simpa [g] using hpi
    have := congrArg (fun f ↦ f x) hleft
    simpa using congrArg (fun f ↦ f.hom) hleft |> fun h => LinearMap.congr_fun h x
  · intro y
    refine ⟨g y, ?_⟩
    apply limit.hom_ext
    intro n
    -- Proof comment: after transporting stage `n` to the `Fin r`-product model, each coordinate
    -- is exactly the `n`th component of the compatible family `y`.
    apply ModuleCat.hom_ext
    ext x i
    simp only [Category.assoc, g]
    rw [limit.post_π, limit.lift_π]
    simpa using
      tensor_free_iso_naturality_proj
        (A := A) (r := r) (f := limit.π M_ n) i

/-- Helper for Lemma 15.27.4: the chosen chain resolution is viewed as the source-faithful
cochain complex supported in nonpositive degrees. -/
private abbrev chosen_resolution_cochain_view
    {Q : Type u} [AddCommGroup Q] [Module A Q]
    {F : ChainComplex (ModuleCat A) ℕ}
    (π : F ⟶ moduleSingle[A] Q) :
    CochainComplex (ModuleCat A) ℤ :=
  F.extend ComplexShape.embeddingDownNat

/-- Helper for Lemma 15.27.4: each degree of the cochain view of a chosen finite free resolution
is projective. This records the bounded-above projective surface before tensoring stagewise with
the inverse system. -/
private theorem chosen_resolution_view_term_projective
    {Q : Type u} [AddCommGroup Q] [Module A Q]
    {F : ChainComplex (ModuleCat A) ℕ}
    (π : F ⟶ moduleSingle[A] Q)
    [ChainComplex.IsFiniteFreeResolution π]
    (n : ℤ) :
    Projective ((chosen_resolution_cochain_view (A := A) π).X n) := by
  by_cases hnonpos : n ≤ 0
  · let e :
        (chosen_resolution_cochain_view (A := A) π).X n ≅ F.X (Int.toNat (-n)) :=
      F.extendXIso ComplexShape.embeddingDownNat (by
        have hneg : 0 ≤ -n := by linarith
        simpa [chosen_resolution_cochain_view, ComplexShape.embeddingDownNat,
          Int.toNat_of_nonneg hneg] using
          (show -((Int.toNat (-n) : ℕ) : ℤ) = n by
            rw [Int.toNat_of_nonneg hneg]
            omega))
    -- Proof comment: nonpositive cochain degrees come directly from the free chain terms.
    letI : Module.Free A (F.X (Int.toNat (-n))) :=
      ChainComplex.IsFiniteFreeResolution.free (R := A) (π := π) (Int.toNat (-n))
    exact Projective.of_iso e inferInstance
  · have hpos : 0 < n := by omega
    let hzero :
        CategoryTheory.Limits.IsZero ((chosen_resolution_cochain_view (A := A) π).X n) :=
      F.isZero_extend_X ComplexShape.embeddingDownNat n fun j hj ↦ by
        have hnonpos' : (ComplexShape.embeddingDownNat.f j : ℤ) ≤ 0 := by
          simp [ComplexShape.embeddingDownNat]
        rw [hj] at hnonpos'
        omega
    -- Proof comment: positive cochain degrees vanish after reindexing, so they are projective.
    exact Projective.of_iso hzero.isoZero (by infer_instance)

/-- Helper for Lemma 15.27.4: in the degree-zero single chain complex, the incoming differential
vanishes after identifying the zeroth term with the underlying module. -/
private theorem single0_objXSelf_comp_d_eq_zero
    {Q : Type u} [AddCommGroup Q] [Module A Q]
    (M : ModuleCat A) :
    ((ChainComplex.single₀ (ModuleCat A)).obj M).d 1 0 ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom = 0 := by
  -- Proof comment: the single complex has no nonzero term in degree `1`, so the first
  -- differential is zero.
  rw [HomologicalComplex.single_obj_d]
  simp [ChainComplex.single₀ObjXSelf]
  rfl

/-- Helper for Lemma 15.27.4: on a degree-zero single chain complex, the canonical map from
zeroth opcycles to the underlying module is the descended degree-zero term map. -/
private theorem single0_opcycles_self_inv_eq_descOpcycles
    {Q : Type u} [AddCommGroup Q] [Module A Q]
    (M : ModuleCat A) :
    (HomologicalComplex.singleObjOpcyclesSelfIso
      (ComplexShape.down ℕ) (0 : ℕ) M).inv =
    ((ChainComplex.single₀ (ModuleCat A)).obj M).descOpcycles
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom
      1 (by simp) (single0_objXSelf_comp_d_eq_zero (A := A) M) := by
  -- Proof comment: both maps out of zeroth opcycles are characterized by the same composite with
  -- `pOpcycles`.
  apply (cancel_epi (((ChainComplex.single₀ (ModuleCat A)).obj M).pOpcycles 0)).1
  calc
    ((ChainComplex.single₀ (ModuleCat A)).obj M).pOpcycles 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.down ℕ) (0 : ℕ) M).inv =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
          simpa [ChainComplex.single₀ObjXSelf] using
            (HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv
              (c := ComplexShape.down ℕ) (j := (0 : ℕ)) (A := M))
    _ =
      ((ChainComplex.single₀ (ModuleCat A)).obj M).pOpcycles 0 ≫
        ((ChainComplex.single₀ (ModuleCat A)).obj M).descOpcycles
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) M).hom
          1 (by simp) (single0_objXSelf_comp_d_eq_zero (A := A) M) := by
            symm
            simpa using
              (HomologicalComplex.p_descOpcycles
                (K := (ChainComplex.single₀ (ModuleCat A)).obj M)
                (i := (0 : ℕ))
                (k := (HomologicalComplex.singleObjXSelf
                  (ComplexShape.down ℕ) (0 : ℕ) M).hom)
                (j := 1)
                (hj := by simp)
                (hk := single0_objXSelf_comp_d_eq_zero (A := A) M))

/-- Helper for Lemma 15.27.4: the augmentation of a chosen finite free resolution is surjective
and exact at degree `0`. -/
private theorem chosen_resolution_augmentation_exact
    {Q : Type u} [AddCommGroup Q] [Module A Q]
    {F : ChainComplex (ModuleCat A) ℕ}
    (π : F ⟶ moduleSingle[A] Q)
    [ChainComplex.IsFiniteFreeResolution π] :
    Function.Surjective (π.f 0).hom ∧ Function.Exact (F.d 1 0).hom (π.f 0).hom := by
  let singleX :
      ((moduleSingle[A] Q).X 0 ≅ ModuleCat.of A Q) :=
    HomologicalComplex.singleObjXSelf
      (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of A Q)
  have hcomp_zero :
      F.d 1 0 ≫ (π.f 0 ≫ singleX.hom) = 0 := by
    -- Proof comment: the chain-map square at degrees `1` and `0` lands in the zero differential
    -- of the degree-zero single complex.
    simpa [Category.assoc, single0_objXSelf_comp_d_eq_zero (A := A) (ModuleCat.of A Q)] using
      congrArg (fun f ↦ f ≫ singleX.hom) (π.comm 1 0)
  let desc :
      F.opcycles 0 ⟶ ModuleCat.of A Q :=
    F.descOpcycles (π.f 0 ≫ singleX.hom) 1 (by simp) hcomp_zero
  have hdesc_eq :
      desc =
        (ChainComplex.isoHomologyι₀ F).inv ≫
          HomologicalComplex.homologyMap π 0 ≫
            ((ChainComplex.isoHomologyι₀ (moduleSingle[A] Q)) ≪≫
              HomologicalComplex.singleObjOpcyclesSelfIso
                (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of A Q)).hom := by
    -- Route correction: rewrite the descended map through the quasi-isomorphism on `H₀`, then
    -- finish with the canonical `H₀(single₀ Q) ≅ Q` comparison.
    apply (cancel_epi (F.homologyι 0)).1
    calc
      F.homologyι 0 ≫ desc =
        F.homologyι 0 ≫
          HomologicalComplex.opcyclesMap π 0 ≫
            (HomologicalComplex.singleObjOpcyclesSelfIso
              (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of A Q)).inv := by
              rw [single0_opcycles_self_inv_eq_descOpcycles (A := A) (ModuleCat.of A Q)]
              simpa [desc, Category.assoc] using
                (HomologicalComplex.opcyclesMap_comp_descOpcycles
                  (K := F)
                  (L := moduleSingle[A] Q)
                  (φ := π)
                  (i := (0 : ℕ))
                  (k := singleX.hom)
                  (j := 1)
                  (hj := by simp)
                  (hk := single0_objXSelf_comp_d_eq_zero (A := A) (ModuleCat.of A Q)))
      _ =
        F.homologyι 0 ≫
          (ChainComplex.isoHomologyι₀ F).inv ≫
            HomologicalComplex.homologyMap π 0 ≫
              (ChainComplex.isoHomologyι₀ (moduleSingle[A] Q)).hom ≫
                (HomologicalComplex.singleObjOpcyclesSelfIso
                  (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of A Q)).inv := by
                    rw [← Category.assoc]
                    simp [ChainComplex.isoHomologyι₀_inv_naturality, Category.assoc]
      _ =
        F.homologyι 0 ≫
          ((ChainComplex.isoHomologyι₀ F).inv ≫
            HomologicalComplex.homologyMap π 0 ≫
              ((ChainComplex.isoHomologyι₀ (moduleSingle[A] Q)) ≪≫
                HomologicalComplex.singleObjOpcyclesSelfIso
                  (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of A Q)).hom) := by
                    simp [Category.assoc]
  have hdescIso : IsIso desc := by
    rw [hdesc_eq]
    infer_instance
  have hdesc_exact_epi :
      Function.Exact (F.d 1 0).hom ((π.f 0 ≫ singleX.hom).hom) ∧ Epi (π.f 0 ≫ singleX.hom) := by
    rw [ChainComplex.isIso_descOpcycles_iff] at hdescIso
    exact hdescIso
  constructor
  · -- Proof comment: surjectivity is unchanged after composing with the degree-zero identification.
    have hsurjComp : Function.Surjective ((π.f 0 ≫ singleX.hom).hom) :=
      (ModuleCat.epi_iff_surjective _).1 hdesc_exact_epi.2
    intro m
    rcases hsurjComp (singleX.hom.hom m) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply singleX.hom.hom.injective
    simpa [Category.assoc] using hx
  · -- Proof comment: exactness descends back across the degree-zero identification isomorphism.
    intro x hx
    have hxComp : ((π.f 0 ≫ singleX.hom).hom) x = 0 := by
      simpa [Category.assoc] using congrArg singleX.hom.hom hx
    rcases hdesc_exact_epi.1 x hxComp with ⟨y, rfl⟩
    exact ⟨y, rfl⟩

/-- Helper for Lemma 15.27.4: after fixing a chosen finite free resolution of `Q`, tensoring it
with a module `N` gives the exact cochain stage used in the source proof. -/
private abbrev tensorized_chosen_resolution_stage
    {Q : Type u} [AddCommGroup Q] [Module A Q]
    {F : ChainComplex (ModuleCat A) ℕ}
    (π : F ⟶ moduleSingle[A] Q)
    (N : ModuleCat A) :
    CochainComplex (ModuleCat A) ℤ :=
  ((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (chosen_resolution_cochain_view (A := A) π)

/-- Helper for Lemma 15.27.4: unfolding the chosen tensorized stage does not introduce any extra
transport; it is literally the tensor-right image of the fixed cochain view. -/
@[simp] private theorem tensorized_chosen_resolution_stage_def
    {Q : Type u} [AddCommGroup Q] [Module A Q]
    {F : ChainComplex (ModuleCat A) ℕ}
    (π : F ⟶ moduleSingle[A] Q)
    (N : ModuleCat A) :
    tensorized_chosen_resolution_stage (A := A) π N =
      ((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (chosen_resolution_cochain_view (A := A) π) :=
  rfl

/-- Helper for Lemma 15.27.4: in any cochain complex, the degree-`0` opcycles are the cokernel of
the incoming differential `d^{-1}`. -/
private noncomputable def two_term_opcycles_zero_iso_cokernel
    (P : CochainComplex (ModuleCat A) ℤ) :
    P.opcycles 0 ≅ cokernel (P.d (-1) 0) := by
  let hOpcycles :
      IsColimit (CokernelCofork.ofπ (P.pOpcycles 0) (P.d_pOpcycles (-1) 0)) := by
    simpa using P.opcyclesIsCokernel (i := -1) (j := 0) (by simp)
  -- Proof comment: compare the owner-level opcycle cokernel with the categorical cokernel of
  -- `d^{-1}`.
  exact
    (IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (P.d (-1) 0))
      hOpcycles).symm

/-- Helper for Lemma 15.27.4: the tensorized chosen resolution has zero outgoing differential from
degree `0`, because the reindexed source complex is supported in nonpositive degrees. -/
private theorem tensorized_chosen_resolution_stage_d_zero_one_eq_zero
    {Q : Type u} [AddCommGroup Q] [Module A Q]
    {F : ChainComplex (ModuleCat A) ℕ}
    (π : F ⟶ moduleSingle[A] Q)
    (N : ModuleCat A) :
    (tensorized_chosen_resolution_stage (A := A) π N).d 0 1 = 0 := by
  let C := chosen_resolution_cochain_view (A := A) π
  have hzeroC : IsZero (C.X 1) := by
    -- Proof comment: positive cochain degrees vanish after extending the chain complex downward.
    exact F.isZero_extend_X ComplexShape.embeddingDownNat 1 fun j hj ↦ by
      have hnonpos : (ComplexShape.embeddingDownNat.f j : ℤ) ≤ 0 := by
        simp [ComplexShape.embeddingDownNat]
      rw [hj] at hnonpos
      omega
  let hzeroT : IsZero ((tensorized_chosen_resolution_stage (A := A) π N).X 1) :=
    (tensorRight N).map_isZero hzeroC
  -- Proof comment: any morphism landing in the zero object is zero.
  exact hzeroT.eq_of_tgt _ _

/-- Helper for Lemma 15.27.4: the degree-`0` homology of the tensorized chosen resolution is the
cokernel of its incoming differential. -/
private noncomputable def tensorized_chosen_resolution_homology_zero_iso_cokernel
    {Q : Type u} [AddCommGroup Q] [Module A Q]
    {F : ChainComplex (ModuleCat A) ℕ}
    (π : F ⟶ moduleSingle[A] Q)
    (N : ModuleCat A) :
    (tensorized_chosen_resolution_stage (A := A) π N).homology 0 ≅
      cokernel ((tensorized_chosen_resolution_stage (A := A) π N).d (-1) 0) := by
  let P := tensorized_chosen_resolution_stage (A := A) π N
  have hzero_next : P.d 0 1 = 0 :=
    tensorized_chosen_resolution_stage_d_zero_one_eq_zero (A := A) (π := π) N
  let eHomology :
      P.homology 0 ≅ P.opcycles 0 :=
    P.isoHomologyι 0 1 (by simp) hzero_next
  -- Proof comment: first identify `H^0` with opcycles, then rewrite opcycles to the categorical
  -- cokernel of `d^{-1}`.
  exact eHomology ≪≫ two_term_opcycles_zero_iso_cokernel (A := A) P

/-- Helper for Lemma 15.27.4: the degree `-1` homology of the tensorized chosen resolution is
the canonical `Tor₁^A(Q, N)` object. This keeps the source proof on the fixed finite free
resolution and only uses the standard chain-to-cochain reindexing once. -/
private noncomputable def tensorized_chosen_resolution_homology_neg_one_iso_tor_one
    {Q : Type u} [AddCommGroup Q] [Module A Q]
    {F : ChainComplex (ModuleCat A) ℕ}
    (π : F ⟶ moduleSingle[A] Q)
    [ChainComplex.IsFiniteFreeResolution π]
    (N : ModuleCat A) :
    (tensorized_chosen_resolution_stage (A := A) π N).homology (-1) ≅
      (((Tor (ModuleCat A) 1).obj (ModuleCat.of A Q)).obj N) := by
  letI : ChainComplex.IsFreeResolution π := inferInstance
  let P := ChainComplex.IsFreeResolution.toProjectiveResolution (R := A) (M := Q) (π := π)
  let eResolution :
      (((Tor (ModuleCat A) 1).obj (ModuleCat.of A Q)).obj N) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 1).obj
          (((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (P : ChainComplex (ModuleCat A) ℕ)) := by
    -- Proof comment: the chosen finite free resolution computes `Tor₁` directly in chain degree
    -- `1`, without changing to a different projective resolution owner.
    simpa [P] using (P.isoLeftDerivedObj (tensorRight N) 1)
  let eCochain :
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 1).obj
          (((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (P : ChainComplex (ModuleCat A) ℕ)) ≅
        (tensorized_chosen_resolution_stage (A := A) π N).homology (-1) := by
    let e :
        ((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (chosen_resolution_cochain_view (A := A) π) ≅
          ((((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).obj
              (P : ChainComplex (ModuleCat A) ℕ)).extend
            ComplexShape.embeddingDownNat) :=
      eqToIso rfl
    -- Proof comment: this is the single transport from the chain model of the chosen resolution
    -- to the cochain model used in the inverse-limit comparison.
    exact
      (((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) (-1)).mapIso e) ≪≫
        ((((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (P : ChainComplex (ModuleCat A) ℕ)).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp))).symm
  -- Proof comment: invert the chain/cochain transport and the chosen-resolution Tor computation
  -- to express the cochain degree `-1` homology as the canonical `Tor₁` object.
  exact eCochain.symm ≪≫ eResolution

-- Proof sketch: resolve the finite `A`-module `Q` by finite free modules, tensor that resolution
-- with each stage `M_n`, use flatness over `A ⧸ I^n` and Lemma `15.27.3` to make the inverse
-- systems of `Tor₁^A(Q, M_n)` eventually zero, then pass to inverse limits through the resulting
-- exact complexes. Because finite free modules commute with inverse limits, the cokernel computed
-- after passing to the limit identifies with `Q ⊗[A] lim M_n`.
/-- Lemma 15.27.4 (1): for a surjective inverse system `M_n` of `A`-modules whose stage `M_n` is
flat over `A ⧸ I^n`, the canonical map from `Q ⊗[A] lim M_n` to `lim (Q ⊗[A] M_n)` is bijective
for every finite `A`-module `Q`. -/
theorem inverseLimit_tensor_finiteModule_bijective_of_surjective_and_quotientFlat
    (hflat :
      ∀ n : ℕ+, Module.Flat (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n)))
    (hsurj : ∀ n : ℕ+, Function.Surjective (stepMap M_ n))
    (Q : Type u) [AddCommGroup Q] [Module A Q] [Module.Finite A Q] :
    Function.Bijective (limit.post M_ (tensorLeft (ModuleCat.of A Q))) := by
  -- Proof comment: the finite free comparison begins with the monoidal-unit case, now recorded
  -- explicitly as the rank-one base case for the source free-resolution argument.
  have hunit :
      Function.Bijective (limit.post M_ (tensorLeft (𝟙_ (ModuleCat A)))) :=
    tensor_unit_limit_post_bijective (A := A) (M_ := M_)
  rcases module_exists_finite_free_resolution (R := A) (M := Q) with ⟨F, π, hπ⟩
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let C := chosen_resolution_cochain_view (A := A) π
  let Tstage : ℕ → CochainComplex (ModuleCat A) ℤ :=
    fun n ↦ tensorized_chosen_resolution_stage (A := A) π
      (M_.obj (toDual (Nat.succPNat n)))
  have hCnegTwo : Projective (C.X (-2)) :=
    chosen_resolution_view_term_projective (A := A) π (-2)
  have hCnegOne : Projective (C.X (-1)) :=
    chosen_resolution_view_term_projective (A := A) π (-1)
  have hTorStage :
      ∀ n : ℕ,
        (Tstage n).homology (-1) ≅
          (((Tor (ModuleCat A) 1).obj (ModuleCat.of A Q)).obj
            (M_.obj (toDual (Nat.succPNat n)))) :=
    fun n ↦
      tensorized_chosen_resolution_homology_neg_one_iso_tor_one
        (A := A) (π := π) (M_.obj (toDual (Nat.succPNat n)))
  -- Proof comment: the remaining source-faithful route is to choose a finite free resolution of
  -- `Q`, tensor the fixed cochain view `C` stagewise with the tower `M_`, identify the degree
  -- `0` and `-1` homology of `Tstage n` with `Q ⊗[A] M_(n+1)` and `Tor₁^A(Q, M_(n+1))`.
  -- The `H^{-1}` bridge is now fixed above; what remains is the degree-`0` comparison and then
  -- the Chapter 12 limit argument using Lemma `15.27.3` on the resulting Tor tower.
  -- TODO: prove the source-faithful degree-`0` bridge
  -- `((Tstage n).homology 0) ≅ (tensorLeft (ModuleCat.of A Q)).obj (M_.obj (toDual (Nat.succPNat n)))`,
  -- transport Lemma `15.27.3` through `hTorStage` to make the `H^{-1}` tower essentially zero,
  -- and then assemble the reindexed sequential tower for Lemma `12.31.7`.
  sorry

-- Proof sketch: by Lemma `10.39.5`, it is enough to test injectivity after tensoring with every
-- injective map of finite `A`-modules. Part `(1)` identifies tensoring with `lim M_n` against a
-- finite module with the inverse limit of the stagewise tensors. The stagewise long exact Tor
-- sequences and Lemma `15.27.3` make the obstruction on kernels eventually vanish, and the
-- exactness of inverse limits for surjective systems then yields the needed injectivity.
/-- Lemma 15.27.4 (2): if `M_n` is a surjective inverse system of `A`-modules and each stage
`M_n` is flat over `A ⧸ I^n`, then the inverse limit `lim M_n` is flat over `A`. -/
theorem inverseLimit_flat_of_surjective_and_quotientFlat
    (hflat :
      ∀ n : ℕ+, Module.Flat (A ⧸ I ^ (n : ℕ)) (M_.obj (toDual n)))
    (hsurj : ∀ n : ℕ+, Function.Surjective (stepMap M_ n)) :
    Module.Flat A ↑(limit M_) := by
  -- Proof comment: the source proof now applies the finitely generated ideal criterion for
  -- flatness and transports injectivity through part `(1)` plus the four-term inverse-limit
  -- exactness theorem.
  -- TODO: apply `Module.Flat.iff_lift_lsmul_comp_subtype_injective`, identify the finitely
  -- generated ideal test with a four-term inverse-limit exactness statement, and then invoke part
  -- `(1)` together with the Tor-vanishing input from Lemma `15.27.3`.
  sorry

end
