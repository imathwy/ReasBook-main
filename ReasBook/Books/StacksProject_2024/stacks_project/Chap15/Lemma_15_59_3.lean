import Mathlib
import StacksProject_2024.Chap12.Remark_12_29_2
import StacksProject_2024.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open ModuleCat
open scoped TensorProduct

noncomputable section

universe u v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]
variable {ℬ : Type u₂} [Category.{v₂} ℬ] [Abelian ℬ]

/-- Helper for Lemma 15.59.3: an exact functor sends an acyclic cochain complex to an acyclic
cochain complex. -/
theorem mapHomologicalComplex_acyclic_of_exact
    (F : 𝒜 ⥤ ℬ) (hF : exactFunctor 𝒜 ℬ F)
    (K : CochainComplex 𝒜 ℤ) (hK : K.Acyclic) :
    by
      letI : F.Additive := (exactFunctor_le_additiveFunctor 𝒜 ℬ) F hF
      exact ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic := by
  -- Exact functors preserve the homology data needed to test acyclicity degreewise.
  letI : F.Additive := (exactFunctor_le_additiveFunctor 𝒜 ℬ) F hF
  let hExact := (exactFunctor_iff F).1 hF
  letI : Limits.PreservesFiniteLimits F := hExact.1
  letI : Limits.PreservesFiniteColimits F := hExact.2
  letI : F.PreservesHomology := inferInstance
  rw [HomologicalComplex.acyclic_iff] at hK ⊢
  intro i
  rw [HomologicalComplex.exactAt_iff]
  have hKi : (K.sc i).Exact := by
    simpa [HomologicalComplex.exactAt_iff] using hK i
  -- The short complex in degree `i` stays exact after applying the exact functor.
  simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
    hKi.map F

end

end CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- Helper for Lemma 15.59.3: if a restricted module is zero, then the original module is zero. -/
lemma isZero_of_restrictScalars_obj
    (f : R →+* R') (M : ModuleCat R')
    (hM : CategoryTheory.Limits.IsZero ((ModuleCat.restrictScalars f).obj M)) :
    CategoryTheory.Limits.IsZero M := by
  -- Restriction of scalars does not change the underlying additive group, so zero objects reflect.
  letI : Subsingleton ↑((ModuleCat.restrictScalars f).obj M) :=
    ModuleCat.subsingleton_of_isZero hM
  have hsub : Subsingleton ↑M := by
    simpa using
      (inferInstance : Subsingleton ↑((ModuleCat.restrictScalars f).obj M))
  letI : Subsingleton ↑M := hsub
  exact ModuleCat.isZero_of_subsingleton M

/-- Helper for Lemma 15.59.3: restriction of scalars sends an acyclic cochain complex to an
acyclic cochain complex. -/
lemma restrictScalarsComplex_acyclic_of_acyclic
    (f : R →+* R') (L : CochainComplex (ModuleCat.{u} R') ℤ)
    (hL : L.Acyclic) :
    (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj L).Acyclic :=
  by
    -- Restriction of scalars is exact, so the general exact-functor bridge applies directly.
    exact CategoryTheory.mapHomologicalComplex_acyclic_of_exact
      (ModuleCat.restrictScalars.{u} f) (restrictScalars_exact f) L hL

/-- Helper for Lemma 15.59.3: if restriction of scalars of a cochain complex is acyclic, then the
original cochain complex is acyclic. -/
lemma acyclic_of_restrictScalarsComplex_acyclic
    (f : R →+* R') (T : CochainComplex (ModuleCat.{u} R') ℤ)
    (hT :
      (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj T).Acyclic) :
    T.Acyclic :=
  by
    rw [HomologicalComplex.acyclic_iff] at hT ⊢
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have hzero_restricted :
        CategoryTheory.Limits.IsZero
          ((((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj T).homology i) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact hT i
    have hzero_restricted_homology :
        CategoryTheory.Limits.IsZero ((ModuleCat.restrictScalars.{u} f).obj (T.homology i)) := by
      -- Compare the restricted homology object with the homology of the restricted complex.
      exact hzero_restricted.of_iso ((T.sc i).mapHomologyIso (ModuleCat.restrictScalars.{u} f)).symm
    -- Restriction of scalars does not change the underlying additive group, so zero reflects back.
    exact isZero_of_restrictScalars_obj f (T.homology i) hzero_restricted_homology

/-- Helper for Lemma 15.59.3: canceling the intermediate base change commutes with maps in the
left tensor factor. -/
lemma cancelBaseChange_naturality_left
    [Algebra R R'] {M M' : Type u} [AddCommGroup M] [Module R' M]
    [Module R M] [IsScalarTower R R' M]
    [AddCommGroup M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']
    {N : Type u} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R'] M') :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R' M' N).toLinearMap ∘ₗ
      TensorProduct.map g (LinearMap.id : (R' ⊗[R] N) →ₗ[R'] (R' ⊗[R] N)) =
    (TensorProduct.AlgebraTensorModule.map g (LinearMap.id : N →ₗ[R] N)) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R' M N).toLinearMap := by
  -- Compare the two composites on pure tensors `m ⊗ (a ⊗ n)` and extend by bilinearity.
  apply TensorProduct.ext'
  intro m y
  induction y using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a n =>
      simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  | add y z hy hz =>
      rw [TensorProduct.tmul_add, LinearMap.map_add, LinearMap.map_add, hy, hz]

/-- Helper for Lemma 15.59.3: canceling the intermediate base change commutes with maps in the
right tensor factor after extending scalars on that factor. -/
lemma cancelBaseChange_naturality_right
    [Algebra R R'] (M : Type u) [AddCommGroup M] [Module R' M]
    [Module R M] [IsScalarTower R R' M]
    {N Q : Type u} [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    (h : N →ₗ[R] Q) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R' M Q).toLinearMap ∘ₗ
      TensorProduct.map (LinearMap.id : M →ₗ[R'] M) (h.baseChange R') =
    (TensorProduct.AlgebraTensorModule.map (LinearMap.id : M →ₗ[R'] M) h) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R' M N).toLinearMap := by
  -- Compare the two composites on pure tensors `m ⊗ (a ⊗ n)` and extend by bilinearity.
  apply TensorProduct.ext'
  intro m y
  induction y using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul a n =>
      simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  | add y z hy hz =>
      rw [TensorProduct.tmul_add, LinearMap.map_add, LinearMap.map_add, hy, hz]

/-- Helper for Lemma 15.59.3: after choosing the algebra structure induced by `f`, the restricted
`R`-action on an `R'`-module forms the expected scalar tower with the original `R'`-action. -/
private lemma restrictScalars_obj_isScalarTower
    (f : R →+* R') (M : ModuleCat.{u} R') :
    letI : Algebra R R' := f.toAlgebra
    letI : Module R ↑M := Module.compHom ↑M f
    IsScalarTower R R' ↑M := by
  letI : Algebra R R' := f.toAlgebra
  letI : Module R ↑M := Module.compHom ↑M f
  -- The restricted action is literally scalar multiplication through `f = algebraMap R R'`.
  exact IsScalarTower.of_algebraMap_smul fun r s ↦ rfl

/-- Helper for Lemma 15.59.3: the component of the base-change cancellation comparison at a fixed
`R`-module `X`. -/
private noncomputable def cancelBaseChange_tensor_right_componentIso
    (f : R →+* R') (M : ModuleCat.{u} R') (X : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars f) ⋙ (curriedTensor (ModuleCat R')).obj M ⋙
      (ModuleCat.restrictScalars.{u} f)).obj X ≅
      ((curriedTensor (ModuleCat R)).obj ((ModuleCat.restrictScalars f).obj M)).obj X :=
  by
    letI : Algebra R R' := f.toAlgebra
    letI : Module R ↑M := Module.compHom ↑M f
    letI : IsScalarTower R R' ↑M :=
      restrictScalars_obj_isScalarTower (R := R) (R' := R') f M
    -- Rewrite both owners to the explicit tensor-product modules so the built-in cancellation
    -- isomorphism applies without extra transport.
    change (ModuleCat.restrictScalars f).obj (ModuleCat.of R' (↑M ⊗[R'] (R' ⊗[R] ↑X))) ≅
      (ModuleCat.restrictScalars f).obj (ModuleCat.of R' (↑M ⊗[R] ↑X))
    exact (ModuleCat.restrictScalars f).mapIso
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R' M X).toModuleIso)

/-- Helper for Lemma 15.59.3: for a fixed `R'`-module `M`, cancelling the intermediate base
change gives a natural isomorphism from first extending scalars and then tensoring by `M` to
tensoring by the restricted module `M` over `R`. -/
noncomputable def cancelBaseChange_tensor_right_natIso
    (f : R →+* R') (M : ModuleCat.{u} R') :
    ((ModuleCat.extendScalars f) ⋙ (curriedTensor (ModuleCat R')).obj M ⋙
      (ModuleCat.restrictScalars.{u} f)) ≅
      (curriedTensor (ModuleCat R)).obj ((ModuleCat.restrictScalars f).obj M) :=
  by
    letI : Algebra R R' := f.toAlgebra
    letI : Module R ↑M := Module.compHom ↑M f
    letI : IsScalarTower R R' ↑M :=
      restrictScalars_obj_isScalarTower (R := R) (R' := R') f M
    -- Route correction: the componentwise cancellation is now packaged in the proved helper
    -- `cancelBaseChange_tensor_right_componentIso`, so only the functor-level naturality square
    -- remains to be normalized to `cancelBaseChange_naturality_right`.
    refine NatIso.ofComponents
      (fun X ↦ cancelBaseChange_tensor_right_componentIso (R := R) (R' := R') f M X)
      (fun {X Y} g ↦ ?_)
    -- Rewriting the functorial maps down to the underlying tensor-product maps leaves exactly
    -- the right-factor naturality identity proved above.
    ext x
    simpa using congrArg (fun k ↦ k x)
      (cancelBaseChange_naturality_right (R := R) (R' := R') (M := (M : Type u)) g.hom)

/-- Helper for Lemma 15.59.3: applying the natural base-change cancellation to a fixed
`R`-complex identifies the two resulting cochain complexes. -/
noncomputable def cancelBaseChange_tensor_right_complexIso
    (f : R →+* R') (M : ModuleCat.{u} R') (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((Functor.mapHomologicalComplex
        ((ModuleCat.extendScalars f) ⋙ (curriedTensor (ModuleCat R')).obj M ⋙
          (ModuleCat.restrictScalars.{u} f))
        (up ℤ)).obj K) ≅
      ((Functor.mapHomologicalComplex
        ((curriedTensor (ModuleCat R)).obj ((ModuleCat.restrictScalars.{u} f).obj M))
        (up ℤ)).obj K) :=
  by
    -- Apply the functor-level natural isomorphism degreewise to the whole complex `K`.
    exact
      (NatIso.mapHomologicalComplex
        (cancelBaseChange_tensor_right_natIso (R := R) (R' := R') f M) (up ℤ)).app K

/-- Helper for Lemma 15.59.3: the restricted tensor bicomplex underlying
`L ⊗_{R'} (R' ⊗_R K)`. -/
private abbrev restrictScalars_tensorObj_extendScalars_bicomplexSource
    (f : R →+* R') (L : CochainComplex (ModuleCat.{u} R') ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj
    ((((curriedTensor (ModuleCat R')).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj L).obj
      (((ModuleCat.extendScalars f).mapHomologicalComplex (up ℤ)).obj K))

/-- Helper for Lemma 15.59.3: the tensor bicomplex underlying
`(L|_R) ⊗_R K`. -/
private abbrev restrictScalars_tensorObj_extendScalars_bicomplexTarget
    (f : R →+* R') (L : CochainComplex (ModuleCat.{u} R') ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj
      (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj L)).obj K)

/-- Helper for Lemma 15.59.3: as the left degree varies, the columnwise base-change
cancellation still intertwines the outer differentials of the restricted tensor bicomplex. -/
private theorem restrictScalars_tensorObj_extendScalars_outer_comm
    (f : R →+* R') (L : CochainComplex (ModuleCat.{u} R') ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (q q' : ℤ) (_hq : (up ℤ).Rel q q') :
    (cancelBaseChange_tensor_right_complexIso (R := R) (R' := R') f (L.X q) K).hom ≫
        (restrictScalars_tensorObj_extendScalars_bicomplexTarget
          (R := R) (R' := R') f L K).d q q' =
      (restrictScalars_tensorObj_extendScalars_bicomplexSource
        (R := R) (R' := R') f L K).d q q' ≫
        (cancelBaseChange_tensor_right_complexIso (R := R) (R' := R') f (L.X q') K).hom := by
  letI : Algebra R R' := f.toAlgebra
  letI : Module R ↑(L.X q) := Module.compHom ↑(L.X q) f
  letI : Module R ↑(L.X q') := Module.compHom ↑(L.X q') f
  letI : IsScalarTower R R' ↑(L.X q) :=
    restrictScalars_obj_isScalarTower (R := R) (R' := R') f (L.X q)
  letI : IsScalarTower R R' ↑(L.X q') :=
    restrictScalars_obj_isScalarTower (R := R) (R' := R') f (L.X q')
  -- Evaluate the outer square degreewise in the `K`-direction; each component is the
  -- left-factor naturality square for cancelling the intermediate base change.
  ext p x
  simp only [restrictScalars_tensorObj_extendScalars_bicomplexSource,
    restrictScalars_tensorObj_extendScalars_bicomplexTarget,
    cancelBaseChange_tensor_right_complexIso]
  simpa using congrArg (fun k ↦ k x)
    ((cancelBaseChange_naturality_left (R := R) (R' := R') (N := (K.X p : Type u))
      (g := (L.d q q').hom)).symm)

/-- Helper for Lemma 15.59.3: the columnwise cancellation isomorphisms assemble to an
isomorphism of the two bicomplexes comparing `L ⊗_{R'} (R' ⊗_R K)` with `(L|_R) ⊗_R K`. -/
private noncomputable def restrictScalars_tensorObj_extendScalars_bicomplexIso
    (f : R →+* R') (L : CochainComplex (ModuleCat.{u} R') ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    restrictScalars_tensorObj_extendScalars_bicomplexSource (R := R) (R' := R') f L K ≅
      restrictScalars_tensorObj_extendScalars_bicomplexTarget (R := R) (R' := R') f L K :=
  -- The source proof identifies the total tensor complexes via a bicomplex isomorphism whose
  -- `q`-th column is the already constructed complex-level cancellation isomorphism.
  HomologicalComplex.Hom.isoOfComponents
    (fun q : ℤ ↦ cancelBaseChange_tensor_right_complexIso (R := R) (R' := R') f (L.X q) K)
    (restrictScalars_tensorObj_extendScalars_outer_comm (R := R) (R' := R') f L K)

/-- Helper for Lemma 15.59.3: restriction of scalars commutes with totalization on a cohomological
bicomplex of modules. -/
private noncomputable def restrictScalars_total_tensorBicomplexIso
    (f : R →+* R')
    (B : HomologicalComplex₂ (ModuleCat.{u} R') (up ℤ) (up ℤ)) :
    ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj
        (HomologicalComplex₂.total B (up ℤ)) ≅
      HomologicalComplex₂.total
        ((((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
          (up ℤ)).obj B)
        (up ℤ) := by
  let F : ModuleCat.{u} R' ⥤ ModuleCat.{u} R := ModuleCat.restrictScalars.{u} f
  let B' :
      HomologicalComplex₂ (ModuleCat.{u} R) (up ℤ) (up ℤ) :=
    (((F.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj B)
  let π := ComplexShape.π (up ℤ) (up ℤ) (up ℤ)
  refine (HomologicalComplex.Hom.isoOfComponents (fun n ↦ ?_) ?_).symm
  · change ∐ F.obj ∘ B.toGradedObject.mapObjFun π n ≅
      F.obj (∐ B.toGradedObject.mapObjFun π n)
    letI : HasCoproduct (B.toGradedObject.mapObjFun π n) := by infer_instance
    letI : PreservesColimit (Discrete.functor (B.toGradedObject.mapObjFun π n)) F := by
      infer_instance
    -- Route correction: `isoOfComponents` expects the comparison from the coproduct of images
    -- back to the image of the coproduct, so we use the symmetric coproduct comparison.
    exact (PreservesCoproduct.iso F (B.toGradedObject.mapObjFun π n)).symm
  intro i j hij
  letI : HasCoproduct (B.toGradedObject.mapObjFun π i) := by infer_instance
  letI : HasCoproduct (B.toGradedObject.mapObjFun π j) := by infer_instance
  letI : PreservesColimit (Discrete.functor (B.toGradedObject.mapObjFun π i)) F := by
    infer_instance
  letI : PreservesColimit (Discrete.functor (B.toGradedObject.mapObjFun π j)) F := by
    infer_instance
  change (PreservesCoproduct.iso F (B.toGradedObject.mapObjFun π i)).inv ≫
      F.map ((HomologicalComplex₂.total B (up ℤ)).d i j) =
    (HomologicalComplex₂.total B' (up ℤ)).d i j ≫
      (PreservesCoproduct.iso F (B.toGradedObject.mapObjFun π j)).inv
  let αi := PreservesCoproduct.iso F (B.toGradedObject.mapObjFun π i)
  let αj := PreservesCoproduct.iso F (B.toGradedObject.mapObjFun π j)
  have hij' : i + 1 = j := by
    simpa [ComplexShape.up, ComplexShape.up'] using hij
  -- Compare both morphisms on each summand of the degree-`i` coproduct.
  apply Limits.Sigma.hom_ext
  rintro ⟨⟨p, q⟩, hpq⟩
  have hp : (up ℤ).Rel p (p + 1) := by
    simp [ComplexShape.up, ComplexShape.up']
  have hq : (up ℤ).Rel q (q + 1) := by
    simp [ComplexShape.up, ComplexShape.up']
  have hpq' : p + q = i := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff, π] using hpq
  have hπ₁ : π (p + 1, q) = j := by
    dsimp [π]
    omega
  have hπ₂ : π (p, q + 1) = j := by
    dsimp [π]
    omega
  have hιi :
      Sigma.ι (F.obj ∘ B.toGradedObject.mapObjFun π i) ⟨⟨p, q⟩, hpq⟩ ≫ αi.inv =
        F.map (Sigma.ι (B.toGradedObject.mapObjFun π i) ⟨⟨p, q⟩, hpq⟩) := by
    -- The summand injection identity is exactly the coproduct comparison computation for `αi.inv`.
    simpa only [PreservesCoproduct.inv_hom] using
      (Limits.ι_comp_sigmaComparison (G := F)
        (f := B.toGradedObject.mapObjFun π i) ⟨⟨p, q⟩, hpq⟩)
  have hιj₁ :
      B'.ιTotal (up ℤ) (p + 1) q j hπ₁ ≫ αj.inv =
        F.map (B.ιTotal (up ℤ) (p + 1) q j hπ₁) := by
    -- The same coproduct comparison identifies the `(p + 1, q)` summand after restriction.
    simpa only [B', π, PreservesCoproduct.inv_hom] using
      (Limits.ι_comp_sigmaComparison (G := F)
        (f := B.toGradedObject.mapObjFun π j) ⟨⟨p + 1, q⟩, hπ₁⟩)
  have hιj₂ :
      B'.ιTotal (up ℤ) p (q + 1) j hπ₂ ≫ αj.inv =
        F.map (B.ιTotal (up ℤ) p (q + 1) j hπ₂) := by
    -- Likewise for the `(p, q + 1)` summand entering the target total degree `j`.
    simpa only [B', π, PreservesCoproduct.inv_hom] using
      (Limits.ι_comp_sigmaComparison (G := F)
        (f := B.toGradedObject.mapObjFun π j) ⟨⟨p, q + 1⟩, hπ₂⟩)
  have hd₁ :
      B'.d₁ (up ℤ) p q j ≫ αj.inv = F.map (B.d₁ (up ℤ) p q j) := by
    -- Expand the horizontal part of the total differential on both bicomplexes.
    rw [HomologicalComplex₂.d₁_eq (K := B) (c₁₂ := up ℤ) hp q j hπ₁,
      HomologicalComplex₂.d₁_eq (K := B') (c₁₂ := up ℤ) hp q j hπ₁]
    rw [show ComplexShape.ε₁ (up ℤ) (up ℤ) (up ℤ) (p, q) = 1 by simp, one_smul, one_smul]
    have hmapd₁ : (B'.d p (p + 1)).f q = F.map ((B.d p (p + 1)).f q) := by
      simpa [B', Functor.mapHomologicalComplex_obj_d]
    -- Precompose the target summand identity with the mapped horizontal differential.
    simpa [Category.assoc, hmapd₁, ← Functor.map_comp] using
      congrArg (fun k => (B'.d p (p + 1)).f q ≫ k) hιj₁
  have hd₂ :
      B'.d₂ (up ℤ) p q j ≫ αj.inv = F.map (B.d₂ (up ℤ) p q j) := by
    -- TODO: finish the signed vertical-differential transport by matching Lean's exact
    -- parenthesization of `p.negOnePow • (d ≫ ι)` on both sides, then precompose `hιj₂` by the
    -- signed mapped differential and fold the target back with `Functor.map_comp` and
    -- `Functor.map_units_smul`.
    sorry
  -- TODO: once `hd₂` is established, finish the naturality check by rewriting
  -- `B.ιTotal ≫ total.d` and `B'.ιTotal ≫ total.d` to `d₁ + d₂`, then substitute `hd₁` and `hd₂`.
  sorry

/-- Helper for Lemma 15.59.3: after restricting scalars, tensoring an `R'`-complex with the
scalar extension of an `R`-complex is canonically the same as tensoring the restricted complex
with the original one over `R`. -/
noncomputable def restrictScalars_tensorObj_extendScalars_iso
    (f : R →+* R') (L : CochainComplex (ModuleCat.{u} R') ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj
      (HomologicalComplex.tensorObj L
        (((ModuleCat.extendScalars f).mapHomologicalComplex (up ℤ)).obj K))) ≅
      HomologicalComplex.tensorObj
        (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj L) K :=
  by
    let B :
        HomologicalComplex₂ (ModuleCat.{u} R') (up ℤ) (up ℤ) :=
      (((curriedTensor (ModuleCat R')).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj L).obj
        (((ModuleCat.extendScalars f).mapHomologicalComplex (up ℤ)).obj K)
    exact
      restrictScalars_total_tensorBicomplexIso (R := R) (R' := R') f B ≪≫
        HomologicalComplex₂.total.mapIso
          (restrictScalars_tensorObj_extendScalars_bicomplexIso (R := R) (R' := R') f L K)
          (up ℤ)

/-- Helper for Lemma 15.59.3: tensoring an acyclic `R'`-complex with the scalar extension of a
K-flat `R`-complex stays acyclic. -/
lemma tensorObj_extendScalars_acyclic_of_isKFlat
    (f : R →+* R') (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.IsKFlat)
    (L : CochainComplex (ModuleCat.{u} R') ℤ) (hL : L.Acyclic) :
    (HomologicalComplex.tensorObj L
      (((ModuleCat.extendScalars f).mapHomologicalComplex (up ℤ)).obj K)).Acyclic :=
  by
    -- Restrict scalars on the acyclic test complex so the original K-flatness hypothesis applies.
    have hRestrictedL :
        (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj L).Acyclic :=
      restrictScalarsComplex_acyclic_of_acyclic f L hL
    have hTensorRestricted :
        (HomologicalComplex.tensorObj
          (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj L) K).Acyclic :=
      CochainComplex.acyclic_tensorObj_of_isKFlat hK hRestrictedL
    have hRestrictedTensor :
        (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (up ℤ)).obj
          (HomologicalComplex.tensorObj L
            (((ModuleCat.extendScalars f).mapHomologicalComplex (up ℤ)).obj K))).Acyclic := by
      -- Transport the restricted tensor complex across the comparison isomorphism.
      intro i
      exact HomologicalComplex.ExactAt.of_iso (hTensorRestricted i)
        (restrictScalars_tensorObj_extendScalars_iso f L K).symm
    -- Reflection of acyclicity along restriction of scalars closes the original goal.
    exact acyclic_of_restrictScalarsComplex_acyclic f _ hRestrictedTensor

/- Domain-style sampling:
- primary domain: change of rings for module-valued cochain complexes and preservation of the
  owner predicate `CochainComplex.IsKFlat`;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `ModuleCat.extendScalars`,
  `Functor.mapHomologicalComplex`.
- best owner abstraction: the owner is still the predicate `K.IsKFlat` on the cochain complex
  itself; extension of scalars is bridge data, not a second owner.
- primitive data: the ring map `f`, the complex `K`, and the hypothesis `hK : K.IsKFlat`.
- derived API: K-flatness of the canonically extended complex.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that extension of scalars preserves K-flatness;
- `core/canonical`: `CochainComplex.IsKFlat`;
- `bridge/view`: the functor `extendScalars f` on module complexes.

The target complex is canonical data coming from `extendScalars f`, so the public statement should
expose only the owner predicate on that complex rather than any auxiliary wrapper.
-/

-- Proof sketch: unfold `CochainComplex.IsKFlat`. For an acyclic `R'`-complex `L`, view `L` as an
-- `R`-complex by restriction of scalars and use the canonical identification
-- `(K ⊗[R] R') ⊗[R'] L ≅ K ⊗[R] L`; then apply the K-flatness of `K`.
/-- Lemma 15.59.3: for a ring map `R → R'`, extension of scalars sends a K-flat complex of
`R`-modules to a K-flat complex of `R'`-modules. -/
theorem extendScalarsComplex_isKFlat
    (f : R →+* R') (K : CochainComplex (ModuleCat R) ℤ)
    (hK : K.IsKFlat) :
    CochainComplex.IsKFlat (((extendScalars f).mapHomologicalComplex (up ℤ)).obj K) :=
  by
    -- Route correction: work source-faithfully by testing against an acyclic `R'`-complex,
    -- restricting scalars, applying the original K-flatness hypothesis, and reflecting back.
    rw [CochainComplex.isKFlat_iff]
    intro L _ hL
    exact tensorObj_extendScalars_acyclic_of_isKFlat f K hK L hL

end
