import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap17.Lemma_17_3_1
import StacksProject_2024.stacks_project.Chap17.Lemma_17_16_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_20_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_15_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_3
import StacksProject_2024.stacks_project.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open Opposite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X

/-- The cochain complex of stalk modules obtained from a complex of `𝒪_X`-modules. -/
abbrev stalkComplex (K : CochainComplex ModX ℤ) (x : X) :
    CochainComplex (ModuleCat (X.presheaf.stalk x)) ℤ :=
  (((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).obj K)

/-- The source-facing stalk complex is exactly the canonical mapped complex at `x`. -/
@[simp] theorem stalkComplex_eq_mapHomologicalComplex_obj
    (K : CochainComplex ModX ℤ) (x : X) :
    stalkComplex K x =
      (((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).obj K) :=
  rfl

/-- The stalkwise K-flatness predicate can be read directly on the canonical mapped complex. -/
@[simp] theorem stalkComplex_isKFlat_iff_mapHomologicalComplex_obj_isKFlat
    (K : CochainComplex ModX ℤ) (x : X) :
    (stalkComplex K x).IsKFlat ↔
      ((((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).obj K)).IsKFlat := by
  rfl

/-- Helper for Lemma 20.26.4: exactness is stable under composing two exact functors. -/
private theorem exactFunctorComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F)
    (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and both
  -- preservation properties compose.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : Limits.PreservesFiniteLimits F := hF.1
  let _ : Limits.PreservesFiniteColimits F := hF.2
  let _ : Limits.PreservesFiniteLimits G := hG.1
  let _ : Limits.PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 20.26.4: exactness transports across a natural isomorphism of functors. -/
private theorem exactFunctorOfNatIso
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {F G : A ⥤ B}
    (e : F ≅ G) :
    exactFunctor A B F → exactFunctor A B G := by
  intro hF
  -- Proof comment: transport finite-limit and finite-colimit preservation across the natural
  -- isomorphism, then repackage the result as exactness.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : Limits.PreservesFiniteLimits F := hF.1
  let _ : Limits.PreservesFiniteColimits F := hF.2
  exact ⟨
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e
  ⟩

section

variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

/-- Helper for Lemma 20.26.4: an open of `X` missing `x` pulls back along `pointInclusion x`
to the bottom open of the one-point space. -/
private theorem pointInclusion_preimage_eq_bot
    (x : X) {U : TopologicalSpace.Opens X} (hxU : x ∉ U) :
    ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) = ⊥ := by
  -- Proof comment: the source of `pointInclusion x` has one point, and that point maps to `x`,
  -- so the preimage is empty exactly when `x` is not in `U`.
  ext y
  cases y
  constructor
  · simpa [pointInclusion_hom_base_apply] using hxU
  · intro hy
    cases hy

/-- Helper for Lemma 20.26.4: the inverse of `pointModuleSheaf_homEquivTop` has the prescribed
top-open component. -/
@[simp] private theorem pointModuleSheaf_homEquivTop_symm_app_top
    (x : X) (G : RingedSpace.Modules (pointRingedSpace x))
    (M : ModuleCat (X.presheaf.stalk x))
    (t : G.val.obj (op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit))) ⟶
      (pointModuleSheaf x M).val.obj (op ⊤)) :
    (((pointModuleSheaf_homEquivTop x G M).symm t).val.app
      (op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit)))) = t :=
  (pointModuleSheaf_homEquivTop x G M).apply_symm_apply t

/-- Helper for Lemma 20.26.4: postcomposing with the top-open isomorphism cancels the inverse
appearing in the point-module comparison map. -/
private theorem pointModuleSheaf_objTopIso_cancel_right
    (x : X) {M N : ModuleCat (X.presheaf.stalk x)}
    (φ : (ModuleCat.restrictScalars
      (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).obj M ⟶
      (ModuleCat.restrictScalars
        (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).obj N) :
    ((pointModuleSheaf_objTopIso x M).hom ≫ φ ≫ (pointModuleSheaf_objTopIso x N).inv) ≫
        (pointModuleSheaf_objTopIso x N).hom =
      (pointModuleSheaf_objTopIso x M).hom ≫ φ := by
  -- Proof comment: reassociate so the rightmost factor is `φ ≫ inv ≫ hom`, then use the iso
  -- triangle identity on `pointModuleSheaf_objTopIso x N`.
  calc
    ((pointModuleSheaf_objTopIso x M).hom ≫ φ ≫ (pointModuleSheaf_objTopIso x N).inv) ≫
        (pointModuleSheaf_objTopIso x N).hom =
      (pointModuleSheaf_objTopIso x M).hom ≫
        (φ ≫ ((pointModuleSheaf_objTopIso x N).inv ≫
          (pointModuleSheaf_objTopIso x N).hom)) := by
        rw [Category.assoc, Category.assoc]
    _ = (pointModuleSheaf_objTopIso x M).hom ≫ (φ ≫ 𝟙 _) := by
      rw [(pointModuleSheaf_objTopIso x N).inv_hom_id]
    _ = (pointModuleSheaf_objTopIso x M).hom ≫ φ := by
      rw [Category.comp_id]

/-- Helper for Lemma 20.26.4: realize a stalk module as the canonical module sheaf on the
one-point ringed space `({x}, \mathcal O_{X, x})`. -/
private noncomputable def pointModuleSheafFunctor
    (x : X) :
    ModuleCat (X.presheaf.stalk x) ⥤ RingedSpace.Modules (pointRingedSpace x) where
  obj M := pointModuleSheaf x M
  map {M N} φ :=
    (pointModuleSheaf_homEquivTop x (pointModuleSheaf x M) N).symm
      ((pointModuleSheaf_objTopIso x M).hom ≫
        (ModuleCat.restrictScalars
          (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).map φ ≫
        (pointModuleSheaf_objTopIso x N).inv)
  map_id M := by
    -- Proof comment: the point-module map is defined by its top-open component, so the identity
    -- law reduces to the identity component on `⊤`.
    -- TODO: after forcing the top-open branch in `pointModuleSheaf_homEquivTop`, identify the
    -- resulting component with `𝟙` by the top-open iso triangle identity.
    sorry
  map_comp {M N P} φ ψ := by
    -- Proof comment: composition is again determined by the top-open component, where the chosen
    -- defining formula is functorial by ordinary composition in `ModuleCat`.
    -- TODO: rewrite the top-open component of the composite as the composite of the two top-open
    -- components, then reduce both `symm` terms at `⊤` and cancel the middle top-open iso.
    sorry

/-- Helper for Lemma 20.26.4: the top-open component of `pointModuleSheafFunctor.map` is the
expected restriction-of-scalars image of the original module morphism. -/
private theorem pointModuleSheafFunctor_map_top
    (x : X) {M N : ModuleCat (X.presheaf.stalk x)} (φ : M ⟶ N) :
    (((pointModuleSheafFunctor (X := X) x).map φ).val.app
        (op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit)))) ≫
        (pointModuleSheaf_objTopIso x N).hom =
      (pointModuleSheaf_objTopIso x M).hom ≫
        (ModuleCat.restrictScalars
          (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).map φ := by
  -- Proof comment: by construction, the map of point module sheaves is the unique morphism whose
  -- top-open component is the displayed restriction-of-scalars map.
  have htop :=
    congrArg (fun t ↦ t ≫ (pointModuleSheaf_objTopIso x N).hom)
      ((pointModuleSheaf_homEquivTop x (pointModuleSheaf x M) N).apply_symm_apply
        ((pointModuleSheaf_objTopIso x M).hom ≫
          (ModuleCat.restrictScalars
            (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).map φ ≫
          (pointModuleSheaf_objTopIso x N).inv))
  have htop' :
      (((pointModuleSheafFunctor (X := X) x).map φ).val.app
          (op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit)))) ≫
          (pointModuleSheaf_objTopIso x N).hom =
        ((pointModuleSheaf_objTopIso x M).hom ≫
          (ModuleCat.restrictScalars
            (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).map φ ≫
          (pointModuleSheaf_objTopIso x N).inv) ≫
          (pointModuleSheaf_objTopIso x N).hom := by
    simpa [pointModuleSheafFunctor, pointModuleSheaf_homEquivTop, Category.assoc] using htop
  exact htop'.trans
    (pointModuleSheaf_objTopIso_cancel_right (x := x)
      ((ModuleCat.restrictScalars
        (eqToHom (pointRingedSpace_ringCatSheaf_obj_top x)).hom).map φ))

/-- Helper for Lemma 20.26.4: taking the stalk complex at `x` preserves acyclicity of a complex
of `𝒪_X`-modules. -/
private theorem stalkComplex_acyclic_of_acyclic
    (M : CochainComplex ModX ℤ) (hM : M.Acyclic) (x : X) :
    (stalkComplex M x).Acyclic := by
  -- Proof comment: acyclicity is degreewise exactness, and exactness of a short complex of
  -- `𝒪_X`-modules can be checked stalkwise by Lemma `17.3.1`.
  rw [HomologicalComplex.acyclic_iff] at hM ⊢
  intro n
  have hStalk :
      (RingedSpace.stalkShortComplex (M.sc n) x).Exact :=
    (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact (M.sc n)).1 (hM n) x
  have hForget :
      (((stalkComplex M x).sc n).map
        (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat)).Exact := by
    -- The stalk of the degree-`n` short complex is definitionally the underlying additive short
    -- complex of the degree-`n` stalk complex.
    simpa [stalkComplex, RingedSpace.stalkShortComplex, RingedSpace.moduleStalkMap] using hStalk
  exact
    ((((stalkComplex M x).sc n).exact_map_iff_of_faithful
      (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat))).mp hForget

/-- Helper for Lemma 20.26.4: taking stalks commutes with tensoring a sheaf module on the right. -/
private noncomputable def stalkTensorRightComparisonIso
    (x : X) (ℱ : ModX) :
    tensorRight ℱ ⋙ RingedSpace.stalkModuleFunctor x ≅
      RingedSpace.stalkModuleFunctor x ⋙
        tensorRight (RingedSpace.stalkModuleCat ℱ x) :=
  NatIso.ofComponents
    (fun 𝒢 ↦ RingedSpace.tensorProductStalkIso 𝒢 ℱ x)
    (fun {𝒢 𝒢'} φ ↦ by
      -- Proof comment: functoriality is exactly the imported tensor/stalk naturality square,
      -- specialized to the identity on the fixed right tensor factor `ℱ`. The remaining
      -- transport blocker is to rewrite the source-side `moduleStalkHom x (φ ▷ ℱ)` and the
      -- target-side `tensorRight` map into a common normal form before applying
      -- `tensorProductStalkIso_naturality`.
      sorry)

/-- Helper for Lemma 20.26.4: after fixing the right tensor factor, the stalk/tensor comparison
extends degreewise to cochain complexes. -/
private noncomputable def stalkTensorRightComplexIso
    (x : X) (ℱ : ModX) (K : CochainComplex ModX ℤ) :
    (((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).obj
      (((tensorRight ℱ).mapHomologicalComplex (up ℤ)).obj K)) ≅
      (((tensorRight (RingedSpace.stalkModuleCat ℱ x)).mapHomologicalComplex (up ℤ)).obj
        (stalkComplex K x)) :=
  -- Proof comment: apply the functor-level tensor/stalk comparison degreewise along the complex
  -- `K`.
  (NatIso.mapHomologicalComplex (stalkTensorRightComparisonIso (X := X) x ℱ) (up ℤ)).app K

/-- Helper for Lemma 20.26.4: the stalked tensor bicomplex underlying `M ⊗ K`. -/
private abbrev stalkTensorObjBicomplexSource
    (M K : CochainComplex ModX ℤ) (x : X) :=
  (((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
    (up ℤ)).obj
      ((((curriedTensor ModX).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj M).obj K)

/-- Helper for Lemma 20.26.4: the tensor bicomplex built from the stalk complexes of `M` and
`K`. -/
private abbrev stalkTensorObjBicomplexTarget
    (M K : CochainComplex ModX ℤ) (x : X) :=
  ((((curriedTensor (ModuleCat (X.presheaf.stalk x))).mapBifunctorHomologicalComplex
    (up ℤ) (up ℤ)).obj (stalkComplex M x)).obj (stalkComplex K x))

/-- Helper for Lemma 20.26.4: the columnwise stalk/tensor comparisons assemble to an
isomorphism between the two tensor bicomplexes. -/
private noncomputable def stalkTensorObjBicomplexIso
    (M K : CochainComplex ModX ℤ) (x : X) :
    stalkTensorObjBicomplexSource (X := X) M K x ≅
      stalkTensorObjBicomplexTarget (X := X) M K x :=
  -- Proof comment: the component in outer degree `q` is `stalkTensorRightComplexIso x (M.X q) K`;
  -- the remaining verification is the naturality of these components against the outer
  -- differential.
  sorry

/-- Helper for Lemma 20.26.4: the point-space realization functor on the one-point ringed space
is exact. -/
private theorem pointModuleSheafFunctorExact
    (x : X) :
    exactFunctor
      (ModuleCat (X.presheaf.stalk x))
      (RingedSpace.Modules (pointRingedSpace x))
      (pointModuleSheafFunctor (X := X) x) := by
  -- Proof comment: if the point-space module functor already carries the standard finite
  -- limit/colimit preservation instances, `ExactFunctor.of` packages the exactness directly.
  -- TODO: package the one-point-space equivalence given by evaluation on `⊤` and transport
  -- exactness across that equivalence; `ExactFunctor.of` does not synthesize the needed finite
  -- limit/colimit instances here.
  sorry

/-- Helper for Lemma 20.26.4: taking the stalk functor commutes with totalization of a
cohomological tensor bicomplex. -/
private abbrev stalkMappedBicomplex
    (x : X) (B : HomologicalComplex₂ ModX (up ℤ) (up ℤ)) :
    HomologicalComplex₂ (ModuleCat (X.presheaf.stalk x)) (up ℤ) (up ℤ) :=
  (((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
    (up ℤ)).obj B

/-- Helper for Lemma 20.26.4: taking the stalk functor commutes with totalization of a
cohomological tensor bicomplex. -/
private noncomputable def stalkTotalTensorBicomplexIso
    (x : X) (B : HomologicalComplex₂ ModX (up ℤ) (up ℤ))
    [B.HasTotal (up ℤ)]
    [(stalkMappedBicomplex (X := X) x B).HasTotal (up ℤ)] :
    stalkComplex (HomologicalComplex₂.total B (up ℤ)) x ≅
      HomologicalComplex₂.total (stalkMappedBicomplex (X := X) x B) (up ℤ) := by
  -- Route correction: the remaining tensor/stalk normalization is no longer degreewise. The
  -- unresolved part is the generic coproduct comparison showing that `stalkModuleFunctor x`
  -- commutes with the totalization coproducts and their induced differential.
  -- TODO: copy the `restrictScalars_total_tensorBicomplexIso` proof pattern from
  -- `Lemma_15_59_3`, replacing restriction of scalars by `stalkModuleFunctor x`.
  sorry

/-- Helper for Lemma 20.26.4: taking stalks commutes with the totalized tensor product of
cochain complexes. -/
private noncomputable def stalkTensorObjIso
    (M K : CochainComplex ModX ℤ) (x : X)
    [HomologicalComplex.HasTensor M K]
    [HomologicalComplex.HasTensor (stalkComplex M x) (stalkComplex K x)] :
    stalkComplex (HomologicalComplex.tensorObj M K) x ≅
      HomologicalComplex.tensorObj (stalkComplex M x) (stalkComplex K x) := by
  -- Route correction: the tensor of cochain complexes is the totalization of the tensor
  -- bicomplex. The degreewise tensor/stalk transport is now isolated in
  -- `stalkTensorObjBicomplexIso`. The remaining blocker is the generic totalization bridge
  -- `stalkTotalTensorBicomplexIso`; once that coproduct comparison is proved, this theorem is the
  -- short composition sketched in the previous attempt.
  sorry

/-- Lemma 20.26.4: a complex `K` of `𝒪_X`-modules is K-flat if and only if, for every point
`x : X`, the induced stalk complex of `𝒪_{X, x}`-modules is K-flat. -/
@[stacks 06YB]
theorem isKFlat_iff_stalkwise_isKFlat (K : CochainComplex ModX ℤ) :
    K.IsKFlat ↔ ∀ x : X, (stalkComplex K x).IsKFlat := by
  -- Route correction: the proof is now split into two explicit frontiers. The easy direction
  -- reduces to the totalized tensor/stalk comparison `stalkTensorObjIso`, whose degreewise
  -- bicomplex part has been isolated above, while the hard direction reduces to the one-point
  -- exact globalization package centered on `pointModuleSheafFunctorExact`.
  -- TODO: compose `stalkTensorObjBicomplexIso` with `stalkTotalTensorBicomplexIso` for the easy
  -- direction, and globalize an acyclic local test complex via `skyscraperModuleSheaf x` for the
  -- reverse direction.
  sorry

/-- If a complex of `𝒪_X`-modules is K-flat, then each stalk complex is K-flat. -/
theorem stalkComplex_isKFlat_of_isKFlat
    (K : CochainComplex ModX ℤ) (hK : K.IsKFlat) (x : X) :
    (stalkComplex K x).IsKFlat :=
  (isKFlat_iff_stalkwise_isKFlat K).mp hK x

/-- If every stalk complex of a complex of `𝒪_X`-modules is K-flat, then the complex is
K-flat. -/
theorem isKFlat_of_stalkComplex_isKFlat
    (K : CochainComplex ModX ℤ)
    (hK : ∀ x : X, (stalkComplex K x).IsKFlat) :
    K.IsKFlat :=
  (isKFlat_iff_stalkwise_isKFlat K).mpr hK

end

end AlgebraicGeometry.RingedSpace
