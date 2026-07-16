import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.ExternalTensor

/-!
# External-tensor collapse infrastructure for Theorem 16-16.1-5

This theorem-local support file builds the external-tensor-on-the-left additive map on Serre's
Grothendieck groups and two collapse lemmas relating external-tensor classes to inflations.

Main declarations:
* `Representation.extTensorLeft` and `Representation.extTensorLeft_apply_class`: external-tensoring
  on the left with a fixed finite-dimensional rep `U` is additive on classes.
* `Representation.finiteRepGrothendieckClass_eq_of_representationEquiv`: a `Representation.Equiv`
  yields an equality of Grothendieck classes.
* `Representation.externalTensor_unit_class_eq_comp_fst`: the class of `U ⊠ 𝟙` collapses to the
  class of the left inflation `U.ρ.comp (MonoidHom.fst S P)`.
-/

noncomputable section

universe u

open CategoryTheory
open scoped Representation Representation.ExternalTensor MonoidAlgebra TensorProduct
open scoped MonoidalCategory

namespace Representation

variable {k : Type u} [Field k]

/-! ### (B) representation equivalence to class equality -/

/-- Helper for Theorem 16-16.1-5: a `Representation.Equiv` of finite-dimensional representations
yields an equality of Grothendieck classes. -/
theorem finiteRepGrothendieckClass_eq_of_representationEquiv {G : Type u} [Group G]
    {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [Module.Finite k V] [Module.Finite k W]
    (ρ : Representation k G V) (σ : Representation k G W) (h : ρ.Equiv σ) :
    [FDRep.of ρ]₀ = [FDRep.of σ]₀ := by
  -- Forward and inverse intertwining maps coming from the linear equivalence `h`.
  let hcomm : ∀ g, (h.toLinearEquiv : V →ₗ[k] W) ∘ₗ ρ g = σ g ∘ₗ (h.toLinearEquiv : V →ₗ[k] W) :=
    fun g => h.toIntertwiningMap.isIntertwining' g
  let hcomm' : ∀ g, (h.toLinearEquiv.symm : W →ₗ[k] V) ∘ₗ σ g
      = ρ g ∘ₗ (h.toLinearEquiv.symm : W →ₗ[k] V) :=
    h.toLinearEquiv.isIntertwining_symm_isIntertwining hcomm
  -- Package both directions as `Rep` morphisms.
  let fRep : (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ) ⟶
      (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of σ) :=
    Rep.ofHom ⟨(h.toLinearEquiv : V →ₗ[k] W), hcomm⟩
  let gRep : (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of σ) ⟶
      (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ) :=
    Rep.ofHom ⟨(h.toLinearEquiv.symm : W →ₗ[k] V), hcomm'⟩
  -- Assemble the `Rep` isomorphism.
  let eRep : (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ) ≅
      (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of σ) := by
    refine ⟨fRep, gRep, ?_, ?_⟩
    · ext x
      change h.toLinearEquiv.symm (h.toLinearEquiv x) = x
      exact h.toLinearEquiv.symm_apply_apply x
    · ext x
      change h.toLinearEquiv (h.toLinearEquiv.symm x) = x
      exact h.toLinearEquiv.apply_symm_apply x
  -- Transport the `Rep` isomorphism to an `FDRep` isomorphism via the forgetful linear equiv.
  let e : FDRep.of ρ ≅ FDRep.of σ := by
    refine ⟨(FDRep.forget₂HomLinearEquiv (FDRep.of ρ) (FDRep.of σ)) eRep.hom,
      (FDRep.forget₂HomLinearEquiv (FDRep.of σ) (FDRep.of ρ)) eRep.inv, ?_, ?_⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) ⟨e⟩

/-! ### (A) external-tensor on the left -/

/-- Helper for Theorem 16-16.1-5: the free lift sending a finite-dimensional class on `P` to its
external tensor on the left with the fixed rep `U`. -/
abbrev extTensorLeftLift {S P : Type u} [Group S] [Group P] (U : FDRep k S) :
    FreeAbelianGroup (FDRep k P) →+ R₀[k](S × P) :=
  FreeAbelianGroup.lift fun W ↦ [FDRep.of (U.ρ ⊠ W.ρ)]₀

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Theorem 16-16.1-5: `id_{U.V} ⊗ f` intertwines the two product-group actions
`U.ρ ⊠ W₁.ρ` and `U.ρ ⊠ W₂.ρ`. -/
theorem extTensorLeft_isIntertwining {S P : Type u} [Group S] [Group P] (U : FDRep k S)
    {W₁ W₂ : FDRep k P} (f : W₁ ⟶ W₂) (sp : S × P) :
    LinearMap.lTensor U.V (((forget₂ (FDRep k P) (Rep k P)).map f).hom.toLinearMap) ∘ₗ
        (U.ρ ⊠ W₁.ρ) sp =
      (U.ρ ⊠ W₂.ρ) sp ∘ₗ
        LinearMap.lTensor U.V (((forget₂ (FDRep k P) (Rep k P)).map f).hom.toLinearMap) := by
  -- `f` intertwines `W₁.ρ` with `W₂.ρ` at the group element `sp.2`.
  have hf := (((forget₂ (FDRep k P) (Rep k P)).map f).hom.isIntertwining' sp.2)
  simp only [FDRep.forget₂_ρ] at hf
  -- Work at the level of linear maps (avoiding the carrier-instance diamond on pure tensors):
  -- expand both external-tensor actions to `TensorProduct.map`, then commute `lTensor` through.
  rw [tprod_apply, tprod_apply]
  simp only [MonoidHom.coe_comp, MonoidHom.coe_fst, MonoidHom.coe_snd, Function.comp_apply]
  rw [LinearMap.lTensor_comp_map, LinearMap.map_comp_lTensor]
  -- Both sides become `TensorProduct.map (U.ρ sp.1) _`; the inner factors agree by `hf`.
  congr 1

/-- Helper for Theorem 16-16.1-5: the explicit `Rep` morphism `id_{U.V} ⊗ f` built from
external-tensoring on the left with `U`. -/
abbrev extTensorLeft_repHom {S P : Type u} [Group S] [Group P] (U : FDRep k S)
    {W₁ W₂ : FDRep k P} (f : W₁ ⟶ W₂) :
    (forget₂ (FDRep k (S × P)) (Rep k (S × P))).obj (FDRep.of (U.ρ ⊠ W₁.ρ)) ⟶
      (forget₂ (FDRep k (S × P)) (Rep k (S × P))).obj (FDRep.of (U.ρ ⊠ W₂.ρ)) :=
  Rep.ofHom ⟨LinearMap.lTensor U.V (((forget₂ (FDRep k P) (Rep k P)).map f).hom.toLinearMap),
    extTensorLeft_isIntertwining (k := k) (S := S) (P := P) U f⟩

/-- Helper for Theorem 16-16.1-5: transport an `FDRep` morphism `f : W₁ ⟶ W₂` along
external-tensoring on the left with `U` by tensoring its underlying `k`-linear map on the left
with `id_{U.V}` and rechecking equivariance for the product-group action. -/
abbrev extTensorLeft_map_local {S P : Type u} [Group S] [Group P] (U : FDRep k S)
    {W₁ W₂ : FDRep k P} (f : W₁ ⟶ W₂) :
    FDRep.of (U.ρ ⊠ W₁.ρ) ⟶ FDRep.of (U.ρ ⊠ W₂.ρ) :=
  (FDRep.forget₂HomLinearEquiv _ _)
    (extTensorLeft_repHom (k := k) (S := S) (P := P) U f)

/-- Helper for Theorem 16-16.1-5: forgetting the external-tensor-transported morphism recovers the
explicit `Rep` morphism built from `id ⊗ f`. -/
theorem extTensorLeft_map_forget_local {S P : Type u} [Group S] [Group P] (U : FDRep k S)
    {W₁ W₂ : FDRep k P} (f : W₁ ⟶ W₂) :
    (forget₂ (FDRep k (S × P)) (Rep k (S × P))).map
        (extTensorLeft_map_local (k := k) (S := S) (P := P) U f) =
      extTensorLeft_repHom (k := k) (S := S) (P := P) U f := by
  exact (FDRep.forget₂HomLinearEquiv _ _).left_inv _

/-- Helper for Theorem 16-16.1-5: the explicit short complex obtained by external-tensoring the
three terms of `S` on the left with `U`, tensoring the underlying linear maps with `id_{U.V}`. -/
abbrev extTensorLeft_shortComplex_local {S P : Type u} [Group S] [Group P] (U : FDRep k S)
    (C : ShortComplex (FDRep k P)) : ShortComplex (FDRep k (S × P)) :=
  ShortComplex.mk
    (extTensorLeft_map_local (k := k) (S := S) (P := P) U C.f)
    (extTensorLeft_map_local (k := k) (S := S) (P := P) U C.g)
    (by
      -- After forgetting to `Rep`, composition is `id ⊗ (g ∘ f) = id ⊗ 0 = 0`.
      apply (forget₂ (FDRep k (S × P)) (Rep k (S × P))).map_injective
      rw [Functor.map_comp]
      rw [extTensorLeft_map_forget_local (k := k) (S := S) (P := P) U C.f]
      rw [extTensorLeft_map_forget_local (k := k) (S := S) (P := P) U C.g]
      -- The underlying linear maps of `C.f` and `C.g` compose to zero over `P`.
      have hgf :
          ((forget₂ (FDRep k P) (Rep k P)).map C.g).hom.toLinearMap ∘ₗ
            ((forget₂ (FDRep k P) (Rep k P)).map C.f).hom.toLinearMap = 0 := by
        have hcomp : (forget₂ (FDRep k P) (Rep k P)).map C.f ≫
            (forget₂ (FDRep k P) (Rep k P)).map C.g = 0 := by
          rw [← Functor.map_comp, C.zero, Functor.map_zero]
        ext z
        have h2 := congrArg (fun m => (Rep.Hom.hom m).toLinearMap z) hcomp
        simpa using h2
      -- Tensoring the composite `g ∘ f = 0` on the left with `U.V` is zero.
      have hlt :
          LinearMap.lTensor U.V (((forget₂ (FDRep k P) (Rep k P)).map C.g).hom.toLinearMap) ∘ₗ
            LinearMap.lTensor U.V (((forget₂ (FDRep k P) (Rep k P)).map C.f).hom.toLinearMap)
              = 0 := by
        rw [← LinearMap.lTensor_comp]
        rw [show ((forget₂ (FDRep k P) (Rep k P)).map C.g).hom.toLinearMap ∘ₗ
              ((forget₂ (FDRep k P) (Rep k P)).map C.f).hom.toLinearMap = 0 from hgf]
        exact LinearMap.lTensor_zero U.V
      -- Reduce the `Rep` composition to its underlying linear map.
      apply (forget₂ (Rep k (S × P)) (ModuleCat k)).map_injective
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [Functor.map_comp, Functor.map_zero, ModuleCat.hom_comp,
        ModuleCat.hom_zero, LinearMap.zero_apply, LinearMap.comp_apply]
      change (LinearMap.lTensor U.V (((forget₂ (FDRep k P) (Rep k P)).map C.g).hom.toLinearMap) ∘ₗ
          LinearMap.lTensor U.V (((forget₂ (FDRep k P) (Rep k P)).map C.f).hom.toLinearMap)) x = 0
      rw [hlt, LinearMap.zero_apply])

/-- Helper for Theorem 16-16.1-5: external-tensoring a short exact sequence on the left with the
fixed finite-dimensional (hence flat) rep `U` keeps it short exact. -/
theorem extTensorLeft_shortExact_local {S P : Type u} [Group S] [Group P] (U : FDRep k S)
    (C : ShortComplex (FDRep k P)) (hC : C.ShortExact) :
    (extTensorLeft_shortComplex_local (k := k) (S := S) (P := P) U C).ShortExact := by
  -- `U.V` is a finite-dimensional vector space over the field `k`, hence flat.
  have : Module.Flat k U.V := inferInstance
  -- The original linear maps over `P`.
  let F : FDRep k P ⥤ ModuleCat k :=
    (forget₂ (FDRep k P) (Rep k P)) ⋙ (forget₂ (Rep k P) (ModuleCat k))
  have hCF : (C.map F).ShortExact := by
    simpa [F] using hC.map_of_exact F
  let fP : C.X₁ →ₗ[k] C.X₂ := (((forget₂ (FDRep k P) (Rep k P)).map C.f).hom.toLinearMap)
  let gP : C.X₂ →ₗ[k] C.X₃ := (((forget₂ (FDRep k P) (Rep k P)).map C.g).hom.toLinearMap)
  have hExact : Function.Exact fP gP := by
    simpa [F, fP, gP] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (C.map F)).mp hCF.exact
  have hInj : Function.Injective fP := by
    simpa [F, fP] using hCF.moduleCat_injective_f
  have hSurj : Function.Surjective gP := by
    simpa [F, gP] using hCF.moduleCat_surjective_g
  -- Tensoring with the flat module `U.V` preserves injectivity, exactness, surjectivity.
  have hInjT : Function.Injective (LinearMap.lTensor U.V fP) :=
    Module.Flat.lTensor_preserves_injective_linearMap fP hInj
  have hExactT : Function.Exact (LinearMap.lTensor U.V fP) (LinearMap.lTensor U.V gP) :=
    Module.Flat.lTensor_exact U.V hExact
  have hSurjT : Function.Surjective (LinearMap.lTensor U.V gP) :=
    LinearMap.lTensor_surjective U.V hSurj
  -- Reflect short exactness from `ModuleCat k` back through `Rep` to `FDRep`.
  let TRep : ShortComplex (Rep k (S × P)) :=
    (extTensorLeft_shortComplex_local (k := k) (S := S) (P := P) U C).map
      (forget₂ (FDRep k (S × P)) (Rep k (S × P)))
  have hRepMap : (TRep.map (forget₂ (Rep k (S × P)) (ModuleCat k))).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
          (TRep.map (forget₂ (Rep k (S × P)) (ModuleCat k)))).2 <| by
            simpa [TRep, extTensorLeft_shortComplex_local, extTensorLeft_map_local,
              fP, gP] using hExactT
    · rw [ModuleCat.mono_iff_injective]
      simpa [TRep, extTensorLeft_shortComplex_local, extTensorLeft_map_local, fP] using hInjT
    · rw [ModuleCat.epi_iff_surjective]
      simpa [TRep, extTensorLeft_shortComplex_local, extTensorLeft_map_local, gP] using hSurjT
  have hRepShort : TRep.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := TRep) (F := forget₂ (Rep k (S × P)) (ModuleCat k))).1 hRepMap
  have hTRep :
      ((extTensorLeft_shortComplex_local (k := k) (S := S) (P := P) U C).map
        (forget₂ (FDRep k (S × P)) (Rep k (S × P)))).ShortExact := by
    simpa [TRep] using hRepShort
  exact
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := extTensorLeft_shortComplex_local (k := k) (S := S) (P := P) U C)
      (F := forget₂ (FDRep k (S × P)) (Rep k (S × P)))).1 hTRep

/-- Helper for Theorem 16-16.1-5: external-tensoring on the left with `U` preserves the defining
Grothendieck relations. -/
theorem extTensorLeftRelations_le_lift_ker {S P : Type u} [Group S] [Group P] (U : FDRep k S) :
    finiteRepGrothendieckRelations k P ≤
      (extTensorLeftLift (k := k) (S := S) (P := P) U).ker := by
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨C, hC⟩, rfl⟩
  have hExt :
      (extTensorLeft_shortComplex_local (k := k) (S := S) (P := P) U C).ShortExact :=
    extTensorLeft_shortExact_local (k := k) (S := S) (P := P) U C hC
  have hRelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := S × P)
      (extTensorLeft_shortComplex_local (k := k) (S := S) (P := P) U C) hExt
  change
    extTensorLeftLift (k := k) (S := S) (P := P) U
        (FreeAbelianGroup.of C.X₂ - FreeAbelianGroup.of C.X₁ - FreeAbelianGroup.of C.X₃) = 0
  change
    [FDRep.of (U.ρ ⊠ C.X₂.ρ)]₀ -
        [FDRep.of (U.ρ ⊠ C.X₁.ρ)]₀ -
        [FDRep.of (U.ρ ⊠ C.X₃.ρ)]₀ = 0
  calc
    [FDRep.of (U.ρ ⊠ C.X₂.ρ)]₀ -
        [FDRep.of (U.ρ ⊠ C.X₁.ρ)]₀ -
        [FDRep.of (U.ρ ⊠ C.X₃.ρ)]₀ =
      ([FDRep.of (U.ρ ⊠ C.X₁.ρ)]₀ + [FDRep.of (U.ρ ⊠ C.X₃.ρ)]₀) -
        [FDRep.of (U.ρ ⊠ C.X₁.ρ)]₀ -
        [FDRep.of (U.ρ ⊠ C.X₃.ρ)]₀ := by rw [hRelation]
    _ = 0 := by abel

/-- External-tensoring on the left with a fixed finite-dim `S`-rep `U` is additive on classes. -/
def extTensorLeft {S P : Type u} [Group S] [Group P] (U : FDRep k S) :
    R₀[k](P) →+ R₀[k](S × P) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k P)
    (extTensorLeftLift (k := k) (S := S) (P := P) U)
    (extTensorLeftRelations_le_lift_ker (k := k) (S := S) (P := P) U)

@[simp] theorem extTensorLeft_apply_class {S P : Type u} [Group S] [Group P]
    (U : FDRep k S) (W : FDRep k P) :
    extTensorLeft U [W]₀ = [FDRep.of (U.ρ ⊠ W.ρ)]₀ := by
  rfl

/-! ### (C) unit collapse -/

/-- Helper for Theorem 16-16.1-5: the class of `U ⊠ 𝟙` collapses to the class of the left
inflation `U.ρ.comp (MonoidHom.fst S P)`, via the right-unitor `U.V ⊗ k ≃ U.V`. -/
theorem externalTensor_unit_class_eq_comp_fst {S P : Type u} [Group S] [Group P]
    (U : FDRep k S) :
    [FDRep.of (U.ρ ⊠ (𝟙_ (FDRep k P)).ρ)]₀ =
      [FDRep.of (U.ρ.comp (MonoidHom.fst S P))]₀ := by
  -- The monoidal unit's representation is the trivial 1-dim rep on `k`, so `U ⊠ 𝟙` is defeq to
  -- `U.ρ ⊠ trivial k P k`, whose carrier is `U.V ⊗ k`.
  have hunit : (𝟙_ (FDRep k P)).ρ = Representation.trivial k P k := rfl
  -- Build a representation equivalence via the right-unitor `U.V ⊗ k ≃ U.V`.
  have hequiv :
      (U.ρ ⊠ (Representation.trivial k P k)).Equiv (U.ρ.comp (MonoidHom.fst S P)) := by
    refine Representation.Equiv.mk
      (ρ := U.ρ ⊠ (Representation.trivial k P k))
      (σ := U.ρ.comp (MonoidHom.fst S P)) (_root_.TensorProduct.rid k U.V) ?_
    intro sp
    apply TensorProduct.ext'
    intro x c
    -- Evaluate on a pure tensor `x ⊗ c`; both sides reduce to `c • (U.ρ sp.1 x)`.
    simp only [LinearMap.coe_comp, Function.comp_apply, tprod_apply,
      TensorProduct.map_tmul, MonoidHom.coe_fst, MonoidHom.coe_snd,
      trivial_apply, MonoidHom.comp_apply]
    -- `rid (m ⊗ₜ c) = c • m` definitionally; the action is `k`-linear.
    change c • (U.ρ sp.1 x) = U.ρ sp.1 (c • x)
    rw [map_smul]
  exact finiteRepGrothendieckClass_eq_of_representationEquiv (G := S × P)
    (U.ρ ⊠ (Representation.trivial k P k)) (U.ρ.comp (MonoidHom.fst S P)) hequiv

end Representation
