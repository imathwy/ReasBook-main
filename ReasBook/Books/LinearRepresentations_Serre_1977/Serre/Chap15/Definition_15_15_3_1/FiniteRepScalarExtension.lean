import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_2
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import Mathlib.RingTheory.TensorProduct.Finite

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra TensorProduct
open scoped Representation

universe u

namespace Representation

section FiniteRepScalarExtension

variable {K : Type u} [Field K]
variable {K' : Type u} [Field K'] [Algebra K K']
variable {G : Type u} [Group G]
variable (K K' G)

/- Domain-style sampling for this owner:
* primary domain: scalar extension of finite-dimensional representations and the induced maps on
  Serre's Grothendieck groups `R₀[K](G)`;
* relevant owner declarations inspected in this domain:
  `Representation.scalarExtension`,
  `FDRep.scalarExtension`,
  `cartanHom`,
  `projectiveGrothendieckScalarExtensionHom`;
* best owner abstraction: the additive map on `R₀[K](G)` induced by the bundled owner
  `FDRep.scalarExtension`.

Primitive data vs derived API:
* primitive data: scalar extension of actual finite-dimensional `K[G]`-representations;
* derived API: the descended quotient map on Grothendieck groups and its evaluation on generator
  classes.
This owner belongs with the Chapter `15` scalar-extension maps, rather than in later Chapter `16`
bridge theorems that merely reuse it.
-/

/-- The additive lift of scalar extension from finite-dimensional `K[G]`-representations to the
free abelian group on their isomorphism classes. -/
private abbrev finiteRepGrothendieckScalarExtensionLift :
    FreeAbelianGroup (FDRep K G) →+ R₀[K'](G) :=
  FreeAbelianGroup.lift fun V ↦ [FDRep.scalarExtension V]₀

/-- Helper for Definition 15-15.3-1: scalar extension sends a morphism of finite-dimensional
`K`-representations to the tensor-extended morphism of the scalar-extended owners. -/
private theorem finiteRep_scalarExtension_repMap_isIntertwining
    {V W : FDRep K G} (f : V ⟶ W) :
    ∀ g : G,
      ((forget₂ (FDRep K G) (Rep K G)).map f).hom.toLinearMap.baseChange K' ∘ₗ
          (FDRep.scalarExtension (k := K') V).ρ g =
        (FDRep.scalarExtension (k := K') W).ρ g ∘ₗ
          ((forget₂ (FDRep K G) (Rep K G)).map f).hom.toLinearMap.baseChange K' := by
  intro g
  ext x
  -- Extensionality for base-changed linear maps reduces the goal to the canonical tensor
  -- generators `1 ⊗ x`.
  simpa [FDRep.scalarExtension, Representation.scalarExtension, LinearMap.baseChange_tmul] using
    congrArg (fun y ↦ (1 : K') ⊗ₜ[K] y)
      (Rep.hom_comm_apply ((forget₂ (FDRep K G) (Rep K G)).map f) g x)

private noncomputable abbrev finiteRep_scalarExtension_map
    {V W : FDRep K G} (f : V ⟶ W) :
    FDRep.scalarExtension (k := K') V ⟶ FDRep.scalarExtension (k := K') W :=
  (FDRep.forget₂HomLinearEquiv (FDRep.scalarExtension (k := K') V)
      (FDRep.scalarExtension (k := K') W))
    (Rep.ofHom
      ⟨((forget₂ (FDRep K G) (Rep K G)).map f).hom.toLinearMap.baseChange K',
        finiteRep_scalarExtension_repMap_isIntertwining (K := K) (K' := K') (G := G) f⟩)

/-- Helper for Definition 15-15.3-1: forgetting a scalar-extended `FDRep` morphism to `Rep K' G`
recovers the tensor-extended `Rep` morphism. -/
private theorem finiteRep_scalarExtension_map_forget
    {V W : FDRep K G} (f : V ⟶ W) :
    (forget₂ (FDRep K' G) (Rep K' G)).map
        (finiteRep_scalarExtension_map (K := K) (K' := K') (G := G) f) =
      Rep.ofHom
        ⟨((forget₂ (FDRep K G) (Rep K G)).map f).hom.toLinearMap.baseChange K', by
          exact finiteRep_scalarExtension_repMap_isIntertwining
            (K := K) (K' := K') (G := G) f⟩ := by
  -- Forgetting through `FDRep.forget₂HomLinearEquiv` recovers the defining `Rep` morphism.
  change
    (FDRep.forget₂HomLinearEquiv (FDRep.scalarExtension (k := K') V)
        (FDRep.scalarExtension (k := K') W)).symm
      ((FDRep.forget₂HomLinearEquiv (FDRep.scalarExtension (k := K') V)
          (FDRep.scalarExtension (k := K') W))
        (Rep.ofHom
          ⟨((forget₂ (FDRep K G) (Rep K G)).map f).hom.toLinearMap.baseChange K',
            finiteRep_scalarExtension_repMap_isIntertwining
              (K := K) (K' := K') (G := G) f⟩)) =
      Rep.ofHom
        ⟨((forget₂ (FDRep K G) (Rep K G)).map f).hom.toLinearMap.baseChange K',
          finiteRep_scalarExtension_repMap_isIntertwining
            (K := K) (K' := K') (G := G) f⟩
  exact
    (FDRep.forget₂HomLinearEquiv (FDRep.scalarExtension (k := K') V)
      (FDRep.scalarExtension (k := K') W)).left_inv _

/-- Helper for Definition 15-15.3-1: scalar extension carries a short complex of
finite-dimensional `K`-representations to the short complex obtained by tensoring both maps with
`K'`. -/
private theorem finiteRep_scalarExtension_shortComplex_zero
    (S : ShortComplex (FDRep K G)) :
    finiteRep_scalarExtension_map (K := K) (K' := K') (G := G) S.f ≫
        finiteRep_scalarExtension_map (K := K) (K' := K') (G := G) S.g = 0 := by
  apply (forget₂ (FDRep K' G) (Rep K' G)).map_injective
  rw [Functor.map_comp]
  rw [finiteRep_scalarExtension_map_forget (K := K) (K' := K') (G := G) S.f]
  rw [finiteRep_scalarExtension_map_forget (K := K) (K' := K') (G := G) S.g]
  ext x
  let F : FDRep K G ⥤ Rep K G := forget₂ (FDRep K G) (Rep K G)
  have hzeroRepHom : F.map S.f ≫ F.map S.g = 0 := by
    rw [← F.map_comp, S.zero, F.map_zero]
  have hzeroRep :
      (F.map S.g).hom.toLinearMap ∘ₗ (F.map S.f).hom.toLinearMap = 0 := by
    simpa using congrArg (fun m ↦ m.hom.toLinearMap) hzeroRepHom
  have hzeroBase :
      ((F.map S.g).hom.toLinearMap ∘ₗ (F.map S.f).hom.toLinearMap).baseChange K' = 0 := by
    have hzeroBase' :=
      congrArg (fun φ : S.X₁.V →ₗ[K] S.X₃.V ↦ φ.baseChange K') hzeroRep
    exact hzeroBase'.trans (LinearMap.baseChange_zero (A := K') (M := S.X₁.V) (N := S.X₃.V))
  have hzeroBaseComp :
      (F.map S.g).hom.toLinearMap.baseChange K' ∘ₗ
          (F.map S.f).hom.toLinearMap.baseChange K' = 0 := by
    simpa [LinearMap.baseChange_comp] using hzeroBase
  exact LinearMap.congr_fun hzeroBaseComp x

/-- Helper for Definition 15-15.3-1: the scalar extension of a short complex is the canonical
short complex on the scalar-extended `FDRep` owners. -/
private noncomputable abbrev finiteRep_scalarExtension_shortComplex
    (S : ShortComplex (FDRep K G)) :
    ShortComplex (FDRep K' G) :=
  ShortComplex.mk
    (finiteRep_scalarExtension_map (K := K) (K' := K') (G := G) S.f)
    (finiteRep_scalarExtension_map (K := K) (K' := K') (G := G) S.g)
    (finiteRep_scalarExtension_shortComplex_zero (K := K) (K' := K') (G := G) S)

/-- Helper for Definition 15-15.3-1: scalar extension preserves short exact sequences of
finite-dimensional representations. -/
private theorem finiteRep_scalarExtension_shortExact
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    (finiteRep_scalarExtension_shortComplex (K := K) (K' := K') (G := G) S).ShortExact := by
  let F : FDRep K G ⥤ ModuleCat K :=
    (forget₂ (FDRep K G) (Rep K G)) ⋙ (forget₂ (Rep K G) (ModuleCat K))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat K` keeps the original short exact sequence.
    simpa [F] using hS.map_of_exact F
  let fRep : IntertwiningMap S.X₁.ρ S.X₂.ρ := ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom
  let gRep : IntertwiningMap S.X₂.ρ S.X₃.ρ := ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom
  let f : S.X₁.V →ₗ[K] S.X₂.V := fRep.toLinearMap
  let g : S.X₂.V →ₗ[K] S.X₃.V := gRep.toLinearMap
  have hExact : Function.Exact f g := by
    -- In `ModuleCat K`, short exactness is exactness of the underlying linear maps.
    simpa [F, f, g, fRep, gRep] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hInj : Function.Injective f := by
    -- The left map of a short exact sequence is injective after forgetting to modules.
    simpa [F, f, fRep] using hSF.moduleCat_injective_f
  have hSurj : Function.Surjective g := by
    -- The right map of a short exact sequence is surjective after the same forgetful step.
    simpa [F, g, gRep] using hSF.moduleCat_surjective_g
  have hExactBase : Function.Exact (f.baseChange K') (g.baseChange K') := by
    -- Scalar extension is exact because `K'` is flat over the field `K`.
    simpa [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_exact (M := K') hExact)
  have hInjBase : Function.Injective (f.baseChange K') := by
    -- Flatness also preserves injectivity of the left map.
    simpa [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := K') f hInj)
  have hSurjBase : Function.Surjective (g.baseChange K') := by
    -- Tensoring with `K'` preserves surjectivity of the right map.
    simpa [LinearMap.baseChange_eq_ltensor] using
      (LinearMap.lTensor_surjective (Q := K') hSurj)
  let SRep : ShortComplex (Rep K' G) :=
    (finiteRep_scalarExtension_shortComplex (K := K) (K' := K') (G := G) S).map
      (forget₂ (FDRep K' G) (Rep K' G))
  have hRepMap : (SRep.map (forget₂ (Rep K' G) (ModuleCat K'))).ShortExact := by
    -- On the underlying `K'`-modules, the scalar-extended sequence is exactly the tensorized
    -- short exact sequence of linear maps.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
          (SRep.map (forget₂ (Rep K' G) (ModuleCat K')))).2 <|
          by
            simpa [SRep, finiteRep_scalarExtension_shortComplex,
              finiteRep_scalarExtension_map_forget, f, g, fRep, gRep] using hExactBase
    · rw [ModuleCat.mono_iff_injective]
      simpa [SRep, finiteRep_scalarExtension_shortComplex, finiteRep_scalarExtension_map_forget,
        f, fRep] using hInjBase
    · rw [ModuleCat.epi_iff_surjective]
      simpa [SRep, finiteRep_scalarExtension_shortComplex, finiteRep_scalarExtension_map_forget,
        g, gRep] using hSurjBase
  have hRepShort : SRep.ShortExact := by
    -- Reflect short exactness from `ModuleCat K'` back to `Rep K' G`.
    exact
      (CategoryTheory.ShortExact.shortExact_map_iff
        (S := SRep) (F := forget₂ (Rep K' G) (ModuleCat K'))).1 hRepMap
  -- Reflect short exactness one last time from `Rep K' G` back to `FDRep K' G`.
  exact
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := finiteRep_scalarExtension_shortComplex (K := K) (K' := K') (G := G) S)
      (F := forget₂ (FDRep K' G) (Rep K' G))).1 hRepShort

-- Proof sketch: scalar extension is exact, so the defining short-exact-sequence generators of
-- `finiteRepGrothendieckRelations K G` map to zero under
-- `finiteRepGrothendieckScalarExtensionLift`.
private theorem finiteRepGrothendieckRelations_le_scalarExtensionLift_ker :
    finiteRepGrothendieckRelations K G ≤
      (finiteRepGrothendieckScalarExtensionLift K K' G).ker := by
  refine (AddSubgroup.closure_le _).2 ?_
  intro x hx
  rcases hx with ⟨⟨S, hS⟩, rfl⟩
  have hScalar :
      (finiteRep_scalarExtension_shortComplex (K := K) (K' := K') (G := G) S).ShortExact :=
    finiteRep_scalarExtension_shortExact (K := K) (K' := K') (G := G) S hS
  have hRelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right
      (L := K') (G := G)
      (finiteRep_scalarExtension_shortComplex (K := K) (K' := K') (G := G) S) hScalar
  -- Evaluate the free lift on the defining generator and rewrite by the scalar-extended
  -- Grothendieck relation.
  change
    finiteRepGrothendieckScalarExtensionLift K K' G
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  change
    [FDRep.scalarExtension (k := K') S.X₂]₀ -
        [FDRep.scalarExtension (k := K') S.X₁]₀ -
        [FDRep.scalarExtension (k := K') S.X₃]₀ = 0
  calc
    [FDRep.scalarExtension (k := K') S.X₂]₀ -
        [FDRep.scalarExtension (k := K') S.X₁]₀ -
        [FDRep.scalarExtension (k := K') S.X₃]₀ =
      ([FDRep.scalarExtension (k := K') S.X₁]₀ +
          [FDRep.scalarExtension (k := K') S.X₃]₀) -
        [FDRep.scalarExtension (k := K') S.X₁]₀ -
        [FDRep.scalarExtension (k := K') S.X₃]₀ := by
          rw [hRelation]
    _ = 0 := by
          abel

/-- Scalar extension along `K → K'` induces a homomorphism `R_K(G) → R_K'(G)` on Grothendieck
groups. -/
def finiteRepGrothendieckScalarExtensionHom :
    R₀[K](G) →+ R₀[K'](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations K G)
    (finiteRepGrothendieckScalarExtensionLift K K' G)
    (finiteRepGrothendieckRelations_le_scalarExtensionLift_ker K K' G)

-- Proof sketch: `finiteRepGrothendieckScalarExtensionHom` is the quotient lift of
-- `finiteRepGrothendieckScalarExtensionLift`, so on a generator it returns the class of the
-- scalar-extended finite-dimensional representation.
/-- On a generator class, scalar extension sends `[V]` in `R_K(G)` to the class of the
scalar-extended representation in `R_K'(G)`. -/
@[simp] theorem finiteRepGrothendieckScalarExtensionHom_class_eq
    (V : FDRep K G) :
    finiteRepGrothendieckScalarExtensionHom K K' G [V]₀ =
      ([FDRep.scalarExtension V]₀ : R₀[K'](G)) := rfl

section FiniteRepRestrictScalars

variable [FiniteDimensional K K']

namespace FDRep

/-- A finite-dimensional representation over `K'`, viewed as a finite-dimensional representation
over `K` by restriction of scalars. -/
abbrev restrictScalars (V : FDRep K' G) : FDRep K G :=
  letI : Module K V.V := Module.compHom V.V (algebraMap K K')
  letI : IsScalarTower K K' V.V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Finite K V := Module.Finite.trans K' V
  FDRep.of (Representation.restrictScalars K V.ρ)

end FDRep

/-- Helper for restriction of scalars: the underlying `K'`-linear morphism, viewed as a
`K`-linear map after restriction of scalars. -/
private abbrev finiteRep_restrictScalars_linearMap
    {V W : FDRep K' G} (f : V ⟶ W) :
    (FDRep.restrictScalars (K := K) (K' := K') (G := G) V).V →ₗ[K]
      (FDRep.restrictScalars (K := K) (K' := K') (G := G) W).V :=
  letI : Module K V.V := Module.compHom V.V (algebraMap K K')
  letI : Module K W.V := Module.compHom W.V (algebraMap K K')
  let lK' : V →ₗ[K'] W := ((forget₂ (FDRep K' G) (Rep K' G)).map f).hom.toLinearMap
  { toFun := fun x ↦ lK' x
    map_add' := fun x y ↦ lK'.map_add x y
    map_smul' := fun a x ↦ by
      change lK' ((algebraMap K K' a) • x) = (algebraMap K K' a) • lK' x
      exact lK'.map_smul (algebraMap K K' a) x }

/-- Helper for restriction of scalars: morphisms of finite-dimensional `K'`-representations
restrict to morphisms of the restricted finite-dimensional `K`-representations. -/
private abbrev finiteRep_restrictScalars_map
    {V W : FDRep K' G} (f : V ⟶ W) :
    FDRep.restrictScalars (K := K) (K' := K') (G := G) V ⟶
    FDRep.restrictScalars (K := K) (K' := K') (G := G) W :=
  (FDRep.forget₂HomLinearEquiv _ _)
    (Rep.ofHom
      ⟨finiteRep_restrictScalars_linearMap K K' G f,
        by
          intro g
          ext x
          simpa [FDRep.restrictScalars, finiteRep_restrictScalars_linearMap,
            Representation.restrictScalars_apply] using
            Rep.hom_comm_apply ((forget₂ (FDRep K' G) (Rep K' G)).map f) g x⟩)

/-- Helper for restriction of scalars: after forgetting to `Rep`, the restricted morphism is the
original intertwining map with scalars restricted. -/
private theorem finiteRep_restrictScalars_map_forget
    {V W : FDRep K' G} (f : V ⟶ W) :
    (forget₂ (FDRep K G) (Rep K G)).map
        (finiteRep_restrictScalars_map (K := K) (K' := K') (G := G) f) =
      Rep.ofHom
        ⟨finiteRep_restrictScalars_linearMap K K' G f,
          by
            intro g
            ext x
            simpa [FDRep.restrictScalars, finiteRep_restrictScalars_linearMap,
              Representation.restrictScalars_apply] using
              Rep.hom_comm_apply ((forget₂ (FDRep K' G) (Rep K' G)).map f) g x⟩ := by
  change (FDRep.forget₂HomLinearEquiv
      (FDRep.restrictScalars (K := K) (K' := K') (G := G) V)
      (FDRep.restrictScalars (K := K) (K' := K') (G := G) W)).symm
    ((FDRep.forget₂HomLinearEquiv
      (FDRep.restrictScalars (K := K) (K' := K') (G := G) V)
      (FDRep.restrictScalars (K := K) (K' := K') (G := G) W))
      (Rep.ofHom
        ⟨finiteRep_restrictScalars_linearMap K K' G f,
          by
            intro g
            ext x
            simpa [FDRep.restrictScalars, finiteRep_restrictScalars_linearMap,
              Representation.restrictScalars_apply] using
              Rep.hom_comm_apply ((forget₂ (FDRep K' G) (Rep K' G)).map f) g x⟩)) = _
  exact (FDRep.forget₂HomLinearEquiv _ _).left_inv _

/-- Helper for restriction of scalars: termwise restriction of a short complex is still a short
complex. -/
private theorem finiteRep_restrictScalars_shortComplex_zero
    (S : ShortComplex (FDRep K' G)) :
    finiteRep_restrictScalars_map (K := K) (K' := K') (G := G) S.f ≫
        finiteRep_restrictScalars_map (K := K) (K' := K') (G := G) S.g = 0 := by
  apply (forget₂ (FDRep K G) (Rep K G)).map_injective
  rw [Functor.map_comp]
  rw [finiteRep_restrictScalars_map_forget (K := K) (K' := K') (G := G) S.f]
  rw [finiteRep_restrictScalars_map_forget (K := K) (K' := K') (G := G) S.g]
  ext x
  let FK' : FDRep K' G ⥤ Rep K' G := forget₂ (FDRep K' G) (Rep K' G)
  have hzeroRepHom : FK'.map S.f ≫ FK'.map S.g = 0 := by
    rw [← FK'.map_comp, S.zero, FK'.map_zero]
  have hzeroRep :
      (FK'.map S.g).hom.toLinearMap ∘ₗ (FK'.map S.f).hom.toLinearMap = 0 := by
    simpa using congrArg (fun m ↦ m.hom.toLinearMap) hzeroRepHom
  simpa [FDRep.restrictScalars, finiteRep_restrictScalars_linearMap] using
    LinearMap.congr_fun hzeroRep x

/-- Helper for restriction of scalars: the short complex obtained by restricting each term and
map of a finite-representation short complex. -/
private abbrev finiteRep_restrictScalars_shortComplex
    (S : ShortComplex (FDRep K' G)) : ShortComplex (FDRep K G) :=
  ShortComplex.mk
    (finiteRep_restrictScalars_map (K := K) (K' := K') (G := G) S.f)
    (finiteRep_restrictScalars_map (K := K) (K' := K') (G := G) S.g)
    (finiteRep_restrictScalars_shortComplex_zero (K := K) (K' := K') (G := G) S)

/-- Restriction of scalars preserves short exact sequences of finite-dimensional
representations. -/
private theorem finiteRep_restrictScalars_shortExact
    (S : ShortComplex (FDRep K' G)) (hS : S.ShortExact) :
    (finiteRep_restrictScalars_shortComplex (K := K) (K' := K') (G := G) S).ShortExact := by
  let FK' : FDRep K' G ⥤ ModuleCat K' :=
    (forget₂ (FDRep K' G) (Rep K' G)) ⋙ (forget₂ (Rep K' G) (ModuleCat K'))
  have hSFK' : (S.map FK').ShortExact := by
    simpa [FK'] using hS.map_of_exact FK'
  let fK' : S.X₁.V →ₗ[K'] S.X₂.V :=
    ((forget₂ (FDRep K' G) (Rep K' G)).map S.f).hom.toLinearMap
  let gK' : S.X₂.V →ₗ[K'] S.X₃.V :=
    ((forget₂ (FDRep K' G) (Rep K' G)).map S.g).hom.toLinearMap
  have hExactK' : Function.Exact fK' gK' := by
    simpa [FK', fK', gK'] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map FK')).mp hSFK'.exact
  have hInjK' : Function.Injective fK' := by
    simpa [FK', fK'] using hSFK'.moduleCat_injective_f
  have hSurjK' : Function.Surjective gK' := by
    simpa [FK', gK'] using hSFK'.moduleCat_surjective_g
  letI : Module K S.X₁.V := Module.compHom S.X₁.V (algebraMap K K')
  letI : Module K S.X₂.V := Module.compHom S.X₂.V (algebraMap K K')
  letI : Module K S.X₃.V := Module.compHom S.X₃.V (algebraMap K K')
  letI : IsScalarTower K K' S.X₁.V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower K K' S.X₂.V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower K K' S.X₃.V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hExactK : Function.Exact (fK'.restrictScalars K) (gK'.restrictScalars K) := by
    intro x
    exact hExactK' x
  have hInjK : Function.Injective (fK'.restrictScalars K) := hInjK'
  have hSurjK : Function.Surjective (gK'.restrictScalars K) := hSurjK'
  let SKRep : ShortComplex (Rep K G) :=
    (finiteRep_restrictScalars_shortComplex (K := K) (K' := K') (G := G) S).map
      (forget₂ (FDRep K G) (Rep K G))
  have hRepMap : (SKRep.map (forget₂ (Rep K G) (ModuleCat K))).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
          (SKRep.map (forget₂ (Rep K G) (ModuleCat K)))).2 <|
          by
            simpa [SKRep, finiteRep_restrictScalars_shortComplex,
              finiteRep_restrictScalars_map_forget, fK', gK'] using hExactK
    · rw [ModuleCat.mono_iff_injective]
      simpa [SKRep, finiteRep_restrictScalars_shortComplex,
        finiteRep_restrictScalars_map_forget, fK'] using hInjK
    · rw [ModuleCat.epi_iff_surjective]
      simpa [SKRep, finiteRep_restrictScalars_shortComplex,
        finiteRep_restrictScalars_map_forget, gK'] using hSurjK
  have hRepShort : SKRep.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := SKRep) (F := forget₂ (Rep K G) (ModuleCat K))).1 hRepMap
  exact
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := finiteRep_restrictScalars_shortComplex (K := K) (K' := K') (G := G) S)
      (F := forget₂ (FDRep K G) (Rep K G))).1 hRepShort

/-- The additive lift sending a `K'`-representation to its restriction-of-scalars class over
`K`. -/
private abbrev finiteRepGrothendieckRestrictScalarsLift :
    FreeAbelianGroup (FDRep K' G) →+ R₀[K](G) :=
  FreeAbelianGroup.lift fun V ↦
    [FDRep.restrictScalars (K := K) (K' := K') (G := G) V]₀

/-- Restriction of scalars kills the defining short-exact relations of the finite-representation
Grothendieck group. -/
private theorem finiteRepGrothendieckRelations_le_restrictScalarsLift_ker :
    finiteRepGrothendieckRelations K' G ≤
      (finiteRepGrothendieckRestrictScalarsLift (K := K) (K' := K') (G := G)).ker := by
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₂]₀ -
      [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₁]₀ -
      [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₃]₀ = 0
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := K) (G := G)
      (finiteRep_restrictScalars_shortComplex (K := K) (K' := K') (G := G) S)
      (finiteRep_restrictScalars_shortExact (K := K) (K' := K') (G := G) S hS)
  have hrelation' :
      [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₂]₀ =
        ([FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₁]₀ : R₀[K](G)) +
          [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₃]₀ := by
    simpa [finiteRep_restrictScalars_shortComplex] using hrelation
  calc
    [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₂]₀ -
        [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₁]₀ -
        [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₃]₀ =
      ([FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₁]₀ +
          [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₃]₀) -
        [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₁]₀ -
        [FDRep.restrictScalars (K := K) (K' := K') (G := G) S.X₃]₀ := by
          rw [hrelation']
    _ = 0 := by
          abel

/-- Restriction of scalars induces an additive homomorphism `R₀[K'](G) → R₀[K](G)`. -/
def finiteRepGrothendieckRestrictScalarsHom :
    R₀[K'](G) →+ R₀[K](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations K' G)
    (finiteRepGrothendieckRestrictScalarsLift (K := K) (K' := K') (G := G))
    (finiteRepGrothendieckRelations_le_restrictScalarsLift_ker
      (K := K) (K' := K') (G := G))

/-- On generator classes, restriction of scalars sends a `K'`-representation to the class of the
restricted finite-dimensional representation over `K`. -/
@[simp] theorem finiteRepGrothendieckRestrictScalarsHom_class_eq
    (V : FDRep K' G) :
    finiteRepGrothendieckRestrictScalarsHom K K' G [V]₀ =
      ([FDRep.restrictScalars (K := K) (K' := K') (G := G) V]₀ : R₀[K](G)) := rfl

/-- Helper for restriction after scalar extension: the coordinatewise action on `n` copies of a
finite-dimensional representation. -/
private def repFinPiCopies (n : ℕ) (V : FDRep K G) :
    Representation K G (Fin n → V.V) where
  toFun g :=
    { toFun := fun x i ↦ V.ρ g (x i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro a x
        ext i
        simp }
  map_one' := by
    ext x i
    simp
  map_mul' := by
    intro g h
    ext x i
    simp [map_mul]

/-- Helper for restriction after scalar extension: the finite representation made of `n`
coordinate copies of `V`. -/
private abbrev fdRepFinPiCopies (n : ℕ) (V : FDRep K G) : FDRep K G :=
  letI : Module.Finite K (Fin n → V.V) := inferInstance
  FDRep.of (repFinPiCopies (K := K) (G := G) n V)

private noncomputable def fdRepIsoOfRho (V : FDRep K G) : V ≅ FDRep.of V.ρ :=
  Action.mkIso (Iso.refl _) fun g ↦ by
    ext x
    rfl

/-- Helper for restriction after scalar extension: a binary product representation has
Grothendieck class equal to the sum of the classes of the two factors. -/
private theorem finiteRepGrothendieckClass_prod_eq_add_for_scalarRestriction
    (E F : FDRep K G) :
    [FDRep.of (Representation.prod E.ρ F.ρ)]₀ =
      ([E]₀ : R₀[K](G)) + [F]₀ := by
  let P : FDRep K G := FDRep.of (Representation.prod E.ρ F.ρ)
  let fRep :
      ((forget₂ (FDRep K G) (Rep K G)).obj E ⟶
        (forget₂ (FDRep K G) (Rep K G)).obj P) :=
    Rep.ofHom ⟨LinearMap.inl K E.V F.V, by
      intro g
      ext x
      change
        LinearMap.inl K E.V F.V (E.ρ g x) =
          ((E.ρ g).prodMap (F.ρ g)) (LinearMap.inl K E.V F.V x)
      simp [LinearMap.prodMap]⟩
  let gRep :
      ((forget₂ (FDRep K G) (Rep K G)).obj P ⟶
        (forget₂ (FDRep K G) (Rep K G)).obj F) :=
    Rep.ofHom ⟨LinearMap.snd K E.V F.V, by
      intro g
      ext x <;> rfl⟩
  let f : E ⟶ P := (FDRep.forget₂HomLinearEquiv E P) fRep
  let g : P ⟶ F := (FDRep.forget₂HomLinearEquiv P F) gRep
  let S : ShortComplex (FDRep K G) := ShortComplex.mk f g (by
    apply (forget₂ (FDRep K G) (Rep K G)).map_injective
    ext x <;> rfl)
  let SRep : ShortComplex (Rep K G) := ShortComplex.mk fRep gRep (by
    ext x <;> rfl)
  have hRepMap : (SRep.map (forget₂ (Rep K G) (ModuleCat K))).ShortExact := by
    let SMod : ShortComplex (ModuleCat K) :=
      CategoryTheory.ShortComplex.moduleCatMk
        (LinearMap.inl K E.V F.V)
        (LinearMap.snd K E.V F.V)
        (by ext x <;> rfl)
    have hSMod : SMod.ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
      · exact CategoryTheory.ShortComplex.Exact.moduleCat_of_range_eq_ker
          (ModuleCat.ofHom (LinearMap.inl K E.V F.V))
          (ModuleCat.ofHom (LinearMap.snd K E.V F.V))
          (by
            ext x
            constructor
            · rintro ⟨y, rfl⟩
              simp
            · intro hx
              refine ⟨x.1, ?_⟩
              ext
              · rfl
              · simpa using hx.symm)
      · exact (ModuleCat.mono_iff_injective _).mpr fun x y h ↦ by
          exact congrArg Prod.fst h
      · exact (ModuleCat.epi_iff_surjective _).mpr fun z ↦ ⟨(0, z), rfl⟩
    simpa [SRep, SMod, fRep, gRep] using hSMod
  have hRepShort : SRep.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := SRep) (F := forget₂ (Rep K G) (ModuleCat K))).1 hRepMap
  have hRep : (S.map (forget₂ (FDRep K G) (Rep K G))).ShortExact := by
    simpa [S, SRep, f, g, fRep, gRep] using hRepShort
  have hS : S.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := S) (F := forget₂ (FDRep K G) (Rep K G))).1 hRep
  simpa [S, P] using finiteRepGrothendieckClass_middle_eq_left_add_right
    (L := K) (G := G) S hS

/-- Helper for restriction after scalar extension: one coordinate copy is the original
representation. -/
private theorem fdRepFinPiCopies_one_class (V : FDRep K G) :
    ([fdRepFinPiCopies (K := K) (G := G) 1 V]₀ : R₀[K](G)) = [V]₀ := by
  let e : (repFinPiCopies (K := K) (G := G) 1 V).Equiv V.ρ :=
    Representation.Equiv.mk (LinearEquiv.funUnique (Fin 1) K V.V) (by
      intro g
      apply LinearMap.ext
      intro x
      rfl)
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G)
    ⟨e.toFDRepIso.trans (fdRepIsoOfRho (K := K) (G := G) V).symm⟩

/-- Helper for restriction after scalar extension: `n+1` coordinate copies split as the product
of one copy and `n` remaining copies. -/
private theorem fdRepFinPiCopies_succ_nonempty_iso_prod
    (n : ℕ) (V : FDRep K G) :
    Nonempty
      (fdRepFinPiCopies (K := K) (G := G) (n + 1) V ≅
        FDRep.of (Representation.prod V.ρ (repFinPiCopies (K := K) (G := G) n V))) := by
  let e :
      (Representation.prod V.ρ (repFinPiCopies (K := K) (G := G) n V)).Equiv
        (repFinPiCopies (K := K) (G := G) (n + 1) V) :=
    Representation.Equiv.mk (Fin.consLinearEquiv K (fun _ : Fin (n + 1) ↦ V.V)) (by
      intro g
      apply LinearMap.ext
      intro x
      ext i
      cases i using Fin.cases <;> rfl)
  exact ⟨e.toFDRepIso.symm⟩

/-- Helper for restriction after scalar extension: the class of `n+1` coordinate copies is
`(n+1)` times the original class. -/
private theorem fdRepFinPiCopies_succ_class_eq_nsmul
    (n : ℕ) (V : FDRep K G) :
    ([fdRepFinPiCopies (K := K) (G := G) (n + 1) V]₀ : R₀[K](G)) =
      (n + 1) • ([V]₀ : R₀[K](G)) := by
  induction n with
  | zero =>
      simpa using fdRepFinPiCopies_one_class (K := K) (G := G) V
  | succ n ih =>
      obtain ⟨e⟩ :=
        fdRepFinPiCopies_succ_nonempty_iso_prod (K := K) (G := G) (n + 1) V
      calc
        ([fdRepFinPiCopies (K := K) (G := G) (n + 1 + 1) V]₀ : R₀[K](G)) =
            [FDRep.of
              (Representation.prod V.ρ (repFinPiCopies (K := K) (G := G) (n + 1) V))]₀ := by
              exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) ⟨e⟩
        _ = ([V]₀ : R₀[K](G)) +
            [fdRepFinPiCopies (K := K) (G := G) (n + 1) V]₀ := by
              exact finiteRepGrothendieckClass_prod_eq_add_for_scalarRestriction
                (K := K) (G := G) V (fdRepFinPiCopies (K := K) (G := G) (n + 1) V)
        _ = ([V]₀ : R₀[K](G)) + (n + 1) • ([V]₀ : R₀[K](G)) := by
              rw [ih]
        _ = (n + 1 + 1) • ([V]₀ : R₀[K](G)) := by
              rw [show (n + 1 + 1) • ([V]₀ : R₀[K](G)) =
                (n + 1) • ([V]₀ : R₀[K](G)) + [V]₀ by
                  rw [succ_nsmul]]
              abel

/-- Helper for restriction after scalar extension: after choosing a `K`-basis of `K'`, the
restricted scalar extension `K' ⊗[K] V` is equivariantly the coordinatewise sum of
`[K' : K]` copies of `V`. -/
private theorem restrictScalars_scalarExtension_nonempty_iso_finPi
    (V : FDRep K G) :
    Nonempty
      (FDRep.restrictScalars (K := K) (K' := K') (G := G)
          (FDRep.scalarExtension (k := K') V) ≅
        fdRepFinPiCopies (K := K) (G := G) (Module.finrank K K') V) := by
  let n : ℕ := Module.finrank K K'
  let W : FDRep K G :=
    FDRep.restrictScalars (K := K) (K' := K') (G := G)
      (FDRep.scalarExtension (k := K') V)
  let T : FDRep K G := fdRepFinPiCopies (K := K) (G := G) n V
  let bK' : Module.Basis (Fin n) K K' := Module.finBasis K K'
  let e0 : (K' ⊗[K] V.V) ≃ₗ[K] (Fin n → V.V) :=
    (TensorProduct.equivFinsuppOfBasisLeft bK').trans
      (Finsupp.linearEquivFunOnFinite K V.V (Fin n))
  letI : AddCommGroup W.V := W.V.obj.isAddCommGroup
  letI : Module K W.V := W.V.obj.isModule
  letI : Module.Finite K W.V := W.V.property
  let eLin : W.V ≃ₗ[K] T.V :=
    { toFun := fun x ↦ e0 (x : K' ⊗[K] V.V)
      invFun := fun y ↦ e0.symm (y : Fin n → V.V)
      left_inv := by
        intro x
        change e0.symm (e0 (x : K' ⊗[K] V.V)) = x
        simp
      right_inv := by
        intro y
        change e0 (e0.symm (y : Fin n → V.V)) = y
        simp
      map_add' := by
        intro x y
        exact e0.map_add x y
      map_smul' := by
        intro a x
        let x' : K' ⊗[K] V.V := x
        change e0 ((algebraMap K K' a) • x') = a • e0 x'
        refine TensorProduct.induction_on x' ?_ ?_ ?_
        · simp
        · intro c v
          ext i
          simp [e0, TensorProduct.smul_tmul']
          rw [← Algebra.smul_def, map_smul]
          simp [smul_smul]
        · intro x y hx hy
          simp [map_add, hx, hy] }
  let eFG : W.V ≅ T.V :=
    { hom := FGModuleCat.ofHom eLin.toLinearMap
      inv := FGModuleCat.ofHom eLin.symm.toLinearMap
      hom_inv_id := by
        apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact eLin.left_inv x
      inv_hom_id := by
        apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact eLin.right_inv x }
  refine ⟨Action.mkIso eFG ?_⟩
  intro g
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change eLin (W.ρ g x) = T.ρ g (eLin x)
  change e0 (W.ρ g x : K' ⊗[K] V.V) =
    (repFinPiCopies (K := K) (G := G) n V g) (e0 (x : K' ⊗[K] V.V))
  let x' : K' ⊗[K] V.V := x
  change e0 (LinearMap.baseChange K' (V.ρ g) x') =
    (repFinPiCopies (K := K) (G := G) n V g) (e0 x')
  refine TensorProduct.induction_on x' ?_ ?_ ?_
  · ext i
    simp [e0, repFinPiCopies]
  · intro c v
    ext i
    simp [e0, repFinPiCopies, LinearMap.baseChange_tmul]
  · intro x y hx hy
    ext i
    simp [map_add, hx, hy]

/-- Restriction of scalars after scalar extension multiplies generator classes by the field
degree. -/
theorem finiteRepGrothendieckRestrictScalarsHom_scalarExtension_class_eq_finrank_nsmul
    (V : FDRep K G) :
    finiteRepGrothendieckRestrictScalarsHom K K' G
        (finiteRepGrothendieckScalarExtensionHom K K' G [V]₀) =
      Module.finrank K K' • ([V]₀ : R₀[K](G)) := by
  rw [finiteRepGrothendieckScalarExtensionHom_class_eq,
    finiteRepGrothendieckRestrictScalarsHom_class_eq]
  obtain ⟨e⟩ :=
    restrictScalars_scalarExtension_nonempty_iso_finPi (K := K) (K' := K') (G := G) V
  have hclass :
      ([FDRep.restrictScalars (K := K) (K' := K') (G := G)
          (FDRep.scalarExtension (k := K') V)]₀ : R₀[K](G)) =
        [fdRepFinPiCopies (K := K) (G := G) (Module.finrank K K') V]₀ := by
    exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) ⟨e⟩
  have hpos : 0 < Module.finrank K K' :=
    Module.finrank_pos (R := K) (M := K')
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [hclass, hn]
  exact fdRepFinPiCopies_succ_class_eq_nsmul (K := K) (G := G) n V

end FiniteRepRestrictScalars

end FiniteRepScalarExtension

end Representation
