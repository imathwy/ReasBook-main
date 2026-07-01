import Mathlib
import Serre.Chap14.Corollary_14_14_4_4
import Serre.Chap14.Lemma_14_14_4_2
import Serre.Chap14.Proposition_14_14_1_1
import Serre.RepresentationTheory.RealizableOver
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

end FiniteRepScalarExtension

end Representation
