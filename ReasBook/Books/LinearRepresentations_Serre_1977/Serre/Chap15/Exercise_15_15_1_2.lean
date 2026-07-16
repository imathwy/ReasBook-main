import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Lemma_14_14_4_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_1_2.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped MonoidAlgebra MonoidalCategory Representation TensorProduct

namespace Representation

section CartanTensorCompatibility

variable (k : Type u) (G : Type u) [Field k] [Group G] [Finite G]

local notation:max "P₀[" A "](" G ")" =>
  finiteProjectiveGroupAlgebraGrothendieckGroup A G

namespace FiniteProjectiveGroupAlgebraModule

variable {k} {G}

/- Route correction: the remaining projective tensor obstruction is owner-level projectivity, not
the finite-over-`k` packaging. Separate the finiteness transfer to the underlying `ModuleCat`
object so the eventual projective proof can focus only on the diagonal `k[G]`-action. -/
/-- Helper for Exercise 15-15.1-2: the `ModuleCat k[G]` owner of the tensor-product
representation is finite over the base field `k`. -/
private theorem tprod_underlying_module_finite
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    let ρ := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
    let Wk : ModuleCat k[G] := Rep.toModuleMonoidAlgebra.obj ρ
    let _ : Module k Wk := Module.compHom Wk (algebraMap k k[G])
    let _ : IsScalarTower k k[G] Wk := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    Module.Finite k Wk := by
  let ρ := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
  let Wk : ModuleCat k[G] := Rep.toModuleMonoidAlgebra.obj ρ
  let _ : Module k Wk := Module.compHom Wk (algebraMap k k[G])
  let _ : IsScalarTower k k[G] Wk := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Finite k ρ := by
    infer_instance
  let f : ρ →ₗ[k] Wk :=
    { toFun := ρ.ρ.asModuleEquiv.symm
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change ρ.ρ.asModuleEquiv.symm (r • x) = ((algebraMap k k[G]) r) • ρ.ρ.asModuleEquiv.symm x
        exact ρ.ρ.asModuleEquiv_symm_map_smul r x }
  -- Transfer finite generation along the underlying `k`-linear equivalence.
  exact Module.Finite.of_surjective f fun y : Wk ↦ ⟨ρ.ρ.asModuleEquiv y, by rfl⟩

/-- Helper for Exercise 15-15.1-2: tensoring the averaging endomorphism of a finite projective
owner with a fixed finite-dimensional representation still averages to the identity on the
diagonal tensor owner. -/
private theorem tprod_raw_tensor_projective
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Projective k (TensorProduct k V P.toRep) := by
  -- Over the field `k`, the tensor carrier is a vector space and hence projective.
  infer_instance

/-- Helper for Exercise 15-15.1-2: the packaged `asModule` owner of `P.toRep` is projective,
because it is canonically equivalent to the original projective `k[G]`-module `P.V`. -/
private theorem toRep_asModule_projective
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Projective k[G] P.toRep.ρ.asModule := by
  -- Compare `P.toRep.ρ.asModule` with the original `k[G]`-module `P.V` via the counit of the
  -- `Rep.ofModuleMonoidAlgebra ⊣ Rep.toModuleMonoidAlgebra` equivalence.
  simpa [FiniteProjectiveGroupAlgebraModule.toRep] using
    (Module.Projective.of_equiv'
      ((Rep.counitIso P.V).toLinearEquiv.symm) :
      Module.Projective k[G] ((Rep.ofModuleMonoidAlgebra ⋙ Rep.toModuleMonoidAlgebra).obj P.V))

/-- Helper for Exercise 15-15.1-2: freeze Serre's Chapter 14 averaging witness on the owner
`P.toRep.ρ.asModule` before transporting it to the tensor-product owner. -/
private theorem toRep_asModule_exists_averaging_endomorphism
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    let ρ := P.toRep.ρ
    let hρMod : Module k ρ.asModule := Representation.instModuleAsModule ρ
    let hρAdd : AddCommGroup ρ.asModule := inferInstance
    let hρGMod : Module k[G] ρ.asModule := inferInstance
    let hρTower : IsScalarTower k k[G] ρ.asModule := inferInstance
    let hFin : Fintype G := Fintype.ofFinite G
    ∃ u : Module.End k ρ.asModule,
      @LinearMap.sumOfConjugates k inferInstance G inferInstance
          ρ.asModule hρAdd hρMod hρGMod hρTower
          ρ.asModule hρAdd hρMod hρGMod hρTower
          u hFin =
        (LinearMap.id : Module.End k ρ.asModule) := by
  dsimp
  -- Apply the Chapter 14 criterion on the frozen owner `P.toRep.ρ.asModule` only once, so the
  -- later tensor proof does not have to solve mixed-owner instance search again.
  let ρ := P.toRep.ρ
  let hρMod : Module k ρ.asModule := Representation.instModuleAsModule ρ
  let _ : Module k ρ.asModule := hρMod
  let hρAdd : AddCommGroup ρ.asModule := by
    infer_instance
  let hρGMod : Module k[G] ρ.asModule := by
    infer_instance
  let hρTower : IsScalarTower k k[G] ρ.asModule := by
    infer_instance
  let _ : Fintype G := Fintype.ofFinite G
  let hiffρ :=
    @projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      k inferInstance G inferInstance inferInstance ρ.asModule hρAdd hρMod hρGMod hρTower
  obtain ⟨_, u, hu⟩ := hiffρ.mp (toRep_asModule_projective (k := k) (G := G) P)
  exact ⟨u, hu⟩

/-- Helper for Exercise 15-15.1-2: the underlying `k`-vector space of the diagonal tensor owner
is projective over the base field. -/
private theorem tprod_asModule_projective
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Projective k
      (Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ).ρ.asModule := by
  -- The tensor owner is definitionally the raw tensor product of the two underlying `k`-spaces.
  simpa [FiniteProjectiveGroupAlgebraModule.toRep] using
    (tprod_raw_tensor_projective (k := k) (G := G) V P)

/-- Helper for Exercise 15-15.1-2: tensoring a short exact sequence in `Rep k G` on the left by a
fixed finite-dimensional representation preserves short exactness. -/
private theorem rep_tensorLeft_shortExact
    (V : FDRep k G) (S : ShortComplex (Rep k G)) (hS : S.ShortExact) :
    (S.map
      (MonoidalCategory.tensorLeft ((forget₂ (FDRep k G) (Rep k G)).obj V))).ShortExact := by
  -- Forget to `ModuleCat k`, where tensoring by a fixed vector space is exact because all
  -- `k`-modules are flat.
  apply
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := S.map
        (MonoidalCategory.tensorLeft ((forget₂ (FDRep k G) (Rep k G)).obj V)))
      (F := forget₂ (Rep k G) (ModuleCat k))).1
  have hForget : (S.map (forget₂ (Rep k G) (ModuleCat k))).ShortExact := by
    simpa using hS.map_of_exact (forget₂ (Rep k G) (ModuleCat k))
  let Vk : ModuleCat k := ModuleCat.of k (((forget₂ (FDRep k G) (Rep k G)).obj V).V)
  have hFlat : Module.Flat k Vk := by
    infer_instance
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (MonoidalCategory.tensorLeft Vk) :=
    (Module.Flat.iff_preservesFiniteLimits_tensorLeft (R := k) Vk).mp hFlat
  have hTensor := hForget.map_of_exact (MonoidalCategory.tensorLeft Vk)
  simpa [Vk] using hTensor

/-- Helper for Exercise 15-15.1-2: the diagonal tensor owner attached to a projective module and
fixed finite-dimensional representation is still finite over `k` before one proves
projectivity over `k[G]`. -/
private theorem tprod_rep_module_finite
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Finite k (Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ) := by
  -- The tensor owner is a finite-dimensional representation, so its underlying `k`-module is
  -- finite automatically.
  infer_instance

/-- Helper for Exercise 15-15.1-2: the diagonal tensor action on pure tensors applies the group
element to each factor separately. -/
private theorem tprod_toRep_apply_tmul
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G)
    (g : G) (v : ((forget₂ (FDRep k G) (Rep k G)).obj V).V) (x : P.toRep.V) :
    (Representation.tprod (FDRep.ρ V) P.toRep.ρ g) (v ⊗ₜ[k] x) =
      (FDRep.ρ V g v) ⊗ₜ[k] (P.toRep.ρ g x) := by
  -- The tensor-product representation acts by `TensorProduct.map` on pure tensors.
  rw [Representation.tprod_apply, TensorProduct.map_tmul]

/-- Helper for Exercise 15-15.1-2: after transporting the diagonal tensor owner to the raw tensor
product, the `k[G]`-action of `g` is the expected action on each tensor factor. -/
private theorem tprod_asModuleEquiv_map_of_tmul
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G)
    (g : G) (v : ((forget₂ (FDRep k G) (Rep k G)).obj V).V) (x : P.toRep.V) :
    let σ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
    σ.ρ.asModuleEquiv ((MonoidAlgebra.of k G g : k[G]) • σ.ρ.asModuleEquiv.symm (v ⊗ₜ[k] x)) =
      (FDRep.ρ V g v) ⊗ₜ[k] (P.toRep.ρ g x) := by
  -- Normalize the `k[G]`-action through `asModuleEquiv` before applying the pure-tensor action
  -- formula for `Representation.tprod`.
  dsimp
  simpa [Representation.asAlgebraHom_of] using
    (Representation.asModuleEquiv_map_smul
      (ρ := Representation.tprod (FDRep.ρ V) P.toRep.ρ)
      (r := MonoidAlgebra.of k G g)
      (x := (Representation.tprod (FDRep.ρ V) P.toRep.ρ).asModuleEquiv.symm (v ⊗ₜ[k] x)))

/-- Helper for Exercise 15-15.1-2: after transporting an endomorphism of `P.toRep.ρ.asModule`
to the diagonal tensor owner, its value on a pure tensor is obtained by applying the original
endomorphism on the projective factor only. -/
private theorem tprod_transport_end_apply_tmul
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G)
    (u : Module.End k P.toRep.ρ.asModule)
    (v : ((forget₂ (FDRep k G) (Rep k G)).obj V).V) (x : P.toRep.V) :
    let σ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
    let _ : Fintype G := Fintype.ofFinite G
    let uRaw : Module.End k P.toRep.V :=
      (P.toRep.ρ.asModuleEquiv : P.toRep.ρ.asModule ≃ₗ[k] P.toRep.V) ∘ₗ
        (u ∘ₗ (P.toRep.ρ.asModuleEquiv.symm : P.toRep.V ≃ₗ[k] P.toRep.ρ.asModule))
    let uσ : Module.End k σ.ρ.asModule :=
      ((σ.ρ.asModuleEquiv.symm : (↑σ) →ₗ[k] σ.ρ.asModule)) ∘ₗ
        ((TensorProduct.map
            (LinearMap.id :
              ((forget₂ (FDRep k G) (Rep k G)).obj V).V →ₗ[k]
                ((forget₂ (FDRep k G) (Rep k G)).obj V).V)
            uRaw) ∘ₗ
          (σ.ρ.asModuleEquiv : σ.ρ.asModule →ₗ[k] (↑σ)))
    uσ (σ.ρ.asModuleEquiv.symm (v ⊗ₜ[k] x)) =
      σ.ρ.asModuleEquiv.symm
        (v ⊗ₜ[k] (P.toRep.ρ.asModuleEquiv (u (P.toRep.ρ.asModuleEquiv.symm x)))) := by
  -- Expand the transported tensor endomorphism once; on a pure tensor this is definitionally the
  -- identity on `V` tensored with the transported endomorphism on `P`.
  rfl

/-- Helper for Exercise 15-15.1-2: conjugating the transported tensor endomorphism and then
moving back to the raw tensor owner keeps the left tensor factor fixed and conjugates the
projective factor exactly as in the source averaging argument. -/
private theorem tprod_transport_conjugate_apply_tmul
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G)
    (u : Module.End k P.toRep.ρ.asModule)
    (g : G)
    (v : ((forget₂ (FDRep k G) (Rep k G)).obj V).V) (x : P.toRep.V) :
    let σ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
    let uRaw : Module.End k P.toRep.V :=
      (P.toRep.ρ.asModuleEquiv : P.toRep.ρ.asModule ≃ₗ[k] P.toRep.V) ∘ₗ
        (u ∘ₗ (P.toRep.ρ.asModuleEquiv.symm : P.toRep.V ≃ₗ[k] P.toRep.ρ.asModule))
    let uσ : Module.End k σ.ρ.asModule :=
      ((σ.ρ.asModuleEquiv.symm : (↑σ) →ₗ[k] σ.ρ.asModule)) ∘ₗ
        ((TensorProduct.map
            (LinearMap.id :
              ((forget₂ (FDRep k G) (Rep k G)).obj V).V →ₗ[k]
                ((forget₂ (FDRep k G) (Rep k G)).obj V).V)
            uRaw) ∘ₗ
          (σ.ρ.asModuleEquiv : σ.ρ.asModule →ₗ[k] (↑σ)))
    σ.ρ.asModuleEquiv
        ((MonoidAlgebra.of k G g : k[G]) •
          uσ
            ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
              σ.ρ.asModuleEquiv.symm (v ⊗ₜ[k] x))) =
      v ⊗ₜ[k]
        (P.toRep.ρ.asModuleEquiv
          ((MonoidAlgebra.of k G g : k[G]) •
            u
              ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
                P.toRep.ρ.asModuleEquiv.symm x))) := by
  -- First rewrite the inverse group action on the tensor owner to an explicit pure tensor.
  dsimp
  have hginv :
      ((MonoidAlgebra.single g⁻¹ (1 : k) : k[G]) •
          (Representation.tprod (FDRep.ρ V) P.toRep.ρ).asModuleEquiv.symm (v ⊗ₜ[k] x)) =
        (Representation.tprod (FDRep.ρ V) P.toRep.ρ).asModuleEquiv.symm
          ((FDRep.ρ V g⁻¹ v) ⊗ₜ[k] (P.toRep.ρ g⁻¹ x)) := by
    -- The new normalization lemma removes the stubborn `asAlgebraHom (single g 1)` presentation.
    apply (Representation.asModuleEquiv (Representation.tprod (FDRep.ρ V) P.toRep.ρ)).injective
    simpa [MonoidAlgebra.of_apply] using
      tprod_asModuleEquiv_map_of_tmul (k := k) (G := G) V P g⁻¹ v x
  have hu :=
    -- Applying `asModuleEquiv` to the transported endomorphism computation turns it into a raw
    -- tensor identity with the inverse action already normalized on `P`.
    (by
      simpa [MonoidAlgebra.of_apply, Representation.asModuleEquiv_symm_map_rho] using
        congrArg (Representation.asModuleEquiv (Representation.tprod (FDRep.ρ V) P.toRep.ρ))
          (tprod_transport_end_apply_tmul (k := k) (G := G) V P u
            (FDRep.ρ V g⁻¹ v) (P.toRep.ρ g⁻¹ x)))
  rw [hginv, hu]
  -- Next transport `u` across the tensor owner, then act by `g` once more on the resulting tensor.
  -- The left tensor factor collapses by `ρ g (ρ g⁻¹ v) = v`, while the right factor is exactly the
  -- conjugated owner action on `P`.
  rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
  simp [Representation.tprod_apply, TensorProduct.map_tmul]
  rfl

/-- Helper for Exercise 15-15.1-2: after transporting the averaging endomorphism on
`P.toRep.ρ.asModule` to the diagonal tensor owner, the averaged operator acts on pure tensors by
leaving the left tensor factor fixed and averaging only the projective factor. -/
private theorem tprod_transport_sumOfConjugates_apply_tmul
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G)
    (u : Module.End k P.toRep.ρ.asModule)
    [Fintype G]
    (v : ((forget₂ (FDRep k G) (Rep k G)).obj V).V) (x : P.toRep.V) :
    let σ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
    let uRaw : Module.End k P.toRep.V :=
      (P.toRep.ρ.asModuleEquiv : P.toRep.ρ.asModule ≃ₗ[k] P.toRep.V) ∘ₗ
        (u ∘ₗ (P.toRep.ρ.asModuleEquiv.symm : P.toRep.V ≃ₗ[k] P.toRep.ρ.asModule))
    let uσ : Module.End k σ.ρ.asModule :=
      ((σ.ρ.asModuleEquiv.symm : (↑σ) →ₗ[k] σ.ρ.asModule)) ∘ₗ
        ((TensorProduct.map
            (LinearMap.id :
              ((forget₂ (FDRep k G) (Rep k G)).obj V).V →ₗ[k]
                ((forget₂ (FDRep k G) (Rep k G)).obj V).V)
            uRaw) ∘ₗ
          (σ.ρ.asModuleEquiv : σ.ρ.asModule →ₗ[k] (↑σ)))
    σ.ρ.asModuleEquiv
        (∑ g : G,
          (MonoidAlgebra.of k G g : k[G]) •
            uσ ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
              σ.ρ.asModuleEquiv.symm (v ⊗ₜ[k] x))) =
      v ⊗ₜ[k]
        ∑ g : G,
          P.toRep.ρ.asModuleEquiv
            ((MonoidAlgebra.of k G g : k[G]) •
              u ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
                P.toRep.ρ.asModuleEquiv.symm x)) := by
  -- Expand the textbook averaging sum and compare the transport termwise on pure tensors.
  dsimp
  rw [map_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl ?_
  intro g _
  -- Route correction: the termwise comparison is stable only after rewriting the conjugation
  -- summand with the previously normalized transport formula.
  simpa using tprod_transport_conjugate_apply_tmul (k := k) (G := G) V P u g v x

/-- Helper for Exercise 15-15.1-2: once the transported averaging sum is rewritten on pure
tensors, the frozen averaging identity `hu` on `P.toRep.ρ.asModule` closes the pure branch of the
tensor induction for the diagonal owner. -/
private theorem tprod_transport_sumOfConjugates_eq_id_apply_tmul
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G)
    (u : Module.End k P.toRep.ρ.asModule)
    [Fintype G]
    (hu :
      ∀ x : P.toRep.V,
        (∑ g : G,
          P.toRep.ρ.asModuleEquiv
            ((MonoidAlgebra.of k G g : k[G]) •
              u ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
                P.toRep.ρ.asModuleEquiv.symm x))) = x)
    (v : ((forget₂ (FDRep k G) (Rep k G)).obj V).V) (x : P.toRep.V) :
    let σ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
    let uRaw : Module.End k P.toRep.V :=
      (P.toRep.ρ.asModuleEquiv : P.toRep.ρ.asModule ≃ₗ[k] P.toRep.V) ∘ₗ
        (u ∘ₗ (P.toRep.ρ.asModuleEquiv.symm : P.toRep.V ≃ₗ[k] P.toRep.ρ.asModule))
    let uσ : Module.End k σ.ρ.asModule :=
      ((σ.ρ.asModuleEquiv.symm : (↑σ) →ₗ[k] σ.ρ.asModule)) ∘ₗ
        ((TensorProduct.map
            (LinearMap.id :
              ((forget₂ (FDRep k G) (Rep k G)).obj V).V →ₗ[k]
                ((forget₂ (FDRep k G) (Rep k G)).obj V).V)
            uRaw) ∘ₗ
          (σ.ρ.asModuleEquiv : σ.ρ.asModule →ₗ[k] (↑σ)))
    σ.ρ.asModuleEquiv
        (∑ g : G,
          (MonoidAlgebra.of k G g : k[G]) •
            uσ ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
              σ.ρ.asModuleEquiv.symm (v ⊗ₜ[k] x))) =
      v ⊗ₜ[k] x := by
  -- Rewrite the transported average on a pure tensor, then collapse the right tensor factor with
  -- the frozen averaging identity on `P.toRep.ρ.asModule`.
  dsimp
  calc
    _ = v ⊗ₜ[k] (
        ∑ g : G,
          P.toRep.ρ.asModuleEquiv
            ((MonoidAlgebra.of k G g : k[G]) •
              u ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
                P.toRep.ρ.asModuleEquiv.symm x))) := by
          simpa using
            tprod_transport_sumOfConjugates_apply_tmul
              (k := k) (G := G) V P u v x
    _ = v ⊗ₜ[k] x := by
          rw [hu x]

/-- Helper for Exercise 15-15.1-2: the frozen Chapter 14 averaging identity on the owner
`P.toRep.ρ.asModule` rewrites to Serre's textbook average formula on the carrier `P.toRep.V`. -/
private theorem toRep_textbook_average_eq_id_apply
    (P : FiniteProjectiveGroupAlgebraModule k G) [Fintype G] :
    let ρ := P.toRep.ρ
    let hρMod : Module k ρ.asModule := Representation.instModuleAsModule ρ
    let hρAdd : AddCommGroup ρ.asModule := inferInstance
    let hρGMod : Module k[G] ρ.asModule := inferInstance
    let hρTower : IsScalarTower k k[G] ρ.asModule := inferInstance
    ∀ u : Module.End k ρ.asModule,
      @LinearMap.sumOfConjugates k inferInstance G inferInstance
          ρ.asModule hρAdd hρMod hρGMod hρTower
          ρ.asModule hρAdd hρMod hρGMod hρTower
          u inferInstance =
        (LinearMap.id : Module.End k ρ.asModule) →
      ∀ x : P.toRep.V,
        (∑ g : G,
          P.toRep.ρ.asModuleEquiv
            ((MonoidAlgebra.of k G g : k[G]) •
              u ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
                P.toRep.ρ.asModuleEquiv.symm x))) = x := by
  -- Rewrite Serre's explicit average as `sumOfConjugates` on the frozen owner, then transport the
  -- identity back to `P.toRep.V` through `asModuleEquiv`.
  dsimp
  classical
  intro u hu x
  let ρ := P.toRep.ρ
  let hρMod : Module k ρ.asModule := Representation.instModuleAsModule ρ
  let _ : Module k ρ.asModule := hρMod
  let hρAdd : AddCommGroup ρ.asModule := inferInstance
  let _ : AddCommGroup ρ.asModule := hρAdd
  let hρGMod : Module k[G] ρ.asModule := inferInstance
  let _ : Module k[G] ρ.asModule := hρGMod
  let hρTower : IsScalarTower k k[G] ρ.asModule := inferInstance
  let _ : IsScalarTower k k[G] ρ.asModule := hρTower
  have howner :
      ∑ g : G,
        (MonoidAlgebra.of k G g : k[G]) •
          u ((MonoidAlgebra.of k G g⁻¹ : k[G]) • P.toRep.ρ.asModuleEquiv.symm x) =
        P.toRep.ρ.asModuleEquiv.symm x := by
    calc
      _ =
          @LinearMap.sumOfConjugates k inferInstance G inferInstance
            ρ.asModule hρAdd hρMod hρGMod hρTower
            ρ.asModule hρAdd hρMod hρGMod hρTower
            u inferInstance
            (P.toRep.ρ.asModuleEquiv.symm x) := by
            simpa [ρ, MonoidAlgebra.of_apply] using
              (@textbook_average_eq_sumOfConjugates k inferInstance G inferInstance inferInstance
                ρ.asModule hρAdd hρMod hρGMod hρTower inferInstance
                u (P.toRep.ρ.asModuleEquiv.symm x))
      _ = (LinearMap.id : Module.End k ρ.asModule) (P.toRep.ρ.asModuleEquiv.symm x) := by
            simpa using
              congrArg
                (fun f : Module.End k ρ.asModule => f (P.toRep.ρ.asModuleEquiv.symm x))
                hu
      _ = P.toRep.ρ.asModuleEquiv.symm x := by
            rfl
  -- Apply the linear equivalence to move the owner equality back to the representation carrier.
  exact
    (by
      simpa [map_sum] using
        congrArg
          (fun z : P.toRep.ρ.asModule => P.toRep.ρ.asModuleEquiv z)
          howner)

/-- Helper for Exercise 15-15.1-2: the transported averaging endomorphism on the diagonal tensor
owner still has `sumOfConjugates = id`. -/
private theorem tprod_transport_sumOfConjugates_eq_id
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) [Fintype G] :
    let ρ := P.toRep.ρ
    let hρMod : Module k ρ.asModule := Representation.instModuleAsModule ρ
    let hρAdd : AddCommGroup ρ.asModule := inferInstance
    let hρGMod : Module k[G] ρ.asModule := inferInstance
    let hρTower : IsScalarTower k k[G] ρ.asModule := inferInstance
    ∀ u : Module.End k ρ.asModule,
      (∀ x : P.toRep.V,
        (∑ g : G,
          P.toRep.ρ.asModuleEquiv
            ((MonoidAlgebra.of k G g : k[G]) •
              u ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
                P.toRep.ρ.asModuleEquiv.symm x))) = x) →
      let σ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
      let hσMod : Module k σ.ρ.asModule := Representation.instModuleAsModule σ.ρ
      let hσAdd : AddCommGroup σ.ρ.asModule := inferInstance
      let hσGMod : Module k[G] σ.ρ.asModule := inferInstance
      let hσTower : IsScalarTower k k[G] σ.ρ.asModule := inferInstance
      let uRaw : Module.End k P.toRep.V :=
        (P.toRep.ρ.asModuleEquiv : P.toRep.ρ.asModule ≃ₗ[k] P.toRep.V) ∘ₗ
          (u ∘ₗ (P.toRep.ρ.asModuleEquiv.symm : P.toRep.V ≃ₗ[k] P.toRep.ρ.asModule))
      let uσ : Module.End k σ.ρ.asModule :=
        ((σ.ρ.asModuleEquiv.symm : (↑σ) →ₗ[k] σ.ρ.asModule)) ∘ₗ
          ((TensorProduct.map
              (LinearMap.id :
                ((forget₂ (FDRep k G) (Rep k G)).obj V).V →ₗ[k]
                  ((forget₂ (FDRep k G) (Rep k G)).obj V).V)
              uRaw) ∘ₗ
            (σ.ρ.asModuleEquiv : σ.ρ.asModule →ₗ[k] (↑σ)))
      @LinearMap.sumOfConjugates k inferInstance G inferInstance
          σ.ρ.asModule hσAdd hσMod hσGMod hσTower
          σ.ρ.asModule hσAdd hσMod hσGMod hσTower
          uσ inferInstance =
        (LinearMap.id : Module.End k σ.ρ.asModule) := by
  classical
  dsimp
  intro u huCarrier
  let σ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
  let hσMod : Module k σ.ρ.asModule := Representation.instModuleAsModule σ.ρ
  let _ : Module k σ.ρ.asModule := hσMod
  let hσAdd : AddCommGroup σ.ρ.asModule := inferInstance
  let _ : AddCommGroup σ.ρ.asModule := hσAdd
  let hσGMod : Module k[G] σ.ρ.asModule := inferInstance
  let _ : Module k[G] σ.ρ.asModule := hσGMod
  let hσTower : IsScalarTower k k[G] σ.ρ.asModule := inferInstance
  let _ : IsScalarTower k k[G] σ.ρ.asModule := hσTower
  let uRaw : Module.End k P.toRep.V :=
    ((P.toRep.ρ.asModuleEquiv : P.toRep.ρ.asModule ≃ₗ[k] P.toRep.V) :
      P.toRep.ρ.asModule →ₗ[k] P.toRep.V) ∘ₗ
      (u ∘ₗ
        ((P.toRep.ρ.asModuleEquiv.symm : P.toRep.V ≃ₗ[k] P.toRep.ρ.asModule) :
          P.toRep.V →ₗ[k] P.toRep.ρ.asModule))
  let uσ : Module.End k σ.ρ.asModule :=
    ((σ.ρ.asModuleEquiv.symm : (↑σ) →ₗ[k] σ.ρ.asModule)) ∘ₗ
      ((TensorProduct.map
          (LinearMap.id :
            ((forget₂ (FDRep k G) (Rep k G)).obj V).V →ₗ[k]
              ((forget₂ (FDRep k G) (Rep k G)).obj V).V)
          uRaw) ∘ₗ
        (σ.ρ.asModuleEquiv : σ.ρ.asModule →ₗ[k] (↑σ)))
  let hσSum : Module.End k σ.ρ.asModule :=
    @LinearMap.sumOfConjugates k inferInstance G inferInstance
      σ.ρ.asModule hσAdd hσMod hσGMod hσTower
      σ.ρ.asModule hσAdd hσMod hσGMod hσTower
      uσ inferInstance
  let _ : Module k (↑σ) := by infer_instance
  let F : Module.End k (↑σ) :=
    (σ.ρ.asModuleEquiv : σ.ρ.asModule →ₗ[k] (↑σ)) ∘ₗ
      (hσSum ∘ₗ
        (σ.ρ.asModuleEquiv.symm : (↑σ) →ₗ[k] σ.ρ.asModule))
  have hF : F = LinearMap.id := by
    apply LinearMap.ext
    intro z
    -- After transporting to the raw tensor carrier, only the pure-tensor branch needs the
    -- averaging argument; zero and addition follow from linearity of `F`.
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [F]
    · intro v x
      have htext :
          σ.ρ.asModuleEquiv
              (∑ g : G,
                (MonoidAlgebra.of k G g : k[G]) •
                  uσ ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
                    σ.ρ.asModuleEquiv.symm (v ⊗ₜ[k] x))) =
            σ.ρ.asModuleEquiv
              (hσSum (σ.ρ.asModuleEquiv.symm (v ⊗ₜ[k] x))) := by
        simpa using
          congrArg
            (fun z : σ.ρ.asModule => σ.ρ.asModuleEquiv z)
            (@textbook_average_eq_sumOfConjugates
              k inferInstance G inferInstance inferInstance
              σ.ρ.asModule hσAdd hσMod hσGMod hσTower inferInstance
              uσ (σ.ρ.asModuleEquiv.symm (v ⊗ₜ[k] x)))
      -- The pure tensor case is exactly the transported Chapter 14 averaging identity.
      calc
        F (v ⊗ₜ[k] x) =
            σ.ρ.asModuleEquiv
              (hσSum (σ.ρ.asModuleEquiv.symm (v ⊗ₜ[k] x))) := by
                rfl
        _ =
            σ.ρ.asModuleEquiv
              (∑ g : G,
                (MonoidAlgebra.of k G g : k[G]) •
                  uσ ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
                    σ.ρ.asModuleEquiv.symm (v ⊗ₜ[k] x))) := by
                exact htext.symm
        _ = v ⊗ₜ[k] x := by
                simpa [σ, uRaw, uσ] using
                  tprod_transport_sumOfConjugates_eq_id_apply_tmul
                    (k := k) (G := G) V P u huCarrier v x
    · intro z₁ z₂ hz₁ hz₂
      calc
        F (z₁ + z₂) = F z₁ + F z₂ := by simp [F]
        _ = z₁ + z₂ := by simpa [hz₁, hz₂]
  -- Apply the raw tensor identity at `σ.ρ.asModuleEquiv y` and transport back to the owner.
  change hσSum = (LinearMap.id : Module.End k σ.ρ.asModule)
  apply LinearMap.ext
  intro y
  apply (σ.ρ.asModuleEquiv : σ.ρ.asModule ≃ₗ[k] (↑σ)).injective
  have hy := congrArg (fun f : Module.End k (↑σ) => f (σ.ρ.asModuleEquiv y)) hF
  simpa [F] using hy

private theorem tprod_projective
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    Module.Projective k[G]
      (Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ).ρ.asModule := by
  -- Route correction: apply the Chapter 14 criterion only after freezing the owner-side average
  -- on `P.toRep.ρ.asModule`, then transport that witness to the diagonal tensor owner.
  let ρ := P.toRep.ρ
  let hρMod : Module k ρ.asModule := Representation.instModuleAsModule ρ
  let _ : Module k ρ.asModule := hρMod
  let hρAdd : AddCommGroup ρ.asModule := by infer_instance
  let hρGMod : Module k[G] ρ.asModule := by infer_instance
  let hρTower : IsScalarTower k k[G] ρ.asModule := by infer_instance
  let hFin : Fintype G := Fintype.ofFinite G
  let _ : Fintype G := hFin
  have hAvg :
      ∃ u : Module.End k ρ.asModule,
        @LinearMap.sumOfConjugates k inferInstance G inferInstance
            ρ.asModule hρAdd hρMod hρGMod hρTower
            ρ.asModule hρAdd hρMod hρGMod hρTower
            u hFin =
          (LinearMap.id : Module.End k ρ.asModule) := by
    simpa [ρ, hρMod, hρAdd, hρGMod, hρTower, hFin] using
      toRep_asModule_exists_averaging_endomorphism (k := k) (G := G) P
  rcases hAvg with ⟨u, hu⟩
  let σ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
  let hσMod : Module k σ.ρ.asModule := Representation.instModuleAsModule σ.ρ
  let _ : Module k σ.ρ.asModule := hσMod
  let hσAdd : AddCommGroup σ.ρ.asModule := by infer_instance
  let hσGMod : Module k[G] σ.ρ.asModule := by infer_instance
  let hσTower : IsScalarTower k k[G] σ.ρ.asModule := by infer_instance
  let uRaw : Module.End k P.toRep.V :=
    (P.toRep.ρ.asModuleEquiv : P.toRep.ρ.asModule ≃ₗ[k] P.toRep.V) ∘ₗ
      (u ∘ₗ (P.toRep.ρ.asModuleEquiv.symm : P.toRep.V ≃ₗ[k] P.toRep.ρ.asModule))
  let uσ : Module.End k σ.ρ.asModule :=
    ((σ.ρ.asModuleEquiv.symm : (↑σ) →ₗ[k] σ.ρ.asModule)) ∘ₗ
      ((TensorProduct.map
          (LinearMap.id :
            ((forget₂ (FDRep k G) (Rep k G)).obj V).V →ₗ[k]
              ((forget₂ (FDRep k G) (Rep k G)).obj V).V)
          uRaw) ∘ₗ
        (σ.ρ.asModuleEquiv : σ.ρ.asModule →ₗ[k] (↑σ)))
  have huCarrier :
      ∀ x : P.toRep.V,
        (∑ g : G,
          P.toRep.ρ.asModuleEquiv
            ((MonoidAlgebra.of k G g : k[G]) •
              u ((MonoidAlgebra.of k G g⁻¹ : k[G]) •
                P.toRep.ρ.asModuleEquiv.symm x))) = x := by
    intro x
    exact
      toRep_textbook_average_eq_id_apply
        (k := k) (G := G) P u hu x
  have huσ :
      @LinearMap.sumOfConjugates k inferInstance G inferInstance
          σ.ρ.asModule hσAdd hσMod hσGMod hσTower
          σ.ρ.asModule hσAdd hσMod hσGMod hσTower
          uσ hFin =
        (LinearMap.id : Module.End k σ.ρ.asModule) := by
    simpa [σ, uRaw, uσ, hσMod, hσAdd, hσGMod, hσTower, hFin] using
      tprod_transport_sumOfConjugates_eq_id
        (k := k) (G := G) V P u huCarrier
  -- Apply the Chapter 14 criterion after transporting the averaging witness to the diagonal owner.
  refine
    (@projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      k inferInstance G inferInstance inferInstance
      σ.ρ.asModule hσAdd hσMod hσGMod hσTower).mpr ?_
  refine ⟨?_, uσ, huσ⟩
  simpa [σ, hσMod] using
    tprod_asModule_projective (k := k) (G := G) V P

/-- Tensoring a finite-dimensional representation with a finite projective representation gives a
finite projective representation. -/
def tprod
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    FiniteProjectiveGroupAlgebraModule k G :=
  let ρ := Rep.of <| Representation.tprod (FDRep.ρ V) P.toRep.ρ
  let Wk : ModuleCat k[G] := Rep.toModuleMonoidAlgebra.obj ρ
  let _ : Module k Wk := Module.compHom Wk (algebraMap k k[G])
  let _ : IsScalarTower k k[G] Wk := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Finite k Wk := tprod_underlying_module_finite V P
  let _ : Module.Finite k[G] Wk := Module.Finite.of_restrictScalars_finite k k[G] Wk
  let W : FGModuleCat k[G] := by
    refine ⟨Wk, ?_⟩
    change Module.Finite k[G] Wk
    infer_instance
  let hW : Module.Projective k[G] W := by
    simpa using tprod_projective V P
  ⟨W, hW⟩

end FiniteProjectiveGroupAlgebraModule

scoped[Representation] notation:max V " ⊗ₚ " P =>
  FiniteProjectiveGroupAlgebraModule.tprod V P

omit [Finite G] in
/-- Helper for Exercise 15-15.1-2: a `Rep`-level isomorphism between the images of two finite
projective owners yields an isomorphism of the owners themselves. -/
private theorem finiteProjective_nonempty_iso_of_toRep_iso
    {P Q : FiniteProjectiveGroupAlgebraModule k G}
    (hPQ : Nonempty (P.toRep ≅ Q.toRep)) :
    Nonempty (P ≅ Q) := by
  rcases hPQ with ⟨e⟩
  let eMod := Rep.toModuleMonoidAlgebra.mapIso e
  let eLin : P.V ≃ₗ[k[G]] Q.V :=
    (Rep.counitIso P.V).toLinearEquiv.symm.trans
      (eMod.toLinearEquiv.trans (Rep.counitIso Q.V).toLinearEquiv)
  -- Repackage the ambient `k[G]`-linear equivalence as an isomorphism in the projective owner
  -- category.
  exact
    (Representation.finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := k) (G := G) P Q).2 ⟨eLin⟩

/-- Helper for Exercise 15-15.1-2: tensoring a finite projective owner with the monoidal unit of
`FDRep k G` is canonically isomorphic to the original owner. -/
private theorem one_tprod_nonempty_iso
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    Nonempty (((𝟙_ (FDRep k G)) ⊗ₚ P) ≅ P) := by
  -- Compare the underlying `Rep` owners through the tensor left unitor, then transport that
  -- isomorphism back to the projective owner category.
  let ρ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ (𝟙_ (FDRep k G))) P.toRep.ρ
  let e₁ : (((𝟙_ (FDRep k G)) ⊗ₚ P).toRep) ≅ ρ := by
    simpa [ρ, FiniteProjectiveGroupAlgebraModule.tprod,
      FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.unitIso ρ).symm
  let e₂ : ρ ≅ P.toRep := by
    simpa [ρ] using (λ_ P.toRep)
  apply finiteProjective_nonempty_iso_of_toRep_iso (k := k) (G := G)
  exact ⟨e₁ ≪≫ e₂⟩

/-- Helper for Exercise 15-15.1-2: the two ways of parenthesizing a threefold tensor product of
finite-dimensional representations and a finite projective owner are isomorphic. -/
private theorem tensorProjective_associator_nonempty_iso
    (V W : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    Nonempty (((V ⊗ W) ⊗ₚ P) ≅ (V ⊗ₚ (W ⊗ₚ P))) := by
  -- Compare the two projective owners after forgetting to `Rep k G`, where the monoidal
  -- associator identifies the two parenthesizations.
  let ρ₁ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ (V ⊗ W)) P.toRep.ρ
  let ρ₂ : Rep k G :=
    Rep.of <| Representation.tprod (FDRep.ρ V)
      (FiniteProjectiveGroupAlgebraModule.tprod W P).toRep.ρ
  let e₁ : (((V ⊗ W) ⊗ₚ P).toRep) ≅ ρ₁ := by
    simpa [ρ₁, FiniteProjectiveGroupAlgebraModule.tprod,
      FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.unitIso ρ₁).symm
  let e₂ :
      ρ₁ ≅
        ((forget₂ (FDRep k G) (Rep k G)).obj V ⊗
          ((forget₂ (FDRep k G) (Rep k G)).obj W ⊗ P.toRep)) := by
    simpa [ρ₁] using
      (α_ ((forget₂ (FDRep k G) (Rep k G)).obj V)
        ((forget₂ (FDRep k G) (Rep k G)).obj W) P.toRep)
  let ρWP : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ W) P.toRep.ρ
  let e₃ :
      ((forget₂ (FDRep k G) (Rep k G)).obj V ⊗
          ((forget₂ (FDRep k G) (Rep k G)).obj W ⊗ P.toRep)) ≅
        ρ₂ := by
    -- First identify `W ⊗ P` in `Rep`, then tensor that comparison on the left by `V`.
    let eWP : ((forget₂ (FDRep k G) (Rep k G)).obj W ⊗ P.toRep) ≅
        (FiniteProjectiveGroupAlgebraModule.tprod W P).toRep := by
      simpa [ρWP, FiniteProjectiveGroupAlgebraModule.tprod,
        FiniteProjectiveGroupAlgebraModule.toRep] using
        (Rep.unitIso ρWP)
    simpa [ρ₂] using
      (((forget₂ (FDRep k G) (Rep k G)).obj V) ◁ᵢ eWP)
  let e₄ : ρ₂ ≅ (V ⊗ₚ (W ⊗ₚ P)).toRep := by
    simpa [ρ₂, FiniteProjectiveGroupAlgebraModule.tprod,
      FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.unitIso ρ₂)
  apply finiteProjective_nonempty_iso_of_toRep_iso (k := k) (G := G)
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄⟩

/-- Helper for Exercise 15-15.1-2: a nontrivial finite `k[G]`-module over the field `k` admits a
nonzero map to the regular module `k[G]`. -/
private theorem exists_nonzero_map_to_regular_of_nontrivial
    {M : Type u} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    [Module.Finite k M] [Nontrivial M] :
    ∃ φ : M →ₗ[k[G]] k[G], φ ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis k M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hrepr_ne : b.repr m ≠ 0 := by
    -- A nonzero vector must have a nonzero coordinate in any basis.
    intro hrepr
    exact hm ((LinearEquiv.map_eq_zero_iff b.repr).1 hrepr)
  obtain ⟨t, ht⟩ := Finsupp.ne_iff.1 hrepr_ne
  let L : M →ₗ[k] k := (Finsupp.lapply t).comp b.repr.toLinearMap
  let φ : M →ₗ[k[G]] k[G] := by
    letI : Fintype G := Fintype.ofFinite G
    refine
      { toFun := fun m' =>
          Finsupp.equivFunOnFinite.symm fun s => L ((MonoidAlgebra.of k G s⁻¹) • m')
        map_add' := by
          intro x y
          apply Finsupp.equivFunOnFinite.injective
          funext s
          simp [smul_add, map_add]
        map_smul' := ?_ }
    intro a m'
    let h : k[G] := Finsupp.equivFunOnFinite.symm fun s => L ((MonoidAlgebra.of k G s⁻¹) • m')
    apply Finsupp.equivFunOnFinite.injective
    funext s
    let P : k[G] → Prop := fun b =>
      L ((MonoidAlgebra.of k G s⁻¹) • (b • m')) = (b * h) s
    have hPa : P a := by
      -- Expanding coefficientwise against the basis of `k[G]` gives the reconstructed regular
      -- probe formula.
      refine MonoidAlgebra.induction_on a ?_ ?_ ?_
      · intro g
        have hsmul :
            MonoidAlgebra.single s⁻¹ (1 : k) • MonoidAlgebra.single g (1 : k) • m' =
              (MonoidAlgebra.single (s⁻¹ * g) (1 : k) : k[G]) • m' := by
          simpa using
            (smul_assoc (MonoidAlgebra.single s⁻¹ (1 : k))
              (MonoidAlgebra.single g (1 : k)) m').symm
        calc
          L ((MonoidAlgebra.of k G s⁻¹) • ((MonoidAlgebra.of k G g) • m')) =
              L (MonoidAlgebra.single s⁻¹ (1 : k) • MonoidAlgebra.single g (1 : k) • m') := by
                simp [MonoidAlgebra.of_apply]
          _ = L ((MonoidAlgebra.single (s⁻¹ * g) (1 : k) : k[G]) • m') := by
                exact congrArg L hsmul
          _ = (((MonoidAlgebra.of k G g) * h : k[G]) s) := by
                simp [h, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply]
      · intro b c hb hc
        -- Additivity of the functional matches additivity of the reconstructed regular-module map.
        calc
          L ((MonoidAlgebra.of k G s⁻¹) • ((b + c) • m')) =
              L ((MonoidAlgebra.of k G s⁻¹) • (b • m')) +
                L ((MonoidAlgebra.of k G s⁻¹) • (c • m')) := by
                  simp [add_smul, map_add]
          _ = (b * h) s + (c * h) s := by rw [hb, hc]
          _ = ((b + c) * h) s := by simp [add_mul]
      · intro r b hb
        -- Scalar multiples commute with the translated coefficient reconstruction.
        calc
          L ((MonoidAlgebra.of k G s⁻¹) • ((r • b) • m')) =
              r * L ((MonoidAlgebra.of k G s⁻¹) • (b • m')) := by
                have hs :
                    (MonoidAlgebra.of k G s⁻¹) • ((r • b) • m') =
                      r • ((MonoidAlgebra.of k G s⁻¹) • (b • m')) := by
                  calc
                    (MonoidAlgebra.of k G s⁻¹) • ((r • b) • m') =
                        (((MonoidAlgebra.of k G s⁻¹) * (r • b)) : k[G]) • m' := by
                          simpa using
                            (smul_assoc (MonoidAlgebra.of k G s⁻¹) (r • b) m').symm
                    _ = (r • (((MonoidAlgebra.of k G s⁻¹) * b : k[G]))) • m' := by
                          rw [mul_smul_comm]
                    _ = r • ((((MonoidAlgebra.of k G s⁻¹) * b : k[G])) • m') := by
                          simpa using
                            (smul_assoc r (((MonoidAlgebra.of k G s⁻¹) * b : k[G])) m')
                    _ = r • ((MonoidAlgebra.of k G s⁻¹) • (b • m')) := by
                          simpa [smul_eq_mul] using
                            congrArg (fun x : M => r • x) (smul_assoc (MonoidAlgebra.of k G s⁻¹) b m')
                calc
                  L ((MonoidAlgebra.of k G s⁻¹) • ((r • b) • m')) =
                      L (r • ((MonoidAlgebra.of k G s⁻¹) • (b • m'))) := by
                        exact congrArg L hs
                  _ = r * L ((MonoidAlgebra.of k G s⁻¹) • (b • m')) := by simp
          _ = r * (b * h) s := by rw [hb]
          _ = ((r • b) * h) s := by simp
    exact hPa
  refine ⟨φ, ?_⟩
  intro hφ
  have hφm : φ m = 0 := by
    simpa [hφ]
  have hLm' : L ((MonoidAlgebra.of k G (1 : G)⁻¹) • m) = 0 := by
    simpa [φ] using congrArg (fun z : k[G] => z 1) hφm
  have hof_one : (MonoidAlgebra.of k G ((1 : G)⁻¹) : k[G]) = 1 := by
    ext g
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.one_def]
  have hsingle_one_smul : (MonoidAlgebra.single 1 (1 : k) : k[G]) • m = m := by
    simpa [MonoidAlgebra.one_def] using (one_smul k[G] m)
  have hLm : L m = 0 := by
    have hLm_single : L ((MonoidAlgebra.single 1 (1 : k) : k[G]) • m) = 0 := by
      simpa [MonoidAlgebra.of_apply] using hLm'
    simpa [hsingle_one_smul] using hLm_single
  have hrepr_t_zero : b.repr m t = 0 := by
    simpa [L] using hLm
  exact ht hrepr_t_zero

/-- Helper for Exercise 15-15.1-2: the regular `k[G]`-module viewed as a finite projective owner.
-/
private abbrev finiteProjective_regular_owner :
    FiniteProjectiveGroupAlgebraModule k G :=
  ⟨FGModuleCat.of k[G] k[G], inferInstance⟩

/-- Helper for Exercise 15-15.1-2: in the field case, an epimorphism of finite projective owners is
already surjective on the forgotten `k[G]`-linear map. -/
private theorem finiteProjective_underlying_surjective_of_epi
    {E X : FiniteProjectiveGroupAlgebraModule k G} (e : E ⟶ X) [Epi e] :
    Function.Surjective e.hom.hom.hom := by
  let eLin : E.V →ₗ[k[G]] X.V := e.hom.hom.hom
  by_contra hnsurj
  let Q : Type u := X.V ⧸ LinearMap.range eLin
  let q : X.V →ₗ[k[G]] Q := (LinearMap.range eLin).mkQ
  have hQ_nontrivial : Nontrivial Q := by
    -- Route correction: the field-case owner bridge still comes from probing the nonzero quotient
    -- `X / range(e)` by the regular module.
    apply not_subsingleton_iff_nontrivial.mp
    intro hQ_sub
    apply hnsurj
    exact LinearMap.range_eq_top.mp ((Submodule.Quotient.subsingleton_iff).mp hQ_sub)
  letI : Nontrivial Q := hQ_nontrivial
  letI : Module k Q := Module.compHom Q (algebraMap k k[G])
  letI : IsScalarTower k k[G] Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module.Finite k Q := by
    let _ : Module.Finite k k[G] := MonoidAlgebra.moduleFinite
    exact Module.Finite.trans k[G] Q
  obtain ⟨η, hη_nonzero⟩ :=
    exists_nonzero_map_to_regular_of_nontrivial (k := k) (G := G) (M := Q)
  let gLin : X.V →ₗ[k[G]] k[G] := η.comp q
  have hq_comp : q.comp eLin = 0 := by
    -- The quotient map kills the whole range of `e`.
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hgLin_comp : gLin.comp eLin = 0 := by
    -- Therefore the induced regular-module probe annihilates `e`.
    ext x t
    have hηx : η (q (eLin x)) = 0 := by
      rw [show q (eLin x) = 0 by exact LinearMap.congr_fun hq_comp x, LinearMap.map_zero]
    simpa [gLin, LinearMap.comp_apply] using congrArg (fun z : k[G] => z t) hηx
  have hgLin_nonzero : gLin ≠ 0 := by
    -- Surjectivity of the quotient map pushes a vanishing composite back to `η = 0`.
    intro hgLin_zero
    apply hη_nonzero
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range eLin) y
    have hx : gLin x = 0 := by
      simp [hgLin_zero]
    simpa [gLin] using hx
  let gMor : X ⟶ finiteProjective_regular_owner (k := k) (G := G) :=
    ObjectProperty.homMk (FGModuleCat.ofHom gLin)
  have hcomp_zero : e ≫ gMor = 0 := by
    -- Repackage the vanished composite as an equality in the owner category.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simpa [gMor, gLin, FGModuleCat.ofHom, LinearMap.comp_apply] using
      (LinearMap.congr_fun hgLin_comp x)
  have hgMor_zero : gMor = 0 := by
    exact (cancel_epi e).1 (by simpa using hcomp_zero)
  have hgLin_zero : gLin = 0 := by
    apply LinearMap.ext
    intro x
    have hx :=
      congrArg
        (fun f : X.obj ⟶ (finiteProjective_regular_owner (k := k) (G := G)).obj => f.hom.hom x)
        (congrArg (fun φ : X ⟶ finiteProjective_regular_owner (k := k) (G := G) ↦ φ.hom) hgMor_zero)
    simpa [gMor, gLin, FGModuleCat.ofHom] using hx
  exact hgLin_nonzero hgLin_zero

/-- Helper for Exercise 15-15.1-2: the regular owner is projective in the projective-owner
category because owner epimorphisms are already surjective on underlying `k[G]`-modules. -/
private theorem regular_owner_projective :
    Projective (finiteProjective_regular_owner (k := k) (G := G)) := by
  refine ⟨?_⟩
  intro E X f e hepi
  letI : Epi e := hepi
  let eLin : E.V →ₗ[k[G]] X.V := e.hom.hom.hom
  let fLin : k[G] →ₗ[k[G]] X.V := f.hom.hom.hom
  have hsurj : Function.Surjective eLin := by
    -- Lift along the underlying surjective linear map.
    simpa [eLin] using finiteProjective_underlying_surjective_of_epi (k := k) (G := G) e
  obtain ⟨l, hl⟩ := Module.projective_lifting_property eLin fLin hsurj
  refine ⟨ObjectProperty.homMk (FGModuleCat.ofHom l), ?_⟩
  -- Repackage the linear lift as a morphism in the owner category.
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  simpa [eLin, fLin] using hl

/-- Helper for Exercise 15-15.1-2: the cyclic map generated by `x` in a `k[G]`-module sends `1`
to `x`. -/
private theorem regular_module_generated_map_apply_one
    {M : Type u} [AddCommGroup M] [Module k[G] M] (x : M) :
    (((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x) 1 : M) = x := by
  simp

/-- Helper for Exercise 15-15.1-2: if `x` lies in the kernel of `g`, then the cyclic map
`r ↦ r • x` already lands in that kernel. -/
private theorem regular_module_generated_map_comp_zero
    {M : Type u} [AddCommGroup M] [Module k[G] M]
    {N : Type u} [AddCommGroup N] [Module k[G] N]
    (g : M →ₗ[k[G]] N) (x : M) (hx : g x = 0) :
    g.comp ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x) = 0 := by
  ext
  simp [hx]

/-- Helper for Exercise 15-15.1-2: forgetting a projective-owner short complex to `ModuleCat k[G]`
preserves the relation `g ∘ f = 0`. -/
private theorem finiteProjective_underlying_moduleCat_zero
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    S.f.hom.hom ≫ S.g.hom.hom = 0 := by
  let F : FiniteProjectiveGroupAlgebraModule k G ⥤ ModuleCat k[G] :=
    (ObjectProperty.ι (fun M : FGModuleCat k[G] ↦ Module.Projective k[G] M)) ⋙
      (ModuleCat.isFG k[G]).ι
  -- Forgetting projectivity does not change the concrete `k[G]`-linear maps.
  simpa using (S.map F).zero

/-- Helper for Exercise 15-15.1-2: a cycle in the middle term of a short exact projective-owner
sequence already comes from the left term at the underlying module level. -/
private theorem finiteProjective_regular_owner_lift_of_kernel_element
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact)
    (x₂ : S.X₂.V) (hx₂ : S.g.hom.hom x₂ = 0) :
    ∃ x₁ : S.X₁.V, S.f.hom.hom x₁ = x₂ := by
  haveI : Projective (finiteProjective_regular_owner (k := k) (G := G)) :=
    regular_owner_projective (k := k) (G := G)
  haveI : S.HasHomology := hS.exact.hasHomology
  let hLeft := S.leftHomologyData
  let ψ₂ : finiteProjective_regular_owner (k := k) (G := G) ⟶ S.X₂ :=
    ObjectProperty.homMk (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂))
  have hψ₂_zero_lin :
      S.g.hom.hom.hom.comp ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂) = 0 := by
    -- The cyclic probe of a cycle still lands in the kernel.
    exact regular_module_generated_map_comp_zero (k := k) (G := G) S.g.hom.hom.hom x₂ hx₂
  have hψ₂_zero : ψ₂ ≫ S.g = 0 := by
    -- Repackage the vanished composite inside the owner category.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    simpa [ψ₂, FGModuleCat.ofHom] using hψ₂_zero_lin
  let ψK : finiteProjective_regular_owner (k := k) (G := G) ⟶ hLeft.K :=
    hLeft.liftK ψ₂ hψ₂_zero
  haveI : Epi hLeft.f' := hS.exact.epi_f' hLeft
  let ψ₁ : finiteProjective_regular_owner (k := k) (G := G) ⟶ S.X₁ :=
    Projective.factorThru ψK hLeft.f'
  have hψ₁_factor : ψ₁ ≫ hLeft.f' = ψK := by
    simpa [ψ₁] using (Projective.factorThru_comp ψK hLeft.f')
  have hψ₁f : ψ₁ ≫ S.f = ψ₂ := by
    -- Compare the two lifts after factoring through the cycles object.
    calc
      ψ₁ ≫ S.f = ψ₁ ≫ hLeft.f' ≫ hLeft.i := by
        simp [hLeft.f'_i]
      _ = ψK ≫ hLeft.i := by
        simpa [Category.assoc] using congrArg (fun φ => φ ≫ hLeft.i) hψ₁_factor
      _ = ψ₂ := by
        simpa [ψK] using hLeft.liftK_i ψ₂ hψ₂_zero
  refine ⟨ψ₁.hom.hom.hom 1, ?_⟩
  -- Evaluate the lifted equality at `1` to recover the original cycle.
  have hEval := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.hom) hψ₁f) 1
  have hEval' :
      S.f.hom.hom.hom (ψ₁.hom.hom.hom 1) =
        ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂) 1 := by
    have hψ₂_eval :
        (ConcreteCategory.hom
            (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂)).hom) 1 =
          ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight x₂) 1 := rfl
    exact hEval.trans hψ₂_eval
  simpa [regular_module_generated_map_apply_one (k := k) (G := G) (x := x₂)] using hEval'

/-- Helper for Exercise 15-15.1-2: owner-category exactness is already exactness of the forgotten
`k[G]`-linear maps. -/
private theorem finiteProjective_underlying_function_exact
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    Function.Exact S.f.hom.hom S.g.hom.hom := by
  intro x₂
  constructor
  · intro hx₂
    -- Lift the cycle through the regular-owner probe construction.
    exact
      finiteProjective_regular_owner_lift_of_kernel_element
        (k := k) (G := G) S hS x₂ hx₂
  · intro hx₂
    -- The reverse inclusion is just the already-known identity `g ∘ f = 0`.
    rcases hx₂ with ⟨x₁, hx₁⟩
    have hzero : S.g.hom.hom (S.f.hom.hom x₁) = 0 := by
      simpa using
        ConcreteCategory.congr_hom
          (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S) x₁
    simpa [hx₁] using hzero

/-- Helper for Exercise 15-15.1-2: mono and epi in the projective-owner category become injective
and surjective after forgetting to the underlying `k[G]`-linear maps. -/
private theorem finiteProjective_underlying_injective_surjective_bridge
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    Function.Injective S.f.hom.hom ∧ Function.Surjective S.g.hom.hom := by
  constructor
  · intro x y hxy
    let ψ : finiteProjective_regular_owner (k := k) (G := G) ⟶ S.X₁ :=
      ObjectProperty.homMk
        (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)))
    have hψ_zero_lin :
        S.f.hom.hom.hom.comp ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)) = 0 := by
      -- The kernel element `x - y` produces a cyclic map killed by `f`.
      ext
      simp [hxy]
    have hψ_zero : ψ ≫ S.f = 0 := by
      -- Repackage the vanished composite back in the owner category.
      apply ObjectProperty.hom_ext
      apply FGModuleCat.hom_ext
      simpa [ψ, FGModuleCat.ofHom] using hψ_zero_lin
    letI : Mono S.f := hS.mono_f
    have hψ_eq_zero : ψ = 0 := by
      exact (cancel_mono S.f).1 (by simpa using hψ_zero)
    have hEval := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.hom) hψ_eq_zero) 1
    have hEval' :
        (ConcreteCategory.hom
            (FGModuleCat.ofHom ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y))).hom) 1 =
          0 := by
      -- Read the vanished cyclic map at the generator `1`.
      simpa [ψ] using hEval
    have hEval'' :
        ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)) 1 = 0 := by
      have hψ_eval :
          (ConcreteCategory.hom
              (FGModuleCat.ofHom
                ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y))).hom) 1 =
            ((LinearMap.id : k[G] →ₗ[k[G]] k[G]).smulRight (x - y)) 1 := rfl
      exact hψ_eval.symm.trans hEval'
    have hdiff : x - y = 0 := by
      simpa [regular_module_generated_map_apply_one (k := k) (G := G) (x := x - y)] using hEval''
    exact sub_eq_zero.mp hdiff
  · letI : Epi S.g := hS.epi_g
    -- The surjective half is the generic owner-to-underlying epi bridge.
    simpa using finiteProjective_underlying_surjective_of_epi (k := k) (G := G) S.g

/-- Helper for Exercise 15-15.1-2: a short exact sequence of finite projective owners is already
short exact after forgetting to the ambient `ModuleCat k[G]`. -/
private theorem finiteProjective_shortExact_underlying_moduleCat
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    (ShortComplex.mk S.f.hom.hom S.g.hom.hom
      (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)).ShortExact := by
  obtain ⟨hf, hg⟩ :=
    finiteProjective_underlying_injective_surjective_bridge (k := k) (G := G) S hS
  -- Rebuild ambient short exactness from exactness of functions plus forgotten mono/epi data.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact finiteProjective_underlying_function_exact (k := k) (G := G) S hS
  · rw [ModuleCat.mono_iff_injective]
    exact hf
  · rw [ModuleCat.epi_iff_surjective]
    exact hg

/-- Helper for Exercise 15-15.1-2: the ambient `ModuleCat k[G]` short complex attached to an owner
short complex. -/
private abbrev finiteProjective_underlying_moduleCat_shortComplex
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    ShortComplex (ModuleCat k[G]) :=
  ShortComplex.mk
    S.f.hom.hom
    S.g.hom.hom
    (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S)

/-- Helper for Exercise 15-15.1-2: if the underlying `ModuleCat k[G]` short complex of an owner
sequence is short exact, then the owner sequence itself is short exact. -/
private theorem finiteProjective_shortExact_of_underlying_moduleCat_shortExact
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G))
    (hS :
      (finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G) S).ShortExact) :
    S.ShortExact := by
  let Smod := finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G) S
  let _ : Projective Smod.X₃ := by
    change Projective S.X₃.V
    infer_instance
  let hsplMod : Smod.Splitting := hS.splittingOfProjective
  let r : S.X₂ ⟶ S.X₁ := ObjectProperty.homMk (FGModuleCat.ofHom hsplMod.r.hom)
  let s : S.X₃ ⟶ S.X₂ := ObjectProperty.homMk (FGModuleCat.ofHom hsplMod.s.hom)
  have hf_r : S.f ≫ r = 𝟙 _ := by
    -- The module-level retraction of `f` is already an owner morphism.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x
    simpa [Smod, r, hsplMod, FGModuleCat.ofHom] using
      ConcreteCategory.congr_hom hsplMod.f_r x
  have hs_g : s ≫ S.g = 𝟙 _ := by
    -- The module-level section of `g` is already an owner morphism.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    ext x
    simpa [Smod, s, hsplMod, FGModuleCat.ofHom] using
      ConcreteCategory.congr_hom hsplMod.s_g x
  have hid : r ≫ S.f + S.g ≫ s = 𝟙 _ := by
    -- The split exactness identity transports componentwise from `ModuleCat`.
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simpa [Smod, r, s, hsplMod, FGModuleCat.ofHom] using
      ConcreteCategory.congr_hom hsplMod.id x
  exact
    ({ r := r
       s := s
       f_r := hf_r
       s_g := hs_g
       id := hid } : S.Splitting).shortExact

/-- Helper for Exercise 15-15.1-2: forgetting a projective-owner short complex to `Rep k G`
repackages its structure maps via `Rep.ofModuleMonoidAlgebra`. -/
private abbrev finiteProjective_toRep_shortComplex
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    ShortComplex (Rep k G) :=
  ShortComplex.mk
    (Rep.ofModuleMonoidAlgebra.map S.f.hom.hom)
    (Rep.ofModuleMonoidAlgebra.map S.g.hom.hom)
    (by
      -- Forget the zero composite in `ModuleCat k[G]` and map it to `Rep k G`.
      simpa using
        congrArg
          (fun m ↦ Rep.ofModuleMonoidAlgebra.map m)
          (finiteProjective_underlying_moduleCat_zero (k := k) (G := G) S))

/-- Helper for Exercise 15-15.1-2: a short exact sequence of projective owners yields the expected
ambient short exact sequence in `Rep k G`. -/
private theorem finiteProjective_toRep_shortComplex_shortExact
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    (finiteProjective_toRep_shortComplex (k := k) (G := G) S).ShortExact := by
  have hMod :=
    finiteProjective_shortExact_underlying_moduleCat (k := k) (G := G) S hS
  -- After forgetting to `ModuleCat k[G]`, applying `Rep.ofModuleMonoidAlgebra` is exact.
  simpa [finiteProjective_toRep_shortComplex,
    finiteProjective_underlying_moduleCat_shortComplex] using
    hMod.map_of_exact (Rep.ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep k G)

/-- Helper for Exercise 15-15.1-2 (local copy of the split-exact bridge): a split exact sequence of
modules identifies the middle term with the product of the two outer terms. -/
private noncomputable def linearEquivProdOfRightSplitExact
    {R : Type u} [Ring R]
    {X₁ : Type u} [AddCommGroup X₁] [Module R X₁]
    {X₂ : Type u} [AddCommGroup X₂] [Module R X₂]
    {X₃ : Type u} [AddCommGroup X₃] [Module R X₃]
    (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃)
    (hf : Function.Injective f) (hexact : Function.Exact f g)
    (s : X₃ →ₗ[R] X₂) (hs : g.comp s = LinearMap.id) :
    (X₁ × X₃) ≃ₗ[R] X₂ := by
  -- Convert the split exact sequence to the canonical biproduct splitting in `ModuleCat`.
  let hexact' : LinearMap.range f = LinearMap.ker g := by
    simpa [LinearMap.exact_iff, eq_comm] using hexact
  exact
    ((ShortComplex.Splitting.ofExactOfSection _
      (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom f)
        (ModuleCat.ofHom g) hexact')
      (ModuleCat.ofHom s) (ModuleCat.hom_ext hs)
      (by simpa only [ModuleCat.mono_iff_injective] using hf)).isoBinaryBiproduct ≪≫
      ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv

/-- Helper for Exercise 15-15.1-2: over the field `k`, a short exact sequence of finite projective
owners splits at the module level (its underlying `ModuleCat k[G]` sequence has projective quotient,
hence is right split). This is the field-only `P_k(G)` analogue used to feed the module-level
Grothendieck relations. -/
private theorem finiteProjective_nonempty_linearEquiv_prod_field
    (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) (hS : S.ShortExact) :
    Nonempty (S.X₂.V ≃ₗ[k[G]] S.X₁.V × S.X₃.V) := by
  let Smod := finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G) S
  have hSmod : Smod.ShortExact :=
    finiteProjective_shortExact_underlying_moduleCat (k := k) (G := G) S hS
  have hsurj : Function.Surjective Smod.g.hom := hSmod.moduleCat_surjective_g
  have hinj : Function.Injective Smod.f.hom := hSmod.moduleCat_injective_f
  have hexact : Function.Exact Smod.f.hom Smod.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S := Smod)).1 hSmod.exact
  let _ : Module.Projective k[G] (Smod.X₃ : ModuleCat k[G]) := by
    change Module.Projective k[G] S.X₃.V; infer_instance
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property Smod.g.hom
      (LinearMap.id : Smod.X₃ →ₗ[k[G]] Smod.X₃) hsurj
  exact ⟨(linearEquivProdOfRightSplitExact Smod.f.hom Smod.g.hom hinj hexact s hs).symm⟩

/-- Helper for Exercise 15-15.1-2: tensoring a projective-owner short complex on the left by a
fixed finite-dimensional representation produces the owner short complex used in Serre's proof. -/
private abbrev tensor_projective_owner_shortComplex
    (V : FDRep k G) (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G)) :
    ShortComplex (FiniteProjectiveGroupAlgebraModule k G) :=
  let TRep :=
    (finiteProjective_toRep_shortComplex (k := k) (G := G) S).map
      (MonoidalCategory.tensorLeft ((forget₂ (FDRep k G) (Rep k G)).obj V))
  let fHom : (V ⊗ₚ S.X₁).V →ₗ[k[G]] (V ⊗ₚ S.X₂).V :=
    (Rep.toModuleMonoidAlgebra.map TRep.f).hom
  let gHom : (V ⊗ₚ S.X₂).V →ₗ[k[G]] (V ⊗ₚ S.X₃).V :=
    (Rep.toModuleMonoidAlgebra.map TRep.g).hom
  ShortComplex.mk
    (ObjectProperty.homMk (FGModuleCat.ofHom fHom))
    (ObjectProperty.homMk (FGModuleCat.ofHom gHom))
    (by
      -- The owner maps are built from the ambient tensor-left maps, so their composite vanishes
      -- after forgetting to `ModuleCat k[G]`.
      apply ObjectProperty.hom_ext
      have hFG :
          FGModuleCat.ofHom fHom ≫ FGModuleCat.ofHom gHom = 0 := by
        apply FGModuleCat.hom_ext
        have hmMor :
            Rep.toModuleMonoidAlgebra.map TRep.f ≫
              Rep.toModuleMonoidAlgebra.map TRep.g = 0 := by
          simpa using
            (TRep.map (Rep.toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat k[G])).zero
        have hm : gHom.comp fHom = 0 := by
          simpa [fHom, gHom, Functor.map_zero] using
            congrArg ModuleCat.Hom.hom hmMor
        simpa [FGModuleCat.ofHom] using hm
      simpa [fHom, gHom, FGModuleCat.ofHom] using hFG)

/-- Helper for Exercise 15-15.1-2: Serre's tensor-left exactness argument on `Rep k G` descends to
the corresponding owner short complex on finite projective modules. -/
private theorem tensor_projective_owner_shortExact
    (V : FDRep k G) (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G))
    (hS : S.ShortExact) :
    (tensor_projective_owner_shortComplex (k := k) (G := G) V S).ShortExact := by
  let TRep :=
    (finiteProjective_toRep_shortComplex (k := k) (G := G) S).map
      (MonoidalCategory.tensorLeft ((forget₂ (FDRep k G) (Rep k G)).obj V))
  have hRep :
      (finiteProjective_toRep_shortComplex (k := k) (G := G) S).ShortExact :=
    finiteProjective_toRep_shortComplex_shortExact (k := k) (G := G) S hS
  have hTensorRep : TRep.ShortExact := by
    -- Tensor-left exactness in `Rep k G` is the source-faithful core of Serre's argument.
    simpa [TRep] using FiniteProjectiveGroupAlgebraModule.rep_tensorLeft_shortExact (k := k) (G := G) V
      (finiteProjective_toRep_shortComplex (k := k) (G := G) S) hRep
  have hTensorMod :
      (finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G)
        (tensor_projective_owner_shortComplex (k := k) (G := G) V S)).ShortExact := by
    -- Forget the ambient tensor-left exact sequence back to `ModuleCat k[G]`, where the owner
    -- maps were packaged.
    simpa [tensor_projective_owner_shortComplex,
      finiteProjective_underlying_moduleCat_shortComplex, TRep, FGModuleCat.ofHom] using
      hTensorRep.map_of_exact (Rep.toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat k[G])
  exact finiteProjective_shortExact_of_underlying_moduleCat_shortExact
    (k := k) (G := G)
    (tensor_projective_owner_shortComplex (k := k) (G := G) V S)
    hTensorMod

/-- Tensoring a short exact sequence of finite projective representations with a fixed
finite-dimensional representation preserves the defining relation in `P_k(G)`. -/
theorem tensorProjectiveClass_middle_eq_left_add_right
    (V : FDRep k G) (S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G))
    (hS : Nonempty (S.X₂.V ≃ₗ[k[G]] S.X₁.V × S.X₃.V)) :
    [V ⊗ₚ S.X₂]ₚ₀ = [V ⊗ₚ S.X₁]ₚ₀ + [V ⊗ₚ S.X₃]ₚ₀ := by
  -- Route correction: keep Serre's route. Rebuild a genuine categorical split short exact
  -- sequence from the splitting, tensor the ambient `Rep k G` sequence on the left, then reflect
  -- that exactness back to the packaged owner short complex.
  obtain ⟨e⟩ := hS
  simpa [tensor_projective_owner_shortComplex] using
    Representation.finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := k) (G := G)
      (tensor_projective_owner_shortComplex (k := k) (G := G) V
        (splitShortComplexOfLinearEquivProd S.X₁ S.X₂ S.X₃ e))
      (finiteProjective_nonempty_linearEquiv_prod_field (k := k) (G := G) _
        (tensor_projective_owner_shortExact (k := k) (G := G) V
          (splitShortComplexOfLinearEquivProd S.X₁ S.X₂ S.X₃ e)
          (splitShortComplexOfLinearEquivProd_shortExact S.X₁ S.X₂ S.X₃ e)))

/-- Tensoring by a fixed finite-dimensional representation defines an additive map on the free
abelian group generated by finite projective representations. -/
private abbrev projectiveTensorLift (V : FDRep k G) :
    FreeAbelianGroup (FiniteProjectiveGroupAlgebraModule k G) →+
      P₀[k](G) :=
  FreeAbelianGroup.lift fun P ↦ [V ⊗ₚ P]ₚ₀

-- Proof sketch: each defining generator `[Y] - [X] - [Z]` of
-- `finiteProjectiveGroupAlgebraGrothendieckRelations k G` is sent to zero by the previous
-- tensorized short-exact-sequence relation.
/-- The tensor-product lift on projective classes factors through the Grothendieck quotient
`P_k(G)`. -/
private theorem finiteProjectiveGroupAlgebraGrothendieckRelations_le_projectiveTensorLift_ker
    (V : FDRep k G) :
    finiteProjectiveGroupAlgebraGrothendieckRelations k G ≤
      (projectiveTensorLift k G V).ker := by
  -- Evaluate a defining short-exact-sequence generator and apply the tensorized projective
  -- Grothendieck relation.
  change
    AddSubgroup.closure
      (Set.range fun S :
        { S : ShortComplex (FiniteProjectiveGroupAlgebraModule k G) //
          Nonempty (S.X₂.V ≃ₗ[k[G]] S.X₁.V × S.X₃.V) } ↦
          FreeAbelianGroup.of S.1.X₂ - FreeAbelianGroup.of S.1.X₁ -
            FreeAbelianGroup.of S.1.X₃) ≤
      (projectiveTensorLift k G V).ker
  refine (AddSubgroup.closure_le (K := (projectiveTensorLift k G V).ker)).2 ?_
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change [V ⊗ₚ S.X₂]ₚ₀ - [V ⊗ₚ S.X₁]ₚ₀ - [V ⊗ₚ S.X₃]ₚ₀ = 0
  rw [sub_eq_zero]
  have hrel := tensorProjectiveClass_middle_eq_left_add_right (k := k) (G := G) V S hS
  calc
    [V ⊗ₚ S.X₂]ₚ₀ - [V ⊗ₚ S.X₁]ₚ₀ =
        ([V ⊗ₚ S.X₁]ₚ₀ + [V ⊗ₚ S.X₃]ₚ₀) - [V ⊗ₚ S.X₁]ₚ₀ := by rw [hrel]
    _ = [V ⊗ₚ S.X₃]ₚ₀ := by abel

/-- Tensoring by a fixed finite-dimensional representation induces an additive endomorphism of
`P_k(G)`. -/
private def projectiveTensorEnd (V : FDRep k G) :
    P₀[k](G) →+ P₀[k](G) :=
  QuotientAddGroup.lift
    (finiteProjectiveGroupAlgebraGrothendieckRelations k G)
    (projectiveTensorLift k G V)
    (finiteProjectiveGroupAlgebraGrothendieckRelations_le_projectiveTensorLift_ker k G V)

/-- Helper for Exercise 15-15.1-2: forgetting an `FDRep` short complex simply views it as a short
complex in `Rep k G`. -/
private abbrev finiteRep_toRep_shortComplex
    (S : ShortComplex (FDRep k G)) :
    ShortComplex (Rep k G) :=
  S.map (forget₂ (FDRep k G) (Rep k G))

/-- Helper for Exercise 15-15.1-2: tensoring an `FDRep` short complex on the right by a fixed
projective owner yields the owner short complex on `S.Xᵢ ⊗ₚ P`. -/
private abbrev finiteRep_tensor_projective_owner_shortComplex
    (S : ShortComplex (FDRep k G)) (P : FiniteProjectiveGroupAlgebraModule k G) :
    ShortComplex (FiniteProjectiveGroupAlgebraModule k G) :=
  let TRep :=
    (finiteRep_toRep_shortComplex (k := k) (G := G) S).map
      (MonoidalCategory.tensorRight P.toRep)
  let fHom : (S.X₁ ⊗ₚ P).V →ₗ[k[G]] (S.X₂ ⊗ₚ P).V :=
    (Rep.toModuleMonoidAlgebra.map TRep.f).hom
  let gHom : (S.X₂ ⊗ₚ P).V →ₗ[k[G]] (S.X₃ ⊗ₚ P).V :=
    (Rep.toModuleMonoidAlgebra.map TRep.g).hom
  ShortComplex.mk
    (ObjectProperty.homMk (FGModuleCat.ofHom fHom))
    (ObjectProperty.homMk (FGModuleCat.ofHom gHom))
    (by
      -- The owner maps are obtained from the ambient tensor-right maps, so the zero composite is
      -- inherited from the `Rep` short complex.
      apply ObjectProperty.hom_ext
      have hFG :
          FGModuleCat.ofHom fHom ≫ FGModuleCat.ofHom gHom = 0 := by
        apply FGModuleCat.hom_ext
        have hmMor :
            Rep.toModuleMonoidAlgebra.map TRep.f ≫
              Rep.toModuleMonoidAlgebra.map TRep.g = 0 := by
          simpa using
            (TRep.map (Rep.toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat k[G])).zero
        have hm : gHom.comp fHom = 0 := by
          simpa [fHom, gHom, Functor.map_zero] using
            congrArg ModuleCat.Hom.hom hmMor
        simpa [FGModuleCat.ofHom] using hm
      simpa [fHom, gHom, FGModuleCat.ofHom] using hFG)

/-- Helper for Exercise 15-15.1-2: braiding identifies the ambient tensor-right short complex with
the tensor-left short exact sequence coming from `P.toFiniteRep`. -/
private theorem finiteRep_tensor_projective_owner_shortExact
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact)
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    (finiteRep_tensor_projective_owner_shortComplex (k := k) (G := G) S P).ShortExact := by
  let SRep := finiteRep_toRep_shortComplex (k := k) (G := G) S
  let TLeft := SRep.map (MonoidalCategory.tensorLeft P.toRep)
  let TRight := SRep.map (MonoidalCategory.tensorRight P.toRep)
  have hSRep : SRep.ShortExact := by
    -- Forget the finite-dimensional sequence to `Rep k G` before tensoring.
    simpa [SRep] using hS.map_of_exact (forget₂ (FDRep k G) (Rep k G))
  have hLeft : TLeft.ShortExact := by
    -- Serre's exactness input is the already-proved tensor-left exactness in `Rep k G`.
    simpa [SRep, TLeft] using
      FiniteProjectiveGroupAlgebraModule.rep_tensorLeft_shortExact
        (k := k) (G := G) P.toFiniteRep SRep hSRep
  have eRightLeft : TRight ≅ TLeft := by
    -- The symmetric braiding turns right tensoring by `P.toRep` into left tensoring by the same
    -- representation.
    refine ShortComplex.isoMk
      (β_ ((forget₂ (FDRep k G) (Rep k G)).obj S.X₁) P.toRep)
      (β_ ((forget₂ (FDRep k G) (Rep k G)).obj S.X₂) P.toRep)
      (β_ ((forget₂ (FDRep k G) (Rep k G)).obj S.X₃) P.toRep)
      ?_ ?_
    · simpa [SRep, TRight, TLeft, finiteRep_toRep_shortComplex] using
        (β_ ((forget₂ (FDRep k G) (Rep k G)).obj S.X₁) P.toRep).hom.naturality
          ((forget₂ (FDRep k G) (Rep k G)).map S.f)
    · simpa [SRep, TRight, TLeft, finiteRep_toRep_shortComplex] using
        (β_ ((forget₂ (FDRep k G) (Rep k G)).obj S.X₂) P.toRep).hom.naturality
          ((forget₂ (FDRep k G) (Rep k G)).map S.g)
  have hRight : TRight.ShortExact := by
    exact (ShortComplex.shortExact_iff_of_iso eRightLeft).2 hLeft
  have hRightMod :
      (finiteProjective_underlying_moduleCat_shortComplex (k := k) (G := G)
        (finiteRep_tensor_projective_owner_shortComplex (k := k) (G := G) S P)).ShortExact := by
    -- Forget the braided ambient exact sequence to `ModuleCat k[G]`, where the owner maps live.
    simpa [finiteRep_tensor_projective_owner_shortComplex,
      finiteProjective_underlying_moduleCat_shortComplex, TRight, FGModuleCat.ofHom] using
      hRight.map_of_exact (Rep.toModuleMonoidAlgebra : Rep k G ⥤ ModuleCat k[G])
  exact finiteProjective_shortExact_of_underlying_moduleCat_shortExact
    (k := k) (G := G)
    (finiteRep_tensor_projective_owner_shortComplex (k := k) (G := G) S P)
    hRightMod

/-- Tensoring a short exact sequence of finite-dimensional representations with a fixed finite
projective representation preserves the defining relation in `P_k(G)`. -/
theorem finiteRep_tensorProjectiveClass_middle_eq_left_add_right
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact)
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    [S.X₂ ⊗ₚ P]ₚ₀ = [S.X₁ ⊗ₚ P]ₚ₀ + [S.X₃ ⊗ₚ P]ₚ₀ := by
  -- Braid the ambient tensor-right sequence to the tensor-left exact sequence for `P.toFiniteRep`,
  -- then reflect that exactness back to the packaged owner short complex.
  simpa [finiteRep_tensor_projective_owner_shortComplex] using
    Representation.finiteProjectiveGroupAlgebraGrothendieckClass_middle_eq_left_add_right
      (A := k) (G := G)
      (finiteRep_tensor_projective_owner_shortComplex (k := k) (G := G) S P)
      (finiteProjective_nonempty_linearEquiv_prod_field (k := k) (G := G) _
        (finiteRep_tensor_projective_owner_shortExact (k := k) (G := G) S hS P))

/-- The tensor action of finite-dimensional representations on `P_k(G)` lifted to the free abelian
group on generators of `R_k(G)`. -/
private abbrev projectiveActionLift :
    FreeAbelianGroup (FDRep k G) →+
      AddMonoid.End (P₀[k](G)) :=
  FreeAbelianGroup.lift fun V ↦ projectiveTensorEnd k G V

-- Proof sketch: the previous theorem shows that the image of every short-exact-sequence generator
-- of `R_k(G)` is the zero endomorphism of `P_k(G)`.
/-- The tensor action on `P_k(G)` factors through the Grothendieck quotient `R_k(G)`. -/
private theorem finiteRepGrothendieckRelations_le_projectiveActionLift_ker :
    finiteRepGrothendieckRelations k G ≤ (projectiveActionLift k G).ker := by
  -- Evaluate a defining short-exact-sequence generator pointwise on `P₀[k](G)` and reduce to the
  -- tensor relation in the finite-representation variable.
  change
    AddSubgroup.closure
      (Set.range fun S : { S : ShortComplex (FDRep k G) // S.ShortExact } ↦
        FreeAbelianGroup.of S.1.X₂ - FreeAbelianGroup.of S.1.X₁ - FreeAbelianGroup.of S.1.X₃) ≤
      (projectiveActionLift k G).ker
  refine (AddSubgroup.closure_le (K := (projectiveActionLift k G).ker)).2 ?_
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  apply AddMonoidHom.ext
  intro y
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro P
    -- On a generator class, the pointwise action is the tensor-product class relation.
    change [S.X₂ ⊗ₚ P]ₚ₀ - [S.X₁ ⊗ₚ P]ₚ₀ - [S.X₃ ⊗ₚ P]ₚ₀ = 0
    rw [sub_eq_zero]
    have hrel :=
      finiteRep_tensorProjectiveClass_middle_eq_left_add_right (k := k) (G := G) S hS P
    calc
      [S.X₂ ⊗ₚ P]ₚ₀ - [S.X₁ ⊗ₚ P]ₚ₀ =
          ([S.X₁ ⊗ₚ P]ₚ₀ + [S.X₃ ⊗ₚ P]ₚ₀) - [S.X₁ ⊗ₚ P]ₚ₀ := by rw [hrel]
      _ = [S.X₃ ⊗ₚ P]ₚ₀ := by abel
  · intro a ha
    -- Negation is respected because the lifted action is additive.
    simpa using congrArg Neg.neg ha
  · intro a₁ a₂ ha₁ ha₂
    -- Addition is respected because the lifted action is additive.
    simpa using congrArg₂ HAdd.hAdd ha₁ ha₂

/-- Tensoring with classes in `R_k(G)` defines an additive action on `P_k(G)`. -/
private def projectiveActionHom :
    R₀[k](G) →+ AddMonoid.End (P₀[k](G)) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (projectiveActionLift k G)
    (finiteRepGrothendieckRelations_le_projectiveActionLift_ker k G)

/-- Helper for Exercise 15-15.1-2: the zero representation class acts trivially on projective
Grothendieck classes. -/
private theorem projectiveActionHom_zero_apply (z : P₀[k](G)) :
    projectiveActionHom k G 0 z = 0 := by
  exact congrArg (fun f : AddMonoid.End (P₀[k](G)) ↦ f z)
    ((projectiveActionHom k G).map_zero)

/-- Helper for Exercise 15-15.1-2: the descended tensor action is additive in the
representation-class variable. -/
private theorem projectiveActionHom_add_apply
    (x y : R₀[k](G)) (z : P₀[k](G)) :
    projectiveActionHom k G (x + y) z =
      projectiveActionHom k G x z + projectiveActionHom k G y z := by
  exact congrArg (fun f : AddMonoid.End (P₀[k](G)) ↦ f z)
    ((projectiveActionHom k G).map_add x y)

/-- Helper for Exercise 15-15.1-2: the descended tensor action sends negatives in the
representation-class variable to negatives. -/
private theorem projectiveActionHom_neg_apply
    (x : R₀[k](G)) (z : P₀[k](G)) :
    projectiveActionHom k G (-x) z = -projectiveActionHom k G x z := by
  exact congrArg (fun f : AddMonoid.End (P₀[k](G)) ↦ f z)
    ((projectiveActionHom k G).map_neg x)

/-- Helper for Exercise 15-15.1-2: on generator classes, the tensor action is associative via the
owner-level tensor associator. -/
private theorem finiteRep_mul_smul_projectiveClass
    (V W : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G))) [P]ₚ₀ =
      projectiveActionHom k G [V]₀ (projectiveActionHom k G [W]₀ [P]ₚ₀) := by
  -- Expand the quotient lifts on generator classes and compare the two tensor parenthesizations.
  change [((V ⊗ W) ⊗ₚ P)]ₚ₀ = [V ⊗ₚ (W ⊗ₚ P)]ₚ₀
  exact Representation.finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
    (A := k) (G := G)
    (tensorProjective_associator_nonempty_iso (k := k) (G := G) V W P)

/-- Tensor-product scalar multiplication makes `P_k(G)` into an `R_k(G)`-module. -/
instance finiteProjectiveGroupAlgebraGrothendieckGroup_module :
    Module (R₀[k](G)) (P₀[k](G)) where
  smul x y := projectiveActionHom k G x y
  one_smul := by
    intro y
    -- Descend to generator classes and compare `𝟙 ⊗ₚ P` with `P` through the owner-level
    -- isomorphism induced by the tensor left unitor in `Rep k G`.
    refine QuotientAddGroup.induction_on y ?_
    intro a
    refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
    · change projectiveActionHom k G (1 : R₀[k](G)) 0 = 0
      exact (projectiveActionHom k G (1 : R₀[k](G))).map_zero
    · intro P
      change [((𝟙_ (FDRep k G)) ⊗ₚ P)]ₚ₀ = [P]ₚ₀
      exact Representation.finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
        (A := k) (G := G) (one_tprod_nonempty_iso (k := k) (G := G) P)
    · intro a ha
      -- Negation is respected because the descended action is additive in the projective class.
      have ha' :
          projectiveActionHom k G (1 : R₀[k](G)) ↑(FreeAbelianGroup.of a) =
            ↑(FreeAbelianGroup.of a) := by
        simpa using ha
      change -projectiveActionHom k G (1 : R₀[k](G)) ↑(FreeAbelianGroup.of a) =
        -↑(FreeAbelianGroup.of a)
      rw [ha']
    · intro a₁ a₂ ha₁ ha₂
      -- Addition is respected because the descended action is additive in the projective class.
      have ha₁' :
          projectiveActionHom k G (1 : R₀[k](G)) ↑a₁ = ↑a₁ := by
        simpa using ha₁
      have ha₂' :
          projectiveActionHom k G (1 : R₀[k](G)) ↑a₂ = ↑a₂ := by
        simpa using ha₂
      change projectiveActionHom k G (1 : R₀[k](G)) (↑a₁ + ↑a₂) = ↑a₁ + ↑a₂
      calc
        projectiveActionHom k G (1 : R₀[k](G)) (↑a₁ + ↑a₂) =
            projectiveActionHom k G (1 : R₀[k](G)) ↑a₁ +
              projectiveActionHom k G (1 : R₀[k](G)) ↑a₂ := by
                exact (projectiveActionHom k G (1 : R₀[k](G))).map_add ↑a₁ ↑a₂
        _ = ↑a₁ + ↑a₂ := by rw [ha₁', ha₂']
  mul_smul := by
    intro x y z
    -- Descend to generator classes and reuse the associativity comparison already proved there.
    refine QuotientAddGroup.induction_on x ?_
    intro a
    refine QuotientAddGroup.induction_on y ?_
    intro b
    refine QuotientAddGroup.induction_on z ?_
    intro c
    refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
    · change
        projectiveActionHom k G (((0 : R₀[k](G)) * (b : R₀[k](G)))) (c : P₀[k](G)) =
          projectiveActionHom k G (0 : R₀[k](G))
            (projectiveActionHom k G (b : R₀[k](G)) (c : P₀[k](G)))
      rw [finiteRepGrothendieck_zero_mul, projectiveActionHom_zero_apply,
        projectiveActionHom_zero_apply]
    · intro V
      refine FreeAbelianGroup.induction_on b ?_ ?_ ?_ ?_
      · change
          projectiveActionHom k G (([V]₀ * (0 : R₀[k](G)))) (c : P₀[k](G)) =
            projectiveActionHom k G [V]₀
              (projectiveActionHom k G (0 : R₀[k](G)) (c : P₀[k](G)))
        rw [finiteRepGrothendieck_mul_zero, projectiveActionHom_zero_apply]
        exact (projectiveActionHom k G [V]₀).map_zero
      · intro W
        refine FreeAbelianGroup.induction_on c ?_ ?_ ?_ ?_
        · change
            projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G))) (0 : P₀[k](G)) =
              projectiveActionHom k G [V]₀
                (projectiveActionHom k G [W]₀ (0 : P₀[k](G)))
          have hW0 : projectiveActionHom k G [W]₀ (0 : P₀[k](G)) = 0 :=
            (projectiveActionHom k G [W]₀).map_zero
          have hV0 : projectiveActionHom k G [V]₀ (0 : P₀[k](G)) = 0 :=
            (projectiveActionHom k G [V]₀).map_zero
          rw [hW0, hV0]
          exact (projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G)))).map_zero
        · intro P
          exact finiteRep_mul_smul_projectiveClass (k := k) (G := G) V W P
        · intro c hc
          have hc' :
              projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G)))
                  (↑(FreeAbelianGroup.of c) : P₀[k](G)) =
                projectiveActionHom k G [V]₀
                  (projectiveActionHom k G [W]₀
                    (↑(FreeAbelianGroup.of c) : P₀[k](G))) := by
            simpa using hc
          change
            projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G)))
                (-↑(FreeAbelianGroup.of c) : P₀[k](G)) =
              projectiveActionHom k G [V]₀
                (projectiveActionHom k G [W]₀
                  (-↑(FreeAbelianGroup.of c) : P₀[k](G)))
          calc
            projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G)))
                (-↑(FreeAbelianGroup.of c) : P₀[k](G)) =
                -projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G)))
                  (↑(FreeAbelianGroup.of c) : P₀[k](G)) := by
                    simpa using
                      (projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G)))).map_neg
                        (↑(FreeAbelianGroup.of c) : P₀[k](G))
            _ = -projectiveActionHom k G [V]₀
                  (projectiveActionHom k G [W]₀
                    (↑(FreeAbelianGroup.of c) : P₀[k](G))) := by rw [hc']
            _ = projectiveActionHom k G [V]₀
                  (-projectiveActionHom k G [W]₀
                    (↑(FreeAbelianGroup.of c) : P₀[k](G))) := by
                      symm
                      simpa using
                        (projectiveActionHom k G [V]₀).map_neg
                          (projectiveActionHom k G [W]₀
                            (↑(FreeAbelianGroup.of c) : P₀[k](G)))
            _ = projectiveActionHom k G [V]₀
                  (projectiveActionHom k G [W]₀
                    (-↑(FreeAbelianGroup.of c) : P₀[k](G))) := by
                      symm
                      simpa using
                        (projectiveActionHom k G [W]₀).map_neg
                          (↑(FreeAbelianGroup.of c) : P₀[k](G))
        · intro c₁ c₂ hc₁ hc₂
          have hc₁' :
              projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G))) (↑c₁ : P₀[k](G)) =
                projectiveActionHom k G [V]₀
                  (projectiveActionHom k G [W]₀ (↑c₁ : P₀[k](G))) := by
            simpa using hc₁
          have hc₂' :
              projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G))) (↑c₂ : P₀[k](G)) =
                projectiveActionHom k G [V]₀
                  (projectiveActionHom k G [W]₀ (↑c₂ : P₀[k](G))) := by
            simpa using hc₂
          change
            projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G)))
                ((↑c₁ + ↑c₂ : P₀[k](G))) =
              projectiveActionHom k G [V]₀
                (projectiveActionHom k G [W]₀ ((↑c₁ + ↑c₂ : P₀[k](G))))
          calc
            projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G)))
                ((↑c₁ + ↑c₂ : P₀[k](G))) =
                projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G))) (↑c₁ : P₀[k](G)) +
                  projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G))) (↑c₂ : P₀[k](G)) := by
                    exact
                      (projectiveActionHom k G (([V]₀ * [W]₀ : R₀[k](G)))).map_add
                        (↑c₁ : P₀[k](G)) (↑c₂ : P₀[k](G))
            _ = projectiveActionHom k G [V]₀
                  (projectiveActionHom k G [W]₀ (↑c₁ : P₀[k](G))) +
                projectiveActionHom k G [V]₀
                  (projectiveActionHom k G [W]₀ (↑c₂ : P₀[k](G))) := by rw [hc₁', hc₂']
            _ = projectiveActionHom k G [V]₀
                  (projectiveActionHom k G [W]₀ (↑c₁ : P₀[k](G)) +
                    projectiveActionHom k G [W]₀ (↑c₂ : P₀[k](G))) := by
                      symm
                      exact
                        (projectiveActionHom k G [V]₀).map_add
                          (projectiveActionHom k G [W]₀ (↑c₁ : P₀[k](G)))
                          (projectiveActionHom k G [W]₀ (↑c₂ : P₀[k](G)))
            _ = projectiveActionHom k G [V]₀
                  (projectiveActionHom k G [W]₀ ((↑c₁ + ↑c₂ : P₀[k](G)))) := by
                      exact congrArg (projectiveActionHom k G [V]₀)
                        ((projectiveActionHom k G [W]₀).map_add
                          (↑c₁ : P₀[k](G)) (↑c₂ : P₀[k](G))).symm
      · intro b hb
        have hb' :
            projectiveActionHom k G (([V]₀ * ((↑(FreeAbelianGroup.of b) : R₀[k](G))) : R₀[k](G))) (↑c : P₀[k](G)) =
              projectiveActionHom k G [V]₀
                (projectiveActionHom k G ((↑(FreeAbelianGroup.of b) : R₀[k](G))) (↑c : P₀[k](G))) := by
          simpa using hb
        change
          projectiveActionHom k G (([V]₀ * (-((↑(FreeAbelianGroup.of b) : R₀[k](G)))) : R₀[k](G))) (↑c : P₀[k](G)) =
            projectiveActionHom k G [V]₀
              (projectiveActionHom k G (-((↑(FreeAbelianGroup.of b) : R₀[k](G)))) (↑c : P₀[k](G)))
        calc
          projectiveActionHom k G
              (([V]₀ * (-((↑(FreeAbelianGroup.of b) : R₀[k](G)))) : R₀[k](G))) (↑c : P₀[k](G)) =
              -projectiveActionHom k G
                (([V]₀ * ((↑(FreeAbelianGroup.of b) : R₀[k](G))) : R₀[k](G))) (↑c : P₀[k](G)) := by
                  rw [finiteRepGrothendieck_mul_neg, projectiveActionHom_neg_apply]
          _ = -projectiveActionHom k G [V]₀
                (projectiveActionHom k G ((↑(FreeAbelianGroup.of b) : R₀[k](G))) (↑c : P₀[k](G))) := by
                  rw [hb']
          _ = projectiveActionHom k G [V]₀
                (-projectiveActionHom k G ((↑(FreeAbelianGroup.of b) : R₀[k](G))) (↑c : P₀[k](G))) := by
                  symm
                  simpa using
                    (projectiveActionHom k G [V]₀).map_neg
                      (projectiveActionHom k G ((↑(FreeAbelianGroup.of b) : R₀[k](G))) (↑c : P₀[k](G)))
          _ = projectiveActionHom k G [V]₀
                (projectiveActionHom k G (-((↑(FreeAbelianGroup.of b) : R₀[k](G)))) (↑c : P₀[k](G))) := by
                  rw [projectiveActionHom_neg_apply]
      · intro b₁ b₂ hb₁ hb₂
        have hb₁' :
            projectiveActionHom k G (([V]₀ * (↑b₁ : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) =
              projectiveActionHom k G [V]₀
                (projectiveActionHom k G (↑b₁ : R₀[k](G)) (↑c : P₀[k](G))) := by
          simpa using hb₁
        have hb₂' :
            projectiveActionHom k G (([V]₀ * (↑b₂ : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) =
              projectiveActionHom k G [V]₀
                (projectiveActionHom k G (↑b₂ : R₀[k](G)) (↑c : P₀[k](G))) := by
          simpa using hb₂
        change
          projectiveActionHom k G (([V]₀ * ((↑b₁ + ↑b₂ : R₀[k](G))) : R₀[k](G))) (↑c : P₀[k](G)) =
            projectiveActionHom k G [V]₀
              (projectiveActionHom k G ((↑b₁ + ↑b₂ : R₀[k](G))) (↑c : P₀[k](G)))
        calc
          projectiveActionHom k G (([V]₀ * ((↑b₁ + ↑b₂ : R₀[k](G))) : R₀[k](G))) (↑c : P₀[k](G)) =
              projectiveActionHom k G (([V]₀ * (↑b₁ : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) +
                projectiveActionHom k G (([V]₀ * (↑b₂ : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) := by
                  rw [finiteRepGrothendieck_mul_add, projectiveActionHom_add_apply]
          _ = projectiveActionHom k G [V]₀
                (projectiveActionHom k G (↑b₁ : R₀[k](G)) (↑c : P₀[k](G))) +
              projectiveActionHom k G [V]₀
                (projectiveActionHom k G (↑b₂ : R₀[k](G)) (↑c : P₀[k](G))) := by
                  rw [hb₁', hb₂']
          _ = projectiveActionHom k G [V]₀
                (projectiveActionHom k G (↑b₁ : R₀[k](G)) (↑c : P₀[k](G)) +
                  projectiveActionHom k G (↑b₂ : R₀[k](G)) (↑c : P₀[k](G))) := by
                    symm
                    exact
                      (projectiveActionHom k G [V]₀).map_add
                        (projectiveActionHom k G (↑b₁ : R₀[k](G)) (↑c : P₀[k](G)))
                        (projectiveActionHom k G (↑b₂ : R₀[k](G)) (↑c : P₀[k](G)))
          _ = projectiveActionHom k G [V]₀
                (projectiveActionHom k G ((↑b₁ + ↑b₂ : R₀[k](G))) (↑c : P₀[k](G))) := by
                    rw [projectiveActionHom_add_apply]
    · intro a ha
      have ha' :
          projectiveActionHom k G (((↑(FreeAbelianGroup.of a) : R₀[k](G)) * (↑b : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) =
            projectiveActionHom k G (↑(FreeAbelianGroup.of a) : R₀[k](G))
              (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G))) := by
        simpa using ha
      change
        projectiveActionHom k G (((-((↑(FreeAbelianGroup.of a) : R₀[k](G))) * (↑b : R₀[k](G)) : R₀[k](G)))) (↑c : P₀[k](G)) =
          projectiveActionHom k G (-((↑(FreeAbelianGroup.of a) : R₀[k](G))))
            (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G)))
      calc
        projectiveActionHom k G
            (((-((↑(FreeAbelianGroup.of a) : R₀[k](G))) * (↑b : R₀[k](G)) : R₀[k](G)))) (↑c : P₀[k](G)) =
            -projectiveActionHom k G
              ((((↑(FreeAbelianGroup.of a) : R₀[k](G)) * (↑b : R₀[k](G)) : R₀[k](G)))) (↑c : P₀[k](G)) := by
                rw [finiteRepGrothendieck_neg_mul, projectiveActionHom_neg_apply]
        _ = -projectiveActionHom k G (↑(FreeAbelianGroup.of a) : R₀[k](G))
              (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G))) := by
                rw [ha']
        _ = projectiveActionHom k G (-((↑(FreeAbelianGroup.of a) : R₀[k](G))))
              (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G))) := by
                symm
                exact
                  projectiveActionHom_neg_apply (k := k) (G := G)
                    (↑(FreeAbelianGroup.of a) : R₀[k](G))
                    (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G)))
    · intro a₁ a₂ ha₁ ha₂
      have ha₁' :
          projectiveActionHom k G (((↑a₁ : R₀[k](G)) * (↑b : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) =
            projectiveActionHom k G (↑a₁ : R₀[k](G))
              (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G))) := by
        simpa using ha₁
      have ha₂' :
          projectiveActionHom k G (((↑a₂ : R₀[k](G)) * (↑b : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) =
            projectiveActionHom k G (↑a₂ : R₀[k](G))
              (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G))) := by
        simpa using ha₂
      change
        projectiveActionHom k G ((((↑a₁ + ↑a₂ : R₀[k](G))) * (↑b : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) =
          projectiveActionHom k G ((↑a₁ + ↑a₂ : R₀[k](G)))
            (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G)))
      calc
        projectiveActionHom k G ((((↑a₁ + ↑a₂ : R₀[k](G))) * (↑b : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) =
            projectiveActionHom k G ((↑a₁ * (↑b : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) +
              projectiveActionHom k G ((↑a₂ * (↑b : R₀[k](G)) : R₀[k](G))) (↑c : P₀[k](G)) := by
                rw [finiteRepGrothendieck_add_mul, projectiveActionHom_add_apply]
        _ = projectiveActionHom k G (↑a₁ : R₀[k](G))
              (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G))) +
            projectiveActionHom k G (↑a₂ : R₀[k](G))
              (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G))) := by
                rw [ha₁', ha₂']
        _ = projectiveActionHom k G ((↑a₁ + ↑a₂ : R₀[k](G)))
              (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G))) := by
                symm
                exact
                  projectiveActionHom_add_apply (k := k) (G := G)
                    (↑a₁ : R₀[k](G)) (↑a₂ : R₀[k](G))
                    (projectiveActionHom k G (↑b : R₀[k](G)) (↑c : P₀[k](G)))
  smul_zero := by
    intro x
    -- The descended action is additive in the projective Grothendieck variable.
    change projectiveActionHom k G x 0 = 0
    exact (projectiveActionHom k G x).map_zero
  smul_add := by
    intro x y z
    -- The descended action is additive in the projective Grothendieck variable.
    change projectiveActionHom k G x (y + z) =
      projectiveActionHom k G x y + projectiveActionHom k G x z
    exact (projectiveActionHom k G x).map_add y z
  add_smul := by
    intro x y z
    -- Additivity in the representation-variable is built into the quotient lift
    -- `projectiveActionHom`.
    change projectiveActionHom k G (x + y) z =
      projectiveActionHom k G x z + projectiveActionHom k G y z
    exact congrArg (fun f : AddMonoid.End (P₀[k](G)) ↦ f z)
      ((projectiveActionHom k G).map_add x y)
  zero_smul := by
    intro z
    -- The zero class acts by the zero additive endomorphism.
    change projectiveActionHom k G 0 z = 0
    exact congrArg (fun f : AddMonoid.End (P₀[k](G)) ↦ f z)
      ((projectiveActionHom k G).map_zero)

/-- Scalar multiplication of a projective Grothendieck class is represented by tensor product. -/
theorem finiteProjectiveGroupAlgebraGrothendieckClass_smul
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    [V]₀ • [P]ₚ₀ = [V ⊗ₚ P]ₚ₀ := by
  -- On generator classes, scalar multiplication is the defining quotient lift.
  rfl

/-- Helper for Exercise 15-15.1-2: forgetting projectivity commutes with tensoring a
finite-dimensional representation with a finite projective `k[G]`-module. -/
private noncomputable def fdRepIsoOfRho (τ : FDRep k G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    ext x
    rfl

/-- Helper for Exercise 15-15.1-2: forgetting projectivity commutes with tensoring a
finite-dimensional representation with a finite projective `k[G]`-module. -/
private theorem projective_tensor_toFiniteRep_class_eq
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    [ (V ⊗ₚ P).toFiniteRep ]₀ = [ V ⊗ P.toFiniteRep ]₀ := by
  let τ₁ : FDRep k G := (V ⊗ₚ P).toFiniteRep
  let τ₂ : FDRep k G := (V ⊗ P.toFiniteRep : FDRep k G)
  let eRep : ((forget₂ (FDRep k G) (Rep k G)).obj τ₂) ≅ Rep.of τ₁.ρ := by
    -- Forgetting the projective tensor object to `Rep k G` yields the same `Rep` tensor product
    -- as the ordinary finite-representation tensor.
    simpa [τ₁, τ₂, FiniteProjectiveGroupAlgebraModule.tprod,
      FiniteProjectiveGroupAlgebraModule.toFiniteRep, FiniteProjectiveGroupAlgebraModule.toRep] using
      Rep.unitIso ((forget₂ (FDRep k G) (Rep k G)).obj τ₂)
  let e : FDRep.of τ₂.ρ ≅ FDRep.of τ₁.ρ :=
    ⟨(FDRep.forget₂HomLinearEquiv (FDRep.of τ₂.ρ) (FDRep.of τ₁.ρ)) eRep.hom,
      (FDRep.forget₂HomLinearEquiv (FDRep.of τ₁.ρ) (FDRep.of τ₂.ρ)) eRep.inv,
      by
        apply (forget₂ (FDRep k G) (Rep k G)).map_injective
        change eRep.hom ≫ eRep.inv = 𝟙 _
        exact eRep.hom_inv_id,
      by
        apply (forget₂ (FDRep k G) (Rep k G)).map_injective
        change eRep.inv ≫ eRep.hom = 𝟙 _
        exact eRep.inv_hom_id⟩
  -- Compare both classes through the same rebundled owner of the common `Rep` tensor product.
  refine finiteRepGrothendieckClass_eq_of_nonempty_iso ?_
  exact ⟨(fdRepIsoOfRho (k := k) (G := G) τ₁).trans
    (e.symm.trans (fdRepIsoOfRho (k := k) (G := G) τ₂).symm)⟩

/-- Helper for Exercise 15-15.1-2: the Cartan homomorphism matches the tensor action on generator
classes. -/
private theorem cartanHom_smul_on_generator_classes
    (V : FDRep k G) (P : FiniteProjectiveGroupAlgebraModule k G) :
    cartanHom k G ([V]₀ • [P]ₚ₀) = [V]₀ * cartanHom k G [P]ₚ₀ := by
  -- Reduce both sides to the same tensor-product class in `R₀[k](G)`.
  rw [finiteProjectiveGroupAlgebraGrothendieckClass_smul, cartanHom_projectiveClass_eq]
  change [ (V ⊗ₚ P).toFiniteRep ]₀ = [V]₀ * [P.toFiniteRep]₀
  rw [finiteRepGrothendieckClass_mul]
  exact projective_tensor_toFiniteRep_class_eq (k := k) (G := G) V P

-- Proof sketch: expand the tensor-product actions on `P_k(G)` and `R_k(G)` via the quotient lifts
-- above, using that forgetting projectivity commutes with tensoring by a fixed finite-dimensional
-- representation.
/-- Exercise 15-15.1-2: the Cartan homomorphism is `R_k(G)`-linear for the tensor-product action,
so `c (x • y) = x • c(y)` for `x ∈ R_k(G)` and `y ∈ P_k(G)`. -/
theorem cartanHom_smul
    (x : R₀[k](G)) (y : P₀[k](G)) :
    cartanHom k G (x • y) = x • cartanHom k G y := by
  -- Descend the generator computation through the two Grothendieck quotients.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine QuotientAddGroup.induction_on y ?_
  intro b
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    refine FreeAbelianGroup.induction_on b ?_ ?_ ?_ ?_
    · simp
    · intro P
      exact cartanHom_smul_on_generator_classes (k := k) (G := G) V P
    · intro b hb
      simp [smul_neg, map_neg, mul_neg, hb]
    · intro b₁ b₂ hb₁ hb₂
      simp [smul_add, mul_add, map_add, hb₁, hb₂]
  · intro a ha
    simp [neg_smul, neg_mul, map_neg, ha]
  · intro a₁ a₂ ha₁ ha₂
    simp [add_smul, add_mul, map_add, ha₁, ha₂]

end CartanTensorCompatibility

end Representation
