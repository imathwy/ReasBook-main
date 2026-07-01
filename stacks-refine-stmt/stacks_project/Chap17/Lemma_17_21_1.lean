import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import stacks_project.LinearAlgebra.PowerOperations
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Lemma_17_16_2

open scoped AlgebraicGeometry TensorProduct
open CategoryTheory Opposite TensorProduct
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.21.1:
- primary domain: exterior and symmetric power constructions on `\mathcal O_X`-module sheaves;
- inspected owner declarations:
  `AlgebraicGeometry.ringedSpaceRingCatSheaf`,
  `ModuleCat.exteriorPower.map`,
  `SymmetricPower.tprod`,
  `PresheafOfModules.sheafification`;
- best owner abstraction: the ambient owner is the existing ringed-space module category
  `(RingedSpace.Modules X)`, and the source-facing objects are the exterior and symmetric power
  sheaves obtained by sheafifying the sectionwise power presheaves;
- primitive data: for each open set `U`, the module `ℱ(U)` over `Γ(U, \mathcal O_X)` together with
  the restriction maps of `ℱ`;
- derived API: the induced restriction maps on exterior and symmetric powers, and the sheafified
  owners `Λ^[n] ℱ` and `Symm[n] ℱ`; the sheafification mechanism is derived infrastructure, not
  primitive source-facing data of these owners.

Source/core/bridge triage:
- `source-facing`: `exteriorPowerSheaf`, `symmetricPowerSheaf`, and their textbook notation;
- `core/canonical`: `(RingedSpace.ringCatSheaf X)`, sectionwise `exteriorPower` / `SymmetricPower`,
  and `PresheafOfModules.sheafification`;
- `bridge/view`: the sectionwise restriction maps and their presheaf-axiom lemmas. -/

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X

private local instance exteriorPowerModule
    {R S M : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] (n : ℕ) :
    Module R ↥(⋀[S]^n M) :=
  Module.compHom _ (algebraMap R S)

private local instance symmetricPowerModule
    {R S M : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] (n : ℕ) :
    Module R (Sym[S] (SymmetricPower.UFin n) M) :=
  Module.compHom _ (algebraMap R S)

/-- The commutative ring of sections of the structure sheaf over an open set. -/
private abbrev sectionRing (X : RingedSpace.{u}) (U : (Opens X)ᵒᵖ) :=
  X.presheaf.obj U

/-- A semilinear map induces a restriction map on exterior powers after restricting scalars along
the ambient algebra. -/
private noncomputable def exteriorPowerRestrict
    {R S M N : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (f : M →ₗ[R] N) :
    ⋀[R]^n M →ₗ[R] ⋀[S]^n N := by
  letI : Module R ↥(⋀[S]^n N) := exteriorPowerModule n
  letI : IsScalarTower R S ↥(⋀[S]^n N) := IsScalarTower.of_compHom R S ↥(⋀[S]^n N)
  let ιN : N [⋀^Fin n]→ₗ[S] ↥(⋀[S]^n N) := exteriorPower.ιMulti S n
  let ιN' : N [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) :=
    { toMultilinearMap :=
        { toFun := ιN
          map_update_add' := by
            intro _ m i x y
            simpa using ιN.map_update_add m i x y
          map_update_smul' := by
            intro _ m i r x
            simpa only [algebraMap_smul S] using ιN.map_update_smul m i (algebraMap R S r) x }
      map_eq_zero_of_eq' := by
        intro m i j hij hne
        exact ιN.map_eq_zero_of_eq m hij hne }
  exact show ⋀[R]^n M →ₗ[R] ⋀[S]^n N from
    exteriorPower.alternatingMapLinearEquiv (ιN'.compLinearMap f)

/-- A semilinear map induces a restriction map on symmetric powers after restricting scalars along
the ambient algebra. -/
private noncomputable def symmetricPowerRestrict
    {R S M N : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (f : M →ₗ[R] N) :
    Sym[R] (SymmetricPower.UFin n) M →ₗ[R] Sym[S] (SymmetricPower.UFin n) N := by
  letI : Module R (Sym[S] (SymmetricPower.UFin n) N) := symmetricPowerModule n
  letI : IsScalarTower R S (Sym[S] (SymmetricPower.UFin n) N) :=
    IsScalarTower.of_compHom R S (Sym[S] (SymmetricPower.UFin n) N)
  let tprodN :
      MultilinearMap S (fun _ : SymmetricPower.UFin n ↦ N)
        (Sym[S] (SymmetricPower.UFin n) N) :=
    SymmetricPower.tprod S
  let tprodN' :
      MultilinearMap R (fun _ : SymmetricPower.UFin n ↦ N)
        (Sym[S] (SymmetricPower.UFin n) N) :=
    { toFun := tprodN
      map_update_add' := by
        intro _ m i x y
        simpa using tprodN.map_update_add m i x y
      map_update_smul' := by
        intro _ m i r x
        simpa only [algebraMap_smul S] using tprodN.map_update_smul m i (algebraMap R S r) x }
  let tensorLift :
      (⨂[R] (_ : SymmetricPower.UFin n), M) →ₗ[R] Sym[S] (SymmetricPower.UFin n) N :=
    PiTensorProduct.lift
      (tprodN'.compLinearMap fun _ ↦ f)
  have hrel :
      addConGen (SymmetricPower.Rel R (SymmetricPower.UFin n) M) ≤
        AddCon.ker tensorLift.toAddMonoidHom := by
    intro x y h
    induction h with
    | of _ _ hrel =>
        cases hrel with
        | perm e m =>
            change tensorLift (PiTensorProduct.tprod R (fun i ↦ m i)) =
              tensorLift (PiTensorProduct.tprod R (fun i ↦ m (e i)))
            simp only [tensorLift, PiTensorProduct.lift.tprod]
            exact (SymmetricPower.tprod_equiv e (f ∘ m)).symm
    | refl => rfl
    | symm hxy ih => exact ih.symm
    | trans hxy hyz ihxy ihyz => exact ihxy.trans ihyz
    | add hxy hyz ihxy ihyz => simpa using congrArg₂ (· + ·) ihxy ihyz
  let g : Sym[R] (SymmetricPower.UFin n) M →+ Sym[S] (SymmetricPower.UFin n) N :=
    AddCon.lift _ tensorLift.toAddMonoidHom hrel
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro r q
        refine AddCon.induction_on q ?_
        intro x
        change tensorLift (r • x) = r • tensorLift x
        simp [tensorLift] }

private abbrev exteriorPowerPresheafObj
    (ℱ : ModX) (n : ℕ) (U : (Opens X)ᵒᵖ) :=
  ModuleCat.of (sectionRing X U) (⋀[sectionRing X U]^n (ℱ.val.obj U))

private abbrev symmetricPowerPresheafObj
    (ℱ : ModX) (n : ℕ) (U : (Opens X)ᵒᵖ) :=
  ModuleCat.of (sectionRing X U) (Sym[sectionRing X U] (SymmetricPower.UFin n) (ℱ.val.obj U))

-- The sectionwise exterior-power restriction map.
private noncomputable def exteriorPowerPresheafMap
    (ℱ : ModX) (n : ℕ)
    {U V : (Opens X)ᵒᵖ} (ρ : U ⟶ V) :
    exteriorPowerPresheafObj ℱ n U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map ρ).hom).obj
        (exteriorPowerPresheafObj ℱ n V) := by
  let R := sectionRing X U
  let S := sectionRing X V
  let M := ℱ.val.obj U
  let N := ℱ.val.obj V
  letI : Algebra R S := (X.presheaf.map ρ).hom.toAlgebra
  letI : Module R N := Module.compHom N (X.presheaf.map ρ).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  letI : Module R ↥(⋀[S]^n N) := Module.compHom _ (algebraMap R S)
  let fUV : M →ₗ[R] N := (ℱ.val.map ρ).hom
  change ModuleCat.of R (⋀[R]^n M) ⟶ ModuleCat.of R ↥(⋀[S]^n N)
  exact ModuleCat.ofHom <| exteriorPowerRestrict n fUV

/-- The sectionwise symmetric-power restriction map. -/
private noncomputable def symmetricPowerPresheafMap
    (ℱ : ModX) (n : ℕ)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    symmetricPowerPresheafObj ℱ n U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
        (symmetricPowerPresheafObj ℱ n V) := by
  let R := sectionRing X U
  let S := sectionRing X V
  let M := ℱ.val.obj U
  let N := ℱ.val.obj V
  letI : Algebra R S := (X.presheaf.map i).hom.toAlgebra
  letI : Module R N := Module.compHom N (X.presheaf.map i).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  letI : Module R (Sym[S] (SymmetricPower.UFin n) N) := Module.compHom _ (algebraMap R S)
  let fUV : M →ₗ[R] N := (ℱ.val.map i).hom
  change ModuleCat.of R (Sym[R] (SymmetricPower.UFin n) M) ⟶
    ModuleCat.of R (Sym[S] (SymmetricPower.UFin n) N)
  exact ModuleCat.ofHom <| symmetricPowerRestrict n fUV

private theorem exteriorPowerPresheafMap_id
    (ℱ : ModX) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    exteriorPowerPresheafMap ℱ n (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (exteriorPowerPresheafObj ℱ n U) := sorry

private theorem exteriorPowerPresheafMap_comp
    (ℱ : ModX) (n : ℕ)
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    exteriorPowerPresheafMap ℱ n (i ≫ j) =
      exteriorPowerPresheafMap ℱ n i ≫
        (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
          (exteriorPowerPresheafMap ℱ n j) ≫
        (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
          (X.presheaf.map j).hom (X.presheaf.map (i ≫ j)).hom
          (congrArg CommRingCat.Hom.hom (X.presheaf.map_comp i j))).inv.app
          (exteriorPowerPresheafObj ℱ n W) := sorry

private theorem symmetricPowerPresheafMap_id
    (ℱ : ModX) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    symmetricPowerPresheafMap ℱ n (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (symmetricPowerPresheafObj ℱ n U) := sorry

private theorem symmetricPowerPresheafMap_comp
    (ℱ : ModX) (n : ℕ)
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    symmetricPowerPresheafMap ℱ n (i ≫ j) =
      symmetricPowerPresheafMap ℱ n i ≫
        (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
          (symmetricPowerPresheafMap ℱ n j) ≫
        (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
          (X.presheaf.map j).hom (X.presheaf.map (i ≫ j)).hom
          (congrArg CommRingCat.Hom.hom (X.presheaf.map_comp i j))).inv.app
          (symmetricPowerPresheafObj ℱ n W) := sorry

/-- The presheaf `U ↦ \bigwedge^n_{\mathcal O_X(U)} \mathcal F(U)`. -/
noncomputable def exteriorPowerPresheaf
    (ℱ : ModX) (n : ℕ) :
    PresheafOfModules (RingedSpace.ringCatSheaf X).obj where
  obj U := exteriorPowerPresheafObj ℱ n U
  map := exteriorPowerPresheafMap ℱ n
  map_id U := exteriorPowerPresheafMap_id ℱ n U
  map_comp i j := exteriorPowerPresheafMap_comp ℱ n i j

/-- The presheaf `U ↦ \operatorname{Sym}^n_{\mathcal O_X(U)} \mathcal F(U)`. -/
noncomputable def symmetricPowerPresheaf
    (ℱ : ModX) (n : ℕ) :
    PresheafOfModules (RingedSpace.ringCatSheaf X).obj where
  obj U := symmetricPowerPresheafObj ℱ n U
  map := symmetricPowerPresheafMap ℱ n
  map_id U := symmetricPowerPresheafMap_id ℱ n U
  map_comp i j := symmetricPowerPresheafMap_comp ℱ n i j

/-- The `n`th exterior-power sheaf of `ℱ`, obtained by sheafifying the sectionwise exterior-power
presheaf. -/
noncomputable abbrev exteriorPowerSheaf
    (ℱ : ModX) (n : ℕ) :
    ModX :=
  (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj
    (exteriorPowerPresheaf ℱ n)

/-- The `n`th symmetric-power sheaf of `ℱ`, obtained by sheafifying the sectionwise symmetric-power
presheaf. -/
noncomputable abbrev symmetricPowerSheaf
    (ℱ : ModX) (n : ℕ) :
    ModX :=
  (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj
    (symmetricPowerPresheaf ℱ n)

/-- `exteriorPowerSheaf` is definitionally the sheafification of `exteriorPowerPresheaf`. -/
theorem exteriorPowerSheaf_eq_sheafification
    (ℱ : ModX) (n : ℕ) :
    exteriorPowerSheaf ℱ n =
      (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj
        (exteriorPowerPresheaf ℱ n) :=
  rfl

/-- `symmetricPowerSheaf` is definitionally the sheafification of `symmetricPowerPresheaf`. -/
theorem symmetricPowerSheaf_eq_sheafification
    (ℱ : ModX) (n : ℕ) :
    symmetricPowerSheaf ℱ n =
      (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj
        (symmetricPowerPresheaf ℱ n) :=
  rfl

/-- The inverse of the sheafification counit for the underlying presheaf of a sheaf of
`\mathcal O_X`-modules. -/
private noncomputable abbrev sheafificationCounitInv
    (ℱ : ModX) :
    ℱ ⟶ (moduleSheafification X.sheaf).obj ℱ.val := by
  let e := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  exact (e.symm.app ℱ).hom

/-- The map on symmetric-power presheaves induced by a morphism of `\mathcal O_X`-modules. -/
private noncomputable def symmetricPowerPresheafHom
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    symmetricPowerPresheaf ℱ n ⟶ symmetricPowerPresheaf 𝒢 n where
  app U := by
    let R := sectionRing X U
    letI : CommRing R := by infer_instance
    let Mℱ : ModuleCat R := ℱ.val.obj U
    let M𝒢 : ModuleCat R := 𝒢.val.obj U
    let fU : Mℱ →ₗ[R] M𝒢 := (φ.val.app U).hom
    exact ModuleCat.ofHom (SymmetricPower.map n fU)
  naturality := by
    intro U V i
    sorry

/-- The map on exterior-power presheaves induced by a morphism of `\mathcal O_X`-modules. -/
private noncomputable def exteriorPowerPresheafHom
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    exteriorPowerPresheaf ℱ n ⟶ exteriorPowerPresheaf 𝒢 n where
  app U := by
    let R := sectionRing X U
    letI : CommRing R := by infer_instance
    let Mℱ : ModuleCat R := ℱ.val.obj U
    let M𝒢 : ModuleCat R := 𝒢.val.obj U
    let fU : Mℱ →ₗ[R] M𝒢 := (φ.val.app U).hom
    exact ModuleCat.ofHom (exteriorPower.map n fU)
  naturality := by
    intro U V i
    sorry

/-- The map on symmetric-power sheaves induced by a morphism of `\mathcal O_X`-modules. -/
noncomputable abbrev symmetricPowerMap
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    symmetricPowerSheaf ℱ n ⟶ symmetricPowerSheaf 𝒢 n :=
  show symmetricPowerSheaf ℱ n ⟶ symmetricPowerSheaf 𝒢 n from
    (moduleSheafification X.sheaf).map (symmetricPowerPresheafHom n φ)

/-- The map on exterior-power sheaves induced by a morphism of `\mathcal O_X`-modules. -/
noncomputable abbrev exteriorPowerMap
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    exteriorPowerSheaf ℱ n ⟶ exteriorPowerSheaf 𝒢 n :=
  show exteriorPowerSheaf ℱ n ⟶ exteriorPowerSheaf 𝒢 n from
    (moduleSheafification X.sheaf).map (exteriorPowerPresheafHom n φ)

/-- The presheaf-level left tensor map
`ℱ(U) ⊗ Sym^n(𝒢(U)) → Sym^(n + 1)(𝒢(U))`
induced by a morphism `ℱ ⟶ 𝒢`. -/
private noncomputable def symmetricPowerLeftTensorPresheafMap
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    PresheafOfModules.Monoidal.tensorObj ℱ.val (symmetricPowerPresheaf 𝒢 n) ⟶
      symmetricPowerPresheaf 𝒢 (n + 1) where
  app U := by
    let R := sectionRing X U
    letI : CommRing R := by infer_instance
    let Mℱ : ModuleCat R := ℱ.val.obj U
    let M𝒢 : ModuleCat R := 𝒢.val.obj U
    let fU : Mℱ →ₗ[R] M𝒢 := (φ.val.app U).hom
    change ModuleCat.of R (Mℱ ⊗[R] Sym[R] (SymmetricPower.UFin n) M𝒢) ⟶
      ModuleCat.of R (Sym[R] (SymmetricPower.UFin (n + 1)) M𝒢)
    exact ModuleCat.ofHom (SymmetricPower.leftTensorMap n fU)
  naturality := by
    intro U V i
    sorry

/-- The presheaf-level left tensor map
`ℱ(U) ⊗ \bigwedge^n(𝒢(U)) → \bigwedge^(n + 1)(𝒢(U))`
induced by a morphism `ℱ ⟶ 𝒢`. -/
private noncomputable def exteriorPowerLeftTensorPresheafMap
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    PresheafOfModules.Monoidal.tensorObj ℱ.val (exteriorPowerPresheaf 𝒢 n) ⟶
      exteriorPowerPresheaf 𝒢 (n + 1) where
  app U := by
    let R := sectionRing X U
    letI : CommRing R := by infer_instance
    let Mℱ : ModuleCat R := ℱ.val.obj U
    let M𝒢 : ModuleCat R := 𝒢.val.obj U
    let fU : Mℱ →ₗ[R] M𝒢 := (φ.val.app U).hom
    change ModuleCat.of R (Mℱ ⊗[R] ⋀[R]^n M𝒢) ⟶
      ModuleCat.of R (⋀[R]^(n + 1) M𝒢)
    exact ModuleCat.ofHom (exteriorPower.leftTensorMap n fU)
  naturality := by
    intro U V i
    sorry

/-- The canonical morphism
`ℱ ⊗ Symm[n] 𝒢 ⟶ Symm[n + 1] 𝒢`
induced by a morphism `ℱ ⟶ 𝒢`. -/
noncomputable def symmetricPowerLeftTensorMap
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    moduleTensor ℱ (symmetricPowerSheaf 𝒢 n) ⟶ symmetricPowerSheaf 𝒢 (n + 1) :=
  moduleTensorMap (sheafificationCounitInv ℱ) (𝟙 (symmetricPowerSheaf 𝒢 n)) ≫
    (moduleSheafificationTensorIso X.sheaf ℱ.val (symmetricPowerPresheaf 𝒢 n)).hom ≫
    (moduleSheafification X.sheaf).map (symmetricPowerLeftTensorPresheafMap n φ)

/-- The canonical morphism
`ℱ ⊗ Λ^[n] 𝒢 ⟶ Λ^[n + 1] 𝒢`
induced by a morphism `ℱ ⟶ 𝒢`. -/
noncomputable def exteriorPowerLeftTensorMap
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    moduleTensor ℱ (exteriorPowerSheaf 𝒢 n) ⟶ exteriorPowerSheaf 𝒢 (n + 1) :=
  moduleTensorMap (sheafificationCounitInv ℱ) (𝟙 (exteriorPowerSheaf 𝒢 n)) ≫
    (moduleSheafificationTensorIso X.sheaf ℱ.val (exteriorPowerPresheaf 𝒢 n)).hom ≫
    (moduleSheafification X.sheaf).map (exteriorPowerLeftTensorPresheafMap n φ)

end AlgebraicGeometry.RingedSpace

scoped[AlgebraicGeometry] notation3:max "Λ^[" n "] " ℱ =>
  AlgebraicGeometry.RingedSpace.exteriorPowerSheaf ℱ n
scoped[AlgebraicGeometry] notation3:max "Symm[" n "] " ℱ =>
  AlgebraicGeometry.RingedSpace.symmetricPowerSheaf ℱ n
