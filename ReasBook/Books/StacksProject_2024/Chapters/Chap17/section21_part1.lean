import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Stalk

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_17_21_1 (from Chap17) -/
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

/-! ### Lemma_17_21_2 (from Chap17) -/
open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-
Domain-style sampling for Lemma 17.21.2:
- primary domain: algebra constructions on sheaves of modules over a ringed space and their
  behavior on stalks;
- inspected owner declarations:
  `RingedSpace.stalkModuleCat`,
  `moduleTensorAlgebra`,
  `moduleSymmetricAlgebra`,
  `moduleExteriorAlgebra`,
  `tensorProductStalkIso`;
- best owner abstraction: the source-facing content is a stalkwise comparison for the sheaf-side
  owners `T(ℱ)`, `Symm(ℱ)`, and `Λ(ℱ)`, with the stalk itself expressed through the existing
  bundled owner `RingedSpace.stalkModuleCat`;
- primitive data: a module sheaf `ℱ : X.Modules` and a point `x : X`;
- derived API: the three canonical stalk isomorphisms into the corresponding algebra objects
  formed from `RingedSpace.stalkModuleCat ℱ x`.

Source/core/bridge triage:
- `source-facing`: the three canonical stalk isomorphisms from the source text;
- `core/canonical`: `RingedSpace.stalkModuleCat` and the sheaf-side owners
  `moduleTensorAlgebra`, `moduleSymmetricAlgebra`, `moduleExteriorAlgebra`;
- `bridge/view`: the explicit presheaf-level filtered-colimit comparisons used internally to
  define the public stalk isomorphisms.

This file should therefore reuse `RingedSpace.stalkModuleCat` directly and expose the canonical
stalk comparisons themselves as the public API, rather than `Nonempty` wrappers around them.
-/

/-- The presheaf category underlying `\mathcal O_X`-modules on a ringed space. -/
private abbrev PresheafModules (X : RingedSpace.{u}) :=
  PresheafOfModules.{u} X.ringCatSheaf.obj

private abbrev stalkRing (x : X) :=
  X.presheaf.stalk x

private abbrev stalkRingGerm (U : Opens X) (x : X) (hx : x ∈ U) :=
  X.presheaf.germ U x hx

private def stalkGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    ℱ.val.obj (op U) →ₛₗ[(stalkRingGerm U x hx).hom] ↑(stalkModuleCat ℱ x) where
  toFun := fun s ↦ (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) s
  map_add' := by
    intro s t
    simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add s t
  map_smul' := by
    intro r s
    simpa using (PresheafOfModules.germ_smul ℱ.val x U hx r s)

/-- The objectwise tensor algebra module on an open set of a ringed space. -/
private abbrev tensorAlgebraPresheafObj (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  ModuleCat.of (X.presheaf.obj U)
    (TensorAlgebra (X.presheaf.obj U) (ℱ.val.obj U))

/-- The linear map on sections induced by restriction for the tensor algebra presheaf. -/
private def tensorAlgebraRestrictionLinear
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    let _ :
        Algebra (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
      Algebra.compHom
        (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
        (X.presheaf.map i).hom
    ℱ.val.obj U →ₗ[X.presheaf.obj U] TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V) := by
  let _ :
      Algebra (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  refine
    { toFun := fun m ↦
        TensorAlgebra.ι (X.presheaf.obj V)
          (show ℱ.val.obj V from (ℱ.val.map i).hom m)
      map_add' := ?_
      map_smul' := ?_ }
  · sorry
  · sorry

/-- The restriction map for the tensor algebra presheaf. -/
private noncomputable def tensorAlgebraPresheafMap
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    tensorAlgebraPresheafObj ℱ U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
        (tensorAlgebraPresheafObj ℱ V) := by
  let _ :
      Algebra (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  exact
    (show tensorAlgebraPresheafObj ℱ U ⟶
        ModuleCat.of (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) from
      ModuleCat.ofHom
        ((TensorAlgebra.lift (X.presheaf.obj U)
          (tensorAlgebraRestrictionLinear ℱ i)).toLinearMap))

/-- The tensor algebra restriction maps satisfy the identity axiom of a presheaf of modules. -/
private theorem tensorAlgebraPresheaf_map_id
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    tensorAlgebraPresheafMap ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (tensorAlgebraPresheafObj ℱ U) := sorry

/-- The tensor algebra restriction maps satisfy the composition axiom of a presheaf of modules. -/
private theorem tensorAlgebraPresheaf_map_comp
    (ℱ : X.Modules) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    tensorAlgebraPresheafMap ℱ (i ≫ j) =
      tensorAlgebraPresheafMap ℱ i ≫
        (ModuleCat.restrictScalars _).map (tensorAlgebraPresheafMap ℱ j) ≫
          (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
            (X.presheaf.map j).hom
            (X.presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
            (tensorAlgebraPresheafObj ℱ W) := sorry

/-- The presheaf of tensor algebras associated to an `\mathcal O_X`-module. -/
private noncomputable def tensorAlgebraPresheaf (ℱ : X.Modules) : PresheafModules X where
  obj := tensorAlgebraPresheafObj ℱ
  map := tensorAlgebraPresheafMap ℱ
  map_id := tensorAlgebraPresheaf_map_id ℱ
  map_comp := tensorAlgebraPresheaf_map_comp ℱ

/-- The objectwise symmetric algebra module on an open set of a ringed space. -/
private abbrev symmetricAlgebraPresheafObj (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  ModuleCat.of (X.presheaf.obj U)
    (SymmetricAlgebra (X.presheaf.obj U) (ℱ.val.obj U))

/-- The linear map on sections induced by restriction for the symmetric algebra presheaf. -/
private def symmetricAlgebraRestrictionLinear
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    let _ :
        Algebra (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
      Algebra.compHom
        (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
        (X.presheaf.map i).hom
    ℱ.val.obj U →ₗ[X.presheaf.obj U] SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V) := by
  let _ :
      Algebra (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  refine
    { toFun := fun m ↦
        SymmetricAlgebra.ι (X.presheaf.obj V) (ℱ.val.obj V)
          (show ℱ.val.obj V from (ℱ.val.map i).hom m)
      map_add' := ?_
      map_smul' := ?_ }
  · sorry
  · sorry

/-- The restriction map for the symmetric algebra presheaf. -/
private noncomputable def symmetricAlgebraPresheafMap
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    symmetricAlgebraPresheafObj ℱ U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
        (symmetricAlgebraPresheafObj ℱ V) := by
  let _ :
      Algebra (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  exact
    (show symmetricAlgebraPresheafObj ℱ U ⟶
        ModuleCat.of (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) from
      ModuleCat.ofHom
        ((SymmetricAlgebra.lift (symmetricAlgebraRestrictionLinear ℱ i)).toLinearMap))

/-- The symmetric algebra restriction maps satisfy the identity axiom of a presheaf of modules. -/
private theorem symmetricAlgebraPresheaf_map_id
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    symmetricAlgebraPresheafMap ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (symmetricAlgebraPresheafObj ℱ U) := sorry

/-- The symmetric algebra restriction maps satisfy the composition axiom of a presheaf of
modules. -/
private theorem symmetricAlgebraPresheaf_map_comp
    (ℱ : X.Modules) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    symmetricAlgebraPresheafMap ℱ (i ≫ j) =
      symmetricAlgebraPresheafMap ℱ i ≫
        (ModuleCat.restrictScalars _).map (symmetricAlgebraPresheafMap ℱ j) ≫
          (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
            (X.presheaf.map j).hom
            (X.presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
            (symmetricAlgebraPresheafObj ℱ W) := sorry

/-- The presheaf of symmetric algebras associated to an `\mathcal O_X`-module. -/
private noncomputable def symmetricAlgebraPresheaf (ℱ : X.Modules) : PresheafModules X where
  obj := symmetricAlgebraPresheafObj ℱ
  map := symmetricAlgebraPresheafMap ℱ
  map_id := symmetricAlgebraPresheaf_map_id ℱ
  map_comp := symmetricAlgebraPresheaf_map_comp ℱ

private abbrev stalkTensorAlgebra (ℱ : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    (TensorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x))

private abbrev stalkSymmetricAlgebra (ℱ : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    (SymmetricAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x))

private abbrev stalkExteriorAlgebra (ℱ : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    (ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x))

private def tensorAlgebraGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    let _ :
        Algebra (X.presheaf.obj (op U))
          (TensorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    ℱ.val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      TensorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  let _ :
      Algebra (X.presheaf.obj (op U))
        (TensorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
    Algebra.compHom _ (stalkRingGerm U x hx).hom
  refine
    { toFun := fun m ↦
        TensorAlgebra.ι (X.presheaf.stalk x)
          ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      map_add' := ?_
      map_smul' := ?_ }
  · intro m n
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (m + n) =
          (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m +
            (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n := by
      simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add m n
    rw [h]
    simpa using (TensorAlgebra.ι (X.presheaf.stalk x)).map_add
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n)
  · intro r m
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (r • m) =
          (stalkRingGerm U x hx) r • (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m := by
      simpa using PresheafOfModules.germ_smul ℱ.val x U hx r m
    rw [h]
    simpa using (TensorAlgebra.ι (X.presheaf.stalk x)).map_smul
      ((stalkRingGerm U x hx) r)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)

private def symmetricAlgebraGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    let _ :
        Algebra (X.presheaf.obj (op U))
          (SymmetricAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    ℱ.val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      SymmetricAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  let _ :
      Algebra (X.presheaf.obj (op U))
        (SymmetricAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
    Algebra.compHom _ (stalkRingGerm U x hx).hom
  refine
    { toFun := fun m ↦
        SymmetricAlgebra.ι (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)
          ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      map_add' := ?_
      map_smul' := ?_ }
  · intro m n
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (m + n) =
          (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m +
            (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n := by
      simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add m n
    rw [h]
    simpa using (SymmetricAlgebra.ι (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)).map_add
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n)
  · intro r m
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (r • m) =
          (stalkRingGerm U x hx) r • (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m := by
      simpa using PresheafOfModules.germ_smul ℱ.val x U hx r m
    rw [h]
    simpa using (SymmetricAlgebra.ι (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)).map_smul
      ((stalkRingGerm U x hx) r)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)

private def exteriorAlgebraGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    let _ :
        Algebra (X.presheaf.obj (op U))
          (ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    ℱ.val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  let _ :
      Algebra (X.presheaf.obj (op U))
        (ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
    Algebra.compHom _ (stalkRingGerm U x hx).hom
  refine
    { toFun := fun m ↦
        ExteriorAlgebra.ι (X.presheaf.stalk x)
          ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      map_add' := ?_
      map_smul' := ?_ }
  · intro m n
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (m + n) =
          (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m +
            (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n := by
      simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add m n
    rw [h]
    simpa using (ExteriorAlgebra.ι (X.presheaf.stalk x)).map_add
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n)
  · intro r m
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (r • m) =
          (stalkRingGerm U x hx) r • (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m := by
      simpa using PresheafOfModules.germ_smul ℱ.val x U hx r m
    rw [h]
    simpa using (ExteriorAlgebra.ι (X.presheaf.stalk x)).map_smul
      ((stalkRingGerm U x hx) r)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)

private theorem exteriorAlgebraGermLinear_sq_zero (ℱ : X.Modules) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    ∀ m : ℱ.val.obj (op U),
      exteriorAlgebraGermLinear ℱ x U hx m *
        exteriorAlgebraGermLinear ℱ x U hx m = 0 := by
  intro m
  simpa [exteriorAlgebraGermLinear] using
    (ExteriorAlgebra.ι_sq_zero
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m))

private noncomputable def tensorAlgebraGermHom (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    (tensorAlgebraPresheaf ℱ).presheaf.obj (op U) ⟶ AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) :=
  by
    let _ :
        Algebra (X.presheaf.obj (op U))
          (TensorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    exact AddCommGrpCat.ofHom <|
      (((TensorAlgebra.lift (X.presheaf.obj (op U))
        (tensorAlgebraGermLinear ℱ x U hx)).toLinearMap).toAddMonoidHom)

private noncomputable def symmetricAlgebraGermHom (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    (symmetricAlgebraPresheaf ℱ).presheaf.obj (op U) ⟶ AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) :=
  by
    let _ :
        Algebra (X.presheaf.obj (op U))
          (SymmetricAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    exact AddCommGrpCat.ofHom <|
      (((SymmetricAlgebra.lift (symmetricAlgebraGermLinear ℱ x U hx)).toLinearMap).toAddMonoidHom)

private noncomputable def exteriorAlgebraGermHom (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    (exteriorAlgebraPresheaf ℱ).presheaf.obj (op U) ⟶ AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) :=
  by
    let _ :
        Algebra (X.presheaf.obj (op U))
          (ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    let e :
        ExteriorAlgebra (X.presheaf.obj (op U)) (ℱ.val.obj (op U)) →ₐ[X.presheaf.obj (op U)]
          ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) :=
      (ExteriorAlgebra.lift (X.presheaf.obj (op U)))
        ⟨exteriorAlgebraGermLinear ℱ x U hx, exteriorAlgebraGermLinear_sq_zero ℱ x U hx⟩
    exact AddCommGrpCat.ofHom <|
      (e.toLinearMap.toAddMonoidHom)

private noncomputable def tensorAlgebraNhdsGermHom
    (ℱ : X.Modules) (x : X) (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ (tensorAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) := by
  exact show (((OpenNhds.inclusion x).op ⋙ (tensorAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) from
    tensorAlgebraGermHom ℱ x (Opposite.unop U).1 (Opposite.unop U).2

private noncomputable def symmetricAlgebraNhdsGermHom
    (ℱ : X.Modules) (x : X) (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ (symmetricAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) := by
  exact show (((OpenNhds.inclusion x).op ⋙ (symmetricAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) from
    symmetricAlgebraGermHom ℱ x (Opposite.unop U).1 (Opposite.unop U).2

private noncomputable def exteriorAlgebraNhdsGermHom
    (ℱ : X.Modules) (x : X) (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ (exteriorAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) := by
  exact show (((OpenNhds.inclusion x).op ⋙ (exteriorAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) from
    exteriorAlgebraGermHom ℱ x (Opposite.unop U).1 (Opposite.unop U).2

private theorem tensorAlgebraNhdsGermHom_naturality
    (ℱ : X.Modules) (x : X) {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ (tensorAlgebraPresheaf ℱ).presheaf).map i) ≫
        tensorAlgebraNhdsGermHom ℱ x V =
      tensorAlgebraNhdsGermHom ℱ x U := sorry

private theorem symmetricAlgebraNhdsGermHom_naturality
    (ℱ : X.Modules) (x : X) {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ (symmetricAlgebraPresheaf ℱ).presheaf).map i) ≫
        symmetricAlgebraNhdsGermHom ℱ x V =
      symmetricAlgebraNhdsGermHom ℱ x U := sorry

private theorem exteriorAlgebraNhdsGermHom_naturality
    (ℱ : X.Modules) (x : X) {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ (exteriorAlgebraPresheaf ℱ).presheaf).map i) ≫
        exteriorAlgebraNhdsGermHom ℱ x V =
      exteriorAlgebraNhdsGermHom ℱ x U := sorry

private def presheafTensorAlgebraStalkComparison (ℱ : X.Modules) (x : X) :
    TopCat.Presheaf.stalk (tensorAlgebraPresheaf ℱ).presheaf x ⟶
      AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (tensorAlgebraPresheaf ℱ).presheaf) <|
    Cocone.mk _ <|
      { app := fun U ↦ tensorAlgebraNhdsGermHom ℱ x U
        naturality := by
          intro U V i
          exact tensorAlgebraNhdsGermHom_naturality ℱ x i }

private def presheafSymmetricAlgebraStalkComparison (ℱ : X.Modules) (x : X) :
    TopCat.Presheaf.stalk (symmetricAlgebraPresheaf ℱ).presheaf x ⟶
      AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (symmetricAlgebraPresheaf ℱ).presheaf) <|
    Cocone.mk _ <|
      { app := fun U ↦ symmetricAlgebraNhdsGermHom ℱ x U
        naturality := by
          intro U V i
          exact symmetricAlgebraNhdsGermHom_naturality ℱ x i }

private def presheafExteriorAlgebraStalkComparison (ℱ : X.Modules) (x : X) :
    TopCat.Presheaf.stalk (exteriorAlgebraPresheaf ℱ).presheaf x ⟶
      AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (exteriorAlgebraPresheaf ℱ).presheaf) <|
    Cocone.mk _ <|
      { app := fun U ↦ exteriorAlgebraNhdsGermHom ℱ x U
        naturality := by
          intro U V i
          exact exteriorAlgebraNhdsGermHom_naturality ℱ x i }

-- Proof sketch: the unit map from the tensor-algebra presheaf to its sheafification becomes an
-- isomorphism on stalks; composing its inverse with the explicit filtered-colimit map from the
-- stalk of the presheaf tensor algebra to the tensor algebra on the stalk module yields the
-- canonical `\mathcal O_{X,x}`-linear comparison.
private noncomputable def tensorAlgebraStalkComparison_hom (ℱ : X.Modules) (x : X) :
    stalkModuleCat (T(ℱ)) x ⟶ stalkTensorAlgebra ℱ x := by
  letI : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (inferInstance : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  letI :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    (inferInstance :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u})
  let η :
      TopCat.Presheaf.stalk (tensorAlgebraPresheaf ℱ).presheaf x ⟶
        TopCat.Presheaf.stalk (T(ℱ)).val.presheaf x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (tensorAlgebraPresheaf ℱ).presheaf)
  haveI : IsIso η := by
    simpa [moduleTensorAlgebra, tensorAlgebraPresheaf] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (tensorAlgebraPresheaf ℱ).presheaf)
  let comparison :
      TopCat.Presheaf.stalk (T(ℱ)).val.presheaf x ⟶ AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) :=
    inv η ≫ presheafTensorAlgebraStalkComparison ℱ x
  exact ModuleCat.ofHom
    { toFun := comparison
      map_add' := by
        intro m n
        simpa [comparison] using comparison.hom.map_add m n
      map_smul' := by
        intro r m
        sorry }

private theorem tensorAlgebraStalkComparison_hom_isIso (ℱ : X.Modules) (x : X) :
    IsIso (tensorAlgebraStalkComparison_hom ℱ x) := sorry

-- Proof sketch: the same sheafification-on-stalks argument identifies the stalk of the symmetric
-- algebra sheaf with the stalk of the presheaf of symmetric algebras, and the latter maps
-- canonically to the symmetric algebra of the stalk module.
private noncomputable def symmetricAlgebraStalkComparison_hom (ℱ : X.Modules) (x : X) :
    stalkModuleCat (Symm(ℱ)) x ⟶ stalkSymmetricAlgebra ℱ x := by
  letI : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (inferInstance : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  letI :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    (inferInstance :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u})
  let η :
      TopCat.Presheaf.stalk (symmetricAlgebraPresheaf ℱ).presheaf x ⟶
        TopCat.Presheaf.stalk (Symm(ℱ)).val.presheaf x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (symmetricAlgebraPresheaf ℱ).presheaf)
  haveI : IsIso η := by
    simpa [moduleSymmetricAlgebra, symmetricAlgebraPresheaf] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (symmetricAlgebraPresheaf ℱ).presheaf)
  let comparison :
      TopCat.Presheaf.stalk (Symm(ℱ)).val.presheaf x ⟶
        AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) :=
    inv η ≫ presheafSymmetricAlgebraStalkComparison ℱ x
  exact ModuleCat.ofHom
    { toFun := comparison
      map_add' := by
        intro m n
        simpa [comparison] using comparison.hom.map_add m n
      map_smul' := by
        intro r m
        sorry }

private theorem symmetricAlgebraStalkComparison_hom_isIso (ℱ : X.Modules) (x : X) :
    IsIso (symmetricAlgebraStalkComparison_hom ℱ x) := sorry

-- Proof sketch: use the same sheafification-on-stalks argument for the exterior-algebra sheaf and
-- then compare the presheaf stalk with the exterior algebra generated by the stalk module.
private noncomputable def exteriorAlgebraStalkComparison_hom (ℱ : X.Modules) (x : X) :
    stalkModuleCat (Λ(ℱ)) x ⟶ stalkExteriorAlgebra ℱ x := by
  letI : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (inferInstance : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  letI :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    (inferInstance :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u})
  let η :
      TopCat.Presheaf.stalk (exteriorAlgebraPresheaf ℱ).presheaf x ⟶
        TopCat.Presheaf.stalk (Λ(ℱ)).val.presheaf x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (exteriorAlgebraPresheaf ℱ).presheaf)
  haveI : IsIso η := by
    simpa [moduleExteriorAlgebra, exteriorAlgebraPresheaf] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (exteriorAlgebraPresheaf ℱ).presheaf)
  let comparison :
      TopCat.Presheaf.stalk (Λ(ℱ)).val.presheaf x ⟶ AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) :=
    inv η ≫ presheafExteriorAlgebraStalkComparison ℱ x
  exact ModuleCat.ofHom
    { toFun := comparison
      map_add' := by
        intro m n
        simpa [comparison] using comparison.hom.map_add m n
      map_smul' := by
        intro r m
        sorry }

private theorem exteriorAlgebraStalkComparison_hom_isIso (ℱ : X.Modules) (x : X) :
    IsIso (exteriorAlgebraStalkComparison_hom ℱ x) := sorry

-- Proof sketch: after constructing the comparison morphism and proving it is an isomorphism, take
-- its associated categorical isomorphism.
/-- Lemma 17.21.2 (1): the stalk of the tensor algebra sheaf of `\mathcal F` at `x` is canonically
isomorphic to the tensor algebra of the stalk `\mathcal F_x` over `\mathcal O_{X, x}`. -/
noncomputable opaque tensorAlgebraStalkIso (ℱ : X.Modules) (x : X) :
    stalkModuleCat (T(ℱ)) x ≅
      ModuleCat.of (X.presheaf.stalk x)
        (TensorAlgebra (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x)) :=
  by
    letI := tensorAlgebraStalkComparison_hom_isIso ℱ x
    exact asIso (tensorAlgebraStalkComparison_hom ℱ x)

-- Proof sketch: compose the symmetric-algebra comparison morphism with its `IsIso` witness.
/-- Lemma 17.21.2 (2): the stalk of the symmetric algebra sheaf of `\mathcal F` at `x` is
canonically isomorphic to the symmetric algebra of the stalk `\mathcal F_x` over
`\mathcal O_{X, x}`. -/
noncomputable opaque symmetricAlgebraStalkIso (ℱ : X.Modules) (x : X) :
    stalkModuleCat (Symm(ℱ)) x ≅
      ModuleCat.of (X.presheaf.stalk x)
        (SymmetricAlgebra (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x)) :=
  by
    letI := symmetricAlgebraStalkComparison_hom_isIso ℱ x
    exact asIso (symmetricAlgebraStalkComparison_hom ℱ x)

-- Proof sketch: compose the exterior-algebra comparison morphism with its `IsIso` witness.
/-- Lemma 17.21.2 (3): the stalk of the exterior algebra sheaf of `\mathcal F` at `x` is
canonically isomorphic to the exterior algebra of the stalk `\mathcal F_x` over
`\mathcal O_{X, x}`. -/
noncomputable opaque exteriorAlgebraStalkIso (ℱ : X.Modules) (x : X) :
    stalkModuleCat (Λ(ℱ)) x ≅
      ModuleCat.of (X.presheaf.stalk x)
        (ExteriorAlgebra (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x)) :=
  by
    letI := exteriorAlgebraStalkComparison_hom_isIso ℱ x
    exact asIso (exteriorAlgebraStalkComparison_hom ℱ x)

end AlgebraicGeometry.RingedSpace
