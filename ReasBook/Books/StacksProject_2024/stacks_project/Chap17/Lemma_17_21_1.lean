import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.stacks_project.LinearAlgebra.PowerOperations
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1

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
- `core/canonical`: `X.ringCatSheaf`, sectionwise `exteriorPower` / `SymmetricPower`,
  and `PresheafOfModules.sheafification`;
- `bridge/view`: the sectionwise restriction maps and their presheaf-axiom lemmas. -/

variable {X : RingedSpace.{u}}

local notation "ModX" => SheafOfModules X.ringCatSheaf
private noncomputable abbrev modSheafification :
    PresheafOfModules X.ringCatSheaf.obj ⥤ ModX :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

private local instance presheafOfModulesMonoidal :
    MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) := by
  infer_instance

private local instance sheafOfModulesMonoidal :
    MonoidalCategory ModX := by
  infer_instance

/-- The source-facing tensor product of `\mathcal O_X`-modules on a ringed space, presented by
sheafifying the sectionwise presheaf tensor product. -/
noncomputable abbrev moduleTensor
    (ℱ 𝒢 : ModX) :
    ModX :=
  modSheafification.obj (PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val)

private noncomputable abbrev moduleTensorMap
    {ℱ₁ ℱ₂ 𝒢₁ 𝒢₂ : ModX}
    (α : ℱ₁ ⟶ ℱ₂) (β : 𝒢₁ ⟶ 𝒢₂) :
    moduleTensor ℱ₁ 𝒢₁ ⟶ moduleTensor ℱ₂ 𝒢₂ :=
  modSheafification.map (PresheafOfModules.Monoidal.tensorHom α.val β.val)

private noncomputable def restrictScalarsIdIso
    (ℱ : PresheafOfModules X.ringCatSheaf.obj) :
    (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj ℱ ≅ ℱ :=
  PresheafOfModules.isoMk
    (fun U ↦ by
      simpa using
        (ModuleCat.restrictScalarsId'App
          (((𝟙 X.ringCatSheaf.obj : X.ringCatSheaf.obj ⟶ X.ringCatSheaf.obj).app U).hom)
          rfl
          (ℱ.obj U)))
    (fun {U V} i ↦ by
      ext x
      rfl)

private noncomputable abbrev sheafificationUnitToVal
    (ℱ : PresheafOfModules X.ringCatSheaf.obj) :
    ℱ ⟶ (modSheafification.obj ℱ).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app ℱ ≫
    (restrictScalarsIdIso ((modSheafification.obj ℱ).val)).hom

private abbrev moduleSheafificationTensorComparison
    (ℱ 𝒢 : PresheafOfModules X.ringCatSheaf.obj) :
    modSheafification.obj (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) ⟶
      moduleTensor (modSheafification.obj ℱ) (modSheafification.obj 𝒢) :=
  -- Proof comment: use the canonical monoidal comparison of sheafification itself.
  ((Functor.Monoidal.μIso modSheafification ℱ 𝒢).symm).hom

private instance moduleSheafificationTensorComparison_isIso
    (ℱ 𝒢 : PresheafOfModules X.ringCatSheaf.obj) :
    IsIso (moduleSheafificationTensorComparison ℱ 𝒢) := by
  -- Proof comment: the comparison is the `hom` of the canonical monoidal isomorphism.
  dsimp [moduleSheafificationTensorComparison]
  infer_instance

private noncomputable abbrev moduleSheafificationTensorIso
    (ℱ 𝒢 : PresheafOfModules X.ringCatSheaf.obj) :
    moduleTensor (modSheafification.obj ℱ) (modSheafification.obj 𝒢) ≅
      modSheafification.obj (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) :=
  (asIso (moduleSheafificationTensorComparison ℱ 𝒢)).symm

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

/-- Helper for Lemma 17.21.1: the exterior-power restriction map sends a standard generator to the
corresponding generator after applying the section restriction map entrywise. -/
private theorem exteriorPowerRestrict_apply_ιMulti
    {R S M N : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (f : M →ₗ[R] N) (m : Fin n → M) :
    exteriorPowerRestrict (R := R) (S := S) n f (exteriorPower.ιMulti R n m) =
      exteriorPower.ιMulti S n (f ∘ m) := by
  -- Unwrap the universal property and evaluate the descended map on the generator.
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
  let A : M [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) := ιN'.compLinearMap f
  change (exteriorPower.alternatingMapLinearEquiv A) (exteriorPower.ιMulti R n m) =
    exteriorPower.ιMulti S n (f ∘ m)
  calc
    (exteriorPower.alternatingMapLinearEquiv A) (exteriorPower.ιMulti R n m)
        = (exteriorPower.alternatingMapLinearEquiv.symm
            (exteriorPower.alternatingMapLinearEquiv A)) m := by
            symm
            simpa using
              (exteriorPower.alternatingMapLinearEquiv_symm_apply
                (F := exteriorPower.alternatingMapLinearEquiv A) m)
    _ = A m := by
          simpa using
            congrArg (fun F : M [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) ↦ F m)
              (exteriorPower.alternatingMapLinearEquiv.symm_apply_apply A)
    _ = exteriorPower.ιMulti S n (f ∘ m) := rfl

/-- Helper for Lemma 17.21.1: linear maps out of an exterior power are determined by their values
on the standard alternating generators `ιMulti`. -/
private theorem exteriorPowerHom_ext_ιMulti
    {R M N : Type _} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (n : ℕ) {f g : ⋀[R]^n M →ₗ[R] N}
    (h : ∀ m : Fin n → M, f (exteriorPower.ιMulti R n m) = g (exteriorPower.ιMulti R n m)) :
    f = g := by
  -- Proof comment: exterior powers are generated by the alternating generators `ιMulti`, and
  -- `exteriorPower.linearMap_ext` packages that extensionality principle directly.
  apply exteriorPower.linearMap_ext
  ext m
  exact h m

/-- Helper for Lemma 17.21.1: the symmetric-power restriction map sends a standard generator to the
corresponding generator after applying the section restriction map entrywise. -/
private theorem symmetricPowerRestrict_tprod
    {R S M N : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (f : M →ₗ[R] N) (m : SymmetricPower.UFin n → M) :
    symmetricPowerRestrict (R := R) (S := S) n f (SymmetricPower.tprod R m) =
      SymmetricPower.tprod S (f ∘ m) := by
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
  -- Route correction: evaluate the descended quotient map directly on the tensor generator.
  change g (SymmetricPower.tprod R m) = SymmetricPower.tprod S (f ∘ m)
  change ((AddCon.lift (addConGen (SymmetricPower.Rel R (SymmetricPower.UFin n) M))
      tensorLift.toAddMonoidHom hrel)
      ((addConGen (SymmetricPower.Rel R (SymmetricPower.UFin n) M)).mk'
        (PiTensorProduct.tprod R m))) =
    SymmetricPower.tprod S (f ∘ m)
  rw [AddCon.lift_mk']
  -- The tensor lift evaluates on pure tensors by the defining multilinear map.
  change tensorLift (PiTensorProduct.tprod R m) = (SymmetricPower.tprod S) (f ∘ m)
  simp [tensorLift, tprodN', Function.comp_def]
  change tprodN (f ∘ m) = tprodN (f ∘ m)
  rfl

/-- Helper for Lemma 17.21.1: linear maps out of a symmetric power are determined by their values
on the standard tensor-product generators `tprod`. -/
private theorem symmetricPowerHom_ext_tprod
    {R M N : Type _} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (n : ℕ) {f g : Sym[R] (SymmetricPower.UFin n) M →ₗ[R] N}
    (h : ∀ m : SymmetricPower.UFin n → M,
      f (SymmetricPower.tprod R m) = g (SymmetricPower.tprod R m)) :
    f = g := by
  -- Proof comment: descend to quotient representatives and then induct on the tensor-product
  -- representative, reducing everything to the pure generators `tprod`.
  ext q
  refine AddCon.induction_on q ?_
  intro x
  change f (SymmetricPower.mk R (SymmetricPower.UFin n) M x) =
    g (SymmetricPower.mk R (SymmetricPower.UFin n) M x)
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
      simpa [SymmetricPower.tprod, LinearMap.map_smul] using
        congrArg (fun z : N ↦ r • z) (h m)
  | add x y hx hy =>
    simp [hx, hy]

/-- Helper for Lemma 17.21.1: restricting sections along a composite equals iterated restriction
on each element. -/
private theorem sectionMapCompApply
    (ℱ : ModX) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (m : ℱ.val.obj U) :
    (ℱ.val.map (i ≫ j)).hom m = (ℱ.val.map j).hom ((ℱ.val.map i).hom m) := by
  -- Proof comment: evaluate the presheaf composition law on the chosen section.
  simpa using congrArg (fun h => (ModuleCat.Hom.hom h) m) (ℱ.val.map_comp i j)

/-- Helper for Lemma 17.21.1: a morphism of module sheaves commutes with restriction on each
section. -/
private theorem sectionHomNaturalityApply
    {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : ℱ.val.obj U) :
    (𝒢.val.map i).hom ((φ.val.app U).hom m) = (φ.val.app V).hom ((ℱ.val.map i).hom m) := by
  -- Proof comment: evaluate the naturality square of `φ` on the chosen section.
  simpa using congrArg (fun h => (ModuleCat.Hom.hom h) m) (φ.val.naturality i).symm

private theorem exteriorPowerPresheafMap_id
    (ℱ : ModX) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    exteriorPowerPresheafMap ℱ n (𝟙 U) =
        (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (exteriorPowerPresheafObj ℱ n U) := by
  -- Route correction: compare the induced exterior-power endomorphism with the identity on the
  -- `ιMulti` generators, then transport that equality through `restrictScalarsId'`.
  have hRing :
      (X.presheaf.map (𝟙 U)).hom = RingHom.id (X.presheaf.obj U) := by
    simpa using congrArg CommRingCat.Hom.hom (X.presheaf.map_id U)
  let R := X.presheaf.obj U
  let M := ℱ.val.obj U
  let F : ⋀[R]^n M →ₗ[R] ⋀[R]^n M :=
    exteriorPowerRestrict (R := R) (S := R) n (ℱ.val.map (𝟙 U)).hom
  have hF : F = LinearMap.id := by
    -- Proof comment: the exterior power is generated by the alternating tensors `ιMulti`.
    apply exteriorPowerHom_ext_ιMulti
    intro m
    rw [exteriorPowerRestrict_apply_ιMulti]
    simp [F, Function.comp_def]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [exteriorPowerPresheafMap, F, hRing, ModuleCat.hom_ofHom,
    ModuleCat.restrictScalarsId'App_inv_apply] using
    congrArg (fun f => f x) hF

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
          (exteriorPowerPresheafObj ℱ n W) := by
  -- Route correction: compare the direct and iterated restriction maps on `ιMulti` generators and
  -- then transport the resulting linear-map equality through `restrictScalarsComp'`.
  have hRing :
      (X.presheaf.map (i ≫ j)).hom = (X.presheaf.map j).hom.comp (X.presheaf.map i).hom := by
    simpa using congrArg CommRingCat.Hom.hom (X.presheaf.map_comp i j)
  let R := X.presheaf.obj U
  let S := X.presheaf.obj V
  let T := X.presheaf.obj W
  let M := ℱ.val.obj U
  let N := ℱ.val.obj V
  let P := ℱ.val.obj W
  let _ : Algebra R S := (X.presheaf.map i).hom.toAlgebra
  let _ : Algebra S T := (X.presheaf.map j).hom.toAlgebra
  let _ : Algebra R T := ((X.presheaf.map j).hom.comp (X.presheaf.map i).hom).toAlgebra
  let _ : Module R N := Module.compHom N (algebraMap R S)
  let _ : Module S P := Module.compHom P (algebraMap S T)
  let _ : Module R P := Module.compHom P (algebraMap R T)
  let _ : IsScalarTower R S N := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower S T P := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R S P := IsScalarTower.of_algebraMap_eq' rfl
  let Fij : ⋀[R]^n M →ₗ[R] ⋀[T]^n P :=
    exteriorPowerRestrict (R := R) (S := T) n (ℱ.val.map (i ≫ j)).hom
  let Fi : ⋀[R]^n M →ₗ[R] ⋀[S]^n N :=
    exteriorPowerRestrict (R := R) (S := S) n (ℱ.val.map i).hom
  let Fj : ⋀[S]^n N →ₗ[S] ⋀[T]^n P :=
    exteriorPowerRestrict (R := S) (S := T) n (ℱ.val.map j).hom
  let Fcomp : ⋀[R]^n M →ₗ[R] ⋀[T]^n P :=
    (Fj.restrictScalars R).comp Fi
  have hcomp : Fij = Fcomp := by
    -- Proof comment: both maps send a generator to the section restricted first along `i` and
    -- then along `j`.
    apply exteriorPowerHom_ext_ιMulti
    intro m
    rw [exteriorPowerRestrict_apply_ιMulti, exteriorPowerRestrict_apply_ιMulti,
      exteriorPowerRestrict_apply_ιMulti]
    congr 1
    ext a
    simpa [Function.comp_def] using sectionMapCompApply ℱ i j (m a)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [exteriorPowerPresheafMap, Fij, Fcomp, Fi, Fj, hRing, ModuleCat.hom_ofHom,
    ModuleCat.restrictScalarsComp'App_inv_apply] using
    congrArg (fun f => f x) hcomp

private theorem symmetricPowerPresheafMap_id
    (ℱ : ModX) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    symmetricPowerPresheafMap ℱ n (𝟙 U) =
        (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (symmetricPowerPresheafObj ℱ n U) := by
  -- Route correction: compare the induced symmetric-power endomorphism with the identity on the
  -- `tprod` generators, then transport that equality through `restrictScalarsId'`.
  have hRing :
      (X.presheaf.map (𝟙 U)).hom = RingHom.id (X.presheaf.obj U) := by
    simpa using congrArg CommRingCat.Hom.hom (X.presheaf.map_id U)
  let R := X.presheaf.obj U
  let M := ℱ.val.obj U
  let F : Sym[R] (SymmetricPower.UFin n) M →ₗ[R] Sym[R] (SymmetricPower.UFin n) M :=
    symmetricPowerRestrict (R := R) (S := R) n (ℱ.val.map (𝟙 U)).hom
  have hF : F = LinearMap.id := by
    -- Proof comment: the symmetric power is generated by the pure tensors `tprod`.
    apply symmetricPowerHom_ext_tprod
    intro m
    rw [symmetricPowerRestrict_tprod]
    simp [F, Function.comp_def]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [symmetricPowerPresheafMap, F, hRing, ModuleCat.hom_ofHom,
    ModuleCat.restrictScalarsId'App_inv_apply] using
    congrArg (fun f => f x) hF

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
          (symmetricPowerPresheafObj ℱ n W) := by
  -- Route correction: compare the direct and iterated restriction maps on `tprod` generators and
  -- then transport the resulting linear-map equality through `restrictScalarsComp'`.
  have hRing :
      (X.presheaf.map (i ≫ j)).hom = (X.presheaf.map j).hom.comp (X.presheaf.map i).hom := by
    simpa using congrArg CommRingCat.Hom.hom (X.presheaf.map_comp i j)
  let R := X.presheaf.obj U
  let S := X.presheaf.obj V
  let T := X.presheaf.obj W
  let M := ℱ.val.obj U
  let N := ℱ.val.obj V
  let P := ℱ.val.obj W
  let _ : Algebra R S := (X.presheaf.map i).hom.toAlgebra
  let _ : Algebra S T := (X.presheaf.map j).hom.toAlgebra
  let _ : Algebra R T := ((X.presheaf.map j).hom.comp (X.presheaf.map i).hom).toAlgebra
  let _ : Module R N := Module.compHom N (algebraMap R S)
  let _ : Module S P := Module.compHom P (algebraMap S T)
  let _ : Module R P := Module.compHom P (algebraMap R T)
  let _ : IsScalarTower R S N := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower S T P := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R S P := IsScalarTower.of_algebraMap_eq' rfl
  let Fij : Sym[R] (SymmetricPower.UFin n) M →ₗ[R] Sym[T] (SymmetricPower.UFin n) P :=
    symmetricPowerRestrict (R := R) (S := T) n (ℱ.val.map (i ≫ j)).hom
  let Fi : Sym[R] (SymmetricPower.UFin n) M →ₗ[R] Sym[S] (SymmetricPower.UFin n) N :=
    symmetricPowerRestrict (R := R) (S := S) n (ℱ.val.map i).hom
  let Fj : Sym[S] (SymmetricPower.UFin n) N →ₗ[S] Sym[T] (SymmetricPower.UFin n) P :=
    symmetricPowerRestrict (R := S) (S := T) n (ℱ.val.map j).hom
  let Fcomp : Sym[R] (SymmetricPower.UFin n) M →ₗ[R] Sym[T] (SymmetricPower.UFin n) P :=
    (Fj.restrictScalars R).comp Fi
  have hcomp : Fij = Fcomp := by
    -- Proof comment: both maps send a pure tensor to the section restricted first along `i` and
    -- then along `j`.
    apply symmetricPowerHom_ext_tprod
    intro m
    rw [symmetricPowerRestrict_tprod, symmetricPowerRestrict_tprod, symmetricPowerRestrict_tprod]
    congr 1
    ext a
    simpa [Function.comp_def] using sectionMapCompApply ℱ i j (m a)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa [symmetricPowerPresheafMap, Fij, Fcomp, Fi, Fj, hRing, ModuleCat.hom_ofHom,
    ModuleCat.restrictScalarsComp'App_inv_apply] using
    congrArg (fun f => f x) hcomp

/-- The presheaf `U ↦ \bigwedge^n_{\mathcal O_X(U)} \mathcal F(U)`. -/
noncomputable def exteriorPowerPresheaf
    (ℱ : ModX) (n : ℕ) :
    PresheafOfModules X.ringCatSheaf.obj where
  obj U := exteriorPowerPresheafObj ℱ n U
  map := exteriorPowerPresheafMap ℱ n
  map_id U := exteriorPowerPresheafMap_id ℱ n U
  map_comp i j := exteriorPowerPresheafMap_comp ℱ n i j

/-- The presheaf `U ↦ \operatorname{Sym}^n_{\mathcal O_X(U)} \mathcal F(U)`. -/
noncomputable def symmetricPowerPresheaf
    (ℱ : ModX) (n : ℕ) :
    PresheafOfModules X.ringCatSheaf.obj where
  obj U := symmetricPowerPresheafObj ℱ n U
  map := symmetricPowerPresheafMap ℱ n
  map_id U := symmetricPowerPresheafMap_id ℱ n U
  map_comp i j := symmetricPowerPresheafMap_comp ℱ n i j

/-- The `n`th exterior-power sheaf of `ℱ`, obtained by sheafifying the sectionwise exterior-power
presheaf. -/
noncomputable abbrev exteriorPowerSheaf
    (ℱ : ModX) (n : ℕ) :
    ModX :=
  modSheafification.obj (exteriorPowerPresheaf ℱ n)

/-- The `n`th symmetric-power sheaf of `ℱ`, obtained by sheafifying the sectionwise symmetric-power
presheaf. -/
noncomputable abbrev symmetricPowerSheaf
    (ℱ : ModX) (n : ℕ) :
    ModX :=
  modSheafification.obj (symmetricPowerPresheaf ℱ n)

scoped[AlgebraicGeometry] notation3:max "Λ^[" n "] " ℱ =>
  AlgebraicGeometry.RingedSpace.exteriorPowerSheaf ℱ n
scoped[AlgebraicGeometry] notation3:max "Symm[" n "] " ℱ =>
  AlgebraicGeometry.RingedSpace.symmetricPowerSheaf ℱ n

/-- The inverse of the sheafification counit for the underlying presheaf of a sheaf of
`\mathcal O_X`-modules. -/
private noncomputable abbrev sheafificationCounitInv
    (ℱ : ModX) :
    ℱ ⟶ modSheafification.obj ℱ.val := by
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
    -- Proof comment: compare both composites on the `tprod` generators and reduce the sectionwise
    -- equality to naturality of `φ`.
    let R := sectionRing X U
    let S := sectionRing X V
    letI : Algebra R S := (X.presheaf.map i).hom.toAlgebra
    let Mℱ : ModuleCat R := ℱ.val.obj U
    let Nℱ : ModuleCat S := ℱ.val.obj V
    let M𝒢 : ModuleCat R := 𝒢.val.obj U
    let N𝒢 : ModuleCat S := 𝒢.val.obj V
    letI : Module R Nℱ := Module.compHom Nℱ (X.presheaf.map i).hom
    letI : Module R N𝒢 := Module.compHom N𝒢 (X.presheaf.map i).hom
    letI : IsScalarTower R S Nℱ := IsScalarTower.of_compHom R S Nℱ
    letI : IsScalarTower R S N𝒢 := IsScalarTower.of_compHom R S N𝒢
    letI : Module R (Sym[S] (SymmetricPower.UFin n) Nℱ) := symmetricPowerModule n
    letI : Module R (Sym[S] (SymmetricPower.UFin n) N𝒢) := symmetricPowerModule n
    apply ModuleCat.hom_ext
    apply symmetricPowerHom_ext_tprod
    intro m
    rw [SymmetricPower.map_tprod, symmetricPowerRestrict_tprod, symmetricPowerRestrict_tprod,
      SymmetricPower.map_tprod]
    congr 1
    ext a
    simpa [Function.comp_def] using sectionHomNaturalityApply (φ := φ) (i := i) (m := m a)

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
    -- Proof comment: compare both composites on the `ιMulti` generators and reduce the sectionwise
    -- equality to naturality of `φ`.
    let R := sectionRing X U
    let S := sectionRing X V
    letI : Algebra R S := (X.presheaf.map i).hom.toAlgebra
    let Mℱ : ModuleCat R := ℱ.val.obj U
    let Nℱ : ModuleCat S := ℱ.val.obj V
    let M𝒢 : ModuleCat R := 𝒢.val.obj U
    let N𝒢 : ModuleCat S := 𝒢.val.obj V
    letI : Module R Nℱ := Module.compHom Nℱ (X.presheaf.map i).hom
    letI : Module R N𝒢 := Module.compHom N𝒢 (X.presheaf.map i).hom
    letI : IsScalarTower R S Nℱ := IsScalarTower.of_compHom R S Nℱ
    letI : IsScalarTower R S N𝒢 := IsScalarTower.of_compHom R S N𝒢
    letI : Module R ↥(⋀[S]^n Nℱ) := exteriorPowerModule n
    letI : Module R ↥(⋀[S]^n N𝒢) := exteriorPowerModule n
    apply ModuleCat.hom_ext
    apply exteriorPowerHom_ext_ιMulti
    intro m
    rw [exteriorPower.map_apply_ιMulti, exteriorPowerRestrict_apply_ιMulti,
      exteriorPowerRestrict_apply_ιMulti, exteriorPower.map_apply_ιMulti]
    congr 1
    ext a
    simpa [Function.comp_def] using sectionHomNaturalityApply (φ := φ) (i := i) (m := m a)

/-- The map on symmetric-power sheaves induced by a morphism of `\mathcal O_X`-modules. -/
noncomputable abbrev symmetricPowerMap
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    symmetricPowerSheaf ℱ n ⟶ symmetricPowerSheaf 𝒢 n :=
  modSheafification.map (symmetricPowerPresheafHom n φ)

/-- The map on exterior-power sheaves induced by a morphism of `\mathcal O_X`-modules. -/
noncomputable abbrev exteriorPowerMap
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    exteriorPowerSheaf ℱ n ⟶ exteriorPowerSheaf 𝒢 n :=
  modSheafification.map (exteriorPowerPresheafHom n φ)

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
    -- Proof comment: fix the left tensor factor, compare the resulting linear maps on `tprod`
    -- generators, and reduce the head entry to naturality of `φ`.
    let R := sectionRing X U
    let S := sectionRing X V
    letI : Algebra R S := (X.presheaf.map i).hom.toAlgebra
    let Mℱ : ModuleCat R := ℱ.val.obj U
    let Nℱ : ModuleCat S := ℱ.val.obj V
    let M𝒢 : ModuleCat R := 𝒢.val.obj U
    let N𝒢 : ModuleCat S := 𝒢.val.obj V
    letI : Module R Nℱ := Module.compHom Nℱ (X.presheaf.map i).hom
    letI : Module R N𝒢 := Module.compHom N𝒢 (X.presheaf.map i).hom
    letI : IsScalarTower R S Nℱ := IsScalarTower.of_compHom R S Nℱ
    letI : IsScalarTower R S N𝒢 := IsScalarTower.of_compHom R S N𝒢
    letI : Module R (Sym[S] (SymmetricPower.UFin n) N𝒢) := symmetricPowerModule n
    letI : Module R (Sym[S] (SymmetricPower.UFin (n + 1)) N𝒢) := symmetricPowerModule (n + 1)
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    let leftMap : Sym[R] (SymmetricPower.UFin n) M𝒢 →ₗ[R]
        Sym[S] (SymmetricPower.UFin (n + 1)) N𝒢 :=
      (((symmetricPowerLeftTensorPresheafMap n φ).app U ≫
          symmetricPowerPresheafMap 𝒢 (n + 1) i).hom).comp (TensorProduct.mk R x)
    let rightMap : Sym[R] (SymmetricPower.UFin n) M𝒢 →ₗ[R]
        Sym[S] (SymmetricPower.UFin (n + 1)) N𝒢 :=
      ((((PresheafOfModules.Monoidal.tensorObj ℱ.val (symmetricPowerPresheaf 𝒢 n)).map i) ≫
          (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
            ((symmetricPowerLeftTensorPresheafMap n φ).app V)).hom).comp
        (TensorProduct.mk R x)
    have hxy : leftMap = rightMap := by
      -- Proof comment: after fixing `x`, the remaining symmetric-power argument is determined by
      -- the `tprod` generators.
      apply symmetricPowerHom_ext_tprod
      intro m
      change (((symmetricPowerLeftTensorPresheafMap n φ).app U ≫
          symmetricPowerPresheafMap 𝒢 (n + 1) i).hom)
          (x ⊗ₜ[R] SymmetricPower.tprod R m) =
        ((((PresheafOfModules.Monoidal.tensorObj ℱ.val (symmetricPowerPresheaf 𝒢 n)).map i) ≫
            (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
              ((symmetricPowerLeftTensorPresheafMap n φ).app V)).hom)
          (x ⊗ₜ[R] SymmetricPower.tprod R m)
      rw [PresheafOfModules.Monoidal.tensorObj_map_tmul, SymmetricPower.leftTensorMap_tmul_tprod,
        symmetricPowerRestrict_tprod, symmetricPowerRestrict_tprod,
        SymmetricPower.leftTensorMap_tmul_tprod]
      congr 1
      ext a
      cases a using Fin.cases with
      | zero =>
          simpa [Function.comp_def] using
            sectionHomNaturalityApply (φ := φ) (i := i) (m := x)
      | succ a =>
          simp [Function.comp_def]
    exact congrArg (fun f => f y) hxy

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
    -- Proof comment: fix the left tensor factor, compare the resulting linear maps on `ιMulti`
    -- generators, and reduce the head entry to naturality of `φ`.
    let R := sectionRing X U
    let S := sectionRing X V
    letI : Algebra R S := (X.presheaf.map i).hom.toAlgebra
    let Mℱ : ModuleCat R := ℱ.val.obj U
    let Nℱ : ModuleCat S := ℱ.val.obj V
    let M𝒢 : ModuleCat R := 𝒢.val.obj U
    let N𝒢 : ModuleCat S := 𝒢.val.obj V
    letI : Module R Nℱ := Module.compHom Nℱ (X.presheaf.map i).hom
    letI : Module R N𝒢 := Module.compHom N𝒢 (X.presheaf.map i).hom
    letI : IsScalarTower R S Nℱ := IsScalarTower.of_compHom R S Nℱ
    letI : IsScalarTower R S N𝒢 := IsScalarTower.of_compHom R S N𝒢
    letI : Module R ↥(⋀[S]^n N𝒢) := exteriorPowerModule n
    letI : Module R ↥(⋀[S]^(n + 1) N𝒢) := exteriorPowerModule (n + 1)
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    let leftMap : ⋀[R]^n M𝒢 →ₗ[R] ⋀[S]^(n + 1) N𝒢 :=
      (((exteriorPowerLeftTensorPresheafMap n φ).app U ≫
          exteriorPowerPresheafMap 𝒢 (n + 1) i).hom).comp (TensorProduct.mk R x)
    let rightMap : ⋀[R]^n M𝒢 →ₗ[R] ⋀[S]^(n + 1) N𝒢 :=
      ((((PresheafOfModules.Monoidal.tensorObj ℱ.val (exteriorPowerPresheaf 𝒢 n)).map i) ≫
          (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
            ((exteriorPowerLeftTensorPresheafMap n φ).app V)).hom).comp
        (TensorProduct.mk R x)
    have hxy : leftMap = rightMap := by
      -- Proof comment: after fixing `x`, the remaining exterior-power argument is determined by
      -- the `ιMulti` generators.
      apply exteriorPowerHom_ext_ιMulti
      intro m
      change (((exteriorPowerLeftTensorPresheafMap n φ).app U ≫
          exteriorPowerPresheafMap 𝒢 (n + 1) i).hom)
          (x ⊗ₜ[R] exteriorPower.ιMulti R n m) =
        ((((PresheafOfModules.Monoidal.tensorObj ℱ.val (exteriorPowerPresheaf 𝒢 n)).map i) ≫
            (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
              ((exteriorPowerLeftTensorPresheafMap n φ).app V)).hom)
          (x ⊗ₜ[R] exteriorPower.ιMulti R n m)
      rw [PresheafOfModules.Monoidal.tensorObj_map_tmul, exteriorPower.leftTensorMap_tmul_ιMulti,
        exteriorPowerRestrict_apply_ιMulti, exteriorPowerRestrict_apply_ιMulti,
        exteriorPower.leftTensorMap_tmul_ιMulti]
      congr 1
      ext a
      cases a using Fin.cases with
      | zero =>
          simpa [Function.comp_def] using
            sectionHomNaturalityApply (φ := φ) (i := i) (m := x)
      | succ a =>
          simp [Function.comp_def]
    exact congrArg (fun f => f y) hxy

/-- The canonical morphism
`ℱ ⊗ Symm[n] 𝒢 ⟶ Symm[n + 1] 𝒢`
induced by a morphism `ℱ ⟶ 𝒢`. -/
noncomputable def symmetricPowerLeftTensorMap
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    moduleTensor ℱ (Symm[n] 𝒢) ⟶ Symm[n + 1] 𝒢 :=
  moduleTensorMap (sheafificationCounitInv ℱ) (𝟙 (Symm[n] 𝒢)) ≫
    (moduleSheafificationTensorIso ℱ.val (symmetricPowerPresheaf 𝒢 n)).hom ≫
    modSheafification.map (symmetricPowerLeftTensorPresheafMap n φ)

/-- The canonical morphism
`ℱ ⊗ Λ^[n] 𝒢 ⟶ Λ^[n + 1] 𝒢`
induced by a morphism `ℱ ⟶ 𝒢`. -/
noncomputable def exteriorPowerLeftTensorMap
    {ℱ 𝒢 : ModX} (n : ℕ) (φ : ℱ ⟶ 𝒢) :
    moduleTensor ℱ (Λ^[n] 𝒢) ⟶ Λ^[n + 1] 𝒢 :=
  moduleTensorMap (sheafificationCounitInv ℱ) (𝟙 (Λ^[n] 𝒢)) ≫
    (moduleSheafificationTensorIso ℱ.val (exteriorPowerPresheaf 𝒢 n)).hom ≫
    modSheafification.map (exteriorPowerLeftTensorPresheafMap n φ)

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

open RingedSpace.Hom

private abbrev preimageOpen (f : X ⟶ Y) (U : (Opens Y)ᵒᵖ) : (Opens X)ᵒᵖ :=
  op ((Opens.map f.hom.base).obj U.unop)

private abbrev preimageRingHom (f : X ⟶ Y) (U : (Opens Y)ᵒᵖ) :
    Y.presheaf.obj U →+* X.presheaf.obj (preimageOpen f U) :=
  (f.hom.c.app U).hom

private abbrev pullbackUnit (f : X ⟶ Y) (ℱ : Y.Modules) :
    ℱ ⟶ (f _*).obj ((f^*).obj ℱ) :=
  (SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)).unit.app ℱ

private noncomputable def exteriorPowerPresheafPushforwardHom
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    exteriorPowerPresheaf ℱ n ⟶
      (PresheafOfModules.pushforward (toRingCatSheafHom f).hom).obj
        (exteriorPowerPresheaf ((f^*).obj ℱ) n) where
  app U := by
    let R := Y.presheaf.obj U
    let S := X.presheaf.obj (preimageOpen f U)
    letI : CommRing R := by infer_instance
    letI : CommRing S := by infer_instance
    letI : Algebra R S := RingHom.toAlgebra (preimageRingHom f U)
    let M : ModuleCat R := ℱ.val.obj U
    let N : ModuleCat S := ((f^*).obj ℱ).val.obj (preimageOpen f U)
    letI : Module R N := Module.compHom N (preimageRingHom f U)
    letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
    letI :
        Module R ↑(exteriorPowerPresheafObj ((f^*).obj ℱ) n (preimageOpen f U)) :=
      exteriorPowerModule n
    let fU : M →ₗ[R] N := (pullbackUnit f ℱ).val.app U |>.hom
    exact
      (show exteriorPowerPresheafObj ℱ n U ⟶
          (ModuleCat.restrictScalars (preimageRingHom f U)).obj
            (exteriorPowerPresheafObj ((f^*).obj ℱ) n (preimageOpen f U)) from
        ModuleCat.ofHom (exteriorPowerRestrict n fU))
  naturality := by
    -- TODO: rewrite the pushforward-side restriction map through `preimageOpen` in the current
    -- owner API and compare the resulting maps on `ιMulti` generators using `pullbackUnit`.
    sorry

private noncomputable def exteriorPowerPresheafToPushforwardExteriorPowerSheaf
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    exteriorPowerPresheaf ℱ n ⟶
      ((f _*).obj (Λ^[n] ((f^*).obj ℱ))).val :=
  exteriorPowerPresheafPushforwardHom f ℱ n ≫
    (PresheafOfModules.pushforward (toRingCatSheafHom f).hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (exteriorPowerPresheaf ((f^*).obj ℱ) n))

private noncomputable def exteriorPowerSheafToPushforwardExteriorPowerSheaf
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    (Λ^[n] ℱ) ⟶ (f _*).obj (Λ^[n] ((f^*).obj ℱ)) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
    (exteriorPowerPresheafToPushforwardExteriorPowerSheaf f ℱ n)

/-- Pullback commutes with the `n`th exterior-power sheaf of a module sheaf on a ringed space. -/
private noncomputable def pullback_exteriorPowerSheaf_hom
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    ((f^*).obj (Λ^[n] ℱ)) ⟶ Λ^[n] ((f^*).obj ℱ) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (toRingCatSheafHom f)).homEquiv _ _).symm
    (exteriorPowerSheafToPushforwardExteriorPowerSheaf f ℱ n)

private theorem pullback_exteriorPowerSheaf_hom_isIso
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    IsIso (pullback_exteriorPowerSheaf_hom f ℱ n) := by
  -- TODO: identify the adjoint mate with the canonical pullback-unit comparison and reuse
  -- `RingedSpace.Hom.pullbackObjUnitToUnit_isIso` after the presheaf pushforward map is normalized.
  sorry

/-- Pullback commutes with the `n`th exterior-power sheaf. -/
noncomputable abbrev pullback_exteriorPowerSheaf
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    ((f^*).obj (Λ^[n] ℱ)) ≅ Λ^[n] ((f^*).obj ℱ) := by
  letI := pullback_exteriorPowerSheaf_hom_isIso f ℱ n
  exact asIso (pullback_exteriorPowerSheaf_hom f ℱ n)

end AlgebraicGeometry.RingedSpace
