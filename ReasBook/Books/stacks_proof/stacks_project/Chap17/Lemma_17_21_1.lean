import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.LinearAlgebra.PowerOperations
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_5_1

open scoped AlgebraicGeometry TensorProduct
open CategoryTheory Opposite TensorProduct
open CategoryTheory.MonoidalCategory
open Functor.OplaxMonoidal
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

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

local notation "ModX" => SheafOfModules X.ringCatSheaf
private noncomputable abbrev modSheafification :
    PresheafOfModules X.ringCatSheaf.obj ⥤ ModX :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

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

/-- Helper for Chap17 Lemma 17 21 1: the canonical oplax-monoidal sheafification comparison from
the sheafification of a tensor-product presheaf to the tensor product of the two sheafifications.
-/
private abbrev moduleSheafificationTensorComparison
    (ℱ 𝒢 : PresheafOfModules X.ringCatSheaf.obj) :
    modSheafification.obj (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) ⟶
      moduleTensor (modSheafification.obj ℱ) (modSheafification.obj 𝒢) :=
  -- Proof comment: use the canonical oplax-monoidal comparison of sheafification itself.
  modSheafification.map
    (PresheafOfModules.Monoidal.tensorHom (sheafificationUnitToVal ℱ) (sheafificationUnitToVal 𝒢))

private instance moduleSheafificationTensorComparison_isIso
    (ℱ 𝒢 : PresheafOfModules X.ringCatSheaf.obj) :
    IsIso (moduleSheafificationTensorComparison ℱ 𝒢) := by
  -- Proof comment: this is exactly the canonical oplax-monoidal comparison `δ` for
  -- sheafification.
  change IsIso
    (Functor.OplaxMonoidal.δ
      (_root_.moduleSheafification (J := Opens.grothendieckTopology X) X.sheaf) ℱ 𝒢)
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

/-- Helper for Chap17 Lemma 17 21 1: the presheaf exterior-power restriction map sends each
standard generator to the generator obtained by restricting every entry. -/
private theorem exteriorPowerPresheafMap_apply_ιMulti
    (ℱ : ModX) (n : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : Fin n → ℱ.val.obj U) :
    (exteriorPowerPresheafMap ℱ n i).hom (exteriorPower.ιMulti (sectionRing X U) n m) =
      exteriorPower.ιMulti (sectionRing X V) n ((ℱ.val.map i).hom ∘ m) := by
  -- Proof comment: the presheaf restriction map is defined from `exteriorPowerRestrict`, so the
  -- generator formula is exactly the sectionwise restriction formula for that map.
  simp [exteriorPowerPresheafMap, exteriorPowerRestrict_apply_ιMulti]

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

/-- Helper for Chap17 Lemma 17 21 1: the presheaf symmetric-power restriction map sends each
standard generator to the generator obtained by restricting every entry. -/
private theorem symmetricPowerPresheafMap_apply_tprod
    (ℱ : ModX) (n : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (m : SymmetricPower.UFin n → ℱ.val.obj U) :
    (symmetricPowerPresheafMap ℱ n i).hom
        (SymmetricPower.tprod (sectionRing X U) m) =
      SymmetricPower.tprod (sectionRing X V) ((ℱ.val.map i).hom ∘ m) := by
  -- Proof comment: the presheaf restriction map is defined from `symmetricPowerRestrict`, so the
  -- generator formula is exactly the sectionwise restriction formula for that map.
  simp [symmetricPowerPresheafMap, symmetricPowerRestrict_tprod]

/-- Helper for Lemma 17.21.1: restricting sections along a composite equals iterated restriction
on each element. -/
private theorem sectionMapCompApply
    (ℱ : ModX) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (m : ℱ.val.obj U) :
    (ℱ.val.map (i ≫ j)).hom m = (ℱ.val.map j).hom ((ℱ.val.map i).hom m) := by
  -- Proof comment: evaluate the presheaf composition law on the chosen section.
  simpa using congrArg (fun h => (ModuleCat.Hom.hom h) m) (ℱ.val.map_comp i j)

/-- Helper for Chap17 Lemma 17 21 1: restricting a section along the identity morphism fixes that
section. -/
private theorem sectionMapIdApply
    (ℱ : ModX) (U : (Opens X)ᵒᵖ) (m : ℱ.val.obj U) :
    (ℱ.val.map (𝟙 U)).hom m = m := by
  -- Proof comment: after expanding the identity restriction-of-scalars transport, the component
  -- map of `ℱ.val.map_id` acts as the identity on each section.
  simpa using
    (ModuleCat.restrictScalarsId'App_inv_apply (X.presheaf.map (𝟙 U)).hom
      (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U)) (ℱ.val.obj U) m)

/-- Helper for Chap17 Lemma 17 21 1: the inverse identity restriction-of-scalars transport is
pointwise the identity on sections. -/
private theorem sectionMapIdTransportApply
    (ℱ : ModX) (U : (Opens X)ᵒᵖ) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom
        ((ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
          (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
          (ℱ.val.obj U))) m = m := by
  -- Proof comment: evaluate the inverse identity restriction-of-scalars comparison on the chosen
  -- section and use the canonical pointwise formula.
  simpa using
    (ModuleCat.restrictScalarsId'App_inv_apply (X.presheaf.map (𝟙 U)).hom
      (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U)) (ℱ.val.obj U) m)

/-- Helper for Lemma 17.21.1: a morphism of module sheaves commutes with restriction on each
section. -/
private theorem sectionHomNaturalityApply
    {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : ℱ.val.obj U) :
    (𝒢.val.map i).hom ((φ.val.app U).hom m) = (φ.val.app V).hom ((ℱ.val.map i).hom m) := by
  -- Proof comment: evaluate the naturality square of `φ` on the chosen section.
  simpa using congrArg (fun h => (ModuleCat.Hom.hom h) m) (φ.val.naturality i).symm

/-- Helper for Chap17 Lemma 17 21 1: the inverse composite restriction-of-scalars transport
evaluates to the expected iterated restriction on sections. -/
private theorem sectionMapCompTransportApply
    (ℱ : ModX) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom
        (ℱ.val.map i ≫
          (ModuleCat.restrictScalars _).map (ℱ.val.map j) ≫
            (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
              (X.presheaf.map j).hom
              (X.presheaf.map (i ≫ j)).hom
              (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
              (ℱ.val.obj W))) m =
      (ℱ.val.map j).hom ((ℱ.val.map i).hom m) := by
  -- Proof comment: expand the composite restriction-of-scalars comparison and then apply the
  -- presheaf composition law on the chosen section.
  simpa [ModuleCat.restrictScalarsComp'App_inv_apply] using sectionMapCompApply ℱ i j m

private theorem exteriorPowerPresheafMap_id
    (ℱ : ModX) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    exteriorPowerPresheafMap ℱ n (𝟙 U) =
        (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (exteriorPowerPresheafObj ℱ n U) := by
  -- Route correction: compare the two endomorphisms on the standard alternating generators and
  -- use the exterior-power extensionality lemma to avoid quotient-level induction.
  refine ModuleCat.hom_ext ?_
  -- Proof comment: both maps are linear endomorphisms of the sectionwise exterior power, so it is
  -- enough to check them on `ιMulti`.
  refine exteriorPowerHom_ext_ιMulti (R := sectionRing X U) (M := ℱ.val.obj U)
    (N := ↥(⋀[sectionRing X U]^n (ℱ.val.obj U))) n ?_
  intro m
  -- Proof comment: the presheaf restriction is the identity on each entry, and the
  -- `restrictScalarsId'` comparison is pointwise trivial on the exterior-power object.
  simp [exteriorPowerPresheafMap_apply_ιMulti, ModuleCat.restrictScalarsId'App_inv_apply]

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
  -- Route correction: prove the composite coherence on generators, then package the resulting
  -- equality of linear maps through `ModuleCat.hom_ext`.
  refine ModuleCat.hom_ext ?_
  -- Proof comment: `ιMulti` spans the exterior power, so generator agreement suffices.
  refine exteriorPowerHom_ext_ιMulti (R := sectionRing X U) (M := ℱ.val.obj U)
    (N := ↥(⋀[sectionRing X W]^n (ℱ.val.obj W))) n ?_
  intro m
  -- Proof comment: the direct composite and the iterated composite both restrict every entry of
  -- `m`, and the final transport is the standard `restrictScalarsComp'` comparison.
  simp [exteriorPowerPresheafMap_apply_ιMulti, ModuleCat.restrictScalarsComp'App_inv_apply,
    sectionMapCompApply, Function.comp_def]

private theorem symmetricPowerPresheafMap_id
    (ℱ : ModX) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    symmetricPowerPresheafMap ℱ n (𝟙 U) =
        (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (symmetricPowerPresheafObj ℱ n U) := by
  -- Route correction: compare the induced symmetric-power endomorphisms on pure tensor
  -- generators and use the quotient extensionality lemma from `symmetricPowerHom_ext_tprod`.
  refine ModuleCat.hom_ext ?_
  -- Proof comment: a symmetric-power linear map is determined by its values on `tprod`.
  refine symmetricPowerHom_ext_tprod (R := sectionRing X U) (M := ℱ.val.obj U)
    (N := Sym[sectionRing X U] (SymmetricPower.UFin n) (ℱ.val.obj U)) n ?_
  intro m
  -- Proof comment: the restriction map fixes each section on the identity open inclusion, and the
  -- inverse identity transport acts trivially on the sectionwise symmetric power.
  simp [symmetricPowerPresheafMap_apply_tprod, ModuleCat.restrictScalarsId'App_inv_apply]

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
  -- Route correction: compare the direct and iterated symmetric-power restrictions on `tprod`
  -- generators, then descend the equality to the quotient-defined symmetric power.
  refine ModuleCat.hom_ext ?_
  -- Proof comment: `tprod` generators span the symmetric power, so generator agreement suffices.
  refine symmetricPowerHom_ext_tprod (R := sectionRing X U) (M := ℱ.val.obj U)
    (N := Sym[sectionRing X W] (SymmetricPower.UFin n) (ℱ.val.obj W)) n ?_
  intro m
  -- Proof comment: both composites restrict every tensor entry in the same way, and the terminal
  -- transport is exactly the `restrictScalarsComp'` comparison.
  simp [symmetricPowerPresheafMap_apply_tprod, ModuleCat.restrictScalarsComp'App_inv_apply,
    sectionMapCompApply, Function.comp_def]

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
    -- Route correction: compare the naturality square on pure symmetric tensors rather than
    -- unfolding the quotient presentation of the symmetric power.
    refine ModuleCat.hom_ext ?_
    -- Proof comment: the source and target linear maps are determined by their values on `tprod`.
    refine symmetricPowerHom_ext_tprod (R := sectionRing X U) (M := ℱ.val.obj U)
      (N := Sym[sectionRing X V] (SymmetricPower.UFin n) (𝒢.val.obj V)) n ?_
    intro m
    -- Proof comment: both composites send each tensor entry through the same sectionwise
    -- naturality square for `φ`.
    simp [symmetricPowerPresheafMap_apply_tprod, SymmetricPower.map_tprod,
      sectionHomNaturalityApply, Function.comp_def]

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
    -- Route correction: compare the exterior-power naturality square on alternating generators,
    -- which avoids any brittle transport through the quotient presentation.
    refine ModuleCat.hom_ext ?_
    -- Proof comment: `ιMulti` spans the exterior power, so equality on these generators is
    -- enough to identify the two linear maps.
    refine exteriorPowerHom_ext_ιMulti (R := sectionRing X U) (M := ℱ.val.obj U)
      (N := ↥(⋀[sectionRing X V]^n (𝒢.val.obj V))) n ?_
    intro m
    -- Proof comment: both composites apply the same restriction-naturality relation for `φ`
    -- entrywise inside `ιMulti`.
    simp [exteriorPowerPresheafMap_apply_ιMulti, exteriorPower.map_apply_ιMulti,
      sectionHomNaturalityApply, Function.comp_def]

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

/-- Helper for Chap17 Lemma 17 21 1: the tensor-product presheaf restriction map carries a pure
tensor to the tensor of the restricted factors. -/
private theorem tensorPresheafMap_apply_tmul
    {ℱ 𝒢 : ModX} {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (x : ℱ.val.obj U) (y : 𝒢.val.obj U) :
    (((PresheafOfModules.Monoidal.tensorObj ℱ.val 𝒢.val).map i).hom)
        (x ⊗ₜ[sectionRing X U] y) =
      (ℱ.val.map i).hom x ⊗ₜ[sectionRing X V] (𝒢.val.map i).hom y := by
  -- Proof comment: the presheaf tensor product is defined objectwise, so restriction acts
  -- entrywise on pure tensors.
  simpa using
    (PresheafOfModules.Monoidal.tensorObj_map_tmul (M₁ := ℱ.val) (M₂ := 𝒢.val) i x y)

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
    -- Route correction: compare the tensor-product naturality square on pure tensors and the
    -- standard `tprod` generators in the symmetric-power factor.
    refine ModuleCat.hom_ext ?_
    -- Proof comment: tensor-product maps are determined by their values on pure tensors, and the
    -- symmetric-power factor is generated by `tprod`.
    refine TensorProduct.ext ?_
    ext x m
    -- Proof comment: both composites restrict the left tensor factor and every symmetric tensor
    -- entry in the same way before applying the sectionwise left-tensor map.
    simp [tensorPresheafMap_apply_tmul, symmetricPowerPresheafMap_apply_tprod,
      sectionHomNaturalityApply, Function.comp_def]

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
    -- Route correction: compare the tensor-product naturality square on pure tensors and the
    -- alternating generators `ιMulti` in the exterior-power factor.
    refine ModuleCat.hom_ext ?_
    -- Proof comment: tensor-product maps are determined by pure tensors, and the exterior-power
    -- factor is generated by the alternating tensors `ιMulti`.
    refine TensorProduct.ext ?_
    ext x m
    -- Proof comment: both composites restrict the left tensor factor and every alternating entry
    -- in the same way before applying the sectionwise left-tensor map.
    simp [tensorPresheafMap_apply_tmul, exteriorPowerPresheafMap_apply_ιMulti,
      sectionHomNaturalityApply, Function.comp_def]

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

/-- Helper for Chap17 Lemma 17 21 1: the pullback-unit morphism commutes with restriction on
sections. -/
private theorem pullbackUnit_apply_naturality
    (f : X ⟶ Y) (ℱ : Y.Modules)
    {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) (m : ℱ.val.obj U) :
    (((f _*).obj ((f^*).obj ℱ)).val.map i).hom (((pullbackUnit f ℱ).val.app U).hom m) =
      ((pullbackUnit f ℱ).val.app V).hom ((ℱ.val.map i).hom m) := by
  -- Proof comment: evaluate the naturality square of the pullback unit on the chosen section.
  simpa using congrArg (fun h => (ModuleCat.Hom.hom h) m) ((pullbackUnit f ℱ).val.naturality i).symm

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
    intro U V i
    -- Route correction: compare the pushforward naturality square on the alternating generators
    -- `ιMulti` rather than unfolding the pushforward construction on all quotients at once.
    refine ModuleCat.hom_ext ?_
    -- Proof comment: the two sectionwise maps are linear over `Γ(U, 𝒪_Y)`, so agreement on the
    -- standard alternating generators suffices.
    refine exteriorPowerHom_ext_ιMulti (R := sectionRing Y U) (M := ℱ.val.obj U)
      (N := ↥(⋀[sectionRing X (preimageOpen f V)]^n
        (((f^*).obj ℱ).val.obj (preimageOpen f V)))) n ?_
    intro m
    -- Proof comment: both composites first restrict every entry of `m`, then apply the pullback
    -- unit componentwise; `pullbackUnit_apply_naturality` identifies those two entrywise routes.
    simp [PresheafOfModules.pushforward_obj_map_apply',
      exteriorPowerPresheafMap_apply_ιMulti, exteriorPowerRestrict_apply_ιMulti,
      pullbackUnit_apply_naturality, Function.comp_def]

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

/-- Helper for Chap17 Lemma 17 21 1: after applying the pullback-pushforward adjunction, the
pullback comparison is exactly the pushed-forward exterior-power comparison used to define it. -/
private theorem pullbackExteriorPowerComparison_homEquiv
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    ((SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)).homEquiv _ _)
      (pullback_exteriorPowerSheaf_hom f ℱ n) =
        exteriorPowerSheafToPushforwardExteriorPowerSheaf f ℱ n := by
  -- Proof comment: `pullback_exteriorPowerSheaf_hom` is defined as the inverse image of
  -- `exteriorPowerSheafToPushforwardExteriorPowerSheaf` under the adjunction equivalence.
  exact Equiv.apply_symm_apply
    (((SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)).homEquiv _ _))
    (exteriorPowerSheafToPushforwardExteriorPowerSheaf f ℱ n)

/-- Helper for Chap17 Lemma 17 21 1: after applying the sheafification adjunction, the sheaf-level
comparison is exactly the sheafified presheaf comparison used to define it. -/
private theorem exteriorPowerSheafComparison_sheafification_homEquiv
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _)
      (exteriorPowerSheafToPushforwardExteriorPowerSheaf f ℱ n) =
        exteriorPowerPresheafToPushforwardExteriorPowerSheaf f ℱ n := by
  -- Proof comment: `exteriorPowerSheafToPushforwardExteriorPowerSheaf` is defined by inverting
  -- the sheafification adjunction on the presheaf-level comparison.
  exact Equiv.apply_symm_apply
    (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _))
    (exteriorPowerPresheafToPushforwardExteriorPowerSheaf f ℱ n)

/-- Helper for Chap17 Lemma 17 21 1: pulling back the sheafified exterior-power presheaf can be
rewritten as sheafification of the pulled-back exterior-power presheaf. -/
private noncomputable abbrev pullbackExteriorPowerSheafSourceIso
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    ((f^*).obj (Λ^[n] ℱ)) ≅
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback (toRingCatSheafHom f).hom).obj
          (exteriorPowerPresheaf ℱ n)) :=
  (SheafOfModules.sheafificationCompPullback (φ := toRingCatSheafHom f)).app
    (exteriorPowerPresheaf ℱ n)

/-- Helper for Chap17 Lemma 17 21 1: the presheaf comparison is the mate of the pushed-forward
presheaf exterior-power map under the presheaf pullback-pushforward adjunction. -/
private noncomputable def pullbackExteriorPowerPresheafComparison
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    ((PresheafOfModules.pullback (toRingCatSheafHom f).hom).obj
      (exteriorPowerPresheaf ℱ n)) ⟶
        exteriorPowerPresheaf ((f^*).obj ℱ) n :=
  ((PresheafOfModules.pullbackPushforwardAdjunction
      (toRingCatSheafHom f).hom).homEquiv _ _).symm
    (exteriorPowerPresheafPushforwardHom f ℱ n)

/-- Helper for Chap17 Lemma 17 21 1: applying the presheaf pullback-pushforward adjunction to the
presheaf comparison recovers the pushed-forward presheaf map. -/
private theorem pullbackExteriorPowerPresheafComparison_homEquiv
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    ((PresheafOfModules.pullbackPushforwardAdjunction
        (toRingCatSheafHom f).hom).homEquiv _ _)
      (pullbackExteriorPowerPresheafComparison f ℱ n) =
        exteriorPowerPresheafPushforwardHom f ℱ n := by
  -- Proof comment: this is the defining adjunction equation for the presheaf mate.
  exact Equiv.apply_symm_apply
    (((PresheafOfModules.pullbackPushforwardAdjunction
        (toRingCatSheafHom f).hom).homEquiv _ _))
    (exteriorPowerPresheafPushforwardHom f ℱ n)

private theorem pullback_exteriorPowerSheaf_hom_isIso
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    IsIso (pullback_exteriorPowerSheaf_hom f ℱ n) := by
  -- Route correction: the remaining step is no longer the raw adjoint-mate normalization.
  -- The source has already been rewritten through `sheafificationCompPullback`, and the open
  -- problem is to show that the presheaf mate is the sectionwise exterior-power base-change
  -- isomorphism induced by scalar extension.
  let eSource := pullbackExteriorPowerSheafSourceIso f ℱ n
  let ψ := pullbackExteriorPowerPresheafComparison f ℱ n
  have hAdj :
      ((SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)).homEquiv _ _)
        (pullback_exteriorPowerSheaf_hom f ℱ n) =
          exteriorPowerSheafToPushforwardExteriorPowerSheaf f ℱ n :=
    pullbackExteriorPowerComparison_homEquiv f ℱ n
  have hSheaf :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _)
        (exteriorPowerSheafToPushforwardExteriorPowerSheaf f ℱ n) =
          exteriorPowerPresheafToPushforwardExteriorPowerSheaf f ℱ n :=
    exteriorPowerSheafComparison_sheafification_homEquiv f ℱ n
  have hPresheaf :
      ((PresheafOfModules.pullbackPushforwardAdjunction
          (toRingCatSheafHom f).hom).homEquiv _ _) ψ =
        exteriorPowerPresheafPushforwardHom f ℱ n :=
    pullbackExteriorPowerPresheafComparison_homEquiv f ℱ n
  -- TODO: prove that `ψ` is the sectionwise base-change isomorphism by identifying each
  -- component with the Chapter 10 linear equivalence
  -- `baseChangeExteriorPowerLinearEquiv`; then `eSource.hom ≫ modSheafification.map ψ` is an
  -- isomorphism and the equalities above identify it with the target comparison morphism.
  let _ := eSource
  let _ := hAdj
  let _ := hSheaf
  let _ := hPresheaf
  sorry

/-- Pullback commutes with the `n`th exterior-power sheaf. -/
noncomputable abbrev pullback_exteriorPowerSheaf
    (f : X ⟶ Y) (ℱ : Y.Modules) (n : ℕ) :
    ((f^*).obj (Λ^[n] ℱ)) ≅ Λ^[n] ((f^*).obj ℱ) := by
  letI := pullback_exteriorPowerSheaf_hom_isIso f ℱ n
  exact asIso (pullback_exteriorPowerSheaf_hom f ℱ n)

end AlgebraicGeometry.RingedSpace
