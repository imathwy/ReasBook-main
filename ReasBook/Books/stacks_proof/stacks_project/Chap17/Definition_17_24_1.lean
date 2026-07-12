import Mathlib
import StacksProject_2024.Chap15.Definition_15_28_1
import StacksProject_2024.Chap17.Lemma_17_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry TensorProduct
open CategoryTheory
open Opposite
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => SheafOfModules X.ringCatSheaf
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
private noncomputable abbrev modSheafification :
    PresheafOfModules X.ringCatSheaf.obj ⥤ ModX :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/- Domain-style sampling for Definition 17.24.1:
- primary domain: sheaf Koszul complexes attached to a morphism `φ : \mathcal E \to \mathcal O_X`;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `exteriorPowerPresheaf` and `exteriorPowerSheaf` from Chapter 17,
  `_root_.koszulComplex` from Definition 15.28.1,
  and `_root_.koszulDifferential` from Definition 15.28.1;
- best owner abstraction: the source-facing object is the Koszul complex of `φ`, whose degree-`n`
  term is `Λ^[n] ℰ`; the sectionwise homogeneous contraction maps are auxiliary bridge data
  sheafified from the canonical linear-model operators;
- primitive data: a morphism `φ : ℰ ⟶ \mathcal O_X`;
- derived API: the sectionwise homogeneous differentials, their sheafified maps, and the resulting
  complex.

Source/core/bridge triage:
- `source-facing`: `koszulComplex`;
- `core/canonical`: `RingedSpace.Modules X`, `Λ^[n] ℰ`, `exteriorPowerPresheaf`,
  `exteriorPowerSheaf`, `_root_.koszulComplex`, and `_root_.koszulDifferential`;
- `bridge/view`: the internal sectionwise homogeneous differentials and their sheafified maps. -/

/-- The commutative ring of sections of the structure sheaf over an open set. -/
private abbrev sectionRing (X : RingedSpace) (U : (Opens X)ᵒᵖ) :=
  X.presheaf.obj U

/-- The degree `n + 1` homogeneous Koszul differential on sections over `U`. -/
private noncomputable abbrev sectionKoszulDifferential
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    (exteriorPowerPresheaf ℰ (n + 1)).obj U ⟶ (exteriorPowerPresheaf ℰ n).obj U :=
  let R := sectionRing X U
  let E := ℰ.val.obj U
  letI : CommRing R := inferInstance
  let φU : E →ₗ[R] R := (φ.val.app U).hom
  _root_.koszulDifferential φU n

/-- Helper for Definition 17.24.1: restricting the linear form `φ` to a smaller open set agrees
with first restricting the section and then applying `φ`. -/
private theorem section_linear_form_naturality
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : ℰ.val.obj U) :
    (X.presheaf.map i).hom (((φ.val.app U).hom) m) =
      ((φ.val.app V).hom) (((ℰ.val.map i).hom) m) := by
  -- Proof comment: this is the naturality square for the sheaf morphism `φ`, evaluated at `m`.
  simpa using
    (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (φ.val.naturality i)) m).symm

/-- Helper for Definition 17.24.1: restriction in the exterior-power presheaf sends an `ιMulti`
generator to the entrywise restricted generator. -/
private theorem exterior_power_presheaf_map_apply_ιMulti
    {ℰ : ModX} {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (m : Fin n → ℰ.val.obj U) :
    ((exteriorPowerPresheaf ℰ n).map i).hom
        (exteriorPower.ιMulti (sectionRing X U) n m) =
      exteriorPower.ιMulti (sectionRing X V) n
        (fun j ↦ show ℰ.val.obj V from ((ℰ.val.map i).hom) (m j)) := by
  -- Proof comment: unfold the presheaf restriction map to the universal exterior-power lift.
  let R := sectionRing X U
  let S := sectionRing X V
  let M := ℰ.val.obj U
  let N := ℰ.val.obj V
  letI : Algebra R S := (X.presheaf.map i).hom.toAlgebra
  letI : Module R N := Module.compHom N (X.presheaf.map i).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  letI : Module R ↥(⋀[S]^n N) := Module.compHom _ (algebraMap R S)
  let f : M →ₗ[R] N := (ℰ.val.map i).hom
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
    exteriorPower.ιMulti S n (fun j ↦ f (m j))
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

/-- Helper for Definition 17.24.1: restriction on exterior powers carries a scalar multiple of an
`ιMulti` generator to the restricted scalar times the restricted generator. -/
private theorem exterior_power_presheaf_map_apply_smul_ιMulti
    {ℰ : ModX} {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (a : sectionRing X U) (m : Fin n → ℰ.val.obj U) :
    ((exteriorPowerPresheaf ℰ n).map i).hom
        (a • exteriorPower.ιMulti (sectionRing X U) n m) =
      ((X.presheaf.map i).hom a : sectionRing X V) •
        exteriorPower.ιMulti (sectionRing X V) n
          (fun j ↦ show ℰ.val.obj V from ((ℰ.val.map i).hom) (m j)) := by
  -- Proof comment: package the `map_smul` and generator-restriction rewrites into one stable step.
  let R := sectionRing X U
  let S := sectionRing X V
  let N := ℰ.val.obj V
  letI : Algebra R S := (X.presheaf.map i).hom.toAlgebra
  letI : Module R N := Module.compHom N (X.presheaf.map i).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  letI : Module R ↥(⋀[S]^n N) := Module.compHom _ (algebraMap R S)
  calc
    ((exteriorPowerPresheaf ℰ n).map i).hom
        (a • exteriorPower.ιMulti (sectionRing X U) n m)
      = ((X.presheaf.map i).hom a : sectionRing X V) •
          (show ↥(⋀[S]^n N) from
            (((exteriorPowerPresheaf ℰ n).map i).hom
              (exteriorPower.ιMulti (sectionRing X U) n m))) := by
          -- Proof comment: first use `R`-linearity of the restriction map.
          simpa using
            (ModuleCat.Hom.hom ((exteriorPowerPresheaf ℰ n).map i)).map_smul a
              (exteriorPower.ιMulti (sectionRing X U) n m)
    _ = ((X.presheaf.map i).hom a : sectionRing X V) •
          exteriorPower.ιMulti (sectionRing X V) n
            (fun j ↦ show ℰ.val.obj V from ((ℰ.val.map i).hom) (m j)) := by
          rw [exterior_power_presheaf_map_apply_ιMulti]

/-- Helper for Definition 17.24.1: the signed coefficient in one Koszul summand is compatible
with restricting sections. -/
private theorem section_koszul_signed_coefficient_naturality
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) {n : ℕ}
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (k : Fin (n + 1))
    (m : Fin (n + 1) → ℰ.val.obj U) :
    (X.presheaf.map i).hom
        (((-1 : sectionRing X U) ^ (k : ℕ)) *
          (show sectionRing X U from ((φ.val.app U).hom (m k)))) =
      (((-1 : sectionRing X V) ^ (k : ℕ)) *
        (show sectionRing X V from ((φ.val.app V).hom (((ℰ.val.map i).hom) (m k))))) := by
  -- Proof comment: move restriction through the product and then use naturality of `φ`.
  rw [map_mul, map_pow]
  simp only [map_neg, map_one]
  rw [section_linear_form_naturality (φ := φ) i (m k)]

/-- Helper for Definition 17.24.1: one summand in the Koszul differential generator formula is
stable under restriction. -/
private theorem section_koszul_generator_term_naturality
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (m : Fin (n + 1) → ℰ.val.obj U) (k : Fin (n + 1)) :
    ((exteriorPowerPresheaf ℰ n).map i).hom
        (((( -1 : sectionRing X U) ^ (k : ℕ) *
            (show sectionRing X U from ((φ.val.app U).hom (m k)))) •
            exteriorPower.ιMulti (sectionRing X U) n (fun j ↦ m (Fin.succAbove k j)))) =
      (((-1 : sectionRing X V) ^ (k : ℕ) *
          (show sectionRing X V from ((φ.val.app V).hom (((ℰ.val.map i).hom) (m k)))) ) •
        exteriorPower.ιMulti (sectionRing X V) n
          (fun j ↦ show ℰ.val.obj V from ((ℰ.val.map i).hom) (m (Fin.succAbove k j)))) := by
  -- Proof comment: transport the scalar multiple of the deleted generator in one rewrite.
  rw [exterior_power_presheaf_map_apply_smul_ιMulti]
  rw [section_koszul_signed_coefficient_naturality (φ := φ) (n := n) (i := i) (k := k) (m := m)]

/-- Helper for Definition 17.24.1: on `ιMulti` generators, the sectionwise Koszul differential
commutes with restricting sections. -/
private theorem section_koszul_differential_on_generators
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (m : Fin (n + 1) → ℰ.val.obj U) :
    (((exteriorPowerPresheaf ℰ (n + 1)).map i ≫
        (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
          (sectionKoszulDifferential φ n V)).hom)
      (exteriorPower.ιMulti (sectionRing X U) (n + 1) m) =
    (((sectionKoszulDifferential φ n U) ≫
        (exteriorPowerPresheaf ℰ n).map i).hom)
      (exteriorPower.ιMulti (sectionRing X U) (n + 1) m) := by
  -- Proof comment: both composites expand to the same alternating deletion sum after rewriting
  -- restriction on generators and the scalar coefficients coming from `φ`.
  let R := sectionRing X U
  let S := sectionRing X V
  let M := ℰ.val.obj U
  let N := ℰ.val.obj V
  letI : Algebra R S := (X.presheaf.map i).hom.toAlgebra
  letI : Module R N := Module.compHom N (X.presheaf.map i).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  letI : Module R ↥(⋀[S]^n N) := Module.compHom _ (algebraMap R S)
  let f : M →ₗ[R] N := (ℰ.val.map i).hom
  let φU : M →ₗ[R] R := (φ.val.app U).hom
  let φV : N →ₗ[S] S := (φ.val.app V).hom
  -- Route correction: compare the two composites only after freezing scalar transport and
  -- generator transport into the dedicated rewrite lemmas above.
  change
    (_root_.koszulDifferentialLinearMap φV n)
        (((exteriorPowerPresheaf ℰ (n + 1)).map i).hom
          (exteriorPower.ιMulti R (n + 1) m)) =
      ((exteriorPowerPresheaf ℰ n).map i).hom
        ((_root_.koszulDifferentialLinearMap φU n)
          (exteriorPower.ιMulti R (n + 1) m))
  rw [exterior_power_presheaf_map_apply_ιMulti]
  rw [_root_.koszulDifferentialLinearMap_apply_ιMulti_eq_sum]
  rw [_root_.koszulDifferentialLinearMap_apply_ιMulti_eq_sum]
  have hmap_sum :
      ((exteriorPowerPresheaf ℰ n).map i).hom
          (∑ k : Fin (n + 1),
            (((-1 : R) ^ (k : ℕ) * φU (m k)) •
              exteriorPower.ιMulti R n (fun j ↦ m (Fin.succAbove k j)))) =
        ∑ k : Fin (n + 1),
          ((exteriorPowerPresheaf ℰ n).map i).hom
            (((( -1 : R) ^ (k : ℕ) * φU (m k)) •
              exteriorPower.ιMulti R n (fun j ↦ m (Fin.succAbove k j)))) := by
    -- Proof comment: distribute the restriction map across the alternating sum once.
    simpa using
      (_root_.map_sum (ModuleCat.Hom.hom ((exteriorPowerPresheaf ℰ n).map i))
        (fun k : Fin (n + 1) ↦
          (((-1 : R) ^ (k : ℕ) * φU (m k)) •
            exteriorPower.ιMulti R n (fun j ↦ m (Fin.succAbove k j))))
        Finset.univ)
  refine Eq.trans ?_ hmap_sum.symm
  refine Finset.sum_congr rfl ?_
  intro k hk
  simpa [f, φU, φV] using
    (section_koszul_generator_term_naturality (φ := φ) (n := n) (i := i) (m := m) k).symm

/-- The sectionwise Koszul differentials are compatible with restriction. -/
private theorem sectionKoszulDifferential_naturality
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (exteriorPowerPresheaf ℰ (n + 1)).map i ≫
        (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
          (sectionKoszulDifferential φ n V) =
      sectionKoszulDifferential φ n U ≫ (exteriorPowerPresheaf ℰ n).map i := by
  -- Proof comment: the exterior powers are generated by the `ιMulti` sections, so it suffices
  -- to compare the two composites on generators.
  let R := sectionRing X U
  let S := sectionRing X V
  let M := ℰ.val.obj U
  let N := ℰ.val.obj V
  letI : Algebra R S := (X.presheaf.map i).hom.toAlgebra
  letI : Module R N := Module.compHom N (X.presheaf.map i).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  letI : Module R ↥(⋀[S]^n N) := Module.compHom _ (algebraMap R S)
  apply ModuleCat.hom_ext
  change
    ((((exteriorPowerPresheaf ℰ (n + 1)).map i ≫
        (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
          (sectionKoszulDifferential φ n V)).hom) :
      ⋀[R]^(n + 1) M →ₗ[R] ↥(⋀[S]^n N)) =
      ((((sectionKoszulDifferential φ n U) ≫
          (exteriorPowerPresheaf ℰ n).map i).hom) :
        ⋀[R]^(n + 1) M →ₗ[R] ↥(⋀[S]^n N))
  refine (exteriorPower.linearMap_ext
    (R := R) (n := n + 1) (M := M) (N := ↥(⋀[S]^n N)) ?_)
  ext m
  simpa using section_koszul_differential_on_generators (φ := φ) n i m

/-- Helper for Definition 17.24.1: the sectionwise Koszul differentials square to zero on every
open set. -/
private theorem section_koszul_differential_sq
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    sectionKoszulDifferential φ (n + 1) U ≫ sectionKoszulDifferential φ n U = 0 := by
  -- Proof comment: after naming the local ring and module, this is exactly the `d_comp_d`
  -- relation in the module-level Koszul complex.
  let R := sectionRing X U
  let E := ℰ.val.obj U
  letI : CommRing R := inferInstance
  let φU : E →ₗ[R] R := (φ.val.app U).hom
  change _root_.koszulDifferential φU (n + 1) ≫ _root_.koszulDifferential φU n = 0
  simpa [Nat.add_assoc] using
    ((_root_.koszulComplex φU).d_comp_d ((n + 1) + 1) (n + 1) n)

-- The implementation presheaf morphism giving the degree `n + 1` Koszul differential.
private noncomputable def presheafKoszulDifferential
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) :
    exteriorPowerPresheaf ℰ (n + 1) ⟶ exteriorPowerPresheaf ℰ n :=
  { app := sectionKoszulDifferential φ n
    naturality := sectionKoszulDifferential_naturality φ n }

/-- The degree `n + 1` Koszul differential on exterior-power sheaves. -/
private noncomputable abbrev sheafKoszulDifferential
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) :
    (Λ^[n + 1] ℰ) ⟶ (Λ^[n] ℰ) :=
  modSheafification.map (presheafKoszulDifferential φ n)

/-- Consecutive Koszul differentials on exterior-power sheaves compose to zero. -/
private theorem sheafKoszulDifferential_sq
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) :
    sheafKoszulDifferential φ (n + 1) ≫ sheafKoszulDifferential φ n =
      0 := by
  -- Proof comment: the presheaf composite is zero objectwise, and sheafification preserves
  -- composition and zero morphisms.
  have hpresheaf :
      presheafKoszulDifferential φ (n + 1) ≫ presheafKoszulDifferential φ n = 0 := by
    ext U x
    exact LinearMap.congr_fun
      (ModuleCat.hom_ext_iff.mp (section_koszul_differential_sq (φ := φ) n U)) x
  simpa [sheafKoszulDifferential, Functor.map_comp] using
    congrArg modSheafification.map hpresheaf

/-- Definition 17.24.1: the Koszul complex attached to `φ : ℰ ⟶ \mathcal O_X` is the chain
complex whose degree-`n` term is `Λ^[n] ℰ` and whose differentials are the sheafified sectionwise
Koszul contractions. -/
@[stacks 062K]
noncomputable def koszulComplex
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) :
    ChainComplex ModX ℕ :=
  ChainComplex.of (fun n ↦ Λ^[n] ℰ)
    (sheafKoszulDifferential φ)
    (sheafKoszulDifferential_sq φ)

/-- The degree `n` object of the sheaf Koszul complex is `Λ^[n] \mathcal E`. -/
theorem koszulComplex_X
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) :
    (koszulComplex φ).X n = (Λ^[n] ℰ) :=
  rfl

end AlgebraicGeometry.RingedSpace
