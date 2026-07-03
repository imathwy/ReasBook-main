import Mathlib
import stacks_project.Chap17.Lemma_17_21_1
import stacks_project.Chap17.Lemma_17_21_3
import stacks_project.Chap15.Definition_15_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry TensorProduct
open CategoryTheory
open Opposite
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "OX" => RingedSpace.ringCatSheaf X
local notation "ModX" => SheafOfModules OX
local notation "𝒪X" => SheafOfModules.unit OX

/- Domain-style sampling for Definition 17.24.1:
- primary domain: sheaf Koszul complexes attached to a morphism `φ : \mathcal E \to \mathcal O_X`;
- inspected owner declarations:
  `moduleExteriorAlgebra` and `exteriorAlgebraPresheaf` from Chapter 17,
  `exteriorPowerSheaf` from Chapter 17,
  `_root_.koszulComplex` from Definition 15.28.1,
  and `_root_.koszulDifferentialLinearMap` from Definition 15.28.1;
- best owner abstraction: the source-facing object is the Koszul complex of `φ`, whose degree-`n`
  term is `Λ^[n] ℰ`; the sectionwise contraction derivation on `Λ(ℰ)` and its homogeneous-piece
  maps are auxiliary bridge data sheafified from the canonical linear-model operators;
- primitive data: a morphism `φ : ℰ ⟶ \mathcal O_X`;
- derived API: the sectionwise contraction derivation, the induced homogeneous-piece
  differentials, and the resulting complex.

Source/core/bridge triage:
- `source-facing`: `koszulComplex`;
- `core/canonical`: `Λ(ℰ)`, `Λ^[n] ℰ`, `exteriorAlgebraPresheaf`, `exteriorPowerSheaf`,
  `_root_.koszulComplex`, and `_root_.koszulDifferentialLinearMap`;
- `bridge/view`: `koszulDerivation`, `koszulDifferential`, and their sectionwise implementation
  data. -/

/-- The commutative ring of sections of the structure sheaf over an open set. -/
private abbrev sectionRing (X : RingedSpace) (U : (Opens X)ᵒᵖ) :=
  X.presheaf.obj U

/-- On sections over an open `U`, the Koszul differential is the contraction derivation extending
`φ(U)` on the exterior algebra `\bigwedge_{\mathcal O_X(U)} \mathcal E(U)`. -/
noncomputable def koszulDerivationSection
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (U : (Opens X)ᵒᵖ) :
    (exteriorAlgebraPresheaf ℰ).obj U ⟶ (exteriorAlgebraPresheaf ℰ).obj U :=
  let R := sectionRing X U
  letI : CommRing R := by infer_instance
  letI : Module R (ℰ.val.obj U) := by infer_instance
  let fU : ℰ.val.obj U →ₗ[R] R := (φ.val.app U).hom
  ModuleCat.ofHom (CliffordAlgebra.contractLeft fU)

/-- On generators, the sectionwise Koszul derivation recovers the local linear form `φ(U)`. -/
theorem koszulDerivationSection_ι
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (U : (Opens X)ᵒᵖ) (m : ℰ.val.obj U) :
    (koszulDerivationSection φ U).hom (ExteriorAlgebra.ι (sectionRing X U) m) =
      (algebraMap (sectionRing X U) (ExteriorAlgebra (sectionRing X U) (ℰ.val.obj U))
        ((φ.val.app U).hom m) :
        ExteriorAlgebra (sectionRing X U) (ℰ.val.obj U)) := by
  let R := sectionRing X U
  letI : CommRing R := by infer_instance
  letI : Module R (ℰ.val.obj U) := by infer_instance
  let fU : ℰ.val.obj U →ₗ[R] R := (φ.val.app U).hom
  change CliffordAlgebra.contractLeft fU (ExteriorAlgebra.ι R m) =
    algebraMap R (ExteriorAlgebra R (ℰ.val.obj U)) (fU m)
  exact CliffordAlgebra.contractLeft_ι (0 : QuadraticForm R (ℰ.val.obj U)) fU m

/-- On sections, the Koszul derivation satisfies the contraction Leibniz rule against generators. -/
theorem koszulDerivationSection_ι_mul
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (U : (Opens X)ᵒᵖ) (m : ℰ.val.obj U)
    (x : ExteriorAlgebra (sectionRing X U) (ℰ.val.obj U)) :
    let δ : ExteriorAlgebra (sectionRing X U) (ℰ.val.obj U) →
        ExteriorAlgebra (sectionRing X U) (ℰ.val.obj U) := (koszulDerivationSection φ U).hom
    δ (ExteriorAlgebra.ι (sectionRing X U) m * x) =
      (algebraMap (sectionRing X U) (ExteriorAlgebra (sectionRing X U) (ℰ.val.obj U))
        ((φ.val.app U).hom m) :
        ExteriorAlgebra (sectionRing X U) (ℰ.val.obj U)) * x -
        ExteriorAlgebra.ι (sectionRing X U) m * δ x := by
  let R := sectionRing X U
  letI : CommRing R := by infer_instance
  letI : Module R (ℰ.val.obj U) := by infer_instance
  let fU : ℰ.val.obj U →ₗ[R] R := (φ.val.app U).hom
  dsimp
  change CliffordAlgebra.contractLeft fU (ExteriorAlgebra.ι R m * x) =
    algebraMap R (ExteriorAlgebra R (ℰ.val.obj U)) (fU m) * x -
      ExteriorAlgebra.ι R m * CliffordAlgebra.contractLeft fU x
  simpa [koszulDerivationSection] using
    (CliffordAlgebra.contractLeft_ι_mul fU m x)

/-- The sectionwise Koszul derivations are compatible with restriction maps. -/
private theorem koszulDerivationPresheaf_naturality
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (exteriorAlgebraPresheaf ℰ).map i ≫
        (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
          (koszulDerivationSection φ V) =
      koszulDerivationSection φ U ≫ (exteriorAlgebraPresheaf ℰ).map i := sorry

-- The implementation presheaf endomorphism whose sheafification is the Koszul differential on
-- `Λ(ℰ)`.
private noncomputable def koszulDerivationPresheaf
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) :
    exteriorAlgebraPresheaf ℰ ⟶ exteriorAlgebraPresheaf ℰ :=
  { app := koszulDerivationSection φ
    naturality := koszulDerivationPresheaf_naturality φ }

/-- Auxiliary bridge data: the Koszul contraction derivation on the exterior-algebra sheaf `Λ(ℰ)`
is obtained by sheafifying the sectionwise contraction derivation extending `φ`. -/
noncomputable def koszulDerivation
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) :
    Λ(ℰ) ⟶ Λ(ℰ) :=
  (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).map
    (koszulDerivationPresheaf φ)

/-- The degree `n + 1` homogeneous Koszul differential is the restriction of
`koszulDerivationSection φ U` to the `(n + 1)`st exterior-power summand. -/
noncomputable def koszulDifferentialSection
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    (exteriorPowerPresheaf ℰ (n + 1)).obj U ⟶ (exteriorPowerPresheaf ℰ n).obj U :=
  let R := sectionRing X U
  letI : CommRing R := by infer_instance
  letI : Module R (ℰ.val.obj U) := by infer_instance
  let fU : ℰ.val.obj U →ₗ[R] R := (φ.val.app U).hom
  ModuleCat.ofHom (koszulDifferentialLinearMap fU n)

/-- The sectionwise Koszul contractions are compatible with restriction maps. -/
private theorem koszulDifferentialPresheaf_naturality
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (exteriorPowerPresheaf ℰ (n + 1)).map i ≫
        (ModuleCat.restrictScalars (X.presheaf.map i).hom).map
          (koszulDifferentialSection φ n V) =
      koszulDifferentialSection φ n U ≫ (exteriorPowerPresheaf ℰ n).map i := sorry

-- The implementation presheaf morphism giving the degree `n + 1` Koszul differential.
private noncomputable def koszulDifferentialPresheaf
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) :
    exteriorPowerPresheaf ℰ (n + 1) ⟶ exteriorPowerPresheaf ℰ n :=
  { app := koszulDifferentialSection φ n
    naturality := koszulDifferentialPresheaf_naturality φ n }

/-- Auxiliary bridge data: the degree `n + 1` differential in the sheaf Koszul complex is the
homogeneous-piece restriction of the sectionwise contraction operators to `Λ^[n + 1] ℰ`. -/
noncomputable def koszulDifferential
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) :
    (Λ^[n + 1] ℰ) ⟶ (Λ^[n] ℰ) :=
  (PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).map
    (koszulDifferentialPresheaf φ n)

/-- Consecutive Koszul differentials on exterior-power sheaves compose to zero. -/
theorem koszulDifferential_sq
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) :
    koszulDifferential φ (n + 1) ≫ koszulDifferential φ n = 0 := sorry

/-- Definition 17.24.1: the Koszul complex attached to `φ : ℰ ⟶ \mathcal O_X` is the chain
complex whose degree-`n` term is `Λ^[n] ℰ` and whose differentials are the sheafified sectionwise
Koszul contractions. -/
noncomputable abbrev koszulComplex
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) :
    ChainComplex ModX ℕ :=
  ChainComplex.of (fun n ↦ Λ^[n] ℰ)
    (koszulDifferential φ)
    (koszulDifferential_sq φ)

/-- The degree `n` object of the sheaf Koszul complex is `Λ^[n] \mathcal E`. -/
theorem koszulComplex_X
    {ℰ : ModX} (φ : ℰ ⟶ 𝒪X) (n : ℕ) :
    (koszulComplex φ).X n = (Λ^[n] ℰ) :=
  rfl

end AlgebraicGeometry.RingedSpace
