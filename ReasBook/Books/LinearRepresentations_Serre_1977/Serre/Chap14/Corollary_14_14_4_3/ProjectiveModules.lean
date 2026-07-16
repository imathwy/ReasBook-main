import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Lemma_14_14_4_2

noncomputable section

open Module
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra Representation TensorProduct

universe u v w

namespace Representation

section ProjectiveGrothendieckGroup

/- 
Domain-style sampling:
* Primary domain: Grothendieck groups of finitely generated projective modules over the group
  algebra `A[G]`, together with the canonical bridge to `Rep A G` and `FDRep A G`.
* Relevant owner declarations inspected in this domain:
  `FGModuleCat`,
  `Rep.ofModuleMonoidAlgebra`,
  `Module.Finite.trans`,
  and `FGModuleCat.isoToLinearEquiv`.
* Best owner abstraction: the canonical finite-generation owner `FGModuleCat A[G]`, with
  projectivity over `A[G]` as the additional source-facing condition.
* Source/core/bridge triage:
  source-facing: `FiniteProjectiveGroupAlgebraModule A G`, Serre's category of finitely generated
    projective `A[G]`-modules;
  core/canonical: `FGModuleCat A[G]`;
  bridge/view: the forgetful view to `ModuleCat A[G]` and, when `[Finite G]`, the restriction of
    scalars to `Rep A G` and `FDRep A G`.
* Primitive data: finite generation over `A[G]` from `FGModuleCat A[G]` and projectivity over
  `A[G]`.
* Derived API: finiteness over `A` when `[Finite G]`, the bridges `toRep` and `toFiniteRep`, and
  the class-equality classification theorems.
  Chapter `14`'s `finiteRepGrothendieckGroup`, and the source-facing owners
  `FiniteProjectiveGroupAlgebraModule A G`,
  `finiteProjectiveGroupAlgebraGrothendieckGroup`, and
  `finiteProjectiveGroupAlgebraGrothendieckClass`.
Thin wrappers around canonical functorial `mapIso` / `toLinearEquiv` constructions are not kept as
separate public owners here.
-/

/-- A finitely generated projective `A[G]`-module, built on the canonical owner `FGModuleCat A[G]`.
-/
abbrev FiniteProjectiveGroupAlgebraModule
    (A : Type u) [CommRing A] (G : Type v) [Group G] :=
  ObjectProperty.FullSubcategory
    (fun M : FGModuleCat.{max u v} A[G] ↦ Module.Projective A[G] M)

instance finiteProjectiveGroupAlgebraModule_containsZero
    (A : Type u) [CommRing A] (G : Type v) [Group G] :
    ObjectProperty.ContainsZero
      (fun M : FGModuleCat.{max u v} A[G] ↦ Module.Projective A[G] M) where
  exists_zero := by
    let Z0 : ModuleCat.{max u v} A[G] := ModuleCat.of A[G] (ULift.{max u v, 0} PUnit)
    have hfg : ModuleCat.isFG (R := A[G]) Z0 := by
      change Module.Finite A[G] (ULift.{max u v, 0} PUnit)
      infer_instance
    let Z : FGModuleCat.{max u v} A[G] := ⟨Z0, hfg⟩
    have hZ0 : IsZero Z0 := by
      exact (ModuleCat.isZero_of_iff_subsingleton
        (R := A[G]) (M := ULift.{max u v, 0} PUnit)).2 inferInstance
    have hZ : IsZero Z := by
      exact IsZero.of_full_of_faithful_of_isZero (ModuleCat.isFG A[G]).ι ⟨Z0, hfg⟩ hZ0
    have hP : Module.Projective A[G] Z := by infer_instance
    exact ⟨Z, hZ, hP⟩

namespace FiniteProjectiveGroupAlgebraModule

variable {A : Type u} [CommRing A] {G : Type v} [Group G]

/-- The underlying `A[G]`-module of a finitely generated projective object. -/
abbrev V (P : FiniteProjectiveGroupAlgebraModule A G) : ModuleCat A[G] :=
  P.obj.obj

instance (P : FiniteProjectiveGroupAlgebraModule A G) : Module A P.V :=
  Module.compHom P.V (algebraMap A A[G])

instance (P : FiniteProjectiveGroupAlgebraModule A G) : IsScalarTower A A[G] P.V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

instance (P : FiniteProjectiveGroupAlgebraModule A G) : Module.Finite A[G] P.V := by
  change Module.Finite A[G] P.obj
  infer_instance

/-- Over a finite group, a finitely generated projective `A[G]`-module is finite over `A`. -/
theorem finite [Finite G] (P : FiniteProjectiveGroupAlgebraModule A G) :
    Module.Finite A P.V :=
  let _ : Module.Finite A A[G] := MonoidAlgebra.moduleFinite
  Module.Finite.trans A[G] P.V

/-- Projectivity over the group algebra `A[G]`. -/
theorem projective (P : FiniteProjectiveGroupAlgebraModule A G) :
    Module.Projective A[G] P.V :=
  P.property

instance [Finite G] (P : FiniteProjectiveGroupAlgebraModule A G) : Module.Finite A P.V :=
  P.finite

instance (P : FiniteProjectiveGroupAlgebraModule A G) : Module.Projective A[G] P.V :=
  P.projective

/-- The canonical representation attached to a finite projective `A[G]`-module. -/
abbrev toRep (P : FiniteProjectiveGroupAlgebraModule A G) : Rep A G :=
  Rep.ofModuleMonoidAlgebra.obj P.V

/-- Over a finite group, the underlying representation of a finitely generated projective
`A[G]`-module is finite over `A`. -/
instance [Finite G] (P : FiniteProjectiveGroupAlgebraModule A G) : Module.Finite A P.toRep := by
  simpa [FiniteProjectiveGroupAlgebraModule.toRep] using (P.finite : Module.Finite A P.V)

/-- Forgetting projectivity turns a finite projective `k[G]`-module into the corresponding
finite-dimensional representation. -/
abbrev toFiniteRep
    {k : Type u} [Field k] {G : Type u} [Group G] [Finite G]
    (P : FiniteProjectiveGroupAlgebraModule k G) : FDRep k G :=
  let _ : Module.Finite k P.toRep := by infer_instance
  FDRep.of P.toRep.ρ

section ResidueFieldReduction

variable [IsLocalRing A] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Corollary 14-14.4-3: over a local coefficient ring, a finite projective
`A[G]`-module is free as an `A`-module. -/
theorem free (P : FiniteProjectiveGroupAlgebraModule A G) : Module.Free A P.V := by
  classical
  -- Restrict a projective splitting along `A → A[G]`, then use finite-flat over a local ring.
  obtain ⟨M, _instAddCommGroup, _instModuleAG, _instFree, i, s, hs⟩ :=
    Projective.iff_split.mp P.projective
  let _ : Module A M := Module.compHom M (algebraMap A A[G])
  let _ : IsScalarTower A A[G] M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Free A M :=
    Module.Free.of_basis
      ((MonoidAlgebra.basis G A).smulTower (Module.Free.chooseBasis (A[G]) M))
  let _ : Module.Projective A P.V := by
    refine Module.Projective.of_split (i.restrictScalars A) (s.restrictScalars A) ?_
    ext x
    exact LinearMap.congr_fun hs x
  let _ : Module.Flat A P.V := by infer_instance
  exact Module.free_of_flat_of_isLocalRing

/-- Helper for Corollary 14-14.4-3: the canonical residue-field reduction of a finite projective
`A[G]`-module. -/
def residueFieldReduction (P : FiniteProjectiveGroupAlgebraModule A G) :
    FiniteProjectiveGroupAlgebraModule k G :=
  let _ : Module.Finite A P.V := P.finite
  let _ : Module.Free A P.V := P.free
  let Wk : ModuleCat k[G] := ModuleCat.of k[G] (k ⊗[A] P.V)
  let _ : Module.Finite k Wk := by
    let b := Module.Free.chooseBasis A P.V
    letI : Finite (Module.Free.ChooseBasisIndex A P.V) := Module.Finite.finite_basis b
    letI : Module k (k ⊗[A] P.V) := TensorProduct.leftModule
    have hfinite : Module.Finite k (k ⊗[A] P.V) :=
      Module.Finite.of_basis (Algebra.TensorProduct.basis k b)
    simpa [Wk] using hfinite
  let _ : Module.Finite k[G] Wk := Module.Finite.of_restrictScalars_finite k k[G] Wk
  let W : FGModuleCat k[G] := by
    refine ⟨Wk, ?_⟩
    change Module.Finite k[G] Wk
    infer_instance
  let hW : Module.Projective k[G] W := by
    -- Reduction preserves projectivity for finite free modules by Lemma `14-14.4-2`.
    simpa using
      (projective_monoidAlgebra_iff_projective_residueFieldReduction).1 P.projective
  ⟨W, hW⟩

end ResidueFieldReduction

end FiniteProjectiveGroupAlgebraModule

end ProjectiveGrothendieckGroup

end Representation
