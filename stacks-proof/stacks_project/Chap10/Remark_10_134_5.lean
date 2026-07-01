import Mathlib
import stacks_project.Chap10.Definition_10_134_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Algebra
open Algebra.Generators
open Algebra.Extension
open CategoryTheory
open CategoryTheory.Limits
open ULift
open scoped NaiveCotangent

noncomputable section

section

variable (A : Type u) (B : Type u) (C : Type u)
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

private noncomputable def restrictOfIso
    {B : Type u} {C : Type u} [CommRing B] [CommRing C] [Algebra B C]
    (M : Type u) [AddCommGroup M] [Module C M] [Module B M] [IsScalarTower B C M] :
    (ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C M) ≅ ModuleCat.of B M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C M)) ≃ₗ[B] M from
      { __ := AddEquiv.refl _
        map_smul' _ _ := by simp }).toModuleIso

local notation:max "NL_{" S "⁄" R "}↾[" T "]" =>
  Algebra.Extension.naiveCotangentChainComplexRestrictScalars
    (Generators.toExtension (Generators.self R S)) T

/- Domain triage:
* primary domain: naive cotangent complexes and chain homotopies for composable maps of
  commutative rings;
* sampled owner declarations:
  - `Algebra.naiveCotangent`,
  - `Generators.self`,
  - `Algebra.Extension.naiveCotangentChainComplex`,
  - `Algebra.Extension.naiveCotangentChainComplexRestrictScalars`,
  - `Algebra.Extension.self`,
  - `Extension.CotangentSpace.map_comp_cotangentComplex`,
  - `Extension.Cotangent.map_sub_map` and `Extension.CotangentSpace.map_sub_map`,
  - `Homotopy.nullHomotopy'`;
* best owner abstraction: the public source-facing item is the canonical comparison
  `NL_{B/A} → NL_{C/A} → NL_{C/B}` on the owner complexes `NL_{B⁄A}` and `NL_{C⁄B}↾[B]`;
  the self-presentation extensions are primitive implementation data, while the comparison morphism
  and its explicit homotopy are derived API. -/

private noncomputable def naiveCotangentComparisonHom :
    (Generators.self A B).toExtension.Hom (Generators.self B C).toExtension :=
  (Generators.defaultHom
    (Generators.self A B : Generators A B B)
    (Generators.self B C : Generators B C C)).toExtensionHom

private noncomputable def naiveCotangentConstantHom :
    (Generators.self A B).toExtension.Hom (Generators.self B C).toExtension :=
  ((Generators.ofComp
      (Generators.self B C : Generators B C C)
      (Generators.self A B : Generators A B B)).comp
    (Generators.toComp
      (Generators.self B C : Generators B C C)
      (Generators.self A B : Generators A B B))).toExtensionHom

private noncomputable def naiveCotangentComparisonHomotopyLinear :
    ((Generators.self A B).toExtension).CotangentSpace →ₗ[B]
      ULift.{u, u} ((Generators.self B C).toExtension).Cotangent := by
  exact moduleEquiv.symm.toLinearMap ∘ₗ
    ((naiveCotangentComparisonHom A B C).sub (naiveCotangentConstantHom A B C))

/-- The canonical comparison
`NL_{B/A} → NL_{C/A} → NL_{C/B}`, viewed as a morphism of naive cotangent complexes over `B`. -/
noncomputable def naiveCotangentComparison_comp :
    NL_{B⁄A} ⟶ NL_{C⁄B}↾[B] := by
  let f₀ :
      (NL_{B⁄A}).X 0 ⟶ (NL_{C⁄B}↾[B]).X 0 :=
    ModuleCat.ofHom (CotangentSpace.map (naiveCotangentComparisonHom A B C)) ≫
      (restrictOfIso ((Generators.self B C).toExtension).CotangentSpace).inv
  let f₁ :
      (NL_{B⁄A}).X 1 ⟶ (NL_{C⁄B}↾[B]).X 1 :=
    ModuleCat.ofHom
        (moduleEquiv.symm.toLinearMap ∘ₗ
          Cotangent.map (naiveCotangentComparisonHom A B C) ∘ₗ
            moduleEquiv.toLinearMap) ≫
      (restrictOfIso (ULift.{u, u} ((Generators.self B C).toExtension).Cotangent)).inv
  refine ChainComplex.mkHom _ _ f₀ f₁ ?_ ?_
  · ext x
    rcases x with ⟨x⟩
    simp [f₀, f₁, Algebra.Extension.naiveCotangentChainComplexRestrictScalars,
      Algebra.Extension.naiveCotangentChainComplex, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
      LinearMap.comp_assoc]
    simpa [LinearMap.comp_assoc] using
      LinearMap.congr_fun (Extension.CotangentSpace.map_comp_cotangentComplex
        (naiveCotangentComparisonHom A B C)).symm x
  · sorry

/-- The explicit degree-`1` homotopy map for Remark 10.134.5. It is zero away from bidegree
`(1,0)`, where it sends `d[X_b]` to the class of `X_{\phi(b)} - b` in the conormal module of
`B[C] → C`. -/
noncomputable def naiveCotangentComparison_comp_homotopyMap
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    (NL_{B⁄A}).X i ⟶ (NL_{C⁄B}↾[B]).X j := by
  rcases i with _ | i
  · rcases j with _ | j
    · exact 0
    · cases j with
      | zero =>
          exact ModuleCat.ofHom (naiveCotangentComparisonHomotopyLinear A B C) ≫
            (restrictOfIso (ULift.{u, u} ((Generators.self B C).toExtension).Cotangent)).inv
      | succ j =>
          exact 0
  · exact 0

private noncomputable def naiveCotangentComparison_comp_nullHomotopicMap :
    NL_{B⁄A} ⟶ NL_{C⁄B}↾[B] :=
  Homotopy.nullHomotopicMap' (naiveCotangentComparison_comp_homotopyMap A B C)

private theorem naiveCotangentComparison_comp_eq_nullHomotopicMap :
    naiveCotangentComparison_comp A B C =
      naiveCotangentComparison_comp_nullHomotopicMap A B C := by
  sorry

/-- Remark 10.134.5: for ring maps `A → B → C`, the comparison
`NL_{B/A} → NL_{C/A} → NL_{C/B}` coming from the canonical self-presentations is chain-homotopic
to zero. The explicit homotopy sends `d[X_b]` to the class of `X_{\phi(b)} - b` in
`ker(B[C] → C) / ker(B[C] → C)^2`. -/
noncomputable def naiveCotangentComparison_comp_homotopy :
    Homotopy (naiveCotangentComparison_comp A B C) 0 := by
  let h :
      Homotopy (naiveCotangentComparison_comp_nullHomotopicMap A B C) 0 :=
    Homotopy.nullHomotopy' fun i j hij ↦
      naiveCotangentComparison_comp_homotopyMap A B C i j hij
  exact (naiveCotangentComparison_comp_eq_nullHomotopicMap A B C) ▸ h

end
