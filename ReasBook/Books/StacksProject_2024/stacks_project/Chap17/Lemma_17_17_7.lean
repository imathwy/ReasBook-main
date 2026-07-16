import Mathlib
import StacksProject_2024.stacks_project.Chap06.Lemma_6_31_8
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_4
import StacksProject_2024.stacks_project.Chap17.Lemma_17_14_5.FreeSections
import StacksProject_2024.stacks_project.Chap17.Lemma_17_3_1
import StacksProject_2024.stacks_project.Chap17.Lemma_17_17_2
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open TopologicalSpace
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

variable {X : RingedSpace.{u}}

/-
Domain-style sampling for Lemma 17.17.7:
- primary domain: epimorphic generators of `X.Modules` by the lower-shriek structure modules
  `j_{U!}\mathcal O_U`, together with the resulting `ObjectProperty` package used in the Chapter 13
  truncation-resolution formalism;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero`,
  `CategoryTheory.ObjectProperty.HasEpiCover`,
  `CategoryTheory.exists_upperTruncationResolutionTower`;
- best owner abstraction: the ambient owner is the canonical module category `X.Modules`; the
  source-facing summands are the canonical lower-shriek modules `j![X.sheaf, U]`, and the
  closure/cover statements should be expressed directly as an `ObjectProperty` on `X.Modules`
  rather than via a parallel wrapper category or a local owner alias;
- primitive data: an index type `I`, a family of opens `U : I → Opens X.carrier`, and an
  epimorphism from the coproduct of the corresponding modules `j_{U_i!}\mathcal O_{U_i}`;
- derived API: the object property of being such a coproduct, its `ContainsZero` /
  `IsClosedUnderFiniteCoproducts` / `HasEpiCover` instances, and the flat quotient corollary.

Source/core/bridge triage:
- `source-facing`: the coproduct and flat epimorphic presentations of an `\mathcal O_X`-module;
- `core/canonical`: `X.Modules`, `j![X.sheaf, U]`, and the generic
  `CategoryTheory.ObjectProperty` closure classes;
- `bridge/view`: the ringed-space flatness specialization from `Lemma_17_17_6`.
-/

local notation "ModX" => X.Modules

/-- Helper for Lemma 17.17.7: the lower-shriek of the structure sheaf from an open subset `U`
back to `X`. -/
private abbrev openSubsetStructureSheafLowerShriek
    (U : Opens X.carrier) : ModX :=
  (openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).obj
    (SheafOfModules.unit
      ((TopCat.Sheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj
        (RingedSpace.ringCatSheaf X)))

/-- Helper for Lemma 17.17.7: morphisms from `j_{U!}\mathcal O_U` to `ℱ` correspond to sections
of `ℱ` over `U`. -/
private noncomputable def openSubsetStructureSheafLowerShriek_homEquiv
    (U : Opens X.carrier) (ℱ : ModX) :
    (openSubsetStructureSheafLowerShriek (X := X) U ⟶ ℱ) ≃ ℱ.val.obj (op U) :=
  -- TODO: bridge the explicit open-subspace extension-by-zero owner to the slice owner
  -- `SheafOfModules.over ℱ U`, then compose the adjunction Hom-equivalence with terminal
  -- evaluation on the slice.
  sorry

/-- Helper for Lemma 17.17.7: the lower-shriek Hom/sections equivalence is natural in the target
module. -/
private theorem openSubsetStructureSheafLowerShriek_homEquiv_naturality_right
    (U : Opens X.carrier) {ℱ 𝒢 : ModX}
    (β : openSubsetStructureSheafLowerShriek (X := X) U ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    openSubsetStructureSheafLowerShriek_homEquiv (X := X) U 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).map α)
        (openSubsetStructureSheafLowerShriek_homEquiv (X := X) U ℱ β) :=
  -- TODO: once the owner bridge in `openSubsetStructureSheafLowerShriek_homEquiv` is explicit,
  -- this should be a short target-functoriality calculation for the composed equivalence.
  sorry

/-- Helper for Lemma 17.17.7: the coproduct over a disjoint union of index types identifies with
the binary coproduct of the two corresponding coproducts. -/
private noncomputable def openSubsetStructureSheafLowerShriek_sumIndexCoprodIso
    {I₁ I₂ : Type u} (U₁ : I₁ → Opens X.carrier) (U₂ : I₂ → Opens X.carrier) :
    ((∐ fun i : I₁ ↦ openSubsetStructureSheafLowerShriek (X := X) (U₁ i)) ⨿
      (∐ fun j : I₂ ↦ openSubsetStructureSheafLowerShriek (X := X) (U₂ j))) ≅
      ∐ fun k : I₁ ⊕ I₂ ↦ openSubsetStructureSheafLowerShriek (X := X) (Sum.elim U₁ U₂ k) :=
  -- TODO: build the forward and inverse maps by `coprod.desc` and `Sigma.desc`, then prove they
  -- are inverse by `coprod.hom_ext` and `Limits.Sigma.hom_ext`.
  sorry

-- Proof sketch: for every open `U ⊆ X` and section `s ∈ ℱ(U)`, the adjunction between
-- restriction to `U` and extension by zero gives a morphism `j_{U!}\mathcal O_U ⟶ ℱ` sending `1`
-- to `s`. Taking the coproduct over all pairs `(U, s)` yields a morphism whose stalk maps are
-- surjective, hence the morphism is epimorphic.
/-- Lemma 17.17.7 (1): any sheaf of `\mathcal O_X`-modules is the quotient of a direct sum of
lower-shriek structure sheaves `j_{U_i!}\mathcal O_{U_i}`. -/
theorem exists_epi_from_coproduct_openSubsetStructureSheafLowerShriek
    (ℱ : ModX) :
    ∃ (I : Type u) (U : I → Opens X.carrier)
      (φ : (∐ fun i : I ↦ openSubsetStructureSheafLowerShriek (X := X) (U i)) ⟶ ℱ), Epi φ :=
  -- TODO: define `φ` as the coproduct map determined by the chosen local sections via
  -- `openSubsetStructureSheafLowerShriek_homEquiv`, then prove `Epi φ` by comparing two
  -- postcompositions on each tested section.
  sorry

/-- The object property on `\mathrm{Mod}(\mathcal O_X)` saying that a module is a direct sum,
equivalently a categorical coproduct, of lower-shriek structure sheaves `j_{U!}\mathcal O_U`. -/
def isCoproductOfOpenSubsetStructureSheafLowerShrieks
    (X : RingedSpace.{u}) : CategoryTheory.ObjectProperty X.Modules :=
  fun ℱ ↦
    ∃ (I : Type u) (U : I → Opens X.carrier),
      Nonempty (ℱ ≅ ∐ fun i : I ↦ openSubsetStructureSheafLowerShriek (X := X) (U i))

/-- Helper for Lemma 17.17.7: being a coproduct of lower-shriek structure sheaves is stable under
ambient isomorphisms. -/
private instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_isClosedUnderIsomorphisms :
    (isCoproductOfOpenSubsetStructureSheafLowerShrieks X).IsClosedUnderIsomorphisms where
  of_iso e hℱ := by
    -- Proof comment: transport the chosen coproduct presentation across the ambient isomorphism.
    rcases hℱ with ⟨I, U, ⟨hU⟩⟩
    exact ⟨I, U, ⟨e.symm ≪≫ hU⟩⟩

/-- The zero `\mathcal O_X`-module is the empty coproduct of lower-shriek structure sheaves. -/
instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_containsZero :
    (isCoproductOfOpenSubsetStructureSheafLowerShrieks X).ContainsZero where
  exists_zero := by
    let F : Discrete PEmpty ⥤ ModX :=
      Discrete.functor (fun i : PEmpty ↦ openSubsetStructureSheafLowerShriek (X := X) (PEmpty.elim i))
    -- Proof comment: the empty coproduct is initial, hence zero in the abelian module category.
    refine ⟨colimit F, ?_, ?_⟩
    · refine (IsInitial.ofIso initialIsInitial ?_).isZero
      let e :
          F ≅ (Functor.const (Discrete PEmpty)).obj (⊥_ ModX) :=
        NatIso.ofComponents (fun i ↦ PEmpty.elim i.as)
      exact CategoryTheory.Limits.colimitConstInitial.symm ≪≫
        (HasColimit.isoOfNatIso e).symm
    · -- Proof comment: use the empty indexing type itself as the coproduct witness.
      refine ⟨PEmpty, PEmpty.elim, ?_⟩
      simpa [F] using (show Nonempty (colimit F ≅ colimit F) from ⟨Iso.refl _⟩)

/-- Helper for Lemma 17.17.7: the coproduct of two coproducts of lower-shriek structure sheaves
is again a coproduct of lower-shriek structure sheaves, indexed by the disjoint union of the two
index sets. -/
private lemma openSubsetStructureSheafLowerShriek_binaryCoproduct_mem
    {I₁ I₂ : Type u} (U₁ : I₁ → Opens X.carrier) (U₂ : I₂ → Opens X.carrier) :
    isCoproductOfOpenSubsetStructureSheafLowerShrieks X
      ((∐ fun i : I₁ ↦ openSubsetStructureSheafLowerShriek (X := X) (U₁ i)) ⨿
        (∐ fun j : I₂ ↦ openSubsetStructureSheafLowerShriek (X := X) (U₂ j))) := by
  -- Proof comment: the coproduct of two coproducts is the coproduct over the disjoint union of
  -- the two index types.
  refine ⟨I₁ ⊕ I₂, Sum.elim U₁ U₂, ?_⟩
  exact ⟨openSubsetStructureSheafLowerShriek_sumIndexCoprodIso (X := X) U₁ U₂⟩

/-- Helper for Lemma 17.17.7: binary coproducts of coproducts of lower-shriek structure sheaves
are again coproducts of lower-shriek structure sheaves. -/
private instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_isClosedUnderBinaryCoproducts :
    (isCoproductOfOpenSubsetStructureSheafLowerShrieks X).IsClosedUnderBinaryCoproducts := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro Z ⟨F, hF⟩
  let A := F.obj ⟨WalkingPair.left⟩
  let B := F.obj ⟨WalkingPair.right⟩
  rcases hF ⟨WalkingPair.left⟩ with ⟨I₁, U₁, ⟨e₁⟩⟩
  rcases hF ⟨WalkingPair.right⟩ with ⟨I₂, U₂, ⟨e₂⟩⟩
  have hExplicit :
      isCoproductOfOpenSubsetStructureSheafLowerShrieks X
        ((∐ fun i : I₁ ↦ openSubsetStructureSheafLowerShriek (X := X) (U₁ i)) ⨿
          (∐ fun j : I₂ ↦ openSubsetStructureSheafLowerShriek (X := X) (U₂ j))) :=
    openSubsetStructureSheafLowerShriek_binaryCoproduct_mem (X := X) U₁ U₂
  let f :
      ((∐ fun i : I₁ ↦ openSubsetStructureSheafLowerShriek (X := X) (U₁ i)) ⨿
        (∐ fun j : I₂ ↦ openSubsetStructureSheafLowerShriek (X := X) (U₂ j))) ⟶
        (A ⨿ B) :=
    coprod.map e₁.inv e₂.inv
  haveI : IsIso f := by
    infer_instance
  have hPairColimit :
      isCoproductOfOpenSubsetStructureSheafLowerShrieks X (A ⨿ B) := by
    exact (isCoproductOfOpenSubsetStructureSheafLowerShrieks X).prop_of_iso (asIso f) hExplicit
  -- Route correction: first reduce to the canonical binary coproduct of the two chosen
  -- presentations, then transport back along the standard `diagramIsoPair` comparison.
  exact (isCoproductOfOpenSubsetStructureSheafLowerShrieks X).prop_of_iso
    (HasColimit.isoOfNatIso (diagramIsoPair F)).symm hPairColimit

/-- Finite coproducts of coproducts of lower-shriek structure sheaves are again coproducts of
lower-shriek structure sheaves. -/
instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_isClosedUnderFiniteCoproducts :
    (isCoproductOfOpenSubsetStructureSheafLowerShrieks X).IsClosedUnderFiniteCoproducts := by
  -- Proof comment: zero objects and binary coproducts already generate all finite coproducts.
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- Every `\mathcal O_X`-module admits an epimorphism from a coproduct of lower-shriek structure
sheaves `j_{U!}\mathcal O_U`. -/
instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_hasEpiCover :
    CategoryTheory.ObjectProperty.HasEpiCover
      (isCoproductOfOpenSubsetStructureSheafLowerShrieks X) where
  exists_epi ℱ := by
    rcases exists_epi_from_coproduct_openSubsetStructureSheafLowerShriek (X := X) ℱ with
      ⟨I, U, φ, hφ⟩
    refine ⟨∐ fun i : I ↦ openSubsetStructureSheafLowerShriek (X := X) (U i), ?_, φ, hφ⟩
    -- Proof comment: the source already comes equipped with the required coproduct presentation.
    exact ⟨I, U, ⟨Iso.refl _⟩⟩

-- Proof sketch: apply the epimorphic coproduct presentation from `(1)` and use that each summand
-- `j_{U_i!}\mathcal O_{U_i}` is flat by the local stalk computation above. Then pass to stalks of
-- the coproduct source and identify them with direct sums of flat modules.
/-- Lemma 17.17.7 (2): any sheaf of `\mathcal O_X`-modules is the quotient of a flat
`\mathcal O_X`-module. -/
theorem exists_epi_from_flat
    (ℱ : ModX) :
    ∃ (𝒢 : ModX)
      (h𝒢 : 𝒢.IsFlat) (φ : 𝒢 ⟶ ℱ), Epi φ := by
  -- TODO: combine the direct epimorphism from part `(1)` with local flatness proofs for each
  -- summand `j_{U!}\mathcal O_U` and a dependency-closed coproduct-flatness argument.
  sorry

end AlgebraicGeometry.RingedSpace.ModuleSheaf
