import Mathlib
import stacks_project.Chap14.Lemma_14_25_1
import stacks_project.Chap14.Definition_14_26_1
import stacks_project.Chap14.Lemma_14_27_1
import stacks_project.Chap14.Lemma_14_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 14.28.6:
- primary domain: simplicial/cosimplicial homotopy and the Dold-Kan comparison functors
  `alternatingCofaceMapComplex` and `normalizedCochainComplexFunctor`;
- sampled same-kind declarations:
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopic`,
  `CategoryTheory.CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`,
  `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`,
  `AlgebraicTopology.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`,
  `CategoryTheory.CosimplicialObject.normalizedCochainComplexFunctor`;
- best owner abstraction: the source-facing relation in this file is
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopic`; the opposite simplicial zigzag relation
  is only the bridge from Lemma 14.28.3, and the normalized complex owner in this chapter is
  `normalizedCochainComplexFunctor`;
- primitive data: directed `Δ[1]`-indexed cosimplicial homotopies and the canonical Moore-complex
  inclusion and retraction on the opposite simplicial side;
- derived API: the resulting existence of chain/cochain homotopies on the alternating and
  normalized complexes after passage through the opposite/unop bridges.

Source/core/bridge triage:
- `source-facing`: the two Stacks statements about homotopic cosimplicial maps inducing homotopic
  maps on `s(U)` and `Q(U)`;
- `core/canonical`: `DeltaOneHomotopic`, `toChainHomotopy`, and the Chapter 14 owner
  `normalizedCochainComplexFunctor`;
- `bridge/view`: `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`, passage to opposite
  simplicial objects, and transport of chain homotopies through `HomologicalComplex.unopFunctor`.
  -/

section HomotopyTransport

variable [Preadditive A]
variable {K L : ChainComplex Aᵒᵖ ℕ} {f g : K ⟶ L}

/-- Transport a chain homotopy in `Aᵒᵖ` across `HomologicalComplex.unopFunctor` to the
corresponding cochain homotopy in `A`. This is the only local bridge theorem needed below. -/
private theorem unopFunctor_map_homotopy
    (h : _root_.Homotopy f g) :
    Nonempty
      (_root_.Homotopy
        ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map f.op)
        ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map g.op)) := by
  sorry

end HomotopyTransport

section AlternatingCofaceMapComplex

variable [Preadditive A]
variable {U V : CosimplicialObject A} {a b : U ⟶ V}

-- Proof sketch: transport the given `DeltaOneHomotopic` relation across
-- `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`, apply
-- `SimplicialObject.alternatingFaceMapComplex_map_homotopic`, and identify the resulting chain
-- homotopy in `Aᵒᵖ` with the desired cochain homotopy on `alternatingCofaceMapComplex`.
/-- Lemma 14.28.6 (1): if two morphisms of cosimplicial objects in an additive category are
`Δ[1]`-homotopic, then the induced morphisms on the alternating coface map complexes
`s(U) ⟶ s(V)` are homotopic as maps of cochain complexes. -/
theorem alternatingCofaceMapComplex_map_homotopic
    (h : DeltaOneHomotopic a b) :
    Nonempty
      (_root_.Homotopy
        ((alternatingCofaceMapComplex A).map a)
        ((alternatingCofaceMapComplex A).map b)) := by
  rcases SimplicialObject.alternatingFaceMapComplex_map_homotopic
      ((deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag a b).1 h) with
    ⟨h'⟩
  have hunop :
      Nonempty
        (_root_.Homotopy
          ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
            ((alternatingFaceMapComplex Aᵒᵖ).map (NatTrans.op a)).op)
          ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
            ((alternatingFaceMapComplex Aᵒᵖ).map (NatTrans.op b)).op)) :=
    unopFunctor_map_homotopy h'
  sorry

end AlternatingCofaceMapComplex

section NormalizedCochainComplex

variable [Abelian A]
local instance : CategoryTheory.Limits.HasZeroObject Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasBinaryCoproducts Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasImages Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasCokernels (CochainComplex A ℕ) := inferInstance

variable {U V : CosimplicialObject A} {a b : U ⟶ V}

-- Proof sketch: transport the given `DeltaOneHomotopic` relation across
-- `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`, apply
-- `SimplicialObject.normalizedMooreComplex_map_homotopic` in `Aᵒᵖ`, and transport the resulting
-- chain homotopy back to a cochain homotopy using `HomologicalComplex.unopFunctor`.
/-- Lemma 14.28.6 (2): if `A` is abelian and two morphisms of cosimplicial objects are homotopic,
then the induced morphisms on the normalized cochain complexes `Q(U) ⟶ Q(V)` are homotopic as
maps of cochain complexes. -/
theorem normalizedCochainComplex_map_homotopic
    (h : DeltaOneHomotopic a b) :
    Nonempty
      (_root_.Homotopy
        (normalizedCochainComplexFunctor.map a)
        (normalizedCochainComplexFunctor.map b)) := by
  rcases SimplicialObject.normalizedMooreComplex_map_homotopic
      ((deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag a b).1 h) with
    ⟨h'⟩
  have hunop :
      Nonempty
        (_root_.Homotopy
          ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
            ((normalizedMooreComplex Aᵒᵖ).map (NatTrans.op a)).op)
          ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
            ((normalizedMooreComplex Aᵒᵖ).map (NatTrans.op b)).op)) :=
    unopFunctor_map_homotopy h'
  sorry

end NormalizedCochainComplex

end CategoryTheory.CosimplicialObject
