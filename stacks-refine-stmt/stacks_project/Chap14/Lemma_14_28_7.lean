import Mathlib
import stacks_project.Chap14.Definition_14_26_6
import stacks_project.Chap14.Lemma_14_28_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open scoped DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 14.28.7:
- primary domain: cosimplicial homotopy equivalences and the induced homotopy-equivalence
  property on the canonical cochain-complex functors `s` and `Q`;
- sampled same-kind owner declarations:
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopic`,
  `CategoryTheory.CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`,
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.SimplicialObject.IsHomotopyEquivalence`,
  `HomologicalComplex.homotopyEquivalences`;
- best owner abstraction: the source-facing owner in this file should be the cosimplicial analogue
  of `SimplicialObject.HomotopyEquiv`, with primitive data given directly by a morphism, a chosen
  inverse, and two `DeltaOneHomotopic` witnesses; `NatTrans.op` is only the bridge/view to the
  already-canonical simplicial owner, while the target-side owner remains
  `HomologicalComplex.homotopyEquivalences`;
- primitive-vs-derived split:
  primitive data are the forward map, inverse map, and the two `DeltaOneHomotopic` witnesses on
  the cosimplicial side;
  derived API is the morphism property `IsHomotopyEquivalence`, its bridge to the opposite
  simplicial owner, and the induced cochain-level homotopy-equivalence property.

Source/core/bridge triage:
- `source-facing`: the two Stacks lemmas on cosimplicial homotopy equivalences;
- `core/canonical`: `CosimplicialObject.HomotopyEquiv`, `CosimplicialObject.IsHomotopyEquivalence`,
  `SimplicialObject.IsHomotopyEquivalence`, and
  `HomologicalComplex.homotopyEquivalences`;
- `bridge/view`: `NatTrans.op` between cosimplicial and simplicial morphisms. -/

/-- A homotopy equivalence between cosimplicial objects consists of a morphism, a chosen inverse,
and zigzag `Δ[1]`-homotopies from the two composites to the corresponding identities. -/
@[ext]
structure HomotopyEquiv (U V : CosimplicialObject A) where
  hom : U ⟶ V
  inv : V ⟶ U
  homotopyHomInvId : DeltaOneHomotopic (hom ≫ inv) (𝟙 U)
  homotopyInvHomId : DeltaOneHomotopic (inv ≫ hom) (𝟙 V)

variable (A) in
/-- The morphism property on cosimplicial objects given by cosimplicial homotopy equivalences. -/
def homotopyEquivalences : MorphismProperty (CosimplicialObject A) :=
  fun U V a ↦ ∃ e : HomotopyEquiv U V, e.hom = a

/-- A morphism of cosimplicial objects is a homotopy equivalence if it is the forward map of a
cosimplicial homotopy equivalence. -/
abbrev IsHomotopyEquivalence {U V : CosimplicialObject A} (a : U ⟶ V) : Prop :=
  homotopyEquivalences A a

namespace HomotopyEquiv

variable {U V : CosimplicialObject A}

/-- The forward morphism of a cosimplicial homotopy equivalence is a morphism-level homotopy
equivalence. -/
theorem isHomotopyEquivalence (e : HomotopyEquiv U V) :
    IsHomotopyEquivalence e.hom :=
  ⟨e, rfl⟩

end HomotopyEquiv

/-- A morphism of cosimplicial objects is a homotopy equivalence exactly when its opposite
simplicial morphism is one. -/
theorem isHomotopyEquivalence_iff_op
    {U V : CosimplicialObject A} (a : U ⟶ V) :
    IsHomotopyEquivalence a ↔
      SimplicialObject.IsHomotopyEquivalence (NatTrans.op a) := by
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨{
      hom := NatTrans.op e.hom
      inv := NatTrans.op e.inv
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_
    }, rfl⟩
    · simpa using
        (deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
          (e.inv ≫ e.hom) (𝟙 V)).1 e.homotopyInvHomId
    · simpa using
        (deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
          (e.hom ≫ e.inv) (𝟙 U)).1 e.homotopyHomInvId
  · rintro ⟨e, he⟩
    refine ⟨{
      hom := a
      inv := NatTrans.unop e.inv
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_
    }, rfl⟩
    · apply (deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
        (a ≫ NatTrans.unop e.inv) (𝟙 U)).2
      simpa [he] using e.homotopyInvHomId
    · apply (deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
        (NatTrans.unop e.inv ≫ a) (𝟙 V)).2
      simpa [he] using e.homotopyHomInvId

section AlternatingCofaceMapComplex

variable [Preadditive A]
variable {U V : CosimplicialObject A} {a : U ⟶ V}

namespace HomotopyEquiv

/-- A cosimplicial homotopy equivalence induces a homotopy equivalence on alternating coface map
complexes. -/
theorem alternatingCofaceMapComplex_map_isHomotopyEquivalence (e : HomotopyEquiv U V) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ))
      ((alternatingCofaceMapComplex A).map e.hom) := by
  classical
  let h :
      _root_.HomotopyEquiv
        ((alternatingCofaceMapComplex A).obj U)
        ((alternatingCofaceMapComplex A).obj V) := {
      hom := (alternatingCofaceMapComplex A).map e.hom
      inv := (alternatingCofaceMapComplex A).map e.inv
      homotopyHomInvId := by
        simpa using Classical.choice (alternatingCofaceMapComplex_map_homotopic e.homotopyHomInvId)
      homotopyInvHomId := by
        simpa using Classical.choice (alternatingCofaceMapComplex_map_homotopic e.homotopyInvHomId)
    }
  exact ⟨h, rfl⟩

end HomotopyEquiv

-- Proof sketch: choose a source-facing cosimplicial homotopy equivalence whose forward morphism is
-- `a`, then apply Lemma 14.28.6 (1) to the two `DeltaOneHomotopic` fields in that witness.
/-- Lemma 14.28.7 (1): if `a` is a homotopy equivalence of cosimplicial objects, then the induced
morphism on alternating coface map complexes `s(a) : s(U) ⟶ s(V)` is a homotopy equivalence of
cochain complexes. -/
theorem alternatingCofaceMapComplex_map_isHomotopyEquivalence
    (ha : IsHomotopyEquivalence a) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ))
      ((alternatingCofaceMapComplex A).map a) := by
  rcases ha with ⟨e, rfl⟩
  exact e.alternatingCofaceMapComplex_map_isHomotopyEquivalence

end AlternatingCofaceMapComplex

section NormalizedCochainComplex

variable [Abelian A]
local instance : CategoryTheory.Limits.HasZeroObject Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasBinaryCoproducts Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasImages Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasCokernels (CochainComplex A ℕ) := inferInstance
variable {U V : CosimplicialObject A} {a : U ⟶ V}

namespace HomotopyEquiv

/-- In an abelian category, a cosimplicial homotopy equivalence induces a homotopy equivalence on
normalized cochain complexes. -/
theorem normalizedCochainComplex_map_isHomotopyEquivalence (e : HomotopyEquiv U V) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ))
      (normalizedCochainComplexFunctor.map e.hom) := by
  classical
  let h :
      _root_.HomotopyEquiv (Q(U)) (Q(V)) := {
      hom := normalizedCochainComplexFunctor.map e.hom
      inv := normalizedCochainComplexFunctor.map e.inv
      homotopyHomInvId := by
        simpa only [Functor.map_comp, Functor.map_id] using
          Classical.choice (normalizedCochainComplex_map_homotopic e.homotopyHomInvId)
      homotopyInvHomId := by
        simpa only [Functor.map_comp, Functor.map_id] using
          Classical.choice (normalizedCochainComplex_map_homotopic e.homotopyInvHomId)
    }
  exact ⟨h, rfl⟩

end HomotopyEquiv

-- Proof sketch: choose a source-facing cosimplicial homotopy equivalence whose forward morphism is
-- `a`, then apply Lemma 14.28.6 (2) to the two `DeltaOneHomotopic` fields in that witness.
/-- Lemma 14.28.7 (2): if `A` is abelian and `a` is a homotopy equivalence of cosimplicial
objects, then the induced morphism `Q(a) : Q(U) ⟶ Q(V)` is a homotopy equivalence of cochain
complexes. -/
theorem normalizedCochainComplex_map_isHomotopyEquivalence
    (ha : IsHomotopyEquivalence a) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ))
      (normalizedCochainComplexFunctor.map a) := by
  rcases ha with ⟨e, rfl⟩
  exact e.normalizedCochainComplex_map_isHomotopyEquivalence

end NormalizedCochainComplex

end CategoryTheory.CosimplicialObject
