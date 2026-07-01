import Mathlib
import stacks_project.Chap14.Definition_14_26_6
import stacks_project.Chap14.Lemma_14_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicTopology

universe u v

noncomputable section

namespace CategoryTheory.SimplicialObject

/- Domain-style sampling for Lemma 14.27.2:
- primary domain: simplicial homotopy equivalences and the induced homotopy-equivalence property
  on the canonical chain-complex functors attached to a simplicial object;
- sampled same-kind declarations:
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.SimplicialObject.IsHomotopyEquivalence`,
  `_root_.HomotopyEquiv`,
  `HomologicalComplex.homotopyEquivalences`,
  `AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`;
- best owner abstraction: the source-side owner is
  `CategoryTheory.SimplicialObject.HomotopyEquiv U V`; the public target-side owner for this file
  is the morphism property `HomologicalComplex.homotopyEquivalences`, while chain-level
  `_root_.HomotopyEquiv` data remain internal proof witnesses only;
- primitive-vs-derived split:
  primitive data are the simplicial homotopy-equivalence witness `e : HomotopyEquiv U V` together
  with the existential chain homotopies furnished by Lemma 14.27.1;
  derived API is the pair of public morphism-property theorems for alternating face map complexes
  and normalized Moore complexes.

Source/core/bridge triage:
- `source-facing`: the textbook statement that a simplicial homotopy equivalence induces a chain
  homotopy equivalence after applying `s` or `N`;
- `core/canonical`: `_root_.HomotopyEquiv` on chain complexes;
- `bridge/view`: the public morphism property
  `HomologicalComplex.homotopyEquivalences`, with any chain-level witness data constructed only
  inside the theorem proofs. -/

section AlternatingFaceMapComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {U V : SimplicialObject A} {a : U ⟶ V}

namespace HomotopyEquiv

-- Proof sketch: apply Lemma 14.27.1 (1) to the two simplicial homotopies in `e`; these produce
-- the two chain homotopies needed to build an internal chain-level `HomotopyEquiv`, which is then
-- packaged into the canonical morphism-property owner.
/-- A simplicial homotopy equivalence induces a homotopy equivalence on alternating face map
complexes. -/
theorem alternatingFaceMapComplex_map_isHomotopyEquivalence (e : HomotopyEquiv U V) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((alternatingFaceMapComplex A).map e.hom) := by
  let h :
      _root_.HomotopyEquiv
        ((alternatingFaceMapComplex A).obj U)
        ((alternatingFaceMapComplex A).obj V) := {
      hom := (alternatingFaceMapComplex A).map e.hom
      inv := (alternatingFaceMapComplex A).map e.inv
      homotopyHomInvId := by
        classical
        simpa using
          Classical.choice
            (alternatingFaceMapComplex_map_homotopic e.homotopyHomInvId)
      homotopyInvHomId := by
        classical
        simpa using
          Classical.choice
            (alternatingFaceMapComplex_map_homotopic e.homotopyInvHomId)
    }
  exact ⟨h, rfl⟩

end HomotopyEquiv

-- Proof sketch: choose a simplicial homotopy equivalence `e` whose forward map is `a`. By
-- the previous theorem,
-- the induced map on alternating face map complexes is a chain-homotopy equivalence. The present
-- statement is the source-facing morphism-property corollary obtained by unpacking
-- `IsHomotopyEquivalence a`.
/-- Lemma 14.27.2: if a morphism of simplicial objects is a simplicial homotopy equivalence, then
the induced morphism on alternating face map complexes `s(a) : s(U) ⟶ s(V)` is a homotopy
equivalence of chain complexes. -/
theorem alternatingFaceMapComplex_map_isHomotopyEquivalence
    (ha : IsHomotopyEquivalence a) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((alternatingFaceMapComplex A).map a) := by
  rcases ha with ⟨e, rfl⟩
  exact e.alternatingFaceMapComplex_map_isHomotopyEquivalence

end AlternatingFaceMapComplex

section NormalizedMooreComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a : U ⟶ V}

namespace HomotopyEquiv

-- Proof sketch: apply Lemma 14.27.1 (2) to the two simplicial homotopies in `e`; this yields the
-- chain homotopies needed to build the internal chain-level witness for the morphism property.
/-- In an abelian category, a simplicial homotopy equivalence induces a homotopy equivalence on
normalized Moore complexes. -/
theorem normalizedMooreComplex_map_isHomotopyEquivalence (e : HomotopyEquiv U V) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((normalizedMooreComplex A).map e.hom) := by
  let h :
      _root_.HomotopyEquiv
        ((normalizedMooreComplex A).obj U)
        ((normalizedMooreComplex A).obj V) := {
      hom := (normalizedMooreComplex A).map e.hom
      inv := (normalizedMooreComplex A).map e.inv
      homotopyHomInvId := by
        classical
        rw [← Functor.map_comp, ← Functor.map_id]
        exact
          Classical.choice
            (normalizedMooreComplex_map_homotopic e.homotopyHomInvId)
      homotopyInvHomId := by
        classical
        rw [← Functor.map_comp, ← Functor.map_id]
        exact
          Classical.choice
            (normalizedMooreComplex_map_homotopic e.homotopyInvHomId)
    }
  exact ⟨h, rfl⟩

end HomotopyEquiv

-- Proof sketch: choose a simplicial homotopy equivalence `e` lifting `a`. By Lemma 14.27.1 (2),
-- the previous theorem yields the required chain-homotopy inverse for `N(a)`. The present
-- statement is the
-- source-facing morphism-property corollary obtained from `IsHomotopyEquivalence a`.
/-- In an abelian category, the normalized Moore complex also sends simplicial homotopy
equivalences to homotopy equivalences of chain complexes. -/
theorem normalizedMooreComplex_map_isHomotopyEquivalence
    (ha : IsHomotopyEquivalence a) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((normalizedMooreComplex A).map a) := by
  rcases ha with ⟨e, rfl⟩
  exact e.normalizedMooreComplex_map_isHomotopyEquivalence

end NormalizedMooreComplex

end CategoryTheory.SimplicialObject
