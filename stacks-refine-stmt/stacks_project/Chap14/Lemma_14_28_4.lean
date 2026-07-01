import Mathlib
import stacks_project.Chap14.Remark_14_26_4
import stacks_project.Chap14.Remark_14_28_2
import stacks_project.Chap14.Lemma_14_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

universe u v u' v'

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.28.4:
- primary domain: simplicial and cosimplicial homotopy relations under functoriality and passage to
  opposites;
- sampled same-kind owner declarations:
  `CategoryTheory.SimplicialObject.Homotopic.whiskerRight`,
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopic.whiskerRight`,
  `CategoryTheory.CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`;
- best owner abstraction: the covariant functoriality statements are already owned by
  `SimplicialObject.Homotopic` and `CosimplicialObject.DeltaOneHomotopic`; the contravariant cases
  in this file are only bridge/view lemmas obtained by composing those owner theorems with the
  opposite-equivalence bridge from Lemma 14.28.3;
- primitive data: only the existing homotopy relation witness;
- derived API: contravariant transport via `NatTrans.unop` or `NatTrans.op`.

Source/core/bridge triage:
- `source-facing`: the four Stacks functoriality clauses;
- `core/canonical`: `SimplicialObject.Homotopic.whiskerRight` and
  `CosimplicialObject.DeltaOneHomotopic.whiskerRight`;
- `bridge/view`: the two contravariant-image clauses below, expressed through
  `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`. -/

/- Lemma 14.28.4 (1): a covariant functor sends homotopic morphisms of simplicial objects to
homotopic morphisms of the image simplicial objects. -/
recall SimplicialObject.Homotopic.whiskerRight
    {D : Type u} [Category.{v} D]
    {U V : SimplicialObject D} {a b : U ⟶ V}
    {D' : Type u'} [Category.{v'} D']
    (h : SimplicialObject.Homotopic a b)
    (F : D ⥤ D') :
  SimplicialObject.Homotopic (Functor.whiskerRight a F) (Functor.whiskerRight b F)

/- Lemma 14.28.4 (2): a covariant functor sends `Δ[1]`-homotopic morphisms of cosimplicial
objects to `Δ[1]`-homotopic morphisms of the image cosimplicial objects. -/
recall CosimplicialObject.DeltaOneHomotopic.whiskerRight
    {C : Type u} [Category.{v} C]
    {C' : Type u'} [Category.{v'} C']
    {U V : CosimplicialObject C} {a b : U ⟶ V}
    (h : CosimplicialObject.DeltaOneHomotopic a b)
    (F : C ⥤ C') :
  CosimplicialObject.DeltaOneHomotopic
    (Functor.whiskerRight a F)
    (Functor.whiskerRight b F)

-- Proof sketch: first whisker the simplicial zigzag along the contravariant functor viewed as a
-- covariant functor into `Cᵒᵖ`; this gives a zigzag of simplicial homotopies in `Cᵒᵖ`. Then apply
-- Lemma 14.28.3 backwards to convert that zigzag into a `Δ[1]`-homotopy zigzag of cosimplicial
-- morphisms in `C`.
section

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

namespace SimplicialObject

variable {U V : SimplicialObject D} {a b : U ⟶ V}

/-- Lemma 14.28.4 (3): a contravariant functor sends homotopic morphisms of simplicial objects to
`Δ[1]`-homotopic morphisms of the associated image cosimplicial objects, reversing the direction
of the maps. This is a bridge/view lemma, not a second owner. -/
theorem Homotopic.contravariantMap
    (h : Homotopic a b) (F : D ⥤ Cᵒᵖ) :
    CosimplicialObject.DeltaOneHomotopic
      (NatTrans.unop (Functor.whiskerRight a F))
      (NatTrans.unop (Functor.whiskerRight b F)) := by
  simpa using
    (CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag
      (NatTrans.unop (Functor.whiskerRight a F))
      (NatTrans.unop (Functor.whiskerRight b F))).2
      (h.whiskerRight F)

end SimplicialObject

-- Proof sketch: convert the given `Δ[1]`-homotopy zigzag to the opposite simplicial zigzag using
-- Lemma 14.28.3, apply the simplicial covariant functoriality statement to `F : Cᵒᵖ ⥤ D`, and
-- identify the resulting whiskered maps with the induced simplicial maps on the contravariant
-- images.
namespace CosimplicialObject

variable {U V : CosimplicialObject C} {a b : U ⟶ V}

/-- Lemma 14.28.4 (4): a contravariant functor sends `Δ[1]`-homotopic morphisms of cosimplicial
objects to homotopic morphisms of the associated image simplicial objects, reversing the direction
of the maps. This is a bridge/view lemma, not a second owner. -/
theorem DeltaOneHomotopic.contravariantMap
    (h : DeltaOneHomotopic a b) (F : Cᵒᵖ ⥤ D) :
    SimplicialObject.Homotopic
      (Functor.whiskerRight (NatTrans.op a) F)
      (Functor.whiskerRight (NatTrans.op b) F) := by
  simpa using
    ((deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag a b).1 h).whiskerRight F

end CosimplicialObject
end

end CategoryTheory
