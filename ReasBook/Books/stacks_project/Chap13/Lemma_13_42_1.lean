import Mathlib
import stacks_project.Chap04.Definition_4_22_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe uI vD uD

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.42.1:
- primary domain: essentially constant cofiltered diagrams in pretriangulated categories, expressed by
  an eventual tailwise biproduct decomposition.
- sampled owner-level declarations:
  * `IsEssentiallyConstantCofilteredDiagram` in `Chap04/Definition_4_22_2`
  * `IsEssentiallyConstantCofilteredCone` in `Chap04/Definition_4_22_1`
  * `Functor.tail` and `Functor.mapLE` below for the canonical tail restriction and cofiltered
    transition-map surface on preorder-indexed inverse systems
  * `Pretriangulated.binaryBiproductData` in mathlib's pretriangulated API
  * `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang` in mathlib
- best owner abstraction:
  * `core/canonical`: `IsEssentiallyConstantCofilteredDiagram F`
  * `source-facing`: `HasTailDirectSumDecomposition F`, the explicit tailwise biproduct
    decomposition criterion
  * `bridge/view`: the equivalence theorem below, specialized to the pretriangulated setting

Primitive-vs-derived split:
- primitive source-facing data: a tail index, a fixed summand `A`, a complementary tail diagram
  `Z : OrderDual (Set.Ici i) ⥤ D`, a functor-level biproduct decomposition
  `F.tail i ≅ (Functor.const _).obj A ⊞ Z`, and eventual vanishing of the complementary transition
  maps along the cofiltered tail.
- derived API: the stagewise isomorphisms and their compatibility with the transition maps, both
  obtained by evaluating that natural isomorphism, together with the equivalence with the chapter
  owner `IsEssentiallyConstantCofilteredDiagram`. -/

namespace Functor

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D]

/-- The restriction of a cofiltered preorder-indexed diagram to the tail `Set.Ici i`. -/
abbrev tail (F : OrderDual I ⥤ D) (i : I) : OrderDual (Set.Ici i) ⥤ D :=
  (OrderHom.Subtype.val (Set.Ici i)).dual.toFunctor ⋙ F

/-- The transition map in a cofiltered preorder-indexed diagram attached to an inequality
`j ≤ j'`. -/
abbrev mapLE {J : Type*} [Preorder J] (F : OrderDual J ⥤ D) {j j' : J} (h : j ≤ j') :
    F.obj j' ⟶ F.obj j :=
  F.map (homOfLE h)

end

end Functor

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D] [HasBinaryBiproducts D]

/-- Evaluating a tailwise biproduct decomposition at a transition map recovers the expected
stagewise compatibility equation. -/
@[reassoc]
theorem tailDirectSumIso_hom_naturality {F : OrderDual I ⥤ D} {i : I} {A : D}
    {Z : OrderDual (Set.Ici i) ⥤ D}
    (e : F.tail i ≅ (Functor.const (OrderDual (Set.Ici i))).obj A ⊞ Z)
    {j j' : Set.Ici i} (hjj' : j ≤ j') :
    (F.tail i).mapLE hjj' ≫ (e.app j).hom =
      (e.app j').hom ≫ (((Functor.const (OrderDual (Set.Ici i))).obj A ⊞ Z).mapLE hjj') := by
  simpa [Functor.mapLE] using e.hom.naturality (homOfLE hjj')

/-- Lemma 13.42.1 source-facing criterion: after some stage, the inverse system `F` splits as a
fixed summand `A` together with a complementary tail diagram whose transition maps are eventually
zero, and the transition maps of `F` act as the identity on `A`. -/
def HasTailDirectSumDecomposition (F : OrderDual I ⥤ D) : Prop :=
  ∃ i : I,
    ∃ A : D,
      ∃ Z : OrderDual (Set.Ici i) ⥤ D,
        ∃ _e : F.tail i ≅ (Functor.const (OrderDual (Set.Ici i))).obj A ⊞ Z,
          ∀ j : Set.Ici i, ∃ j' : Set.Ici i, ∃ hjj' : j ≤ j', Z.mapLE hjj' = 0

end

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

-- Proof sketch: starting from an essentially constant cone, choose the eventual retraction from
-- Definition 4.22.1 and transport it to the whole tail. The pretriangulated splitting lemmas then
-- identify the whole tail functor with a biproduct `(Functor.const _).obj A ⊞ Z`, whose evaluated
-- components recover the stagewise isomorphisms `Fⱼ ≅ A ⊞ Zⱼ`; the factorization data assembles
-- the complementary summands into a tail inverse system whose transition maps become zero far
-- enough out.
-- Conversely, such a tailwise split decomposition directly reconstructs the retraction and
-- eventual factorization criterion in Definition 4.22.1.
/-- Lemma 13.42.1: a directed inverse system in a pretriangulated category is essentially constant
if and only if, after some index, every stage is isomorphic to a fixed summand `A` plus a
complementary inverse system `Z`, the transition maps `Fⱼ' ⟶ Fⱼ` act as the identity on `A`, and
the complementary transition maps are eventually zero. -/
theorem isEssentiallyConstantCofilteredDiagram_iff_hasEventuallyConstantDirectSumDecomposition
    [IsDirectedOrder I] (F : OrderDual I ⥤ D) :
    IsEssentiallyConstantCofilteredDiagram F ↔ HasTailDirectSumDecomposition F := sorry

end

end CategoryTheory
