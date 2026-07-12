import Mathlib
import StacksProject_2024.Chap10.Definition_10_88_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace Module

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Chap10 Definition 10 88 7: a directed colimit presentation of an `R`-module by a
Mittag-Leffler directed system. -/
structure MittagLefflerPresentation (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] where
  index : Type v
  indexPreorder : Preorder index
  indexNonempty : Nonempty index
  indexDirected : IsDirectedOrder index
  diagram : index ⥤ ModuleCat R
  presentation_isMittagLeffler : @IsMittagLefflerDirectedSystem R _ index indexPreorder
    indexNonempty indexDirected diagram
  colimitIso : Nonempty (colimit diagram ≅ ModuleCat.of R M)

/-- Helper for Chap10 Definition 10 88 7: an `R`-module `M` is Mittag-Leffler when it is the
colimit of a directed system satisfying `IsMittagLefflerDirectedSystem`. -/
@[stacks 059F]
class MittagLeffler (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] where
  exists_presentation : Nonempty (MittagLefflerPresentation R M)

/-- Helper for Chap10 Definition 10 88 7: the one-object constant module diagram with value
`M`. -/
abbrev constantModuleDiagram : PUnit.{v + 1} ⥤ ModuleCat.{v} R :=
  (Functor.const PUnit.{v + 1}).obj (ModuleCat.of.{v} R M)

/-- Helper for Chap10 Definition 10 88 7: every transition map in the Hom inverse system of the
constant diagram is the identity on morphisms. -/
lemma constantModuleDiagram_homInverseSystem_map
    (N : ModuleCat.{v} R) {i j : (PUnit.{v + 1})ᵒᵖ} (f : i ⟶ j)
    (φ : (colimitPresentationHomInverseSystem.{u, v, 0}
      (constantModuleDiagram (R := R) (M := M)) N).obj i) :
    (colimitPresentationHomInverseSystem.{u, v, 0}
      (constantModuleDiagram (R := R) (M := M)) N).map f φ =
      φ := by
  -- There is only one object and one morphism, so the contravariant Hom map is the identity.
  cases i
  cases j
  simp [constantModuleDiagram, colimitPresentationHomInverseSystem]

/-- Helper for Chap10 Definition 10 88 7: the Hom inverse system associated to the constant
diagram is Mittag-Leffler. -/
lemma constantModuleDiagram_homInverseSystem_isMittagLeffler (N : ModuleCat.{v} R) :
    (colimitPresentationHomInverseSystem.{u, v, 0}
      (constantModuleDiagram (R := R) (M := M)) N).IsMittagLeffler := by
  -- Surjectivity of all transition maps reduces the Mittag-Leffler condition to the preceding
  -- identity computation.
  refine Functor.isMittagLeffler_of_surjective (F :=
    colimitPresentationHomInverseSystem.{u, v, 0}
      (constantModuleDiagram (R := R) (M := M)) N) ?_
  intro i j f φ
  exact ⟨φ, constantModuleDiagram_homInverseSystem_map (R := R) (M := M) N f φ⟩

/-- Helper for Chap10 Definition 10 88 7: the constant diagram on a finitely presented module is a
Mittag-Leffler directed system. -/
lemma constantModuleDiagram_isMittagLefflerDirectedSystem [Module.FinitePresentation R M] :
    @IsMittagLefflerDirectedSystem R _ PUnit.{v + 1} inferInstance inferInstance inferInstance
      (constantModuleDiagram (R := R) (M := M)) := by
  -- The directed-system predicate has the stagewise finite-presentation field and the Hom-system
  -- Mittag-Leffler field.
  refine ⟨?_, ?_⟩
  · intro i
    -- Every stage is the original module `M`.
    cases i
    simpa [constantModuleDiagram] using (inferInstance : Module.FinitePresentation R M)
  · intro N
    exact constantModuleDiagram_homInverseSystem_isMittagLeffler (R := R) (M := M) N

/-- Helper for Chap10 Definition 10 88 7: the colimit of the one-object constant diagram is its
constant value. -/
lemma constantModuleDiagram_colimitIso :
    Nonempty (colimit (constantModuleDiagram (R := R) (M := M)) ≅ ModuleCat.of.{v} R M) := by
  -- The connected-constant-colimit API identifies the colimit of a constant diagram with the
  -- displayed value.
  exact ⟨colimit.isoColimitCocone
    ⟨constCocone PUnit.{v + 1} (ModuleCat.of.{v} R M), isColimitConstCocone PUnit.{v + 1}
      (ModuleCat.of.{v} R M)⟩⟩

-- Proof sketch: take the constant one-object directed system on `M`. Finite presentation gives the
-- stagewise hypothesis, the colimit is `M` itself, and the unique transition maps satisfy the
-- factorization condition tautologically.
/-- Chap10 Definition 10 88 7: a finitely presented module is Mittag-Leffler. -/
instance instMittagLefflerOfFinitePresentation
    [Module.FinitePresentation R M] : MittagLeffler R M := by
  -- Package the constant directed-system presentation; all proof fields are supplied by the named
  -- helpers above.
  refine ⟨⟨{
    index := PUnit.{v + 1}
    indexPreorder := inferInstance
    indexNonempty := inferInstance
    indexDirected := inferInstance
    diagram := constantModuleDiagram (R := R) (M := M)
    presentation_isMittagLeffler :=
      constantModuleDiagram_isMittagLefflerDirectedSystem (R := R) (M := M)
    colimitIso := constantModuleDiagram_colimitIso (R := R) (M := M)
  }⟩⟩

end

end Module
