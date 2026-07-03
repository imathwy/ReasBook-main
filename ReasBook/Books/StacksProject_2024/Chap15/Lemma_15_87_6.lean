import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksProject_2024.Chap15.Lemma_15_87_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]

/- Domain-style sampling for Lemma 15.87.6:
- primary domain: derived limits in a triangulated category and isomorphisms of the associated
  sequential pro-objects;
- sampled owner declarations:
  `exists_representative`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso`,
  `CategoryTheory.homToDerivedLimit_hasMilnorShortExactSequence`;
- best owner abstraction: the public pro-isomorphism hypothesis belongs to the canonical
  pro-object morphism `η`; a sequential representative of `η` is private bridge data used only to
  pass to inverse systems of abelian groups;
- primitive data: the towers `Ksys`, `Msys`, their chosen derived limits `K`, `M`, and a
  pro-object morphism
  `η : colimit (Msys.op ⋙ uliftCoyoneda.{0}) ⟶
    proSystemHomColimitFunctor Ksys ⋙ uliftFunctor.{0}`;
- derived API: the owner-level isomorphism hypothesis `IsIso η`, a chosen representative of `η`,
  the induced represented-Hom representative, and the Milnor short exact sequences from Lemma
  `15.87.5`.

Source/core/bridge triage:
- `source-facing`: the existence of a non-canonical isomorphism between chosen derived limits of
  pro-isomorphic towers;
- `core/canonical`: `η`, `IsDerivedLimit`, and the owner theorem
  `inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso`;
- `bridge/view`: a chosen representative `a` of `η` and the represented-Hom representative
  `preadditiveCoyonedaRep a L`. -/

namespace SequentialProObjectMorphismRep

variable {Ksys Msys : ℕᵒᵖ ⥤ D}

local notation "SeqRep" => _root_.CategoryTheory.SequentialProObjectMorphismRep

-- Proof sketch: apply the additive covariant functor `preadditiveCoyoneda.obj (op L)` to the
-- compatibility square defining `a`. This transports the levelwise commutativity relation from
-- `D` to the inverse systems of abelian groups `Hom_D(L, K_n)` and `Hom_D(L, M_n)`.
/-- Applying `preadditiveCoyoneda.obj (op L)` to the defining compatibility square of `a` yields
the compatibility square on the represented-Hom towers. -/
private theorem preadditiveCoyonedaRep_comm
    (a : SeqRep Ksys Msys) (L : D) :
    ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      (Ksys ⋙ preadditiveCoyoneda.obj (op L)).map (homOfLE (a.reindex.monotone h)).op ≫
          (preadditiveCoyoneda.obj (op L)).map (a.map n) =
        (preadditiveCoyoneda.obj (op L)).map (a.map n') ≫
          (Msys ⋙ preadditiveCoyoneda.obj (op L)).map (homOfLE h).op := sorry

/-- The induced representative on the sequential inverse systems of abelian groups
`Hom_D(L, K_n)` and `Hom_D(L, M_n)`. -/
private def preadditiveCoyonedaRep
    (a : SeqRep Ksys Msys) (L : D) :
    SeqRep
      (Ksys ⋙ preadditiveCoyoneda.obj (op L))
      (Msys ⋙ preadditiveCoyoneda.obj (op L)) where
  reindex := a.reindex
  hom :=
    { app := fun n ↦ (preadditiveCoyoneda.obj (op L)).map (a.map n.unop)
      naturality := fun n n' g ↦ by
        let h : n'.unop ≤ n.unop := leOfHom g.unop
        simpa [h] using preadditiveCoyonedaRep_comm a L h }

end SequentialProObjectMorphismRep

-- Proof sketch: choose a representative `a` of `η` by Example `4.22.6`, then use Remark 13.34.4
-- to extend the product maps attached to `a` to some comparison morphism `f : K ⟶ M` between
-- chosen derived-limit triangles. For every `L`, Lemma 15.87.5 gives Milnor short exact
-- sequences for `K` and `M`, while the owner-level hypothesis `IsIso η` implies, after passing to
-- the represented-Hom towers via `preadditiveCoyonedaRep a L` and applying Lemma 15.87.4, that
-- the outer vertical maps are isomorphisms. Hence `(preadditiveCoyoneda.obj (op L)).map f` is an
-- isomorphism for every `L`, so Yoneda implies that `f` itself is an isomorphism.
/-- Lemma 15.87.6: let `D` be a triangulated category, let `(K_n)` and `(M_n)` be inverse systems
of objects of `D` with derived limits `K` and `M`, and let `η` be an isomorphism between the
associated pro-objects. Then `η` induces a non-canonical isomorphism `K ⟶ M` between the chosen
derived limits. -/
theorem exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit
    {Ksys Msys : ℕᵒᵖ ⥤ D} {K M : D}
    (hK : IsDerivedLimit Ksys K) (hM : IsDerivedLimit Msys M)
    (η : colimit (Msys.op ⋙ uliftCoyoneda.{0}) ⟶
      proSystemHomColimitFunctor Ksys ⋙ uliftFunctor.{0}) [IsIso η] :
    ∃ f : K ⟶ M, IsIso f := sorry

end

end CategoryTheory
