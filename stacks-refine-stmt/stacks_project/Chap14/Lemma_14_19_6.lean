import stacks_project.Chap14.Lemma_14_19_5

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open SimplexCategory.Truncated
open scoped Simplicial
open scoped SimplexCategory.Truncated

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.19.6:
- primary domain: one-step right-adjoint objects for truncation of truncated simplicial objects;
- sampled owner API:
  `Functor.rightAdjointObjIsDefined`,
  `Functor.rightAdjointObjIsDefined_iff`,
  `Functor.partialRightAdjointObj`,
  `Functor.partialRightAdjointHomEquiv`;
- best owner abstraction: the one-step truncation functor
  `Truncated.trunc C (n + 1) n : SimplicialObject.Truncated C (n + 1) ⥤
    SimplicialObject.Truncated C n`
  together with the representability owner
  `((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).IsRepresentedBy (eqToHom htrunc)`;
- primitive data: the truncated simplicial object `U`, the proposed top-degree object `U_succ`,
  and the matching-family representability hypothesis
  `(matchingFamilyFunctor U).RepresentableBy U_succ`;
- derived API: existence of an `(n + 1)`-truncated extension with the prescribed truncation and
  top-degree term, and the owner-level consequence that the object `U` lies in the domain of
  definition of the partial right adjoint of `Truncated.trunc C (n + 1) n` under the weaker
  hypothesis that `matchingFamilyFunctor U` is representable.

Source/core/bridge triage:
- `source-facing`: the existence of a one-step extension of `U` with top term `U_succ`;
- `core/canonical`: `Functor.rightAdjointObjIsDefined` for `Truncated.trunc C (n + 1) n`;
- `bridge/view`: the specific witness object `V : SimplicialObject.Truncated C (n + 1)` together
  with the universal element `eqToHom htrunc :
    (Truncated.trunc C (n + 1) n).obj V ⟶ U` and the representability datum
  `((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).IsRepresentedBy (eqToHom htrunc)`.

The old file packaged this bridge data into a bespoke structure. The refined file keeps the
source-facing existence theorem directly, but replaces the ad hoc `homEquiv` field by the canonical
representability owner and exposes the partial-right-adjoint consequence as a separate theorem. -/

-- Proof sketch: use the representing object for `matchingFamilyFunctor U` as the new degree
-- `n + 1` term, define the extra simplicial structure maps by the universal property of the
-- matching diagram, and then identify morphisms into the extension with morphisms into `U`
-- after truncation.
/-- Lemma 14.19.6: if the matching-family functor of an `n`-truncated simplicial object `U` is
representable by an object `U_{n+1}` of `C`, then `U` extends to an `(n + 1)`-truncated
simplicial object with degree-`n + 1` term `U_{n+1}` and with the expected adjointness between
maps into the extension and maps into `U` after truncation. The adjointness part is recorded by
the canonical representability owner for the one-step truncation functor. -/
theorem exists_truncated_extension_of_matching_family_representable
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ) :
    ∃ (V : SimplicialObject.Truncated C (n + 1))
      (htrunc : (Truncated.trunc C (n + 1) n).obj V = U),
        V.obj (op ⦋n + 1⦌ₙ₊₁) = U_succ ∧
          (((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).IsRepresentedBy
            (eqToHom htrunc)) := by
  sorry

-- Proof sketch: unpack the source-facing existence theorem and forget the explicit witness `V`;
-- the remaining content is exactly the owner predicate `rightAdjointObjIsDefined` for the
-- one-step truncation functor, which only depends on `matchingFamilyFunctor U` being
-- representable.
/-- The extension theorem of Lemma 14.19.6 implies that `U` lies in the domain of definition of
the partial right adjoint to one-step truncation. -/
theorem trunc_succ_rightAdjointObjIsDefined_of_matching_family_representable
    {n : ℕ} (U : SimplicialObject.Truncated C n)
    (hrep : (matchingFamilyFunctor U).IsRepresentable) :
    (Truncated.trunc C (n + 1) n).rightAdjointObjIsDefined U := by
  letI := hrep
  rw [Functor.rightAdjointObjIsDefined_iff]
  rcases exists_truncated_extension_of_matching_family_representable
      U (matchingFamilyFunctor U).reprX (matchingFamilyFunctor U).representableBy with
    ⟨V, htrunc, -, hV⟩
  simpa using hV.representableBy.isRepresentable

end CategoryTheory
