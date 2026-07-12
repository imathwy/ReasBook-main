import StacksProject_2024.Chap14.Lemma_14_19_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.IsLimit.OfNatIso
open CategoryTheory.SimplicialObject
open SimplexCategory.Truncated
open scoped Simplicial
open scoped SimplexCategory.Truncated

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

noncomputable section

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
/-- Helper for Lemma 14.19.6: the top structured-arrow diagram for the one-step extension along
`Δ≤n ↪ Δ≤(n + 1)` is canonically represented by the same object that represents the matching
family functor of `U`. -/
private noncomputable def one_step_top_representable_by
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ) :
    (StructuredArrow.proj (op (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1)))
        (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ⋙ U).cones.RepresentableBy
      U_succ := by
  let Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
    op (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1))
  -- Proof comment: postcompose the structured-arrow category with the inclusion
  -- `Δ≤(n + 1) ↪ Δ` to compare the one-step diagram directly with the matching diagram.
  let e :
      StructuredArrow Y (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ≌
        StructuredArrow ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
          (SimplexCategory.Truncated.inclusion n).op :=
    (StructuredArrow.post Y
        (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op
        (SimplexCategory.Truncated.inclusion (n + 1)).op).asEquivalence.trans
      (StructuredArrow.mapNatIso (Iso.refl _ :
        (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ⋙
            (SimplexCategory.Truncated.inclusion (n + 1)).op ≅
          (SimplexCategory.Truncated.inclusion n).op))
  let w :
      e.functor ⋙
          StructuredArrow.proj ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
            (SimplexCategory.Truncated.inclusion n).op ⋙ U ≅
        StructuredArrow.proj Y
          (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ⋙ U :=
    Iso.refl _
  let hlim : IsLimit (limitCone hrep) :=
    IsLimit.ofRepresentableBy hrep
  -- Proof comment: first transfer the limiting cone across the indexing equivalence, then
  -- transport the resulting representability datum across the induced diagram isomorphism.
  let hrep' :
      (e.functor ⋙
          StructuredArrow.proj ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
            (SimplexCategory.Truncated.inclusion n).op ⋙ U).cones.RepresentableBy U_succ :=
    (hlim.whiskerEquivalence e).representableBy
  exact Functor.RepresentableBy.ofIso hrep' ((CategoryTheory.cones _ _).mapIso w)

/-- Helper for Lemma 14.19.6: at an old degree `Y ≤ n`, the one-step structured-arrow diagram has
the expected limit because the corresponding structured-arrow category has an initial object. -/
private noncomputable def one_step_old_hasLimit
    {n : ℕ} (U : SimplicialObject.Truncated C n)
    {Y : SimplexCategory.Truncated (n + 1)} (hY : Y.obj.len ≤ n) :
    HasLimit
      (StructuredArrow.proj
        ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op.obj
          (op (⟨Y.obj, hY⟩ : SimplexCategory.Truncated n)))
        (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ⋙ U) := by
  let X : (SimplexCategory.Truncated n)ᵒᵖ := op (⟨Y.obj, hY⟩ : SimplexCategory.Truncated n)
  -- Proof comment: `incl n (n + 1)` is the inclusion of a full subcategory, so the identity
  -- structured arrow at the old object is initial exactly as in Lemma 14.19.3.
  letI : (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).Full := by
    simpa [SimplexCategory.Truncated.incl] using
      (ObjectProperty.full_ιOfLE
        (P := fun a : SimplexCategory => a.len ≤ n)
        (P' := fun a : SimplexCategory => a.len ≤ n + 1)
        (fun _ h' => h'.trans (Nat.le_succ n)))
  letI : (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).Faithful := by
    simpa [SimplexCategory.Truncated.incl] using
      (ObjectProperty.faithful_ιOfLE
        (P := fun a : SimplexCategory => a.len ≤ n)
        (P' := fun a : SimplexCategory => a.len ≤ n + 1)
        (fun _ h' => h'.trans (Nat.le_succ n)))
  letI :
      HasInitial
        (StructuredArrow
          ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op.obj X)
          (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op) :=
    ((StructuredArrow.mkIdInitial :
      IsInitial
        (StructuredArrow.mk
          (𝟙 ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op.obj X))))).hasInitial
  infer_instance

/-- Helper for Lemma 14.19.6: the one-step structured-arrow diagram has a chosen limit at every
degree, with old degrees handled by initiality and the top degree handled by matching-family
representability. -/
private noncomputable def one_step_hasLimit
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ)
    (Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ) :
    HasLimit
      (StructuredArrow.proj Y
        (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ⋙ U) := by
  refine Opposite.rec ?_ Y
  intro Y
  by_cases hY : Y.obj.len ≤ n
  · -- Proof comment: after rewriting `Y` as the image of its old-degree predecessor, the limit is
    -- the initial-object limit from `one_step_old_hasLimit`.
    simpa using one_step_old_hasLimit (U := U) hY
  · have hlen : Y.obj.len = n + 1 := by
      exact le_antisymm Y.property (Nat.succ_le_of_lt (Nat.not_le.mp hY))
    have hEq : Y = (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1)) := by
      ext
      simpa [SimplexCategory.len_mk] using hlen
    subst hEq
    -- Proof comment: at the top degree, reuse the transported representability witness and turn it
    -- into an explicit chosen limit cone with vertex `U_succ`.
    let htop := one_step_top_representable_by (U := U) U_succ hrep
    let c :
        Cone
          (StructuredArrow.proj (op (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1))
            : (SimplexCategory.Truncated (n + 1))ᵒᵖ)
            (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ⋙ U) :=
      limitCone htop
    let hc : IsLimit c := by
      simpa [c] using (IsLimit.ofRepresentableBy htop)
    exact HasLimit.mk ⟨c, hc⟩

/-- Helper for Lemma 14.19.6: the one-step inclusion `Δ≤n ↪ Δ≤(n + 1)` is full. -/
private instance one_step_inclusion_full (n : ℕ) :
    (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).Full := by
  simpa [SimplexCategory.Truncated.incl] using
    (ObjectProperty.full_ιOfLE
      (P := fun a : SimplexCategory => a.len ≤ n)
      (P' := fun a : SimplexCategory => a.len ≤ n + 1)
      (fun _ h => h.trans (Nat.le_succ n)))

/-- Helper for Lemma 14.19.6: the one-step inclusion `Δ≤n ↪ Δ≤(n + 1)` is faithful. -/
private instance one_step_inclusion_faithful (n : ℕ) :
    (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).Faithful := by
  simpa [SimplexCategory.Truncated.incl] using
    (ObjectProperty.faithful_ιOfLE
      (P := fun a : SimplexCategory => a.len ≤ n)
      (P' := fun a : SimplexCategory => a.len ≤ n + 1)
      (fun _ h => h.trans (Nat.le_succ n)))

/-- Helper for Lemma 14.19.6: the opposite of the one-step truncation inclusion. -/
private abbrev one_step_inclusion_op (n : ℕ) :
    (SimplexCategory.Truncated n)ᵒᵖ ⥤ (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
  (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op

/-- Helper for Lemma 14.19.6: the explicit object assignment for the desired one-step extension. -/
private noncomputable def one_step_target_obj
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C) :
    (SimplexCategory.Truncated (n + 1))ᵒᵖ → C :=
  fun Y =>
    if hY : Y.unop.obj.len ≤ n then
      U.obj (op (⟨Y.unop.obj, hY⟩ : SimplexCategory.Truncated n))
    else
      U_succ

/-- Helper for Lemma 14.19.6: on old degrees the explicit extension keeps the old object. -/
private lemma one_step_target_obj_old
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (X : (SimplexCategory.Truncated n)ᵒᵖ) :
    one_step_target_obj U U_succ ((one_step_inclusion_op n).obj X) = U.obj X := by
  -- Proof comment: evaluating the explicit object assignment on an old degree triggers the old
  -- branch of the piecewise definition.
  dsimp [one_step_target_obj, one_step_inclusion_op]
  split_ifs with hX
  · cases X
    rfl
  · exact False.elim (hX X.unop.property)

/-- Helper for Lemma 14.19.6: at the top degree the explicit extension uses the representing
object `U_{n+1}`. -/
private lemma one_step_target_obj_top
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C) :
    one_step_target_obj U U_succ
        (op (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1))) =
      U_succ := by
  -- Proof comment: the top simplex has length `n + 1`, so it lands in the top-degree branch.
  simp [one_step_target_obj]

/-- Helper for Lemma 14.19.6: on old degrees the pointwise right-Kan-extension counit is an
isomorphism. -/
private theorem one_step_old_counit_isIso
    {n : ℕ} (U : SimplicialObject.Truncated C n)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (X : (SimplexCategory.Truncated n)ᵒᵖ) :
    IsIso ((Functor.pointwiseRightKanExtensionCounit (one_step_inclusion_op n) U).app X) := by
  let E : Functor.RightExtension (one_step_inclusion_op n) U :=
    Functor.RightExtension.mk _ (Functor.pointwiseRightKanExtensionCounit
      (one_step_inclusion_op n) U)
  let hE : E.IsPointwiseRightKanExtensionAt ((one_step_inclusion_op n).obj X) :=
    Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension
      (one_step_inclusion_op n) U ((one_step_inclusion_op n).obj X)
  -- Proof comment: fullness and faithfulness of the inclusion identify the old-degree counit with
  -- the initial-object projection.
  simpa [E] using
    (Functor.RightExtension.IsPointwiseRightKanExtensionAt.isIso_hom_app
      (E := E) (X := X) hE)

/-- Helper for Lemma 14.19.6: on old degrees the comparison with the pointwise right Kan
extension is the inverse counit component. -/
private noncomputable def one_step_old_component_iso
    {n : ℕ} (U : SimplicialObject.Truncated C n)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (X : (SimplexCategory.Truncated n)ᵒᵖ) :
    U.obj X ≅
      (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj
        ((one_step_inclusion_op n).obj X) :=
  letI :
      IsIso ((Functor.pointwiseRightKanExtensionCounit (one_step_inclusion_op n) U).app X) :=
    one_step_old_counit_isIso U X
  (asIso ((Functor.pointwiseRightKanExtensionCounit (one_step_inclusion_op n) U).app X)).symm

/-- Helper for Lemma 14.19.6: the chosen top-degree representing object is canonically
isomorphic to the top object of the pointwise right Kan extension. -/
private noncomputable def one_step_top_component_iso
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U] :
    U_succ ≅
      (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj
        (op (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1))) := by
  let Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
    op (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1))
  let E : Functor.RightExtension (one_step_inclusion_op n) U :=
    Functor.RightExtension.mk
      (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U)
      (Functor.pointwiseRightKanExtensionCounit (one_step_inclusion_op n) U)
  let hlimit := by
    let hE : E.IsPointwiseRightKanExtensionAt Y :=
      Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension
        (one_step_inclusion_op n) U Y
    -- Proof comment: the pointwise right Kan extension chooses a limit cone at `Y`, so its cone
    -- point already corepresents the cone functor for the top diagram.
    simpa [E] using (Limits.IsLimit.representableBy hE)
  -- Proof comment: compare the source-side representing object `U_succ` with the chosen limit
  -- object for the same top structured-arrow diagram.
  exact Functor.RepresentableBy.uniqueUpToIso
    (one_step_top_representable_by (U := U) U_succ hrep)
    hlimit

/-- Helper for Lemma 14.19.6: an old-degree object of `Δ≤(n + 1)` is literally in the image of
the one-step inclusion `Δ≤n ↪ Δ≤(n + 1)`. -/
private lemma one_step_old_obj_eq
    {n : ℕ} {Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ}
    (hY : Y.unop.obj.len ≤ n) :
    (one_step_inclusion_op n).obj (op (⟨Y.unop.obj, hY⟩ : SimplexCategory.Truncated n)) = Y := by
  apply Opposite.unop_injective
  ext
  rfl

/-- Helper for Lemma 14.19.6: an object of `Δ≤(n + 1)` that is not old must be the top simplex. -/
private lemma one_step_eq_top_of_not_old
    {n : ℕ} (Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ)
    (hY : ¬ Y.unop.obj.len ≤ n) :
    Y = op (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1)) := by
  apply Opposite.unop_injective
  have hlen : Y.unop.obj.len = n + 1 := by
    exact le_antisymm Y.unop.property (Nat.succ_le_of_lt (Nat.not_le.mp hY))
  ext
  simpa [SimplexCategory.len_mk] using hlen

/-- Helper for Lemma 14.19.6: the explicit textbook object assignment is branchwise isomorphic to
the pointwise right Kan extension object. -/
private noncomputable def one_step_component_iso
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ) :
    one_step_target_obj U U_succ Y ≅
      (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Y := by
  by_cases hY : Y.unop.obj.len ≤ n
  · -- Proof comment: on the old branch, the explicit object is literally `U.obj X`, so the
    -- comparison is the old-degree inverse counit conjugated by the literal old-object equalities.
    let X : (SimplexCategory.Truncated n)ᵒᵖ :=
      op (⟨Y.unop.obj, hY⟩ : SimplexCategory.Truncated n)
    exact
      (eqToIso (by simp [one_step_target_obj, hY, X])) ≪≫
        one_step_old_component_iso (U := U) (n := n) X ≪≫
        eqToIso (by
          simpa [X] using congrArg
            (fun Z =>
              (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Z)
            (one_step_old_obj_eq (n := n) (Y := Y) hY))
  · -- Proof comment: on the top branch, the explicit object is `U_succ`, and the comparison is
    -- the top-degree representing-object comparison conjugated by the literal top-object equality.
    exact
      (eqToIso (by simp [one_step_target_obj, hY])) ≪≫
        one_step_top_component_iso (U := U) U_succ hrep ≪≫
        eqToIso (by
          simpa using congrArg
            (fun Z =>
              (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Z)
            (one_step_eq_top_of_not_old (n := n) Y hY).symm)

/-- Helper for Lemma 14.19.6: on objects coming from `Δ≤n`, the comparison with the pointwise
right Kan extension can be written without any residual codomain transport. -/
private noncomputable def one_step_old_image_component_iso
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (X : (SimplexCategory.Truncated n)ᵒᵖ) :
    one_step_target_obj U U_succ ((one_step_inclusion_op n).obj X) ≅
      (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj
        ((one_step_inclusion_op n).obj X) :=
  eqToIso (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X) ≪≫
    one_step_old_component_iso (U := U) (n := n) X

/-- Helper for Lemma 14.19.6: rewrapping an old simplex with any proof of the same bound does not
change the corresponding object of the opposite truncated simplex category. -/
private lemma one_step_old_image_obj_eq
    {n : ℕ} (X : SimplexCategory.Truncated n)
    (hX : ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).obj X).obj.len ≤ n) :
    (op (⟨((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).obj X).obj, hX⟩ :
      SimplexCategory.Truncated n) : (SimplexCategory.Truncated n)ᵒᵖ) =
      op X := by
  -- Proof comment: the inclusion does not change the underlying simplex, so the two truncated
  -- objects differ only by proof data and hence coincide by extensionality.
  cases X
  rfl

/-- Helper for Lemma 14.19.6: on a literal inclusion-image object, the residual codomain
transport in the old branch of `one_step_component_iso` is the identity. -/
private lemma one_step_old_image_transport
    {n : ℕ} (U : SimplicialObject.Truncated C n) (_U_succ : C)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (X : (SimplexCategory.Truncated n)ᵒᵖ) :
    eqToHom
        (congrArg
          (fun Z =>
            (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Z)
          (one_step_old_obj_eq (n := n)
            (Y := (one_step_inclusion_op n).obj X) X.unop.property)) =
      𝟙 _ := by
  -- Proof comment: after exposing the literal inclusion-image object, the residual transport is
  -- definitionally reflexive, so its `eqToHom` is the identity.
  cases X
  rfl

/-- Helper for Lemma 14.19.6: on an inclusion-image object, the old-branch comparison has the
expected hom component. -/
private lemma one_step_component_iso_old_image_hom
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (X : (SimplexCategory.Truncated n)ᵒᵖ) :
    (one_step_component_iso (U := U) U_succ hrep ((one_step_inclusion_op n).obj X)).hom =
      eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X) ≫
        (one_step_old_component_iso (U := U) (n := n) X).hom := by
  -- Route correction: specialize `one_step_component_iso` to the literal inclusion-image object
  -- and eliminate the proof-only rewrapping by cases on `X`.
  cases X
  rename_i X
  have hY : (unop ((one_step_inclusion_op n).obj (op X))).obj.len ≤ n := by
    simpa [one_step_inclusion_op] using X.property
  rw [one_step_component_iso, dif_pos hY]
  have hp : hY = X.property := Subsingleton.elim _ _
  subst hp
  have hobj :
      (op (⟨(unop ((one_step_inclusion_op n).obj (op X))).obj, X.property⟩ :
        SimplexCategory.Truncated n) : (SimplexCategory.Truncated n)ᵒᵖ) =
        op X := by
    simpa [one_step_inclusion_op] using one_step_old_image_obj_eq (n := n) X X.property
  have hiso_hom :
      (one_step_old_component_iso (U := U) (n := n)
          (op (⟨(unop ((one_step_inclusion_op n).obj (op X))).obj,
            X.property⟩ : SimplexCategory.Truncated n))).hom =
        (one_step_old_component_iso (U := U) (n := n) (op X)).hom := by
    cases hobj
    rfl
  have htransport :
      eqToHom
          (congrArg
            (fun Z =>
              (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Z)
            (one_step_old_obj_eq (n := n)
              (Y := (one_step_inclusion_op n).obj (op X)) X.property)) =
        𝟙 _ := by
    simpa [one_step_inclusion_op] using
      one_step_old_image_transport (U := U) (_U_succ := U_succ) (n := n) (op X)
  simp only [Iso.trans_hom, eqToIso.hom]
  rw [htransport]
  rw [hiso_hom]
  have hId :
      (𝟙 ((Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj
          ((one_step_inclusion_op n).obj
            (op (⟨(unop ((one_step_inclusion_op n).obj (op X))).obj, X.property⟩ :
              SimplexCategory.Truncated n))))) =
        𝟙 ((Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj
          ((one_step_inclusion_op n).obj (op X))) := by
    cases hobj
    rfl
  rw [hId]
  cases hobj
  let f :
      one_step_target_obj U U_succ ((one_step_inclusion_op n).obj (op X)) ⟶
        U.obj (op X) :=
    eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) (op X))
  let g :
      U.obj (op X) ⟶
        (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj
          ((one_step_inclusion_op n).obj (op X)) :=
    (one_step_old_component_iso (U := U) (n := n) (op X)).hom
  calc
    f ≫ g ≫ 𝟙 _ = (f ≫ g) ≫ 𝟙 _ := by
      simpa using (Category.assoc f g (𝟙 _)).symm
    _ = f ≫ g := by
      exact Category.comp_id (f ≫ g)

/-- Helper for Lemma 14.19.6: on an inclusion-image object, the old-branch comparison has the
expected inverse component. -/
private lemma one_step_component_iso_old_image_inv
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (X : (SimplexCategory.Truncated n)ᵒᵖ) :
    (one_step_component_iso (U := U) U_succ hrep ((one_step_inclusion_op n).obj X)).inv =
      (one_step_old_component_iso (U := U) (n := n) X).inv ≫
        eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X).symm := by
  -- Route correction: the inverse endpoint uses the same specialized inclusion-image
  -- normalization as the hom endpoint, so the remaining transport disappears after `cases X`.
  cases X
  rename_i X
  have hY : (unop ((one_step_inclusion_op n).obj (op X))).obj.len ≤ n := by
    simpa [one_step_inclusion_op] using X.property
  rw [one_step_component_iso, dif_pos hY]
  have hp : hY = X.property := Subsingleton.elim _ _
  subst hp
  have hobj :
      (op (⟨(unop ((one_step_inclusion_op n).obj (op X))).obj, X.property⟩ :
        SimplexCategory.Truncated n) : (SimplexCategory.Truncated n)ᵒᵖ) =
        op X := by
    simpa [one_step_inclusion_op] using one_step_old_image_obj_eq (n := n) X X.property
  have hiso_inv :
      (one_step_old_component_iso (U := U) (n := n)
          (op (⟨(unop ((one_step_inclusion_op n).obj (op X))).obj,
            X.property⟩ : SimplexCategory.Truncated n))).inv =
        (one_step_old_component_iso (U := U) (n := n) (op X)).inv := by
    cases hobj
    rfl
  have htransport :
      eqToHom
          (congrArg
            (fun Z =>
              (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Z)
            (one_step_old_obj_eq (n := n)
              (Y := (one_step_inclusion_op n).obj (op X)) X.property)) =
        𝟙 _ := by
    simpa [one_step_inclusion_op] using
      one_step_old_image_transport (U := U) (_U_succ := U_succ) (n := n) (op X)
  have htransport_symm :
      eqToHom
          (congrArg
            (fun Z =>
              (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Z)
            (one_step_old_obj_eq (n := n)
              (Y := (one_step_inclusion_op n).obj (op X)) X.property)).symm =
        𝟙 _ := by
    cases
      congrArg
        (fun Z =>
          (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Z)
        (one_step_old_obj_eq (n := n)
          (Y := (one_step_inclusion_op n).obj (op X)) X.property)
    rfl
  simp only [Iso.trans_inv, eqToIso.inv, Category.assoc]
  rw [htransport_symm]
  rw [hiso_inv]
  exact
    Category.id_comp
      ((one_step_old_component_iso (U := U) (n := n) (op X)).inv ≫
        eqToHom
          (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) (op X)).symm)

/-- Helper for Lemma 14.19.6: conjugating a functor by a componentwise family of isomorphisms
preserves identity maps. -/
private theorem one_step_conjugated_extension_map_id
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (eObj :
      ∀ Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ,
        one_step_target_obj U U_succ Y ≅
          (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Y)
    (Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ) :
    (eObj Y).hom ≫
        (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).map (𝟙 Y) ≫
        (eObj Y).inv =
      𝟙 (one_step_target_obj U U_succ Y) := by
  -- Proof comment: the conjugated identity collapses to the identity after functoriality of
  -- `pointwiseRightKanExtension` and the inverse identities of `eObj Y`.
  rw [Functor.map_id]
  simp

/-- Helper for Lemma 14.19.6: conjugating a functor by a componentwise family of isomorphisms
preserves composition. -/
private theorem one_step_conjugated_extension_map_comp
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (eObj :
      ∀ Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ,
        one_step_target_obj U U_succ Y ≅
          (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Y)
    {X Y Z : (SimplexCategory.Truncated (n + 1))ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (eObj X).hom ≫
        (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).map (f ≫ g) ≫
        (eObj Z).inv =
      ((eObj X).hom ≫
          (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).map f ≫
          (eObj Y).inv) ≫
        ((eObj Y).hom ≫
          (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).map g ≫
          (eObj Z).inv) := by
  -- Proof comment: insert the middle identity `(eObj Y).inv ≫ (eObj Y).hom = 𝟙` between the two
  -- conjugated factors and use functoriality of the right Kan extension.
  rw [Functor.map_comp]
  simp [Category.assoc]

/-- Helper for Lemma 14.19.6: the conjugated extension carries the comparison family as a natural
isomorphism to the pointwise right Kan extension. -/
private theorem one_step_conjugated_extension_hom_naturality
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (eObj :
      ∀ Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ,
        one_step_target_obj U U_succ Y ≅
          (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Y)
    {X Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ} (f : X ⟶ Y) :
    ((eObj X).hom ≫
        (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).map f ≫
        (eObj Y).inv) ≫
        (eObj Y).hom =
      (eObj X).hom ≫
        (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).map f := by
  -- Proof comment: the comparison family isomorphism is natural because the terminal inverse-hom
  -- pair on the target object cancels immediately.
  simp [Category.assoc]

/-- Helper for Lemma 14.19.6: conjugating the pointwise right Kan extension by the comparison
family produces the explicit one-step extension functor. -/
private noncomputable def one_step_conjugated_extension
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    (eObj :
      ∀ Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ,
        one_step_target_obj U U_succ Y ≅
          (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).obj Y) :
    SimplicialObject.Truncated C (n + 1) where
  obj := one_step_target_obj U U_succ
  map := fun f ↦
    (eObj _).hom ≫
      (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).map f ≫
      (eObj _).inv
  map_id := one_step_conjugated_extension_map_id U U_succ eObj
  map_comp := one_step_conjugated_extension_map_comp U U_succ eObj

/-- Helper for Lemma 14.19.6: on the old part of the simplex category, the conjugated extension
has exactly the same structure maps as `U`. -/
private lemma one_step_conjugated_old_map_eq
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ)
    [Functor.HasPointwiseRightKanExtension (one_step_inclusion_op n) U]
    {X X' : (SimplexCategory.Truncated n)ᵒᵖ} (f : X ⟶ X') :
    (one_step_conjugated_extension (U := U) U_succ
        (one_step_component_iso (U := U) U_succ hrep)).map
        ((one_step_inclusion_op n).map f) =
      eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X) ≫
        U.map f ≫
        eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X').symm := by
  -- Proof comment: once the old-image comparison is normalized, this becomes counit naturality.
  -- Proof comment: rewrite the endpoint comparison by the explicit old-image formulas, then use
  -- naturality of the pointwise counit to replace the middle composite by `U.map f`.
  change
    (one_step_component_iso (U := U) U_succ hrep
        (op ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).obj X.unop))).hom ≫
      (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).map
        ((one_step_inclusion_op n).map f) ≫
      (one_step_component_iso (U := U) U_succ hrep
        (op ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).obj X'.unop))).inv =
    eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X) ≫
      U.map f ≫
      eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X').symm
  have hhom :
      (one_step_component_iso (U := U) U_succ hrep
          (op ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).obj X.unop))).hom =
        eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X) ≫
          (one_step_old_component_iso (U := U) (n := n) X).hom := by
    simpa [one_step_inclusion_op] using
      one_step_component_iso_old_image_hom (U := U) (U_succ := U_succ) (hrep := hrep) X
  have hinv :
      (one_step_component_iso (U := U) U_succ hrep
          (op ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).obj X'.unop))).inv =
        (one_step_old_component_iso (U := U) (n := n) X').inv ≫
          eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X').symm := by
    simpa [one_step_inclusion_op] using
      one_step_component_iso_old_image_inv (U := U) (U_succ := U_succ) (hrep := hrep) X'
  rw [hhom, hinv]
  have hmiddle :
      (one_step_old_component_iso (U := U) (n := n) X).hom ≫
          (Functor.pointwiseRightKanExtension (one_step_inclusion_op n) U).map
            ((one_step_inclusion_op n).map f) ≫
          (one_step_old_component_iso (U := U) (n := n) X').inv =
        U.map f := by
    let ε := Functor.pointwiseRightKanExtensionCounit (one_step_inclusion_op n) U
    have hnat := NatTrans.naturality ε f
    simpa [Category.assoc, one_step_old_component_iso] using
      congrArg
        (fun k => (one_step_old_component_iso (U := U) (n := n) X).hom ≫ k)
        hnat
  simpa [Category.assoc] using
    congrArg
      (fun k =>
        eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X) ≫
          k ≫
          eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X').symm)
      hmiddle

/-- Lemma 14.19.6: if the matching-family functor of an `n`-truncated simplicial object `U` is
representable by an object `U_{n+1}` of `C`, then `U` extends to an `(n + 1)`-truncated
simplicial object with degree-`n + 1` term `U_{n+1}` and with the expected adjointness between
maps into the extension and maps into `U` after truncation. The adjointness part is recorded by
the canonical representability owner for the one-step truncation functor. -/
@[stacks 0187]
theorem exists_truncated_extension_of_matching_family_representable
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ) :
    ∃ (V : SimplicialObject.Truncated C (n + 1))
      (htrunc : (Truncated.trunc C (n + 1) n).obj V = U),
        V.obj (op ⦋n + 1⦌ₙ₊₁) = U_succ ∧
          (((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).IsRepresentedBy
            (eqToHom htrunc)) := by
  let L :
      (SimplexCategory.Truncated n)ᵒᵖ ⥤ (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
    one_step_inclusion_op n
  -- Proof comment: the source proof first forms the canonical one-step right Kan extension over
  -- `Δ≤n ↪ Δ≤(n + 1)` using the old-degree initiality and the top-degree matching object.
  letI : Functor.HasPointwiseRightKanExtension L U :=
    fun Y ↦ one_step_hasLimit (U := U) U_succ hrep Y
  -- Route correction: instead of forcing literal equalities directly on the right Kan extension,
  -- conjugate it by the normalized old-degree counit isomorphisms and the top-degree
  -- representability isomorphism.
  let W : SimplicialObject.Truncated C (n + 1) :=
    Functor.pointwiseRightKanExtension L U
  let eObj :
      ∀ Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ,
        one_step_target_obj U U_succ Y ≅ W.obj Y :=
    one_step_component_iso (U := U) U_succ hrep
  let V : SimplicialObject.Truncated C (n + 1) :=
    one_step_conjugated_extension (U := U) U_succ eObj
  let e : V ≅ W :=
    NatIso.ofComponents eObj
      (one_step_conjugated_extension_hom_naturality (U := U) U_succ eObj)
  have htrunc : (Truncated.trunc C (n + 1) n).obj V = U := by
    -- Proof comment: the conjugated extension agrees literally with `U` on old degrees, both on
    -- objects and on structure maps, so truncation identifies it with `U`.
    refine Functor.ext ?_ ?_
    · intro X
      simpa [V, one_step_conjugated_extension, Truncated.trunc, L] using
        one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X
    · intro X X' f
      simpa [V, one_step_conjugated_extension, Truncated.trunc, L] using
        one_step_conjugated_old_map_eq (U := U) (U_succ := U_succ) (hrep := hrep) (f := f)
  have htop : V.obj (op ⦋n + 1⦌ₙ₊₁) = U_succ := by
    -- Proof comment: at the new top degree, the explicit object assignment is exactly `U_succ`.
    simpa [V, one_step_conjugated_extension] using
      one_step_target_obj_top (U := U) (U_succ := U_succ) (n := n)
  let E : Functor.RightExtension L U :=
    Functor.RightExtension.mk W (Functor.pointwiseRightKanExtensionCounit L U)
  have hE : E.IsPointwiseRightKanExtension := by
    intro Y
    simpa [E, W] using
      Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension L U Y
  have hW :
      (((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).IsRepresentedBy
        (Functor.pointwiseRightKanExtensionCounit L U)) := by
    refine Functor.IsRepresentedBy.mk ?_
    intro X
    constructor
    · intro f g hfg
      -- Proof comment: the universal morphism into the right Kan extension is characterized by
      -- postcomposing with the counit.
      apply (hE.isUniversal).hom_ext
      simpa [Truncated.trunc, L] using hfg
    · intro α
      refine ⟨(hE.isUniversal).lift (Functor.RightExtension.mk X α), ?_⟩
      -- Proof comment: the universal lift realizes any truncation morphism uniquely as a map
      -- into the pointwise right Kan extension.
      simpa [Truncated.trunc, L] using
        (hE.isUniversal).fac (Functor.RightExtension.mk X α)
  have hcounit :
      (((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).map e.hom.op)
          (Functor.pointwiseRightKanExtensionCounit L U) =
        eqToHom htrunc := by
    -- Proof comment: on each old degree the conjugated comparison is the inverse counit, so the
    -- transported counit becomes the identity witness for `htrunc`.
    apply NatTrans.ext
    funext X
    -- Proof comment: evaluate the transported counit at `X`, rewrite the comparison component on
    -- the old branch, and then identify the result with the object component of `htrunc`.
    have hcomp :
        (e.hom.app (L.obj X)) ≫ (Functor.pointwiseRightKanExtensionCounit L U).app X =
          eqToHom (one_step_target_obj_old (U := U) (U_succ := U_succ) (n := n) X) := by
      -- Proof comment: the component of `e.hom` on an old degree is the normalized comparison
      -- isomorphism, whose hom followed by the counit is the literal old-degree identity.
      have hh :=
        congrArg
          (fun k =>
            k ≫ (Functor.pointwiseRightKanExtensionCounit L U).app X)
          (one_step_component_iso_old_image_hom (U := U) (U_succ := U_succ)
            (hrep := hrep) X)
      simpa [L, e, V, W, one_step_conjugated_extension, Category.assoc,
        one_step_old_component_iso] using hh
    -- Proof comment: after unfolding the Yoneda transport and the truncation equality, the target
    -- component is exactly the same old-degree identity as `hcomp`.
    simpa [Truncated.trunc, L, e, V, W, htrunc, one_step_conjugated_extension, Category.assoc]
      using hcomp
  have hV :
      (((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).IsRepresentedBy
        (eqToHom htrunc)) := by
    -- Proof comment: transport the representing element on `W` across the comparison isomorphism
    -- `e : V ≅ W`, then rewrite that transported element using `hcounit`.
    exact hcounit ▸ (Functor.IsRepresentedBy.of_isoObj hW e)
  exact ⟨V, htrunc, htop, hV⟩

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

end
end CategoryTheory
