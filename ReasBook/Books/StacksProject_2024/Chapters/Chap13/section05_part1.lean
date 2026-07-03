import Mathlib
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_5_1 (from Chap13) -/
universe v u

namespace CategoryTheory.MorphismProperty

/- Domain-style sampling:
- primary domain: compatibility of multiplicative systems with the triangulated structure on a
  pretriangulated category, as used in localization of triangulated categories;
- relevant upstream owner declarations in this domain:
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.IsCompatibleWithShift`,
  `MorphismProperty.compatible_with_triangulation`,
  `Triangulated.Localization.pretriangulated`,
  `Triangulated.Localization.isTriangulated_functor`;
- source/core/bridge triage:
  `source-facing`: Stacks Definition 13.5.1, namely compatibility with the triangulated
    structure, consisting of the shift condition `f ∈ S ↔ f[1] ∈ S` together with the
    distinguished-triangle completion square;
  `core/canonical`: the owner class `MorphismProperty.IsCompatibleWithTriangulation`, whose
    primitive data is exactly the shift-compatibility owner `MorphismProperty.IsCompatibleWithShift`
    plus the triangle-completion field `compatible_with_triangulation`;
  `bridge/view`: the projection `compatible_with_triangulation`, used downstream to complete a
    morphism of distinguished triangles.

Primitive data is exactly the canonical owner class; the named projection and the localization
consequences are derived API. Since Definition 13.5.1 only recalls this existing owner, the
refined file should stay a pure canonical recall rather than introducing any parallel wrapper.
-/

/- Definition 13.5.1: the textbook notion that a multiplicative system is compatible with the
triangulated structure, meaning both shift invariance and the distinguished-triangle completion
condition, is the canonical mathlib class `MorphismProperty.IsCompatibleWithTriangulation`. -/
recall IsCompatibleWithTriangulation

/- Companion recall: the triangle-completion clause of Definition 13.5.1 is exposed by the
projection `compatible_with_triangulation`; the shift clause is inherited from
`MorphismProperty.IsCompatibleWithShift`. -/
recall compatible_with_triangulation

end CategoryTheory.MorphismProperty

/-! ### Lemma_13_5_2 (from Chap13) -/
universe v u

namespace CategoryTheory

open CategoryTheory.MorphismProperty
open Pretriangulated
open CategoryTheory.Pretriangulated.Opposite

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling:
- primary domain: morphism properties on a pretriangulated category, especially the canonical
  owners `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.RespectsIso`,
  `MorphismProperty.HasLeftCalculusOfFractions`, and
  `MorphismProperty.HasRightCalculusOfFractions`;
- sampled upstream declarations in this domain:
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.compatible_with_triangulation`,
  `MorphismProperty.isomorphisms_le_of_containsIdentities`,
  `MorphismProperty.HasLeftCalculusOfFractions`,
  `MorphismProperty.HasRightCalculusOfFractions`;
- best owner abstraction: the calculus-of-fractions conclusions are owner instances on the
  existing `MorphismProperty` class, so this file should refine to those owners directly rather
  than introducing any parallel wrapper structure.

Primitive data:
- the morphism property `S`;
- the canonical owner assumptions `[S.ContainsIdentities]`, `[S.IsMultiplicative]`,
  `[S.IsCompatibleWithTriangulation]`;
- the source-facing cancellation hypotheses `hExt`.

Derived API:
- clause `(1)` is a direct recall of the chapter-level theorem
  `isomorphisms_le_of_containsIdentities_of_triangleCompletion`;
- the owner instances `S.HasLeftCalculusOfFractions` and `S.HasRightCalculusOfFractions`.

Source/core/bridge triage:
- `source-facing`: the three textbook clauses of Lemma 13.5.2;
- `core/canonical`: the `MorphismProperty` owners listed above;
- `bridge/view`: the source hypotheses `hExt`, feeding the canonical owner fields `ext`.
-/

/- Lemma 13.5.2 (1): if a morphism property `S` on a pretriangulated category contains all
identities and satisfies the triangulated compatibility axiom `MS6`, then every isomorphism of
the category lies in `S`. This is the owner-level theorem from Remark `13.5.3`, recalled here
rather than redeclared under a parallel name. -/
recall isomorphisms_le_of_containsIdentities_of_triangleCompletion

section

variable (S : MorphismProperty D) [S.IsMultiplicative] [S.IsCompatibleWithTriangulation]

omit [S.IsMultiplicative] in
/-- Helper for Lemma 13.5.2: a commutative square on the second and third morphisms of
distinguished triangles extends to a first morphism that still lies in the property. -/
lemma complete_compatible_triangle_morphism₁
    (T₁ T₂ : Triangle D) (hT₁ : T₁ ∈ distTriang D) (hT₂ : T₂ ∈ distTriang D)
    (b : T₁.obj₂ ⟶ T₂.obj₂) (c : T₁.obj₃ ⟶ T₂.obj₃)
    (hb : S b) (hc : S c) (comm : T₁.mor₂ ≫ c = b ≫ T₂.mor₂) :
    ∃ (a : T₁.obj₁ ⟶ T₂.obj₁), S a ∧ T₁.mor₁ ≫ b = a ≫ T₂.mor₁ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  -- Rotate once so that the given `mor₂`/`mor₃` square becomes the standard MS6 input.
  obtain ⟨d, hd, hd₁, hd₂⟩ := S.compatible_with_triangulation T₁.rotate T₂.rotate
    (rot_of_distTriang _ hT₁) (rot_of_distTriang _ hT₂) b c hb hc comm
  refine ⟨(shiftFunctor D (1 : ℤ)).preimage d, ?_, ?_, ?_⟩
  · -- Shift compatibility transfers membership from the rotated third map back to the source.
    have hd' : S (((shiftFunctor D (1 : ℤ)).preimage d)⟦(1 : ℤ)⟧') := by
      simpa using hd
    simpa [Functor.map_preimage] using
      (IsCompatibleWithShift.iff S ((shiftFunctor D (1 : ℤ)).preimage d) (1 : ℤ)).1 hd'
  · -- This is the rotated `comm₃` identity rewritten back on the original triangles.
    apply (shiftFunctor D (1 : ℤ)).map_injective
    dsimp at hd₂
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_inj] at hd₂
    simpa only [Functor.map_comp, Functor.map_preimage] using hd₂
  · -- This is the rotated `comm₂` identity after undoing the shift.
    simpa only [Functor.map_preimage] using hd₁

end

instance isCompatibleWithTriangulation_op (S : MorphismProperty D)
    [S.IsMultiplicative] [S.IsCompatibleWithTriangulation] : S.op.IsCompatibleWithTriangulation := by
  -- The shift field on the opposite category comes from the explicit opposite-shift isomorphism.
  have hiso : isomorphisms D ≤ S :=
    isomorphisms_le_of_containsIdentities_of_triangleCompletion S
      (fun T₁ T₂ hT₁ hT₂ a b ha hb hab ↦ by
        obtain ⟨c, hc, hc₂, hc₃⟩ := S.compatible_with_triangulation T₁ T₂ hT₁ hT₂ a b ha hb hab
        exact ⟨c, hc, hc₂, hc₃⟩)
  letI : S.RespectsIso := respectsIso_of_isStableUnderComposition hiso
  refine
    { toIsCompatibleWithShift := ?_
      compatible_with_triangulation := ?_ }
  · refine ⟨fun n ↦ ?_⟩
    ext X Y f
    change S ((f⟦n⟧').unop) ↔ S f.unop
    let eX := (shiftFunctorOpIso D n (-n) (add_neg_cancel n)).app X
    let eY := (shiftFunctorOpIso D n (-n) (add_neg_cancel n)).app Y
    have hrewrite :
        ((f⟦n⟧').unop) = eY.inv.unop ≫ (f.unop⟦(-n : ℤ)⟧') ≫ eX.hom.unop := by
      simpa [eX, eY] using congrArg Quiver.Hom.unop
        (shiftFunctor_op_map (C := D) f n (-n) (add_neg_cancel n))
    let eX' := eX.unop
    let eY' := eY.symm.unop
    rw [hrewrite]
    simpa [eX, eY, eX', eY', Category.assoc] using
      ((S.cancel_left_of_respectsIso eY'.hom ((f.unop⟦(-n : ℤ)⟧') ≫ eX'.hom)).trans
        ((S.cancel_right_of_respectsIso (f.unop⟦(-n : ℤ)⟧') eX'.hom).trans
          (IsCompatibleWithShift.iff S f.unop (-n : ℤ))))
  · -- TODO for Lemma 13.5.2: transport the rotated `mor₂/mor₃` compatibility helper
    -- through `triangleOpEquivalence` to recover the opposite MS6 field.
    intro T₁ T₂ hT₁ hT₂ a b ha hb comm
    let U₁ : Triangle D := ((triangleOpEquivalence D).inverse.obj T₁).unop
    let U₂ : Triangle D := ((triangleOpEquivalence D).inverse.obj T₂).unop
    have hU₁ : U₁ ∈ distTriang D := by
      simpa [U₁] using (unop_distinguished T₁ hT₁)
    have hU₂ : U₂ ∈ distTriang D := by
      simpa [U₂] using (unop_distinguished T₂ hT₂)
    -- The opposite `mor₁` square is a `mor₂/mor₃` square on the unop triangles.
    obtain ⟨c, hc, hc₁, hc₂⟩ :=
      complete_compatible_triangle_morphism₁ (S := S) U₂ U₁ hU₂ hU₁ b.unop a.unop hb ha
        (Quiver.Hom.op_inj comm.symm)
    -- This is the same normalization used in mathlib's opposite pretriangulated structure.
    replace hc₂ := ((opShiftFunctorEquivalence D 1).unitIso.hom.app T₂.obj₁).unop ≫= hc₂
    dsimp [U₁, U₂] at hc₁ hc₂
    refine ⟨c.op, hc, ?_, ?_⟩
    · exact Quiver.Hom.unop_inj hc₁.symm
    · apply Quiver.Hom.unop_inj
      apply (shiftFunctor D (1 : ℤ)).map_injective
      have hnat' :
          ((opShiftFunctorEquivalence D 1).unitIso.inv.app T₂.obj₁).unop ≫
              (shiftFunctor D (1 : ℤ)).map ((shiftFunctor Dᵒᵖ (1 : ℤ)).map a).unop =
            a.unop ≫ ((opShiftFunctorEquivalence D 1).unitIso.inv.app T₁.obj₁).unop := by
        simpa [Category.assoc] using congrArg Quiver.Hom.unop
          (opShiftFunctorEquivalence_unitIso_inv_naturality
            (C := D) (n := (1 : ℤ)) (f := a))
      have hnat :
          (shiftFunctor D (1 : ℤ)).map ((shiftFunctor Dᵒᵖ (1 : ℤ)).map a).unop =
            ((opShiftFunctorEquivalence D 1).unitIso.hom.app T₂.obj₁).unop ≫
              a.unop ≫ ((opShiftFunctorEquivalence D 1).unitIso.inv.app T₁.obj₁).unop := by
        have hnat'' := congrArg (((opShiftFunctorEquivalence D 1).unitIso.hom.app T₂.obj₁).unop ≫ ·)
          hnat'
        simpa only [Category.assoc, Iso.unop_hom_inv_id_app_assoc] using hnat''
      have hcomm' :
          (((opShiftFunctorEquivalence D 1).unitIso.hom.app T₂.obj₁).unop ≫
              a.unop ≫ ((opShiftFunctorEquivalence D 1).unitIso.inv.app T₁.obj₁).unop) ≫
            (shiftFunctor D (1 : ℤ)).map T₁.mor₃.unop =
          ((opShiftFunctorEquivalence D 1).unitIso.hom.app T₂.obj₁).unop ≫
            ((opShiftFunctorEquivalence D 1).unitIso.inv.app T₂.obj₁).unop ≫
              (shiftFunctor D (1 : ℤ)).map T₂.mor₃.unop ≫ (shiftFunctor D (1 : ℤ)).map c := by
        simpa [Category.assoc] using hc₂.symm
      rw [unop_comp, unop_comp, Functor.map_comp, Functor.map_comp]
      rw [hnat]
      have hcancel :
          ((opShiftFunctorEquivalence D 1).unitIso.hom.app T₂.obj₁).unop ≫
              ((opShiftFunctorEquivalence D 1).unitIso.inv.app T₂.obj₁).unop ≫
                (shiftFunctor D (1 : ℤ)).map T₂.mor₃.unop ≫ (shiftFunctor D (1 : ℤ)).map c =
            (shiftFunctor D (1 : ℤ)).map T₂.mor₃.unop ≫ (shiftFunctor D (1 : ℤ)).map c.op.unop := by
        simpa [Category.assoc, Quiver.Hom.unop_op] using
          (CategoryTheory.Iso.unop_hom_inv_id_app_assoc
            ((opShiftFunctorEquivalence D 1).unitIso) T₂.obj₁
            ((shiftFunctor D (1 : ℤ)).map T₂.mor₃.unop ≫ (shiftFunctor D (1 : ℤ)).map c))
      exact hcomm'.trans hcancel

section

variable (S : MorphismProperty D) [S.IsMultiplicative] [S.IsCompatibleWithTriangulation]

-- Proof sketch: for a right fraction `X' ⟶ X ⟶ Y`, complete `X ⟶ Y` and `X' ⟶ X` to
-- distinguished triangles, rotate the second triangle so that the shift-compatibility and triangle
-- completion data bundled in `S.IsCompatibleWithTriangulation` apply to the maps in `S`, and
-- obtain the required denominator on the target side. The explicit hypothesis `hExt` supplies the
-- left-cancellation field of `HasLeftCalculusOfFractions`.
/-- Lemma 13.5.2 (2): if a morphism property `S` is multiplicative, satisfies the left
denominator cancellation hypothesis `hExt`, and is compatible with the triangulated structure,
then `S` has the left calculus of fractions. -/
theorem hasLeftCalculusOfFractions_of_ext_and_compatibleWithTriangulation
    (hExt :
      ∀ ⦃X' X Y : D⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X),
        S s →
          s ≫ f₁ = s ≫ f₂ →
            ∃ (Y' : D) (t : Y ⟶ Y'), S t ∧ f₁ ≫ t = f₂ ≫ t) :
    S.HasLeftCalculusOfFractions := by
  refine
    { toIsMultiplicative := inferInstance
      exists_leftFraction := ?_
      ext := ?_ }
  · intro X Y φ
    obtain ⟨Z, g, h, hT₁₀⟩ := distinguished_cocone_triangle φ.f
    let T₁ : Triangle D := Triangle.mk φ.f g h
    have hT₁ : T₁ ∈ distTriang D := by
      simpa [T₁] using hT₁₀
    obtain ⟨Y', f', g', hT₂₀⟩ := distinguished_cocone_triangle₂ (h ≫ φ.s⟦(1 : ℤ)⟧')
    let T₂ : Triangle D := Triangle.mk f' g' (h ≫ φ.s⟦(1 : ℤ)⟧')
    have hT₂ : T₂ ∈ distTriang D := by
      simpa [T₂] using hT₂₀
    -- Route correction: choose the dotted map directly from MS6 on the rotated triangles,
    -- so the denominator is produced inside `S` rather than proved afterward.
    obtain ⟨s', hs', _, hs'₂⟩ :=
      complete_compatible_triangle_morphism₁ (S := S) T₁.rotate T₂.rotate
        (rot_of_distTriang _ hT₁) (rot_of_distTriang _ hT₂) (𝟙 Z) (φ.s⟦(1 : ℤ)⟧')
        (S.id_mem Z) ((IsCompatibleWithShift.iff S φ.s (1 : ℤ)).2 φ.hs)
        (by
          dsimp [T₁, T₂]
          simp)
    refine ⟨MorphismProperty.LeftFraction.mk f' s' hs', ?_⟩
    -- Undo the rotation relation on the third morphisms to recover the roof equality.
    apply (shiftFunctor D (1 : ℤ)).map_injective
    dsimp [T₁, T₂] at hs'₂
    have hs'' :
        -((shiftFunctor D (1 : ℤ)).map (φ.f ≫ s')) =
          -((shiftFunctor D (1 : ℤ)).map (φ.s ≫ f')) := by
      calc
        -((shiftFunctor D (1 : ℤ)).map (φ.f ≫ s')) =
            (-(shiftFunctor D (1 : ℤ)).map φ.f) ≫ (shiftFunctor D (1 : ℤ)).map s' := by
              rw [Functor.map_comp, Preadditive.neg_comp]
        _ = (shiftFunctor D (1 : ℤ)).map φ.s ≫ (-(shiftFunctor D (1 : ℤ)).map f') := hs'₂
        _ = -((shiftFunctor D (1 : ℤ)).map (φ.s ≫ f')) := by
              rw [Functor.map_comp, Preadditive.comp_neg]
    exact neg_inj.mp hs''
  · intro X' X Y f₁ f₂ s hs hsf
    obtain ⟨Y', t, ht, hfac⟩ := hExt f₁ f₂ s hs hsf
    exact ⟨Y', t, ht, hfac⟩

-- Proof sketch: apply the previous argument in the opposite category. Equivalently, rotate the
-- distinguished triangles in the proof of clause `(2)` to turn a left fraction into a right
-- fraction, and use the explicit right-cancellation hypothesis `hExt` to recover the second field
-- of `HasRightCalculusOfFractions`. The canonical `op`/`unop` transport for calculi of fractions
-- then carries the left-handed owner back to `S`.
/-- Lemma 13.5.2 (3): if a morphism property `S` is multiplicative, satisfies the right
denominator cancellation hypothesis `hExt`, and is compatible with the triangulated structure,
then `S` has the right calculus of fractions. -/
theorem hasRightCalculusOfFractions_of_ext_and_compatibleWithTriangulation
    (hExt :
      ∀ ⦃X Y Y' : D⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y'),
        S s →
          f₁ ≫ s = f₂ ≫ s →
            ∃ (X' : D) (t : X' ⟶ X), S t ∧ t ≫ f₁ = t ≫ f₂) :
    S.HasRightCalculusOfFractions := by
  have hExtOp :
      ∀ ⦃X' X Y : Dᵒᵖ⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X),
        S.op s →
          s ≫ f₁ = s ≫ f₂ →
            ∃ (Y' : Dᵒᵖ) (t : Y ⟶ Y'), S.op t ∧ f₁ ≫ t = f₂ ≫ t := by
    intro X' X Y f₁ f₂ s hs hsf
    obtain ⟨X'', t, ht, hfac⟩ := hExt f₁.unop f₂.unop s.unop hs
      (by simpa using congrArg Quiver.Hom.unop hsf)
    exact ⟨Opposite.op X'', t.op, ht, by simpa using congrArg Quiver.Hom.op hfac⟩
  letI : S.op.HasLeftCalculusOfFractions :=
    hasLeftCalculusOfFractions_of_ext_and_compatibleWithTriangulation (S.op) hExtOp
  exact inferInstanceAs (S.op).unop.HasRightCalculusOfFractions

end

end CategoryTheory

/-! ### Remark_13_5_3 (from Chap13) -/
universe v u

namespace CategoryTheory

open CategoryTheory.MorphismProperty
open Limits
open Pretriangulated
open scoped ZeroObject

section

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]

/- Domain-style sampling:
- primary domain: shift-compatibility of morphism properties on a pretriangulated category;
- sampled owner declarations in this domain:
  `MorphismProperty.IsCompatibleWithShift`,
  `MorphismProperty.IsCompatibleWithShift.iff`,
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.compatible_with_triangulation`,
  `MorphismProperty.RespectsIso`,
  `MorphismProperty.respectsIso_of_isStableUnderComposition`;
- best owner abstraction: the canonical owner for shift invariance is
  `MorphismProperty.IsCompatibleWithShift ℤ`;
- primitive data: a morphism property `S`, the one-step textbook condition `MS5`, and in the
  pretriangulated situation the triangle-completion clause `MS6`;
- derived API: iso-invariance `S.RespectsIso` and the formulas `S (s⟦n⟧') ↔ S s` for arbitrary
  shifts.

Source/core/bridge triage:
- `source-facing`: the textbook `MS5` formulation using the shift by `1`;
- `core/canonical`: `S.IsCompatibleWithShift ℤ`;
- `bridge/view`: deriving the all-shifts formulation from `MS5` once `S` respects
  isomorphisms. -/

-- Proof sketch: the canonical shift isomorphisms identify `(s⟦n⟧')⟦(1 : ℤ)⟧'` with
-- `s⟦n + 1⟧'`; use `S.RespectsIso` to transport membership across these isomorphisms and then
-- iterate the one-step equivalence `hMS5` over positive and negative integers.
/-- If a morphism property respects isomorphisms, then the textbook one-step shift
compatibility condition `MS5` propagates to every integer shift. -/
theorem mem_shift_iff_of_mem_shift_one_iff
    (S : MorphismProperty D) [S.RespectsIso]
    (hMS5 : ∀ ⦃X Y : D⦄ (s : X ⟶ Y), S (s⟦(1 : ℤ)⟧') ↔ S s)
    {X Y : D} (s : X ⟶ Y) (n : ℤ) :
    S (s⟦n⟧') ↔ S s := by
  have hsucc : ∀ m : ℤ, S (s⟦m + 1⟧') ↔ S (s⟦m⟧') := fun m ↦ by
    have hshift : S (s⟦m⟧'⟦(1 : ℤ)⟧') ↔ S (s⟦m⟧') := hMS5 (s⟦m⟧')
    have hiso : S (s⟦m⟧'⟦(1 : ℤ)⟧') ↔ S (s⟦m + 1⟧') := by
      rw [@shift_shift' D ℤ _ _ _ X Y s m (1 : ℤ)]
      simpa [Category.assoc] using
        ((S.cancel_left_of_respectsIso
          ((CategoryTheory.shiftAdd X m (1 : ℤ)).inv)
          ((s⟦m + 1⟧') ≫ (CategoryTheory.shiftAdd Y m (1 : ℤ)).hom)).trans
            (S.cancel_right_of_respectsIso
              (s⟦m + 1⟧') ((CategoryTheory.shiftAdd Y m (1 : ℤ)).hom)))
    exact hiso.symm.trans hshift
  refine Int.induction_on n ?_ ?_ ?_
  · rw [@shiftZero' D ℤ _ _ _ X Y s]
    simpa [Category.assoc] using
      ((S.cancel_left_of_respectsIso
        ((shiftZero ℤ X).hom)
        (s ≫ (shiftZero ℤ Y).inv)).trans
          (S.cancel_right_of_respectsIso s
            ((shiftZero ℤ Y).inv)))
  · intro m hm
    simpa using (hsucc m).trans hm
  · intro m hm
    have hm' : -(m : ℤ) - 1 + 1 = -(m : ℤ) := by
      omega
    have hpred := (hsucc (-(m : ℤ) - 1)).symm
    rw [hm'] at hpred
    exact hpred.trans hm

end

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable (S : MorphismProperty D)
variable
  (hMS6 :
    ∀ (T₁ T₂ : Triangle D) (_ : T₁ ∈ distTriang D) (_ : T₂ ∈ distTriang D)
      (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
      (_ : S a) (_ : S b) (_ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁),
        ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), S c ∧
          T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
            T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃)

/- Domain-style sampling for the triangle-completion part:
- primary domain: compatibility of multiplicative morphism properties with a pretriangulated
  structure;
- sampled owner declarations:
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.compatible_with_triangulation`,
  `MorphismProperty.IsCompatibleWithShift`,
  `IsCompatibleWithShift.iff`;
- best owner abstraction: once the triangle-completion datum `hMS6` is fixed, the chapter owner is
  `S.IsCompatibleWithTriangulation`, while `S.IsCompatibleWithShift ℤ` is only its canonical
  shift field;
- primitive data: the morphism property `S`, the textbook one-step condition `MS5`, and the fixed
  triangle-completion datum `hMS6`;
- derived API: the owner theorem producing `S.IsCompatibleWithTriangulation`, the shift-field
  companion theorem, and the all-shifts reformulation. -/

include hMS6

-- Proof sketch: complete the map from the contractible distinguished triangle on `𝟙 X` to a
-- distinguished triangle on an isomorphism `f` using `hMS6`; the third component lies in `S`,
-- and the usual contractible-triangle argument identifies `f` itself as lying in `S`.
/-- If a morphism property contains identities and satisfies the triangle-completion axiom
`MS6`, then every isomorphism lies in the property. -/
theorem isomorphisms_le_of_containsIdentities_of_triangleCompletion
    [S.ContainsIdentities] :
    isomorphisms D ≤ S := by
  intro X Y f hf
  letI : IsIso f := hf
  let T₁ : Triangle D := Triangle.mk (0 : 0 ⟶ X) (𝟙 X) 0
  let T₂ : Triangle D := Triangle.mk (0 : 0 ⟶ X) f 0
  have hT₁ : T₁ ∈ distTriang D := by
    dsimp [T₁]
    simpa using contractible_distinguished₁ X
  have hT₂ : T₂ ∈ distTriang D := by
    refine (Triangle.distinguished_iff_of_isZero₁ _ (Limits.isZero_zero D)).2 ?_
    dsimp [T₂]
    infer_instance
  obtain ⟨c, hc, hc₂, _⟩ := hMS6 T₁ T₂ hT₁ hT₂ (𝟙 (0 : D)) (𝟙 X) (S.id_mem 0) (S.id_mem X)
    (by dsimp [T₁, T₂]; simp)
  have hcf : c = f := by
    simpa [T₁, T₂] using hc₂
  simpa [hcf] using hc

/-- Remark 13.5.3: in a pretriangulated category, if a multiplicative morphism property
satisfies the triangle-completion axiom `MS6`, then the textbook one-step axiom `MS5` upgrades
that fixed triangle-completion datum to the canonical owner
`MorphismProperty.IsCompatibleWithTriangulation`. -/
theorem isCompatibleWithTriangulation_of_mem_shift_one_iff_of_triangleCompletion
    [S.IsMultiplicative]
    (hMS5 : ∀ ⦃X Y : D⦄ (s : X ⟶ Y), S (s⟦(1 : ℤ)⟧') ↔ S s) :
    S.IsCompatibleWithTriangulation := by
  have hiso : isomorphisms D ≤ S :=
    isomorphisms_le_of_containsIdentities_of_triangleCompletion S hMS6
  letI : S.RespectsIso := respectsIso_of_isStableUnderComposition hiso
  exact
    { toIsCompatibleWithShift :=
        { condition := fun n ↦ by
            ext X Y s
            simpa using (mem_shift_iff_of_mem_shift_one_iff S hMS5 s n) }
      compatible_with_triangulation := by
        intro T₁ T₂ hT₁ hT₂ a b ha hb hab
        obtain ⟨c, hc, hc₂, hc₃⟩ := hMS6 T₁ T₂ hT₁ hT₂ a b ha hb hab
        exact ⟨c, hc, hc₂, hc₃⟩ }

/-- Companion formulation of Remark 13.5.3: with `hMS6` fixed, the textbook one-step axiom
`MS5` is equivalent to the shift field of the owner
`MorphismProperty.IsCompatibleWithTriangulation`. -/
theorem isCompatibleWithShift_iff_mem_shift_one_iff_of_triangleCompletion
    [S.IsMultiplicative] :
    (∀ ⦃X Y : D⦄ (s : X ⟶ Y), S (s⟦(1 : ℤ)⟧') ↔ S s) ↔ S.IsCompatibleWithShift ℤ := by
  constructor
  · intro hMS5
    letI : S.IsCompatibleWithTriangulation :=
      isCompatibleWithTriangulation_of_mem_shift_one_iff_of_triangleCompletion S hMS6 hMS5
    infer_instance
  · intro h X Y s
    letI : S.IsCompatibleWithShift ℤ := h
    simpa using (IsCompatibleWithShift.iff S s (1 : ℤ))

/-- Companion formulation of Remark 13.5.3: the textbook one-step axiom `MS5` is equivalent to
asking `S (s⟦n⟧') ↔ S s` for every integer shift `n`. The main owner-level statement is
`isCompatibleWithTriangulation_of_mem_shift_one_iff_of_triangleCompletion`. -/
theorem mem_shift_one_iff_iff_mem_shift_of_triangleCompletion
    [S.IsMultiplicative] :
    (∀ ⦃X Y : D⦄ (s : X ⟶ Y), S (s⟦(1 : ℤ)⟧') ↔ S s) ↔
      ∀ ⦃X Y : D⦄ (s : X ⟶ Y) (n : ℤ), S (s⟦n⟧') ↔ S s := by
  constructor
  · intro hMS5 X Y s n
    letI : S.IsCompatibleWithTriangulation :=
      isCompatibleWithTriangulation_of_mem_shift_one_iff_of_triangleCompletion S hMS6 hMS5
    simpa using (IsCompatibleWithShift.iff S s n)
  · intro h X Y s
    simpa using h s (1 : ℤ)

omit hMS6

end

end CategoryTheory

/-! ### Lemma_13_5_4 (from Chap13) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open ObjectProperty
open MorphismProperty
open Pretriangulated

section

variable {D : Type u₁} {D' : Type u₂} [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D'] [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D' n)]
  [Pretriangulated D] [Pretriangulated D']

section ExactFunctor

variable (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/- Domain-style sampling:
- primary domain: the triangulated kernel of an exact functor and its associated cone-defined
  morphism property;
- sampled owner declarations:
  `Functor.kernel`,
  `ObjectProperty.trW`,
  `IsSaturatedMultiplicativeSystem`;
- best owner abstraction: for an exact functor `F`, the intrinsic morphism property is
  `F.kernel.trW`; the source-facing class of morphisms inverted by `F` should be treated as a
  bridge/view of this owner via an equality theorem, with compatibility and saturation derived
  from the owner-level picture;
- primitive data: the functor `F` together with the exact-functor owners
  `[F.CommShift ℤ]` and `[F.IsTriangulated]`;
- derived API: the bridge `F.kernel.trW = ((isomorphisms D').inverseImage F)` and the resulting
  saturated multiplicative-system structure on the source-facing inverse-image class.

Source/core/bridge triage:
- `source-facing`: Lemma 13.5.4, asserting that the morphisms inverted by an exact functor form a
  saturated multiplicative system;
- `core/canonical`: the kernel object property `F.kernel` and the cone-defined owner `F.kernel.trW`;
- `bridge/view`: the identification of `F.kernel.trW` with the inverse-image class of
  isomorphisms.
-/

-- Proof sketch: complete `f` to a distinguished triangle in `D`; the cone of `f` belongs to
-- `F.kernel` exactly when the mapped triangle in `D'` has zero third object, which is equivalent
-- to `F.map f` being an isomorphism.
/-- For an exact functor, the source-facing class of inverted morphisms is exactly the canonical
cone-defined morphism property of its kernel subcategory. -/
theorem kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor
    : F.kernel.trW = (isomorphisms D').inverseImage F := by
  ext X Y f
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  simpa [Functor.kernel, prop_inverseImage_iff, MorphismProperty.inverseImage_iff,
      isomorphisms.iff] using
    ((F.kernel).trW_iff_of_distinguished (Triangle.mk f g h) hT).trans
      (Triangle.isZero₃_iff_isIso₁ (F.mapTriangle.obj (Triangle.mk f g h))
        (F.map_distinguished _ hT))

private theorem inverseImage_isomorphisms_of_exactFunctor_ext_left
    {X' X Y : D} (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X)
    (hs : ((isomorphisms D').inverseImage F) s) (hsf : s ≫ f₁ = s ≫ f₂) :
    ∃ (Y' : D) (t : Y ⟶ Y'), ((isomorphisms D').inverseImage F) t ∧ f₁ ≫ t = f₂ ≫ t := by
  rw [← kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] at hs
  rcases hs with ⟨Z, g, h, H, hZ⟩
  have hsf' : s ≫ (f₁ - f₂) = 0 := by
    simpa using (sub_eq_zero.2 hsf : s ≫ f₁ - s ≫ f₂ = 0)
  obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ _ H _ hsf'
  obtain ⟨Y', r, t, hT⟩ := distinguished_cocone_triangle q
  refine ⟨Y', r, ?_, ?_⟩
  · have hr : F.kernel.trW r :=
      ⟨_, _, _, rot_of_distTriang _ hT, F.kernel.le_shift _ _ hZ⟩
    simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hr
  · apply sub_eq_zero.1
    have hzero : (f₁ - f₂) ≫ r = 0 := by
      rw [hq]
      have hqr : q ≫ r = 0 := comp_distTriang_mor_zero₁₂ _ hT
      calc
        ((Triangle.mk s g h).mor₂ ≫ q) ≫ r = (Triangle.mk s g h).mor₂ ≫ (q ≫ r) := by
          simp [Category.assoc]
        _ = 0 := by
          rw [hqr]
          change (Triangle.mk s g h).mor₂ ≫ (0 : (Triangle.mk s g h).obj₃ ⟶ Y') = 0
          exact Limits.comp_zero
    simpa using hzero

private theorem inverseImage_isomorphisms_of_exactFunctor_ext_right
    {X Y Y' : D} (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y')
    (hs : ((isomorphisms D').inverseImage F) s) (hfs : f₁ ≫ s = f₂ ≫ s) :
    ∃ (X' : D) (t : X' ⟶ X), ((isomorphisms D').inverseImage F) t ∧ t ≫ f₁ = t ≫ f₂ := by
  rw [← kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] at hs
  change F.kernel.trW s at hs
  rw [F.kernel.trW_iff'] at hs
  rcases hs with ⟨Z, g, h, H, hZ⟩
  have hfs' : (f₁ - f₂) ≫ s = 0 := by
    simpa using (sub_eq_zero.2 hfs : f₁ ≫ s - f₂ ≫ s = 0)
  obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ H _ hfs'
  obtain ⟨X', t, r, hT⟩ := distinguished_cocone_triangle₁ q
  refine ⟨X', t, ?_, ?_⟩
  · have ht : F.kernel.trW t := ⟨_, _, _, hT, hZ⟩
    simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using ht
  · apply sub_eq_zero.1
    have hzero : t ≫ (f₁ - f₂) = 0 := by
      rw [hq]
      have htq : t ≫ q = 0 := comp_distTriang_mor_zero₁₂ _ hT
      calc
        t ≫ (q ≫ (Triangle.mk g s h).mor₁) = (t ≫ q) ≫ (Triangle.mk g s h).mor₁ := by
          simp [Category.assoc]
        _ = 0 := by
          rw [htq]
          change (0 : X' ⟶ (Triangle.mk g s h).obj₁) ≫ (Triangle.mk g s h).mor₁ = 0
          exact Limits.zero_comp
    simpa using hzero

private theorem kernel_trW_of_exactFunctor_hasLeftCalculusOfFractions
    : HasLeftCalculusOfFractions F.kernel.trW := by
  refine
    { toIsMultiplicative := ?_
      exists_leftFraction := ?_
      ext := ?_ }
  · simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using
      (inferInstance : ((isomorphisms D').inverseImage F).IsMultiplicative)
  · intro X Y φ
    obtain ⟨Z, f, g, H, hZ⟩ := φ.hs
    obtain ⟨Y', s', f', hT⟩ := distinguished_cocone_triangle₂ (g ≫ φ.f⟦1⟧')
    obtain ⟨b, ⟨hb₁, _⟩⟩ := complete_distinguished_triangle_morphism₂ _ _ H hT φ.f (𝟙 Z)
      (by simp)
    exact ⟨MorphismProperty.LeftFraction.mk b s' ⟨_, _, _, hT, hZ⟩, hb₁.symm⟩
  · intro X' X Y f₁ f₂ s hs hsf
    have hs' : ((isomorphisms D').inverseImage F) s := by
      simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hs
    obtain ⟨Y', t, ht, hfac⟩ :=
      inverseImage_isomorphisms_of_exactFunctor_ext_left F f₁ f₂ s hs' hsf
    have ht' : F.kernel.trW t := by
      simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using ht
    exact ⟨Y', t, ht', hfac⟩

private theorem kernel_trW_of_exactFunctor_hasRightCalculusOfFractions
    : HasRightCalculusOfFractions F.kernel.trW := by
  refine
    { toIsMultiplicative := ?_
      exists_rightFraction := ?_
      ext := ?_ }
  · simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using
      (inferInstance : ((isomorphisms D').inverseImage F).IsMultiplicative)
  · intro X Y φ
    obtain ⟨Z, f, g, H, hZ⟩ := φ.hs
    obtain ⟨X', f', h', hT⟩ := distinguished_cocone_triangle₁ (φ.f ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ _ hT H φ.f (𝟙 Z)
      (by simp)
    exact ⟨MorphismProperty.RightFraction.mk f' ⟨_, _, _, hT, hZ⟩ a, ha₁⟩
  · intro X Y Y' f₁ f₂ s hs hfs
    have hs' : ((isomorphisms D').inverseImage F) s := by
      simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hs
    obtain ⟨X', t, ht, hfac⟩ :=
      inverseImage_isomorphisms_of_exactFunctor_ext_right F f₁ f₂ s hs' hfs
    have ht' : F.kernel.trW t := by
      simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using ht
    exact ⟨X', t, ht', hfac⟩

-- Proof sketch: the owner `F.kernel.trW` has the left and right calculus of fractions by the
-- standard `trW` completion arguments, with multiplicativity transported from the equivalent
-- inverse-image isomorphism class. The saturation axiom is then reduced to the corresponding
-- saturation of `isomorphisms D'` via the bridge theorem.
/-- The cone-defined morphism property attached to the kernel of an exact functor is a saturated
multiplicative system. -/
theorem kernel_trW_of_exactFunctor_isSaturatedMultiplicativeSystem
    : IsSaturatedMultiplicativeSystem F.kernel.trW := by
  letI : HasLeftCalculusOfFractions F.kernel.trW :=
    kernel_trW_of_exactFunctor_hasLeftCalculusOfFractions F
  letI : HasRightCalculusOfFractions F.kernel.trW :=
    kernel_trW_of_exactFunctor_hasRightCalculusOfFractions F
  refine
    { toHasLeftCalculusOfFractions := inferInstance
      toHasRightCalculusOfFractions := inferInstance
      saturation := ?_ }
  intro X₀ X₁ X₂ X₃ f g h hfg hgh
  have hfg' : ((isomorphisms D').inverseImage F) (f ≫ g) := by
    simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hfg
  have hgh' : ((isomorphisms D').inverseImage F) (g ≫ h) := by
    simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hgh
  have hg' : ((isomorphisms D').inverseImage F) g := by
    change ((isomorphisms D').inverseImage F) (f ≫ g) at hfg'
    change ((isomorphisms D').inverseImage F) (g ≫ h) at hgh'
    change ((isomorphisms D').inverseImage F) g
    rw [MorphismProperty.inverseImage_iff, isomorphisms.iff] at hfg' hgh' ⊢
    have hfg'' : isomorphisms D' (F.map f ≫ F.map g) := by
      simpa [Functor.map_comp] using hfg'
    have hgh'' : isomorphisms D' (F.map g ≫ F.map h) := by
      simpa [Functor.map_comp] using hgh'
    exact (show IsIso (F.map g) from by
      simpa [isomorphisms.iff] using
        IsSaturatedMultiplicativeSystem.saturation (F.map f) (F.map g) (F.map h) hfg'' hgh'')
  simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using hg'

-- Proof sketch: transport the owner-level saturated multiplicative-system structure on
-- `F.kernel.trW` across the bridge to the source-facing inverse-image class.
/-- Lemma 13.5.4: if `F : D ⥤ D'` is an exact functor between pretriangulated categories, then
the morphisms `f` of `D` such that `F.map f` is an isomorphism form a saturated multiplicative
system. -/
theorem inverseImage_isomorphisms_of_exactFunctor_isSaturatedMultiplicativeSystem
    : IsSaturatedMultiplicativeSystem ((isomorphisms D').inverseImage F) := by
  simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F] using
    kernel_trW_of_exactFunctor_isSaturatedMultiplicativeSystem F

end ExactFunctor

end

end CategoryTheory

/-! ### Lemma_13_5_5 (from Chap13) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Abelian
open ComposableArrows
open ObjectProperty
open MorphismProperty
open Pretriangulated

section

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : D ⥤ A) [Functor.IsHomological H] [H.ShiftSequence ℤ]

local notation "S" => H.homologicalKernel.trW

/- Domain-style sampling for Lemma 13.5.5:
- primary domain: morphism properties attached to a homological functor on a pretriangulated
  category;
- inspected owner declarations:
  `Functor.mem_homologicalKernel_trW_iff`,
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.HasLeftCalculusOfFractions`,
  `MorphismProperty.HasRightCalculusOfFractions`,
  `IsSaturatedMultiplicativeSystem`;
- best owner abstraction: the canonical morphism property `H.homologicalKernel.trW`, together
  with the owner classes `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.IsMultiplicative`, and `IsSaturatedMultiplicativeSystem`;
- primitive-vs-derived split:
  primitive data: the homological functor `H`;
  derived API: the homological-kernel object property `H.homologicalKernel`, the canonical
  morphism property `H.homologicalKernel.trW`, the bridge
    `Functor.mem_homologicalKernel_trW_iff`, and the compatibility/multiplicativity/saturation
    results below.

Source/core/bridge triage:
- `source-facing`: the textbook class `S` of maps inducing isomorphisms on every shifted functor
  `H^i`;
- `core/canonical`: the owner `H.homologicalKernel.trW` together with the classes
  `MorphismProperty.IsMultiplicative`, `MorphismProperty.IsCompatibleWithTriangulation`, and
  `IsSaturatedMultiplicativeSystem`;
- `bridge/view`: `Functor.mem_homologicalKernel_trW_iff`, identifying the textbook description
  with the canonical owner.
-/

/- Companion recall: for a homological functor, the textbook class `S` of morphisms inducing
isomorphisms on all shifted values `H^i` is exactly the canonical morphism property
`H.homologicalKernel.trW`. -/
#check Functor.mem_homologicalKernel_trW_iff

/-- Helper for Lemma 13.5.5: the canonical textbook class of morphisms inverted by every shift of
`H` is multiplicative. -/
private instance homologicalKernel_trW_isMultiplicative :
    MorphismProperty.IsMultiplicative S where
  id_mem X := by
    -- Unpack membership in `S` into the shifted-isomorphism formulation.
    rw [H.mem_homologicalKernel_trW_iff]
    intro n
    simpa using (inferInstance : IsIso ((H.shift n).map (𝟙 X)))
  comp_mem f g hf hg := by
    -- Composition stays in `S` because every shifted image is a composition of isomorphisms.
    rw [H.mem_homologicalKernel_trW_iff] at hf hg ⊢
    intro n
    letI : IsIso ((H.shift n).map f) := hf n
    letI : IsIso ((H.shift n).map g) := hg n
    have : IsIso (((H.shift n).map f) ≫ (H.shift n).map g) := by infer_instance
    simpa [Functor.map_comp] using
      this

omit [H.ShiftSequence ℤ] in
/-- Helper for Lemma 13.5.5: if the first object of a distinguished triangle lies in the
homological kernel of `H`, then the second morphism belongs to `S`. -/
private theorem homologicalKernel_trW_of_second_morphism
    ⦃X Y Z : D⦄ ⦃f : X ⟶ Y⦄ ⦃g : Y ⟶ Z⦄ ⦃h : Z ⟶ X⟦(1 : ℤ)⟧⦄
    (hT : Triangle.mk f g h ∈ distTriang D) (hX : H.homologicalKernel X) :
    S g := by
  -- Rotate once so that `g` becomes the first morphism, and shift the kernel object accordingly.
  exact ⟨_, _, _, rot_of_distTriang _ hT, H.homologicalKernel.le_shift _ _ hX⟩

omit [Abelian A] [H.IsHomological] [H.ShiftSequence ℤ] in
/-- Helper for Lemma 13.5.5: if the third object of a distinguished triangle lies in the
homological kernel of `H`, then the first morphism belongs to `S`. -/
private theorem homologicalKernel_trW_of_first_morphism
    ⦃X Y Z : D⦄ ⦃f : X ⟶ Y⦄ ⦃g : Y ⟶ Z⦄ ⦃h : Z ⟶ X⟦(1 : ℤ)⟧⦄
    (hT : Triangle.mk f g h ∈ distTriang D) (hZ : H.homologicalKernel Z) :
    S f := by
  -- This is exactly the cone description of membership in `H.homologicalKernel.trW`.
  exact ⟨_, _, _, hT, hZ⟩

omit [H.ShiftSequence ℤ] in
/-- Helper for Lemma 13.5.5: left cancellation for `S` follows by factoring `f₁ - f₂` through the
cone of a denominator and then using the next map in the resulting distinguished triangle. -/
private theorem homologicalKernel_trW_ext_left
    ⦃X' X Y : D⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X)
    (hs : S s) (hsf : s ≫ f₁ = s ≫ f₂) :
    ∃ (Y' : D) (t : Y ⟶ Y'), S t ∧ f₁ ≫ t = f₂ ≫ t := by
  rcases hs with ⟨Z, g, h, Hs, hZ⟩
  -- Rewrite the equality as the vanishing of the difference to match exactness.
  have hsf' : s ≫ (f₁ - f₂) = 0 := by
    simpa using (sub_eq_zero.2 hsf : s ≫ f₁ - s ≫ f₂ = 0)
  -- Factor the difference through the cone object of `s`.
  obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ _ Hs _ hsf'
  obtain ⟨Y', r, t, hT⟩ := distinguished_cocone_triangle q
  refine ⟨Y', r, ?_, ?_⟩
  · exact homologicalKernel_trW_of_second_morphism (H := H) hT hZ
  · -- The factorization dies after postcomposing with the next triangle morphism.
    apply sub_eq_zero.1
    simpa using calc
      (f₁ - f₂) ≫ r = (g ≫ q) ≫ r := by
        simpa [Category.assoc] using congrArg (fun u ↦ u ≫ r) hq
      _ = 0 := by
        have hqr : q ≫ r = 0 := by
          simpa using comp_distTriang_mor_zero₁₂ _ hT
        have hgqr : g ≫ (q ≫ r) = g ≫ (0 : Z ⟶ Y') := congrArg (fun u ↦ g ≫ u) hqr
        have hg0 : g ≫ (0 : Z ⟶ Y') = 0 := by simp
        simpa [Category.assoc] using hgqr.trans hg0

omit [H.ShiftSequence ℤ] in
/-- Helper for Lemma 13.5.5: right cancellation for `S` is the dual cone argument, obtained from
the exactness of `Triangle.coyoneda`. -/
private theorem homologicalKernel_trW_ext_right
    ⦃X Y Y' : D⦄ (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y')
    (hs : S s) (hfs : f₁ ≫ s = f₂ ≫ s) :
    ∃ (X' : D) (t : X' ⟶ X), S t ∧ t ≫ f₁ = t ≫ f₂ := by
  rw [H.homologicalKernel.trW_iff'] at hs
  rcases hs with ⟨Z, g, h, Hs, hZ⟩
  -- Rewrite the equality as the vanishing of the difference to feed exactness.
  have hfs' : (f₁ - f₂) ≫ s = 0 := by
    simpa using (sub_eq_zero.2 hfs : f₁ ≫ s - f₂ ≫ s = 0)
  -- Factor the difference through the cone of `s` on the dual side.
  obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ Hs _ hfs'
  obtain ⟨X', t, r, hT⟩ := distinguished_cocone_triangle₁ q
  refine ⟨X', t, ?_, ?_⟩
  · exact homologicalKernel_trW_of_first_morphism (H := H) hT hZ
  · apply sub_eq_zero.1
    -- The factorization dies after precomposing with the previous triangle morphism.
    simpa using calc
      t ≫ (f₁ - f₂) = (t ≫ q) ≫ g := by
        simpa [Category.assoc] using congrArg (fun u ↦ t ≫ u) hq
      _ = 0 := by
        have htq : t ≫ q = 0 := by
          simpa using comp_distTriang_mor_zero₁₂ _ hT
        have htqg : (t ≫ q) ≫ g = 0 ≫ g := congrArg (fun u ↦ u ≫ g) htq
        have h0g : (0 : X' ⟶ Z) ≫ g = 0 := by simp
        simpa [Category.assoc] using htqg.trans h0g

/-- Helper for Lemma 13.5.5: the class `S` satisfies the triangulated compatibility axiom `MS6`
because the third vertical arrow in a morphism of distinguished triangles is an isomorphism on
every shifted value of `H` whenever the first two are. -/
instance :
    MorphismProperty.IsCompatibleWithTriangulation S := by
  refine
    { toIsCompatibleWithShift := inferInstance
      compatible_with_triangulation := ?_ }
  intro T₁ T₂ hT₁ hT₂ a b ha hb hab
  -- Complete the partial square to a morphism of distinguished triangles.
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b hab
  refine ⟨c, ?_, hc₂, hc₃⟩
  rw [H.mem_homologicalKernel_trW_iff] at ha hb ⊢
  intro n
  let φ : T₁ ⟶ T₂ :=
    { hom₁ := a
      hom₂ := b
      hom₃ := c
      comm₁ := hab
      comm₂ := hc₂
      comm₃ := hc₃ }
  let R₁ : ComposableArrows A 4 :=
    (H.homologySequenceComposableArrows₅ T₁ n (n + 1) rfl).δlast
  let R₂ : ComposableArrows A 4 :=
    (H.homologySequenceComposableArrows₅ T₂ n (n + 1) rfl).δlast
  let ψ₅ :
      H.homologySequenceComposableArrows₅ T₁ n (n + 1) rfl ⟶
        H.homologySequenceComposableArrows₅ T₂ n (n + 1) rfl :=
    homMk₅ ((H.shift n).map a) ((H.shift n).map b) ((H.shift n).map c)
      ((H.shift (n + 1)).map a) ((H.shift (n + 1)).map b) ((H.shift (n + 1)).map c)
      (by simpa [Functor.map_comp] using congrArg ((H.shift n).map) hab)
      (by simpa [Functor.map_comp] using congrArg ((H.shift n).map) hc₂)
      (by
        simpa using (H.homologySequenceδ_naturality T₁ T₂ φ n (n + 1) rfl).symm)
      (by simpa [Functor.map_comp] using congrArg ((H.shift (n + 1)).map) hab)
      (by simpa [Functor.map_comp] using congrArg ((H.shift (n + 1)).map) hc₂)
  let ψ : R₁ ⟶ R₂ :=
    δlastFunctor.map ψ₅
  have hR₁ : R₁.Exact := by
    simpa [R₁] using
      (H.homologySequenceComposableArrows₅_exact T₁ hT₁ n (n + 1) rfl).δlast
  have hR₂ : R₂.Exact := by
    simpa [R₂] using
      (H.homologySequenceComposableArrows₅_exact T₂ hT₂ n (n + 1) rfl).δlast
  -- The surrounding four vertical maps are isomorphisms, hence the middle one is too.
  letI : IsIso ((H.shift n).map a) := ha n
  letI : IsIso ((H.shift n).map b) := hb n
  letI : IsIso ((H.shift (n + 1)).map a) := ha (n + 1)
  letI : IsIso ((H.shift (n + 1)).map b) := hb (n + 1)
  have h₀ : Epi (app' ψ 0) := by
    simpa [ψ, ψ₅] using (show Epi ((H.shift n).map a) by infer_instance)
  have h₁ : IsIso (app' ψ 1) := by
    simpa [ψ, ψ₅] using (show IsIso ((H.shift n).map b) by infer_instance)
  have h₂ : IsIso (app' ψ 3) := by
    simpa [ψ, ψ₅] using (show IsIso ((H.shift (n + 1)).map a) by infer_instance)
  have h₃ : Mono (app' ψ 4) := by
    simpa [ψ, ψ₅] using (show Mono ((H.shift (n + 1)).map b) by infer_instance)
  have hψ :
      IsIso (app' ψ 2) :=
    isIso_of_epi_of_isIso_of_isIso_of_mono hR₁ hR₂ ψ h₀ h₁ h₂ h₃
  simpa [ψ, ψ₅] using hψ

/-- Lemma 13.5.5: the morphisms inverted by all shifted values of a homological functor form a
saturated multiplicative system compatible with the triangulated structure. -/
instance :
    IsSaturatedMultiplicativeSystem S := by
  -- Lemma 13.5.2 packages MS2 and MS3 from the two cancellation lemmas above.
  letI : MorphismProperty.HasLeftCalculusOfFractions S :=
    hasLeftCalculusOfFractions_of_ext_and_compatibleWithTriangulation S
      (homologicalKernel_trW_ext_left H)
  letI : MorphismProperty.HasRightCalculusOfFractions S :=
    hasRightCalculusOfFractions_of_ext_and_compatibleWithTriangulation S
      (homologicalKernel_trW_ext_right H)
  refine
    { toHasLeftCalculusOfFractions := inferInstance
      toHasRightCalculusOfFractions := inferInstance
      saturation := ?_ }
  intro X₀ X₁ X₂ X₃ f g h hfg hgh
  -- Saturation is checked after applying each shifted functor into the abelian target.
  rw [H.mem_homologicalKernel_trW_iff] at hfg hgh ⊢
  intro n
  have hfg' : isomorphisms A (((H.shift n).map f) ≫ (H.shift n).map g) := by
    simpa [Functor.map_comp, isomorphisms.iff] using hfg n
  have hgh' : isomorphisms A (((H.shift n).map g) ≫ (H.shift n).map h) := by
    simpa [Functor.map_comp, isomorphisms.iff] using hgh n
  simpa [isomorphisms.iff] using
    IsSaturatedMultiplicativeSystem.saturation
      ((H.shift n).map f) ((H.shift n).map g) ((H.shift n).map h) hfg' hgh'

end

end CategoryTheory

/-! ### Proposition_13_5_6 (from Chap13) -/
universe v u

namespace CategoryTheory

/- Domain-style sampling:
- primary domain: localization of pretriangulated and triangulated categories by a multiplicative
  system compatible with distinguished triangles;
- relevant upstream owner declarations in this domain:
  `MorphismProperty.commShift_Q`,
  `Triangulated.Localization.pretriangulated`,
  `Triangulated.Localization.isTriangulated_functor`,
  `Functor.distTriang_iff`;
- source/core/bridge triage:
  `source-facing`: the Verdier-localized category carries distinguished triangles coming from the
    essential image of distinguished triangles upstairs;
  `core/canonical`: the owner API in `CategoryTheory.Localization.Triangulated`;
  `bridge/view`: `Functor.distTriang_iff`, specialized downstream to the localization functor
    `W.Q`.

Primitive data is the localization functor `W.Q` together with the compatible-triangulation
hypothesis on `W`. The pretriangulated structure on `W.Localization`, exactness of `W.Q`, the
distinguished-triangle characterization, and the triangulated structure under `[IsTriangulated D]`
are all derived owner API, so this file should stay at direct canonical recall/use.
-/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

variable (W : MorphismProperty D) [W.HasLeftCalculusOfFractions] [W.IsCompatibleWithTriangulation]

/- Companion recall: the localization functor `W.Q` commutes with the shift by `ℤ` via the
canonical instance `MorphismProperty.commShift_Q`. -/
recall MorphismProperty.commShift_Q

/- Proposition 13.5.6: if `D` is pretriangulated and `W` is a multiplicative system compatible
with the triangulated structure, then the localized category `W.Localization` carries the
canonical pretriangulated structure `Triangulated.Localization.pretriangulated`. The companion
recalls below record that `W.Q` commutes with shift, is exact, and that `W.Localization` is
triangulated whenever `D` is triangulated. -/
recall Triangulated.Localization.pretriangulated

/- Companion recall: with the canonical pretriangulated structure on `W.Localization`, the
localization functor `W.Q` is triangulated, i.e. exact. -/
recall Triangulated.Localization.isTriangulated_functor

/- Companion recall: with the canonical pretriangulated structure on `W.Localization`, a triangle
is distinguished exactly when it lies in the essential image of distinguished triangles of `D`
under `W.Q`. -/
recall Functor.distTriang_iff

variable [IsTriangulated D]

/- Companion recall: if the source category `D` is triangulated, then the localized category
`W.Localization` is triangulated. -/
recall Triangulated.Localization.isTriangulated

end CategoryTheory

/-! ### Lemma_13_5_7 (from Chap13) -/
open CategoryTheory

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (S : MorphismProperty D) [S.HasLeftCalculusOfFractions] [S.IsCompatibleWithTriangulation]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable {D' : Type u₃} [Category.{v₃} D'] [Limits.HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/- Domain-style sampling:
- primary domain: localization of pretriangulated categories and induced homological/triangulated
  structures on localized factorizations;
- inspected owner declarations:
  `Localization.lift`,
  `Localization.fac`,
  `Functor.isHomological_of_localization`,
  `Functor.commShiftOfLocalization`,
  `Functor.isTriangulated_of_precomp_iso`;
- source/core/bridge triage:
  `source-facing`: the two statements of Lemma 13.5.7 about the canonical factorization through
    `S.Q`;
  `core/canonical`: the localization lift `Localization.lift ... S.Q` and the induced
    homological/triangulated owner theorems in mathlib;
  `bridge/view`: the canonical factorization isomorphism `Localization.fac ... S.Q`.

Primitive data here is just the localization functor `S.Q`, a functor that inverts `S`, and the
canonical comparison isomorphism of its factorization. Homologicality, shift-commutation of the
lift, and triangulatedness are all derived owner API and should be reused directly.
-/

-- Proof sketch: equip `S.Localization` with the pretriangulated structure of Proposition 13.5.6
-- so that `S.Q` is triangulated. Then use `Localization.essSurj_mapArrow S.Q S` together with the
-- factorization isomorphism `Localization.fac H hH S.Q` and
-- apply `Functor.isHomological_of_localization`.
/-- Lemma 13.5.7 (1): if `H : D ⥤ A` is a homological functor that inverts every morphism of the
multiplicative system `S`, then its canonical factorization through the localization functor
`S.Q : D ⥤ S.Localization` is homological as well. -/
theorem homological_factorization_isHomological
    (H : D ⥤ A) [H.IsHomological] (hH : S.IsInvertedBy H) :
    (Localization.lift H hH S.Q).IsHomological := by
  letI : Functor.EssSurj ((S.Q).mapArrow) := Localization.essSurj_mapArrow S.Q S
  exact Functor.isHomological_of_localization S.Q (Localization.lift H hH S.Q) H
    (Localization.fac H hH S.Q)

-- The induced shift-commuting structure on a localization lift is the canonical owner instance
-- `Functor.commShiftOfLocalization`, specialized to the factorization through `S.Q`.
noncomputable instance (F : D ⥤ D') [F.CommShift ℤ] (hF : S.IsInvertedBy F) :
    (Localization.lift F hF S.Q).CommShift ℤ :=
  Functor.commShiftOfLocalization S.Q S ℤ F (Localization.lift F hF S.Q)

-- Proof sketch: endow the localized factorization `F' := Localization.lift F hF S.Q` with the
-- canonical shift-commuting structure `Functor.commShiftOfLocalization S.Q S ℤ F F'`. The
-- canonical lifting isomorphism `Localization.Lifting.iso S.Q S F (Localization.lift F hF S.Q)`
-- is compatible with shifts, and
-- `Localization.essSurj_mapArrow S.Q S` makes `S.Q` essentially surjective on arrows; then apply
-- `Functor.isTriangulated_of_precomp_iso`.
/-- Lemma 13.5.7 (2): if `F : D ⥤ D'` is an exact functor between pretriangulated categories that
inverts every morphism of the multiplicative system `S`, then its canonical factorization through
`S.Q : D ⥤ S.Localization` is exact too; in Lean, exactness is encoded by the induced
shift-commuting structure together with `Functor.IsTriangulated`. -/
theorem exact_factorization_isTriangulated
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (hF : S.IsInvertedBy F) :
    (Localization.lift F hF S.Q).IsTriangulated := by
  letI : (Localization.lift F hF S.Q).CommShift ℤ := inferInstance
  letI : Functor.EssSurj ((S.Q).mapArrow) := Localization.essSurj_mapArrow S.Q S
  exact Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso S.Q S F (Localization.lift F hF S.Q))

end

end CategoryTheory

/-! ### Lemma_13_5_8 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Localization
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory

section

/- 
Domain-style sampling:
- primary domain: morphisms of localizers and the induced functors between localization categories;
- relevant owner declarations inspected upstream:
  `Localization.LocalizerMorphism`,
  `LocalizerMorphism.localizedFunctor`,
  `LocalizerMorphism.IsLocalizedEquivalence`,
  `ObjectProperty.FullSubcategory`.

Source/core/bridge triage:
- `source-facing`: the restricted system on `P.FullSubcategory` and the hypothesis that every
  object of `D` is reached from `P.FullSubcategory` by a morphism of `S`;
- `core/canonical`: `LocalizerMorphism`, `localizedFunctor`, and
  `LocalizerMorphism.IsLocalizedEquivalence`;
- `bridge/view`: the inclusion-induced localizer morphism
  `fullSubcategoryLocalizerMorphism` and its induced localization functor
  `fullSubcategoryLocalizationFunctor`.

Primitive data here are the object property `P`, the morphism property `S`, and the inclusion
`P.ι : P.FullSubcategory ⥤ D`. The localized comparison functor and its equivalence property are
derived from the canonical localizer-morphism owner, so the public equivalence statements should
stay at that plain localizer layer. Triangulated compatibility is additional structure used only by
the companion `CommShift` and `IsTriangulated` instances below.
-/

section Localizer

variable {D : Type u} [Category.{v} D]
variable (P : ObjectProperty D)
variable (S : MorphismProperty D)

/-- The multiplicative system on `P.FullSubcategory` obtained by restricting `S` along the
inclusion `P.ι : P.FullSubcategory ⥤ D`. -/
abbrev fullSubcategoryLocalizationSystem : MorphismProperty P.FullSubcategory :=
  S.inverseImage P.ι

/-- Helper for Lemma 13.5.8: the restricted system admits right fractions once every ambient
auxiliary object can be refined back into the full subcategory by a morphism of `S`. -/
theorem fullSubcategoryLocalizationSystem_hasRightCalculusOfFractions_of_cover
    [IsSaturatedMultiplicativeSystem S] :
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) →
    HasRightCalculusOfFractions (fullSubcategoryLocalizationSystem P S) := by
  intro hP
  refine
    { toIsMultiplicative := inferInstance
      exists_rightFraction := ?_
      ext := ?_ }
  · intro X Y φ
    -- Start from the ambient right-fraction witness and then refine its source back into `P`.
    obtain ⟨ψ, hψ⟩ :=
      (LeftFraction.mk φ.f.hom φ.s.hom
        (by simpa [fullSubcategoryLocalizationSystem] using φ.hs)).exists_rightFraction
    obtain ⟨Z, u, hu⟩ := hP ψ.X'
    refine
      ⟨RightFraction.mk (ObjectProperty.homMk (u ≫ ψ.s))
        (by
          simpa [fullSubcategoryLocalizationSystem] using S.comp_mem _ _ hu ψ.hs)
        (ObjectProperty.homMk (u ≫ ψ.f)), ?_⟩
    -- Forgetting to `D`, this is exactly the ambient compatibility square precomposed with `u`.
    apply P.ι.map_injective
    simpa [Category.assoc] using congrArg (fun k ↦ u ≫ k) hψ
  · intro X Y Y' f₁ f₂ s hs hfs
    -- Apply ambient right-cancellation and then refine the new source back into `P`.
    obtain ⟨X', t, ht, hfac⟩ :=
      HasRightCalculusOfFractions.ext f₁.hom f₂.hom s.hom
        (by simpa [fullSubcategoryLocalizationSystem] using hs)
        (by simpa using congrArg (fun k ↦ k.hom) hfs)
    obtain ⟨Z, u, hu⟩ := hP X'
    refine ⟨Z, ObjectProperty.homMk (u ≫ t), ?_, ?_⟩
    · simpa [fullSubcategoryLocalizationSystem] using S.comp_mem _ _ hu ht
    · apply P.ι.map_injective
      simpa [Category.assoc] using congrArg (fun k ↦ u ≫ k) hfac

/-- Helper for Lemma 13.5.8: the restricted arrows are exactly the arrows of the full subcategory
whose image in the ambient localization becomes an isomorphism. -/
theorem fullSubcategoryLocalizationSystem_eq_inverseImage_isomorphisms_of_localized_inclusion
    [IsSaturatedMultiplicativeSystem S] :
    fullSubcategoryLocalizationSystem P S =
      (isomorphisms S.Localization).inverseImage (P.ι ⋙ S.Q) := by
  ext X Y f
  constructor
  · intro hf
    -- Any restricted denominator is inverted by the ambient localization functor.
    simpa [fullSubcategoryLocalizationSystem] using
      (Localization.inverts S.Q S f.hom (by simpa [fullSubcategoryLocalizationSystem] using hf))
  · intro hf
    -- Conversely, saturation identifies the inverse-image isomorphisms with `S` itself.
    have hsat :
        S.saturatedClosure (P.ι.map f) := by
      simpa [MorphismProperty.saturatedClosure] using hf
    exact (MorphismProperty.saturatedClosure_le S le_rfl) _ hsat

/-- The localizer morphism induced by the inclusion `P.FullSubcategory ⥤ D`. -/
abbrev fullSubcategoryLocalizerMorphism :
    LocalizerMorphism (fullSubcategoryLocalizationSystem P S) S :=
  LocalizerMorphism.ofEq rfl

/-- The functor on localizations induced by the inclusion `P.FullSubcategory ⥤ D`. -/
noncomputable abbrev fullSubcategoryLocalizationFunctor :
    (fullSubcategoryLocalizationSystem P S).Localization ⥤ S.Localization :=
  (fullSubcategoryLocalizerMorphism P S).localizedFunctor
    (fullSubcategoryLocalizationSystem P S).Q S.Q

/-- Helper for Lemma 13.5.8: the localized inclusion is essentially surjective once every
ambient object is covered by an `S`-morphism from the full subcategory. -/
theorem fullSubcategoryLocalizationFunctor_essSurj
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) :
    (fullSubcategoryLocalizationFunctor P S).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  let X := S.Q.objPreimage Y
  -- Choose an `S`-cover of a representative of `Y`.
  obtain ⟨X', s, hs⟩ := hP X
  refine ⟨(fullSubcategoryLocalizationSystem P S).Q.obj X', ⟨?_⟩⟩
  -- Compare the two localization functors through the canonical comparison square,
  -- then invert the chosen denominator and the ambient essential-surjectivity isomorphism.
  let e₁ :
      (fullSubcategoryLocalizationFunctor P S).obj
          ((fullSubcategoryLocalizationSystem P S).Q.obj X') ≅
        S.Q.obj (P.ι.obj X') :=
    (((fullSubcategoryLocalizerMorphism P S).catCommSq
      (fullSubcategoryLocalizationSystem P S).Q S.Q).iso.app X').symm
  let e₂ : S.Q.obj (P.ι.obj X') ≅ S.Q.obj X := by
    letI := Localization.inverts S.Q S _ hs
    exact asIso (S.Q.map s)
  let e₃ : S.Q.obj X ≅ Y := S.Q.objObjPreimageIso Y
  exact e₁ ≪≫ e₂ ≪≫ e₃

/- The remaining source-faithful step is the Hom-colimit comparison: use
`right_localization_hom_colimit` for the restricted and ambient systems, compare the diagrams via
the denominator-refinement functor, and then invoke finality on the opposite denominator
categories. -/
/-- Helper for Lemma 13.5.8: after comparing the two right-fraction Hom colimits along the
denominator-refinement functor, the localized inclusion is fully faithful. -/
-- TODO: the remaining blocker is to package the diagram-level natural isomorphism between the
-- restricted Hom diagram and the ambient Hom diagram precomposed with the opposite
-- denominator-refinement functor, and then identify the induced map on colimits with
-- `fullSubcategoryLocalizationFunctor P S`. The right-fraction comparison infrastructure is now
-- in place, but the final colimit-level identification still needs a dedicated adapter lemma.
noncomputable def fullSubcategoryLocalizationFunctor_fullyFaithful
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) :
    (fullSubcategoryLocalizationFunctor P S).FullyFaithful := sorry

-- Proof sketch: the composite `P.ι ⋙ S.Q` inverts exactly the restricted system
-- `S.inverseImage P.ι`, so the induced functor on localizations is the canonical comparison
-- functor. The hypothesis gives essential surjectivity after localization because every object of
-- `D` is reached from an object of `P.FullSubcategory` by a morphism of `S`. For full faithfulness,
-- use the colimit description of morphisms in a right-fraction localization and refine every
-- denominator in `S` to one whose source lies in `P.FullSubcategory`.
/-- The owner-level localizer-morphism formulation of Lemma 13.5.8. -/
theorem fullSubcategoryLocalizerMorphism_isLocalizedEquivalence
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) :
    (fullSubcategoryLocalizerMorphism P S).IsLocalizedEquivalence := by
  -- Route correction: finish on the source proof’s denominator-colimit route, using the
  -- structural full-faithfulness helper rather than the discarded unrestricted saturation route.
  letI : (fullSubcategoryLocalizationFunctor P S).Full :=
    (fullSubcategoryLocalizationFunctor_fullyFaithful (P := P) (S := S) hP).full
  letI : (fullSubcategoryLocalizationFunctor P S).Faithful :=
    (fullSubcategoryLocalizationFunctor_fullyFaithful (P := P) (S := S) hP).faithful
  letI : (fullSubcategoryLocalizationFunctor P S).EssSurj :=
    fullSubcategoryLocalizationFunctor_essSurj P S hP
  letI : (fullSubcategoryLocalizationFunctor P S).IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact LocalizerMorphism.IsLocalizedEquivalence.mk'
    (fullSubcategoryLocalizerMorphism P S)
    (fullSubcategoryLocalizationSystem P S).Q S.Q
    (fullSubcategoryLocalizationFunctor P S)

/-- Lemma 13.5.8: let `D` be a category, let `P.FullSubcategory ⊆ D` be a full subcategory, and
let `S` be a saturated multiplicative system. If every object of `D` receives a morphism in `S`
from an object of `P.FullSubcategory`, then the induced functor
`(S.inverseImage P.ι)⁻¹(P.FullSubcategory) ⥤ S⁻¹D` is an equivalence. -/
theorem fullSubcategoryLocalization_inclusion_isEquivalence
    [IsSaturatedMultiplicativeSystem S]
    (hP :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s) :
    Functor.IsEquivalence (fullSubcategoryLocalizationFunctor P S) := by
  letI := fullSubcategoryLocalizerMorphism_isLocalizedEquivalence P S hP
  change
    ((fullSubcategoryLocalizerMorphism P S).localizedFunctor
      (fullSubcategoryLocalizationSystem P S).Q S.Q).IsEquivalence
  infer_instance

end Localizer

section Triangulated

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (P : ObjectProperty D) [P.IsTriangulated]
variable (S : MorphismProperty D) [IsSaturatedMultiplicativeSystem S]
  [S.IsCompatibleWithTriangulation]

/-- The restriction of a triangulation-compatible multiplicative system to a full
pretriangulated subcategory remains compatible with the triangulated structure. -/
-- TODO: the remaining blocker is to transport the ambient triangle-completion axiom along `P.ι`
-- and use `P.ι.commShiftIso_hom_naturality` to rewrite the shifted third-edge equation back in
-- the full subcategory.
instance fullSubcategoryLocalizationSystem_isCompatibleWithTriangulation :
    (fullSubcategoryLocalizationSystem P S).IsCompatibleWithTriangulation := sorry

local instance fullSubcategoryLocalizerMorphism_commShift :
    (fullSubcategoryLocalizerMorphism P S).functor.CommShift ℤ := by
  change P.ι.CommShift ℤ
  infer_instance

local instance fullSubcategoryLocalizationFunctor_commShift :
    (fullSubcategoryLocalizationFunctor P S).CommShift ℤ :=
  (fullSubcategoryLocalizerMorphism P S).commShift ℤ
    (fullSubcategoryLocalizationSystem P S).Q S.Q
    (fullSubcategoryLocalizationFunctor P S)
    (Localization.fac
      (P.ι ⋙ S.Q)
      ((fullSubcategoryLocalizerMorphism P S).inverts S.Q)
      (fullSubcategoryLocalizationSystem P S).Q).symm

/-- The localized inclusion functor is exact for the canonical pretriangulated structures on the
source and target localizations; its `CommShift ℤ` structure is inherited from the generic
`LocalizerMorphism.localizedFunctor` instance. -/
noncomputable instance [HasLeftCalculusOfFractions (fullSubcategoryLocalizationSystem P S)] :
    (fullSubcategoryLocalizationFunctor P S).IsTriangulated := by
  -- Route correction: exactness of the localized inclusion only needs the restricted system
  -- to admit left fractions, not the stronger unrestricted saturation helper above.
  let F : P.FullSubcategory ⥤ S.Localization := P.ι ⋙ S.Q
  have hF : (fullSubcategoryLocalizationSystem P S).IsInvertedBy F := by
    intro X Y f hf
    exact Localization.inverts S.Q S _ hf
  -- Apply the generic exact-factorization theorem to the composite `P.ι ⋙ S.Q`.
  simpa [F, fullSubcategoryLocalizationFunctor] using
    (exact_factorization_isTriangulated
      (S := fullSubcategoryLocalizationSystem P S) (F := F) hF)

end Triangulated

end

end CategoryTheory

/-! ### Lemma_13_5_9 (from Chap13) -/
open CategoryTheory.Limits
open CategoryTheory
open MorphismProperty
open Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (S : MorphismProperty D) [S.IsCompatibleWithTriangulation] (Z : D)

/- Domain-style sampling:
- primary domain: localization of a pretriangulated category at a morphism property compatible with
  distinguished triangles;
- sampled owner declarations:
  `localization_object_isZero_tfae`,
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.IsSaturatedMultiplicativeSystem`,
  `CategoryTheory.Retract`,
  `binaryBiproductTriangle_distinguished`;
- best owner abstraction: the canonical localization functor `S.Q`, with primitive zero-object
  data recorded by `IsZero (S.Q.obj Z)` and the Chapter 12 owner theorem
  `localization_object_isZero_tfae`; the direct-summand clause is most canonically expressed by
  the retract owner `Retract` rather than by equality with a chosen biproduct model;
- primitive data: the morphism property `S`, the object `Z`, and the relevant localization owner
  instances;
- derived API: the triangulated and saturated refinements that add the distinguished-triangle
  formulations, best stated through the owner objects `Triangle D` and `Retract` rather than by
  primitive biproduct-coordinate data.

Source/core/bridge triage:
- `source-facing`: Lemma 13.5.9, which adds the triangulated direct-summand and distinguished-triangle
  formulations to the zero-object criterion;
- `core/canonical`: the localization owner `S.Q`, the zero-object criterion
  `localization_object_isZero_tfae`, and the saturation owner
  `MorphismProperty.IsSaturatedMultiplicativeSystem`;
- `bridge/view`: the passage between zero morphisms in `S` and distinguished triangles, expressed
  through `Triangle D`, `Retract`, and `binaryBiproductTriangle_distinguished` together with
  `S.compatible_with_triangulation`.
-/

-- Proof sketch: combine the additive-localization criterion `localization_object_isZero_tfae`
-- for clauses `(1)`–`(3)` with the pretriangulated binary-biproduct triangle
-- `binaryBiproductTriangle_distinguished`, the retract/direct-summand owner `Retract`, and the
-- compatibility axiom for `S` to pass between a zero morphism in `S` and a distinguished triangle
-- whose third object has `Z` as a direct summand and whose first morphism lies in `S`.
/-- Lemma 13.5.9: for a pretriangulated category `D`, a multiplicative system `S` compatible with
the triangulated structure, and an object `Z` of `D`, the following are equivalent: `S.Q.obj Z`
is zero; some zero morphism `0 : Z ⟶ Z'` lies in `S`; some zero morphism `0 : Z' ⟶ Z` lies in
`S`; and `Z` is a retract, hence a direct summand, of the third term of a distinguished triangle
whose first morphism lies in `S`. -/
theorem localization_object_isZero_tfae_of_compatibleWithTriangulation
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions] :
    List.TFAE
      [ IsZero (S.Q.obj Z)
      , ∃ Z' : D, S (0 : Z ⟶ Z')
      , ∃ Z' : D, S (0 : Z' ⟶ Z)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
      ] := sorry

-- Proof sketch: under saturation, Lemma `4.27.21` identifies `S` with the inverse image of the
-- isomorphisms under `S.Q`; hence the maps `0 ⟶ Z` and `Z ⟶ 0` lie in `S` exactly when
-- `S.Q.obj Z` is zero. The triangle `(0, Z, Z, 0, 𝟙 Z, 0)` is distinguished, so these zero-object
-- conditions are equivalent to the existence of a distinguished triangle with third vertex `Z`
-- whose first morphism lies in `S`.
/-- If `S` is saturated, the preceding zero-object criterion is also equivalent to the canonical
zero morphisms `0 ⟶ Z` and `Z ⟶ 0` lying in `S`, and to the existence of a distinguished triangle
with third vertex exactly `Z` whose first morphism belongs to `S`. -/
theorem localization_object_isZero_tfae_of_saturated_compatibleWithTriangulation
    [IsSaturatedMultiplicativeSystem S] :
    List.TFAE
      [ IsZero (S.Q.obj Z)
      , ∃ Z' : D, S (0 : Z ⟶ Z')
      , ∃ Z' : D, S (0 : Z' ⟶ Z)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
      , S (0 : 0 ⟶ Z)
      , S (0 : Z ⟶ 0)
      , ∃ T : Triangle D, T ∈ distTriang D ∧ S T.mor₁ ∧ T.obj₃ = Z
      ] := sorry

end

end CategoryTheory
