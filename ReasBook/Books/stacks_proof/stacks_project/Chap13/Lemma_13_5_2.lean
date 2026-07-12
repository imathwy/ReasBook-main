import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Remark_13_5_3

-- Declarations for this item will be appended below by the statement pipeline.

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
    dsimp [U₁, U₂] at c hc₁ hc₂
    simp only [Category.assoc] at hc₂
    refine ⟨c.op, hc, Quiver.Hom.unop_inj hc₁.symm, Quiver.Hom.unop_inj ?_⟩
    -- Transport the shifted third-map equality back across the opposite-shift equivalence.
    apply (shiftFunctor D (1 : ℤ)).map_injective
    let e₁ := ((opShiftFunctorEquivalence D 1).unitIso.inv.app T₁.obj₁).unop
    let e₂ := ((opShiftFunctorEquivalence D 1).unitIso.inv.app T₂.obj₁).unop
    let e₂' := ((opShiftFunctorEquivalence D 1).unitIso.hom.app T₂.obj₁).unop
    have hnat :
        e₂ ≫
            (shiftFunctor D (1 : ℤ)).map ((shiftFunctor Dᵒᵖ (1 : ℤ)).map a).unop =
          a.unop ≫ e₁ := by
      simpa using congrArg Quiver.Hom.unop
        (Pretriangulated.opShiftFunctorEquivalence_unitIso_inv_naturality
          (C := D) (n := (1 : ℤ)) a)
    have hright :
        e₂ ≫ ((shiftFunctor D (1 : ℤ)).map T₂.mor₃.unop ≫ (shiftFunctor D (1 : ℤ)).map c) =
          a.unop ≫ e₁ ≫ (shiftFunctor D (1 : ℤ)).map T₁.mor₃.unop := by
      refine (cancel_epi e₂').1 ?_
      simpa [e₁, e₂, e₂', Category.assoc] using hc₂
    have hleft :
        e₂ ≫
            ((shiftFunctor D (1 : ℤ)).map ((shiftFunctor Dᵒᵖ (1 : ℤ)).map a).unop ≫
              (shiftFunctor D (1 : ℤ)).map T₁.mor₃.unop) =
          a.unop ≫ e₁ ≫ (shiftFunctor D (1 : ℤ)).map T₁.mor₃.unop := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ (shiftFunctor D (1 : ℤ)).map T₁.mor₃.unop) hnat
    have hinv :
        e₂ ≫
            ((shiftFunctor D (1 : ℤ)).map ((shiftFunctor Dᵒᵖ (1 : ℤ)).map a).unop ≫
              (shiftFunctor D (1 : ℤ)).map T₁.mor₃.unop) =
          e₂ ≫ ((shiftFunctor D (1 : ℤ)).map T₂.mor₃.unop ≫ (shiftFunctor D (1 : ℤ)).map c) := by
      exact hleft.trans hright.symm
    have hfinal :
        (shiftFunctor D (1 : ℤ)).map ((shiftFunctor Dᵒᵖ (1 : ℤ)).map a).unop ≫
            (shiftFunctor D (1 : ℤ)).map T₁.mor₃.unop =
          (shiftFunctor D (1 : ℤ)).map T₂.mor₃.unop ≫ (shiftFunctor D (1 : ℤ)).map c := by
      exact (cancel_epi e₂).1 (by simpa [Category.assoc] using hinv)
    rw [unop_comp, unop_comp, Functor.map_comp, Functor.map_comp, Quiver.Hom.unop_op]
    exact hfinal

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
@[stacks 05R3]
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
@[stacks 05R3]
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
