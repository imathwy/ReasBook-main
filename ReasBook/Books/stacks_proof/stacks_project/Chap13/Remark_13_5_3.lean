import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 0H30]
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
