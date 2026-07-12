import Mathlib
import StacksProject_2024.Chap13.Proposition_13_4_23
import StacksProject_2024.Chap13.Definition_13_3_4
import StacksProject_2024.Chap13.Lemma_13_35_1
import StacksProject_2024.Chap13.Definition_13_40_1
import StacksProject_2024.Chap13.Lemma_13_40_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits ZeroObject Pretriangulated
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 13.40.6:
- primary domain: triangulated closure of extension products of object properties in a
  triangulated category;
- sampled core/canonical declarations:
  `ObjectProperty.extensionProduct`,
  `ObjectProperty.leftOrthogonal`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsClosedUnderBinaryCoproducts`;
- best owner abstraction: the source-facing object property `(^⊥A) ⋆ A`, owned canonically by
  `ObjectProperty.extensionProduct`, whose three distinguished-triangle closure clauses are
  organized by the owner predicate `.IsTriangulated`, while clause `(4)` is the generic
  `ObjectProperty.IsClosedUnderBinaryCoproducts` consequence of a triangulated object property in a
  preadditive ambient category;
- primitive data: the object property `A`, its canonical left orthogonal `^⊥A`, and their
  canonical extension product `(^⊥A) ⋆ A`;
- derived API: the clausewise closure predicates
  `((^⊥A) ⋆ A).IsTriangulatedClosed₁`,
  `((^⊥A) ⋆ A).IsTriangulatedClosed₂`, and
  `((^⊥A) ⋆ A).IsTriangulatedClosed₃`;
  clause `(4)` is the derived binary-coproduct closure of the same owner.

Source/core/bridge triage:
- `source-facing`: Lemma `13.40.6` asserts that `(^⊥A) ⋆ A` is closed under the three
  distinguished-triangle clauses and under binary direct sums;
- `core/canonical`: the owner declarations `extensionProduct`, `leftOrthogonal`, and
  `IsTriangulated`;
- `bridge/view`: the clausewise `IsTriangulatedClosed₁/₂/₃` consequences obtained by inference
  from the main triangulated owner instance, together with the generic binary-coproduct closure
  instance reused for clause `(4)`.

This file should therefore keep the owner-level triangulated instance as the main declaration and
demote the individual closure clauses to companion recalls, mirroring Lemma `13.40.5` on the dual
side. -/

section Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

/-- Helper for Lemma 13.40.6: a morphism of distinguished triangles whose first two components are
isomorphisms also identifies the third components up to isomorphism. -/
lemma third_obj_iso_of_distinguished_triangle_morphism
    {T₁ T₂ : Triangle D} (hT₁ : T₁ ∈ distTriang D) (hT₂ : T₂ ∈ distTriang D)
    (e₁ : T₁.obj₁ ≅ T₂.obj₁) (e₂ : T₁.obj₂ ≅ T₂.obj₂)
    (hcomm : T₁.mor₁ ≫ e₂.hom = e₁.hom ≫ T₂.mor₁) :
    Nonempty (T₁.obj₃ ≅ T₂.obj₃) := by
  classical
  let c :=
    Classical.choose
      (complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ e₁.hom e₂.hom hcomm)
  have hc₂ : T₁.mor₂ ≫ c = e₂.hom ≫ T₂.mor₂ := by
    exact (Classical.choose_spec
      (complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ e₁.hom e₂.hom hcomm)).1
  have hc₃ : T₁.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
    exact (Classical.choose_spec
      (complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ e₁.hom e₂.hom hcomm)).2
  let φ : T₁ ⟶ T₂ := Triangle.homMk _ _ e₁.hom e₂.hom c hcomm hc₂ hc₃
  have hIso₃ : IsIso c := by
    simpa [φ] using
      (Pretriangulated.isIso₃_of_isIso₁₂ φ hT₁ hT₂
        (by infer_instance : IsIso e₁.hom) (by infer_instance : IsIso e₂.hom))
  letI : IsIso c := hIso₃
  exact ⟨⟨c, inv c, by simp, by simp⟩⟩

-- Proof sketch: a witness triangle `K₀ ⟶ X ⟶ A₀ ⟶ K₀⟦1⟧` with `K₀ ∈ ^⊥A`
-- identifies the second map as `A`-local via Lemma `13.40.3`.
/-- Helper for Lemma 13.40.6: in a witness triangle for `(^⊥A) ⋆ A`, the second morphism is
`A`-local as soon as the first vertex lies in `^⊥A`. -/
lemma extension_witness_second_map_is_local
    {X K₀ A₀ : D} {a : K₀ ⟶ X} {b : X ⟶ A₀} {c : A₀ ⟶ K₀⟦(1 : ℤ)⟧}
    (hT : Triangle.mk a b c ∈ distTriang D) (hK₀ : ^⊥A K₀) :
    A.isLocal b := by
  -- Proof comment: Lemma 13.40.3 is exactly the bridge from left orthogonality of the first
  -- vertex to locality of the second morphism.
  exact (leftOrthogonal_obj₁_iff_isLocal_mor₂ (A := A) (Triangle.mk a b c) hT).1 hK₀

/-- Helper for Lemma 13.40.6: if the last two vertices of a distinguished triangle belong to
`(^⊥A) ⋆ A`, then so does the first vertex. -/
lemma leftOrthogonal_extensionProduct_closed₁_of_distTriang
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₂ : ((^⊥A) ⋆ A) T.obj₂) (h₃ : ((^⊥A) ⋆ A) T.obj₃) :
    ((^⊥A) ⋆ A) T.obj₁ := by
  classical
  rw [extensionProduct_iff] at h₂ h₃
  rcases h₂ with ⟨K₁, A₁, a₁, b₁, c₁, hT₁, hK₁, hA₁⟩
  rcases h₃ with ⟨K₂, A₂, a₂, b₂, c₂, hT₂, hK₂, hA₂⟩
  have hlocal₁ : A.isLocal b₁ := by
    -- Proof comment: the left-orthogonal term in the first witness is what makes the square
    -- extendable on the `A`-side.
    exact extension_witness_second_map_is_local (A := A) hT₁ hK₁
  obtain ⟨v, hv⟩ := (hlocal₁ A₂ hA₂).2 (T.mor₂ ≫ b₂)
  let sq : CommSq b₁ T.mor₂ v b₂ := CommSq.mk hv
  obtain ⟨E⟩ := commSq_has_distinguished_three_by_three_extension sq
  have hA₃ : A.isoClosure E.middleColumn.obj₃ := by
    -- Proof comment: the middle column is a distinguished triangle whose first two vertices lie
    -- in `A`, so the third vertex stays in the iso-closure of `A`.
    exact A.ext_of_isTriangulatedClosed₃'
      E.middleColumn E.middleColumn_mem_distTriang hA₁ hA₂
  have etop : E.topRow.obj₃ ≅ (K₁⟦(1 : ℤ)⟧) := by
    -- Proof comment: the top row is another distinguished triangle with the same first two
    -- vertices and first morphism as the rotated first witness.
    exact Classical.choice <|
      third_obj_iso_of_distinguished_triangle_morphism
        (T₁ := E.topRow) (T₂ := (Triangle.mk a₁ b₁ c₁).rotate)
        E.topRow_mem_distTriang (rot_of_distTriang _ hT₁)
        (Iso.refl _) (Iso.refl _) (by simp)
  have emiddle : E.middleRow.obj₃ ≅ (K₂⟦(1 : ℤ)⟧) := by
    -- Proof comment: the middle row is similarly identified with the rotated second witness.
    exact Classical.choice <|
      third_obj_iso_of_distinguished_triangle_morphism
        (T₁ := E.middleRow) (T₂ := (Triangle.mk a₂ b₂ c₂).rotate)
        E.middleRow_mem_distTriang (rot_of_distTriang _ hT₂)
        (Iso.refl _) (Iso.refl _) (by simp)
  have hK₁_top : ^⊥A E.topRow.obj₃ := by
    exact (^⊥A).prop_of_iso etop.symm (by simpa using ((^⊥A).le_shift 1 _ hK₁))
  have hK₂_middle : ^⊥A E.middleRow.obj₃ := by
    exact (^⊥A).prop_of_iso emiddle.symm (by simpa using ((^⊥A).le_shift 1 _ hK₂))
  have hK₃_shift : ^⊥A E.rightColumn.obj₃ := by
    -- Proof comment: the right column is built from the rotated witness cones, so its third
    -- vertex remains in `^⊥A`.
    exact (^⊥A).ext_of_isTriangulatedClosed₃
      E.rightColumn E.rightColumn_mem_distTriang hK₁_top hK₂_middle
  have hleft_shift : ((^⊥A) ⋆ A) E.leftColumn.obj₃ := by
    -- Proof comment: inverse-rotating the bottom row presents the left-column cone as an
    -- extension of a shifted `^⊥A`-object by an `A`-object.
    rw [← extensionProduct_isoClosure_right]
    rw [extensionProduct_iff]
    exact ⟨E.bottomRow.invRotate.obj₁, E.bottomRow.invRotate.obj₃,
      E.bottomRow.invRotate.mor₁, E.bottomRow.invRotate.mor₂, E.bottomRow.invRotate.mor₃,
      inv_rot_of_distTriang _ E.bottomRow_mem_distTriang,
      by simpa using ((^⊥A).le_shift (-1) _ hK₃_shift), hA₃⟩
  have e : E.leftColumn.obj₃ ≅ T.obj₁⟦(1 : ℤ)⟧ := by
    -- Proof comment: the left column and `T.rotate` have the same first two vertices and first
    -- two morphisms, so TR3 upgrades the comparison of their third vertices to an isomorphism.
    exact Classical.choice <|
      third_obj_iso_of_distinguished_triangle_morphism
        (T₁ := E.leftColumn) (T₂ := T.rotate)
        E.leftColumn_mem_distTriang (rot_of_distTriang _ hT)
        (Iso.refl _) (Iso.refl _) (by simp)
  have h₁_shift : ((^⊥A) ⋆ A) (T.obj₁⟦(1 : ℤ)⟧) := by
    -- Proof comment: transport the inverse-rotated bottom-row witness across the comparison with
    -- `T.rotate`.
    exact ((^⊥A) ⋆ A).prop_of_iso e hleft_shift
  -- Proof comment: shift back by `-1` to recover the original first vertex of `T`.
  exact ((^⊥A) ⋆ A).prop_of_iso (shiftShiftNeg T.obj₁ (1 : ℤ))
    (((^⊥A) ⋆ A).le_shift (-1) _ h₁_shift)

/-- Helper for Lemma 13.40.6: the middle-object closure follows from the previous first-object
closure after rotation. -/
lemma leftOrthogonal_extensionProduct_closed₂_via_rotate
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : ((^⊥A) ⋆ A) T.obj₁) (h₃ : ((^⊥A) ⋆ A) T.obj₃) :
    ((^⊥A) ⋆ A) T.obj₂ := by
  have h₁_shift : ((^⊥A) ⋆ A) (T.obj₁⟦(1 : ℤ)⟧) := by
    -- Proof comment: the owner is shift-stable, so the first-vertex hypothesis can be moved to
    -- the third vertex of the rotated triangle.
    exact ((^⊥A) ⋆ A).le_shift 1 _ h₁
  -- Proof comment: apply the first-vertex closure to the rotated triangle.
  simpa using
    leftOrthogonal_extensionProduct_closed₁_of_distTriang
      (A := A) T.rotate (rot_of_distTriang _ hT) h₃ h₁_shift

-- Proof sketch: the owner-level mathematical content of clauses `(1)`–`(3)` is that the
-- canonical extension product `(^⊥A) ⋆ A` is triangulated. Clause `(2)` is the primitive
-- triangulated-closure field; clauses `(1)` and `(3)` are then derived automatically.
/-- Lemma 13.40.6 (1)–(3): the canonical extension product `(^⊥A) ⋆ A` is a
triangulated subcategory. Equivalently, it satisfies all three distinguished-triangle closure
clauses from the source statement. -/
instance leftOrthogonal_extensionProduct_isTriangulated :
    ((^⊥A) ⋆ A).IsTriangulated where
  toContainsZero := by
    obtain ⟨Z, hZ, hA⟩ := A.exists_prop_of_containsZero
    exact ⟨Z, hZ, le_extensionProduct_right (^⊥A) Z hA⟩
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := by
    -- Route correction: instead of forcing the middle-object clause directly, first prove the
    -- source-faithful dual `(obj₂,obj₃) -> obj₁` case by a `3-by-3` diagram and then rotate back.
    refine IsTriangulatedClosed₂.mk' ?_
    intro T hT h₁ h₃
    exact leftOrthogonal_extensionProduct_closed₂_via_rotate (A := A) T hT h₁ h₃

/- Companion recall for clause `(1)`: this is the canonical `Closed₁` consequence of the
triangulated owner instance above. -/
#check (inferInstance : ((^⊥A) ⋆ A).IsTriangulatedClosed₁)

/- Companion recall for clause `(2)`: this is the `Closed₂` field of the triangulated owner
instance above. -/
#check (inferInstance : ((^⊥A) ⋆ A).IsTriangulatedClosed₂)

/- Companion recall for clause `(3)`: this is the canonical `Closed₃` consequence of the
triangulated owner instance above. -/
#check (inferInstance : ((^⊥A) ⋆ A).IsTriangulatedClosed₃)

/- Companion recall for clause `(4)`: binary direct-sum closure is the generic owner consequence
of the triangulated instance above together with the canonical isomorphism-closure of
`extensionProduct`. -/
#check (inferInstance : ((^⊥A) ⋆ A).IsClosedUnderBinaryCoproducts)

end Triangulated

end CategoryTheory.ObjectProperty
