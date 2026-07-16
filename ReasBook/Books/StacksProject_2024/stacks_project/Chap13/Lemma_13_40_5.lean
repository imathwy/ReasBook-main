import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_3_4
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_40_1
import StacksProject_2024.stacks_project.Chap13.Proposition_13_4_23

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Pretriangulated
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 13.40.5:
- primary domain: triangulated closure of extension products of object properties in a
  triangulated category;
- sampled core/canonical declarations:
  `ObjectProperty.extensionProduct`,
  `ObjectProperty.rightOrthogonal`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsClosedUnderBinaryProducts`,
  `ObjectProperty.IsClosedUnderBinaryCoproducts`;
- best owner abstraction: the source-facing object property `A ⋆ A^⊥`, owned canonically by
  `ObjectProperty.extensionProduct`, whose three triangle-closure clauses are organized by the
  owner predicate `.IsTriangulated`, while direct-sum closure is the generic
  `ObjectProperty.IsClosedUnderBinaryCoproducts` owner consequence of a triangulated object
  property in the preadditive ambient category;
- primitive data: the object property `A`, its canonical right orthogonal `A^⊥`, and their
  canonical extension product `A ⋆ A^⊥`;
- derived API: the clausewise closure predicates
  `(A ⋆ A^⊥).IsTriangulatedClosed₁`,
  `(A ⋆ A^⊥).IsTriangulatedClosed₂`, and
  `(A ⋆ A^⊥).IsTriangulatedClosed₃`;
  clause `(4)` is the direct binary-coproduct closure of this same owner, obtained from its
  triangulated/product closure and the canonical biproduct bridge in a preadditive category.

Source/core/bridge triage:
- `source-facing`: Lemma `13.40.5` asserts that `A ⋆ A^⊥` is closed under the three distinguished
  triangle clauses and under binary direct sums;
- `core/canonical`: the owner declarations `extensionProduct`, `rightOrthogonal`, and
  `IsTriangulated`;
- `bridge/view`: the clausewise `IsTriangulatedClosed₁/₂/₃` consequences obtained by inference from
  the main triangulated owner instance, together with the generic binary-coproduct closure owner
  instance reused for clause `(4)`.

The file should therefore keep the owner-level triangulated instance as the main declaration and
demote the individual closure clauses to companion recalls, rather than storing all three as
primitive parallel instances. -/

section Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

omit [IsTriangulated D] in
/-- Helper for Lemma 13.40.5: in an extension-product witness
`A₀ ⟶ X ⟶ B₀ ⟶ A₀⟦1⟧` with `B₀ ∈ A^⊥`, the first map is `A`-colocal. -/
lemma extension_witness_first_map_is_colocal
    {X A₀ B₀ : D} {a : A₀ ⟶ X} {b : X ⟶ B₀} {c : B₀ ⟶ A₀⟦(1 : ℤ)⟧}
    (hT : Triangle.mk a b c ∈ distTriang D) (hB₀ : A^⊥ B₀) :
    A.isColocal a := by
  intro B hB
  constructor
  · intro f₁ f₂ h
    -- Proof comment: exactness for the inverse rotation turns a kernel element for `a` into a
    -- map to `B₀⟦-1⟧`, which must vanish because the right orthogonal is shift-stable.
    have hsub : (f₁ - f₂) ≫ a = 0 := by
      rw [Preadditive.sub_comp, sub_eq_zero]
      exact h
    obtain ⟨g, hg⟩ :=
      (Triangle.mk a b c).invRotate.coyoneda_exact₂
        (inv_rot_of_distTriang _ hT) (f₁ - f₂) hsub
    have hg_zero : g = 0 := by
      exact ((A^⊥).le_shift (-1) _ hB₀) g hB
    have hsub_zero : f₁ - f₂ = 0 := by
      calc
        f₁ - f₂ = g ≫ (Triangle.mk a b c).invRotate.mor₁ := by
          simpa using hg
        _ = 0 := by
          rw [hg_zero]
          exact zero_comp
    exact sub_eq_zero.mp hsub_zero
  · intro g
    -- Proof comment: exactness at `Hom(B, X)` gives a preimage of `g` once its composite with
    -- `b` vanishes, and that composite is zero because `B₀` lies in `A^⊥`.
    have hg_zero : g ≫ b = 0 := by
      exact hB₀ (g ≫ b) hB
    obtain ⟨f, hf⟩ := (Triangle.mk a b c).coyoneda_exact₂ hT g hg_zero
    exact ⟨f, hf.symm⟩

omit [IsTriangulated D] in
/-- Helper for Lemma 13.40.5: two distinguished triangles with the same first morphism have
isomorphic third vertices. -/
lemma nonempty_iso_of_same_first_morphism
    {X Y Z Z' : D} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}
    {g' : Y ⟶ Z'} {h' : Z' ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang D)
    (hT' : Triangle.mk f g' h' ∈ distTriang D) :
    Nonempty (Z ≅ Z') := by
  classical
  let hexists :=
    complete_distinguished_triangle_morphism
      (Triangle.mk f g h) (Triangle.mk f g' h') hT hT' (𝟙 X) (𝟙 Y) (by simp)
  let d : Z ⟶ Z' := Classical.choose hexists
  have hd₂ : g ≫ d = 𝟙 Y ≫ g' := (Classical.choose_spec hexists).1
  have hd₃ : h ≫ (𝟙 X)⟦(1 : ℤ)⟧' = d ≫ h' := (Classical.choose_spec hexists).2
  have hcomm₁ : f ≫ 𝟙 Y = 𝟙 X ≫ f := by
    simp
  have hcomm₂ : g ≫ d = 𝟙 Y ≫ g' := hd₂
  have hcomm₃ : h ≫ (𝟙 X)⟦(1 : ℤ)⟧' = d ≫ h' := hd₃
  let φ : Triangle.mk f g h ⟶ Triangle.mk f g' h' :=
    Triangle.homMk _ _ (𝟙 X) (𝟙 Y) d hcomm₁ hcomm₂ hcomm₃
  have hIso₁ : IsIso φ.hom₁ := by
    change IsIso (𝟙 X)
    infer_instance
  have hIso₂ : IsIso φ.hom₂ := by
    change IsIso (𝟙 Y)
    infer_instance
  have hIso₃ : IsIso d := by
    simpa [φ] using
      (Pretriangulated.isIso₃_of_isIso₁₂ φ hT hT' hIso₁ hIso₂)
  letI : IsIso d := hIso₃
  exact ⟨⟨d, inv d, by simp, by simp⟩⟩

/-- Helper for Lemma 13.40.5: if the first two vertices of a distinguished triangle belong to
`A ⋆ A^⊥`, then so does the third vertex. -/
lemma extensionProduct_rightOrthogonal_closed₃_of_distTriang
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : (A ⋆ A^⊥) T.obj₁) (h₂ : (A ⋆ A^⊥) T.obj₂) :
    (A ⋆ A^⊥) T.obj₃ := by
  classical
  rw [extensionProduct_iff] at h₁ h₂
  rcases h₁ with ⟨A₁, B₁, a₁, b₁, c₁, hT₁, hA₁, hB₁⟩
  rcases h₂ with ⟨A₂, B₂, a₂, b₂, c₂, hT₂, hA₂, hB₂⟩
  have hcolocal₂ : A.isColocal a₂ := by
    -- Proof comment: the right-orthogonal term in the second witness supplies the needed
    -- colocality for the lifting step of the source proof.
    exact extension_witness_first_map_is_colocal (A := A) hT₂ hB₂
  obtain ⟨u, hu⟩ := (hcolocal₂ A₁ hA₁).2 (a₁ ≫ T.mor₁)
  have hsq : a₁ ≫ T.mor₁ = u ≫ a₂ := hu.symm
  let sq : CommSq a₁ u T.mor₁ a₂ := CommSq.mk hsq
  let E : DistinguishedThreeByThreeExtension sq :=
    Classical.choice (commSq_has_distinguished_three_by_three_extension sq)
  have hTop : A^⊥ E.topRow.obj₃ := by
    -- Proof comment: the top row has the same first morphism as the chosen witness for `T.obj₁`,
    -- so TR3 identifies its cone with `B₁`.
    let eTop : E.topRow.obj₃ ≅ B₁ :=
      Classical.choice (nonempty_iso_of_same_first_morphism E.topRow_mem_distTriang hT₁)
    exact
      (A^⊥).prop_of_iso eTop.symm hB₁
  have hMiddleRow : A^⊥ E.middleRow.obj₃ := by
    -- Proof comment: the same comparison identifies the middle-row cone with the chosen `B₂`.
    let eMiddleRow : E.middleRow.obj₃ ≅ B₂ :=
      Classical.choice (nonempty_iso_of_same_first_morphism E.middleRow_mem_distTriang hT₂)
    exact
      (A^⊥).prop_of_iso eMiddleRow.symm hB₂
  have hA₃ : A.isoClosure E.leftColumn.obj₃ := by
    -- Proof comment: the left column is a distinguished triangle with first two terms in `A`,
    -- so the third term remains in `A` by triangulated closure.
    exact A.ext_of_isTriangulatedClosed₃' E.leftColumn E.leftColumn_mem_distTriang hA₁ hA₂
  have hB₃ : A^⊥ E.rightColumn.obj₃ := by
    -- Proof comment: the right column is a distinguished triangle with first two terms already in
    -- the right orthogonal, and `A^⊥` is itself triangulated.
    exact
      (A^⊥).ext_of_isTriangulatedClosed₃
        E.rightColumn E.rightColumn_mem_distTriang hTop hMiddleRow
  have hmid_isoClosure : (A.isoClosure ⋆ A^⊥) E.middleColumn.obj₃ := by
    -- Proof comment: the bottom row now exhibits the middle-column cone as an extension of the
    -- new `A`-object by the new `A^⊥`-object.
    rw [extensionProduct_iff]
    exact ⟨E.leftColumn.obj₃, E.rightColumn.obj₃, E.bottom1, E.bottom2, E.bottom3,
      E.bottomRow_mem_distTriang, hA₃, hB₃⟩
  have hmid : (A ⋆ A^⊥) E.middleColumn.obj₃ := by
    simpa [extensionProduct_isoClosure_left] using hmid_isoClosure
  have e : E.middleColumn.obj₃ ≅ T.obj₃ := by
    -- Proof comment: TR3 compares the middle column with the original triangle by identities on
    -- the first two vertices; two-out-of-three upgrades the third comparison map to an iso.
    exact Classical.choice (nonempty_iso_of_same_first_morphism E.middleColumn_mem_distTriang hT)
  -- Proof comment: transport the bottom-row witness across the comparison isomorphism to recover
  -- the original third vertex of `T`.
  exact (A ⋆ A^⊥).prop_of_iso e hmid

/-- Helper for Lemma 13.40.5: the middle-object closure follows from the previous third-object
closure after inverse rotation. -/
lemma extensionProduct_rightOrthogonal_closed₂_via_invRotate
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : (A ⋆ A^⊥) T.obj₁) (h₃ : (A ⋆ A^⊥) T.obj₃) :
    (A ⋆ A^⊥) T.obj₂ := by
  have h₃_shift : (A ⋆ A^⊥) (T.obj₃⟦(-1 : ℤ)⟧) := by
    -- Proof comment: `A ⋆ A^⊥` is already shift-stable, so the third-vertex hypothesis can be
    -- moved to the first vertex of the inverse rotation.
    exact (A ⋆ A^⊥).le_shift (-1) _ h₃
  -- Proof comment: apply the source-proof third-vertex argument to the inverse rotation.
  simpa using
    extensionProduct_rightOrthogonal_closed₃_of_distTriang
      (A := A) T.invRotate (inv_rot_of_distTriang _ hT) h₃_shift h₁

-- Proof sketch: the owner-level mathematical content of clauses `(1)`–`(3)` is that the
-- canonical extension product `A ⋆ A^⊥` is triangulated. Its `Closed₁` and
-- `Closed₃` clauses are then derived automatically from the canonical owner instance.
/-- Lemma 13.40.5 (1)–(3): the canonical extension product `A ⋆ A^⊥` is a
triangulated subcategory. Equivalently, it satisfies all three distinguished-triangle closure
clauses from the source statement. -/
instance extensionProduct_rightOrthogonal_isTriangulated :
    (A ⋆ A^⊥).IsTriangulated where
  toContainsZero := by
    obtain ⟨Z, hZ, hA⟩ := A.exists_prop_of_containsZero
    exact ⟨Z, hZ, le_extensionProduct_left (A^⊥) Z hA⟩
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := by
    -- Route correction: instead of trying to prove the middle-object clause directly, first prove
    -- the source-proof `(obj₁,obj₂) -> obj₃` case by a `3-by-3` diagram and then rotate back.
    refine IsTriangulatedClosed₂.mk' ?_
    intro T hT h₁ h₃
    exact extensionProduct_rightOrthogonal_closed₂_via_invRotate (A := A) T hT h₁ h₃

/- Companion recall for clause `(1)`: this is the canonical `Closed₁` consequence of the
triangulated owner instance above. -/
#check (inferInstance : (A ⋆ A^⊥).IsTriangulatedClosed₁)

/- Companion recall for clause `(2)`: this is the `Closed₂` field of the triangulated owner
instance above. -/
#check (inferInstance : (A ⋆ A^⊥).IsTriangulatedClosed₂)

/- Companion recall for clause `(3)`: this is the canonical `Closed₃` consequence of the
triangulated owner instance above. -/
#check (inferInstance : (A ⋆ A^⊥).IsTriangulatedClosed₃)

/- Companion recall for clause `(4)`: binary direct-sum closure is the generic owner consequence
of the triangulated instance above together with the canonical isomorphism-closure of
`extensionProduct`. -/
#check (inferInstance : (A ⋆ A^⊥).IsClosedUnderBinaryCoproducts)

end Triangulated

end CategoryTheory.ObjectProperty
