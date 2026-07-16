import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Triangulated.Rotate
import stacks_proof.stacks_project.Chap04.Definition_4_27_20
import stacks_proof.stacks_project.Chap04.Lemma_4_27_21
import stacks_proof.stacks_project.Chap04.Remark_4_27_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped MorphismPropertyUnder

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-
Domain-style sampling:
- primary domain: denominator categories in a pretriangulated category, built from morphisms from
  a fixed triangle into distinguished triangles;
- sampled owner declarations:
  `ObjectProperty.FullSubcategory`,
  `MorphismProperty.Under`,
  `MorphismProperty.localizationTargetArrows_isFiltered`,
  `Triangle.π₁`, `Triangle.π₂`, `Triangle.π₃`;
- best owner abstraction: the source-facing object is the full subcategory of `Under T`
  consisting of arrows to distinguished triangles whose three components lie in `S`, and the
  public derived API should be the three projection functors to the denominator categories over
  the vertices of `T`.

Primitive-vs-derived split:
- primitive data: an object of `Under T`, together with the conditions that its target triangle is
  distinguished and its three components lie in `S`;
- derived API: the full subcategory
  `distinguished_triangle_denominators S T`, its three projection functors, and the cofinality and
  filteredness theorems below.

Source/core/bridge triage:
- `source-facing`: `distinguished_triangle_denominators S T` and the projection functors to
  `T.objᵢ / S`;
- `core/canonical`: `ObjectProperty.FullSubcategory` on `Under T` and the canonical denominator
  owner `T.objᵢ / S`;
- `bridge/view`: the private predicate cutting out the full subcategory and the private generic
  projection helper.
-/

private abbrev triangleDenominatorProperty (S : MorphismProperty D) (T : Triangle D) :
    ObjectProperty (Under T) :=
  fun U ↦ U.right ∈ distTriang D ∧ S U.hom.hom₁ ∧ S U.hom.hom₂ ∧ S U.hom.hom₃

/-- The category of morphisms from `T` to distinguished triangles whose three components lie in
`S`, realized as the corresponding full subcategory of `Under T`. -/
abbrev distinguished_triangle_denominators (S : MorphismProperty D) (T : Triangle D) : Type _ :=
  (triangleDenominatorProperty S T).FullSubcategory

/-- A triangle projection `πᵢ : Triangle D ⥤ D` canonically yields a functor from `Under T` to
the under-category over `πᵢ.obj T` by applying `πᵢ` to the structural arrows. -/
private def triangle_projection_to_under (T : Triangle D) (π : Triangle D ⥤ D) :
    Under T ⥤ Under (π.obj T) :=
  Functor.toUnder (Under.forget T ⋙ π) (π.obj T) (fun U ↦ π.map U.hom) fun {U V} f ↦ by
    change π.map U.hom ≫ π.map f.right = π.map V.hom
    rw [← π.map_comp]
    exact congrArg (fun φ ↦ π.map φ) (Under.w f)

/-- A triangle projection `πᵢ : Triangle D ⥤ D` induces a projection from the
triangle-denominator category to the corresponding denominator category under `πᵢ.obj T`. -/
private def distinguished_triangle_denominators_to_under
    (S : MorphismProperty D) (T : Triangle D) (π : Triangle D ⥤ D)
    (hπ : ∀ U : Under T, triangleDenominatorProperty S T U → S (π.map U.hom)) :
    distinguished_triangle_denominators S T ⥤ π.obj T / S :=
  MorphismProperty.Comma.lift
    ((triangleDenominatorProperty S T).ι ⋙ triangle_projection_to_under T π)
    (fun U ↦ hπ U.obj U.property)
    (fun {_ _} _ ↦ trivial)
    (fun {_ _} _ ↦ trivial)

/-- The projection from the triangle-denominator category to the under-category over the first
vertex of `T`, remembering only the first component of a morphism of triangles. -/
def distinguished_triangle_denominators_to_under_one (S : MorphismProperty D) (T : Triangle D) :
    distinguished_triangle_denominators S T ⥤ T.obj₁ / S :=
  distinguished_triangle_denominators_to_under S T Triangle.π₁
    fun _ hU ↦ hU.2.1

/-- The projection from the triangle-denominator category to the under-category over the second
vertex of `T`, remembering only the second component of a morphism of triangles. -/
def distinguished_triangle_denominators_to_under_two (S : MorphismProperty D) (T : Triangle D) :
    distinguished_triangle_denominators S T ⥤ T.obj₂ / S :=
  distinguished_triangle_denominators_to_under S T Triangle.π₂
    fun _ hU ↦ hU.2.2.1

/-- The projection from the triangle-denominator category to the under-category over the third
vertex of `T`, remembering only the third component of a morphism of triangles. -/
def distinguished_triangle_denominators_to_under_three (S : MorphismProperty D) (T : Triangle D) :
    distinguished_triangle_denominators S T ⥤ T.obj₃ / S :=
  distinguished_triangle_denominators_to_under S T Triangle.π₃
    fun _ hU ↦ hU.2.2.2

variable (S : MorphismProperty D) [IsSaturatedMultiplicativeSystem S]
  [S.IsCompatibleWithTriangulation] (T : Triangle D)

/-- Helper for Lemma 13.5.10: every comparison morphism in the localization target-arrow category
`X / S` has underlying arrow in `S` when `S` is saturated. -/
lemma localization_target_arrow_mem {X : D} {s t : X / S} (f : s ⟶ t) :
    S f.right := by
  -- The underlying map becomes an isomorphism after applying the localization functor.
  have hsaturated : S.saturatedClosure f.right := by
    change IsIso (S.Q.map f.right)
    let es := Localization.isoOfHom S.Q S s.hom s.prop
    let et := Localization.isoOfHom S.Q S t.hom t.prop
    have hcomp : es.hom ≫ S.Q.map f.right = et.hom := by
      simpa [es, et, Functor.map_comp] using
        congrArg (Functor.map S.Q) (MorphismProperty.Under.w f)
    have hmap : S.Q.map f.right = es.inv ≫ et.hom := by
      have hpre := congrArg (fun k ↦ es.inv ≫ k) hcomp
      simpa [Category.assoc] using hpre
    rw [hmap]
    change IsIso ((es.symm ≪≫ et).hom)
    infer_instance
  -- Saturation identifies the saturated closure with `S` itself.
  exact (saturatedClosure_le S le_rfl) _ hsaturated

/-- Helper for Lemma 13.5.10: every isomorphism belongs to a saturated multiplicative system. -/
lemma mem_of_isIso {X Y : D} (f : X ⟶ Y) [IsIso f] : S f := by
  -- The localization sends isomorphisms to isomorphisms, so saturation puts them back in `S`.
  have hsaturated : S.saturatedClosure f := by
    change IsIso (S.Q.map f)
    infer_instance
  exact (saturatedClosure_le S le_rfl) _ hsaturated

/-- Helper for Lemma 13.5.10: an arrow in `S` out of the first vertex of a distinguished triangle
extends to a morphism into another distinguished triangle whose other two components also lie in
`S`. -/
lemma exists_triangle_morphism_of_hom₁_in_S {T₁ : Triangle D} (hT₁ : T₁ ∈ distTriang D)
    {X' : D} (a : T₁.obj₁ ⟶ X') (ha : S a) :
    ∃ (Y Z : D) (f' : X' ⟶ Y) (g' : Y ⟶ Z) (h' : Z ⟶ X'⟦(1 : ℤ)⟧),
      Triangle.mk f' g' h' ∈ distTriang D ∧
        ∃ φ : T₁ ⟶ Triangle.mk f' g' h', φ.hom₁ = a ∧ S φ.hom₂ ∧ S φ.hom₃ := by
  -- First create the Ore square on the first morphism of `T₁`.
  let ρ : S.RightFraction X' T₁.obj₂ := MorphismProperty.RightFraction.mk a ha T₁.mor₁
  obtain ⟨ℓ, hℓ⟩ := MorphismProperty.HasLeftCalculusOfFractions.exists_leftFraction ρ
  -- Next complete the new first morphism to a distinguished target triangle.
  obtain ⟨Z, g, h, hT₂₀⟩ := distinguished_cocone_triangle ℓ.f
  let T₂ : Triangle D := Triangle.mk ℓ.f g h
  have hT₂ : T₂ ∈ distTriang D := by
    simpa [T₂] using hT₂₀
  -- MS6 supplies the third component in `S`.
  obtain ⟨c, hc, hc₂, hc₃⟩ := S.compatible_with_triangulation T₁ T₂ hT₁ hT₂ a ℓ.s ha ℓ.hs
    (by simpa [ρ, T₂] using hℓ)
  have hcomm₁ : T₁.mor₁ ≫ ℓ.s = a ≫ T₂.mor₁ := by
    simpa [ρ, T₂] using hℓ
  have hcomm₂ : T₁.mor₂ ≫ c = ℓ.s ≫ T₂.mor₂ := hc₂
  have hcomm₃ : T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
    simpa [T₂] using hc₃
  let φ : T₁ ⟶ T₂ :=
    { hom₁ := a
      hom₂ := ℓ.s
      hom₃ := c
      comm₁ := hcomm₁
      comm₂ := hcomm₂
      comm₃ := hcomm₃ }
  exact ⟨_, _, _, _, _, hT₂, φ, rfl, ℓ.hs, hc⟩

/-- Helper for Lemma 13.5.10: an arrow in `S` out of the second vertex of a distinguished
triangle extends to a morphism into another distinguished triangle whose first and third
components also lie in `S`. -/
lemma exists_triangle_morphism_of_hom₂_in_S {T₁ : Triangle D} (hT₁ : T₁ ∈ distTriang D)
    {Y' : D} (b : T₁.obj₂ ⟶ Y') (hb : S b) :
    ∃ (X Z : D) (f' : X ⟶ Y') (g' : Y' ⟶ Z) (h' : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f' g' h' ∈ distTriang D ∧
        ∃ φ : T₁ ⟶ Triangle.mk f' g' h', φ.hom₂ = b ∧ S φ.hom₁ ∧ S φ.hom₃ := by
  -- Rotate once so that the prescribed second component becomes the first component.
  obtain ⟨Y₂, Z₂, f₂, g₂, h₂, hT₂rot, φrot, hφrot₁, hφrot₂, hφrot₃⟩ :=
    exists_triangle_morphism_of_hom₁_in_S (S := S) (T₁ := T₁.rotate)
      (CategoryTheory.Pretriangulated.rot_of_distTriang _ hT₁) b hb
  let T₂rot : Triangle D := Triangle.mk f₂ g₂ h₂
  let T₂ : Triangle D := T₂rot.invRotate
  have hT₂ : T₂ ∈ distTriang D := by
    -- Inverse rotation transports the distinguished target triangle back to the original shape.
    simpa [T₂, T₂rot] using CategoryTheory.Pretriangulated.inv_rot_of_distTriang T₂rot hT₂rot
  let φ : T₁ ⟶ T₂ := ((triangleRotation D).unitIso.app T₁).hom ≫ (invRotate D).map φrot
  have hφ₂ : φ.hom₂ = b := by
    -- The unit isomorphism is the identity on the second component, and `invRotate` turns
    -- the first rotated component into the second original component.
    dsimp [φ]
    simpa [Category.assoc, hφrot₁]
  have hφ₃ : S φ.hom₃ := by
    -- The third component is exactly the rotated witness `φrot.hom₂`.
    dsimp [φ]
    simpa [Category.assoc] using hφrot₂
  have hshift : S (((invRotate D).map φrot).hom₁) := by
    -- Shift compatibility moves the rotated third denominator back to degree `-1`.
    simpa [invRotate] using (IsCompatibleWithShift.iff S φrot.hom₃ (-1 : ℤ)).2 hφrot₃
  have hunit : S (((triangleRotation D).unitIso.app T₁).hom.hom₁) :=
    mem_of_isIso (S := S) ((triangleRotation D).unitIso.app T₁).hom.hom₁
  have hφ₁ : S φ.hom₁ := by
    -- Compose the unit-isomorphism denominator with the shifted rotated denominator.
    exact S.comp_mem _ _ hunit hshift
  exact ⟨T₂.obj₁, T₂.obj₃, T₂.mor₁, T₂.mor₂, T₂.mor₃, hT₂, φ, hφ₂, hφ₁, hφ₃⟩

/-- Helper for Lemma 13.5.10: an arrow in `S` out of the third vertex of a distinguished triangle
extends to a morphism into another distinguished triangle whose first and second components also
lie in `S`. -/
lemma exists_triangle_morphism_of_hom₃_in_S {T₁ : Triangle D} (hT₁ : T₁ ∈ distTriang D)
    {Z' : D} (c : T₁.obj₃ ⟶ Z') (hc : S c) :
    ∃ (X Y : D) (f' : X ⟶ Y) (g' : Y ⟶ Z') (h' : Z' ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f' g' h' ∈ distTriang D ∧
        ∃ φ : T₁ ⟶ Triangle.mk f' g' h', φ.hom₃ = c ∧ S φ.hom₁ ∧ S φ.hom₂ := by
  -- Rotate once more so that the prescribed third component becomes a prescribed second one.
  obtain ⟨X₂, Z₂, f₂, g₂, h₂, hT₂rot, φrot, hφrot₂, hφrot₁, hφrot₃⟩ :=
    exists_triangle_morphism_of_hom₂_in_S (S := S) (T₁ := T₁.rotate)
      (CategoryTheory.Pretriangulated.rot_of_distTriang _ hT₁) c hc
  let T₂rot : Triangle D := Triangle.mk f₂ g₂ h₂
  let T₂ : Triangle D := T₂rot.invRotate
  have hT₂ : T₂ ∈ distTriang D := by
    -- Undo the auxiliary rotation to recover a target triangle in the original orientation.
    simpa [T₂, T₂rot] using CategoryTheory.Pretriangulated.inv_rot_of_distTriang T₂rot hT₂rot
  let φ : T₁ ⟶ T₂ := ((triangleRotation D).unitIso.app T₁).hom ≫ (invRotate D).map φrot
  have hφ₃ : φ.hom₃ = c := by
    -- The third component is the prescribed second component on the rotated comparison.
    dsimp [φ]
    simpa [Category.assoc, hφrot₂]
  have hφ₂ : S φ.hom₂ := by
    -- The second component is the first component of the rotated witness.
    dsimp [φ]
    simpa [Category.assoc] using hφrot₁
  have hshift : S (((invRotate D).map φrot).hom₁) := by
    -- Shift compatibility again converts the rotated third denominator to the unrotated first.
    simpa [invRotate] using (IsCompatibleWithShift.iff S φrot.hom₃ (-1 : ℤ)).2 hφrot₃
  have hunit : S (((triangleRotation D).unitIso.app T₁).hom.hom₁) :=
    mem_of_isIso (S := S) ((triangleRotation D).unitIso.app T₁).hom.hom₁
  have hφ₁ : S φ.hom₁ := by
    -- The first component is still a composite of denominators.
    exact S.comp_mem _ _ hunit hshift
  exact ⟨T₂.obj₁, T₂.obj₂, T₂.mor₁, T₂.mor₂, T₂.mor₃, hT₂, φ, hφ₃, hφ₁, hφ₂⟩

/-- Helper for Lemma 13.5.10: if the first square between two distinguished triangles commutes in
the localization, then postcomposing the target triangle along a denominator on the second vertex
strictifies that square to an actual equality in `D`. -/
lemma strictify_mor₁_after_postcompose
    {T₁ T₂ : Triangle D} (hT₂ : T₂ ∈ distTriang D)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (hcomm : S.Q.map (a ≫ T₂.mor₁) = S.Q.map (T₁.mor₁ ≫ b)) :
    ∃ (T₃ : Triangle D) (φ : T₂ ⟶ T₃),
      T₃ ∈ distTriang D ∧ S φ.hom₁ ∧ S φ.hom₂ ∧ S φ.hom₃ ∧
        a ≫ φ.hom₁ ≫ T₃.mor₁ = T₁.mor₁ ≫ b ≫ φ.hom₂ := by
  -- Route correction: the source proof only needs one raw strictification step on `mor₁`;
  -- the `mor₂` and `mor₃` versions should later come from rotating this lemma.
  -- Convert the localization equality into an honest postcomposition equalizer in `S`.
  obtain ⟨Y₃, u, hu, hu_eq⟩ :=
    (map_eq_iff_postcomp S.Q S (a ≫ T₂.mor₁) (T₁.mor₁ ≫ b)).mp hcomm
  -- Complete that denominator on the second vertex to a morphism of distinguished triangles.
  obtain ⟨X₃, Z₃, f₃, g₃, h₃, hT₃, φ, hφ₂, hφ₁, hφ₃⟩ :=
    exists_triangle_morphism_of_hom₂_in_S (S := S) (T₁ := T₂) hT₂ u hu
  let T₃ : Triangle D := Triangle.mk f₃ g₃ h₃
  refine ⟨T₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact φ
  · simpa [T₃] using hT₃
  · simpa [T₃] using hφ₁
  · -- The second component is the chosen equalizing denominator.
    simpa [T₃, hφ₂] using hu
  · simpa [T₃] using hφ₃
  · -- Rewrite through the strict triangle relation `φ.comm₁`.
    calc
      a ≫ φ.hom₁ ≫ T₃.mor₁ = a ≫ (φ.hom₁ ≫ T₃.mor₁) := by simp [Category.assoc]
      _ = a ≫ (T₂.mor₁ ≫ φ.hom₂) := by rw [φ.comm₁]
      _ = (a ≫ T₂.mor₁) ≫ φ.hom₂ := by simp [Category.assoc]
      _ = (T₁.mor₁ ≫ b) ≫ φ.hom₂ := by simpa [Category.assoc, hφ₂] using hu_eq
      _ = T₁.mor₁ ≫ b ≫ φ.hom₂ := by simp [Category.assoc]

/-- Helper for Lemma 13.5.10: if the second square between two distinguished triangles commutes in
the localization, then rotating once reduces the problem to
`strictify_mor₁_after_postcompose`, and inverse rotation transports the strictified square back to
the original orientation. -/
lemma strictify_mor₂_after_postcompose
    {T₁ T₂ : Triangle D} (hT₂ : T₂ ∈ distTriang D)
    (b : T₁.obj₂ ⟶ T₂.obj₂) (c : T₁.obj₃ ⟶ T₂.obj₃)
    (hcomm : S.Q.map (b ≫ T₂.mor₂) = S.Q.map (T₁.mor₂ ≫ c)) :
    ∃ (T₃ : Triangle D) (φ : T₂ ⟶ T₃),
      T₃ ∈ distTriang D ∧ S φ.hom₁ ∧ S φ.hom₂ ∧ S φ.hom₃ ∧
        b ≫ φ.hom₂ ≫ T₃.mor₂ = T₁.mor₂ ≫ c ≫ φ.hom₃ := by
  -- Proof comment: after one rotation, the `mor₂` square is literally the `mor₁` square.
  have hT₂rot : T₂.rotate ∈ distTriang D := CategoryTheory.Pretriangulated.rot_of_distTriang _ hT₂
  obtain ⟨T₃rot, φrot, hT₃rot, hφrot₁, hφrot₂, hφrot₃, hstrictrot⟩ :=
    strictify_mor₁_after_postcompose (S := S) (T₁ := T₁.rotate) (T₂ := T₂.rotate)
      hT₂rot b c hcomm
  let T₃ : Triangle D := T₃rot.invRotate
  have hT₃ : T₃ ∈ distTriang D := by
    -- Proof comment: the rotated target remains distinguished after inverse rotation.
    simpa [T₃] using CategoryTheory.Pretriangulated.inv_rot_of_distTriang T₃rot hT₃rot
  let φ : T₂ ⟶ T₃ := ((triangleRotation D).unitIso.app T₂).hom ≫ (invRotate D).map φrot
  have hφ₂ : S φ.hom₂ := by
    -- Proof comment: the second transported component is the first component of the rotated
    -- strictifying morphism.
    dsimp [φ]
    simpa [Category.assoc] using hφrot₁
  have hφ₃ : S φ.hom₃ := by
    -- Proof comment: the third transported component is the second rotated component.
    dsimp [φ]
    simpa [Category.assoc] using hφrot₂
  have hshift : S (((invRotate D).map φrot).hom₁) := by
    -- Proof comment: inverse rotation shifts the rotated third denominator back to degree `-1`.
    simpa [invRotate] using (IsCompatibleWithShift.iff S φrot.hom₃ (-1 : ℤ)).2 hφrot₃
  have hunit : S (((triangleRotation D).unitIso.app T₂).hom.hom₁) :=
    mem_of_isIso (S := S) ((triangleRotation D).unitIso.app T₂).hom.hom₁
  have hφ₁ : S φ.hom₁ := by
    -- Proof comment: the first transported component is a composite of the unit isomorphism and
    -- the shifted rotated denominator.
    exact S.comp_mem _ _ hunit hshift
  refine ⟨T₃, φ, hT₃, hφ₁, hφ₂, hφ₃, ?_⟩
  -- Proof comment: after unfolding the transported components, the rotated strict equality is
  -- exactly the desired `mor₂` square.
  simpa [T₃, φ, Category.assoc] using hstrictrot

/-- Helper for Lemma 13.5.10: the inverse-rotation counit on `X⟦1⟧` is the shifted first
component of the rotation unit on `X`. -/
lemma shift_counit_inv_app_eq_shift_unit_hom (X : D) :
    (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app
        ((shiftFunctor D (1 : ℤ)).obj X) =
      (shiftFunctor D (1 : ℤ)).map
        ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by omega)).inv.app X) := by
  -- Proof comment: both maps are inverse to the shifted first component of the rotation unit, so
  -- we identify them by right-cancellation.
  apply (cancel_mono ((shiftFunctor D (1 : ℤ)).map
    ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by omega)).hom.app X))).1
  have hleft :
      (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app
          ((shiftFunctor D (1 : ℤ)).obj X) ≫
        (shiftFunctor D (1 : ℤ)).map
          ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by omega)).hom.app X) =
          𝟙 ((shiftFunctor D (1 : ℤ)).obj X) := by
    -- Proof comment: this is the triangle identity for the shift equivalence.
    simpa [Functor.map_comp, Category.assoc] using
      (CategoryTheory.Equivalence.counitIso_functor_comp (shiftEquiv D (1 : ℤ)) X)
  have hright :
      (shiftFunctor D (1 : ℤ)).map
          ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by omega)).inv.app X) ≫
        (shiftFunctor D (1 : ℤ)).map
          ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by omega)).hom.app X) =
          𝟙 ((shiftFunctor D (1 : ℤ)).obj X) := by
    -- Proof comment: the right-hand side is the shift of the obvious inverse-hom identity.
    rw [← Functor.map_comp]
    simpa using congrArg ((shiftFunctor D (1 : ℤ)).map)
      (((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by omega)).app X).inv_hom_id)
  exact hleft.trans hright.symm

/-- Helper for Lemma 13.5.10: after transporting a rotated morphism back by inverse rotation, the
rotated third component followed by the inverse-rotation counit is exactly the shifted first
component of the transported morphism. -/
lemma invRotate_transport_hom₁_shift_eq_counit_postcompose
    {T₂ T₃rot : Triangle D} (φrot : T₂.rotate ⟶ T₃rot) :
    φrot.hom₃ ≫ (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app T₃rot.obj₃ =
      (shiftFunctor D (1 : ℤ)).map (((triangleRotation D).unitIso.app T₂).hom.hom₁) ≫
        (shiftFunctor D (1 : ℤ)).map (((invRotate D).map φrot).hom₁) := by
  have hnat :
      φrot.hom₃ ≫ (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app T₃rot.obj₃ =
        (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app
            ((shiftFunctor D (1 : ℤ)).obj T₂.obj₁) ≫
          (shiftFunctor D (1 : ℤ)).map ((shiftFunctor D (-1 : ℤ)).map φrot.hom₃) := by
    -- Proof comment: naturality of the shift-equivalence counit moves `φrot.hom₃` across the
    -- inverse-rotation counit.
    simpa [Functor.comp_map, Functor.map_comp, Category.assoc] using
      ((shiftEquiv D (1 : ℤ)).counitIso.inv.naturality φrot.hom₃)
  have hunit :
      (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app
            ((shiftFunctor D (1 : ℤ)).obj T₂.obj₁) ≫
          (shiftFunctor D (1 : ℤ)).map ((shiftFunctor D (-1 : ℤ)).map φrot.hom₃) =
        (shiftFunctor D (1 : ℤ)).map (((triangleRotation D).unitIso.app T₂).hom.hom₁) ≫
          (shiftFunctor D (1 : ℤ)).map (((invRotate D).map φrot).hom₁) := by
    -- Proof comment: replace the inverse-rotation counit by the shifted rotation-unit component.
    rw [shift_counit_inv_app_eq_shift_unit_hom (D := D) T₂.obj₁]
    simp [invRotate]
  exact hnat.trans hunit

/-- Helper for Lemma 13.5.10: rotating once turns the `mor₃` square into a `mor₂` square, so the
preceding helper strictifies it after postcomposition and inverse rotation transports the result
back to the original orientation. -/
lemma strictify_mor₃_after_postcompose
    {T₁ T₂ : Triangle D} (hT₂ : T₂ ∈ distTriang D)
    (c : T₁.obj₃ ⟶ T₂.obj₃) (a : T₁.obj₁⟦(1 : ℤ)⟧ ⟶ T₂.obj₁⟦(1 : ℤ)⟧)
    (hcomm : S.Q.map (c ≫ T₂.mor₃) = S.Q.map (T₁.mor₃ ≫ a)) :
    ∃ (T₃ : Triangle D) (φ : T₂ ⟶ T₃),
      T₃ ∈ distTriang D ∧ S φ.hom₁ ∧ S φ.hom₂ ∧ S φ.hom₃ ∧
        c ≫ φ.hom₃ ≫ T₃.mor₃ = T₁.mor₃ ≫ a ≫ φ.hom₁⟦(1 : ℤ)⟧' := by
  -- Proof comment: after one rotation, the `mor₃` square becomes the `mor₂` square, so we can
  -- strictify there and then transport the result back through inverse rotation.
  have hT₂rot : T₂.rotate ∈ distTriang D := CategoryTheory.Pretriangulated.rot_of_distTriang _ hT₂
  obtain ⟨T₃rot, φrot, hT₃rot, hφrot₁, hφrot₂, hφrot₃, hstrictrot⟩ :=
    strictify_mor₂_after_postcompose (S := S) (T₁ := T₁.rotate) (T₂ := T₂.rotate)
      hT₂rot c a hcomm
  let T₃ : Triangle D := T₃rot.invRotate
  have hT₃ : T₃ ∈ distTriang D := by
    -- Proof comment: inverse rotation keeps the target distinguished.
    simpa [T₃] using CategoryTheory.Pretriangulated.inv_rot_of_distTriang T₃rot hT₃rot
  let φ : T₂ ⟶ T₃ := ((triangleRotation D).unitIso.app T₂).hom ≫ (invRotate D).map φrot
  have hφ₃ : S φ.hom₃ := by
    -- Proof comment: the transported third component is the strictifying rotated second component.
    dsimp [φ]
    simpa [Category.assoc] using hφrot₂
  have hφ₂ : S φ.hom₂ := by
    -- Proof comment: the transported second component is the rotated first component.
    dsimp [φ]
    simpa [Category.assoc] using hφrot₁
  have hshift : S (((invRotate D).map φrot).hom₁) := by
    -- Proof comment: shift compatibility converts the rotated third denominator to the unrotated
    -- first component of `invRotate.map φrot`.
    simpa [invRotate] using (IsCompatibleWithShift.iff S φrot.hom₃ (-1 : ℤ)).2 hφrot₃
  have hunit : S (((triangleRotation D).unitIso.app T₂).hom.hom₁) :=
    mem_of_isIso (S := S) ((triangleRotation D).unitIso.app T₂).hom.hom₁
  have hφ₁ : S φ.hom₁ := by
    -- Proof comment: the transported first component is the composite of the unit component and
    -- the shifted rotated denominator.
    exact S.comp_mem _ _ hunit hshift
  refine ⟨T₃, φ, hT₃, hφ₁, hφ₂, hφ₃, ?_⟩
  have htransport :=
    invRotate_transport_hom₁_shift_eq_counit_postcompose (D := D) φrot
  have hstrict :
      c ≫ φrot.hom₂ ≫ T₃rot.mor₂ ≫
          (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app T₃rot.obj₃ =
        T₁.mor₃ ≫ a ≫ φrot.hom₃ ≫
          (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app T₃rot.obj₃ := by
    -- Proof comment: postcompose the rotated strict equality with the inverse-rotation counit.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app T₃rot.obj₃)
        hstrictrot
  have htransport' :
      T₁.mor₃ ≫ a ≫ φrot.hom₃ ≫
          (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app T₃rot.obj₃ =
        T₁.mor₃ ≫ a ≫ φ.hom₁⟦(1 : ℤ)⟧' := by
    -- Proof comment: the transported rotated third component is the shifted first component of
    -- the inverse-rotated morphism.
    simpa [φ, Category.assoc] using congrArg (fun k ↦ T₁.mor₃ ≫ a ≫ k) htransport
  -- Proof comment: rewrite the inverse-rotated third morphism and then substitute the rotated
  -- strict equality followed by the transport identity for `φ.hom₁⟦1⟧'`.
  have hstart :
      c ≫ φ.hom₃ ≫ T₃.mor₃ =
        c ≫ φrot.hom₂ ≫ T₃rot.mor₂ ≫
          (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by omega)).inv.app T₃rot.obj₃ := by
    simp [T₃, φ, Category.assoc]
  exact hstart.trans (hstrict.trans htransport')

/-- Helper for Lemma 13.5.10: every object of `T.obj₁ / S` admits a morphism into the first
projection of some object of the triangle-denominator category. -/
lemma exists_object_over_under_one (hT : T ∈ distTriang D) (s : T.obj₁ / S) :
    ∃ U : distinguished_triangle_denominators S T,
      Nonempty (s ⟶ (distinguished_triangle_denominators_to_under_one S T).obj U) := by
  -- Complete the prescribed first-component denominator to a morphism of distinguished triangles.
  obtain ⟨Y, Z, f', g', h', hT', φ, hφ₁, hφ₂, hφ₃⟩ :=
    exists_triangle_morphism_of_hom₁_in_S (S := S) (T₁ := T) hT s.hom s.prop
  let U₀ : Under T := Under.mk φ
  have hU₀ : triangleDenominatorProperty S T U₀ := by
    -- The completed comparison already has a distinguished target and all three components in `S`.
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [U₀] using hT'
    · simpa [U₀, hφ₁] using s.prop
    · simpa [U₀] using hφ₂
    · simpa [U₀] using hφ₃
  refine ⟨⟨U₀, hU₀⟩, ⟨?_⟩⟩
  -- The comparison arrow is the identity on the chosen codomain object `s.right`.
  refine
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₁)
      (A := s) (B := (distinguished_triangle_denominators_to_under_one S T).obj ⟨U₀, hU₀⟩)
      (𝟙 s.right) ?_
  -- The first projection of the completed triangle morphism is exactly `φ.hom₁ = s.hom`.
  have hproj :
      s.hom =
        ((distinguished_triangle_denominators_to_under_one S T).obj ⟨U₀, hU₀⟩).hom := by
    simpa [distinguished_triangle_denominators_to_under_one, distinguished_triangle_denominators_to_under,
      triangle_projection_to_under, U₀] using hφ₁.symm
  have hid : s.hom ≫ 𝟙 s.right = s.hom := by simp
  exact hid.trans hproj

/-- Helper for Lemma 13.5.10: every comparison morphism in `T.obj₁ / S` lifts to a morphism in
the triangle-denominator category after replacing the target by a further denominator object. -/
lemma exists_morphism_over_under_one
    (U : distinguished_triangle_denominators S T) {t : T.obj₁ / S}
    (f : (distinguished_triangle_denominators_to_under_one S T).obj U ⟶ t) :
    ∃ (V : distinguished_triangle_denominators S T) (_g : U ⟶ V)
      (δ : t ⟶ (distinguished_triangle_denominators_to_under_one S T).obj V),
      f ≫ δ = (distinguished_triangle_denominators_to_under_one S T).map _g := by
  -- Saturation shows that the comparison map in `T.obj₁ / S` is itself a denominator.
  have hf : S f.right := localization_target_arrow_mem (S := S) f
  -- Complete that denominator out of the target triangle of `U`.
  obtain ⟨Y, Z, f', g', h', hT', φ, hφ₁, hφ₂, hφ₃⟩ :=
    exists_triangle_morphism_of_hom₁_in_S (S := S) (T₁ := U.obj.right) U.property.1 f.right hf
  let V₀ : Under T := Under.mk (U.obj.hom ≫ φ)
  have hV₀ : triangleDenominatorProperty S T V₀ := by
    -- The new denominator object is obtained by postcomposing the structural map of `U`.
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [V₀] using hT'
    · change S (U.obj.hom.hom₁ ≫ φ.hom₁)
      simpa [hφ₁] using S.comp_mem _ _ U.property.2.1 hf
    · change S (U.obj.hom.hom₂ ≫ φ.hom₂)
      simpa using S.comp_mem _ _ U.property.2.2.1 hφ₂
    · change S (U.obj.hom.hom₃ ≫ φ.hom₃)
      simpa using S.comp_mem _ _ U.property.2.2.2 hφ₃
  let V : distinguished_triangle_denominators S T := ⟨V₀, hV₀⟩
  let g₀ : U.obj ⟶ V₀ := Under.homMk φ rfl
  let g : U ⟶ V := ObjectProperty.homMk g₀
  -- The replacement is chosen so that its first projection has the same codomain and arrow as `t`.
  have hw : ((distinguished_triangle_denominators_to_under_one S T).obj U).hom ≫ f.right = t.hom :=
    MorphismProperty.Under.w f
  -- The first projection of `U.obj.hom ≫ φ` is the composite of first components.
  have hproj :
      t.hom = ((distinguished_triangle_denominators_to_under_one S T).obj V).hom := by
    change t.hom = U.obj.hom.hom₁ ≫ φ.hom₁
    simpa [distinguished_triangle_denominators_to_under_one, distinguished_triangle_denominators_to_under,
      triangle_projection_to_under, hφ₁] using hw.symm
  have hid : t.hom ≫ 𝟙 t.right = t.hom := by simp
  have hδ :
      t.hom ≫ 𝟙 t.right = ((distinguished_triangle_denominators_to_under_one S T).obj V).hom :=
    hid.trans hproj
  let δ :
      t ⟶ (distinguished_triangle_denominators_to_under_one S T).obj V :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₁)
      (A := t) (B := (distinguished_triangle_denominators_to_under_one S T).obj V)
      (𝟙 t.right) hδ
  refine ⟨V, g, δ, ?_⟩
  refine Under.Hom.ext ?_
  -- The factorization equality is visible on underlying arrows in the denominator category.
  simp [δ, distinguished_triangle_denominators_to_under_one, distinguished_triangle_denominators_to_under,
    triangle_projection_to_under, g, g₀, V, V₀, hφ₁]

/-- Helper for Lemma 13.5.10: every object of `T.obj₂ / S` admits a morphism into the second
projection of some object of the triangle-denominator category. -/
lemma exists_object_over_under_two (hT : T ∈ distTriang D) (s : T.obj₂ / S) :
    ∃ U : distinguished_triangle_denominators S T,
      Nonempty (s ⟶ (distinguished_triangle_denominators_to_under_two S T).obj U) := by
  -- Complete the prescribed second-component denominator to a morphism of distinguished triangles.
  obtain ⟨X, Z, f', g', h', hT', φ, hφ₂, hφ₁, hφ₃⟩ :=
    exists_triangle_morphism_of_hom₂_in_S (S := S) (T₁ := T) hT s.hom s.prop
  let U₀ : Under T := Under.mk φ
  have hU₀ : triangleDenominatorProperty S T U₀ := by
    -- The completed comparison again lands in the denominator full subcategory.
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [U₀] using hT'
    · simpa [U₀] using hφ₁
    · simpa [U₀, hφ₂] using s.prop
    · simpa [U₀] using hφ₃
  refine ⟨⟨U₀, hU₀⟩, ⟨?_⟩⟩
  -- The comparison arrow is the identity on the codomain of the chosen denominator `s`.
  refine
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₂)
      (A := s) (B := (distinguished_triangle_denominators_to_under_two S T).obj ⟨U₀, hU₀⟩)
      (𝟙 s.right) ?_
  have hproj :
      s.hom =
        ((distinguished_triangle_denominators_to_under_two S T).obj ⟨U₀, hU₀⟩).hom := by
    simpa [distinguished_triangle_denominators_to_under_two, distinguished_triangle_denominators_to_under,
      triangle_projection_to_under, U₀] using hφ₂.symm
  have hid : s.hom ≫ 𝟙 s.right = s.hom := by simp
  exact hid.trans hproj

/-- Helper for Lemma 13.5.10: every comparison morphism in `T.obj₂ / S` lifts to a morphism in
the triangle-denominator category after replacing the target by a further denominator object. -/
lemma exists_morphism_over_under_two
    (U : distinguished_triangle_denominators S T) {t : T.obj₂ / S}
    (f : (distinguished_triangle_denominators_to_under_two S T).obj U ⟶ t) :
    ∃ (V : distinguished_triangle_denominators S T) (_g : U ⟶ V)
      (δ : t ⟶ (distinguished_triangle_denominators_to_under_two S T).obj V),
      f ≫ δ = (distinguished_triangle_denominators_to_under_two S T).map _g := by
  -- Saturation again shows that the comparison map itself lies in `S`.
  have hf : S f.right := localization_target_arrow_mem (S := S) f
  -- Complete that denominator on the second vertex of the target triangle of `U`.
  obtain ⟨X, Z, f', g', h', hT', φ, hφ₂, hφ₁, hφ₃⟩ :=
    exists_triangle_morphism_of_hom₂_in_S (S := S) (T₁ := U.obj.right) U.property.1 f.right hf
  let V₀ : Under T := Under.mk (U.obj.hom ≫ φ)
  have hV₀ : triangleDenominatorProperty S T V₀ := by
    -- Postcomposing the structural morphism of `U` with the completed comparison keeps all three
    -- components inside `S`.
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [V₀] using hT'
    · change S (U.obj.hom.hom₁ ≫ φ.hom₁)
      simpa using S.comp_mem _ _ U.property.2.1 hφ₁
    · change S (U.obj.hom.hom₂ ≫ φ.hom₂)
      simpa [hφ₂] using S.comp_mem _ _ U.property.2.2.1 hf
    · change S (U.obj.hom.hom₃ ≫ φ.hom₃)
      simpa using S.comp_mem _ _ U.property.2.2.2 hφ₃
  let V : distinguished_triangle_denominators S T := ⟨V₀, hV₀⟩
  let g₀ : U.obj ⟶ V₀ := Under.homMk φ rfl
  let g : U ⟶ V := ObjectProperty.homMk g₀
  have hw : ((distinguished_triangle_denominators_to_under_two S T).obj U).hom ≫ f.right = t.hom :=
    MorphismProperty.Under.w f
  have hproj :
      t.hom = ((distinguished_triangle_denominators_to_under_two S T).obj V).hom := by
    change t.hom = U.obj.hom.hom₂ ≫ φ.hom₂
    simpa [distinguished_triangle_denominators_to_under_two, distinguished_triangle_denominators_to_under,
      triangle_projection_to_under, hφ₂] using hw.symm
  have hid : t.hom ≫ 𝟙 t.right = t.hom := by simp
  have hδ :
      t.hom ≫ 𝟙 t.right = ((distinguished_triangle_denominators_to_under_two S T).obj V).hom :=
    hid.trans hproj
  let δ :
      t ⟶ (distinguished_triangle_denominators_to_under_two S T).obj V :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₂)
      (A := t) (B := (distinguished_triangle_denominators_to_under_two S T).obj V)
      (𝟙 t.right) hδ
  refine ⟨V, g, δ, ?_⟩
  refine Under.Hom.ext ?_
  -- The factorization equality is visible on underlying arrows in the denominator category.
  simp [δ, distinguished_triangle_denominators_to_under_two, distinguished_triangle_denominators_to_under,
    triangle_projection_to_under, g, g₀, V, V₀, hφ₂]

/-- Helper for Lemma 13.5.10: every object of `T.obj₃ / S` admits a morphism into the third
projection of some object of the triangle-denominator category. -/
lemma exists_object_over_under_three (hT : T ∈ distTriang D) (s : T.obj₃ / S) :
    ∃ U : distinguished_triangle_denominators S T,
      Nonempty (s ⟶ (distinguished_triangle_denominators_to_under_three S T).obj U) := by
  -- Complete the prescribed third-component denominator to a morphism of distinguished triangles.
  obtain ⟨X, Y, f', g', h', hT', φ, hφ₃, hφ₁, hφ₂⟩ :=
    exists_triangle_morphism_of_hom₃_in_S (S := S) (T₁ := T) hT s.hom s.prop
  let U₀ : Under T := Under.mk φ
  have hU₀ : triangleDenominatorProperty S T U₀ := by
    -- The completed comparison still lies in the denominator subcategory.
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [U₀] using hT'
    · simpa [U₀] using hφ₁
    · simpa [U₀] using hφ₂
    · simpa [U₀, hφ₃] using s.prop
  refine ⟨⟨U₀, hU₀⟩, ⟨?_⟩⟩
  -- The comparison arrow is again the identity on the chosen codomain object `s`.
  refine
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₃)
      (A := s) (B := (distinguished_triangle_denominators_to_under_three S T).obj ⟨U₀, hU₀⟩)
      (𝟙 s.right) ?_
  have hproj :
      s.hom =
        ((distinguished_triangle_denominators_to_under_three S T).obj ⟨U₀, hU₀⟩).hom := by
    simpa [distinguished_triangle_denominators_to_under_three, distinguished_triangle_denominators_to_under,
      triangle_projection_to_under, U₀] using hφ₃.symm
  have hid : s.hom ≫ 𝟙 s.right = s.hom := by simp
  exact hid.trans hproj

/-- Helper for Lemma 13.5.10: every comparison morphism in `T.obj₃ / S` lifts to a morphism in
the triangle-denominator category after replacing the target by a further denominator object. -/
lemma exists_morphism_over_under_three
    (U : distinguished_triangle_denominators S T) {t : T.obj₃ / S}
    (f : (distinguished_triangle_denominators_to_under_three S T).obj U ⟶ t) :
    ∃ (V : distinguished_triangle_denominators S T) (_g : U ⟶ V)
      (δ : t ⟶ (distinguished_triangle_denominators_to_under_three S T).obj V),
      f ≫ δ = (distinguished_triangle_denominators_to_under_three S T).map _g := by
  -- Saturation again identifies the comparison map with a denominator.
  have hf : S f.right := localization_target_arrow_mem (S := S) f
  -- Complete that denominator on the third vertex of the target triangle of `U`.
  obtain ⟨X, Y, f', g', h', hT', φ, hφ₃, hφ₁, hφ₂⟩ :=
    exists_triangle_morphism_of_hom₃_in_S (S := S) (T₁ := U.obj.right) U.property.1 f.right hf
  let V₀ : Under T := Under.mk (U.obj.hom ≫ φ)
  have hV₀ : triangleDenominatorProperty S T V₀ := by
    -- Postcomposing the denominator object keeps all three components inside `S`.
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [V₀] using hT'
    · change S (U.obj.hom.hom₁ ≫ φ.hom₁)
      simpa using S.comp_mem _ _ U.property.2.1 hφ₁
    · change S (U.obj.hom.hom₂ ≫ φ.hom₂)
      simpa using S.comp_mem _ _ U.property.2.2.1 hφ₂
    · change S (U.obj.hom.hom₃ ≫ φ.hom₃)
      simpa [hφ₃] using S.comp_mem _ _ U.property.2.2.2 hf
  let V : distinguished_triangle_denominators S T := ⟨V₀, hV₀⟩
  let g₀ : U.obj ⟶ V₀ := Under.homMk φ rfl
  let g : U ⟶ V := ObjectProperty.homMk g₀
  have hw :
      ((distinguished_triangle_denominators_to_under_three S T).obj U).hom ≫ f.right = t.hom :=
    MorphismProperty.Under.w f
  have hproj :
      t.hom = ((distinguished_triangle_denominators_to_under_three S T).obj V).hom := by
    change t.hom = U.obj.hom.hom₃ ≫ φ.hom₃
    simpa [distinguished_triangle_denominators_to_under_three, distinguished_triangle_denominators_to_under,
      triangle_projection_to_under, hφ₃] using hw.symm
  have hid : t.hom ≫ 𝟙 t.right = t.hom := by simp
  have hδ :
      t.hom ≫ 𝟙 t.right = ((distinguished_triangle_denominators_to_under_three S T).obj V).hom :=
    hid.trans hproj
  let δ :
      t ⟶ (distinguished_triangle_denominators_to_under_three S T).obj V :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₃)
      (A := t) (B := (distinguished_triangle_denominators_to_under_three S T).obj V)
      (𝟙 t.right) hδ
  refine ⟨V, g, δ, ?_⟩
  refine Under.Hom.ext ?_
  -- The factorization equality is visible on underlying arrows in the denominator category.
  simp [δ, distinguished_triangle_denominators_to_under_three, distinguished_triangle_denominators_to_under,
    triangle_projection_to_under, g, g₀, V, V₀, hφ₃]

/-- Helper for Lemma 13.5.10: after replacing the second denominator object by a further
denominator object, the first projections of two objects admit a comparison arrow in `T.obj₁ / S`.
This is the source proof's first synchronization step before strictifying the other two squares by
rotation. -/
lemma distinguished_triangle_denominators_synchronize_first_component
    (U V : distinguished_triangle_denominators S T) :
    ∃ (W : distinguished_triangle_denominators S T) (_g : V ⟶ W),
      Nonempty
        ((distinguished_triangle_denominators_to_under_one S T).obj U ⟶
          (distinguished_triangle_denominators_to_under_one S T).obj W) := by
  let F := distinguished_triangle_denominators_to_under_one S T
  -- First take a common successor of the first projections in the filtered denominator category.
  let _ : IsFilteredOrEmpty (T.obj₁ / S) := inferInstance
  rcases IsFilteredOrEmpty.cocone_objs (F.obj U) (F.obj V) with ⟨t, ⟨α⟩, ⟨β⟩⟩
  let α' : F.obj U ⟶ t :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₁)
      (A := F.obj U) (B := t) α.right (by simpa using α.w.symm)
  let β' : F.obj V ⟶ t :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₁)
      (A := F.obj V) (B := t) β.right (by simpa using β.w.symm)
  -- Then lift the comparison out of `F.obj V` back to the denominator category.
  obtain ⟨W, g, δ, hδ⟩ :=
    exists_morphism_over_under_one (S := S) (T := T) V β'
  -- Composing the common-successor map with the lifted replacement gives the desired comparison.
  refine ⟨W, g, ⟨?_⟩⟩
  refine
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₁)
      (A := F.obj U) (B := F.obj W) (α.right ≫ δ.right) ?_
  -- The manual composite avoids the transport mismatch between the raw comma cocone witness
  -- and the canonical `Under` morphism view.
  have hα : (F.obj U).hom ≫ α.right = t.hom := by
    simpa using α.w.symm
  have hδ : t.hom ≫ δ.right = (F.obj W).hom := MorphismProperty.Under.w δ
  have hcomp :
      (F.obj U).hom ≫ (α.right ≫ δ.right) = t.hom ≫ δ.right := by
    calc
      (F.obj U).hom ≫ (α.right ≫ δ.right) = ((F.obj U).hom ≫ α.right) ≫ δ.right := by
        simp [Category.assoc]
      _ = t.hom ≫ δ.right := by
        exact congrArg (fun k ↦ k ≫ δ.right) hα
  exact hcomp.trans hδ

/-- Helper for Lemma 13.5.10: after replacing the second denominator object by a further
denominator object, the second projections of two objects admit a comparison arrow in `T.obj₂ / S`.
This is the source proof's second synchronization step. -/
lemma distinguished_triangle_denominators_synchronize_second_component
    (U V : distinguished_triangle_denominators S T) :
    ∃ (W : distinguished_triangle_denominators S T) (_g : V ⟶ W),
      Nonempty
        ((distinguished_triangle_denominators_to_under_two S T).obj U ⟶
          (distinguished_triangle_denominators_to_under_two S T).obj W) := by
  let F := distinguished_triangle_denominators_to_under_two S T
  -- First take a common successor of the second projections in the filtered denominator category.
  let _ : IsFilteredOrEmpty (T.obj₂ / S) := inferInstance
  rcases IsFilteredOrEmpty.cocone_objs (F.obj U) (F.obj V) with ⟨t, ⟨α⟩, ⟨β⟩⟩
  let α' : F.obj U ⟶ t :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₂)
      (A := F.obj U) (B := t) α.right (by simpa using α.w.symm)
  let β' : F.obj V ⟶ t :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₂)
      (A := F.obj V) (B := t) β.right (by simpa using β.w.symm)
  -- Then lift the comparison out of `F.obj V` back to the denominator category.
  obtain ⟨W, g, δ, hδ⟩ :=
    exists_morphism_over_under_two (S := S) (T := T) V β'
  -- Composing the common-successor map with the lifted replacement gives the desired comparison.
  refine ⟨W, g, ⟨?_⟩⟩
  refine
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₂)
      (A := F.obj U) (B := F.obj W) (α.right ≫ δ.right) ?_
  have hα : (F.obj U).hom ≫ α.right = t.hom := by
    simpa using α.w.symm
  have hδ : t.hom ≫ δ.right = (F.obj W).hom := MorphismProperty.Under.w δ
  have hcomp :
      (F.obj U).hom ≫ (α.right ≫ δ.right) = t.hom ≫ δ.right := by
    calc
      (F.obj U).hom ≫ (α.right ≫ δ.right) = ((F.obj U).hom ≫ α.right) ≫ δ.right := by
        simp [Category.assoc]
      _ = t.hom ≫ δ.right := by
        exact congrArg (fun k ↦ k ≫ δ.right) hα
  exact hcomp.trans hδ

/-- Helper for Lemma 13.5.10: after replacing the second denominator object by a further
denominator object, the third projections of two objects admit a comparison arrow in `T.obj₃ / S`.
This is the source proof's third synchronization step. -/
lemma distinguished_triangle_denominators_synchronize_third_component
    (U V : distinguished_triangle_denominators S T) :
    ∃ (W : distinguished_triangle_denominators S T) (_g : V ⟶ W),
      Nonempty
        ((distinguished_triangle_denominators_to_under_three S T).obj U ⟶
          (distinguished_triangle_denominators_to_under_three S T).obj W) := by
  let F := distinguished_triangle_denominators_to_under_three S T
  -- First take a common successor of the third projections in the filtered denominator category.
  let _ : IsFilteredOrEmpty (T.obj₃ / S) := inferInstance
  rcases IsFilteredOrEmpty.cocone_objs (F.obj U) (F.obj V) with ⟨t, ⟨α⟩, ⟨β⟩⟩
  let α' : F.obj U ⟶ t :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₃)
      (A := F.obj U) (B := t) α.right (by simpa using α.w.symm)
  let β' : F.obj V ⟶ t :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₃)
      (A := F.obj V) (B := t) β.right (by simpa using β.w.symm)
  -- Then lift the comparison out of `F.obj V` back to the denominator category.
  obtain ⟨W, g, δ, hδ⟩ :=
    exists_morphism_over_under_three (S := S) (T := T) V β'
  -- Composing the common-successor map with the lifted replacement gives the desired comparison.
  refine ⟨W, g, ⟨?_⟩⟩
  refine
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₃)
      (A := F.obj U) (B := F.obj W) (α.right ≫ δ.right) ?_
  have hα : (F.obj U).hom ≫ α.right = t.hom := by
    simpa using α.w.symm
  have hδ : t.hom ≫ δ.right = (F.obj W).hom := MorphismProperty.Under.w δ
  have hcomp :
      (F.obj U).hom ≫ (α.right ≫ δ.right) = t.hom ≫ δ.right := by
    calc
      (F.obj U).hom ≫ (α.right ≫ δ.right) = ((F.obj U).hom ≫ α.right) ≫ δ.right := by
        simp [Category.assoc]
      _ = t.hom ≫ δ.right := by
        exact congrArg (fun k ↦ k ≫ δ.right) hα
  exact hcomp.trans hδ

/-- Helper for Lemma 13.5.10: negating a morphism does not change membership in the saturated
multiplicative system `S`. -/
lemma neg_mem_iff {X Y : D} (f : X ⟶ Y) : S (-f) ↔ S f := by
  constructor
  · intro hf
    have hneg : S (-𝟙 X) := by
      simpa using mem_of_isIso (S := S) ((-Iso.refl X).hom)
    have hcomp : (-𝟙 X) ≫ (-f) = f := by simp
    simpa [hcomp] using S.comp_mem (-𝟙 X) (-f) hneg hf
  · intro hf
    have hneg : S (-𝟙 X) := by
      simpa using mem_of_isIso (S := S) ((-Iso.refl X).hom)
    have hcomp : (-𝟙 X) ≫ f = -f := by simp
    simpa [hcomp] using S.comp_mem (-𝟙 X) f hneg hf

/-- Helper for Lemma 13.5.10: rotating a denominator object keeps it inside the denominator
subcategory for the rotated source triangle. -/
lemma triangle_denominator_property_rotate
    {U : Under T} (hU : triangleDenominatorProperty S T U) :
    triangleDenominatorProperty S T.rotate
      ((Under.post (X := T) (triangleRotation D).functor).obj U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Proof comment: distinguished triangles stay distinguished after one rotation.
    simpa using CategoryTheory.Pretriangulated.rot_of_distTriang _ hU.1
  · -- Proof comment: the first rotated component is the original second component.
    simpa [Under.post, triangleRotation, Triangle.rotate] using hU.2.2.1
  · -- Proof comment: the second rotated component is the original third component.
    simpa [Under.post, triangleRotation, Triangle.rotate] using hU.2.2.2
  · -- Proof comment: the third rotated component is the shifted negative of the original first
    -- component, so shift compatibility keeps it in `S`.
    have hshift : S ((shiftFunctor D (1 : ℤ)).map U.hom.hom₁) :=
      (IsCompatibleWithShift.iff S U.hom.hom₁ (1 : ℤ)).2 hU.2.1
    simpa [Under.post, triangleRotation, Triangle.rotate] using hshift

/-- Helper for Lemma 13.5.10: inverse rotation carries denominator objects for `T.rotate` back to
denominator objects for `T`. -/
lemma triangle_denominator_property_invRotate
    {U : Under T.rotate} (hU : triangleDenominatorProperty S T.rotate U) :
    triangleDenominatorProperty S T
      ((Under.postEquiv T (triangleRotation D)).inverse.obj U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Proof comment: inverse rotation preserves distinguished triangles.
    simpa using CategoryTheory.Pretriangulated.inv_rot_of_distTriang _ hU.1
  · -- Proof comment: the first inverse-rotated component is the shifted negative of the rotated
    -- third component, preceded by the canonical shift-composition isomorphism.
    have hshift : S ((shiftFunctor D (-1 : ℤ)).map U.hom.hom₃) :=
      (IsCompatibleWithShift.iff S U.hom.hom₃ (-1 : ℤ)).2 hU.2.2.2
    have hiso :
        S ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by omega)).inv.app T.obj₁) := by
      simpa using
        mem_of_isIso (S := S) ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by omega)).inv.app T.obj₁)
    simpa [Under.postEquiv, Under.post, invRotate, Triangle.invRotate, Category.assoc] using
      S.comp_mem _ _ hiso hshift
  · -- Proof comment: the second inverse-rotated component is the original first component.
    simpa [Under.postEquiv, Under.post, invRotate, Triangle.invRotate] using hU.2.1
  · -- Proof comment: the third inverse-rotated component is the original second component.
    simpa [Under.postEquiv, Under.post, invRotate, Triangle.invRotate] using hU.2.2.1

/-- Helper for Lemma 13.5.10: rotation induces a functor between the two denominator full
subcategories. -/
noncomputable def rotate_distinguished_triangle_denominators_functor :
    distinguished_triangle_denominators S T ⥤ distinguished_triangle_denominators S T.rotate :=
  (triangleDenominatorProperty S T.rotate).lift
    ((triangleDenominatorProperty S T).ι ⋙ (Under.postEquiv T (triangleRotation D)).functor)
    (fun U ↦ triangle_denominator_property_rotate (S := S) (T := T) U.property)

/-- Helper for Lemma 13.5.10: inverse rotation induces the reverse functor between the two
denominator full subcategories. -/
noncomputable def invRotate_distinguished_triangle_denominators_functor :
    distinguished_triangle_denominators S T.rotate ⥤ distinguished_triangle_denominators S T :=
  (triangleDenominatorProperty S T).lift
    ((triangleDenominatorProperty S T.rotate).ι ⋙ (Under.postEquiv T (triangleRotation D)).inverse)
    (fun U ↦ triangle_denominator_property_invRotate (S := S) (T := T) U.property)

/-- Helper for Lemma 13.5.10: the component of the lifted unit isomorphism at a denominator
object is the ambient `Under.postEquiv` unit, viewed in the full subcategory. -/
noncomputable def rotate_distinguished_triangle_denominators_unitComponentIso
    (U : distinguished_triangle_denominators S T) :
    U ≅
      (rotate_distinguished_triangle_denominators_functor (S := S) (T := T) ⋙
        invRotate_distinguished_triangle_denominators_functor (S := S) (T := T)).obj U :=
  let e :
      U.obj ≅
        ((rotate_distinguished_triangle_denominators_functor (S := S) (T := T) ⋙
          invRotate_distinguished_triangle_denominators_functor (S := S) (T := T)).obj U).obj :=
    (Under.postEquiv T (triangleRotation D)).unitIso.app U.obj
  ObjectProperty.isoMk (P := triangleDenominatorProperty S T) (X := U)
    (Y := (rotate_distinguished_triangle_denominators_functor (S := S) (T := T) ⋙
      invRotate_distinguished_triangle_denominators_functor (S := S) (T := T)).obj U) e

/-- Helper for Lemma 13.5.10: the lifted unit components are natural. -/
lemma rotate_distinguished_triangle_denominators_unit_naturality
    {U V : distinguished_triangle_denominators S T} (f : U ⟶ V) :
    f ≫ (rotate_distinguished_triangle_denominators_unitComponentIso
        (S := S) (T := T) V).hom =
      (rotate_distinguished_triangle_denominators_unitComponentIso
        (S := S) (T := T) U).hom ≫
        ((rotate_distinguished_triangle_denominators_functor (S := S) (T := T) ⋙
          invRotate_distinguished_triangle_denominators_functor (S := S) (T := T)).map f) := by
  -- Proof comment: after forgetting the full-subcategory structure, this is exactly the
  -- naturality of the ambient unit on `Under T`.
  apply ObjectProperty.hom_ext
  simpa [rotate_distinguished_triangle_denominators_unitComponentIso,
    rotate_distinguished_triangle_denominators_functor,
    invRotate_distinguished_triangle_denominators_functor] using
    ((Under.postEquiv T (triangleRotation D)).unitIso.hom.naturality f.hom)

/-- Helper for Lemma 13.5.10: the lifted rotation and inverse-rotation functors inherit the unit
isomorphism from `Under.postEquiv`. -/
noncomputable def rotate_distinguished_triangle_denominators_unitIso :
    𝟭 (distinguished_triangle_denominators S T) ≅
      rotate_distinguished_triangle_denominators_functor (S := S) (T := T) ⋙
        invRotate_distinguished_triangle_denominators_functor (S := S) (T := T) :=
  NatIso.ofComponents
    (rotate_distinguished_triangle_denominators_unitComponentIso (S := S) (T := T))
    (fun f ↦ rotate_distinguished_triangle_denominators_unit_naturality (S := S) (T := T) f)

/-- Helper for Lemma 13.5.10: the component of the lifted counit isomorphism at a rotated
denominator object is the ambient `Under.postEquiv` counit, viewed in the full subcategory. -/
noncomputable def rotate_distinguished_triangle_denominators_counitComponentIso
    (U : distinguished_triangle_denominators S T.rotate) :
    (invRotate_distinguished_triangle_denominators_functor (S := S) (T := T) ⋙
      rotate_distinguished_triangle_denominators_functor (S := S) (T := T)).obj U ≅ U :=
  let e :
      ((invRotate_distinguished_triangle_denominators_functor (S := S) (T := T) ⋙
        rotate_distinguished_triangle_denominators_functor (S := S) (T := T)).obj U).obj ≅
        U.obj :=
    (Under.postEquiv T (triangleRotation D)).counitIso.app U.obj
  ObjectProperty.isoMk (P := triangleDenominatorProperty S T.rotate)
    (X := (invRotate_distinguished_triangle_denominators_functor (S := S) (T := T) ⋙
      rotate_distinguished_triangle_denominators_functor (S := S) (T := T)).obj U)
    (Y := U) e

/-- Helper for Lemma 13.5.10: the lifted counit components are natural. -/
lemma rotate_distinguished_triangle_denominators_counit_naturality
    {U V : distinguished_triangle_denominators S T.rotate} (f : U ⟶ V) :
    ((invRotate_distinguished_triangle_denominators_functor (S := S) (T := T) ⋙
        rotate_distinguished_triangle_denominators_functor (S := S) (T := T)).map f) ≫
      (rotate_distinguished_triangle_denominators_counitComponentIso
        (S := S) (T := T) V).hom =
        (rotate_distinguished_triangle_denominators_counitComponentIso
          (S := S) (T := T) U).hom ≫ f := by
  -- Proof comment: forgetting again reduces the statement to ambient counit naturality.
  apply ObjectProperty.hom_ext
  simpa [rotate_distinguished_triangle_denominators_counitComponentIso,
    rotate_distinguished_triangle_denominators_functor,
    invRotate_distinguished_triangle_denominators_functor] using
    ((Under.postEquiv T (triangleRotation D)).counitIso.hom.naturality f.hom)

/-- Helper for Lemma 13.5.10: the lifted rotation functors inherit the counit isomorphism from
`Under.postEquiv`. -/
noncomputable def rotate_distinguished_triangle_denominators_counitIso :
    invRotate_distinguished_triangle_denominators_functor (S := S) (T := T) ⋙
      rotate_distinguished_triangle_denominators_functor (S := S) (T := T) ≅
        𝟭 (distinguished_triangle_denominators S T.rotate) :=
  NatIso.ofComponents
    (rotate_distinguished_triangle_denominators_counitComponentIso (S := S) (T := T))
    (fun f ↦ rotate_distinguished_triangle_denominators_counit_naturality (S := S) (T := T) f)

/-- Helper for Lemma 13.5.10: the lifted unit and counit satisfy the triangle identity needed to
package the rotation functor as an equivalence. -/
lemma rotate_distinguished_triangle_denominators_functor_unitIso_comp
    (U : distinguished_triangle_denominators S T) :
    dsimp%
      (rotate_distinguished_triangle_denominators_counitIso (S := S) (T := T)).inv.app
          ((rotate_distinguished_triangle_denominators_functor (S := S) (T := T)).obj U) ≫
        (rotate_distinguished_triangle_denominators_functor (S := S) (T := T)).map
          ((rotate_distinguished_triangle_denominators_unitIso (S := S) (T := T)).inv.app U) =
      𝟙 ((rotate_distinguished_triangle_denominators_functor (S := S) (T := T)).obj U) := by
  -- Proof comment: this is the triangle identity for the ambient rotation equivalence, lifted
  -- through the denominator full subcategories.
  apply ObjectProperty.hom_ext
  simpa [rotate_distinguished_triangle_denominators_unitComponentIso,
    rotate_distinguished_triangle_denominators_counitComponentIso,
    rotate_distinguished_triangle_denominators_unitIso,
    rotate_distinguished_triangle_denominators_counitIso,
    rotate_distinguished_triangle_denominators_functor,
    invRotate_distinguished_triangle_denominators_functor] using
    (CategoryTheory.Equivalence.counitIso_functor_comp
      (Under.postEquiv T (triangleRotation D)) U.obj)

/-- Helper for Lemma 13.5.10: rotation and inverse rotation give an equivalence between the
denominator full subcategories for `T` and `T.rotate`. -/
noncomputable def rotate_distinguished_triangle_denominators_equivalence :
    distinguished_triangle_denominators S T ≌ distinguished_triangle_denominators S T.rotate :=
  CategoryTheory.Equivalence.mk''
    (rotate_distinguished_triangle_denominators_functor (S := S) (T := T))
    (invRotate_distinguished_triangle_denominators_functor (S := S) (T := T))
    (rotate_distinguished_triangle_denominators_unitIso (S := S) (T := T))
    (rotate_distinguished_triangle_denominators_counitIso (S := S) (T := T))
    (rotate_distinguished_triangle_denominators_functor_unitIso_comp (S := S) (T := T))

/-- Helper for Lemma 13.5.10: parallel morphisms in the denominator category become equal after
postcomposing with a further denominator morphism. -/
lemma distinguished_triangle_denominators_cocone_maps
    {U V : distinguished_triangle_denominators S T} (α β : U ⟶ V) :
    ∃ (W : distinguished_triangle_denominators S T) (γ : V ⟶ W), α ≫ γ = β ≫ γ := by
  let F₁ := distinguished_triangle_denominators_to_under_one S T
  let F₂ := distinguished_triangle_denominators_to_under_two S T
  let F₃ := distinguished_triangle_denominators_to_under_three S T
  -- First equalize the first projected morphisms in `T.obj₁ / S`.
  let _ : IsFilteredOrEmpty (T.obj₁ / S) := inferInstance
  obtain ⟨t₁, η₁, hη₁⟩ := IsFilteredOrEmpty.cocone_maps (F₁.map α) (F₁.map β)
  obtain ⟨W₁, γ₁, δ₁, hδ₁⟩ :=
    exists_morphism_over_under_one (S := S) (T := T) V η₁
  let α₁ : U ⟶ W₁ := α ≫ γ₁
  let β₁ : U ⟶ W₁ := β ≫ γ₁
  have hEq₁ : F₁.map α₁ = F₁.map β₁ := by
    -- Proof comment: the first projections agree because `η₁` equalizes them and `γ₁` lifts
    -- `η₁` through the denominator category.
    calc
      F₁.map α₁ = F₁.map α ≫ (F₁.map γ₁) := by simp [α₁]
      _ = F₁.map α ≫ (η₁ ≫ δ₁) := by rw [← hδ₁]
      _ = (F₁.map α ≫ η₁) ≫ δ₁ := by simp [Category.assoc]
      _ = (F₁.map β ≫ η₁) ≫ δ₁ := by rw [hη₁]
      _ = F₁.map β ≫ (η₁ ≫ δ₁) := by simp [Category.assoc]
      _ = F₁.map β ≫ (F₁.map γ₁) := by rw [hδ₁]
      _ = F₁.map β₁ := by simp [β₁]
  -- Next equalize the second projected morphisms after the first replacement.
  let _ : IsFilteredOrEmpty (T.obj₂ / S) := inferInstance
  obtain ⟨t₂, η₂, hη₂⟩ := IsFilteredOrEmpty.cocone_maps (F₂.map α₁) (F₂.map β₁)
  obtain ⟨W₂, γ₂, δ₂, hδ₂⟩ :=
    exists_morphism_over_under_two (S := S) (T := T) W₁ η₂
  let α₂ : U ⟶ W₂ := α₁ ≫ γ₂
  let β₂ : U ⟶ W₂ := β₁ ≫ γ₂
  have hEq₂ : F₂.map α₂ = F₂.map β₂ := by
    -- Proof comment: the second projections now agree by the same lifting-and-postcomposition
    -- argument on the second vertex.
    calc
      F₂.map α₂ = F₂.map α₁ ≫ (F₂.map γ₂) := by simp [α₂]
      _ = F₂.map α₁ ≫ (η₂ ≫ δ₂) := by rw [← hδ₂]
      _ = (F₂.map α₁ ≫ η₂) ≫ δ₂ := by simp [Category.assoc]
      _ = (F₂.map β₁ ≫ η₂) ≫ δ₂ := by rw [hη₂]
      _ = F₂.map β₁ ≫ (η₂ ≫ δ₂) := by simp [Category.assoc]
      _ = F₂.map β₁ ≫ (F₂.map γ₂) := by rw [hδ₂]
      _ = F₂.map β₂ := by simp [β₂]
  have hEq₁' : F₁.map α₂ = F₁.map β₂ := by
    -- Proof comment: later postcomposition preserves the already-established equality on the
    -- first projections.
    calc
      F₁.map α₂ = F₁.map α₁ ≫ F₁.map γ₂ := by simp [α₂]
      _ = F₁.map β₁ ≫ F₁.map γ₂ := by rw [hEq₁]
      _ = F₁.map β₂ := by simp [β₂]
  -- Finally equalize the third projected morphisms.
  let _ : IsFilteredOrEmpty (T.obj₃ / S) := inferInstance
  obtain ⟨t₃, η₃, hη₃⟩ := IsFilteredOrEmpty.cocone_maps (F₃.map α₂) (F₃.map β₂)
  obtain ⟨W₃, γ₃, δ₃, hδ₃⟩ :=
    exists_morphism_over_under_three (S := S) (T := T) W₂ η₃
  let γ : V ⟶ W₃ := γ₁ ≫ γ₂ ≫ γ₃
  have hEq₃ : F₃.map (α ≫ γ) = F₃.map (β ≫ γ) := by
    -- Proof comment: the third projections agree after the last replacement.
    calc
      F₃.map (α ≫ γ) = F₃.map α₂ ≫ F₃.map γ₃ := by
        simp [γ, α₁, α₂, Category.assoc]
      _ = F₃.map α₂ ≫ (η₃ ≫ δ₃) := by rw [← hδ₃]
      _ = (F₃.map α₂ ≫ η₃) ≫ δ₃ := by simp [Category.assoc]
      _ = (F₃.map β₂ ≫ η₃) ≫ δ₃ := by rw [hη₃]
      _ = F₃.map β₂ ≫ (η₃ ≫ δ₃) := by simp [Category.assoc]
      _ = F₃.map β₂ ≫ F₃.map γ₃ := by rw [hδ₃]
      _ = F₃.map (β ≫ γ) := by
        simp [γ, β₁, β₂, Category.assoc]
  have hEq₂' : F₂.map (α ≫ γ) = F₂.map (β ≫ γ) := by
    -- Proof comment: the second equality persists through the final postcomposition.
    calc
      F₂.map (α ≫ γ) = F₂.map α₂ ≫ F₂.map γ₃ := by
        simp [γ, α₁, α₂, Category.assoc]
      _ = F₂.map β₂ ≫ F₂.map γ₃ := by rw [hEq₂]
      _ = F₂.map (β ≫ γ) := by
        simp [γ, β₁, β₂, Category.assoc]
  have hEq₁'' : F₁.map (α ≫ γ) = F₁.map (β ≫ γ) := by
    -- Proof comment: the first equality likewise survives all later replacements.
    calc
      F₁.map (α ≫ γ) = F₁.map α₂ ≫ F₁.map γ₃ := by
        simp [γ, α₁, α₂, Category.assoc]
      _ = F₁.map β₂ ≫ F₁.map γ₃ := by rw [hEq₁']
      _ = F₁.map (β ≫ γ) := by
        simp [γ, β₁, β₂, Category.assoc]
  have h₁comp : (α ≫ γ).hom.right.hom₁ = (β ≫ γ).hom.right.hom₁ := by
    simpa [F₁, distinguished_triangle_denominators_to_under_one, distinguished_triangle_denominators_to_under,
      triangle_projection_to_under] using congrArg (fun f ↦ f.right) hEq₁''
  have h₂comp : (α ≫ γ).hom.right.hom₂ = (β ≫ γ).hom.right.hom₂ := by
    simpa [F₂, distinguished_triangle_denominators_to_under_two, distinguished_triangle_denominators_to_under,
      triangle_projection_to_under] using congrArg (fun f ↦ f.right) hEq₂'
  have h₃comp : (α ≫ γ).hom.right.hom₃ = (β ≫ γ).hom.right.hom₃ := by
    simpa [F₃, distinguished_triangle_denominators_to_under_three, distinguished_triangle_denominators_to_under,
      triangle_projection_to_under] using congrArg (fun f ↦ f.right) hEq₃
  refine ⟨W₃, γ, ?_⟩
  apply ObjectProperty.hom_ext
  -- Proof comment: a morphism of triangles is determined by its three components, and each
  -- component equality was produced by equalizing the corresponding projected morphisms.
  have hleft : (α ≫ γ).hom.left = (β ≫ γ).hom.left := by simp
  exact CommaMorphism.ext hleft <|
    Triangle.hom_ext ((α ≫ γ).hom.right) ((β ≫ γ).hom.right) h₁comp h₂comp h₃comp

/-- Helper for Chap13 Lemma 13 5 10: postcomposing a denominator object with a morphism of
distinguished triangles whose components lie in `S` produces another denominator object. -/
lemma triangleDenominatorProperty_postcompose
    {U : Under T} (hU : triangleDenominatorProperty S T U) {T' : Triangle D}
    (φ : U.right ⟶ T') (hT' : T' ∈ distTriang D)
    (hφ₁ : S φ.hom₁) (hφ₂ : S φ.hom₂) (hφ₃ : S φ.hom₃) :
    triangleDenominatorProperty S T (Under.mk (U.hom ≫ φ)) := by
  refine ⟨hT', ?_, ?_, ?_⟩
  · -- Proof comment: the first denominator stays in `S` after postcomposition.
    change S (U.hom.hom₁ ≫ φ.hom₁)
    simpa using S.comp_mem _ _ hU.2.1 hφ₁
  · -- Proof comment: the second denominator behaves identically.
    change S (U.hom.hom₂ ≫ φ.hom₂)
    simpa using S.comp_mem _ _ hU.2.2.1 hφ₂
  · -- Proof comment: the third denominator is again stable under postcomposition.
    change S (U.hom.hom₃ ≫ φ.hom₃)
    simpa using S.comp_mem _ _ hU.2.2.2 hφ₃

/-- Helper for Chap13 Lemma 13 5 10: first- and second-vertex comparison maps between projected
denominator objects induce the localization equality needed to strictify the first square. -/
lemma localizationCommMor1OfProjectionMaps
    {U W : distinguished_triangle_denominators S T}
    (a : (distinguished_triangle_denominators_to_under_one S T).obj U ⟶
      (distinguished_triangle_denominators_to_under_one S T).obj W)
    (b : (distinguished_triangle_denominators_to_under_two S T).obj U ⟶
      (distinguished_triangle_denominators_to_under_two S T).obj W) :
    S.Q.map (a.right ≫ W.obj.right.mor₁) = S.Q.map (U.obj.right.mor₁ ≫ b.right) := by
  -- Proof comment: cancel the localized first denominator of `U`, then compare both composites
  -- through the structural triangle-morphism identities of `U` and `W`.
  rw [← cancel_mono (Localization.isoOfHom S.Q S U.obj.hom.hom₁ U.property.2.1).hom]
  simp only [Localization.isoOfHom_hom, Functor.map_comp, Category.assoc]
  calc
    S.Q.map U.obj.hom.hom₁ ≫ S.Q.map a.right ≫ S.Q.map W.obj.right.mor₁ =
        S.Q.map W.obj.hom.hom₁ ≫ S.Q.map W.obj.right.mor₁ := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) (MorphismProperty.Under.w a)
    _ = S.Q.map T.mor₁ ≫ S.Q.map W.obj.hom.hom₂ := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) W.obj.hom.comm₁.symm
    _ = S.Q.map T.mor₁ ≫ (S.Q.map U.obj.hom.hom₂ ≫ S.Q.map b.right) := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) (MorphismProperty.Under.w b).symm
    _ = S.Q.map U.obj.hom.hom₁ ≫ (S.Q.map U.obj.right.mor₁ ≫ S.Q.map b.right) := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) U.obj.hom.comm₁

/-- Helper for Chap13 Lemma 13 5 10: second- and third-vertex comparison maps between projected
denominator objects induce the localization equality needed to strictify the second square. -/
lemma localizationCommMor2OfProjectionMaps
    {U W : distinguished_triangle_denominators S T}
    (b : (distinguished_triangle_denominators_to_under_two S T).obj U ⟶
      (distinguished_triangle_denominators_to_under_two S T).obj W)
    (c : (distinguished_triangle_denominators_to_under_three S T).obj U ⟶
      (distinguished_triangle_denominators_to_under_three S T).obj W) :
    S.Q.map (b.right ≫ W.obj.right.mor₂) = S.Q.map (U.obj.right.mor₂ ≫ c.right) := by
  -- Proof comment: cancel the localized second denominator of `U`, then rewrite through the
  -- second commutative squares of the structural morphisms.
  rw [← cancel_mono (Localization.isoOfHom S.Q S U.obj.hom.hom₂ U.property.2.2.1).hom]
  simp only [Localization.isoOfHom_hom, Functor.map_comp, Category.assoc]
  calc
    S.Q.map U.obj.hom.hom₂ ≫ S.Q.map b.right ≫ S.Q.map W.obj.right.mor₂ =
        S.Q.map W.obj.hom.hom₂ ≫ S.Q.map W.obj.right.mor₂ := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) (MorphismProperty.Under.w b)
    _ = S.Q.map T.mor₂ ≫ S.Q.map W.obj.hom.hom₃ := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) W.obj.hom.comm₂.symm
    _ = S.Q.map T.mor₂ ≫ (S.Q.map U.obj.hom.hom₃ ≫ S.Q.map c.right) := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) (MorphismProperty.Under.w c).symm
    _ = S.Q.map U.obj.hom.hom₂ ≫ (S.Q.map U.obj.right.mor₂ ≫ S.Q.map c.right) := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) U.obj.hom.comm₂

/-- Helper for Chap13 Lemma 13 5 10: third- and shifted first-vertex comparison maps between
projected denominator objects induce the localization equality needed to strictify the third
square. -/
lemma localizationCommMor3OfProjectionMaps
    {U W : distinguished_triangle_denominators S T}
    (c : (distinguished_triangle_denominators_to_under_three S T).obj U ⟶
      (distinguished_triangle_denominators_to_under_three S T).obj W)
    (a : (distinguished_triangle_denominators_to_under_one S T).obj U ⟶
      (distinguished_triangle_denominators_to_under_one S T).obj W) :
    S.Q.map (c.right ≫ W.obj.right.mor₃) =
      S.Q.map (U.obj.right.mor₃ ≫ a.right⟦(1 : ℤ)⟧') := by
  -- Proof comment: cancel the localized third denominator of `U`, then move the shifted first
  -- component across the structural `mor₃` squares.
  have hshift :
      U.obj.hom.hom₁⟦(1 : ℤ)⟧' ≫ a.right⟦(1 : ℤ)⟧' = W.obj.hom.hom₁⟦(1 : ℤ)⟧' := by
    simpa [Functor.map_comp] using
      congrArg (fun k ↦ (shiftFunctor D (1 : ℤ)).map k) (MorphismProperty.Under.w a)
  rw [← cancel_mono (Localization.isoOfHom S.Q S U.obj.hom.hom₃ U.property.2.2.2).hom]
  simp only [Localization.isoOfHom_hom, Functor.map_comp, Category.assoc]
  calc
    S.Q.map U.obj.hom.hom₃ ≫ S.Q.map c.right ≫ S.Q.map W.obj.right.mor₃ =
        S.Q.map W.obj.hom.hom₃ ≫ S.Q.map W.obj.right.mor₃ := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) (MorphismProperty.Under.w c)
    _ = S.Q.map T.mor₃ ≫ S.Q.map (W.obj.hom.hom₁⟦(1 : ℤ)⟧') := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) W.obj.hom.comm₃.symm
    _ = S.Q.map T.mor₃ ≫
        (S.Q.map (U.obj.hom.hom₁⟦(1 : ℤ)⟧') ≫ S.Q.map (a.right⟦(1 : ℤ)⟧')) := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) hshift.symm
    _ = S.Q.map U.obj.hom.hom₃ ≫
        (S.Q.map U.obj.right.mor₃ ≫ S.Q.map (a.right⟦(1 : ℤ)⟧')) := by
      simpa [Functor.map_comp, Category.assoc] using
        congrArg (Functor.map S.Q) U.obj.hom.comm₃

/-- Helper for Chap13 Lemma 13 5 10: any two denominator objects admit a common successor. The
proof synchronizes the three projected denominators and then strictifies the resulting three
localization-commutative squares one by one. -/
lemma distinguished_triangle_denominators_cocone_objects
    (U V : distinguished_triangle_denominators S T) :
    ∃ (W : distinguished_triangle_denominators S T) (_α : U ⟶ W) (_β : V ⟶ W), True := by
  let F₁ := distinguished_triangle_denominators_to_under_one S T
  let F₂ := distinguished_triangle_denominators_to_under_two S T
  let F₃ := distinguished_triangle_denominators_to_under_three S T
  -- Proof comment: first synchronize the three projected denominator objects onto one target.
  obtain ⟨W₁, g₁, ⟨a₁⟩⟩ :=
    distinguished_triangle_denominators_synchronize_first_component (S := S) (T := T) U V
  obtain ⟨W₂, g₂, ⟨b₂⟩⟩ :=
    distinguished_triangle_denominators_synchronize_second_component (S := S) (T := T) U W₁
  let a₂ : F₁.obj U ⟶ F₁.obj W₂ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₁)
      (A := F₁.obj U) (B := F₁.obj W₂) (a₁.right ≫ g₂.hom.right.hom₁) <| by
        calc
          (F₁.obj U).hom ≫ (a₁.right ≫ g₂.hom.right.hom₁) =
              ((F₁.obj U).hom ≫ a₁.right) ≫ g₂.hom.right.hom₁ := by
            simp [Category.assoc]
          _ = (F₁.obj W₁).hom ≫ g₂.hom.right.hom₁ := by
            rw [MorphismProperty.Under.w a₁]
          _ = (F₁.obj W₂).hom := by
            simpa [F₁, distinguished_triangle_denominators_to_under_one,
              distinguished_triangle_denominators_to_under, triangle_projection_to_under] using
              congrArg (fun f ↦ f.hom₁) (MorphismProperty.Under.w g₂.hom)
  obtain ⟨W₃, g₃, ⟨c₃⟩⟩ :=
    distinguished_triangle_denominators_synchronize_third_component (S := S) (T := T) U W₂
  let a₃ : F₁.obj U ⟶ F₁.obj W₃ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₁)
      (A := F₁.obj U) (B := F₁.obj W₃) (a₂.right ≫ g₃.hom.right.hom₁) <| by
        calc
          (F₁.obj U).hom ≫ (a₂.right ≫ g₃.hom.right.hom₁) =
              ((F₁.obj U).hom ≫ a₂.right) ≫ g₃.hom.right.hom₁ := by
            simp [Category.assoc]
          _ = (F₁.obj W₂).hom ≫ g₃.hom.right.hom₁ := by
            rw [MorphismProperty.Under.w a₂]
          _ = (F₁.obj W₃).hom := by
            simpa [F₁, distinguished_triangle_denominators_to_under_one,
              distinguished_triangle_denominators_to_under, triangle_projection_to_under] using
              congrArg (fun f ↦ f.hom₁) (MorphismProperty.Under.w g₃.hom)
  let b₃ : F₂.obj U ⟶ F₂.obj W₃ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₂)
      (A := F₂.obj U) (B := F₂.obj W₃) (b₂.right ≫ g₃.hom.right.hom₂) <| by
        calc
          (F₂.obj U).hom ≫ (b₂.right ≫ g₃.hom.right.hom₂) =
              ((F₂.obj U).hom ≫ b₂.right) ≫ g₃.hom.right.hom₂ := by
            simp [Category.assoc]
          _ = (F₂.obj W₂).hom ≫ g₃.hom.right.hom₂ := by
            rw [MorphismProperty.Under.w b₂]
          _ = (F₂.obj W₃).hom := by
            simpa [F₂, distinguished_triangle_denominators_to_under_two,
              distinguished_triangle_denominators_to_under, triangle_projection_to_under] using
              congrArg (fun f ↦ f.hom₂) (MorphismProperty.Under.w g₃.hom)
  -- Proof comment: strictify the first square after postcomposing the common target.
  obtain ⟨T₄, ψ₁, hT₄, hψ₁₁, hψ₁₂, hψ₁₃, hmor₁⟩ :=
    strictify_mor₁_after_postcompose (S := S) (T₁ := U.obj.right) (T₂ := W₃.obj.right)
      W₃.property.1 a₃.right b₃.right
      (localizationCommMor1OfProjectionMaps (S := S) (T := T) a₃ b₃)
  let W₄₀ : Under T := Under.mk (W₃.obj.hom ≫ ψ₁)
  have hW₄₀ : triangleDenominatorProperty S T W₄₀ :=
    triangleDenominatorProperty_postcompose (S := S) (T := T) W₃.property ψ₁ hT₄
      hψ₁₁ hψ₁₂ hψ₁₃
  let W₄ : distinguished_triangle_denominators S T := ⟨W₄₀, hW₄₀⟩
  let γ₁₀ : W₃.obj ⟶ W₄₀ := Under.homMk ψ₁ rfl
  let γ₁ : W₃ ⟶ W₄ := ObjectProperty.homMk γ₁₀
  let a₄ : F₁.obj U ⟶ F₁.obj W₄ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₁)
      (A := F₁.obj U) (B := F₁.obj W₄) (a₃.right ≫ ψ₁.hom₁) <| by
        calc
          (F₁.obj U).hom ≫ (a₃.right ≫ ψ₁.hom₁) = ((F₁.obj U).hom ≫ a₃.right) ≫ ψ₁.hom₁ := by
            simp [Category.assoc]
          _ = (F₁.obj W₃).hom ≫ ψ₁.hom₁ := by
            rw [MorphismProperty.Under.w a₃]
          _ = (F₁.obj W₄).hom := by
            rfl
  let b₄ : F₂.obj U ⟶ F₂.obj W₄ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₂)
      (A := F₂.obj U) (B := F₂.obj W₄) (b₃.right ≫ ψ₁.hom₂) <| by
        calc
          (F₂.obj U).hom ≫ (b₃.right ≫ ψ₁.hom₂) = ((F₂.obj U).hom ≫ b₃.right) ≫ ψ₁.hom₂ := by
            simp [Category.assoc]
          _ = (F₂.obj W₃).hom ≫ ψ₁.hom₂ := by
            rw [MorphismProperty.Under.w b₃]
          _ = (F₂.obj W₄).hom := by
            rfl
  let c₄ : F₃.obj U ⟶ F₃.obj W₄ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₃)
      (A := F₃.obj U) (B := F₃.obj W₄) (c₃.right ≫ ψ₁.hom₃) <| by
        calc
          (F₃.obj U).hom ≫ (c₃.right ≫ ψ₁.hom₃) = ((F₃.obj U).hom ≫ c₃.right) ≫ ψ₁.hom₃ := by
            simp [Category.assoc]
          _ = (F₃.obj W₃).hom ≫ ψ₁.hom₃ := by
            rw [MorphismProperty.Under.w c₃]
          _ = (F₃.obj W₄).hom := by
            rfl
  have hmor₁₄ : a₄.right ≫ W₄.obj.right.mor₁ = U.obj.right.mor₁ ≫ b₄.right := by
    -- Proof comment: the first square is now strict by construction of `ψ₁`.
    simpa [a₄, b₄, W₄, W₄₀, Category.assoc] using hmor₁
  -- Proof comment: repeat the strictification on the second square.
  obtain ⟨T₅, ψ₂, hT₅, hψ₂₁, hψ₂₂, hψ₂₃, hmor₂⟩ :=
    strictify_mor₂_after_postcompose (S := S) (T₁ := U.obj.right) (T₂ := W₄.obj.right)
      W₄.property.1 b₄.right c₄.right
      (localizationCommMor2OfProjectionMaps (S := S) (T := T) b₄ c₄)
  let W₅₀ : Under T := Under.mk (W₄.obj.hom ≫ ψ₂)
  have hW₅₀ : triangleDenominatorProperty S T W₅₀ :=
    triangleDenominatorProperty_postcompose (S := S) (T := T) W₄.property ψ₂ hT₅
      hψ₂₁ hψ₂₂ hψ₂₃
  let W₅ : distinguished_triangle_denominators S T := ⟨W₅₀, hW₅₀⟩
  let γ₂₀ : W₄.obj ⟶ W₅₀ := Under.homMk ψ₂ rfl
  let γ₂ : W₄ ⟶ W₅ := ObjectProperty.homMk γ₂₀
  let a₅ : F₁.obj U ⟶ F₁.obj W₅ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₁)
      (A := F₁.obj U) (B := F₁.obj W₅) (a₄.right ≫ ψ₂.hom₁) <| by
        calc
          (F₁.obj U).hom ≫ (a₄.right ≫ ψ₂.hom₁) = ((F₁.obj U).hom ≫ a₄.right) ≫ ψ₂.hom₁ := by
            simp [Category.assoc]
          _ = (F₁.obj W₄).hom ≫ ψ₂.hom₁ := by
            rw [MorphismProperty.Under.w a₄]
          _ = (F₁.obj W₅).hom := by
            rfl
  let b₅ : F₂.obj U ⟶ F₂.obj W₅ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₂)
      (A := F₂.obj U) (B := F₂.obj W₅) (b₄.right ≫ ψ₂.hom₂) <| by
        calc
          (F₂.obj U).hom ≫ (b₄.right ≫ ψ₂.hom₂) = ((F₂.obj U).hom ≫ b₄.right) ≫ ψ₂.hom₂ := by
            simp [Category.assoc]
          _ = (F₂.obj W₄).hom ≫ ψ₂.hom₂ := by
            rw [MorphismProperty.Under.w b₄]
          _ = (F₂.obj W₅).hom := by
            rfl
  let c₅ : F₃.obj U ⟶ F₃.obj W₅ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₃)
      (A := F₃.obj U) (B := F₃.obj W₅) (c₄.right ≫ ψ₂.hom₃) <| by
        calc
          (F₃.obj U).hom ≫ (c₄.right ≫ ψ₂.hom₃) = ((F₃.obj U).hom ≫ c₄.right) ≫ ψ₂.hom₃ := by
            simp [Category.assoc]
          _ = (F₃.obj W₄).hom ≫ ψ₂.hom₃ := by
            rw [MorphismProperty.Under.w c₄]
          _ = (F₃.obj W₅).hom := by
            rfl
  have hmor₁₅ : a₅.right ≫ W₅.obj.right.mor₁ = U.obj.right.mor₁ ≫ b₅.right := by
    -- Proof comment: postcomposition along `ψ₂` preserves the already strict first square.
    calc
      a₅.right ≫ W₅.obj.right.mor₁ = a₄.right ≫ (ψ₂.hom₁ ≫ W₅.obj.right.mor₁) := by
        simp [a₅, Category.assoc]
      _ = a₄.right ≫ (W₄.obj.right.mor₁ ≫ ψ₂.hom₂) := by
        rw [ψ₂.comm₁]
      _ = (a₄.right ≫ W₄.obj.right.mor₁) ≫ ψ₂.hom₂ := by
        simp [Category.assoc]
      _ = (U.obj.right.mor₁ ≫ b₄.right) ≫ ψ₂.hom₂ := by
        rw [hmor₁₄]
      _ = U.obj.right.mor₁ ≫ b₅.right := by
        simp [b₅, Category.assoc]
  have hmor₂₅ : b₅.right ≫ W₅.obj.right.mor₂ = U.obj.right.mor₂ ≫ c₅.right := by
    -- Proof comment: the second square is the one strictified by `ψ₂`.
    simpa [b₅, c₅, W₅, W₅₀, Category.assoc] using hmor₂
  -- Proof comment: strictify the third square after one final postcomposition.
  obtain ⟨T₆, ψ₃, hT₆, hψ₃₁, hψ₃₂, hψ₃₃, hmor₃⟩ :=
    strictify_mor₃_after_postcompose (S := S) (T₁ := U.obj.right) (T₂ := W₅.obj.right)
      W₅.property.1 c₅.right (a₅.right⟦(1 : ℤ)⟧')
      (localizationCommMor3OfProjectionMaps (S := S) (T := T) c₅ a₅)
  let W₆₀ : Under T := Under.mk (W₅.obj.hom ≫ ψ₃)
  have hW₆₀ : triangleDenominatorProperty S T W₆₀ :=
    triangleDenominatorProperty_postcompose (S := S) (T := T) W₅.property ψ₃ hT₆
      hψ₃₁ hψ₃₂ hψ₃₃
  let W₆ : distinguished_triangle_denominators S T := ⟨W₆₀, hW₆₀⟩
  let γ₃₀ : W₅.obj ⟶ W₆₀ := Under.homMk ψ₃ rfl
  let γ₃ : W₅ ⟶ W₆ := ObjectProperty.homMk γ₃₀
  let a₆ : F₁.obj U ⟶ F₁.obj W₆ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₁)
      (A := F₁.obj U) (B := F₁.obj W₆) (a₅.right ≫ ψ₃.hom₁) <| by
        calc
          (F₁.obj U).hom ≫ (a₅.right ≫ ψ₃.hom₁) = ((F₁.obj U).hom ≫ a₅.right) ≫ ψ₃.hom₁ := by
            simp [Category.assoc]
          _ = (F₁.obj W₅).hom ≫ ψ₃.hom₁ := by
            rw [MorphismProperty.Under.w a₅]
          _ = (F₁.obj W₆).hom := by
            rfl
  let b₆ : F₂.obj U ⟶ F₂.obj W₆ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₂)
      (A := F₂.obj U) (B := F₂.obj W₆) (b₅.right ≫ ψ₃.hom₂) <| by
        calc
          (F₂.obj U).hom ≫ (b₅.right ≫ ψ₃.hom₂) = ((F₂.obj U).hom ≫ b₅.right) ≫ ψ₃.hom₂ := by
            simp [Category.assoc]
          _ = (F₂.obj W₅).hom ≫ ψ₃.hom₂ := by
            rw [MorphismProperty.Under.w b₅]
          _ = (F₂.obj W₆).hom := by
            rfl
  let c₆ : F₃.obj U ⟶ F₃.obj W₆ :=
    MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := T.obj₃)
      (A := F₃.obj U) (B := F₃.obj W₆) (c₅.right ≫ ψ₃.hom₃) <| by
        calc
          (F₃.obj U).hom ≫ (c₅.right ≫ ψ₃.hom₃) = ((F₃.obj U).hom ≫ c₅.right) ≫ ψ₃.hom₃ := by
            simp [Category.assoc]
          _ = (F₃.obj W₅).hom ≫ ψ₃.hom₃ := by
            rw [MorphismProperty.Under.w c₅]
          _ = (F₃.obj W₆).hom := by
            rfl
  have hmor₁₆ : a₆.right ≫ W₆.obj.right.mor₁ = U.obj.right.mor₁ ≫ b₆.right := by
    -- Proof comment: postcomposition along `ψ₃` again preserves the first strict square.
    calc
      a₆.right ≫ W₆.obj.right.mor₁ = a₅.right ≫ (ψ₃.hom₁ ≫ W₆.obj.right.mor₁) := by
        simp [a₆, Category.assoc]
      _ = a₅.right ≫ (W₅.obj.right.mor₁ ≫ ψ₃.hom₂) := by
        rw [ψ₃.comm₁]
      _ = (a₅.right ≫ W₅.obj.right.mor₁) ≫ ψ₃.hom₂ := by
        simp [Category.assoc]
      _ = (U.obj.right.mor₁ ≫ b₅.right) ≫ ψ₃.hom₂ := by
        rw [hmor₁₅]
      _ = U.obj.right.mor₁ ≫ b₆.right := by
        simp [b₆, Category.assoc]
  have hmor₂₆ : b₆.right ≫ W₆.obj.right.mor₂ = U.obj.right.mor₂ ≫ c₆.right := by
    -- Proof comment: the second strict square also survives the last postcomposition.
    calc
      b₆.right ≫ W₆.obj.right.mor₂ = b₅.right ≫ (ψ₃.hom₂ ≫ W₆.obj.right.mor₂) := by
        simp [b₆, Category.assoc]
      _ = b₅.right ≫ (W₅.obj.right.mor₂ ≫ ψ₃.hom₃) := by
        rw [ψ₃.comm₂]
      _ = (b₅.right ≫ W₅.obj.right.mor₂) ≫ ψ₃.hom₃ := by
        simp [Category.assoc]
      _ = (U.obj.right.mor₂ ≫ c₅.right) ≫ ψ₃.hom₃ := by
        rw [hmor₂₅]
      _ = U.obj.right.mor₂ ≫ c₆.right := by
        simp [c₆, Category.assoc]
  have hmor₃₆ : c₆.right ≫ W₆.obj.right.mor₃ = U.obj.right.mor₃ ≫ a₆.right⟦(1 : ℤ)⟧' := by
    -- Proof comment: the third square is the one strictified by `ψ₃`.
    simpa [a₆, c₆, W₆, W₆₀, Category.assoc] using hmor₃
  -- Proof comment: the final strictified component maps assemble into a genuine morphism of
  -- triangles from `U` to the last denominator object.
  let φU : U.obj.right ⟶ W₆.obj.right :=
    { hom₁ := a₆.right
      hom₂ := b₆.right
      hom₃ := c₆.right
      comm₁ := hmor₁₆.symm
      comm₂ := hmor₂₆.symm
      comm₃ := hmor₃₆.symm }
  have hα₁ : U.obj.hom.hom₁ ≫ a₆.right = W₆.obj.hom.hom₁ := by
    simpa [F₁, distinguished_triangle_denominators_to_under_one,
      distinguished_triangle_denominators_to_under, triangle_projection_to_under] using
      (MorphismProperty.Under.w a₆)
  have hα₂ : U.obj.hom.hom₂ ≫ b₆.right = W₆.obj.hom.hom₂ := by
    simpa [F₂, distinguished_triangle_denominators_to_under_two,
      distinguished_triangle_denominators_to_under, triangle_projection_to_under] using
      (MorphismProperty.Under.w b₆)
  have hα₃ : U.obj.hom.hom₃ ≫ c₆.right = W₆.obj.hom.hom₃ := by
    simpa [F₃, distinguished_triangle_denominators_to_under_three,
      distinguished_triangle_denominators_to_under, triangle_projection_to_under] using
      (MorphismProperty.Under.w c₆)
  let α₀ : U.obj ⟶ W₆.obj := Under.homMk φU <| by
    apply Triangle.hom_ext
    · exact hα₁
    · exact hα₂
    · exact hα₃
  let α : U ⟶ W₆ := ObjectProperty.homMk α₀
  let β : V ⟶ W₆ := g₁ ≫ g₂ ≫ g₃ ≫ γ₁ ≫ γ₂ ≫ γ₃
  exact ⟨W₆, α, β, trivial⟩

/-- Helper for Chap13 Lemma 13 5 10: the denominator category of a distinguished triangle is
filtered. -/
lemma distinguishedTriangleDenominatorsIsFiltered
    (hT : T ∈ distTriang D) :
    IsFiltered (distinguished_triangle_denominators S T) := by
  refine
    { cocone_objs := ?_
      cocone_maps := ?_
      nonempty := ?_ }
  · intro U V
    -- Proof comment: the new object-cocone helper supplies the filteredness object axiom.
    obtain ⟨W, α, β, _⟩ :=
      distinguished_triangle_denominators_cocone_objects (S := S) (T := T) U V
    exact ⟨W, α, β, trivial⟩
  · intro U V α β
    -- Proof comment: equalizing parallel morphisms was already proved separately.
    exact distinguished_triangle_denominators_cocone_maps (S := S) (T := T) α β
  · -- Proof comment: the identity morphism on `T` is already a denominator object.
    let U₀ : Under T := Under.mk (𝟙 T)
    have hU₀ : triangleDenominatorProperty S T U₀ := by
      refine ⟨hT, ?_, ?_, ?_⟩
      · simpa [U₀] using mem_of_isIso (S := S) ((𝟙 T : T ⟶ T).hom₁)
      · simpa [U₀] using mem_of_isIso (S := S) ((𝟙 T : T ⟶ T).hom₂)
      · simpa [U₀] using mem_of_isIso (S := S) ((𝟙 T : T ⟶ T).hom₃)
    exact ⟨⟨U₀, hU₀⟩⟩

-- Proof sketch: complete any arrow in `S` out of `T.obj₁` to a morphism of distinguished
-- triangles using the compatibility axiom of `S`, use saturation to control arrows in the
-- localization, and then verify the structured-arrow connectedness criterion for cofinality.
/-- The first projection from the triangle-denominator category to the under-category over
`T.obj₁` is cofinal. -/
theorem distinguished_triangle_denominators_to_under_one_final
    (hT : T ∈ distTriang D) :
    (distinguished_triangle_denominators_to_under_one S T).Final := by
  -- Route correction: the proof should now use the new `hom₂`/`hom₃` completion lemmas to
  -- strictify localization-level equalities inside each structured-arrow fiber.
  let F := distinguished_triangle_denominators_to_under_one S T
  let _ : IsFiltered (distinguished_triangle_denominators S T) :=
    distinguishedTriangleDenominatorsIsFiltered (S := S) (T := T) hT
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · -- Proof comment: every object of the target under-category is reached by a denominator
    -- object via the first projection.
    intro s
    exact exists_object_over_under_one (S := S) (T := T) hT s
  · -- Proof comment: equalize inside `T.obj₁ / S`, then lift the replacement back to the
    -- denominator category.
    intro d U s s'
    let _ : IsFilteredOrEmpty (T.obj₁ / S) := inferInstance
    obtain ⟨t, η, hη⟩ := IsFilteredOrEmpty.cocone_maps s s'
    obtain ⟨V, g, δ, hδ⟩ := exists_morphism_over_under_one (S := S) (T := T) U η
    refine ⟨V, g, ?_⟩
    calc
      s ≫ F.map g = s ≫ (η ≫ δ) := by rw [hδ]
      _ = (s ≫ η) ≫ δ := by simp [Category.assoc]
      _ = (s' ≫ η) ≫ δ := by rw [hη]
      _ = s' ≫ (η ≫ δ) := by simp [Category.assoc]
      _ = s' ≫ F.map g := by rw [hδ]

-- Proof sketch: use the compatibility of `S` with the triangulated structure to complete arrows
-- in `S` to morphisms of distinguished triangles, obtaining surjectivity of the first projection
-- on objects and arrows; use rotation to transfer the same statements to the other two
-- projections; and then verify the three filteredness axioms by reducing to the filtered
-- denominator categories over the three vertices of `T`.
/-- Lemma 13.5.10: let `T` be a distinguished triangle in a pretriangulated category `D`, and let
`S` be a saturated multiplicative system compatible with the triangulated structure. Then the
category of morphisms of triangles from `T` to distinguished triangles whose three components lie
in `S` is filtered. The three canonical projections to the denominator categories over the
vertices of `T` are defined above and shown cofinal in the companion theorems. -/
@[stacks 05R9]
theorem distinguished_triangle_denominators_are_filtered
    (hT : T ∈ distTriang D) :
    IsFiltered (distinguished_triangle_denominators S T) := by
  -- Proof comment: the dedicated helper already assembles the three filteredness axioms.
  exact distinguishedTriangleDenominatorsIsFiltered (S := S) (T := T) hT

-- Proof sketch: rotate distinguished triangles and apply the cofinality statement for the first
-- projection to identify the second projection with the same argument after rotation.
/-- The second projection from the triangle-denominator category to the under-category over
`T.obj₂` is cofinal. -/
theorem distinguished_triangle_denominators_to_under_two_final
    (hT : T ∈ distTriang D) :
    (distinguished_triangle_denominators_to_under_two S T).Final := by
  let e := rotate_distinguished_triangle_denominators_equivalence (S := S) (T := T)
  let _ : e.functor.IsEquivalence := by
    change (rotate_distinguished_triangle_denominators_equivalence
      (S := S) (T := T)).functor.IsEquivalence
    infer_instance
  let _ :
      (distinguished_triangle_denominators_to_under_one S T.rotate).Final :=
    distinguished_triangle_denominators_to_under_one_final
      (S := S) (T := T.rotate)
      (CategoryTheory.Pretriangulated.rot_of_distTriang _ hT)
  -- Proof comment: after one rotation, the first projection is definitionally the original
  -- second projection, so finality transports across the lifted equivalence functor.
  simpa [e, rotate_distinguished_triangle_denominators_equivalence] using
    (CategoryTheory.Functor.final_equivalence_comp e.functor
      (distinguished_triangle_denominators_to_under_one S T.rotate))

-- Proof sketch: rotate distinguished triangles twice and reduce the third projection to the first
-- projection after transporting the denominator category along the rotation equivalence.
/-- The third projection from the triangle-denominator category to the under-category over
`T.obj₃` is cofinal. -/
theorem distinguished_triangle_denominators_to_under_three_final
    (hT : T ∈ distTriang D) :
    (distinguished_triangle_denominators_to_under_three S T).Final := by
  let e := rotate_distinguished_triangle_denominators_equivalence (S := S) (T := T)
  let _ : e.functor.IsEquivalence := by
    change (rotate_distinguished_triangle_denominators_equivalence
      (S := S) (T := T)).functor.IsEquivalence
    infer_instance
  let _ :
      (distinguished_triangle_denominators_to_under_two S T.rotate).Final :=
    distinguished_triangle_denominators_to_under_two_final
      (S := S) (T := T.rotate)
      (CategoryTheory.Pretriangulated.rot_of_distTriang _ hT)
  -- Proof comment: applying the previous step to `T.rotate` identifies the rotated second
  -- projection with the original third projection.
  simpa [e, rotate_distinguished_triangle_denominators_equivalence] using
    (CategoryTheory.Functor.final_equivalence_comp e.functor
      (distinguished_triangle_denominators_to_under_two S T.rotate))

end

end CategoryTheory
