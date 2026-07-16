import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Triangulated.Subcategory
import stacks_proof.stacks_project.Chap13.Definition_13_8_1
import stacks_proof.stacks_project.Chap13.Lemma_13_10_5
import stacks_proof.stacks_project.Chap13.Definition_13_11_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Localization
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory
open scoped ZeroObject

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.23.5:
- primary domain: bounded-below injective complexes in the homotopy category and exact functors
  between triangulated categories;
- sampled owner declarations:
  `Functor.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: the source-facing owners in this file are the full subcategory
  `K^+(\mathcal I) ⊆ K^+(\mathcal A)` and the corresponding homotopy resolution functor, while
  exactness itself is owned canonically upstream by `Functor.CommShift` together with
  `Functor.IsTriangulated`;
- primitive-vs-derived split:
  primitive data: the bounded-below injective full subcategory `K^+(\mathcal I)` together with a
    functor into that full subcategory and the comparison natural transformation from the
    identity;
  derived API: the triangulated instance on the injective subcategory and the exactness statement
    for the chosen resolution functor.

Source/core/bridge triage:
- `source-facing`: `HomotopyResolutionFunctor`;
- `core/canonical`: the exact-functor owners `Functor.CommShift` and `Functor.IsTriangulated`;
- `bridge/view`: the earlier owner API `boundedBelowInjectiveHomotopyProperty` and
  `boundedBelowInjectiveHomotopyCat`, which isolate the bounded-below injective objects before
  expressing exactness in the canonical triangulated API.
-/

/-- The object property on `K^+(\mathcal A)` cutting out the bounded-below complexes whose terms
are injective objects of `𝒜`. -/
abbrev boundedBelowInjectiveHomotopyProperty (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :
    ObjectProperty (K⁺(𝒜)) :=
  fun K ↦
    let C : CochainComplex 𝒜 ℤ := K.obj.as
    ∀ n : ℤ, Injective (C.X n)

/-- The bounded-below homotopy category `K^+(\mathcal I)` of complexes of injective objects in
`𝒜`. -/
abbrev boundedBelowInjectiveHomotopyCat (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :=
  (boundedBelowInjectiveHomotopyProperty 𝒜).FullSubcategory

/- The textbook category `K^+(\mathcal I)` depends on the ambient abelian category `𝒜` through
its injective objects. The scoped notation `K⁺ᵢ(𝒜)` keeps that ambient parameter explicit on the
Lean theorem surface while replacing the raw owner name. -/
scoped[CategoryTheory] notation:max "K⁺" "ᵢ(" A:arg ")" => boundedBelowInjectiveHomotopyCat A

/-- The quasi-isomorphisms in `K^+(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedBelowHomotopyQuasiIso (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (K⁺(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (HomotopyCategory.plus 𝒜).ι

scoped notation "Qis⁺(" A:arg ")" => boundedBelowHomotopyQuasiIso A

/-- Helper for Lemma 13.23.5: the ambient quotient `K(\mathcal A) ⟶ D(\mathcal A)` sends
bounded-below homotopy objects to bounded-below derived objects. -/
theorem qh_obj_mem_t_plus
    (X : K⁺(𝒜)) :
    (t.plus : ObjectProperty (D(𝒜))) (DerivedCategory.Qh.obj X.obj) := by
  let K : CochainComplex 𝒜 ℤ := X.obj.as
  have hK : CochainComplex.plus 𝒜 K := by
    simpa [K, HomotopyCategory.plus] using X.property
  rcases hK with ⟨n, hn⟩
  let _ : K.IsStrictlyGE n := by simpa [K] using hn
  let _ : K.IsGE n := inferInstance
  let e : DerivedCategory.Qh.obj X.obj ≅ DerivedCategory.Q.obj K := by
    simpa [K, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso 𝒜).app K
  have hQ : (t.plus : ObjectProperty (D(𝒜))) (DerivedCategory.Q.obj K) := by
    refine ⟨n, ?_⟩
    change (DerivedCategory.Q.obj K).IsGE n
    exact (DerivedCategory.isGE_Q_obj_iff K n).2 inferInstance
  exact (t.plus : ObjectProperty (D(𝒜))).prop_of_iso e.symm hQ

/-- The canonical functor `K^+(\mathcal A) ⟶ D^+(\mathcal A)`. -/
abbrev mapBoundedBelowHomotopyToDerivedBelow :
    K⁺(𝒜) ⥤ D⁺(𝒜) :=
  (t.plus : ObjectProperty (D(𝒜))).lift
    ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
    qh_obj_mem_t_plus

/-- A resolution functor on `K^+(\mathcal A)` is a functor from the bounded-below homotopy
category to the full subcategory of bounded-below complexes of injective objects, together with a
natural quasi-isomorphism from the identity after forgetting injectivity. -/
structure HomotopyResolutionFunctor (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] where
  /-- The underlying functor `K^+(\mathcal A) ⥤ K^+(\mathcal I)`. -/
  toFunctor : K⁺(𝒜) ⥤ K⁺ᵢ(𝒜)
  /-- The comparison morphism from a bounded-below complex to its chosen injective resolution. -/
  ι : 𝟭 (K⁺(𝒜)) ⟶
    toFunctor ⋙ ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
  /-- The comparison morphism is a quasi-isomorphism in `K^+(\mathcal A)` on every object. -/
  quasiIso_app (K : K⁺(𝒜)) : Qis⁺(𝒜) (ι.app K)

/-- Helper for Lemma 13.23.5: the canonical bounded-below localization functor
`K^+(\mathcal A) ⥤ D^+(\mathcal A)`. -/
private abbrev boundedBelowHomotopyToDerived :
    K⁺(𝒜) ⥤ D⁺(𝒜) :=
  mapBoundedBelowHomotopyToDerivedBelow

/-- Helper for Lemma 13.23.5: the inclusion `K^+(\mathcal I) ⥤ K^+(\mathcal A)`. -/
private abbrev boundedBelowInjectiveIncl :
    K⁺ᵢ(𝒜) ⥤ K⁺(𝒜) :=
  ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)

/-- Helper for Lemma 13.23.5: the functor from bounded-below injective homotopy objects to
`D^+(\mathcal A)`. -/
private abbrev boundedBelowInjectiveToDerived :
    K⁺ᵢ(𝒜) ⥤ D⁺(𝒜) :=
  boundedBelowInjectiveIncl (𝒜 := 𝒜) ⋙ boundedBelowHomotopyToDerived (𝒜 := 𝒜)

namespace boundedBelowInjectiveHomotopyCat

/-- Helper for Lemma 13.23.5: an object of `K^+(\mathcal I)` is represented by a bounded-below
cochain complex. -/
theorem plus (I : K⁺ᵢ(𝒜)) :
    CochainComplex.plus 𝒜 I.obj.obj.as := by
  -- The ambient bounded-below structure is already stored on the underlying `K^+(\mathcal A)`
  -- object, so this is just an unpacking step.
  simpa [HomotopyCategory.plus] using I.obj.property

/-- Helper for Lemma 13.23.5: the representing complex of an object of `K^+(\mathcal I)` has
injective terms. -/
theorem term_injective (I : K⁺ᵢ(𝒜)) (n : ℤ) :
    Injective (I.obj.obj.as.X n) := by
  -- Membership in `K^+(\mathcal I)` is exactly the termwise injectivity condition.
  simpa using I.property n

/-- Helper for Lemma 13.23.5: the representing complex of an object of `K^+(\mathcal I)` is
K-injective. -/
theorem isKInjective (I : K⁺ᵢ(𝒜)) :
    CochainComplex.IsKInjective I.obj.obj.as := by
  let C : CochainComplex 𝒜 ℤ := I.obj.obj.as
  -- Unpack bounded-below and termwise injective hypotheses, then invoke the canonical bridge
  -- from bounded-below injective complexes to K-injective complexes.
  have hC : CochainComplex.plus 𝒜 C := by
    simpa [C] using plus I
  obtain ⟨a, ha⟩ := hC
  let _ : C.IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective (C.X n) := by
    intro n
    simpa [C] using term_injective I n
  simpa [C] using CochainComplex.isKInjective_of_injective C a

end boundedBelowInjectiveHomotopyCat

open CochainComplex
open HomotopyCategory
open Pretriangulated

/-- Helper for Lemma 13.23.5: the mapping cone of a morphism in `K^+(\mathcal A)` is still
bounded below. -/
private theorem mappingCone_plus {X Y : K⁺(𝒜)} (f : X.obj.as ⟶ Y.obj.as) :
    CochainComplex.plus 𝒜 (mappingCone f) := by
  -- Read off explicit lower bounds on both complexes and propagate them through the mapping-cone
  -- construction.
  obtain ⟨n₁, hn₁⟩ : CochainComplex.plus 𝒜 X.obj.as := by
    simpa [HomotopyCategory.plus] using X.property
  obtain ⟨n₂, hn₂⟩ : CochainComplex.plus 𝒜 Y.obj.as := by
    simpa [HomotopyCategory.plus] using Y.property
  refine ⟨min (n₁ - 1) n₂, ?_⟩
  let K : CochainComplex 𝒜 ℤ := X.obj.as
  let L : CochainComplex 𝒜 ℤ := Y.obj.as
  let _ : K.IsStrictlyGE n₁ := by simpa [K] using hn₁
  let _ : L.IsStrictlyGE n₂ := by simpa [L] using hn₂
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hi₁ : i + 1 < n₁ := by
    have : i < n₁ - 1 := lt_of_lt_of_le hi (min_le_left _ _)
    linarith
  have hi₂ : i < n₂ := lt_of_lt_of_le hi (min_le_right _ _)
  simp only [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE n₁ _ hi₁, L.isZero_of_isStrictlyGE n₂ _ hi₂⟩

/-- Helper for Lemma 13.23.5: each term of the mapping cone of a morphism between bounded-below
injective complexes is injective. -/
private theorem mappingCone_term_injective
    {X Y : K⁺(𝒜)} (f : X.obj.as ⟶ Y.obj.as)
    (hX : boundedBelowInjectiveHomotopyProperty 𝒜 X)
    (hY : boundedBelowInjectiveHomotopyProperty 𝒜 Y) (n : ℤ) :
    Injective ((mappingCone f).X n) := by
  -- Each degree of the mapping cone is canonically a biproduct of one shifted source term and
  -- one target term.
  let _ : Injective (X.obj.as.X (n + 1)) := hX (n + 1)
  let _ : Injective (Y.obj.as.X n) := hY n
  exact
    Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm
      inferInstance

/-- Helper for Lemma 13.23.5: the bounded-below injective homotopy property contains an explicit
zero object. -/
private theorem boundedBelowInjective_containsZero_explicit :
    ∃ Z : K⁺(𝒜), IsZero Z ∧ boundedBelowInjectiveHomotopyProperty 𝒜 Z := by
  let Z : K⁺(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (HomologicalComplex.zero : CochainComplex 𝒜 ℤ),
      by
        simpa [HomotopyCategory.plus, HomotopyCategory.quotient_obj_as] using
          zero_mem_plus 𝒜⟩
  have hUnderlying : IsZero Z.obj := by
    -- The ambient zero complex stays zero after passing to the homotopy category.
    simpa [Z] using
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map_isZero HomologicalComplex.isZero_zero
  have hZ : IsZero Z := by
    -- Reflect zero-ness back through the fully faithful bounded-below inclusion.
    exact IsZero.of_full_of_faithful_of_isZero (HomotopyCategory.plus 𝒜).ι Z hUnderlying
  refine ⟨Z, hZ, ?_⟩
  intro n
  -- Each degree of the zero complex is the zero object of `𝒜`, hence injective.
  simpa [Z, HomotopyCategory.quotient_obj_as] using (inferInstance : Injective (0 : 𝒜))

/-- Helper for Lemma 13.23.5: the degree-`n` term of a shifted object of `K^+(\mathcal A)` is the
degree-`n + a` term of the underlying cochain complex. -/
private theorem kplus_shift_obj_eq_ambient_shift (K : K⁺(𝒜)) (a : ℤ) :
    ((K⟦a⟧).obj : K(𝒜)) = K.obj⟦a⟧ := by
  -- Route correction: make the full-subcategory shift explicit once so later termwise rewrites
  -- can use the ambient homotopy-category shift without repeated transport gymnastics.
  set_option allowUnsafeReducibility true in
    unfold ObjectProperty.hasShift
    unfold Functor.FullyFaithful.hasShift
    rfl

/-- Helper for Lemma 13.23.5: the degree-`n` term of a shifted object of `K^+(\mathcal A)` is the
degree-`n + a` term of the underlying cochain complex. -/
private theorem homotopy_shift_obj_as_X (K : K(𝒜)) (a n : ℤ) :
    ((K⟦a⟧).as.X n) = K.as.X (n + a) := by
  -- Route correction: descend to a representing cochain complex before computing the shift in
  -- the quotient homotopy category.
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  -- Unfold the quotient-induced shift once so the shifted object is represented by `C⟦a⟧`.
  set_option allowUnsafeReducibility true in
    unfold HomotopyCategory.hasShift CategoryTheory.HasShift.quotient
  -- The lifted shift functor acts on the representative complex degreewise.
  dsimp [Quotient.lift, HomotopyCategory.quotient]
  rfl

/-- Helper for Lemma 13.23.5: the degree-`n` term of a shifted object of `K^+(\mathcal A)` is the
degree-`n + a` term of the underlying cochain complex. -/
private theorem kplus_shift_obj_as_X (K : K⁺(𝒜)) (a n : ℤ) :
    ((K⟦a⟧).obj.as.X n) = K.obj.as.X (n + a) := by
  -- Rewrite the full-subcategory shift to the ambient homotopy-category shift first.
  rw [kplus_shift_obj_eq_ambient_shift (K := K) (a := a)]
  -- Then compute the degree on the ambient shifted representative.
  simpa using homotopy_shift_obj_as_X (K := K.obj) a n

/-- Helper for Lemma 13.23.5: shifting a bounded-below injective homotopy object preserves
termwise injectivity. -/
private theorem boundedBelowInjective_shift
    (K : K⁺(𝒜)) (a : ℤ)
    (hK : boundedBelowInjectiveHomotopyProperty 𝒜 K) :
    boundedBelowInjectiveHomotopyProperty 𝒜 (K⟦a⟧) := by
  intro n
  -- Reindex the shifted term back to the original complex and reuse injectivity there.
  simpa [kplus_shift_obj_as_X (K := K) (a := a) (n := n)] using hK (n + a)

/-- Helper for Lemma 13.23.5: the first morphism of the standard homotopy mapping-cone triangle is
the image of the original cochain map in the homotopy category. -/
private theorem homotopy_mappingCone_triangleh_mor1
    {X Y : CochainComplex 𝒜 ℤ} (f : X ⟶ Y) :
    (CochainComplex.mappingCone.triangleh f).mor₁ =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map f := by
  -- Unfold the standard cone triangle once; its first morphism is the quotient image of `f`.
  rfl

/-- Helper for Lemma 13.23.5: in a distinguished triangle of `K^+(\mathcal A)`, if the first and
third vertices have injective terms, then the middle vertex lies in the isomorphism-closure of the
bounded-below injective property. -/
private theorem boundedBelowInjective_closed₂_of_invRotate_cone
    (T : Triangle (K⁺(𝒜))) (hT : T ∈ distTriang (K⁺(𝒜)))
    (h₁ : boundedBelowInjectiveHomotopyProperty 𝒜 T.obj₁)
    (h₃ : boundedBelowInjectiveHomotopyProperty 𝒜 T.obj₃) :
    (boundedBelowInjectiveHomotopyProperty 𝒜).isoClosure T.obj₂ := by
  let T' : Triangle (K(𝒜)) := ((HomotopyCategory.plus 𝒜).ι.mapTriangle.obj T.invRotate)
  have hT' : T' ∈ distTriang (K(𝒜)) := by
    -- Move the distinguished triangle into the ambient homotopy category after inverse rotation.
    simpa [T'] using
      (HomotopyCategory.plus 𝒜).ι.map_distinguished T.invRotate (inv_rot_of_distTriang _ hT)
  have h₃_shift :
      boundedBelowInjectiveHomotopyProperty 𝒜 (T.obj₃⟦(-1 : ℤ)⟧) := by
    -- The first vertex of `T.invRotate` is the shifted original third vertex.
    exact boundedBelowInjective_shift (𝒜 := 𝒜) T.obj₃ (-1) h₃
  have hT'₁ :
      boundedBelowInjectiveHomotopyProperty 𝒜 T.invRotate.obj₁ := by
    simpa [Triangle.invRotate_obj₁] using h₃_shift
  have hT'₂ :
      boundedBelowInjectiveHomotopyProperty 𝒜 T.invRotate.obj₂ := by
    simpa [Triangle.invRotate_obj₂] using h₁
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient 𝒜 (up ℤ)).map_surjective T'.mor₁
  let M : K⁺(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (mappingCone f), by
      -- The cone of a map between bounded-below complexes stays bounded below.
      simpa [HomotopyCategory.plus, HomotopyCategory.quotient_obj_as, T',
        Triangle.invRotate_obj₁, Triangle.invRotate_obj₂] using
          mappingCone_plus (𝒜 := 𝒜) (X := T.invRotate.obj₁) (Y := T.invRotate.obj₂) f⟩
  have hM :
      boundedBelowInjectiveHomotopyProperty 𝒜 M := by
    intro n
    -- Cone terms are biproducts of injective terms from the first two vertices.
    simpa [M, HomotopyCategory.quotient_obj_as, T', Triangle.invRotate_obj₁,
      Triangle.invRotate_obj₂] using
        mappingCone_term_injective (𝒜 := 𝒜) (X := T.invRotate.obj₁) (Y := T.invRotate.obj₂) f
          hT'₁ hT'₂ n
  have e :
      T' ≅ CochainComplex.mappingCone.triangleh f := by
    -- Compare the ambient inverse-rotated triangle to the standard cone triangle with the same
    -- first morphism.
    refine Pretriangulated.isoTriangleOfIso₁₂ T' _ hT'
      (HomotopyCategory.mappingCone_triangleh_distinguished f) (Iso.refl _) (Iso.refl _) ?_
    have h₁ :
        T'.mor₁ ≫ (Iso.refl T'.obj₂).hom = T'.mor₁ := by
      simp
    have h₂ :
        T'.mor₁ = (HomotopyCategory.quotient 𝒜 (up ℤ)).map f := hf.symm
    have h₃ :
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map f =
          (Iso.refl T'.obj₁).hom ≫ (CochainComplex.mappingCone.triangleh f).mor₁ := by
      simp
    exact h₁.trans (h₂.trans h₃)
  refine ⟨M, hM, ?_⟩
  -- Transport the cone injectivity witness back along the third component isomorphism.
  refine ⟨ObjectProperty.isoMk (P := HomotopyCategory.plus 𝒜) (X := T.obj₂) (Y := M) ?_⟩
  simpa [M, T', Triangle.invRotate_obj₃] using (Triangle.π₃.mapIso e)

-- Proof sketch: shifts preserve termwise injectivity by reindexing. For the triangulated
-- two-out-of-three clause, compare a distinguished triangle in `K^+(\mathcal A)` with the
-- standard mapping-cone triangle of a representing cochain map; the cone has injective terms
-- degreewise because those terms are finite biproducts of injectives.
/-- The bounded-below injective object property on `K^+(\mathcal A)` is triangulated. -/
instance boundedBelowInjectiveHomotopyProperty_isTriangulated :
    ObjectProperty.IsTriangulated (boundedBelowInjectiveHomotopyProperty 𝒜) := by
  refine
    { exists_zero := ?_
      toIsStableUnderShift := ?_
      toIsTriangulatedClosed₂ := ?_ }
  · -- Use the explicit zero witness rather than computing with the chosen categorical zero term.
    rcases boundedBelowInjective_containsZero_explicit (𝒜 := 𝒜) with ⟨Z, hZzero, hZ⟩
    exact ⟨Z, hZzero, hZ⟩
  · refine
      { isStableUnderShiftBy := fun a ↦ IsStableUnderShiftBy.mk <| by
          intro K hK
          exact boundedBelowInjective_shift (𝒜 := 𝒜) K a hK }
  · refine ⟨fun T hT h₁ h₃ ↦ ?_⟩
    -- Apply the source-faithful inverse-rotation cone argument.
    exact boundedBelowInjective_closed₂_of_invRotate_cone (𝒜 := 𝒜) T hT h₁ h₃

/-- Helper for Lemma 13.23.5: the bounded-below derived functor sends bounded-below
quasi-isomorphisms to isomorphisms. -/
private theorem mapBoundedBelowHomotopyToDerivedBelow_map_isIso
    {X Y : K⁺(𝒜)} (f : X ⟶ Y) (hf : Qis⁺(𝒜) f) :
    IsIso (mapBoundedBelowHomotopyToDerivedBelow.map f) := by
  let ιplus : D⁺(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
  have hUnderlying :
      IsIso (((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Forget to the ambient homotopy category and use the ordinary derived localization.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.plus 𝒜).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.plus 𝒜).ι.map f)
      (by simpa [boundedBelowHomotopyQuasiIso] using hf)
  have hLifted :
      IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map f)) := by
    -- Transport invertibility across the comparison between the bounded-below lift and the
    -- ambient quotient.
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (t.plus : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_plus)
        f)).2 hUnderlying
  let _ : IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map f)) := hLifted
  exact isIso_of_fully_faithful ιplus (mapBoundedBelowHomotopyToDerivedBelow.map f)

namespace HomotopyResolutionFunctor

/-- Helper for Lemma 13.23.5: the canonical functor from bounded-below injective homotopy objects
to `D^+(\mathcal A)` is full and faithful on morphisms. -/
private theorem boundedBelowInjective_toDerived_map_bijective
    (X Y : K⁺ᵢ(𝒜)) :
    Function.Bijective
      (((boundedBelowInjectiveToDerived (𝒜 := 𝒜)).map :
        (X ⟶ Y) →
          ((boundedBelowInjectiveToDerived (𝒜 := 𝒜)).obj X ⟶
            (boundedBelowInjectiveToDerived (𝒜 := 𝒜)).obj Y))) := by
  let KinjIncl := boundedBelowInjectiveIncl (𝒜 := 𝒜)
  let Q := boundedBelowHomotopyToDerived (𝒜 := 𝒜)
  let IToD := boundedBelowInjectiveToDerived (𝒜 := 𝒜)
  let KplusIncl := (ObjectProperty.ι (HomotopyCategory.plus 𝒜) : K⁺(𝒜) ⥤ _)
  let Qplus := KplusIncl ⋙ DerivedCategory.Qh
  let DplusIncl := (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))) : D⁺(𝒜) ⥤ _)
  -- Proof comment: first forget the injective structure, which is fully faithful by construction.
  have hIncl :
      Function.Bijective
        (KinjIncl.map : (X ⟶ Y) → (X.obj ⟶ Y.obj)) := by
    simpa using (Functor.FullyFaithful.ofFullyFaithful KinjIncl).map_bijective X Y
  -- Proof comment: then compare the bounded-below localization with the ambient derived category.
  have hQ :
      Function.Bijective
        (Q.map : (X.obj ⟶ Y.obj) → (Q.obj X.obj ⟶ Q.obj Y.obj)) := by
    have hAmbient :
        Function.Bijective
          (Qplus.map :
            (X.obj ⟶ Y.obj) → (Qplus.obj X.obj ⟶ Qplus.obj Y.obj)) := by
      have hKplusIncl :
          Function.Bijective
            (KplusIncl.map :
              (X.obj ⟶ Y.obj) → (X.obj.obj ⟶ Y.obj.obj)) := by
        simpa using
          (Functor.FullyFaithful.ofFullyFaithful KplusIncl).map_bijective X.obj Y.obj
      have hQh :
          Function.Bijective
            (DerivedCategory.Qh.map :
              (X.obj.obj ⟶ Y.obj.obj) →
                (DerivedCategory.Qh.obj X.obj.obj ⟶ DerivedCategory.Qh.obj Y.obj.obj)) := by
        let _ : CochainComplex.IsKInjective Y.obj.obj.as :=
          boundedBelowInjectiveHomotopyCat.isKInjective Y
        -- Route correction: use the canonical `Qh_map_bijective` theorem directly after
        -- rebuilding the local K-injective bridge on `K^+(\mathcal I)`.
        simpa using
          CochainComplex.IsKInjective.Qh_map_bijective (K := X.obj.obj) (L := Y.obj.obj.as)
      simpa [Functor.comp_map] using hQh.comp hKplusIncl
    have hDplusIncl :
        Function.Bijective
          (DplusIncl.map :
            (Q.obj X.obj ⟶ Q.obj Y.obj) →
              (DplusIncl.obj (Q.obj X.obj) ⟶ DplusIncl.obj (Q.obj Y.obj))) := by
      simpa using
        (Functor.FullyFaithful.ofFullyFaithful DplusIncl).map_bijective
          (Q.obj X.obj) (Q.obj Y.obj)
    have hcomp :
        DplusIncl.map ∘
            (Q.map : (X.obj ⟶ Y.obj) → (Q.obj X.obj ⟶ Q.obj Y.obj)) =
          (Qplus.map : (X.obj ⟶ Y.obj) → (Qplus.obj X.obj ⟶ Qplus.obj Y.obj)) := by
      funext f
      rfl
    exact (Function.Bijective.of_comp_iff' hDplusIncl _).mp (hcomp ▸ hAmbient)
  simpa [IToD, Functor.comp_map] using hQ.comp hIncl

/-- Helper for Lemma 13.23.5: the comparison quasi-isomorphisms identify direct localization of
`K^+(\mathcal A)` with first resolving and then passing to `D^+(\mathcal A)`. -/
private noncomputable def resolution_to_derived_iso (j : HomotopyResolutionFunctor 𝒜) :
    j.toFunctor ⋙ boundedBelowInjectiveToDerived (𝒜 := 𝒜) ≅
      boundedBelowHomotopyToDerived (𝒜 := 𝒜) := by
  let KinjIncl := boundedBelowInjectiveIncl (𝒜 := 𝒜)
  let Q := boundedBelowHomotopyToDerived (𝒜 := 𝒜)
  let IToD := boundedBelowInjectiveToDerived (𝒜 := 𝒜)
  let τ : Q ⟶ j.toFunctor ⋙ IToD :=
    (Functor.leftUnitor Q).inv ≫ Functor.whiskerRight j.ι Q ≫
      (Functor.associator j.toFunctor KinjIncl Q).hom
  -- Proof comment: each comparison map becomes an isomorphism in the localization because
  -- `j.ι.app X` is a quasi-isomorphism.
  have hτ : ∀ X, IsIso (τ.app X) := by
    intro X
    have hι :
        IsIso ((Functor.whiskerRight j.ι Q).app X) := by
      simpa using
        mapBoundedBelowHomotopyToDerivedBelow_map_isIso (𝒜 := 𝒜) (j.ι.app X) (j.quasiIso_app X)
    change IsIso
      ((Functor.leftUnitor Q).inv.app X ≫
        (Functor.whiskerRight j.ι Q).app X ≫
        (Functor.associator j.toFunctor KinjIncl Q).hom.app X)
    infer_instance
  -- Proof comment: package the objectwise isomorphisms into a natural isomorphism and orient it
  -- so that `Functor.CommShift.ofComp` can pull exactness back to `j.toFunctor`.
  exact (NatIso.ofComponents (fun X ↦ asIso (τ.app X)) (fun f ↦ τ.naturality f)).symm

-- Proof sketch: for each `n : ℤ`, compare the two injective resolutions `j(K⟦n⟧)` and
-- `j(K)⟦n⟧` of the shifted object `K⟦n⟧`. Lemmas 13.18.6 and 13.18.7 give a unique comparison
-- isomorphism compatible with the quasi-isomorphisms from `K⟦n⟧`, and these isomorphisms assemble
-- functorially into a `CommShift ℤ` structure. For a distinguished triangle
-- `(K, L, M, f, g, h)`, the comparison quasi-isomorphisms identify the image triangle
-- `(j(K), j(L), j(M), j(f), j(g), ξ_K ≫ j(h))` with a distinguished triangle in `D^+(\mathcal A)`;
-- Proposition 13.23.1 and Lemma 13.4.18 then imply that it is distinguished already in
-- `K^+(\mathcal I)`.
/-- Lemma 13.23.5: any resolution functor
`j : K^+(\mathcal A) ⥤ K^+(\mathcal I)` is exact, i.e. admits a shift-commuting structure for
which it is triangulated. -/
@[stacks 014W]
theorem toFunctor_exact (j : HomotopyResolutionFunctor 𝒜) :
    ∃ hcomm : j.toFunctor.CommShift ℤ,
      letI : j.toFunctor.CommShift ℤ := hcomm
      j.toFunctor.IsTriangulated := by
  let IToD := boundedBelowInjectiveToDerived (𝒜 := 𝒜)
  let Q := boundedBelowHomotopyToDerived (𝒜 := 𝒜)
  -- Proof comment: the injective-to-derived functor is full and faithful, so we can reflect the
  -- exact structure of the canonical localization functor back to `j.toFunctor`.
  obtain ⟨hFF⟩ : Nonempty IToD.FullyFaithful := by
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro X Y
    exact boundedBelowInjective_toDerived_map_bijective (𝒜 := 𝒜) X Y
  let _ : IToD.Full := hFF.full
  let _ : IToD.Faithful := hFF.faithful
  let e : j.toFunctor ⋙ IToD ≅ Q := resolution_to_derived_iso (𝒜 := 𝒜) j
  -- Proof comment: `Q` already commutes with shift and is triangulated, so pull those structures
  -- back along the comparison isomorphism `e`.
  let hcomm : j.toFunctor.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  refine ⟨hcomm, ?_⟩
  letI : j.toFunctor.CommShift ℤ := hcomm
  letI : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).2 inferInstance

end HomotopyResolutionFunctor

end CategoryTheory
