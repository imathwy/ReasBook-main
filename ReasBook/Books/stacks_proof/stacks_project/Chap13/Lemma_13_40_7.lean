import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.Tactic.StacksAttribute
import StacksProject_2024.Chap13.Lemma_13_35_1
import StacksProject_2024.Chap13.Definition_13_40_1
import StacksProject_2024.Chap13.Lemma_13_40_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

/-- Helper for Lemma 13.40.7: in a distinguished triangle, if the cone term lies in `A^⊥`,
then the first morphism is `A`-colocal. -/
theorem isColocal_mor₁_of_rightOrthogonal_obj₃
    (T : Triangle D) (hT : T ∈ distTriang D) (h₃ : A^⊥ T.obj₃) :
    A.isColocal T.mor₁ := by
  -- Proof comment: rewrite `A^⊥` as Hom-vanishing and run the long exact `coyoneda` sequence.
  rw [A.rightOrthogonal_iff] at h₃
  intro B hB
  constructor
  · intro f₁ f₂ h
    apply sub_eq_zero.mp
    have hsub : (f₁ - f₂) ≫ T.mor₁ = 0 := by
      rw [Preadditive.sub_comp]
      exact sub_eq_zero.mpr h
    have hshift :
        (f₁ - f₂)⟦(1 : ℤ)⟧' ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
      simpa only [Functor.map_sub, Functor.map_zero, Functor.map_comp] using
        congrArg (Functor.map (shiftFunctor D (1 : ℤ))) hsub
    obtain ⟨g, hg⟩ := T.coyoneda_exact₁ hT ((f₁ - f₂)⟦(1 : ℤ)⟧') hshift
    have hg_zero : g = 0 := h₃ g (A.le_shift 1 _ hB)
    have hmap_zero : (f₁ - f₂)⟦(1 : ℤ)⟧' = 0 := by
      simpa [hg_zero] using hg
    exact (shiftFunctor D (1 : ℤ)).map_injective <| by simpa using hmap_zero
  · intro g
    obtain ⟨f, hf⟩ := T.coyoneda_exact₂ hT g (h₃ (g ≫ T.mor₂) hB)
    exact ⟨f, hf.symm⟩

/-- Helper for Lemma 13.40.7: in a distinguished triangle, if the first morphism is
`A`-colocal, then the cone term lies in `A^⊥`. -/
theorem rightOrthogonal_obj₃_of_isColocal_mor₁
    (T : Triangle D) (hT : T ∈ distTriang D) (h₁ : A.isColocal T.mor₁) :
    A^⊥ T.obj₃ := by
  -- Proof comment: use injectivity and surjectivity of postcomposition by `T.mor₁`
  -- on `A` and `A⟦-1⟧` to kill every map into the cone.
  rw [A.rightOrthogonal_iff]
  intro B f hB
  have hinjShift :
      Function.Injective (fun h : B ⟶ T.obj₁⟦(1 : ℤ)⟧ ↦ h ≫ T.mor₁⟦(1 : ℤ)⟧') := by
    intro h₁' h₂' hh
    let adj := (shiftEquiv D (1 : ℤ)).symm.toAdjunction
    let e₁ := adj.homEquiv B T.obj₁
    let e₂ := adj.homEquiv B T.obj₂
    obtain ⟨g₁, rfl⟩ := e₁.surjective h₁'
    obtain ⟨g₂, rfl⟩ := e₁.surjective h₂'
    have hg : g₁ ≫ T.mor₁ = g₂ ≫ T.mor₁ := by
      apply e₂.injective
      change e₂ (g₁ ≫ T.mor₁) = e₂ (g₂ ≫ T.mor₁)
      rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_right]
      exact hh
    have hg' : g₁ = g₂ := (h₁ _ (A.le_shift (-1) _ hB)).1 hg
    change e₁ g₁ = e₁ g₂
    exact congrArg e₁ hg'
  have hf_zero : f ≫ T.mor₃ = 0 := by
    apply hinjShift
    simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) (comp_distTriang_mor_zero₃₁ T hT)
  obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hT f hf_zero
  obtain ⟨k, hk⟩ := (h₁ _ hB).2 g
  rw [hg, ← hk, Category.assoc, comp_distTriang_mor_zero₁₂ _ hT]
  simp

/-- Helper for Lemma 13.40.7: the Hom-equivalence coming from an `A`-colocal first morphism,
transported from the ambient category to the full subcategory `A.FullSubcategory`. -/
noncomputable def distinguished_isColocal_homEquiv
    (T : Triangle D) (h₁ : A T.obj₁) (hcoloc : A.isColocal T.mor₁)
    {W : A.FullSubcategory} :
    (W ⟶ ⟨T.obj₁, h₁⟩) ≃ (((A.ι).op ⋙ yoneda.obj T.obj₂).obj (Opposite.op W)) :=
  (Functor.FullyFaithful.ofFullyFaithful A.ι).homEquiv.trans
    (ObjectProperty.isColocal.homEquiv hcoloc W.obj W.property)

omit [HasZeroObject D] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [A.IsTriangulated] in
/-- Helper for Lemma 13.40.7: the transported colocal Hom-equivalences are natural in the source
object of the full subcategory. -/
theorem distinguished_isColocal_homEquiv_comp
    (T : Triangle D) (h₁ : A T.obj₁) (hcoloc : A.isColocal T.mor₁)
    {W W' : A.FullSubcategory} (f : W ⟶ W') (g : W' ⟶ ⟨T.obj₁, h₁⟩) :
    A.distinguished_isColocal_homEquiv T h₁ hcoloc (f ≫ g) =
      ((A.ι.op ⋙ yoneda.obj T.obj₂).map f.op)
        (A.distinguished_isColocal_homEquiv T h₁ hcoloc g) := by
  -- Proof comment: both sides are the same composite in the ambient category.
  change A.ι.map (f ≫ g) ≫ T.mor₁ = A.ι.map f ≫ (A.ι.map g ≫ T.mor₁)
  simp [Category.assoc]

omit [HasZeroObject D] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [A.IsTriangulated] in
/-- Helper for Lemma 13.40.7: a distinguished triangle with first term in `A` and `A`-colocal
first morphism makes the restricted Yoneda presheaf of the middle term representable. -/
theorem isRepresentable_of_distinguished_isColocal
    (T : Triangle D) (h₁ : A T.obj₁) (hcoloc : A.isColocal T.mor₁) :
    ((A.ι).op ⋙ yoneda.obj T.obj₂).IsRepresentable := by
  -- Proof comment: package the natural Hom-equivalences as a representability witness.
  let hrep :
      ((A.ι).op ⋙ yoneda.obj T.obj₂).RepresentableBy ⟨T.obj₁, h₁⟩ :=
    Functor.RepresentableBy.mk
      (fun {W} ↦ A.distinguished_isColocal_homEquiv T h₁ hcoloc)
      (fun {W W'} f g ↦
        A.distinguished_isColocal_homEquiv_comp T h₁ hcoloc f g)
  exact hrep.isRepresentable

/- Domain-style sampling for Lemma 13.40.7:
- primary domain: admissibility and semi-orthogonal decompositions of triangulated subcategories;
- sampled core/canonical declarations:
  `Functor.rightAdjointObjIsDefined`,
  `Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`,
  `ObjectProperty.extensionProduct`,
  `ObjectProperty.rightOrthogonal`;
- best owner abstraction: the inclusion functor owner `A.ι.rightAdjointObjIsDefined`, whose
  equality with `⊤` is the canonical adjoint-existence criterion for `A.ι`;
- primitive data: the triangulated object property `A` and its inclusion functor `A.ι`;
- derived API: the source-facing extension-product description `A ⋆ A^⊥ = ⊤`, retract stability,
  and the orthogonal-equality corollary under strict fullness;
- source/core/bridge triage:
  `source-facing`: the semi-orthogonal decomposition criterion `A ⋆ A^⊥ = ⊤`;
  `core/canonical`: `A.ι.rightAdjointObjIsDefined` together with
    `Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`;
  `bridge/view`: the identification of `A.ι.rightAdjointObjIsDefined` with
    `A ⋆ A^⊥`.

Primitive data should stay with the inclusion-functor owner. The extension-product condition is a
source-facing bridge theorem, not a second owner for adjointability. -/

-- Proof sketch: for `X : D`, the representability criterion defining
-- `A.ι.rightAdjointObjIsDefined X` is equivalent to the existence of a distinguished triangle
-- `A' ⟶ X ⟶ B ⟶ A'⟦1⟧` with `A A'` and `A^⊥ B`, via Lemma `13.40.2` applied to the universal map
-- representing `Hom_D(A.ι.obj -, X)`.
/-- Bridge theorem for Lemma 13.40.7: the canonical partial-right-adjoint domain of the inclusion
`A.ι` is exactly the extension product `A ⋆ A^⊥`. -/
theorem rightAdjointObjIsDefined_eq_extensionProduct_rightOrthogonal :
    A.ι.rightAdjointObjIsDefined = A ⋆ A^⊥ := by
  ext X
  rw [Functor.rightAdjointObjIsDefined_iff, extensionProduct_iff]
  constructor
  · intro hX
    let F : A.FullSubcategoryᵒᵖ ⥤ Type v := (A.ι.op ⋙ yoneda.obj X)
    let rep := F.representableBy
    let eRep : ∀ {W : A.FullSubcategory}, (W ⟶ F.reprX) ≃ (W.obj ⟶ X) := fun {_} ↦ rep.homEquiv
    let R := F.reprX
    let u : R.obj ⟶ X := eRep (𝟙 R)
    -- Proof comment: complete the universal morphism to a distinguished triangle.
    obtain ⟨B, g, h, hT⟩ := distinguished_cocone_triangle u
    refine ⟨R.obj, B, u, g, h, hT, R.property, ?_⟩
    -- Proof comment: representability identifies postcomposition by `u` with the Hom-bijection.
    have hu : A.isColocal u := by
      intro Y hY
      let Y' : A.FullSubcategory := ⟨Y, hY⟩
      let eFF : (Y' ⟶ R) ≃ (Y ⟶ R.obj) :=
        (Functor.FullyFaithful.ofFullyFaithful A.ι).homEquiv
      let eY : (Y' ⟶ R) ≃ (Y ⟶ X) := eRep
      constructor
      · intro f₁ f₂ h
        have hrepr :
            eY (eFF.symm f₁) = eY (eFF.symm f₂) := by
          have hEq₁ : eRep (eFF.symm f₁) = A.ι.map (eFF.symm f₁) ≫ u := by
            simpa [rep, eRep, u] using
              (Functor.RepresentableBy.homEquiv_eq rep (eFF.symm f₁))
          have hEq₂ : A.ι.map (eFF.symm f₂) ≫ u = eRep (eFF.symm f₂) := by
            simpa [rep, eRep, u] using
              (Functor.RepresentableBy.homEquiv_eq rep (eFF.symm f₂)).symm
          have hm₁ : (eFF.symm f₁).hom = f₁ := by
            simpa [eFF] using eFF.apply_symm_apply f₁
          have hm₂ : (eFF.symm f₂).hom = f₂ := by
            simpa [eFF] using eFF.apply_symm_apply f₂
          have h₁' : eRep (eFF.symm f₁) = f₁ ≫ u := by
            simpa [hm₁] using hEq₁
          have h₂' : f₂ ≫ u = eRep (eFF.symm f₂) := by
            simpa [hm₂] using hEq₂
          exact h₁'.trans (h.trans h₂')
        have hfull : eFF.symm f₁ = eFF.symm f₂ :=
          eY.injective hrepr
        simpa using congrArg eFF hfull
      · intro f
        let g : Y' ⟶ R := eY.symm f
        refine ⟨eFF g, ?_⟩
        have hg : eY g = f := by
          simpa [eY, g] using eY.apply_symm_apply f
        have hEq : eRep g = A.ι.map g ≫ u := by
          simpa [rep, eRep, u] using (Functor.RepresentableBy.homEquiv_eq rep g)
        change eFF g ≫ u = f
        rw [← hg]
        simpa [eFF] using hEq.symm
    exact A.rightOrthogonal_obj₃_of_isColocal_mor₁ (Triangle.mk u g h) hT hu
  · rintro ⟨Y, B, f, g, h, hT, hY, hB⟩
    -- Proof comment: the orthogonal condition turns `f` into the universal morphism
    -- representing `Hom_D(A-, X)`.
    have hf : A.isColocal f :=
      A.isColocal_mor₁_of_rightOrthogonal_obj₃ (Triangle.mk f g h) hT hB
    exact A.isRepresentable_of_distinguished_isColocal (Triangle.mk f g h) hY hf

-- Proof sketch: for `(→)`, let `v` be a chosen right adjoint to the inclusion `A.ι`; for each
-- `X`, complete the counit map `A.ι.obj ((Functor.leftAdjoint A.ι).obj X) ⟶ X` to a distinguished
-- triangle and use Lemma `13.40.2` to identify the cone with an object of `A^⊥`.
-- For `(←)`, use the chosen distinguished triangle for each `X` to define the object part of a
-- right adjoint and use the same bijectivity criterion from Lemma `13.40.2` to define the action
-- on morphisms and prove the adjunction.
/-- Lemma 13.40.7: for a triangulated subcategory `A` of a triangulated category `D`, the
inclusion functor `A.ι : A.FullSubcategory ⥤ D` has a right adjoint if and only if every object of
`D` belongs to the extension product of `A` with its right orthogonal `A^⊥`. The saturation and
strict-full orthogonal-equality consequences are recorded below as corollaries. -/
@[stacks 0CQS]
theorem isLeftAdjoint_iff_extensionProduct_rightOrthogonal_eq_top [IsTriangulated D] :
    A.ι.IsLeftAdjoint ↔ A ⋆ A^⊥ = ⊤ := by
  simpa [A.rightAdjointObjIsDefined_eq_extensionProduct_rightOrthogonal] using
    A.ι.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

/- Proof sketch: the adjoint criterion gives `A ⋆ A^⊥ = ⊤`. The easy inclusion
`A.isoClosure ≤ ^⊥(A^⊥)` is the defining orthogonality of `A^⊥`, transported across the
isomorphism in `isoClosure`. For the converse, decompose `X ∈ ^⊥(A^⊥)` by the extension-product
criterion; the third vertex of the witness triangle lies both in `A^⊥` and `^⊥(A^⊥)`, hence is
zero, so the first morphism is an isomorphism and transports the `A`-object into `A.isoClosure`.
-/
omit [IsTriangulated D] in
/-- Helper for Lemma 13.40.7: if the inclusion of `A` admits a right adjoint, then the strict-full
closure `A.isoClosure` is exactly the left orthogonal `^⊥(A^⊥)`. -/
theorem isoClosure_eq_leftOrthogonal_rightOrthogonal_of_inclusion_isLeftAdjoint
    (hA : A.ι.IsLeftAdjoint) :
    A.isoClosure = ^⊥(A^⊥) := by
  have hTop : A ⋆ A^⊥ = ⊤ :=
    by
      simpa [A.rightAdjointObjIsDefined_eq_extensionProduct_rightOrthogonal] using
        (A.ι.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top).1 hA
  apply le_antisymm
  · intro X hX
    rw [ObjectProperty.prop_isoClosure_iff] at hX
    rw [(A^⊥).leftOrthogonal_iff]
    intro Z f hZ
    rcases hX with ⟨Y, hY, ⟨e⟩⟩
    -- Proof comment: transport the map `f : X ⟶ Z` across the chosen isomorphism `X ≅ Y`
    -- and use the defining vanishing property of `A^⊥` on the `A`-object `Y`.
    calc
      f = e.hom ≫ (e.inv ≫ f) := by simp
      _ = 0 := by rw [hZ (e.inv ≫ f) hY, comp_zero]
  · intro X hX
    have htopX : (A ⋆ A^⊥) X := by
      rw [hTop]
      trivial
    rw [extensionProduct_iff] at htopX
    rcases htopX with ⟨A', B', f, g, h, hT, hA', hB'⟩
    have hA'left : (^⊥(A^⊥)) A' := by
      rw [(A^⊥).leftOrthogonal_iff]
      intro Z k hZ
      exact hZ k hA'
    have hB'left : (^⊥(A^⊥)) B' := by
      -- Proof comment: in the distinguished triangle `A' ⟶ X ⟶ B' ⟶ A'⟦1⟧`, the first two
      -- terms already lie in the left orthogonal, so triangulated closure forces the third term
      -- there as well.
      exact (^⊥(A^⊥)).ext_of_isTriangulatedClosed₃ (Triangle.mk f g h) hT hA'left hX
    have hB'zero : IsZero B' := by
      rw [(A^⊥).leftOrthogonal_iff] at hB'left
      exact (IsZero.iff_id_eq_zero B').2 (hB'left (𝟙 B') hB')
    have hfIso : IsIso f := by
      -- Proof comment: once the third vertex vanishes, the first morphism in a distinguished
      -- triangle is an isomorphism.
      simpa using ((Triangle.mk f g h).isZero₃_iff_isIso₁ hT).1 hB'zero
    letI : IsIso f := hfIso
    -- Proof comment: transport the `A`-membership of the first vertex across the isomorphism
    -- `A' ≅ X`.
    exact A.prop_isoClosure hA' f

-- Proof sketch: by the main equivalence, the hypothesis gives `A ⋆ A^⊥ = ⊤`. Lemma `13.40.5`
-- shows this extension product is triangulated, and Lemma
-- `13.40.4` shows `A^⊥` is stable under retracts; the source then replaces `A` by the strictly
-- full subcategory with the same isomorphism classes, i.e. `A.isoClosure`.
omit [IsTriangulated D] in
/-- Corollary to Lemma 13.40.7: if the inclusion of `A` into `D` admits a right adjoint, then the
strictly full closure of `A`
is saturated, i.e. stable under retracts. This is the Lean translation of the source's step of
replacing `A` by the strictly full subcategory with the same isomorphism classes. -/
@[stacks 0CQS]
theorem isoClosure_isStableUnderRetracts_of_inclusion_isLeftAdjoint
    (hA : A.ι.IsLeftAdjoint) :
    A.isoClosure.IsStableUnderRetracts := by
  -- Route correction: prove the canonical orthogonal equality once and reuse the left-orthogonal
  -- retract-stability instance instead of rebuilding retract arguments directly.
  rw [A.isoClosure_eq_leftOrthogonal_rightOrthogonal_of_inclusion_isLeftAdjoint hA]
  infer_instance

-- Proof sketch: use the main equivalence to obtain, for each `X`, a distinguished triangle
-- `A' ⟶ X ⟶ B ⟶ A'⟦1⟧` with `A A'` and `A^⊥ B`. If `X` lies in the left orthogonal
-- of `A^⊥`, then the map `X ⟶ B` is zero, so Lemma `13.4.11` splits the triangle and
-- strict fullness of `A` transports the resulting isomorphism `A' ≅ X` back into `A`. The reverse
-- inclusion is immediate from the
-- definition of the right orthogonal.
omit [IsTriangulated D] in
/-- Corollary to Lemma 13.40.7: if the inclusion of `A` into `D` has a right adjoint and `A` is strictly full,
then `A`
equals the left orthogonal of its right orthogonal. -/
@[stacks 0CQS]
theorem eq_rightOrthogonal_leftOrthogonal_of_inclusion_isLeftAdjoint
    [A.IsClosedUnderIsomorphisms]
    (hA : A.ι.IsLeftAdjoint) :
    A = ^⊥(A^⊥) := by
  -- Route correction: after identifying `A.isoClosure` with the left orthogonal, strict fullness
  -- collapses `isoClosure` back to `A`.
  simpa [ObjectProperty.isoClosure_eq_self] using
    (A.isoClosure_eq_leftOrthogonal_rightOrthogonal_of_inclusion_isLeftAdjoint hA)

end

end CategoryTheory.ObjectProperty
