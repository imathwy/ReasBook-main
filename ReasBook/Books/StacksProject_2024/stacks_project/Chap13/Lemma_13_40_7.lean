import Mathlib
import StacksProject_2024.Chap13.Lemma_13_35_1
import StacksProject_2024.Chap13.Definition_13_40_1

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
    (ObjectProperty.isColocal.homEquiv (P := A) hcoloc W.obj W.property)

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [A.IsTriangulated] in
/-- Helper for Lemma 13.40.7: the transported colocal Hom-equivalences are natural in the source
object of the full subcategory. -/
theorem distinguished_isColocal_homEquiv_comp
    (T : Triangle D) (h₁ : A T.obj₁) (hcoloc : A.isColocal T.mor₁)
    {W W' : A.FullSubcategory} (f : W ⟶ W') (g : W' ⟶ ⟨T.obj₁, h₁⟩) :
    distinguished_isColocal_homEquiv (A := A) T h₁ hcoloc (f ≫ g) =
      ((A.ι.op ⋙ yoneda.obj T.obj₂).map f.op)
        (distinguished_isColocal_homEquiv (A := A) T h₁ hcoloc g) := by
  -- Proof comment: both sides are the same composite in the ambient category.
  change A.ι.map (f ≫ g) ≫ T.mor₁ = A.ι.map f ≫ (A.ι.map g ≫ T.mor₁)
  simp [Category.assoc]

/-- Helper for Lemma 13.40.7: a distinguished triangle with first term in `A` and `A`-colocal
first morphism makes the restricted Yoneda presheaf of the middle term representable. -/
theorem isRepresentable_of_distinguished_isColocal
    (T : Triangle D) (h₁ : A T.obj₁) (hcoloc : A.isColocal T.mor₁) :
    ((A.ι).op ⋙ yoneda.obj T.obj₂).IsRepresentable := by
  -- Proof comment: package the natural Hom-equivalences as a representability witness.
  let hrep :
      ((A.ι).op ⋙ yoneda.obj T.obj₂).RepresentableBy ⟨T.obj₁, h₁⟩ :=
    Functor.RepresentableBy.mk
      (fun {W} ↦ distinguished_isColocal_homEquiv (A := A) T h₁ hcoloc)
      (fun {W W'} f g ↦
        distinguished_isColocal_homEquiv_comp (A := A) T h₁ hcoloc f g)
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
    let R := F.reprX
    let u : R.obj ⟶ X := F.representableBy.homEquiv (𝟙 R)
    -- Proof comment: complete the universal morphism to a distinguished triangle.
    obtain ⟨B, g, h, hT⟩ := distinguished_cocone_triangle u
    refine ⟨R.obj, B, u, g, h, hT, R.property, ?_⟩
    -- Proof comment: representability identifies postcomposition by `u` with the Hom-bijection.
    have hu : A.isColocal u := by
      intro Y hY
      let Y' : A.FullSubcategory := ⟨Y, hY⟩
      let eFF : (Y' ⟶ R) ≃ (Y ⟶ R.obj) :=
        (Functor.FullyFaithful.ofFullyFaithful A.ι).homEquiv
      constructor
      · intro f₁ f₂ h
        have hrepr :
            F.representableBy.homEquiv (eFF.symm f₁) =
              F.representableBy.homEquiv (eFF.symm f₂) := by
          have hEq₁ := Functor.RepresentableBy.homEquiv_eq F.representableBy (eFF.symm f₁)
          have hEq₂ := Functor.RepresentableBy.homEquiv_eq F.representableBy (eFF.symm f₂)
          have hEq₁' : F.representableBy.homEquiv (eFF.symm f₁) = A.ι.map (eFF.symm f₁) ≫ u := by
            change F.representableBy.homEquiv (eFF.symm f₁) = A.ι.map (eFF.symm f₁) ≫ u
            simpa [u] using hEq₁
          have hEq₂' : A.ι.map (eFF.symm f₂) ≫ u = F.representableBy.homEquiv (eFF.symm f₂) := by
            change A.ι.map (eFF.symm f₂) ≫ u = F.representableBy.homEquiv (eFF.symm f₂)
            simpa [u] using hEq₂.symm
          have hm₁ : (eFF.symm f₁).hom = f₁ := by
            simpa [eFF] using eFF.apply_symm_apply f₁
          have hm₂ : (eFF.symm f₂).hom = f₂ := by
            simpa [eFF] using eFF.apply_symm_apply f₂
          have h₁' : F.representableBy.homEquiv (eFF.symm f₁) = f₁ ≫ u := by
            simpa [hm₁] using hEq₁'
          have h₂' : f₂ ≫ u = F.representableBy.homEquiv (eFF.symm f₂) := by
            simpa [hm₂] using hEq₂'
          exact h₁'.trans (h.trans h₂')
        have hfull : eFF.symm f₁ = eFF.symm f₂ :=
          F.representableBy.homEquiv.injective hrepr
        simpa using congrArg eFF hfull
      · intro f
        let g : Y' ⟶ R := F.representableBy.homEquiv.symm f
        refine ⟨eFF g, ?_⟩
        have hg : F.representableBy.homEquiv g = f :=
          by simpa [g] using F.representableBy.homEquiv.apply_symm_apply f
        have hEq := Functor.RepresentableBy.homEquiv_eq F.representableBy g
        change eFF g ≫ u = f
        rw [← hg]
        simpa [u, eFF] using hEq.symm
    exact A.rightOrthogonal_obj₃_of_isColocal_mor₁ (Triangle.mk u g h) hT hu
  · rintro ⟨Y, B, f, g, h, hT, hY, hB⟩
    -- Proof comment: the orthogonal condition turns `f` into the universal morphism
    -- representing `Hom_D(A-, X)`.
    have hf : A.isColocal f :=
      A.isColocal_mor₁_of_rightOrthogonal_obj₃ (Triangle.mk f g h) hT hB
    exact isRepresentable_of_distinguished_isColocal (A := A) (Triangle.mk f g h) hY hf

-- Proof sketch: for `(→)`, let `v` be a chosen right adjoint to the inclusion `A.ι`; for each
-- `X`, complete the counit map `A.ι.obj ((Functor.leftAdjoint A.ι).obj X) ⟶ X` to a distinguished
-- triangle and use Lemma `13.40.2` to identify the cone with an object of `A^⊥`.
-- For `(←)`, use the chosen distinguished triangle for each `X` to define the object part of a
-- right adjoint and use the same bijectivity criterion from Lemma `13.40.2` to define the action
-- on morphisms and prove the adjunction.
/-- Lemma 13.40.7: for a triangulated subcategory `A` of a pretriangulated category `D`, the
inclusion functor `A.ι : A.FullSubcategory ⥤ D` has a right adjoint if and only if every object of
`D` belongs to the extension product of `A` with its right orthogonal `A^⊥`. -/
theorem isLeftAdjoint_iff_extensionProduct_rightOrthogonal_eq_top :
    A.ι.IsLeftAdjoint ↔ A ⋆ A^⊥ = ⊤ := by
  simpa [A.rightAdjointObjIsDefined_eq_extensionProduct_rightOrthogonal] using
    A.ι.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

-- Proof sketch: by the main equivalence, the hypothesis gives `A ⋆ A^⊥ = ⊤`. Lemma `13.40.5`
-- shows this extension product is triangulated, and Lemma
-- `13.40.4` shows `A^⊥` is stable under retracts; then the textbook argument implies
-- that `A` itself is stable under retracts.
/-- If the inclusion of `A` into `D` admits a right adjoint, then `A` is saturated, i.e. stable
under retracts. -/
theorem isStableUnderRetracts_of_inclusion_isLeftAdjoint
    (hA : A.ι.IsLeftAdjoint) :
    A.IsStableUnderRetracts := by
  -- TODO: the source proof only forces the chosen retract object into `A.isoClosure`.
  -- In the current encoding, `A` is not assumed strictly full / closed under isomorphisms, so
  -- the final step from `A.isoClosure X` to `A X` is unavailable.
  sorry

-- Proof sketch: use the main equivalence to obtain, for each `X`, a distinguished triangle
-- `A' ⟶ X ⟶ B ⟶ A'⟦1⟧` with `A A'` and `A^⊥ B`. If `X` lies in the left orthogonal
-- of `A^⊥`, then the map `X ⟶ B` is zero, so Lemma `13.4.11` splits the triangle and
-- saturation from `hA` gives strict fullness of `A`, forcing `X` to lie in `A`. The reverse
-- inclusion is immediate from the
-- definition of the right orthogonal.
/-- If the inclusion of `A` into `D` has a right adjoint, then `A` equals the left orthogonal of
its right orthogonal. -/
theorem eq_rightOrthogonal_leftOrthogonal_of_inclusion_isLeftAdjoint
    (hA : A.ι.IsLeftAdjoint) :
    A = ^⊥(A^⊥) := by
  -- TODO: the reverse inclusion requires the strict-full conclusion from the source text.
  -- Without an explicit `A.IsClosedUnderIsomorphisms` hypothesis, the split-triangle argument
  -- again only yields membership in `A.isoClosure`.
  sorry

end

end CategoryTheory.ObjectProperty
