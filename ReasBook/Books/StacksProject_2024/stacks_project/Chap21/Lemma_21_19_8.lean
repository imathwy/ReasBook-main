import StacksProject_2024.Chap13.«13_17_1_1»
import StacksProject_2024.Chap18.Lemma_18_5_2
import StacksProject_2024.Chap12.Lemma_12_9_6
import StacksProject_2024.Chap21.Lemma_21_10_1
import StacksProject_2024.Chap21.SiteAbelianSheaf

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.ShortComplex
open AddCommGrpCat.Hom
open Opposite
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 21.19.8:
- sampled owner declarations:
  `ObjectProperty.IsSerreClass`,
  `weakSerreSubcategoryDerivedComparisonFunctor`,
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategoryWithCohomologyIn`;
- best owner abstraction: the source-facing owner is the torsion object property on abelian
  sheaves, and the core/canonical derived-category owner is the Chapter 13 comparison functor for
  weak Serre full subcategories;
- source/core/bridge triage:
  `source-facing`: `torsionAbelianSheafProperty J`;
  `core/canonical`: `weakSerreSubcategoryDerivedComparisonFunctor`;
  `bridge/view`: the specialization of the Chapter 13 unbounded comparison functor to the torsion
    property.

The source theorem `0DD7` is the unbounded comparison statement
`D((torsionAbelianSheafProperty J).FullSubcategory) ⥤ D_{torsionAbelianSheafProperty J}`.
The earlier bounded-above `epi_lift` specialization was not source-faithful, so this file now
keeps the source-facing torsion property, its sectionwise companion API, and the source-facing
specialization theorem asserting that the Chapter 13 comparison functor is an equivalence. The
actual comparison equivalence belongs on the unbounded Chapter 13 owner and must follow the
injective torsion-subcomplex route from the source proof, not the bounded-above `epi_lift`
criterion. -/

/-- The object property on `AddCommGrpCat` consisting of torsion abelian groups. -/
abbrev addCommGrpCatTorsionProperty : ObjectProperty AddCommGrpCat :=
  fun A ↦ AddMonoid.IsTorsion A

/-- Torsion abelian groups form a Serre subcategory of `AddCommGrpCat`. -/
instance addCommGrpCatTorsionProperty_isSerreClass :
    addCommGrpCatTorsionProperty.IsSerreClass where
  exists_zero := by
    refine ⟨AddCommGrpCat.of PUnit, ?_, ?_⟩
    · exact (AddCommGrpCat.isZero_iff_subsingleton).2 inferInstance
    · intro x
      simpa using (IsOfFinAddOrder.zero : IsOfFinAddOrder (0 : PUnit))
  prop_of_mono f _ hY := by
    intro x
    exact
      (Function.Injective.isOfFinAddOrder_iff
        ((AddCommGrpCat.mono_iff_injective f).1 inferInstance)).1
        (hY (f.hom x))
  prop_of_epi f _ hX := by
    exact AddIsTorsion.of_surjective ((AddCommGrpCat.epi_iff_surjective f).1 inferInstance) hX
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    let sf := hom S.f
    let sg := hom S.g
    have hf : Function.Injective sf := (AddCommGrpCat.mono_iff_injective S.f).1 hS.mono_f
    let e : S.X₁ ≃+ ↥sf.range := AddMonoidHom.ofInjective hf
    have hrange : AddMonoid.IsTorsion ↥sf.range := AddIsTorsion.of_surjective e.surjective h₁
    have hrange_eq_ker : sf.range = sg.ker := by
      exact ab_exact_iff_range_eq_ker.1 hS.exact
    exact AddIsTorsion.extension_closed hrange_eq_ker h₃ hrange

/-- The object property on `SiteAbelianSheafCat J` consisting of torsion abelian sheaves, meaning
that every section group is torsion. -/
abbrev torsionAbelianSheafProperty (J : GrothendieckTopology C) :
    ObjectProperty (SiteAbelianSheafCat J) :=
  fun F ↦ ∀ U : C, addCommGrpCatTorsionProperty (F.obj.obj (op U))

namespace torsionAbelianSheafProperty

/-- A sheaf lies in `torsionAbelianSheafProperty J` iff each of its section groups is torsion. -/
@[simp] theorem iff_isTorsion_sections (F : SiteAbelianSheafCat J) :
    torsionAbelianSheafProperty J F ↔
      ∀ U : C, AddMonoid.IsTorsion (F.obj.obj (op U)) :=
  Iff.rfl

/-- Objectwise torsion of sections gives the torsion sheaf property. -/
theorem of_isTorsion_sections {F : SiteAbelianSheafCat J}
    (hF : ∀ U : C, AddMonoid.IsTorsion (F.obj.obj (op U))) :
    torsionAbelianSheafProperty J F :=
  hF

/-- A torsion abelian sheaf has torsion sections over every object of the site. -/
theorem isTorsion_sections {F : SiteAbelianSheafCat J}
    (hF : torsionAbelianSheafProperty J F) (U : C) :
    AddMonoid.IsTorsion (F.obj.obj (op U)) :=
  hF U

end torsionAbelianSheafProperty

/-- Torsion abelian sheaves form a Serre subcategory of `SiteAbelianSheafCat J`. -/
instance torsionAbelianSheafProperty_isSerreClass :
    (torsionAbelianSheafProperty J).IsSerreClass := by
  -- Proof comment: every Serre-class condition is checked sectionwise by evaluating a sheaf on
  -- `U`, where the problem becomes the already-solved torsion Serre property in `AddCommGrpCat`.
  refine
    { exists_zero := ?_
      prop_of_mono := ?_
      prop_of_epi := ?_
      prop_X₂_of_shortExact := ?_ }
  · refine ⟨0, inferInstance, ?_⟩
    -- Proof comment: sections of the zero sheaf are zero groups, hence torsion.
    intro U x
    simpa using (IsOfFinAddOrder.zero : IsOfFinAddOrder (0 : (0 : SiteAbelianSheafCat J).obj.obj
      (op U)))
  · intro X Y f _ hY U
    let evalU : SiteAbelianSheafCat J ⥤ AddCommGrpCat :=
      sheafToPresheaf J AddCommGrpCat.{max u v} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
    -- Proof comment: a monomorphism of sheaves stays injective on sections over `U`.
    exact
      (Function.Injective.isOfFinAddOrder_iff
        ((AddCommGrpCat.mono_iff_injective (evalU.map f)).1 inferInstance)).1
        (hY U)
  · intro X Y f _ hX U
    let evalU : SiteAbelianSheafCat J ⥤ AddCommGrpCat :=
      sheafToPresheaf J AddCommGrpCat.{max u v} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
    -- Proof comment: an epimorphism of sheaves stays surjective on sections over `U`.
    exact
      AddIsTorsion.of_surjective
        ((AddCommGrpCat.epi_iff_surjective (evalU.map f)).1 inferInstance)
        (hX U)
  · intro S hS h₁ h₃ U
    let evalU : SiteAbelianSheafCat J ⥤ AddCommGrpCat :=
      sheafToPresheaf J AddCommGrpCat.{max u v} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
    have hEval : (S.map evalU).ShortExact := by
      -- Proof comment: evaluation preserves the exact row, so the middle section group sits in a
      -- short exact sequence of abelian groups.
      exact ShortComplex.ShortExact.map_of_exact hS evalU
    -- Proof comment: apply the torsion Serre property in `AddCommGrpCat` to the evaluated row.
    simpa [evalU] using
      (addCommGrpCatTorsionProperty_isSerreClass.prop_X₂_of_shortExact
        (S := S.map evalU) hEval (h₁ U) (h₃ U))

/-- Helper for Lemma 21.19.8: the inclusion of torsion abelian sheaves into all abelian sheaves on
`J` is exact. -/
theorem torsionAbelianSheafInclusion_exact :
    exactFunctor (torsionAbelianSheafProperty J).FullSubcategory
      (SiteAbelianSheafCat J) (torsionAbelianSheafProperty J).ι := by
  -- Proof comment: once torsion sheaves are known to form a weak Serre subcategory, exactness of
  -- the inclusion is the generic Chapter 12 consequence for weak Serre full subcategories.
  exact weakSerreSubcategory_inclusion_exact (torsionAbelianSheafProperty J)

/-- Helper for Lemma 21.19.8: the image of a morphism from a torsion abelian sheaf is torsion. -/
private theorem torsionAbelianSheafProperty_image
    {F G : SiteAbelianSheafCat J} (f : F ⟶ G)
    (hF : torsionAbelianSheafProperty J F) :
    torsionAbelianSheafProperty J (imageSubobject f : SiteAbelianSheafCat J) := by
  -- Proof comment: the canonical map `F ⟶ image(f)` is epi, and the torsion property is stable
  -- under quotients by the Serre-class structure proved above.
  exact
    (torsionAbelianSheafProperty_isSerreClass (J := J)).prop_of_epi
      (factorThruImageSubobject f) hF

/-- Helper for Lemma 21.19.8: torsion of sections is preserved under isomorphisms of abelian
sheaves. -/
private theorem torsionAbelianSheafProperty_of_iso
    {F G : SiteAbelianSheafCat J} (e : F ≅ G)
    (hF : torsionAbelianSheafProperty J F) :
    torsionAbelianSheafProperty J G := by
  -- Proof comment: evaluate the sheaf isomorphism on sections over `U`; the resulting surjective
  -- homomorphism carries torsion of `F(U)` to torsion of `G(U)`.
  intro U
  exact
    AddIsTorsion.of_surjective
      ((AddCommGrpCat.epi_iff_surjective (e.hom.app (op U))).1 inferInstance)
      (hF U)

/-- Helper for Lemma 21.19.8: canonical subquotients of torsion subobjects are torsion sheaves. -/
private theorem torsionAbelianSheafProperty_subobjectSubquotient
    {F : SiteAbelianSheafCat J} {X Y : Subobject F} (hXY : X ≤ Y)
    (hY : torsionAbelianSheafProperty J (Y : SiteAbelianSheafCat J)) :
    torsionAbelianSheafProperty J (subobjectSubquotient hXY : SiteAbelianSheafCat J) := by
  let e :
      (imageSubobject (Y.arrow ≫ cokernel.π X.arrow) : SiteAbelianSheafCat J) ≅
        subobjectSubquotient hXY :=
    Subobject.isoOfEq _ _
      (Subobject.image_subobject_toQuotient_eq_subobjectSubquotient (A := F) hXY)
  have himage :
      torsionAbelianSheafProperty J
        (imageSubobject (Y.arrow ≫ cokernel.π X.arrow) : SiteAbelianSheafCat J) := by
    -- Proof comment: the canonical subquotient is represented as an image inside `F / X`, so the
    -- existing image-stability lemma applies directly.
    exact torsionAbelianSheafProperty_image (Y.arrow ≫ cokernel.π X.arrow) hY
  -- Proof comment: transport torsion across the canonical identification of `Y / X` with that
  -- image subobject.
  exact torsionAbelianSheafProperty_of_iso (J := J) e himage

/-- Helper for Lemma 21.19.8: morphisms from the free abelian representable presheaf on `U`
identify with sections over `U`. -/
private noncomputable def freeAbelianRepresentableHomEquivSections
    (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P) ≃ P.obj (op U) :=
  ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv

/-- Helper for Lemma 21.19.8: precomposition with the free abelian representable map induced by
`i : V ⟶ U` matches restriction on sections. -/
private theorem freeAbelianRepresentableHomEquivSections_naturality
    {U V : C} (i : V ⟶ U) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (f : ((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P) :
    freeAbelianRepresentableHomEquivSections V P
        ((Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) ≫ f) =
      P.map i.op (freeAbelianRepresentableHomEquivSections U P f) := by
  -- Proof comment: after unfolding the two equivalences, both sides evaluate the same natural
  -- transformation at the identity morphism of `V`.
  change
    yonedaEquiv
        (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
          ((Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) ≫ f)) =
      P.map i.op
        (yonedaEquiv (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) f))
  have hpre :
      ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
          ((Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) ≫ f) =
        yoneda.map i ≫
          (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) f) := by
    simpa using
      (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left (yoneda.map i) f
  rw [hpre]
  simpa using
    (yonedaEquiv_naturality
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) f) i).symm

/-- Helper for Lemma 21.19.8: if `i : V ⟶ U` is mono, then the induced map between free abelian
representable presheaves is mono. -/
private theorem freeAbelianRepresentableMap_mono_of_mono
    {U V : C} (i : V ⟶ U) [Mono i] :
    Mono ((Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free :
      ((yoneda.obj V) ⋙ AddCommGrpCat.free) ⟶ ((yoneda.obj U) ⋙ AddCommGrpCat.free))) := by
  -- Proof comment: evaluate objectwise and reduce monomorphy to injectivity of the induced map on
  -- free abelian groups, using a left inverse on generators.
  classical
  refine (NatTrans.mono_iff_mono_app _).2 ?_
  intro W
  rw [AddCommGrpCat.mono_iff_injective]
  let f : (W.unop ⟶ V) → (W.unop ⟶ U) := fun g ↦ g ≫ i
  have hf : Function.Injective f := by
    intro g g' hgg'
    exact (cancel_mono i).1 hgg'
  intro x y hxy
  let r : (W.unop ⟶ U) → FreeAbelianGroup (W.unop ⟶ V) := fun h ↦
    if hh : ∃ g : W.unop ⟶ V, f g = h then FreeAbelianGroup.of (Classical.choose hh) else 0
  have hr : ∀ g : W.unop ⟶ V, r (f g) = FreeAbelianGroup.of g := by
    intro g
    dsimp [r]
    split_ifs with hh
    · apply congrArg FreeAbelianGroup.of
      exact hf (Classical.choose_spec hh)
    · exact (hh ⟨g, rfl⟩).elim
  have hmap :
      Function.LeftInverse (FreeAbelianGroup.lift r) (AddCommGrpCat.free.map f) := by
    intro z
    change FreeAbelianGroup.lift r (FreeAbelianGroup.map f z) = z
    rw [← FreeAbelianGroup.lift_comp f r z]
    have hrf : r ∘ f = FreeAbelianGroup.of := by
      ext g
      exact hr g
    rw [hrf]
    simpa [FreeAbelianGroup.map] using (FreeAbelianGroup.map_id_apply z)
  exact hmap.injective hxy

/-- Helper for Lemma 21.19.8: for an injective abelian presheaf, restriction along a monomorphism
in the base category is surjective on sections. -/
private theorem injectivePresheafSectionsSurjectiveOfMono
    {U V : C} (i : V ⟶ U) [Mono i]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (hP : Injective P) :
    Function.Surjective (P.map i.op) := by
  letI : Injective P := hP
  let m :
      ((yoneda.obj V) ⋙ AddCommGrpCat.free) ⟶
        ((yoneda.obj U) ⋙ AddCommGrpCat.free) :=
    Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free
  let _ : Mono m := freeAbelianRepresentableMap_mono_of_mono i
  intro s
  let fs :
      ((yoneda.obj V) ⋙ AddCommGrpCat.free) ⟶ P :=
    (freeAbelianRepresentableHomEquivSections V P).symm s
  let t :
      ((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P :=
    Injective.factorThru fs m
  refine ⟨freeAbelianRepresentableHomEquivSections U P t, ?_⟩
  -- Proof comment: convert the factorization identity back into a restriction identity on
  -- sections via the representable/sections equivalence.
  calc
    P.map i.op (freeAbelianRepresentableHomEquivSections U P t) =
        freeAbelianRepresentableHomEquivSections V P (m ≫ t) := by
          symm
          simpa [m] using
            freeAbelianRepresentableHomEquivSections_naturality i P t
    _ = freeAbelianRepresentableHomEquivSections V P fs := by
          simpa [t] using (Injective.comp_factorThru fs m)
    _ = s := by
          simp [fs]

/-- Helper for Lemma 21.19.8: injective abelian sheaves have surjective restriction maps on
sections along monomorphisms in the site. -/
private theorem injectiveSheafSectionsSurjectiveOfMono
    {U V : C} (i : V ⟶ U) [Mono i]
    (ℐ : SiteAbelianSheafCat J) (hℐ : Injective ℐ) :
    Function.Surjective (ℐ.obj.map i.op) := by
  -- Proof comment: forget to the underlying abelian presheaf, where injectivity is preserved by
  -- Lemma `21.10.1`, and apply the presheaf-level extension argument.
  simpa using
    injectivePresheafSectionsSurjectiveOfMono i
      ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj ℐ)
      (injective_underlying_abelian_presheaf ℐ hℐ)

section FreeAbelianSheafifiedRepresentable

variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]

/-- Helper for Lemma 21.19.8: applying `presheafToSheaf` to multiplication by `n` on the free
abelian presheaf gives multiplication by `n` on the free abelian sheafified representable. -/
private theorem freeAbelianSheafifiedRepresentable_zsmul_eq_presheafToSheaf_map
    (U : C) (n : ℤ) :
    n • 𝟙 ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J]) =
      (presheafToSheaf J AddCommGrpCat.{max u v}).map
        (n • 𝟙
          (Functor.whiskerRight
            ((sheafToPresheaf J (Type (max u v))).obj h[U]^#[J])
            AddCommGrpCat.free)) := by
  -- Proof comment: `composeAndSheafify` is `sheafToPresheaf ⋙ whiskerRight free ⋙ presheafToSheaf`,
  -- so the claim is just functoriality of `presheafToSheaf` with respect to `zsmul`.
  simp [Sheaf.composeAndSheafify, Functor.map_zsmul]

/-- Helper for Lemma 21.19.8: multiplication by a nonzero integer on the free abelian sheafified
representable is a monomorphism. -/
private theorem freeAbelianSheafifiedRepresentable_zsmul_mono
    (U : C) (n : ℤ) (hn : n ≠ 0) :
    Mono (n • 𝟙 ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J])) := by
  let P :=
    Functor.whiskerRight
      ((sheafToPresheaf J (Type (max u v))).obj h[U]^#[J])
      AddCommGrpCat.free
  have hPmono : Mono (n • 𝟙 P) := by
    -- Proof comment: objectwise this is multiplication by `n` on a free abelian group, hence
    -- injective because `n ≠ 0`.
    refine (NatTrans.mono_iff_mono_app _).2 ?_
    intro V
    rw [AddCommGrpCat.mono_iff_injective]
    exact smul_right_injective ℤ hn
  letI : Mono (n • 𝟙 P) := hPmono
  let F := presheafToSheaf J AddCommGrpCat.{max u v}
  let hExact : exactFunctor _ _ F :=
    (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩
  letI : PreservesFiniteLimits F := (exactFunctor_iff F).1 hExact |>.1
  rw [freeAbelianSheafifiedRepresentable_zsmul_eq_presheafToSheaf_map (J := J) U n]
  exact F.map_mono (n • 𝟙 P)

/-- Helper for Lemma 21.19.8: in the cokernel of multiplication by `n`, multiplication by `n`
vanishes on the quotient. -/
private theorem zsmul_cokernel_eq_zero
    (A : SiteAbelianSheafCat J) (n : ℤ) :
    n • 𝟙 (cokernel (n • 𝟙 A)) = 0 := by
  -- Proof comment: postcompose with the cokernel projection; the result is the cokernel relation
  -- `n • 𝟙 ≫ π = 0`, and the projection is epi.
  apply (cancel_epi (cokernel.π (n • 𝟙 A))).1
  calc
    cokernel.π (n • 𝟙 A) ≫ (n • 𝟙 (cokernel (n • 𝟙 A))) =
        n • cokernel.π (n • 𝟙 A) := by
          simp [Preadditive.comp_zsmul]
    _ = 0 := by
          simpa [Preadditive.zsmul_comp] using (cokernel.condition (n • 𝟙 A))

/-- Helper for Lemma 21.19.8: the cokernel of multiplication by a positive integer on the free
abelian sheafified representable is a torsion sheaf, in fact killed by that integer. -/
private theorem freeAbelianSheafifiedRepresentableCokernel_isTorsion
    (U : C) (n : ℕ+) :
    torsionAbelianSheafProperty J
      (cokernel (((n : ℕ+) : ℤ) •
        𝟙 ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J]))) := by
  let A := (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J]
  let B := cokernel (((n : ℕ+) : ℤ) • 𝟙 A)
  have hz : (((n : ℕ+) : ℤ) • 𝟙 B) = 0 := by
    -- Proof comment: the previous cokernel lemma specializes directly to the free sheafified
    -- representable source object.
    simpa [A, B] using zsmul_cokernel_eq_zero (J := J) A (((n : ℕ+) : ℤ))
  intro V s
  refine ⟨n, ?_⟩
  have hs :
      ((((n : ℕ+) : ℤ) • 𝟙 B).hom.app (op V)) s = 0 := by
    -- Proof comment: evaluate the vanishing endomorphism on the chosen local section.
    simpa [hz]
  -- Proof comment: evaluation turns multiplication-by-`n` on the sheaf into multiplication-by-`n`
  -- on the section group.
  simpa [B] using hs

/-- Helper for Lemma 21.19.8: the free-abelian sheafified-representable Hom/sections equivalence
is natural in the codomain sheaf. -/
private theorem freeAbelianSheafifiedRepresentableHomEquivSections_naturality_right
    (U : C) {𝒜 ℬ : SiteAbelianSheafCat J} (f : 𝒜 ⟶ ℬ)
    (α : (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J] ⟶ 𝒜) :
    freeAbelianSheafifiedRepresentableHomEquivSections J U ℬ (α ≫ f) =
      f.hom.app (op U)
        (freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 α) := by
  let β : h[U]^#[J] ⟶ (sheafForget J).obj 𝒜 :=
    (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[U]^#[J] 𝒜 α
  -- Proof comment: rewrite through the sheaf adjunction, then use the standard right naturality
  -- of `uliftSheafifiedRepresentableHomEquiv`.
  change
    J.uliftSheafifiedRepresentableHomEquiv ((sheafForget J).obj ℬ) U
      (((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[U]^#[J] ℬ) (α ≫ f)) =
      _
  rw [show
      ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[U]^#[J] ℬ) (α ≫ f) =
        β ≫ (sheafForget J).map f by
          dsimp [β]
          exact (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv_naturality_right
            f α]
  simpa [β] using
    J.uliftSheafifiedRepresentableHomEquiv_comp ((sheafForget J).map f) β

/-- Helper for Lemma 21.19.8: precomposition by multiplication with `n` on the free abelian
sheafified representable corresponds to multiplication by `n` on sections. -/
private theorem freeAbelianSheafifiedRepresentableHomEquivSections_zsmul
    (U : C) (𝒜 : SiteAbelianSheafCat J)
    (α : (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J] ⟶ 𝒜)
    (n : ℤ) :
    freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜
        ((n • 𝟙 _) ≫ α) =
      n • freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 α := by
  -- Proof comment: move the `zsmul` from the source to the codomain using preadditivity, then
  -- apply the codomain naturality lemma and evaluate the resulting endomorphism on sections.
  calc
    freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 ((n • 𝟙 _) ≫ α) =
        freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 (α ≫ (n • 𝟙 𝒜)) := by
          simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    _ = (n • 𝟙 𝒜).hom.app (op U)
          (freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 α) := by
          simpa using
            freeAbelianSheafifiedRepresentableHomEquivSections_naturality_right
              (J := J) U (n • 𝟙 𝒜) α
    _ = n • freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜 α := by
          simp

/-- Helper for Lemma 21.19.8: sections of an injective abelian sheaf are divisible by every
nonzero integer. -/
private theorem injectiveSheafSectionsDivisible
    (ℐ : SiteAbelianSheafCat J) (hℐ : Injective ℐ)
    (U : C) (n : ℤ) (hn : n ≠ 0) :
    Function.Surjective (fun s : ℐ.obj.obj (op U) ↦ n • s) := by
  letI : Injective ℐ := hℐ
  let A := (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J]
  let m : A ⟶ A := n • 𝟙 A
  letI : Mono m := freeAbelianSheafifiedRepresentable_zsmul_mono (J := J) U n hn
  intro s
  let γ : A ⟶ ℐ := (freeAbelianSheafifiedRepresentableHomEquivSections J U ℐ).symm s
  let δ : A ⟶ ℐ := Injective.factorThru γ m
  refine ⟨freeAbelianSheafifiedRepresentableHomEquivSections J U ℐ δ, ?_⟩
  have hδ : m ≫ δ = γ := by
    simpa [m, δ] using Injective.comp_factorThru γ m
  -- Proof comment: the factorization `m ≫ δ = γ` says exactly that the new section maps to `s`
  -- under multiplication by `n` once we translate through the Hom/sections equivalence.
  calc
    n • freeAbelianSheafifiedRepresentableHomEquivSections J U ℐ δ =
        freeAbelianSheafifiedRepresentableHomEquivSections J U ℐ (m ≫ δ) := by
          symm
          simpa [m] using
            freeAbelianSheafifiedRepresentableHomEquivSections_zsmul
              (J := J) U ℐ δ n
    _ = freeAbelianSheafifiedRepresentableHomEquivSections J U ℐ γ := by
          rw [hδ]
    _ = s := by
          simp [γ]

end FreeAbelianSheafifiedRepresentable

/-- Helper for Lemma 21.19.8: once the comparison functor has a right adjoint whose unit and
counit are objectwise isomorphisms, the comparison functor is an equivalence. -/
private theorem weakSerreSubcategoryDerivedComparisonFunctor_isEquivalence_of_adjunction
    (P : ObjectProperty (SiteAbelianSheafCat J)) [P.IsWeakSerreClass]
    (G : DerivedCategoryWithCohomologyIn P ⥤ DerivedCategory P.FullSubcategory)
    (adj : CategoryTheory.weakSerreSubcategoryDerivedComparisonFunctor P ⊣ G)
    (hunit : ∀ K : DerivedCategory P.FullSubcategory, IsIso (adj.unit.app K))
    (hcounit : ∀ K : DerivedCategoryWithCohomologyIn P,
      IsIso (adj.counit.app K)) :
    Functor.IsEquivalence
      (CategoryTheory.weakSerreSubcategoryDerivedComparisonFunctor P) := by
  -- Proof comment: the objectwise unit/counit isomorphisms are exactly the quasi-inverse data
  -- required by `Functor.IsEquivalence.mk'`.
  letI : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  letI : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  exact Functor.IsEquivalence.mk' G (asIso adj.unit) (asIso adj.counit)

-- Proof sketch: specialize the Chapter 13 unbounded comparison theorem to the Serre subcategory
-- of torsion abelian sheaves on `J`.
/-- Lemma 21.19.8: the canonical comparison functor from the derived category of torsion abelian
sheaves to the full subcategory of `D(SiteAbelianSheafCat J)` with torsion cohomology sheaves is
an equivalence. -/
@[stacks 0DD7]
theorem torsionAbelianSheafDerivedComparisonFunctor_isEquivalence :
    Functor.IsEquivalence
      (CategoryTheory.weakSerreSubcategoryDerivedComparisonFunctor
        (torsionAbelianSheafProperty J)) := by
  -- Route correction: the source-proof divisibility step is now available through
  -- `injectiveSheafSectionsDivisible`, and the quotient side of the Step 1 subobject calculus is
  -- now isolated in `torsionAbelianSheafProperty_subobjectSubquotient`, while the bounded-exponent
  -- generator quotient is available as
  -- `freeAbelianSheafifiedRepresentableCokernel_isTorsion`. The remaining blocker is no longer the
  -- Step 1 torsion-generator package, but the complex-level adjunction package: one still has to
  -- build the termwise torsion subcomplex right adjoint on cochain complexes, derive it, and
  -- identify the derived counit on torsion-cohomology K-injective representatives with the
  -- torsion-subcomplex inclusion.
  -- TODO: instantiate the formal helper
  -- `weakSerreSubcategoryDerivedComparisonFunctor_isEquivalence_of_adjunction` with the derived
  -- torsion coreflector once that right-adjoint/counit package is available.
  sorry

instance instTorsionAbelianSheafDerivedComparisonFunctorIsEquivalence :
    Functor.IsEquivalence
      (CategoryTheory.weakSerreSubcategoryDerivedComparisonFunctor
        (torsionAbelianSheafProperty J)) :=
  torsionAbelianSheafDerivedComparisonFunctor_isEquivalence

end

end CategoryTheory.Sheaf
