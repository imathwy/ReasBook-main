import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import StacksProject_2024.stacks_project.Chap12.Definition_12_6_2

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

namespace CategoryTheory
namespace ExtensionClass

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A A' B B' : C}

/-
Domain triage: this item lies in the abelian-category `Ext¹` classification domain for short exact
sequences.

Sampled owner-style declarations:
* `inferInstance : AddCommGroup (Ext B A 1)`
* `(Ext.mk₀ u).precomp A (zero_add 1) : Ext B A 1 →+ Ext B' A 1`
* `(Ext.mk₀ a).postcomp B (add_zero 1) : Ext B A 1 →+ Ext B A' 1`
* `ExtensionClass.toExt_add`, `ExtensionClass.toExt_pullback`, and `ExtensionClass.toExt_pushout`

Layering for this item:
* source-facing: `ExtensionClass A B` with Baer sum, split extension, pullback, and pushout;
* core/canonical: `Ext B A 1` with its additive structure and first/second-variable maps;
* bridge/view: `ExtensionClass.toExt`.

This file targets the `source-facing` layer: it upgrades the source-facing operations to the
commutative-group and additive-functorial structure stated in Lemma 12.6.3, while reusing the
canonical owner `Ext¹` through `toExt`.
-/

noncomputable instance : Sub (ExtensionClass A B) where
  sub ξ η := ξ + -η

noncomputable instance : SMul ℕ (ExtensionClass A B) where
  smul n ξ := nsmulRec n ξ

noncomputable instance : SMul ℤ (ExtensionClass A B) where
  smul := zsmulRec nsmulRec

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {A A' B B' : C}

@[simp] theorem toExt_sub (ξ η : ExtensionClass A B) : toExt (ξ - η) = toExt ξ - toExt η := by
  change toExt (ξ + -η) = toExt ξ - toExt η
  simp [sub_eq_add_neg, toExt_add, toExt_neg]

@[simp] theorem toExt_nsmul (ξ : ExtensionClass A B) (n : ℕ) : toExt (n • ξ) = n • toExt ξ := by
  induction n with
  | zero =>
      change toExt 0 = 0 • toExt ξ
      rw [zero_nsmul]
      exact toExt_zero
  | succ n ih =>
      change toExt (nsmulRec n ξ + ξ) = (n + 1) • toExt ξ
      rw [toExt_add, succ_nsmul]
      simpa [HSMul.hSMul] using congrArg (fun x ↦ x + toExt ξ) ih

@[simp] theorem toExt_zsmul (ξ : ExtensionClass A B) (n : ℤ) : toExt (n • ξ) = n • toExt ξ := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, natCast_zsmul]
      exact toExt_nsmul ξ n
  | negSucc n =>
      change toExt (-(nsmulRec (n + 1) ξ)) = (Int.negSucc n) • toExt ξ
      rw [toExt_neg, negSucc_zsmul]
      simpa [HSMul.hSMul] using congrArg Neg.neg (toExt_nsmul ξ (n + 1))

/-- Helper for Lemma 12.6.3: equal `Ext¹` classes force the corresponding source-facing
extensions to be endpoint-fixing isomorphic. -/
lemma extension_isomorphic_of_extClass_eq {S T : Extension A B}
    (h : S.extClass = T.extClass) : Extension.Isomorphic S T := by
  letI := HasDerivedCategory.standard C
  let hff : (DerivedCategory.singleFunctor C 0).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor C 0)
  -- Compare the connecting morphisms of the canonical distinguished triangles.
  have hδ : S.shortExact.singleδ = T.shortExact.singleδ := by
    have hhom : S.extClass.hom = T.extClass.hom := by simpa using congrArg Ext.hom h
    rw [S.shortExact.extClass_hom, T.shortExact.extClass_hom] at hhom
    exact hhom
  have hcomm₃ :
      S.shortExact.singleδ ≫
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
            (Iso.refl ((DerivedCategory.singleFunctor C 0).obj A)).hom =
        (Iso.refl ((DerivedCategory.singleFunctor C 0).obj B)).hom ≫ T.shortExact.singleδ := by
    simpa using hδ
  -- Uniqueness of distinguished triangles with fixed endpoints and third morphism gives an
  -- isomorphism on the middle terms.
  let eTriangle :=
    Pretriangulated.isoTriangleOfIso₁₃ S.shortExact.singleTriangle T.shortExact.singleTriangle
      S.shortExact.singleTriangle_distinguished T.shortExact.singleTriangle_distinguished
      (Iso.refl ((DerivedCategory.singleFunctor C 0).obj A))
      (Iso.refl ((DerivedCategory.singleFunctor C 0).obj B)) hcomm₃
  let eMid : S.E ≅ T.E := hff.preimageIso (Pretriangulated.Triangle.π₂.mapIso eTriangle)
  refine ⟨eMid, ?_, ?_⟩
  · -- The first structure map is preserved after pulling the middle-term isomorphism back to `C`.
    apply hff.map_injective
    have hcomm₁ := eTriangle.hom.comm₁
    simpa [eMid, Functor.map_comp] using hcomm₁
  · -- The second structure map is preserved for the same reason.
    apply hff.map_injective
    have hcomm₂ := eTriangle.hom.comm₂
    simpa [eMid, Functor.map_comp] using hcomm₂.symm

/-- Helper for Lemma 12.6.3: the bridge `toExt` is injective on source-facing extension classes. -/
lemma toExt_injective : Function.Injective (toExt : ExtensionClass A B → Ext B A 1) := by
  intro ξ η hξη
  revert hξη
  refine Quotient.inductionOn₂ ξ η ?_
  intro S T hST
  -- Quotient classes agree once the representatives are isomorphic.
  exact ExtensionClass.mk_eq_mk_of_isomorphic (extension_isomorphic_of_extClass_eq hST)

omit [HasExt.{w} C] in
/-- Helper for Lemma 12.6.3: every degree-one morphism between single objects can be completed to a
distinguished triangle whose first two maps come from honest morphisms in `C`. -/
lemma exists_distinguished_single_triangle_of_hom [HasDerivedCategory C]
    (δ : (DerivedCategory.singleFunctor C 0).obj B ⟶
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).obj ((DerivedCategory.singleFunctor C 0).obj A)) :
    ∃ (E : C) (f : A ⟶ E) (g : E ⟶ B),
      Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor C 0).map f)
          ((DerivedCategory.singleFunctor C 0).map g) δ ∈
        Pretriangulated.distinguishedTriangles := by
  let hff : (DerivedCategory.singleFunctor C 0).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor C 0)
  rcases Pretriangulated.distinguished_cocone_triangle₂ δ with ⟨Y, fY, gY, hT⟩
  have hA_le : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor C 0).obj A) 0 := by
    infer_instance
  have hB_le : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor C 0).obj B) 0 := by
    infer_instance
  -- The canonical `t`-structure keeps the middle term concentrated in degree `0`.
  have hY_le : DerivedCategory.TStructure.t.IsLE Y 0 :=
    CategoryTheory.Triangulated.TStructure.isLE₂ (DerivedCategory.TStructure.t)
      (Pretriangulated.Triangle.mk fY gY δ) hT 0 hA_le hB_le
  have hA_ge : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor C 0).obj A) 0 := by
    infer_instance
  have hB_ge : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor C 0).obj B) 0 := by
    infer_instance
  have hY_ge : DerivedCategory.TStructure.t.IsGE Y 0 :=
    CategoryTheory.Triangulated.TStructure.isGE₂ (DerivedCategory.TStructure.t)
      (Pretriangulated.Triangle.mk fY gY δ) hT 0 hA_ge hB_ge
  letI : Y.IsLE 0 := hY_le
  letI : Y.IsGE 0 := hY_ge
  rcases DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y 0 with ⟨E, ⟨eY⟩⟩
  let f : A ⟶ E := hff.preimage (fY ≫ eY.hom)
  let g : E ⟶ B := hff.preimage (eY.inv ≫ gY)
  have hf : (DerivedCategory.singleFunctor C 0).map f = fY ≫ eY.hom := by
    exact hff.map_preimage (fY ≫ eY.hom)
  have hg : (DerivedCategory.singleFunctor C 0).map g = eY.inv ≫ gY := by
    exact hff.map_preimage (eY.inv ≫ gY)
  -- Transport the distinguished triangle across the chosen degree-zero identification.
  let eT : Pretriangulated.Triangle.mk fY gY δ ≅
      Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor C 0).map f)
        ((DerivedCategory.singleFunctor C 0).map g) δ :=
    Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) eY (Iso.refl _)
      (by simpa using hf.symm)
      (by
        simpa using
          (calc
            gY = eY.hom ≫ (eY.inv ≫ gY) := by simp
            _ = eY.hom ≫ (DerivedCategory.singleFunctor C 0).map g := by rw [hg]))
      (by simp)
  refine ⟨E, f, g, ?_⟩
  exact Pretriangulated.isomorphic_distinguished _ hT _ eT.symm

/-
The next three helpers only use the derived-category `t`-structure, not the `Ext` owner.
-/
omit [HasExt.{w} C] in
/-- Helper for Lemma 12.6.3: a negative shift of a degree-zero single object receives no
nontrivial morphisms from another degree-zero single object. -/
lemma singleFunctor_hom_shift_neg_eq_zero [HasDerivedCategory C]
    {X Y : C} {n : ℤ}
    (φ : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧)
    (hn : n < 0) :
    φ = 0 := by
  have hX : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor C 0).obj X) 0 := by
    infer_instance
  have hshift :
      DerivedCategory.TStructure.t.IsGE
        (((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) 1 := by
    have hbase :
        DerivedCategory.TStructure.t.IsGE
          (((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) (0 - n) := by
      simpa using
        (DerivedCategory.TStructure.t.isGE_shift
          ((DerivedCategory.singleFunctor C 0).obj Y) 0 n (0 - n) (by omega) :
            DerivedCategory.TStructure.t.IsGE
              (((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) (0 - n))
    exact DerivedCategory.TStructure.t.isGE_of_ge
      (((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) 1 (0 - n) (by omega)
  -- The canonical `t`-structure orthogonality kills maps from degree `≤ 0` to degree `≥ 1`.
  exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE
    φ 0 1 (by omega) hX hshift

omit [HasExt.{w} C] in
/-- Helper for Lemma 12.6.3: the first two morphisms in a distinguished single triangle compose to
zero already in the abelian category `C`. -/
lemma comp_zero_of_distinguished_single_triangle [HasDerivedCategory C]
    {E : C} {f : A ⟶ E} {g : E ⟶ B}
    {δ : (DerivedCategory.singleFunctor C 0).obj B ⟶
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).obj ((DerivedCategory.singleFunctor C 0).obj A)}
    (hT : Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor C 0).map f)
        ((DerivedCategory.singleFunctor C 0).map g) δ ∈
      Pretriangulated.distinguishedTriangles) :
    f ≫ g = 0 := by
  let hff : (DerivedCategory.singleFunctor C 0).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor C 0)
  -- Faithfulness transports the standard triangle relation back to `C`.
  apply hff.map_injective
  simpa [Functor.map_comp] using
    (Pretriangulated.comp_distTriang_mor_zero₁₂
      (Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor C 0).map f)
        ((DerivedCategory.singleFunctor C 0).map g) δ) hT)

omit [HasExt.{w} C] in
/-- Helper for Lemma 12.6.3: a distinguished triangle on degree-zero single objects determines the
expected short exact sequence in the heart. -/
lemma shortExact_of_distinguished_single_triangle [HasDerivedCategory C]
    {E : C} {f : A ⟶ E} {g : E ⟶ B}
    {δ : (DerivedCategory.singleFunctor C 0).obj B ⟶
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).obj ((DerivedCategory.singleFunctor C 0).obj A)}
    (hT : Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor C 0).map f)
        ((DerivedCategory.singleFunctor C 0).map g) δ ∈
      Pretriangulated.distinguishedTriangles) :
    let hfg0 := comp_zero_of_distinguished_single_triangle (C := C) (A := A) (B := B)
      (f := f) (g := g) hT
    (ShortComplex.mk f g hfg0).ShortExact := by
  let hfg0 : f ≫ g = 0 :=
    comp_zero_of_distinguished_single_triangle (C := C) (A := A) (B := B)
      (f := f) (g := g) hT
  let S0 : ShortComplex C := ShortComplex.mk f g hfg0
  have hKernel : Limits.IsLimit (Limits.KernelFork.ofι f hfg0) := by
    -- The heart API identifies `f` with the kernel of `g`.
    simpa [S0, hfg0] using
      (CategoryTheory.Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
        (ι := DerivedCategory.singleFunctor C 0)
        (hι := fun {X Y n} φ hn ↦ singleFunctor_hom_shift_neg_eq_zero (C := C) φ hn)
        f g δ hT)
  have hCokernel : Limits.IsColimit (Limits.CokernelCofork.ofπ g hfg0) := by
    -- The same heart extraction identifies `g` with the cokernel of `f`.
    simpa [S0, hfg0] using
      (CategoryTheory.Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
        (ι := DerivedCategory.singleFunctor C 0)
        (hι := fun {X Y n} φ hn ↦ singleFunctor_hom_shift_neg_eq_zero (C := C) φ hn)
        f g δ hT)
  have hExactMono : S0.Exact ∧ Mono S0.f := by
    -- Convert the kernel owner into exactness plus monicity on the left map.
    exact (S0.exact_and_mono_f_iff_f_is_kernel).2 ⟨hKernel⟩
  have hExactEpi : S0.Exact ∧ Epi S0.g := by
    -- Convert the cokernel owner into exactness plus epimorphy on the right map.
    exact (S0.exact_and_epi_g_iff_g_is_cokernel).2 ⟨hCokernel⟩
  -- The short exact sequence now follows from the standard constructor.
  simpa [S0, hfg0] using ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 hExactEpi.2

omit [HasExt.{w} C] in
/-- Helper for Lemma 12.6.3: rotating to the common map `g` gives a comparison isomorphism
between the canonical short-exact-sequence triangle and any distinguished single triangle with the
same first two maps, and this comparison fixes the middle and right vertices. -/
lemma rotated_single_triangle_iso_fixing_middle_right [HasDerivedCategory C]
    {E : C} {f : A ⟶ E} {g : E ⟶ B} {hfg0 : f ≫ g = 0}
    {δ : (DerivedCategory.singleFunctor C 0).obj B ⟶
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).obj ((DerivedCategory.singleFunctor C 0).obj A)}
    (hT : Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor C 0).map f)
        ((DerivedCategory.singleFunctor C 0).map g) δ ∈
      Pretriangulated.distinguishedTriangles)
    (hS : (ShortComplex.mk f g hfg0).ShortExact) :
    ∃ e : hS.singleTriangle ≅
        Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor C 0).map f)
          ((DerivedCategory.singleFunctor C 0).map g) δ,
      e.hom.hom₂ = 𝟙 _ ∧ e.hom.hom₃ = 𝟙 _ := by
  let T₁ : Pretriangulated.Triangle (DerivedCategory C) := hS.singleTriangle
  let T₂ : Pretriangulated.Triangle (DerivedCategory C) :=
    Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor C 0).map f)
      ((DerivedCategory.singleFunctor C 0).map g) δ
  -- Compare the rotated triangles, whose first morphism is the common map `g`.
  obtain ⟨eRotate, heRotate₁, heRotate₂⟩ :=
    Pretriangulated.exists_iso_of_arrow_iso T₁.rotate T₂.rotate
      (Pretriangulated.rot_of_distTriang _ hS.singleTriangle_distinguished)
      (Pretriangulated.rot_of_distTriang _ hT)
      (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by simpa [T₁, T₂]))
  -- Undo the rotation; the unit of the rotation equivalence still fixes the last two vertices.
  let e : T₁ ≅ T₂ :=
    Pretriangulated.rotCompInvRot.app T₁ ≪≫
      ((Pretriangulated.invRotate (DerivedCategory C)).mapIso eRotate) ≪≫
      (Pretriangulated.rotCompInvRot.app T₂).symm
  refine ⟨e, ?_, ?_⟩
  · -- The middle component comes from the first rotated component, hence is the identity.
    simpa [T₁, T₂, e, heRotate₁]
  · -- The right component comes from the second rotated component, hence is the identity.
    simpa [T₁, T₂, e, heRotate₂]

omit [HasExt.{w} C] in
/-- Helper for Lemma 12.6.3: once the triangle comparison fixes the middle and right vertices, the
left vertex is forced to be the identity by cancelling the mono `f`. -/
lemma left_component_eq_id_of_triangle_iso_fixing_middle_right [HasDerivedCategory C]
    {E : C} {f : A ⟶ E} {g : E ⟶ B} {hfg0 : f ≫ g = 0}
    {δ : (DerivedCategory.singleFunctor C 0).obj B ⟶
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).obj ((DerivedCategory.singleFunctor C 0).obj A)}
    (hS : (ShortComplex.mk f g hfg0).ShortExact)
    (e : hS.singleTriangle ≅
      Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor C 0).map f)
        ((DerivedCategory.singleFunctor C 0).map g) δ)
    (he₂ : e.hom.hom₂ = 𝟙 _)
    (_he₃ : e.hom.hom₃ = 𝟙 _) :
    e.hom.hom₁ = 𝟙 _ := by
  let hff : (DerivedCategory.singleFunctor C 0).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor C 0)
  let a : A ⟶ A := hff.preimage e.hom.hom₁
  have ha : (DerivedCategory.singleFunctor C 0).map a = e.hom.hom₁ := by
    exact hff.map_preimage e.hom.hom₁
  have hf : f = a ≫ f := by
    -- Pull `comm₁` back through the fully faithful single functor.
    apply hff.map_injective
    simpa [a, ha, he₂, Functor.map_comp] using e.hom.comm₁
  letI : Mono f := hS.mono_f
  have ha_id : a = 𝟙 A := by
    -- The left map of a short exact sequence is mono, so the only endomorphism preserving it is
    -- the identity.
    apply (cancel_mono f).1
    simpa using hf.symm
  -- Push the identity statement forward through the fully faithful functor.
  simpa [a, ha_id] using ha.symm

omit [HasExt.{w} C] in
/-- Helper for Lemma 12.6.3: the connecting morphism of the short exact sequence extracted from a
distinguished single triangle is exactly the original third map. -/
lemma single_delta_eq_of_distinguished_single_triangle [HasDerivedCategory C]
    {E : C} {f : A ⟶ E} {g : E ⟶ B} {hfg0 : f ≫ g = 0}
    {δ : (DerivedCategory.singleFunctor C 0).obj B ⟶
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).obj ((DerivedCategory.singleFunctor C 0).obj A)}
    (hT : Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor C 0).map f)
        ((DerivedCategory.singleFunctor C 0).map g) δ ∈
      Pretriangulated.distinguishedTriangles)
    (hS : (ShortComplex.mk f g hfg0).ShortExact) :
    hS.singleδ = δ := by
  obtain ⟨e, he₂, he₃⟩ :=
    rotated_single_triangle_iso_fixing_middle_right (C := C) (A := A) (B := B)
      (f := f) (g := g) (hfg0 := hfg0) hT hS
  have he₁ :
      e.hom.hom₁ = 𝟙 ((DerivedCategory.singleFunctor C 0).obj A) :=
    left_component_eq_id_of_triangle_iso_fixing_middle_right (C := C) (A := A) (B := B)
      (f := f) (g := g) (hfg0 := hfg0) (δ := δ) hS e he₂ he₃
  -- With all three components identified as identities, `comm₃` reads exactly as `singleδ = δ`.
  simpa [he₁, he₃] using e.hom.comm₃

/-- Helper for Lemma 12.6.3: every class in `Ext¹(B, A)` should come from an actual extension. -/
lemma extension_exists_of_ext [HasDerivedCategory C]
    (e : Ext B A 1) :
    ∃ S : Extension A B, S.extClass = e := by
  rcases exists_distinguished_single_triangle_of_hom (C := C) (A := A) (B := B) e.hom with
    ⟨E, f, g, hT⟩
  let hfg0 : f ≫ g = 0 :=
    comp_zero_of_distinguished_single_triangle (C := C) (A := A) (B := B)
      (f := f) (g := g) hT
  have hS : (ShortComplex.mk f g hfg0).ShortExact := by
    -- The heart-extraction step is now closed by the previous helper.
    simpa [hfg0] using
      shortExact_of_distinguished_single_triangle (C := C) (A := A) (B := B)
        (f := f) (g := g) hT
  -- Route correction: after extracting the short exact sequence, compare its canonical triangle
  -- with the input triangle on the common map `g` to recover the original connecting morphism.
  have hδ : hS.singleδ = e.hom :=
    single_delta_eq_of_distinguished_single_triangle (C := C) (A := A) (B := B)
      (f := f) (g := g) (hfg0 := hfg0) hT hS
  let S : Extension A B := ⟨E, f, g, hfg0, hS⟩
  refine ⟨S, ?_⟩
  -- The extension class is determined by its connecting morphism in `Ext¹`.
  apply Ext.ext
  rw [S.shortExact.extClass_hom]
  simpa [S] using hδ

/-- Helper for Lemma 12.6.3: surjectivity of `toExt` reduces to realizing each `Ext¹` class by an
actual extension. -/
lemma toExt_surjective_of_extension_exists
    (h :
      ∀ e : Ext B A 1, ∃ S : Extension A B, S.extClass = e) :
    Function.Surjective (toExt : ExtensionClass A B → Ext B A 1) := by
  intro e
  -- Once a representative extension exists, its quotient class maps back to `e`.
  rcases h e with ⟨S, hS⟩
  refine ⟨⟦S⟧, ?_⟩
  simpa [toExt] using hS

/-- The canonical comparison map from source-facing extension classes to `Ext¹` is bijective. -/
theorem toExt_bijective :
    Function.Bijective (toExt : ExtensionClass A B → Ext B A 1) := by
  constructor
  · -- Injectivity is already reduced to uniqueness of distinguished triangles.
    exact toExt_injective
  · letI := HasDerivedCategory.standard C
    -- The surjective half is now reduced to the remaining boundary-map comparison helper.
    exact toExt_surjective_of_extension_exists (C := C) (A := A) (B := B)
      (extension_exists_of_ext (C := C) (A := A) (B := B))

/-- The categorical extension group `ExtensionClass A B` is canonically identified with
`Ext¹(B, A)`. -/
noncomputable def toExtAddEquiv : ExtensionClass A B ≃+ Ext B A 1 :=
  { toEquiv := Equiv.ofBijective (toExt : ExtensionClass A B → Ext B A 1) toExt_bijective
    map_add' := toExt_add }

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A A' B B' : C}

/-- Lemma 12.6.3: Baer sum gives the source-facing extension classes a commutative group law. -/
noncomputable instance : AddCommGroup (ExtensionClass A B) :=
  letI : HasExt.{max u v} C := HasExt.standard C
  Function.Injective.addCommGroup toExt toExt_bijective.injective toExt_zero toExt_add toExt_neg
    toExt_sub toExt_nsmul toExt_zsmul

/-- Pullback of extension classes along a morphism in the right endpoint is additive. -/
noncomputable def pullbackAddHom (u : B' ⟶ B) : ExtensionClass A B →+ ExtensionClass A B' :=
  letI : HasExt.{max u v} C := HasExt.standard C
  let e : ExtensionClass A B ≃+ Ext B A 1 := toExtAddEquiv
  let e' : ExtensionClass A B' ≃+ Ext B' A 1 := toExtAddEquiv
  let f : Ext B A 1 →+ Ext B' A 1 := (Ext.mk₀ u).precomp A (zero_add 1)
  (e'.symm : Ext B' A 1 →+ ExtensionClass A B').comp (f.comp (e : ExtensionClass A B →+ Ext B A 1))

/-- Pushout of extension classes along a morphism in the left endpoint is additive. -/
noncomputable def pushoutAddHom (a : A ⟶ A') : ExtensionClass A B →+ ExtensionClass A' B :=
  letI : HasExt.{max u v} C := HasExt.standard C
  let e : ExtensionClass A B ≃+ Ext B A 1 := toExtAddEquiv
  let e' : ExtensionClass A' B ≃+ Ext B A' 1 := toExtAddEquiv
  let f : Ext B A 1 →+ Ext B A' 1 := (Ext.mk₀ a).postcomp B (add_zero 1)
  (e'.symm : Ext B A' 1 →+ ExtensionClass A' B).comp (f.comp (e : ExtensionClass A B →+ Ext B A 1))

@[simp] theorem pullbackAddHom_apply (u : B' ⟶ B) (ξ : ExtensionClass A B) :
    pullbackAddHom u ξ = pullback u ξ := by
  letI : HasExt.{max u v} C := HasExt.standard C
  let e : ExtensionClass A B' ≃+ Ext B' A 1 := toExtAddEquiv
  let f : Ext B A 1 →+ Ext B' A 1 := (Ext.mk₀ u).precomp A (zero_add 1)
  apply toExt_bijective.injective
  rw [toExt_pullback]
  change e (e.symm (f (toExt ξ))) = f (toExt ξ)
  exact e.apply_symm_apply (f (toExt ξ))

@[simp] theorem pushoutAddHom_apply (a : A ⟶ A') (ξ : ExtensionClass A B) :
    pushoutAddHom a ξ = pushout a ξ := by
  letI : HasExt.{max u v} C := HasExt.standard C
  let e : ExtensionClass A' B ≃+ Ext B A' 1 := toExtAddEquiv
  let f : Ext B A 1 →+ Ext B A' 1 := (Ext.mk₀ a).postcomp B (add_zero 1)
  apply toExt_bijective.injective
  rw [toExt_pushout]
  change e (e.symm (f (toExt ξ))) = f (toExt ξ)
  exact e.apply_symm_apply (f (toExt ξ))

@[simp] theorem pullback_zero (u : B' ⟶ B) :
    pullback u (0 : ExtensionClass A B) = 0 := by
  rw [← pullbackAddHom_apply]
  exact (pullbackAddHom u).map_zero

@[simp] theorem pullback_add (u : B' ⟶ B) (ξ η : ExtensionClass A B) :
    pullback u (ξ + η) = pullback u ξ + pullback u η := by
  rw [← pullbackAddHom_apply, ← pullbackAddHom_apply, ← pullbackAddHom_apply]
  exact (pullbackAddHom u).map_add ξ η

@[simp] theorem pushout_zero (a : A ⟶ A') :
    pushout a (0 : ExtensionClass A B) = 0 := by
  rw [← pushoutAddHom_apply]
  exact (pushoutAddHom a).map_zero

@[simp] theorem pushout_add (a : A ⟶ A') (ξ η : ExtensionClass A B) :
    pushout a (ξ + η) = pushout a ξ + pushout a η := by
  rw [← pushoutAddHom_apply, ← pushoutAddHom_apply, ← pushoutAddHom_apply]
  exact (pushoutAddHom a).map_add ξ η

end

end ExtensionClass
end CategoryTheory
