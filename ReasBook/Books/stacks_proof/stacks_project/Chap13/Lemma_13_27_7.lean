import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open ShortComplex.ShortExact

universe w v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {A B C : 𝒜}

/- Domain-style sampling for Lemma 13.27.7:
- primary domain: short exact sequences in an abelian category, their Yoneda composition in
  `Ext²`, and the `3 × 3` pullback comparison between short exact sequences;
- inspected owner declarations:
  `Extension`,
  `Extension.Isomorphic`,
  `ExtensionClass.pullback`,
  `DistinguishedThreeByThreeExtension`;
- best owner abstraction:
  `source-facing`: a commutative exact `3 × 3` extension diagram over fixed rows
    `S : Extension A B` and `T : Extension B C`;
  `core/canonical`: the degree-`1` owner `ExtensionClass A T.E`;
  `bridge/view`: the pullback equation
    `ExtensionClass.pullback T.f (⟦U⟧ : ExtensionClass A T.E) = ⟦S⟧`.

Primitive data are the middle short exact row `0 ⟶ A ⟶ W ⟶ T.E ⟶ 0`, a comparison morphism
`S.E ⟶ W`, and the pullback square over `T.f : B ⟶ T.E`. The extension-class pullback identity is
derived bridge API from that source-facing diagram data, not the main owner.
-/

-- Proof sketch: apply the contravariant long exact sequence in `Ext(-, A)` to the short exact
-- sequence `T : 0 ⟶ B ⟶ T.E ⟶ C ⟶ 0`. The vanishing of the Yoneda product means that the class of
-- `S : 0 ⟶ A ⟶ S.E ⟶ B ⟶ 0` lifts to an element of `Ext¹(T.E, A)`, and such a lift is represented
-- by a short exact sequence `0 ⟶ A ⟶ W ⟶ T.E ⟶ 0` whose pullback along `B ⟶ T.E` recovers `S`,
-- equivalently giving the claimed exact `3 × 3` diagram.
namespace Extension

/-- Source-facing `3 × 3` extension data for Lemma 13.27.7. This is the exact diagrammatic owner:
the top row is `S`, the bottom row is `T`, the middle row is a short exact sequence
`0 ⟶ A ⟶ W ⟶ T.E ⟶ 0`, and the right-hand square is a pullback. In an abelian category this is an
exact canonical equivalent of the textbook commutative exact `3 × 3` diagram. -/
@[stacks 0GSM]
structure ThreeByThree (S : Extension A B) (T : Extension B C) where
  middleRow : Extension A T.E
  middleColumnMap : S.E ⟶ middleRow.E
  left_comm : S.f ≫ middleColumnMap = middleRow.f
  right_pullback : IsPullback S.g middleColumnMap T.f middleRow.g

namespace ThreeByThree

variable {S : Extension A B} {T : Extension B C}

@[simp]
theorem right_comm (D : ThreeByThree S T) :
    S.g ≫ T.f = D.middleColumnMap ≫ D.middleRow.g :=
  D.right_pullback.w

/-- Helper for Lemma 13.27.7: a source-facing `3 × 3` diagram identifies the top row with the
pullback extension of its middle row along `T.f`. -/
lemma pullback_isomorphic (D : ThreeByThree S T) :
    Extension.Isomorphic (Extension.pullback T.f D.middleRow) S := by
  let e : (Extension.pullback T.f D.middleRow).E ≅ S.E := D.right_pullback.isoPullback.symm
  have he_fst : e.hom ≫ S.g = pullback.fst T.f D.middleRow.g := by
    change D.right_pullback.isoPullback.inv ≫ S.g = pullback.fst T.f D.middleRow.g
    exact D.right_pullback.isoPullback_inv_fst
  have he_snd : e.hom ≫ D.middleColumnMap = pullback.snd T.f D.middleRow.g := by
    change D.right_pullback.isoPullback.inv ≫ D.middleColumnMap = pullback.snd T.f D.middleRow.g
    exact D.right_pullback.isoPullback_inv_snd
  refine ⟨e, ?_, ?_⟩
  · -- Compare the two maps `A ⟶ S.E` through the two pullback projections.
    apply D.right_pullback.hom_ext
    · calc
        ((Extension.pullback T.f D.middleRow).f ≫ e.hom) ≫ S.g =
            (Extension.pullback T.f D.middleRow).f ≫ pullback.fst T.f D.middleRow.g := by
              rw [Category.assoc, he_fst]
        _ = 0 := by
              simpa [Extension.pullback] using
                (pullback.lift_fst (0 : A ⟶ B) D.middleRow.f
                  (by simpa using D.middleRow.zero.symm))
        _ = S.f ≫ S.g := by simpa using S.zero.symm
    · calc
        ((Extension.pullback T.f D.middleRow).f ≫ e.hom) ≫ D.middleColumnMap =
            (Extension.pullback T.f D.middleRow).f ≫ pullback.snd T.f D.middleRow.g := by
              rw [Category.assoc, he_snd]
        _ = D.middleRow.f := by
              simpa [Extension.pullback] using
                (pullback.lift_snd (0 : A ⟶ B) D.middleRow.f
                  (by simpa using D.middleRow.zero.symm))
        _ = S.f ≫ D.middleColumnMap := D.left_comm.symm
  · -- The right endpoint compatibility is one of the pullback comparison formulas.
    simpa [Extension.pullback] using he_fst

end ThreeByThree

end Extension

/-- Helper for Lemma 13.27.7: an isomorphism from a pullback extension back to `S` yields the
required source-facing `3 × 3` diagram. -/
lemma nonempty_threeByThree_of_pullback_isomorphic
    {S : Extension A B} {T : Extension B C} {U : Extension A T.E}
    (h : Extension.Isomorphic (Extension.pullback T.f U) S) :
    Nonempty (Extension.ThreeByThree S T) := by
  rcases h with ⟨e, hf, hg⟩
  refine ⟨{
      middleRow := U
      middleColumnMap := e.inv ≫ pullback.snd T.f U.g
      left_comm := ?_
      right_pullback := ?_ }⟩
  · -- Rewrite the left square through the endpoint-fixing pullback isomorphism.
    have hf' : S.f ≫ e.inv = (Extension.pullback T.f U).f := by
      have hf'' := congrArg (fun k ↦ k ≫ e.inv) hf
      simpa [Category.assoc] using hf''.symm
    have hf_snd :
        S.f ≫ (e.inv ≫ pullback.snd T.f U.g) =
          (Extension.pullback T.f U).f ≫ pullback.snd T.f U.g := by
      have hf_snd' :
          (S.f ≫ e.inv) ≫ pullback.snd T.f U.g =
            (Extension.pullback T.f U).f ≫ pullback.snd T.f U.g :=
        congrArg (fun k ↦ k ≫ pullback.snd T.f U.g) hf'
      simpa [Category.assoc] using hf_snd'
    calc
      S.f ≫ (e.inv ≫ pullback.snd T.f U.g) =
          (Extension.pullback T.f U).f ≫ pullback.snd T.f U.g := hf_snd
      _ = U.f := by
            simpa [Extension.pullback] using
              (pullback.lift_snd (0 : A ⟶ B) U.f (by simpa using U.zero.symm))
  · -- Transport the canonical pullback square along the isomorphism on the top-left corner.
    have hg' : e.inv ≫ pullback.fst T.f U.g = S.g := by
      change e.inv ≫ (Extension.pullback T.f U).g = S.g
      rw [← hg, Iso.inv_hom_id_assoc]
    refine (IsPullback.of_hasPullback T.f U.g).of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simpa [Extension.pullback] using hg'
    · simp [Extension.pullback]
    · simp
    · simp

/-- The source-facing `3 × 3` extension data of `Extension.ThreeByThree` is equivalent to the
bridge/view statement that the middle row has pullback extension class `⟦S⟧`. -/
theorem nonempty_threeByThree_iff_exists_pullback_extClass_eq
    (S : Extension A B) (T : Extension B C) :
    Nonempty (Extension.ThreeByThree S T) ↔
      ∃ U : Extension A T.E,
        ExtensionClass.pullback T.f (⟦U⟧ : ExtensionClass A T.E) = ⟦S⟧ := by
  constructor
  · rintro ⟨D⟩
    refine ⟨D.middleRow, ?_⟩
    -- The top row and the pullback of the middle row represent the same extension class.
    change (⟦Extension.pullback T.f D.middleRow⟧ : ExtensionClass A B) = ⟦S⟧
    exact ExtensionClass.mk_eq_mk_of_isomorphic D.pullback_isomorphic
  · rintro ⟨U, hU⟩
    -- Equality of quotient classes gives an endpoint-fixing isomorphism of the top row.
    change (⟦Extension.pullback T.f U⟧ : ExtensionClass A B) = ⟦S⟧ at hU
    exact nonempty_threeByThree_of_pullback_isomorphic (Quotient.exact hU)

variable [HasExt.{w} 𝒜]

/-- Helper for Lemma 13.27.7: equal degree-one `Ext` classes force the corresponding extensions to
be endpoint-fixing isomorphic. -/
lemma extension_isomorphic_of_extClass_eq {S T : Extension A B}
    (h : S.extClass = T.extClass) : Extension.Isomorphic S T := by
  letI := HasDerivedCategory.standard 𝒜
  let hff : (DerivedCategory.singleFunctor 𝒜 0).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor 𝒜 0)
  -- Compare the connecting morphisms of the canonical distinguished triangles.
  have hδ : S.shortExact.singleδ = T.shortExact.singleδ := by
    have hhom : S.extClass.hom = T.extClass.hom := by simpa using congrArg Ext.hom h
    rw [S.shortExact.extClass_hom, T.shortExact.extClass_hom] at hhom
    exact hhom
  have hcomm₃ :
      S.shortExact.singleδ ≫
          (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).map
            (Iso.refl ((DerivedCategory.singleFunctor 𝒜 0).obj A)).hom =
        (Iso.refl ((DerivedCategory.singleFunctor 𝒜 0).obj B)).hom ≫ T.shortExact.singleδ := by
    simpa using hδ
  -- Uniqueness of distinguished triangles with fixed endpoints and third morphism gives an
  -- isomorphism on the middle terms.
  let eTriangle :=
    Pretriangulated.isoTriangleOfIso₁₃ S.shortExact.singleTriangle T.shortExact.singleTriangle
      S.shortExact.singleTriangle_distinguished T.shortExact.singleTriangle_distinguished
      (Iso.refl ((DerivedCategory.singleFunctor 𝒜 0).obj A))
      (Iso.refl ((DerivedCategory.singleFunctor 𝒜 0).obj B)) hcomm₃
  let eMid : S.E ≅ T.E := hff.preimageIso (Pretriangulated.Triangle.π₂.mapIso eTriangle)
  refine ⟨eMid, ?_, ?_⟩
  · -- The first structure map is preserved after pulling the middle-term isomorphism back to `𝒜`.
    apply hff.map_injective
    have hcomm₁ := eTriangle.hom.comm₁
    simpa [eMid, Functor.map_comp] using hcomm₁
  · -- The second structure map is preserved for the same reason.
    apply hff.map_injective
    have hcomm₂ := eTriangle.hom.comm₂
    simpa [eMid, Functor.map_comp] using hcomm₂.symm

omit [HasExt.{w} 𝒜] in
/-- Helper for Lemma 13.27.7: every degree-one morphism between single objects extends to a
distinguished triangle whose first two maps come from honest morphisms in `𝒜`. -/
lemma exists_distinguished_single_triangle_of_hom [HasDerivedCategory 𝒜]
    (δ : (DerivedCategory.singleFunctor 𝒜 0).obj B ⟶
      (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).obj ((DerivedCategory.singleFunctor 𝒜 0).obj A)) :
    ∃ (E : 𝒜) (f : A ⟶ E) (g : E ⟶ B),
      Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor 𝒜 0).map f)
          ((DerivedCategory.singleFunctor 𝒜 0).map g) δ ∈
        Pretriangulated.distinguishedTriangles := by
  let hff : (DerivedCategory.singleFunctor 𝒜 0).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor 𝒜 0)
  rcases Pretriangulated.distinguished_cocone_triangle₂ δ with ⟨Y, fY, gY, hT⟩
  have hA_le : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor 𝒜 0).obj A) 0 := by
    infer_instance
  have hB_le : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor 𝒜 0).obj B) 0 := by
    infer_instance
  -- The canonical `t`-structure keeps the middle term concentrated in degree `0`.
  have hY_le : DerivedCategory.TStructure.t.IsLE Y 0 :=
    CategoryTheory.Triangulated.TStructure.isLE₂ (DerivedCategory.TStructure.t)
      (Pretriangulated.Triangle.mk fY gY δ) hT 0 hA_le hB_le
  have hA_ge : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor 𝒜 0).obj A) 0 := by
    infer_instance
  have hB_ge : DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor 𝒜 0).obj B) 0 := by
    infer_instance
  have hY_ge : DerivedCategory.TStructure.t.IsGE Y 0 :=
    CategoryTheory.Triangulated.TStructure.isGE₂ (DerivedCategory.TStructure.t)
      (Pretriangulated.Triangle.mk fY gY δ) hT 0 hA_ge hB_ge
  letI : Y.IsLE 0 := hY_le
  letI : Y.IsGE 0 := hY_ge
  rcases DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y 0 with ⟨E, ⟨eY⟩⟩
  let f : A ⟶ E := hff.preimage (fY ≫ eY.hom)
  let g : E ⟶ B := hff.preimage (eY.inv ≫ gY)
  have hf : (DerivedCategory.singleFunctor 𝒜 0).map f = fY ≫ eY.hom := by
    exact hff.map_preimage (fY ≫ eY.hom)
  have hg : (DerivedCategory.singleFunctor 𝒜 0).map g = eY.inv ≫ gY := by
    exact hff.map_preimage (eY.inv ≫ gY)
  -- Transport the distinguished triangle across the chosen degree-zero identification.
  let eT : Pretriangulated.Triangle.mk fY gY δ ≅
      Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor 𝒜 0).map f)
        ((DerivedCategory.singleFunctor 𝒜 0).map g) δ :=
    Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) eY (Iso.refl _)
      (by simpa using hf.symm)
      (by
        simpa using
          (calc
            gY = eY.hom ≫ (eY.inv ≫ gY) := by simp
            _ = eY.hom ≫ (DerivedCategory.singleFunctor 𝒜 0).map g := by rw [hg]))
      (by simp)
  refine ⟨E, f, g, ?_⟩
  exact Pretriangulated.isomorphic_distinguished _ hT _ eT.symm

omit [HasExt.{w} 𝒜] in
/-- Helper for Lemma 13.27.7: a negative shift of a degree-zero single object receives no
nontrivial morphisms from another degree-zero single object. -/
lemma singleFunctor_hom_shift_neg_eq_zero [HasDerivedCategory 𝒜]
    {X Y : 𝒜} {n : ℤ}
    (φ : (DerivedCategory.singleFunctor 𝒜 0).obj X ⟶
      ((DerivedCategory.singleFunctor 𝒜 0).obj Y)⟦n⟧)
    (hn : n < 0) :
    φ = 0 := by
  have hX : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor 𝒜 0).obj X) 0 := by
    infer_instance
  have hshift :
      DerivedCategory.TStructure.t.IsGE
        (((DerivedCategory.singleFunctor 𝒜 0).obj Y)⟦n⟧) 1 := by
    have hbase :
        DerivedCategory.TStructure.t.IsGE
          (((DerivedCategory.singleFunctor 𝒜 0).obj Y)⟦n⟧) (0 - n) := by
      simpa using
        (DerivedCategory.TStructure.t.isGE_shift
          ((DerivedCategory.singleFunctor 𝒜 0).obj Y) 0 n (0 - n) (by omega) :
            DerivedCategory.TStructure.t.IsGE
              (((DerivedCategory.singleFunctor 𝒜 0).obj Y)⟦n⟧) (0 - n))
    exact DerivedCategory.TStructure.t.isGE_of_ge
      (((DerivedCategory.singleFunctor 𝒜 0).obj Y)⟦n⟧) 1 (0 - n) (by omega)
  -- The canonical `t`-structure orthogonality kills maps from degree `≤ 0` to degree `≥ 1`.
  exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE
    φ 0 1 (by omega) hX hshift

omit [HasExt.{w} 𝒜] in
/-- Helper for Lemma 13.27.7: the first two maps in a distinguished single triangle already
compose to zero in the abelian category `𝒜`. -/
lemma comp_zero_of_distinguished_single_triangle [HasDerivedCategory 𝒜]
    {E : 𝒜} {f : A ⟶ E} {g : E ⟶ B}
    {δ : (DerivedCategory.singleFunctor 𝒜 0).obj B ⟶
      (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).obj ((DerivedCategory.singleFunctor 𝒜 0).obj A)}
    (hT : Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor 𝒜 0).map f)
        ((DerivedCategory.singleFunctor 𝒜 0).map g) δ ∈
      Pretriangulated.distinguishedTriangles) :
    f ≫ g = 0 := by
  let hff : (DerivedCategory.singleFunctor 𝒜 0).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor 𝒜 0)
  -- Faithfulness transports the standard triangle relation back to `𝒜`.
  apply hff.map_injective
  simpa [Functor.map_comp] using
    (Pretriangulated.comp_distTriang_mor_zero₁₂
      (Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor 𝒜 0).map f)
        ((DerivedCategory.singleFunctor 𝒜 0).map g) δ) hT)

omit [HasExt.{w} 𝒜] in
/-- Helper for Lemma 13.27.7: a distinguished triangle on degree-zero single objects determines
the expected short exact sequence in the heart. -/
lemma shortExact_of_distinguished_single_triangle [HasDerivedCategory 𝒜]
    {E : 𝒜} {f : A ⟶ E} {g : E ⟶ B}
    {δ : (DerivedCategory.singleFunctor 𝒜 0).obj B ⟶
      (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).obj ((DerivedCategory.singleFunctor 𝒜 0).obj A)}
    (hT : Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor 𝒜 0).map f)
        ((DerivedCategory.singleFunctor 𝒜 0).map g) δ ∈
      Pretriangulated.distinguishedTriangles) :
    let hfg0 := comp_zero_of_distinguished_single_triangle (𝒜 := 𝒜) (A := A) (B := B)
      (f := f) (g := g) hT
    (ShortComplex.mk f g hfg0).ShortExact := by
  let hfg0 : f ≫ g = 0 :=
    comp_zero_of_distinguished_single_triangle (𝒜 := 𝒜) (A := A) (B := B)
      (f := f) (g := g) hT
  let S0 : ShortComplex 𝒜 := ShortComplex.mk f g hfg0
  have hKernel : Limits.IsLimit (Limits.KernelFork.ofι f hfg0) := by
    -- The heart API identifies `f` with the kernel of `g`.
    simpa [S0, hfg0] using
      (CategoryTheory.Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
        (ι := DerivedCategory.singleFunctor 𝒜 0)
        (hι := fun {X Y n} φ hn ↦ singleFunctor_hom_shift_neg_eq_zero (𝒜 := 𝒜) φ hn)
        f g δ hT)
  have hCokernel : Limits.IsColimit (Limits.CokernelCofork.ofπ g hfg0) := by
    -- The same heart extraction identifies `g` with the cokernel of `f`.
    simpa [S0, hfg0] using
      (CategoryTheory.Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
        (ι := DerivedCategory.singleFunctor 𝒜 0)
        (hι := fun {X Y n} φ hn ↦ singleFunctor_hom_shift_neg_eq_zero (𝒜 := 𝒜) φ hn)
        f g δ hT)
  have hExactMono : S0.Exact ∧ Mono S0.f := by
    exact (S0.exact_and_mono_f_iff_f_is_kernel).2 ⟨hKernel⟩
  have hExactEpi : S0.Exact ∧ Epi S0.g := by
    exact (S0.exact_and_epi_g_iff_g_is_cokernel).2 ⟨hCokernel⟩
  -- The short exact sequence now follows from the standard constructor.
  simpa [S0, hfg0] using ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 hExactEpi.2

omit [HasExt.{w} 𝒜] in
/-- Helper for Lemma 13.27.7: the connecting morphism of the short exact sequence extracted from a
distinguished single triangle is exactly the original third map. -/
lemma single_delta_eq_of_distinguished_single_triangle [HasDerivedCategory 𝒜]
    {E : 𝒜} {f : A ⟶ E} {g : E ⟶ B} {hfg0 : f ≫ g = 0}
    {δ : (DerivedCategory.singleFunctor 𝒜 0).obj B ⟶
      (shiftFunctor (DerivedCategory 𝒜) (1 : ℤ)).obj ((DerivedCategory.singleFunctor 𝒜 0).obj A)}
    (hT : Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor 𝒜 0).map f)
        ((DerivedCategory.singleFunctor 𝒜 0).map g) δ ∈
      Pretriangulated.distinguishedTriangles)
    (hS : (ShortComplex.mk f g hfg0).ShortExact) :
    hS.singleδ = δ := by
  let T₂ : Pretriangulated.Triangle (DerivedCategory 𝒜) :=
    Pretriangulated.Triangle.mk ((DerivedCategory.singleFunctor 𝒜 0).map f)
      ((DerivedCategory.singleFunctor 𝒜 0).map g) δ
  let e :=
    Pretriangulated.isoTriangleOfIso₁₂ hS.singleTriangle T₂
      hS.singleTriangle_distinguished hT
      (Iso.refl ((DerivedCategory.singleFunctor 𝒜 0).obj A))
      (Iso.refl ((DerivedCategory.singleFunctor 𝒜 0).obj E))
      (by simp [T₂])
  have he₁ : e.hom.hom₁ = 𝟙 ((DerivedCategory.singleFunctor 𝒜 0).obj A) := by
    simp [e, T₂]
  have he₂ : e.hom.hom₂ = 𝟙 ((DerivedCategory.singleFunctor 𝒜 0).obj E) := by
    simp [e, T₂]
  let hff : (DerivedCategory.singleFunctor 𝒜 0).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor 𝒜 0)
  have he₃ : e.hom.hom₃ = 𝟙 ((DerivedCategory.singleFunctor 𝒜 0).obj B) := by
    let b : B ⟶ B := hff.preimage e.hom.hom₃
    have hb : (DerivedCategory.singleFunctor 𝒜 0).map b = e.hom.hom₃ := by
      exact hff.map_preimage e.hom.hom₃
    have hgb : g ≫ b = g := by
      have hmap :
          (DerivedCategory.singleFunctor 𝒜 0).map g ≫ e.hom.hom₃ =
            (DerivedCategory.singleFunctor 𝒜 0).map g := by
        simpa [T₂, he₂] using e.hom.comm₂
      apply hff.map_injective
      simpa [b, hb, Functor.map_comp] using hmap
    letI : Epi g := hS.epi_g
    have hb_id : b = 𝟙 B := by
      apply (cancel_epi g).1
      simpa using hgb
    simpa [b, hb_id] using hb.symm
  -- With the first two components fixed to be identities, `comm₃` reads exactly as `singleδ = δ`.
  simpa [T₂, he₁, he₃] using e.hom.comm₃

/-- Helper for Lemma 13.27.7: every class in `Ext¹(B, A)` comes from an actual extension. -/
lemma extension_exists_of_ext (e : Ext B A 1) :
    ∃ S : Extension A B, S.extClass = e := by
  letI := HasDerivedCategory.standard 𝒜
  rcases exists_distinguished_single_triangle_of_hom (𝒜 := 𝒜) (A := A) (B := B) e.hom with
    ⟨E, f, g, hT⟩
  let hfg0 : f ≫ g = 0 :=
    comp_zero_of_distinguished_single_triangle (𝒜 := 𝒜) (A := A) (B := B)
      (f := f) (g := g) hT
  have hS : (ShortComplex.mk f g hfg0).ShortExact := by
    -- The heart-extraction step is exactly the previous helper.
    simpa [hfg0] using
      shortExact_of_distinguished_single_triangle (𝒜 := 𝒜) (A := A) (B := B)
        (f := f) (g := g) hT
  have hδ : hS.singleδ = e.hom :=
    single_delta_eq_of_distinguished_single_triangle (𝒜 := 𝒜) (A := A) (B := B)
      (f := f) (g := g) (hfg0 := hfg0) hT hS
  let S : Extension A B := ⟨E, f, g, hfg0, hS⟩
  refine ⟨S, ?_⟩
  -- The extension class is determined by its connecting morphism in `Ext¹`.
  apply Ext.ext
  rw [S.shortExact.extClass_hom]
  simpa [S] using hδ

/-- Helper for Lemma 13.27.7: pullback equality of extension classes is the same as the existence
of an `Ext¹(T.E, A)` lift of the top extension class. -/
lemma exists_pullback_extClass_eq_iff_exists_ext_lift
    (S : Extension A B) (T : Extension B C) :
    (∃ U : Extension A T.E,
        ExtensionClass.pullback T.f (⟦U⟧ : ExtensionClass A T.E) = ⟦S⟧) ↔
      ∃ x : Ext T.E A 1, (Ext.mk₀ T.f).precomp A (zero_add 1) x = extClass S.shortExact := by
  constructor
  · rintro ⟨U, hU⟩
    refine ⟨ExtensionClass.toExt (⟦U⟧ : ExtensionClass A T.E), ?_⟩
    -- Apply the `ExtensionClass → Ext¹` bridge to the pullback identity.
    have hToExt := congrArg ExtensionClass.toExt hU
    simpa [Extension.extClass, ExtensionClass.toExt_pullback] using hToExt
  · rintro ⟨x, hx⟩
    obtain ⟨U, hU⟩ := extension_exists_of_ext (A := A) (B := T.E) x
    have hPull : (Extension.pullback T.f U).extClass = S.extClass := by
      calc
        (Extension.pullback T.f U).extClass =
            (Ext.mk₀ T.f).precomp A (zero_add 1) U.extClass := by
              simpa [Extension.extClass] using
                (ExtensionClass.toExt_pullback T.f (⟦U⟧ : ExtensionClass A T.E))
        _ = extClass S.shortExact := by simpa [hU] using hx
    have hIso : Extension.Isomorphic (Extension.pullback T.f U) S :=
      extension_isomorphic_of_extClass_eq (A := A) (B := B) hPull
    refine ⟨U, ?_⟩
    -- Equal `Ext¹` classes now give an endpoint-fixing isomorphism of the represented extensions.
    change (⟦Extension.pullback T.f U⟧ : ExtensionClass A B) = ⟦S⟧
    exact ExtensionClass.mk_eq_mk_of_isomorphic hIso

/-- Helper for Lemma 13.27.7: the Yoneda product vanishes exactly when the top extension class
lifts one step to `Ext¹(T.E, A)` in the contravariant long exact sequence of `T`. -/
lemma comp_extClass_eq_zero_iff_exists_ext_lift
    (S : Extension A B) (T : Extension B C) :
    (extClass T.shortExact).comp (extClass S.shortExact) rfl = 0 ↔
      ∃ x : Ext T.E A 1, (Ext.mk₀ T.f).precomp A (zero_add 1) x = extClass S.shortExact := by
  constructor
  · intro hcomp
    -- Exactness of the contravariant `Ext` sequence for `T` produces the desired lift.
    obtain ⟨x, hx⟩ :=
      Abelian.Ext.contravariant_sequence_exact₁
        (hS := T.shortExact) (Y := A) (x₁ := extClass S.shortExact) (hn₁ := rfl) hcomp
    exact ⟨x, by simpa [Ext.precomp] using hx⟩
  · rintro ⟨x, hx⟩
    -- Compose the given lift with the extension class of `T` and use exactness-on-the-nose.
    calc
      (extClass T.shortExact).comp (extClass S.shortExact) rfl =
          (extClass T.shortExact).comp ((Ext.mk₀ T.f).precomp A (zero_add 1) x) rfl := by
            rw [hx.symm]
      _ = 0 := by
        simpa [Ext.precomp] using
          (extClass_comp_assoc (hS := T.shortExact) (γ := x) (h := rfl))

/-- Lemma 13.27.7: for short exact sequences `S : 0 ⟶ A ⟶ E ⟶ B ⟶ 0` and
`T : 0 ⟶ B ⟶ E' ⟶ C ⟶ 0` in an abelian category, the Yoneda product of their classes in
`Ext²(C, A)` is zero if and only if there exists a commutative `3 × 3` diagram with exact
rows and columns whose middle row is `0 ⟶ A ⟶ W ⟶ E' ⟶ 0` and whose middle column is
`0 ⟶ E ⟶ W ⟶ C ⟶ 0`. -/
@[stacks 0GSM]
theorem comp_extClass_eq_zero_iff_exists_exact_three_by_three_diagram
    (S : Extension A B) (T : Extension B C) :
    (extClass T.shortExact).comp (extClass S.shortExact) rfl = 0 ↔
      Nonempty (Extension.ThreeByThree S T) := by
  -- Rewrite the diagrammatic condition into pullback equality of extension classes, then into an
  -- `Ext¹(T.E, A)` lift, so the long exact sequence closes the proof.
  rw [nonempty_threeByThree_iff_exists_pullback_extClass_eq]
  rw [exists_pullback_extClass_eq_iff_exists_ext_lift]
  exact comp_extClass_eq_zero_iff_exists_ext_lift S T

end

end CategoryTheory
