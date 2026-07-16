import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import stacks_proof.stacks_project.Chap13.Lemma_13_27_3
import stacks_proof.stacks_project.Chap13.Lemma_13_27_9
import stacks_proof.stacks_project.Chap15.Lemma_15_77_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped CategoryTheory
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- Helper for Lemma 15.77.6: if the degree-`n` derived Ext functor is zero, then each of its
values is a subsingleton Ext group. -/
private lemma ext_eq_zero_of_derivedExtToModuleFunctor_isZero
    (K : DMod) (n : ℤ)
    (hzero : IsZero (derivedExtToModuleFunctor K n))
    (M : ModuleCat R)
    (x : Ext^n(K, (single₀).obj M)) :
    x = 0 := by
  rw [Functor.isZero_iff] at hzero
  -- Proof comment: the zero-functor hypothesis says the value at `M` is a zero object in
  -- `AddCommGrpCat`, hence its underlying Ext group is a subsingleton.
  let hsubAdd :
      Subsingleton (((derivedExtToModuleFunctor K n).obj M) : Type _) :=
    AddCommGrpCat.subsingleton_of_isZero (hzero M)
  let hsubExt : Subsingleton (Ext^n(K, (single₀).obj M)) := by
    simpa [derivedExtToModuleFunctor] using hsubAdd
  exact @Subsingleton.elim _ hsubExt _ _

/-- Helper for Lemma 15.77.6: a zero derived Ext functor automatically preserves
monomorphisms. -/
private lemma derivedExtToModuleFunctor_preservesMonomorphisms_of_isZero
    (K : DMod) (n : ℤ)
    (hzero : IsZero (derivedExtToModuleFunctor K n)) :
    (derivedExtToModuleFunctor K n).PreservesMonomorphisms := by
  rw [Functor.isZero_iff] at hzero
  refine ⟨?_⟩
  intro X Y f hf
  -- Proof comment: every source value of the zero functor is a zero additive group, so the
  -- induced map is injective for trivial reasons.
  exact ConcreteCategory.mono_of_injective ((derivedExtToModuleFunctor K n).map f)
    (fun x y _ ↦ by
      let _ :
          Subsingleton (((derivedExtToModuleFunctor K n).obj X) : Type _) :=
        AddCommGrpCat.subsingleton_of_isZero (hzero X)
      exact Subsingleton.elim _ _)

/-- Helper for Lemma 15.77.6: a compatible `τ≤ a ⊞ U` splitting makes the degree-`-a` Ext of
`τ≤ a` vanish once the degree-`-a` Ext of the whole object vanishes. -/
private lemma truncLE_ext_neg_a_vanishes_of_compatible_split
    (K U : DMod) (a : ℤ)
    (e : K ≅ (t.truncLE a).obj K ⊞ U)
    (hcompat : ((t.truncLEι a).app K) ≫ e.hom = biprod.inl)
    (hExt : IsZero (derivedExtToModuleFunctor K (-a))) :
    ∀ (M : ModuleCat R),
      ∀ x : Ext^(-a)(((t.truncLE a).obj K), (single₀).obj M), x = 0 := by
  intro M x
  let r : K ⟶ (t.truncLE a).obj K := e.hom ≫ biprod.fst
  have hr : ((t.truncLEι a).app K) ≫ r = 𝟙 _ := by
    -- Proof comment: the left truncation becomes a retract through the compatible biproduct
    -- decomposition.
    calc
      ((t.truncLEι a).app K) ≫ r =
          (((t.truncLEι a).app K) ≫ e.hom) ≫ biprod.fst := by
            simp [r, Category.assoc]
      _ = biprod.inl ≫ biprod.fst := by rw [hcompat]
      _ = 𝟙 _ := by simp
  have hzeroK : r ≫ x = 0 :=
    ext_eq_zero_of_derivedExtToModuleFunctor_isZero K (-a) hExt M (r ≫ x)
  -- Proof comment: any class on `τ≤ a K` comes by restriction from a class on `K`, and those
  -- classes vanish by the zero-functor hypothesis.
  calc
    x = ((t.truncLEι a).app K) ≫ (r ≫ x) := by
      simpa [Category.assoc] using (congrArg (fun k ↦ k ≫ x) hr).symm
    _ = 0 := by simp [hzeroK]

/-- Helper for Lemma 15.77.6: the map on degree-`a` homology induced by the upper truncation
inclusion `τ≤ a Z ⟶ Z` is an isomorphism. -/
private theorem homology_map_truncLEι_isIso
    (Z : DMod) (a : ℤ) :
    IsIso ((H a).map ((t.truncLEι a).app Z)) := by
  let T : Triangle DMod := (t.triangleLEGT a).obj Z
  have hT : T ∈ distTriang DMod := by
    -- Proof comment: use the standard `τ≤ a Z ⟶ Z ⟶ τ≥ a + 1 Z` distinguished triangle.
    simpa [T] using t.triangleLEGT_distinguished a Z
  have h₃ : T.obj₃.IsGE (a + 1) := by
    dsimp [T]
    infer_instance
  have hmor₂_zero : (H a).map T.mor₂ = 0 := by
    -- Proof comment: the upper-truncation piece contributes no degree-`a` homology.
    exact (isZero_of_isGE T.obj₃ (a + 1) a (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (a - 1) a (by omega) = 0 := by
    -- Proof comment: the connecting morphism also lands in a vanishing homology group.
    exact (isZero_of_isGE T.obj₃ (a + 1) (a - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H a).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT a).2 hmor₂_zero
  letI : Mono ((H a).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (a - 1) a (by omega)).2 hδ_zero
  simpa [T] using isIso_of_mono_of_epi ((H a).map T.mor₁)

/-- Helper for Lemma 15.77.6: for an object concentrated in degrees `≤ a`, degree `0 - a` Ext
against `M[0]` identifies with morphisms from `H^a` into `M`. -/
private noncomputable abbrev ext_neg_homology_hom_equiv_of_isLE
    (X : DMod) (a : ℤ) (M : ModuleCat R) [X.IsLE a] :
    Ext^((0 : ℤ) - a)(X, (single₀).obj M) ≃ ((H a).obj X ⟶ M) :=
  ((Equiv.ofBijective (shiftedHomToHomologyMap X ((single₀).obj M) a 0)
      (shiftedHomToHomologyMap_bijective X ((single₀).obj M) a 0 inferInstance inferInstance)).trans
    ((Iso.refl _).homCongr ((singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app M))).trans
    ((Iso.refl _).homCongr (eqToIso rfl))

/-- Helper for Lemma 15.77.6: vanishing of `Ext^{-a}(τ≤ a K, M[0])` for all `M` forces
`H^a(K) = 0`. -/
private lemma homology_isZero_of_truncLE_ext_neg_a_vanishing
    (K : DMod) (a : ℤ)
    (hExt :
      ∀ (M : ModuleCat R),
        ∀ x : Ext^(-a)(((t.truncLE a).obj K), (single₀).obj M), x = 0) :
    IsZero ((H a).obj K) := by
  -- Route correction: package the degree `-a` Ext comparison as one equivalence, so the source
  -- argument becomes "the class mapping to `𝟙` is zero, hence `𝟙 = 0`".
  let X := (t.truncLE a).obj K
  let eExt :
      Ext^((0 : ℤ) - a)(X, (single₀).obj ((H a).obj X)) ≃ ((H a).obj X ⟶ (H a).obj X) :=
    ext_neg_homology_hom_equiv_of_isLE X a ((H a).obj X)
  let hExt₀ :
      ∀ x : Ext^((0 : ℤ) - a)(X, (single₀).obj ((H a).obj X)), x = 0 := by
    intro x
    -- Proof comment: rewrite the source statement from degree `-a` to the equivalent degree
    -- `0 - a` normalization before applying the vanishing hypothesis.
    have hx :
        (show Ext^(-a)(X, (single₀).obj ((H a).obj X)) from by simpa using x) = 0 :=
      hExt ((H a).obj X) (show Ext^(-a)(X, (single₀).obj ((H a).obj X)) from by simpa using x)
    convert hx using 1 <;> simp
  let xId : Ext^((0 : ℤ) - a)(X, (single₀).obj ((H a).obj X)) := eExt.symm (𝟙 _)
  have hx_zero : xId = 0 := hExt₀ xId
  have himage : eExt xId = eExt 0 := congrArg eExt hx_zero
  have hext_zero : eExt 0 = 0 := by
    -- Proof comment: the comparison equivalence is built from additive maps and identity
    -- transports, so it sends the zero class to the zero morphism.
    -- TODO: unfold the composite equivalence and normalize its action on `0` through the
    -- `singleFunctorCompHomologyFunctorIso` transport, so the target reduces to `zero_comp`.
    sorry
  have hid_zero : 𝟙 ((H a).obj X) = 0 := by
    -- Proof comment: the chosen Ext class maps to the identity, so killing the class kills the
    -- identity endomorphism on `H^a(τ≤ a K)`.
    calc
      𝟙 ((H a).obj X) = eExt xId := by simp [xId]
      _ = eExt 0 := himage
      _ = 0 := hext_zero
  have hzeroX : IsZero ((H a).obj X) := (IsZero.iff_id_eq_zero _).2 hid_zero
  let eHa : (H a).obj X ≅ (H a).obj K :=
    @asIso _ _ _ _ ((H a).map ((t.truncLEι a).app K)) (homology_map_truncLEι_isIso K a)
  -- Proof comment: `τ≤ a K ⟶ K` is an isomorphism on degree-`a` homology, so the vanishing
  -- transports from the truncation back to `K`.
  exact IsZero.of_iso hzeroX eHa.symm

/-- Helper for Lemma 15.77.6: the single object on a zero module is zero in the derived
category. -/
private theorem singleFunctor_obj_isZero_of_isZero
    (n : ℤ) {M : ModuleCat R} (hM : IsZero M) :
    IsZero ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M) := by
  -- Proof comment: the single-degree embedding preserves zero objects.
  simpa using Functor.map_isZero (DerivedCategory.singleFunctor (ModuleCat R) n) hM

/-- Helper for Lemma 15.77.6: if the right summand is zero, then the left biproduct inclusion is
an isomorphism. -/
private theorem biprod_inl_isIso_of_isZero_right
    {X Y : DMod} [HasBinaryBiproduct X Y]
    (hY : IsZero Y) :
    IsIso (biprod.inl : X ⟶ X ⊞ Y) := by
  have hsnd_zero : (biprod.snd : X ⊞ Y ⟶ Y) = 0 := by
    exact hY.eq_of_tgt _ _
  -- Proof comment: `biprod.fst` becomes a two-sided inverse once the right summand vanishes.
  refine ⟨⟨biprod.fst, ?_, ?_⟩⟩
  · simp
  · apply biprod.hom_ext
    · simp [Category.assoc]
    · simpa [Category.assoc, hsnd_zero]

/-- Helper for Lemma 15.77.6: vanishing of `H^i(X)` makes the adjacent lower-truncation
comparison `τ≤ i - 1 X ⟶ τ≤ i X` an isomorphism. -/
private theorem truncLE_step_comparison_isIso_of_homology_isZero
    (X : DMod) (i : ℤ)
    (hzero : IsZero ((H i).obj X)) :
    IsIso ((t.natTransTruncLEOfLE (i - 1) i (by omega)).app X) := by
  -- Route correction: reuse the one-step truncation triangle from Remark `13.12.4` verbatim,
  -- rather than introducing a second bridge lemma for adjacent lower truncations.
  let T : Triangle DMod := _root_.truncLE_step_homologyTriangle X (i - 1)
  have hT : T ∈ distTriang DMod := by
    -- Proof comment: this is the standard one-step lower-truncation triangle.
    simpa [T] using _root_.truncLE_step_homology_triangle (K := X) (a := i - 1)
  have h₃ : IsZero T.obj₃ := by
    -- Proof comment: the third vertex is the single object on `H^i(X)`.
    simpa [T, _root_.truncLE_step_homologyTriangle] using
      singleFunctor_obj_isZero_of_isZero i hzero
  have hzero₃ : T.mor₃ = 0 := by
    -- Proof comment: every morphism out of a zero object vanishes.
    exact h₃.eq_of_src T.mor₃ 0
  obtain ⟨e, he₁, _he₂⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hzero₃
  have hinl : IsIso (biprod.inl : T.obj₁ ⟶ T.obj₁ ⊞ T.obj₃) :=
    biprod_inl_isIso_of_isZero_right h₃
  have hcomp : IsIso (T.mor₁ ≫ e.hom) := by
    simpa [he₁] using hinl
  have hmor₁ : IsIso T.mor₁ := by
    letI : IsIso (T.mor₁ ≫ e.hom) := hcomp
    exact IsIso.of_isIso_comp_right T.mor₁ e.hom
  -- Proof comment: in this explicit triangle, `mor₁` is the adjacent truncation comparison.
  -- TODO: compare the owner `truncLT` step map in `truncLE_step_homologyTriangle` with the
  -- target `truncLE` comparison map by an explicit bridge lemma between the two truncation APIs.
  sorry

/-- Helper for Lemma 15.77.6: package the one-step lower-truncation comparison as an
isomorphism once `H^i(X)` vanishes. -/
private noncomputable def truncLE_step_iso_of_homology_isZero
    (X : DMod) (i : ℤ)
    (hzero : IsZero ((H i).obj X)) :
    (t.truncLE (i - 1)).obj X ≅ (t.truncLE i).obj X :=
  @asIso _ _ _ _
    ((t.natTransTruncLEOfLE (i - 1) i (by omega)).app X)
    (truncLE_step_comparison_isIso_of_homology_isZero X i hzero)

/-- Helper for Lemma 15.77.6: transport the unique `τ≤ i ⊞ U` splitting along an isomorphism
`τ≤ i - 1 X ≅ τ≤ i X`. -/
private theorem transport_unique_gap_split_of_truncLE_iso
    (X : DMod) (i : ℤ) (U : DMod)
    (ρ : X ⟶ U)
    {eLE : (t.truncLE (i - 1)).obj X ≅ (t.truncLE i).obj X}
    (hι :
      eLE.hom ≫ ((t.truncLEι i).app X) =
        ((t.truncLEι (i - 1)).app X))
    (hsplit :
      ∃! e : X ≅ (t.truncLE i).obj X ⊞ U,
        ((t.truncLEι i).app X) ≫ e.hom = biprod.inl ∧
          e.hom ≫ biprod.snd = ρ) :
    ∃! e : X ≅ (t.truncLE (i - 1)).obj X ⊞ U,
      ((t.truncLEι (i - 1)).app X) ≫ e.hom = biprod.inl ∧
        e.hom ≫ biprod.snd = ρ := by
  rcases hsplit with ⟨e₀, he₀, huniq₀⟩
  let e : X ≅ (t.truncLE (i - 1)).obj X ⊞ U :=
    e₀ ≪≫ biprod.mapIso eLE.symm (Iso.refl U)
  refine ⟨e, ?_, ?_⟩
  · constructor
    · -- Proof comment: conjugating by `biprod.mapIso eLE.symm (Iso.refl U)` transports the left
      -- truncation compatibility from `τ≤ i` to `τ≤ i - 1`.
      calc
        ((t.truncLEι (i - 1)).app X) ≫ e.hom =
            eLE.hom ≫ ((t.truncLEι i).app X) ≫ e.hom := by
              simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e.hom) hι.symm
        _ =
            eLE.hom ≫ (((t.truncLEι i).app X) ≫ e₀.hom) ≫
              (biprod.mapIso eLE.symm (Iso.refl U)).hom := by
              simp [e, Category.assoc]
        _ = eLE.hom ≫ biprod.inl ≫ (biprod.mapIso eLE.symm (Iso.refl U)).hom := by
              rw [he₀.1]
        _ = biprod.inl := by
              simp [Category.assoc]
    · -- Proof comment: the conjugation leaves the right projection unchanged.
      calc
        e.hom ≫ biprod.snd =
            e₀.hom ≫ (biprod.mapIso eLE.symm (Iso.refl U)).hom ≫ biprod.snd := by
              simp [e, Category.assoc]
        _ = e₀.hom ≫ biprod.snd := by
              simp [Category.assoc]
        _ = ρ := he₀.2
  · intro e' he'
    let e'' : X ≅ (t.truncLE i).obj X ⊞ U :=
      e' ≪≫ biprod.mapIso eLE (Iso.refl U)
    have he'' :
        ((t.truncLEι i).app X) ≫ e''.hom = biprod.inl ∧
          e''.hom ≫ biprod.snd = ρ := by
      constructor
      · -- Proof comment: composing back with `biprod.mapIso eLE (Iso.refl U)` recovers a
        -- compatible `τ≤ i` splitting, so uniqueness reduces to the original one.
        calc
          ((t.truncLEι i).app X) ≫ e''.hom =
              eLE.inv ≫ ((t.truncLEι (i - 1)).app X) ≫ e''.hom := by
                rw [← hι]
                simp
          _ =
              eLE.inv ≫ (((t.truncLEι (i - 1)).app X) ≫ e'.hom) ≫
                (biprod.mapIso eLE (Iso.refl U)).hom := by
                simp [e'', Category.assoc]
          _ = eLE.inv ≫ biprod.inl ≫ (biprod.mapIso eLE (Iso.refl U)).hom := by
                rw [he'.1]
          _ = biprod.inl := by
                simp [Category.assoc]
      · calc
          e''.hom ≫ biprod.snd =
              e'.hom ≫ (biprod.mapIso eLE (Iso.refl U)).hom ≫ biprod.snd := by
                simp [e'', Category.assoc]
        _ = e'.hom ≫ biprod.snd := by
              simp [Category.assoc]
        _ = ρ := he'.2
    have heq : e'' = e₀ := huniq₀ e'' he''
    have hround :
        (biprod.mapIso eLE.symm (Iso.refl U)).hom ≫
          (biprod.mapIso eLE (Iso.refl U)).hom = 𝟙 _ := by
      -- Proof comment: the forward and backward transport maps are inverse on each biproduct
      -- summand.
      apply biprod.hom_ext
      · simp [Category.assoc]
      · simp [Category.assoc]
    apply Iso.ext
    apply (cancel_mono (biprod.mapIso eLE (Iso.refl U)).hom).1
    calc
      e'.hom ≫ (biprod.mapIso eLE (Iso.refl U)).hom = e₀.hom := by
        simpa [e''] using congrArg Iso.hom heq
      _ = e₀.hom ≫ (biprod.mapIso eLE.symm (Iso.refl U)).hom ≫
            (biprod.mapIso eLE (Iso.refl U)).hom := by
              simpa [Category.assoc] using
                (congrArg (fun k ↦ e₀.hom ≫ k) hround).symm
      _ = e.hom ≫ (biprod.mapIso eLE (Iso.refl U)).hom := by
            simp [e, Category.assoc]

/-- Lemma 15.77.6: if `K` is an object of `D^-(R)` and `Ext^{-a}_R(K, M)` vanishes for every
`R`-module `M`, then there is a unique isomorphism
`K \cong \tau_{\le a - 1}K \oplus \tau_{\ge a + 1}K` compatible with the canonical truncation
maps, and the upper truncation `\tau_{\ge a + 1}K` has projective-amplitude in `[a + 1, b]` for
some `b`. -/
@[stacks 0G98]
theorem existsUnique_truncation_gap_biprod_and_projectiveAmplitude_of_ext_vanishing
    (K : D⁻((ModuleCat R))) (a : ℤ)
    (hExt : IsZero (derivedExtToModuleFunctor K.obj (-a))) :
    ∃ b : ℤ,
      HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b ∧
        ∃! e : K.obj ≅ (t.truncLE (a - 1)).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
          ((t.truncLEι (a - 1)).app K.obj) ≫ e.hom = biprod.inl ∧
            e.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj) := by
  let hMono :
      (derivedExtToModuleFunctor K.obj (-a)).PreservesMonomorphisms :=
    derivedExtToModuleFunctor_preservesMonomorphisms_of_isZero K.obj (-a) hExt
  rcases
      existsUnique_truncation_biprod_and_projectiveAmplitude_of_ext_preserves_monos K a hMono
    with ⟨b, hAmp, ⟨e, he, huniq⟩⟩
  have htruncExt :
      ∀ (M : ModuleCat R),
        ∀ x : Ext^(-a)(((t.truncLE a).obj K.obj), (single₀).obj M), x = 0 :=
    truncLE_ext_neg_a_vanishes_of_compatible_split
      K.obj ((t.truncGE (a + 1)).obj K.obj) a e he.1 hExt
  have hHa : IsZero ((H a).obj K.obj) :=
    homology_isZero_of_truncLE_ext_neg_a_vanishing K.obj a htruncExt
  let eLE : (t.truncLE (a - 1)).obj K.obj ≅ (t.truncLE a).obj K.obj :=
    truncLE_step_iso_of_homology_isZero K.obj a hHa
  have hι :
      eLE.hom ≫ (t.truncLEι a).app K.obj =
        (t.truncLEι (a - 1)).app K.obj := by
    -- Proof comment: this is the canonical compatibility of the adjacent lower truncations.
    simpa [eLE] using t.natTransTruncLEOfLE_ι_app (a - 1) a (by omega) K.obj
  have hgap :
      ∃! e' : K.obj ≅ (t.truncLE (a - 1)).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
        ((t.truncLEι (a - 1)).app K.obj) ≫ e'.hom = biprod.inl ∧
          e'.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj) := by
    -- Proof comment: transport the unique `τ≤ a ⊞ τ≥ a + 1` splitting across the one-step
    -- identification `τ≤ a - 1 ≅ τ≤ a` forced by the vanishing of `H^a(K)`.
    exact
      transport_unique_gap_split_of_truncLE_iso K.obj a
        ((t.truncGE (a + 1)).obj K.obj) ((t.truncGEπ (a + 1)).app K.obj) hι
        ⟨e, he, huniq⟩
  exact ⟨b, hAmp, hgap⟩

end

end CategoryTheory
