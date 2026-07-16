import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import stacks_proof.stacks_project.Chap13.Definition_13_15_3
import stacks_proof.stacks_project.Chap13.Lemma_13_10_2
import stacks_proof.stacks_project.Chap13.Lemma_13_14_6
import stacks_proof.stacks_project.Chap13.Lemma_13_14_11
import stacks_proof.stacks_project.Chap13.Lemma_13_14_12
import stacks_proof.stacks_project.Chap13.Lemma_13_15_2
import stacks_proof.stacks_project.Chap13.Lemma_13_16_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped CategoryTheory
open ComplexShape

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "H" => DerivedCategory.homologyFunctor ℬ

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): a cochain complex supported in the
single degree `a` becomes the corresponding single object in the homotopy category. -/
noncomputable abbrev representative_single_iso_of_strict_bounds
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE a] :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a) :=
  let M : 𝒜 := Classical.choose (CochainComplex.exists_iso_single (K := K) a)
  let e : K ≅ (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) a).obj M :=
    Classical.choice (Classical.choose_spec (CochainComplex.exists_iso_single (K := K) a))
  let eX : K.X a ≅ M :=
    (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) a).mapIso e ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M
  (HomotopyCategory.quotient 𝒜 (up ℤ)).mapIso e ≪≫
    (HomotopyCategory.singleFunctor 𝒜 a).mapIso eX.symm

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): quasi-isomorphisms in the unbounded
homotopy category are stable under shifts. This is the bridge needed to apply the generic
shift-stability API for `ComputesRightDerivedAt` to `K(\mathcal A) ⟶ D(\mathcal B)`. -/
local instance homotopyCategory_quasiIso_isCompatibleWithShift :
    (HomotopyCategory.quasiIso 𝒜 (up ℤ)).IsCompatibleWithShift ℤ where
  condition n := by
    ext X Y f
    change Qis (f⟦n⟧') ↔ Qis f
    rw [HomotopyCategory.mem_quasiIso_iff]
    rw [HomotopyCategory.mem_quasiIso_iff]
    constructor
    · intro hf j
      -- Shift the homology index back by `n` so the shifted quasi-isomorphism hypothesis matches
      -- the source of the canonical homology shift isomorphism.
      simpa [Functor.comp_map] using
        (NatIso.isIso_map_iff
          ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) 0).shiftIso
            n (j - n) j (by omega)) f).1
          (hf (j - n))
    · intro hf i
      -- The forward direction uses the same homology shift isomorphism with target degree
      -- `n + i`.
      simpa [Functor.comp_map] using
        (NatIso.isIso_map_iff
          ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) 0).shiftIso
            n i (n + i) rfl) f).2
          (hf (n + i))

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): a cochain complex concentrated in a
single degree whose unique term is right `F`-acyclic computes the unbounded right derived
functor. -/
lemma computesRightDerivedAt_single_degree_of_right_acyclic
    (K : CochainComplex 𝒜 ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE a]
    (hK : IsRightAcyclicForAdditiveFunctor F (K.X a)) :
    ComputesRightDerivedAt KtoD Qis ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- Identify the representative with the single complex concentrated in degree `a`.
  let e := representative_single_iso_of_strict_bounds (𝒜 := 𝒜) K a
  have hsingle_shift :
      ComputesRightDerivedAt KtoD Qis
        (((HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a))⟦a⟧) := by
    -- The shift of the single complex in degree `a` is the degree-zero single complex.
    exact ((mapHomotopyCategoryToDerived F).computesRightDerivedObjectProperty Qis).prop_of_iso
      (((HomotopyCategory.singleFunctors 𝒜).shiftIso a 0 a (by simp)).symm.app (K.X a))
      hK
  have hsingle :
      ComputesRightDerivedAt KtoD Qis
        ((HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a)) := by
    -- Shift invariance transports the computation statement back to degree `a`.
    exact (computesRightDerivedAt_iff_shift (F := KtoD) (S := Qis)
      (X := (HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a)) (n := a)).2 hsingle_shift
  -- Finally transport the computation statement across the chosen representative isomorphism.
  exact ((mapHomotopyCategoryToDerived F).computesRightDerivedObjectProperty Qis).prop_of_iso
    e.symm hsingle

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): termwise bounded-below right acyclicity
of a bounded-below homotopy object implies termwise right acyclicity of the underlying unbounded
homotopy object. -/
lemma isTermwiseRightAcyclic_of_termwise_boundedBelowRightAcyclic
    (A : K⁺(𝒜))
    (hA : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A) :
    IsTermwiseRightAcyclicForAdditiveFunctor F A := by
  intro n
  -- Convert each degree-zero bounded-below computation statement to the unbounded one via the
  -- canonical comparison of Lemma `13.15.2`.
  simpa [IsRightAcyclicForAdditiveFunctor, HomotopyCategory.quotient_obj_as] using
    (computes_right_derived_functor_at_iff_bounded_below
      (F := F) ((single0Plus 𝒜).obj (A.obj.as.X n))).2 (hA n)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): ambient isomorphisms preserve right
acyclicity for the additive functor `F`. -/
lemma isRightAcyclicForAdditiveFunctor_iff_of_iso
    (X Y : 𝒜) (e : X ≅ Y) :
    IsRightAcyclicForAdditiveFunctor F X ↔
      IsRightAcyclicForAdditiveFunctor F Y := by
  constructor
  · intro hX
    -- Transport the computation statement for the degree-zero single complex across the induced
    -- isomorphism in the homotopy category.
    exact ((mapHomotopyCategoryToDerived F).computesRightDerivedObjectProperty Qis).prop_of_iso
      ((HomotopyCategory.singleFunctor 𝒜 0).mapIso e) hX
  · intro hY
    -- The converse is the same transport along the inverse isomorphism.
    exact ((mapHomotopyCategoryToDerived F).computesRightDerivedObjectProperty Qis).prop_of_iso
      ((HomotopyCategory.singleFunctor 𝒜 0).mapIso e.symm) hY

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the zero object is right acyclic for the
unbounded right derived functor of an additive functor. -/
lemma isRightAcyclicForAdditiveFunctor_zero :
    IsRightAcyclicForAdditiveFunctor F (0 : 𝒜) := by
  -- The degree-zero single complex on the zero object is itself a zero object of the homotopy
  -- category, and every zero object lies in the computation object property.
  exact ObjectProperty.prop_of_isZero
    (P := (mapHomotopyCategoryToDerived F).computesRightDerivedObjectProperty Qis)
    (inferInstance : IsZero ((HomotopyCategory.singleFunctor 𝒜 0).obj (0 : 𝒜)))

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): any zero object of `\mathcal A` is
right acyclic for the unbounded right derived functor of `F`. -/
lemma isRightAcyclicForAdditiveFunctor_of_isZero
    (X : 𝒜) (hX : IsZero X) :
    IsRightAcyclicForAdditiveFunctor F X := by
  -- Transport the zero-object computation statement across the canonical isomorphism `X ≅ 0`.
  exact
    (isRightAcyclicForAdditiveFunctor_iff_of_iso (F := F) X 0 hX.isoZero).2
      (isRightAcyclicForAdditiveFunctor_zero (F := F))

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): turn an `IsIso` witness into an explicit
isomorphism. -/
private noncomputable def isoOfIsIso
    {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} (hf : IsIso f) :
    X ≅ Y := by
  let invf := hf.out.choose
  have h₁ : f ≫ invf = 𝟙 X := hf.out.choose_spec.1
  have h₂ : invf ≫ f = 𝟙 Y := hf.out.choose_spec.2
  exact ⟨f, invf, h₁, h₂⟩

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): a morphism in `D(\mathcal B)` is an
isomorphism exactly when all of its cohomology maps are isomorphisms. -/
lemma derivedCategory_isIso_iff_homology_map_isIso
    {X Y : DerivedCategory ℬ} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i : ℤ, IsIso ((H i).map f) := by
  constructor
  · intro hf
    intro i
    -- Any isomorphism stays an isomorphism after applying the cohomology functor.
    let _ : IsIso f := hf
    exact Functor.map_isIso (H i) f
  · intro hf
    -- Lift `f` to the homotopy category and detect isomorphisms there via quasi-isomorphisms.
    obtain ⟨g, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh.mapArrow) (Arrow.mk f)
    have hq : HomotopyCategory.quasiIso ℬ (ComplexShape.up ℤ) g.hom := by
      rw [HomotopyCategory.mem_quasiIso_iff]
      intro i
      haveI : IsIso e.hom := e.isIso_hom
      let eleft :
          (H i).obj (DerivedCategory.Qh.obj g.left) ≅ (H i).obj X :=
        Functor.mapIso (H i) (isoOfIsIso (Functor.map_isIso Arrow.leftFunc e.hom))
      let eright :
          (H i).obj (DerivedCategory.Qh.obj g.right) ≅ (H i).obj Y :=
        Functor.mapIso (H i) (isoOfIsIso (Functor.map_isIso Arrow.rightFunc e.hom))
      let ef : (H i).obj X ≅ (H i).obj Y := isoOfIsIso (hf i)
      have hw :
          (H i).map (Arrow.Hom.left e.hom) ≫ (H i).map f =
            (H i).map (DerivedCategory.Qh.map g.hom) ≫ (H i).map (Arrow.Hom.right e.hom) := by
        simpa [Functor.map_comp] using congrArg ((H i).map) (Arrow.w e.hom)
      have hcomp :
          IsIso ((H i).map (DerivedCategory.Qh.map g.hom) ≫
            (H i).map (Arrow.Hom.right e.hom)) := by
        haveI : IsIso (eleft.hom ≫ ef.hom) := by infer_instance
        rw [← hw]
        change IsIso (eleft.hom ≫ ef.hom)
        infer_instance
      have heright : eright.hom = (H i).map (Arrow.Hom.right e.hom) := by
        rfl
      haveI :
          IsIso ((H i).map (DerivedCategory.Qh.map g.hom) ≫ eright.hom) := by
        rw [heright]
        exact hcomp
      have hmap : IsIso ((H i).map (DerivedCategory.Qh.map g.hom)) := by
        exact IsIso.of_isIso_comp_right ((H i).map (DerivedCategory.Qh.map g.hom)) eright.hom
      rw [← NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh ℬ i) g.hom]
      exact hmap
    have hQg : IsIso (DerivedCategory.Qh.map g.hom) :=
      (DerivedCategory.isIso_Qh_map_iff g.hom).2 hq
    haveI : IsIso e.hom := e.isIso_hom
    exact (Arrow.isIso_iff_isIso_of_isIso e.hom).1 hQg

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the canonical identity-denominator legs
for pointwise right-derived values are natural in the source morphism. -/
lemma rightDerivedValueLeg_id_naturality
    {X Y : HomotopyCategory 𝒜 (up ℤ)} (f : X ⟶ Y)
    [HasPointwiseRightDerivedFunctorAt KtoD Qis X]
    [HasPointwiseRightDerivedFunctorAt KtoD Qis Y] :
    (mapHomotopyCategoryToDerived F).map f ≫
        rightDerivedValueLeg Qis KtoD (𝟙 Y)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) Y) =
      rightDerivedValueLeg Qis KtoD (𝟙 X)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) X) ≫
        rightDerivedValueMap Qis KtoD f := by
  -- The generic denominator-square compatibility specializes to the square with identity
  -- denominators on both sides.
  simpa using
    (show CommSq
        (rightDerivedValueLeg Qis KtoD (𝟙 X)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) X))
        ((mapHomotopyCategoryToDerived F).map f)
        (rightDerivedValueMap Qis KtoD f)
        (rightDerivedValueLeg Qis KtoD (𝟙 Y)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) Y)) from
      rightDerivedValueMap_comp_of_square Qis KtoD f
        (𝟙 X) (𝟙 Y)
        (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) X)
        (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) Y)
        f ⟨by simp⟩).w.symm

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): if the source truncation cutoff is at
least `i`, then applying `F` to the truncation inclusion induces an isomorphism on degree-`i`
homology. -/
lemma source_truncation_homologyMap_isIso
    (K : CochainComplex 𝒜 ℤ) (a i : ℤ) (hi : i ≤ a) :
    IsIso
      (HomologicalComplex.homologyMap
        (((F.mapHomologicalComplex (up ℤ)).map (K.ιTruncLE a)) : _)
        i) := by
  -- The mapped truncation inclusion is the canonical truncation inclusion on `F(K)`, so the
  -- standard truncation quasi-isomorphism criterion applies directly degreewise.
  have htrunc :
      QuasiIsoAt
        (((F.mapHomologicalComplex (up ℤ)).map (K.ιTruncLE a)) : _)
        i := by
    simpa using
      (CochainComplex.quasiIsoAt_ιTruncLE
        (((F.mapHomologicalComplex (up ℤ)).obj K) : CochainComplex ℬ ℤ)
        a i hi)
  -- Rewrite the quasi-isomorphism-at-degree statement to the homology map formulation.
  rwa [quasiIsoAt_iff_isIso_homologyMap] at htrunc

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): objects computing the right derived
functor are closed under the middle vertex of a distinguished triangle. -/
lemma computesRightDerivedAt_obj₂_of_distinguished_triangle
    (T : Triangle (HomotopyCategory 𝒜 (up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory 𝒜 (up ℤ)))
    (h₁ : ComputesRightDerivedAt KtoD Qis T.obj₁)
    (h₃ : ComputesRightDerivedAt KtoD Qis T.obj₃) :
    ComputesRightDerivedAt KtoD Qis T.obj₂ := by
  -- Rotate the triangle backwards so the original middle vertex becomes the third vertex.
  have h₃_shift :
      ComputesRightDerivedAt KtoD Qis (T.obj₃⟦(-1 : ℤ)⟧) := by
    exact
      (computesRightDerivedAt_iff_shift
        (F := KtoD) (S := Qis) (X := T.obj₃) (n := (-1 : ℤ))).1 h₃
  -- The third-vertex closure theorem now applies to the inverse rotation.
  simpa using
    computesRightDerivedAt_obj₃_of_distinguished_triangle
      (F := KtoD) (S := Qis)
      T.invRotate (inv_rot_of_distTriang _ hT) h₃_shift h₁

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): enlarging the upper support bound keeps a
strictly bounded-above complex strictly bounded above. -/
lemma cochainComplex_isStrictlyLE_of_le
    (K : CochainComplex 𝒜 ℤ) {b a : ℤ} [K.IsStrictlyLE b] (hba : b ≤ a) :
    K.IsStrictlyLE a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyLE b i (lt_of_lt_of_le hi hba)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): on retained degrees of the upper brutal
truncation, the truncated term canonically identifies with the original term. -/
private noncomputable def upper_stupid_truncation_x_iso
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) {i : ℤ} (hi : i ≤ a) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X i ≅ K.X i := by
  let j : ℕ := Int.toNat (a - i)
  have hj : (ComplexShape.embeddingUpIntLE a).f j = i :=
    embeddingUpIntLE_toNat_sub_eq a i hi
  exact K.stupidTruncXIso (ComplexShape.embeddingUpIntLE a) hj

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): after transporting along the retained
upper-truncation identifications, the differentials agree with those of the original complex. -/
private theorem upper_stupid_truncation_d_via_x_iso
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) {i j : ℤ}
    (hi : i ≤ a) (hj : j ≤ a) :
    (upper_stupid_truncation_x_iso (𝒜 := 𝒜) K a hi).inv ≫
      (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d i j ≫
      (upper_stupid_truncation_x_iso (𝒜 := 𝒜) K a hj).hom =
        K.d i j := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntLE a
  let i₀ : ℕ := Int.toNat (a - i)
  let j₀ : ℕ := Int.toNat (a - j)
  have hi₀ : e.f i₀ = i := embeddingUpIntLE_toNat_sub_eq a i hi
  have hj₀ : e.f j₀ = j := embeddingUpIntLE_toNat_sub_eq a j hj
  -- Read the upper brutal truncation as `restriction` followed by `extend`, then peel both
  -- constructions away to expose the original differential of `K`.
  change (upper_stupid_truncation_x_iso (𝒜 := 𝒜) K a hi).inv ≫
      ((K.restriction e).extend e).d i j ≫
      (upper_stupid_truncation_x_iso (𝒜 := 𝒜) K a hj).hom =
        K.d i j
  rw [HomologicalComplex.extend_d_eq (K := K.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := K) (e := e) hi₀ hj₀]
  simp [upper_stupid_truncation_x_iso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso, e, i₀, j₀]

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the upper brutal truncation carries a
canonical projection from the original complex. -/
private noncomputable def upper_stupid_truncation_projection
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) :
    K ⟶ K.stupidTrunc (ComplexShape.embeddingUpIntLE a) where
  f i :=
    if hi : i ≤ a then
      (upper_stupid_truncation_x_iso (𝒜 := 𝒜) K a hi).inv
    else
      0
  comm' i j hij := by
    by_cases hi : i ≤ a
    · have hj : j ≤ a := by
        have hij' : j = i + 1 := by
          simpa [ComplexShape.up, eq_comm] using hij
        omega
      rw [dif_pos hi, dif_pos hj]
      have hdiff :
          (upper_stupid_truncation_x_iso (𝒜 := 𝒜) K a hi).inv ≫
              (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).d i j =
            K.d i j ≫ (upper_stupid_truncation_x_iso (𝒜 := 𝒜) K a hj).inv := by
        -- Postcompose the transported-differential identity with the inverse of the retained
        -- target-degree isomorphism.
        have h :=
          upper_stupid_truncation_d_via_x_iso (𝒜 := 𝒜) K a hi hj
        have h' := congrArg (fun f ↦ f ≫ (upper_stupid_truncation_x_iso (𝒜 := 𝒜) K a hj).inv) h
        simpa [Category.assoc] using h'
      simpa [Category.assoc] using hdiff.symm
    · have hj : ¬ j ≤ a := by
        have hij' : j = i + 1 := by
          simpa [ComplexShape.up, eq_comm] using hij
        omega
      simp [upper_stupid_truncation_projection, hi, hj]

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): after transporting along the retained
upper-truncation term isomorphism, right acyclicity of the ambient term descends to the upper
brutal truncation. -/
lemma upper_stupid_truncation_X_rightAcyclic
    (K : CochainComplex 𝒜 ℤ) (a n : ℤ) (hn : n ≤ a)
    (hX : IsRightAcyclicForAdditiveFunctor F (K.X n)) :
    IsRightAcyclicForAdditiveFunctor F
      ((K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X n) := by
  -- The upper brutal truncation keeps the degree-`n` term up to the canonical retained-term
  -- identification, so right acyclicity transports across that isomorphism.
  exact
    (isRightAcyclicForAdditiveFunctor_iff_of_iso (F := F)
      ((K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X n) (K.X n)
      (upper_stupid_truncation_x_iso (𝒜 := 𝒜) K a hn)).2 hX

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): if the original complex is strictly zero
below `c`, then its upper brutal truncation is still strictly zero below `c`. -/
lemma upper_stupid_truncation_isStrictlyGE
    (K : CochainComplex 𝒜 ℤ) (a c : ℤ) [K.IsStrictlyGE c] :
    (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).IsStrictlyGE c := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  by_cases hia : i ≤ a
  · -- On retained degrees, transport the vanishing statement from the ambient complex.
    let hKi : IsZero (K.X i) := K.isZero_of_isStrictlyGE c i hi
    exact hKi.of_iso (upper_stupid_truncation_x_iso (𝒜 := 𝒜) K a hia)
  · -- Above the cutoff, the upper brutal truncation vanishes by construction.
    exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE a) i
      (by
        intro n hn
        dsimp [ComplexShape.embeddingUpIntLE] at hn
        omega)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the upper brutal truncation is strictly
zero above its cutoff degree. -/
lemma upper_stupid_truncation_isStrictlyLE
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).IsStrictlyLE a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  -- Above the cutoff, the upper brutal truncation vanishes by construction.
  exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE a) i
    (by
      intro n hn
      dsimp [ComplexShape.embeddingUpIntLE] at hn
      omega)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): on retained degrees of the lower brutal
truncation, the truncated term canonically identifies with the original term. -/
private noncomputable def lower_stupid_truncation_x_iso
    (K : CochainComplex 𝒜 ℤ) (t : ℤ) {i : ℤ} (hti : t ≤ i) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X i ≅ K.X i :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntGE t)
    (embeddingUpIntGE_toNat_sub_eq t i hti)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): after transporting along the retained
lower-truncation identifications, the differentials agree with those of the original complex. -/
private theorem lower_stupid_truncation_d_via_x_iso
    (K : CochainComplex 𝒜 ℤ) (t : ℤ) {i j : ℤ}
    (hti : t ≤ i) (htj : t ≤ j) :
    (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t hti).inv ≫
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
      (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t htj).hom =
        K.d i j := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntGE t
  let i₀ : ℕ := Int.toNat (i - t)
  let j₀ : ℕ := Int.toNat (j - t)
  have hi₀ : e.f i₀ = i := embeddingUpIntGE_toNat_sub_eq t i hti
  have hj₀ : e.f j₀ = j := embeddingUpIntGE_toNat_sub_eq t j htj
  -- Read the lower brutal truncation as `restriction` followed by `extend`, then peel both
  -- constructions away to expose the original differential of `K`.
  change (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t hti).inv ≫
      ((K.restriction e).extend e).d i j ≫
      (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t htj).hom =
        K.d i j
  rw [HomologicalComplex.extend_d_eq (K := K.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := K) (e := e) hi₀ hj₀]
  simp [lower_stupid_truncation_x_iso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso, e, i₀, j₀]

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the lower brutal truncation carries a
canonical inclusion into the original complex. -/
private noncomputable def lower_stupid_truncation_inclusion
    (K : CochainComplex 𝒜 ℤ) (t : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE t) ⟶ K where
  f i :=
    if hti : t ≤ i then
      (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t hti).hom
    else
      0
  comm' i j hij := by
    by_cases hti : t ≤ i
    · have htj : t ≤ j := by
        have hj : j = i + 1 := by
          simpa [ComplexShape.up, eq_comm] using hij
        omega
      rw [dif_pos hti, dif_pos htj]
      calc
        (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t hti).hom ≫ K.d i j =
            (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t hti).hom ≫
              ((lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t hti).inv ≫
                (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
                  (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t htj).hom) := by
              rw [lower_stupid_truncation_d_via_x_iso (𝒜 := 𝒜) K t hti htj]
        _ = (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j ≫
              (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t htj).hom := by
              simp [Category.assoc]
    · have hzero :
          IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).X i) := by
        -- Below the cutoff, the lower brutal truncation has no degree-`i` term.
        exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) i
          (by
            simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
              lt_of_not_ge hti)
      by_cases htj : t ≤ j
      · have hsrczero :
            (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j = 0 :=
          hzero.eq_of_src ((K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).d i j) 0
        simp [lower_stupid_truncation_inclusion, hti, htj, hsrczero]
      · simp [lower_stupid_truncation_inclusion, hti, htj]

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): after transporting along the retained
lower-truncation term isomorphism, right acyclicity of the ambient term descends to the lower
brutal truncation. -/
lemma lower_stupid_truncation_X_rightAcyclic
    (K : CochainComplex 𝒜 ℤ) (a n : ℤ) (hn : a + 1 ≤ n)
    (hX : IsRightAcyclicForAdditiveFunctor F (K.X n)) :
    IsRightAcyclicForAdditiveFunctor F
      ((K.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))).X n) := by
  -- The lower brutal truncation keeps the degree-`n` term up to the canonical retained-term
  -- identification, so right acyclicity transports across that isomorphism.
  exact
    (isRightAcyclicForAdditiveFunctor_iff_of_iso (F := F)
      ((K.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))).X n) (K.X n)
      (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K (a + 1) hn)).2 hX

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): on the retained support interval, the
lower brutal truncation inherits the termwise right acyclicity of the original complex. -/
lemma lower_stupid_truncation_interval_rightAcyclic
    (K : CochainComplex 𝒜 ℤ) (a b : ℤ)
    (hK : ∀ n : ℤ, a + 1 ≤ n → n ≤ b →
      IsRightAcyclicForAdditiveFunctor F (K.X n)) :
    ∀ n : ℤ, a + 1 ≤ n → n ≤ b →
      IsRightAcyclicForAdditiveFunctor F
        ((K.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))).X n) := by
  intro n hn₁ hn₂
  -- Each retained term of the lower brutal truncation is canonically the corresponding term of
  -- `K`, so the interval-local acyclicity hypothesis transports degreewise.
  exact lower_stupid_truncation_X_rightAcyclic (F := F) K a n hn₁ (hK n hn₁ hn₂)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): if the original complex is strictly zero
above `b`, then its lower brutal truncation is still strictly zero above `b`. -/
lemma lower_stupid_truncation_isStrictlyLE
    (K : CochainComplex 𝒜 ℤ) (t b : ℤ) [K.IsStrictlyLE b] :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_cases hti : t ≤ i
  · -- On retained degrees, transport the vanishing statement from the ambient complex.
    let hKi : IsZero (K.X i) := K.isZero_of_isStrictlyLE b i hi
    exact hKi.of_iso (lower_stupid_truncation_x_iso (𝒜 := 𝒜) K t hti)
  · -- Below the cutoff, the lower brutal truncation vanishes by construction.
    exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) i
      (by
        simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hti)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the lower brutal truncation is strictly
zero below its cutoff degree. -/
lemma lower_stupid_truncation_isStrictlyGE
    (K : CochainComplex 𝒜 ℤ) (t : ℤ) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)).IsStrictlyGE t := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  -- Below the cutoff, the lower brutal truncation vanishes by construction.
  exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE t) i
    (by
      simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hi)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the brutal cut maps
`σ_{≥ a+1}K ⟶ K ⟶ σ_{≤ a}K` compose to zero. -/
private theorem stupid_truncation_cut_comp_zero
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) :
    lower_stupid_truncation_inclusion (𝒜 := 𝒜) K (a + 1) ≫
        upper_stupid_truncation_projection (𝒜 := 𝒜) K a =
      0 := by
  ext i
  by_cases hi : i ≤ a
  · have hnot : ¬ a + 1 ≤ i := by omega
    simp [HomologicalComplex.comp_f, lower_stupid_truncation_inclusion,
      upper_stupid_truncation_projection, hi, hnot]
  · simp [HomologicalComplex.comp_f, lower_stupid_truncation_inclusion,
    upper_stupid_truncation_projection, hi]

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the brutal cut
`σ_{≥ a+1}K ⟶ K ⟶ σ_{≤ a}K` packaged as a short complex. -/
private noncomputable def stupid_truncation_cut_short_complex
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk
    (lower_stupid_truncation_inclusion (𝒜 := 𝒜) K (a + 1))
    (upper_stupid_truncation_projection (𝒜 := 𝒜) K a)
    (stupid_truncation_cut_comp_zero (𝒜 := 𝒜) K a)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): every degree of the brutal cut short
complex splits, with one outer term zero below the cutoff and the other zero above it. -/
private theorem stupid_truncation_cut_degreewise_splitting
    (K : CochainComplex 𝒜 ℤ) (a i : ℤ) :
    ((stupid_truncation_cut_short_complex (𝒜 := 𝒜) K a).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)).Splitting := by
  let S :=
    (stupid_truncation_cut_short_complex (𝒜 := 𝒜) K a).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
  by_cases hi : i ≤ a
  · change S.Splitting
    have hX₁ : IsZero S.X₁ := by
      dsimp [S, stupid_truncation_cut_short_complex]
      exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (a + 1)) i
        (by
          simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
            lt_of_lt_of_le (by omega : i < a + 1) le_rfl)
    have hg : IsIso S.g := by
      dsimp [S, stupid_truncation_cut_short_complex, upper_stupid_truncation_projection]
      rw [dif_pos hi]
      infer_instance
    exact ShortComplex.Splitting.ofIsZeroOfIsIso S hX₁ hg
  · change S.Splitting
    have hX₃ : IsZero S.X₃ := by
      dsimp [S, stupid_truncation_cut_short_complex]
      exact K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE a) i
        (by
          intro n hn
          dsimp [ComplexShape.embeddingUpIntLE] at hn
          omega)
    have hf : IsIso S.f := by
      dsimp [S, stupid_truncation_cut_short_complex, lower_stupid_truncation_inclusion]
      have hge : a + 1 ≤ i := by omega
      rw [dif_pos hge]
      infer_instance
    exact ShortComplex.Splitting.ofIsIsoOfIsZero S hf hX₃

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the brutal cut
`σ_{≥ a+1}K ⟶ K ⟶ σ_{≤ a}K` is a degreewise split short complex, hence yields a distinguished
triangle in the homotopy category. -/
lemma stupid_truncation_cut_triangle_distinguished
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) :
    let S := stupid_truncation_cut_short_complex (𝒜 := 𝒜) K a
    let σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting :=
      stupid_truncation_cut_degreewise_splitting (𝒜 := 𝒜) K a
    let T := CochainComplex.trianglehOfDegreewiseSplit S σ
    Triangle.mk ((HomotopyCategory.quotient 𝒜 (up ℤ)).map S.f) T.mor₂ T.mor₃ ∈
      distTriang (HomotopyCategory 𝒜 (up ℤ)) := by
  let S := stupid_truncation_cut_short_complex (𝒜 := 𝒜) K a
  let σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting :=
    stupid_truncation_cut_degreewise_splitting (𝒜 := 𝒜) K a
  let T := CochainComplex.trianglehOfDegreewiseSplit S σ
  -- The canonical degreewise-split short-complex triangle is distinguished in the homotopy
  -- category by the standard bridge from Lemma 13.10.2.
  simpa [S, T] using
    CochainComplex.triangle_mk_mem_distTriang_of_degreewise_split_short_complex
      (V := 𝒜) S σ

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the upper brutal truncation at degree
`a` is concentrated in degree `a`, so the single retained term computes the derived value as soon
as that term is right `F`-acyclic. -/
lemma computesRightDerivedAt_upper_stupid_truncation_of_rightAcyclic
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hKa : IsRightAcyclicForAdditiveFunctor F (K.X a)) :
    ComputesRightDerivedAt KtoD Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj
        (K.stupidTrunc (ComplexShape.embeddingUpIntLE a))) := by
  let L := K.stupidTrunc (ComplexShape.embeddingUpIntLE a)
  letI : L.IsStrictlyGE a := upper_stupid_truncation_isStrictlyGE (𝒜 := 𝒜) K a a
  letI : L.IsStrictlyLE a := upper_stupid_truncation_isStrictlyLE (𝒜 := 𝒜) K a
  have hLa :
      IsRightAcyclicForAdditiveFunctor F (L.X a) := by
    -- The retained degree-`a` term is canonically the original degree-`a` term.
    simpa [L] using
      upper_stupid_truncation_X_rightAcyclic (F := F) K a a le_rfl hKa
  -- The brutal upper truncation is now a single-degree complex, so the one-term computation
  -- lemma applies directly.
  simpa [L] using
    computesRightDerivedAt_single_degree_of_right_acyclic (F := F) L a hLa

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the brutal bounded-support case should
be proved by induction on the width of the support interval, peeling off one term with stupid
truncation triangles. -/
lemma computesRightDerivedAt_of_strict_bounds_termwise_rightAcyclic
    (K : CochainComplex 𝒜 ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ n : ℤ, a ≤ n → n ≤ b →
      IsRightAcyclicForAdditiveFunctor F (K.X n)) :
    ComputesRightDerivedAt KtoD Qis ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- Route correction: the right source-faithful triangle is the termwise split short complex
  -- `σ_{≥ a + 1}K ⟶ K ⟶ σ_{≤ a}K` built from brutal truncations, and the middle-vertex closure
  -- is handled by `computesRightDerivedAt_obj₂_of_distinguished_triangle`.
  let P :
      ℕ → Prop :=
    fun n ↦
      ∀ {a b : ℤ} (L : CochainComplex 𝒜 ℤ),
        Int.toNat (b - a) = n →
        L.IsStrictlyGE a →
        L.IsStrictlyLE b →
        (∀ m : ℤ, a ≤ m → m ≤ b →
          IsRightAcyclicForAdditiveFunctor F (L.X m)) →
        ComputesRightDerivedAt KtoD Qis ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj L)
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n with
    | zero =>
        intro a b L hn hGE hLE hL
        by_cases hab : a ≤ b
        · have hba : b ≤ a := by
            have hsub : b - a = 0 := by
              calc
                b - a = (Int.toNat (b - a) : ℤ) := by
                  symm
                  exact Int.toNat_of_nonneg (sub_nonneg.mpr hab)
                _ = 0 := by
                  simpa using congrArg (fun m : ℕ ↦ (m : ℤ)) hn
            omega
          have hb_eq : b = a := by
            omega
          subst b
          letI : L.IsStrictlyGE a := hGE
          letI : L.IsStrictlyLE a := by
            simpa using hLE
          -- Width `0` means only degree `a` can survive, so the single-degree computation lemma
          -- applies to the unique right-acyclic term.
          exact computesRightDerivedAt_single_degree_of_right_acyclic (F := F) L a
            (hL a le_rfl le_rfl)
        · have hlt : b < a := by
            omega
          letI : L.IsStrictlyGE a := hGE
          letI : L.IsStrictlyLE a :=
            cochainComplex_isStrictlyLE_of_le (𝒜 := 𝒜) L (b := b) (a := a) (le_of_lt hlt)
          have hLa_zero : IsZero (L.X a) := by
            exact (show L.IsStrictlyLE b from hLE).isZero_of_isStrictlyLE b a hlt
          have hLa :
              IsRightAcyclicForAdditiveFunctor F (L.X a) := by
            -- In the empty-support base case, the only potentially surviving degree is already
            -- zero, hence right acyclic.
            exact isRightAcyclicForAdditiveFunctor_of_isZero (F := F) (L.X a) hLa_zero
          exact computesRightDerivedAt_single_degree_of_right_acyclic (F := F) L a hLa
    | succ n ih =>
        intro a b L hn hGE hLE hL
        have hab : a ≤ b := by
          by_contra hba
          have hnonpos : b - a ≤ 0 := by
            omega
          have : Int.toNat (b - a) = 0 := by
            rw [Int.toNat_eq_zero]
            exact hnonpos
          omega
        have hwidth : b - a = ((n + 1 : ℕ) : ℤ) := by
          rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
          exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
        have hn' : Int.toNat (b - (a + 1)) = n := by
          rw [show b - (a + 1) = (n : ℤ) by omega]
          simp
        letI : L.IsStrictlyGE a := hGE
        letI : L.IsStrictlyLE b := hLE
        let Llower : CochainComplex 𝒜 ℤ :=
          L.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))
        let Lupper : CochainComplex 𝒜 ℤ :=
          L.stupidTrunc (ComplexShape.embeddingUpIntLE a)
        have hupper :
            ComputesRightDerivedAt KtoD Qis
              ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj Lupper) := by
          -- The upper brutal piece keeps only the degree-`a` term.
          exact computesRightDerivedAt_upper_stupid_truncation_of_rightAcyclic
            (F := F) L a (hL a le_rfl hab)
        have hlower :
            ComputesRightDerivedAt KtoD Qis
              ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj Llower) := by
          let hGE_lower : Llower.IsStrictlyGE (a + 1) :=
            lower_stupid_truncation_isStrictlyGE (𝒜 := 𝒜) L (a + 1)
          let hLE_lower : Llower.IsStrictlyLE b :=
            lower_stupid_truncation_isStrictlyLE (𝒜 := 𝒜) L (a + 1) b
          -- The lower brutal piece has strictly smaller width and inherits the interval-local
          -- right-acyclicity on `[a + 1, b]`.
          exact ih (a := a + 1) (b := b) Llower hn' hGE_lower hLE_lower
            (lower_stupid_truncation_interval_rightAcyclic (F := F) L a b (by
              intro m hm₁ hm₂
              exact hL m (by omega) hm₂))
        let S := stupid_truncation_cut_short_complex (𝒜 := 𝒜) L a
        let σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting :=
          stupid_truncation_cut_degreewise_splitting (𝒜 := 𝒜) L a
        let T := CochainComplex.trianglehOfDegreewiseSplit S σ
        have hT :
            Triangle.mk ((HomotopyCategory.quotient 𝒜 (up ℤ)).map S.f) T.mor₂ T.mor₃ ∈
              distTriang (HomotopyCategory 𝒜 (up ℤ)) := by
          simpa [S, T] using stupid_truncation_cut_triangle_distinguished (𝒜 := 𝒜) L a
        -- The brutal cut distinguished triangle has outer vertices computing `RF`, so the middle
        -- vertex does as well.
        simpa [S, T, Llower, Lupper] using
          computesRightDerivedAt_obj₂_of_distinguished_triangle
            (F := F)
            (T := Triangle.mk ((HomotopyCategory.quotient 𝒜 (up ℤ)).map S.f) T.mor₂ T.mor₃)
            hT hlower hupper
  letI : K.IsStrictlyGE a := inferInstance
  letI : K.IsStrictlyLE b := inferInstance
  exact hP (Int.toNat (b - a)) K rfl inferInstance inferInstance hK

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): if the unbounded right derived functor
is defined at `A` and the bounded upper brutal cut computes it, then the complementary lower
brutal truncation is also a defined stage. -/
lemma hasPointwiseRightDerivedFunctorAt_lower_stupid_truncation_of_cut
    (A : K⁺(𝒜))
    (hder : HasPointwiseRightDerivedFunctorAt KtoD Qis A.obj)
    (hA : IsTermwiseRightAcyclicForAdditiveFunctor F A)
    (i : ℤ) :
    HasPointwiseRightDerivedFunctorAt KtoD Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj
        (A.obj.as.stupidTrunc (ComplexShape.embeddingUpIntGE (i + 2)))) := by
  let K : CochainComplex 𝒜 ℤ := A.obj.as
  obtain ⟨a₀, hKplus⟩ := (CochainComplex.plus_iff 𝒜 K).1 (by
    simpa [K] using A.property)
  letI : K.IsStrictlyGE a₀ := hKplus
  let Kupper : CochainComplex 𝒜 ℤ := K.stupidTrunc (ComplexShape.embeddingUpIntLE (i + 1))
  let Klower : CochainComplex 𝒜 ℤ := K.stupidTrunc (ComplexShape.embeddingUpIntGE (i + 2))
  have hupper :
      ComputesRightDerivedAt KtoD Qis
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj Kupper) := by
    letI : Kupper.IsStrictlyGE a₀ :=
      upper_stupid_truncation_isStrictlyGE (𝒜 := 𝒜) K (i + 1) a₀
    letI : Kupper.IsStrictlyLE (i + 1) :=
      upper_stupid_truncation_isStrictlyLE (𝒜 := 𝒜) K (i + 1)
    -- The bounded upper brutal cut is supported on `[a₀, i + 1]`, so the bounded-support Leray
    -- step applies directly.
    exact computesRightDerivedAt_of_strict_bounds_termwise_rightAcyclic
      (F := F) Kupper a₀ (i + 1)
      (by
        intro n hn₁ hn₂
        simpa [Kupper] using
          upper_stupid_truncation_X_rightAcyclic (F := F) K (i + 1) n hn₂
            (hA n))
  let S := stupid_truncation_cut_short_complex (𝒜 := 𝒜) K (i + 1)
  let σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting :=
    stupid_truncation_cut_degreewise_splitting (𝒜 := 𝒜) K (i + 1)
  let T := CochainComplex.trianglehOfDegreewiseSplit S σ
  have hT :
      Triangle.mk ((HomotopyCategory.quotient 𝒜 (up ℤ)).map S.f) T.mor₂ T.mor₃ ∈
        distTriang (HomotopyCategory 𝒜 (up ℤ)) := by
    simpa [S, T] using stupid_truncation_cut_triangle_distinguished (𝒜 := 𝒜) K (i + 1)
  have hT₂ :
      HasPointwiseRightDerivedFunctorAt KtoD Qis
        (Triangle.mk ((HomotopyCategory.quotient 𝒜 (up ℤ)).map S.f) T.mor₂ T.mor₃).obj₂ := by
    -- The middle vertex is the original bounded-below complex.
    simpa [S, T, K] using hder
  have hT₃ :
      HasPointwiseRightDerivedFunctorAt KtoD Qis
        (Triangle.mk ((HomotopyCategory.quotient 𝒜 (up ℤ)).map S.f) T.mor₂ T.mor₃).obj₃ := by
    -- The upper brutal piece computes `RF`, hence in particular lies in the definedness owner.
    simpa [S, T, Kupper] using hupper.toHasPointwiseRightDerivedFunctorAt
  -- Two-out-of-three for the definedness object property recovers the lower brutal stage.
  simpa [S, T, Klower] using
    (rightDerivedDefinedObjectProperty KtoD Qis).ext_of_isTriangulatedClosed₁
      (Triangle.mk ((HomotopyCategory.quotient 𝒜 (up ℤ)).map S.f) T.mor₂ T.mor₃)
      hT hT₂ hT₃

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): after applying `F` termwise and passing
to the derived category, the lower brutal truncation lies in the canonical lower aisle
`D(\mathcal B)^{\ge t}`. -/
lemma lower_stupid_truncation_source_stage_isGE
    (K : CochainComplex 𝒜 ℤ) (t : ℤ) :
    ((KtoD).obj ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE t)))).IsGE t := by
  -- The lower brutal truncation is strictly zero below `t`, so its image under `F` has the same
  -- derived-category lower bound.
  exact
    mapHomotopyCategoryToDerived_obj_isGE_of_isStrictlyGE (F := F) t
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE t))
      (lower_stupid_truncation_isStrictlyGE (𝒜 := 𝒜) K t)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): for a fixed degree `i`, the canonical
identity-denominator leg on a bounded-below termwise right-acyclic complex induces an isomorphism
on `H^i` by comparing the inverse-rotated brutal-cut triangles on the source and derived sides. -/
lemma rightDerivedValueLeg_homologyMap_isIso_of_stupid_cut
    (A : K⁺(𝒜))
    (hder : HasPointwiseRightDerivedFunctorAt KtoD Qis A.obj)
    (hA : IsTermwiseRightAcyclicForAdditiveFunctor F A)
    (i : ℤ) :
    IsIso ((H i).map
      (rightDerivedValueLeg Qis KtoD (𝟙 A.obj) (MorphismProperty.id_mem Qis A.obj))) := by
  -- Route correction: the remaining fixed-degree step should run on the inverse-rotated brutal
  -- cut triangle so that the map on `H^i(A)` is the middle vertical arrow in the five-term row.
  let K : CochainComplex 𝒜 ℤ := A.obj.as
  obtain ⟨a₀, hKplus⟩ := (CochainComplex.plus_iff 𝒜 K).1 (by
    simpa [K] using A.property)
  letI : K.IsStrictlyGE a₀ := hKplus
  let Kupper : CochainComplex 𝒜 ℤ := K.stupidTrunc (ComplexShape.embeddingUpIntLE (i + 1))
  let Klower : CochainComplex 𝒜 ℤ := K.stupidTrunc (ComplexShape.embeddingUpIntGE (i + 2))
  let S := stupid_truncation_cut_short_complex (𝒜 := 𝒜) K (i + 1)
  let σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting :=
    stupid_truncation_cut_degreewise_splitting (𝒜 := 𝒜) K (i + 1)
  let Ttriangle := CochainComplex.trianglehOfDegreewiseSplit S σ
  let T0 :
      Triangle (HomotopyCategory 𝒜 (up ℤ)) :=
    Triangle.mk ((HomotopyCategory.quotient 𝒜 (up ℤ)).map S.f) Ttriangle.mor₂ Ttriangle.mor₃
  let T : Triangle (HomotopyCategory 𝒜 (up ℤ)) := T0.invRotate
  have hT0 : T0 ∈ distTriang (HomotopyCategory 𝒜 (up ℤ)) := by
    -- The brutal cut short complex is degreewise split, hence its homotopy-category triangle is
    -- distinguished.
    simpa [T0, S, σ, Ttriangle] using
      stupid_truncation_cut_triangle_distinguished (𝒜 := 𝒜) K (i + 1)
  have hT : T ∈ distTriang (HomotopyCategory 𝒜 (up ℤ)) := by
    -- Inverse rotation puts `A` in the third vertex, matching the five-term row used below.
    simpa [T] using inv_rot_of_distTriang (HomotopyCategory 𝒜 (up ℤ)) hT0
  have hupper :
      ComputesRightDerivedAt KtoD Qis
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj Kupper) := by
    letI : Kupper.IsStrictlyGE a₀ :=
      upper_stupid_truncation_isStrictlyGE (𝒜 := 𝒜) K (i + 1) a₀
    letI : Kupper.IsStrictlyLE (i + 1) :=
      upper_stupid_truncation_isStrictlyLE (𝒜 := 𝒜) K (i + 1)
    -- The upper brutal piece is bounded and inherits termwise right acyclicity from `A`.
    exact computesRightDerivedAt_of_strict_bounds_termwise_rightAcyclic
      (F := F) Kupper a₀ (i + 1) (by
        intro n hn₁ hn₂
        simpa [Kupper] using
          upper_stupid_truncation_X_rightAcyclic (F := F) K (i + 1) n hn₂ (hA n))
  have hupper_shift :
      ComputesRightDerivedAt KtoD Qis
        (((HomotopyCategory.quotient 𝒜 (up ℤ)).obj Kupper)⟦(-1 : ℤ)⟧) := by
    -- Shift stability turns the upper brutal piece into the first vertex of `T`.
    exact
      (computesRightDerivedAt_iff_shift
        (F := KtoD) (S := Qis)
        (X := (HomotopyCategory.quotient 𝒜 (up ℤ)).obj Kupper)
        (n := (-1 : ℤ))).1 hupper
  have hTobj₁ :
      ComputesRightDerivedAt KtoD Qis T.obj₁ := by
    simpa [T, T0, Kupper, Triangle.invRotate] using hupper_shift
  have hTobj₂_defined :
      HasPointwiseRightDerivedFunctorAt KtoD Qis T.obj₂ := by
    -- Two-out-of-three for the brutal cut supplies right-derived definedness of the lower piece.
    simpa [T, T0, Klower, Triangle.invRotate] using
      hasPointwiseRightDerivedFunctorAt_lower_stupid_truncation_of_cut
        (F := F) A hder hA i
  have hTobj₃_defined :
      HasPointwiseRightDerivedFunctorAt KtoD Qis T.obj₃ := by
    simpa [T, T0, Triangle.invRotate] using hder
  letI : ComputesRightDerivedAt KtoD Qis T.obj₁ := hTobj₁
  letI : HasPointwiseRightDerivedFunctorAt KtoD Qis T.obj₂ := hTobj₂_defined
  letI : HasPointwiseRightDerivedFunctorAt KtoD Qis T.obj₃ := hTobj₃_defined
  let Tder :
      Triangle (DerivedCategory ℬ) :=
    Triangle.mk (rightDerivedValueMap Qis KtoD T.mor₁)
      (rightDerivedValueMap Qis KtoD T.mor₂)
      (rightDerivedValueMap Qis KtoD T.mor₃ ≫
        (rightDerivedValueShiftIso KtoD Qis T.obj₁ (1 : ℤ)).hom)
  have hTder : Tder ∈ distTriang (DerivedCategory ℬ) := by
    -- The right-derived values of a distinguished triangle again form a distinguished triangle.
    simpa [Tder] using
      right_derived_triangle_distinguished
        (F := KtoD) (S := Qis)
        (X := T.obj₁) (Y := T.obj₂) (Z := T.obj₃)
        (f := T.mor₁) (g := T.mor₂) (h := T.mor₃) hT
  let φ := right_derived_comparison_triangle_morphism (F := KtoD) (S := Qis) T
  let R₁ : ComposableArrows ℬ 4 :=
    ((H 0).homologySequenceComposableArrows₅ ((KtoD).mapTriangle.obj T) i (i + 1) rfl).δlast
  let R₂ : ComposableArrows ℬ 4 :=
    ((H 0).homologySequenceComposableArrows₅ Tder i (i + 1) rfl).δlast
  let ψ₅ :
      (H 0).homologySequenceComposableArrows₅ ((KtoD).mapTriangle.obj T) i (i + 1) rfl ⟶
        (H 0).homologySequenceComposableArrows₅ Tder i (i + 1) rfl :=
    homMk₅ ((H i).map φ.hom₁) ((H i).map φ.hom₂) ((H i).map φ.hom₃)
      ((H (i + 1)).map φ.hom₁) ((H (i + 1)).map φ.hom₂) ((H (i + 1)).map φ.hom₃)
      (by simpa [Functor.map_comp] using congrArg ((H i).map) φ.comm₁)
      (by simpa [Functor.map_comp] using congrArg ((H i).map) φ.comm₂)
      (by
        simpa using
          ((H 0).homologySequenceδ_naturality ((KtoD).mapTriangle.obj T) Tder φ i (i + 1) rfl).symm)
      (by simpa [Functor.map_comp] using congrArg ((H (i + 1)).map) φ.comm₁)
      (by simpa [Functor.map_comp] using congrArg ((H (i + 1)).map) φ.comm₂)
  let ψ : R₁ ⟶ R₂ := δlastFunctor.map ψ₅
  have hR₁ : R₁.Exact := by
    -- This is the centered five-term exact row for the `F`-image of the inverse-rotated brutal
    -- cut triangle.
    simpa [R₁] using
      ((H 0).homologySequenceComposableArrows₅_exact ((KtoD).mapTriangle.obj T)
        ((KtoD).map_distinguished T hT) i (i + 1) rfl).δlast
  have hR₂ : R₂.Exact := by
    -- The same exactness statement holds for the induced right-derived triangle.
    simpa [R₂] using
      ((H 0).homologySequenceComposableArrows₅_exact Tder hTder i (i + 1) rfl).δlast
  have hupper_slot₀ : IsIso (app' ψ 0) := by
    -- The first slot is the degree-`i` homology map of the upper brutal piece shifted by `[-1]`,
    -- which computes the derived value.
    simpa [ψ, ψ₅, φ, right_derived_comparison_triangle_morphism] using
      (show IsIso ((H i).map φ.hom₁) by infer_instance)
  have hupper_slot₃ : IsIso (app' ψ 3) := by
    -- The fourth slot is the same comparison one degree later.
    simpa [ψ, ψ₅, φ, right_derived_comparison_triangle_morphism] using
      (show IsIso ((H (i + 1)).map φ.hom₁) by infer_instance)
  have hlower_source_i :
      IsZero ((H i).obj ((KtoD).obj T.obj₂)) := by
    -- The source lower brutal stage lies in degrees `≥ i + 2`, so `H^i` vanishes.
    let hGE := lower_stupid_truncation_source_stage_isGE (F := F) K (i + 2)
    letI :
        ((KtoD).obj ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj Klower)).IsGE (i + 2) := hGE
    simpa [T, T0, Klower, Triangle.invRotate] using
      (DerivedCategory.isZero_of_isGE
        ((KtoD).obj ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj Klower))
        (i + 2) i (by omega))
  have hlower_source_succ :
      IsZero ((H (i + 1)).obj ((KtoD).obj T.obj₂)) := by
    -- The same lower-bound argument kills `H^(i + 1)` of the source lower stage.
    let hGE := lower_stupid_truncation_source_stage_isGE (F := F) K (i + 2)
    letI :
        ((KtoD).obj ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj Klower)).IsGE (i + 2) := hGE
    simpa [T, T0, Klower, Triangle.invRotate] using
      (DerivedCategory.isZero_of_isGE
        ((KtoD).obj ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj Klower))
        (i + 2) (i + 1) (by omega))
  have hlower_target_i :
      IsZero ((H i).obj (rightDerivedValue Qis KtoD T.obj₂)) := by
    -- The derived lower brutal stage has the same lower bound by Lemma `13.16.1`.
    simpa [T, T0, Klower, Triangle.invRotate] using
      (rightDerivedValue_isZero_homology_below_of_isGE
        (F := F) (a := i + 2) Klower
        (lower_stupid_truncation_isStrictlyGE (𝒜 := 𝒜) K (i + 2))
        i (by omega))
  have hlower_target_succ :
      IsZero ((H (i + 1)).obj (rightDerivedValue Qis KtoD T.obj₂)) := by
    -- One degree higher still lies below the cutoff `i + 2`.
    simpa [T, T0, Klower, Triangle.invRotate] using
      (rightDerivedValue_isZero_homology_below_of_isGE
        (F := F) (a := i + 2) Klower
        (lower_stupid_truncation_isStrictlyGE (𝒜 := 𝒜) K (i + 2))
        (i + 1) (by omega))
  have hlower_slot₁_map : IsIso ((H i).map φ.hom₂) := by
    -- Between two zero objects, the comparison map is canonically an isomorphism.
    let e₁ := hlower_source_i.isoZero
    let e₂ := hlower_target_i.isoZero
    have hEq :
        (H i).map φ.hom₂ = e₁.inv ≫ e₂.hom := by
      exact hlower_source_i.eq_of_src _ _
    rw [hEq]
    infer_instance
  have hlower_slot₄_map : IsIso ((H (i + 1)).map φ.hom₂) := by
    -- The same zero-object argument applies in degree `i + 1`.
    let e₁ := hlower_source_succ.isoZero
    let e₂ := hlower_target_succ.isoZero
    have hEq :
        (H (i + 1)).map φ.hom₂ = e₁.inv ≫ e₂.hom := by
      exact hlower_source_succ.eq_of_src _ _
    rw [hEq]
    infer_instance
  have hlower_slot₁ : IsIso (app' ψ 1) := by
    simpa [ψ, ψ₅] using hlower_slot₁_map
  have hlower_slot₄ : IsIso (app' ψ 4) := by
    simpa [ψ, ψ₅] using hlower_slot₄_map
  have hmiddle :
      app' ψ 2 =
        (H i).map
          (rightDerivedValueLeg Qis KtoD (𝟙 A.obj) (MorphismProperty.id_mem Qis A.obj)) := by
    -- The middle component of the row morphism is exactly the identity-denominator leg on `A`.
    simpa [ψ, ψ₅, φ, right_derived_comparison_triangle_morphism, T, T0,
      Triangle.invRotate]
  have h₀ : Epi (app' ψ 0) := by
    letI : IsIso (app' ψ 0) := hupper_slot₀
    infer_instance
  have h₁ : IsIso (app' ψ 1) := hlower_slot₁
  have h₂ : IsIso (app' ψ 3) := hupper_slot₃
  have h₃ : Mono (app' ψ 4) := by
    letI : IsIso (app' ψ 4) := hlower_slot₄
    infer_instance
  have hψ : IsIso (app' ψ 2) :=
    Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR₁ hR₂ ψ h₀ h₁ h₂ h₃
  rw [hmiddle] at hψ
  simpa using hψ

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): once the bounded-support case is known,
each bounded-below termwise right-acyclic complex computes `RF` by comparing it degreewise with
its upper truncations. -/
lemma computesRightDerivedAt_obj_of_termwise_rightAcyclic
    (A : K⁺(𝒜))
    (hder : HasPointwiseRightDerivedFunctorAt KtoD Qis A.obj)
    (hA : IsTermwiseRightAcyclicForAdditiveFunctor F A) :
    ComputesRightDerivedAt KtoD Qis A.obj := by
  refine
    { toHasPointwiseRightDerivedFunctorAt := hder
      isIso_rightDerivedValueLeg := ?_ }
  -- Detect the unit map on `A` by checking all of its cohomology maps.
  exact
    (derivedCategory_isIso_iff_homology_map_isIso (ℬ := ℬ)
      (rightDerivedValueLeg Qis KtoD (𝟙 A.obj) (MorphismProperty.id_mem Qis A.obj))).2
      (fun i ↦
        rightDerivedValueLeg_homologyMap_isIso_of_stupid_cut
          (F := F) A hder hA i)

/- Domain-style sampling for Lemma 13.16.7:
- primary domain: bounded-below right derived functors of additive functors between abelian
  categories, and the Leray criterion that termwise right-acyclic bounded-below complexes already
  compute the derived value;
- sampled owner declarations:
  `HasPointwiseRightDerivedFunctorAt KplusToDplus QisPlus`,
  `ComputesRightDerivedAt KplusToDplus QisPlus`,
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`;
- best owner abstraction: the source-facing owner here is the pointwise computation predicate
  `ComputesRightDerivedAt KplusToDplus QisPlus A`; the termwise acyclicity hypothesis should be
  expressed directly using the chapter owner
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A`;
- primitive data: a bounded-below homotopy object `A`, pointwise right-derived-definedness at `A`,
  and the termwise bounded-below right-acyclicity predicate
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A`;
- derived API: the Leray comparison theorem below, asserting that `A` computes the bounded-below
  right derived functor.

Source/core/bridge triage:
- `source-facing`: the Leray acyclicity criterion for bounded-below complexes;
- `core/canonical`: `HasPointwiseRightDerivedFunctorAt KplusToDplus QisPlus`,
  `ComputesRightDerivedAt KplusToDplus QisPlus`, and
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`;
- `bridge/view`: the bounded/unbounded comparison results from Lemma `13.15.2` and Proposition
  `13.16.8`, which should reuse this owner-level criterion rather than replace it.
-/

-- Proof sketch: argue first for bounded complexes by induction on the amplitude, using stupid
-- truncation triangles and Lemma `13.14.12` together with the fact that a single right
-- `F`-acyclic object computes the bounded-below right derived functor by Definition `13.15.3`.
-- Then truncate a bounded-below complex above degree `i + 1`, compare the long exact cohomology
-- sequences for `F(A^•)` and `RF(A^•)`, and use Lemma `13.16.1` to see that the higher
-- truncation contributes no cohomology in degrees `i` and `i + 1`.
/-- Lemma 13.16.7 (Leray's acyclicity lemma): if `A^•` is a bounded-below complex whose every term
is right acyclic for the bounded-below right derived functor of `F`, and if that right derived
functor is defined at `A^•`, then `A^•` computes the bounded-below right derived functor of `F`,
formalized by `ComputesRightDerivedAt KplusToDplus QisPlus A`. Equivalently, the canonical map
`F(A^•) ⟶ RF(A^•)` is an isomorphism in `D^+(\mathcal B)`. -/
@[stacks 015E]
theorem computesRightDerivedAt_of_termwise_boundedBelowRightAcyclic
    (A : K⁺(𝒜))
    (hder : HasPointwiseRightDerivedFunctorAt KplusToDplus QisPlus A)
    (hA : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A) :
    ComputesRightDerivedAt KplusToDplus QisPlus A := by
  -- Route correction: the viable proof route is to pass to the unbounded homotopy category,
  -- prove the bounded-support part there using truncation triangles, and then transport the
  -- resulting computation back to `K^+`.
  have hA' : IsTermwiseRightAcyclicForAdditiveFunctor F A :=
    isTermwiseRightAcyclic_of_termwise_boundedBelowRightAcyclic (F := F) A hA
  have hder' : HasPointwiseRightDerivedFunctorAt KtoD Qis A.obj := by
    exact (right_derived_defined_at_iff_bounded_below (F := F) A).2 hder
  have hcompute' : ComputesRightDerivedAt KtoD Qis A.obj :=
    computesRightDerivedAt_obj_of_termwise_rightAcyclic (F := F) A hder' hA'
  -- The final step is the bounded/unbounded comparison from Lemma `13.15.2`.
  exact (computes_right_derived_functor_at_iff_bounded_below (F := F) A).1 hcompute'

end

end CategoryTheory
