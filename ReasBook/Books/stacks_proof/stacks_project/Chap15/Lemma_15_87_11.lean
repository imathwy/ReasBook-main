import Mathlib
import StacksProject_2024.Chap15.«15_87_1_1»
import StacksProject_2024.Chap19.Theorem_19_12_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.SequentialInverseSystem
open ComplexShape
open Opposite

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

local notation "Ab" => AddCommGrpCat
local notation "AbSeq" => SequentialInverseSystem Ab
local notation "CpxAb" => CochainComplex Ab ℤ
local notation "DAb" => DerivedCategory Ab
local notation "DAbSeq" => DerivedCategory AbSeq

/-- Helper for Lemma 15.87.11: stagewise evaluation on derived categories is computed by the
standard `mapDerivedCategoryFactors` comparison. -/
private local instance stagewise_evaluation_isRightDerivedFunctor (n : ℕ) :
    (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategory).IsRightDerivedFunctor
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso AbSeq (up ℤ)) := by
  -- This is the same owner-level derived-functor package used to define the stagewise tower.
  simpa using
    (Functor.isRightDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso AbSeq (up ℤ))
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategory)
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategoryFactors))

/-- Helper for Lemma 15.87.11: a tower of cochain complexes determines, in each degree, a tower
of abelian groups. -/
private def complex_of_complex_tower_degree
    (I : SequentialInverseSystem CpxAb) (i : ℤ) : ℕ → Ab :=
  fun n ↦ (I.obj (op n)).X i

/-- Helper for Lemma 15.87.11: a tower of cochain complexes determines, in each degree, a tower
of abelian groups. -/
private def complex_of_complex_tower_X
    (I : SequentialInverseSystem CpxAb) (i : ℤ) : AbSeq :=
  @Functor.ofOpSequence Ab _ (complex_of_complex_tower_degree I i)
    (fun n ↦ (I.transitionMap (Nat.le_succ n)).f i)

/-- Helper for Lemma 15.87.11: the successor map in the degreewise tower is the given successor
transition map on the original tower of complexes. -/
private theorem complex_of_complex_tower_X_map_succ
    (I : SequentialInverseSystem CpxAb) (i : ℤ) (n : ℕ) :
    (complex_of_complex_tower_X I i).map (homOfLE (Nat.le_succ n)).op =
      (I.transitionMap (Nat.le_succ n)).f i := by
  -- `Functor.ofOpSequence` is designed so that its successor map is definitionally the input map.
  simp [complex_of_complex_tower_X]

/-- Helper for Lemma 15.87.11: the `n`-th object of the degreewise tower is the `i`-th term of
the `n`-th complex. -/
private theorem complex_of_complex_tower_X_obj
    (I : SequentialInverseSystem CpxAb) (i : ℤ) (n : ℕᵒᵖ) :
    (complex_of_complex_tower_X I i).obj n = (I.obj n).X i := by
  cases n
  rfl

/-- Helper for Lemma 15.87.11: the differentials in a tower of complexes are compatible with the
successor transition maps. -/
private theorem complex_of_complex_tower_d_naturality
    (I : SequentialInverseSystem CpxAb) (i j : ℤ) (n : ℕ) :
    (complex_of_complex_tower_X I i).map (homOfLE (Nat.le_succ n)).op ≫
        (I.obj (op n)).d i j =
      (I.obj (op (n + 1))).d i j ≫
        (complex_of_complex_tower_X I j).map (homOfLE (Nat.le_succ n)).op := by
  -- Each successor transition in the tower is a chain map, so it commutes with the differential.
  rw [complex_of_complex_tower_X_map_succ, complex_of_complex_tower_X_map_succ]
  exact (I.transitionMap (Nat.le_succ n)).comm i j

/-- Helper for Lemma 15.87.11: the differentials of a tower of complexes assemble into a
degreewise natural transformation. -/
private def complex_of_complex_tower_d
    (I : SequentialInverseSystem CpxAb) (i j : ℤ) :
    complex_of_complex_tower_X I i ⟶ complex_of_complex_tower_X I j :=
  NatTrans.ofOpSequence
    (fun n ↦ (I.obj (op n)).d i j)
    (complex_of_complex_tower_d_naturality I i j)

/-- Helper for Lemma 15.87.11: the reassembled complex has the usual cochain-complex shape. -/
private theorem complex_of_complex_tower_shape
    (I : SequentialInverseSystem CpxAb) :
    ∀ i j : ℤ, ¬(ComplexShape.up ℤ).Rel i j → complex_of_complex_tower_d I i j = 0 :=
by
  intro i j hij
  -- The reassembled differential is checked stagewise against the shape equation of `I.obj n`.
  ext n x
  change ((I.obj n).d i j).hom x = 0
  simpa using
    congrArg
      (fun f : AddCommGrpCat.of ((I.obj n).X i) ⟶ AddCommGrpCat.of ((I.obj n).X j) ↦ f.hom x)
      ((I.obj n).shape i j hij)

/-- Helper for Lemma 15.87.11: the reassembled differential still squares to zero because this
holds at every stage of the input tower. -/
private theorem complex_of_complex_tower_d_comp_d
    (I : SequentialInverseSystem CpxAb) :
    ∀ i j k : ℤ, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      complex_of_complex_tower_d I i j ≫ complex_of_complex_tower_d I j k = 0 := by
  intro i j k hij hjk
  -- The composite vanishes stagewise by the cochain-complex identities in the given tower.
  ext n x
  change (((I.obj n).d i j ≫ (I.obj n).d j k)).hom x = 0
  simpa using congrArg AddCommGrpCat.Hom.hom ((I.obj n).d_comp_d i j k)

/-- Helper for Lemma 15.87.11: a sequential inverse system of cochain complexes can be
reassembled into a cochain complex valued in sequential inverse systems. -/
private def complex_of_complex_tower
    (I : SequentialInverseSystem CpxAb) : CochainComplex AbSeq ℤ :=
  { X := complex_of_complex_tower_X I
    d := complex_of_complex_tower_d I
    shape := complex_of_complex_tower_shape I
    d_comp_d' := complex_of_complex_tower_d_comp_d I }

/-- Helper for Lemma 15.87.11: evaluating the reassembled complex at a stage recovers the
original complex at that stage. -/
private theorem complex_of_complex_tower_eval_X_eq
    (I : SequentialInverseSystem CpxAb) (n : ℕ) (i : ℤ) :
    ((((evaluation ℕᵒᵖ Ab).obj (op n)).mapHomologicalComplex (up ℤ)).obj
        (complex_of_complex_tower I)).X i =
      (I.obj (op n)).X i := by
  -- Evaluation just reads off the `n`-th object of the degreewise tower.
  rfl

/-- Helper for Lemma 15.87.11: evaluating the reassembled complex at a stage recovers the
original complex at that stage. -/
private def complex_of_complex_tower_eval_iso
    (I : SequentialInverseSystem CpxAb) (n : ℕ) :
    (((evaluation ℕᵒᵖ Ab).obj (op n)).mapHomologicalComplex (up ℤ)).obj
        (complex_of_complex_tower I) ≅
      I.obj (op n) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ eqToIso (complex_of_complex_tower_eval_X_eq I n i))
    (fun i j hij ↦ by
      -- After evaluation, the differential is literally the stagewise differential of `I`.
      change (𝟙 ((I.obj (op n)).X i)) ≫ (I.obj (op n)).d i j =
        (I.obj (op n)).d i j ≫ 𝟙 ((I.obj (op n)).X j)
      simp)

/-- Helper for Lemma 15.87.11: the evaluation isomorphisms on the reassembled complex are
compatible with the successor maps of the original tower. -/
private theorem complex_of_complex_tower_eval_iso_naturality
    (I : SequentialInverseSystem CpxAb) (n : ℕ) :
    (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ Ab).map ((homOfLE (Nat.le_succ n)).op))
        (up ℤ)).app (complex_of_complex_tower I) ≫
      (complex_of_complex_tower_eval_iso I n).hom =
        (complex_of_complex_tower_eval_iso I (n + 1)).hom ≫
          I.stepMap n := by
  -- The source route compares towers stagewise, so it is enough to check each cochain degree.
  ext i x
  -- After unfolding the evaluation isomorphisms, the square becomes the defining successor map.
  simpa [complex_of_complex_tower_eval_iso, SequentialInverseSystem.stepMap] using
    congrArg
      (fun f : (complex_of_complex_tower_X I i).obj (op (n + 1)) ⟶
          (complex_of_complex_tower_X I i).obj (op n) ↦ f.hom x)
      (complex_of_complex_tower_X_map_succ I i n)

/-- Helper for Lemma 15.87.11: after applying `DerivedCategory.Q`, the stagewise evaluation
comparison still matches the successor maps of the original tower. -/
private theorem derived_complex_of_complex_tower_eval_iso_naturality
    (I : SequentialInverseSystem CpxAb) (n : ℕ) :
    DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
            ((evaluation ℕᵒᵖ Ab).map ((homOfLE (Nat.le_succ n)).op))
            (up ℤ)).app (complex_of_complex_tower I)) ≫
      DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I n).hom =
        DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I (n + 1)).hom ≫
          DerivedCategory.Q.map (I.stepMap n) := by
  -- Apply the localization functor to the strict stagewise square proved above.
  simpa [Functor.map_comp] using
    congrArg DerivedCategory.Q.map (complex_of_complex_tower_eval_iso_naturality I n)

/-- Helper for Lemma 15.87.11: conjugating a homotopy-category map through
`DerivedCategory.quotientCompQhIso` recovers the corresponding `DerivedCategory.Q` map. -/
private theorem quotientCompQhIso_homCongr_map
    {K L : CpxAb}
    (f : K ⟶ L) :
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso Ab).app K)
      ((DerivedCategory.quotientCompQhIso Ab).app L))
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient Ab (ComplexShape.up ℤ)).map f)) =
        DerivedCategory.Q.map f := by
  -- Rewrite the conjugated `Qh`-image using naturality of `quotient ⋙ Qh ≅ Q`.
  change
    (DerivedCategory.quotientCompQhIso Ab).inv.app K ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient Ab (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso Ab).hom.app L =
      DerivedCategory.Q.map f
  have hnat :
      DerivedCategory.Qh.map ((HomotopyCategory.quotient Ab (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso Ab).hom.app L =
        (DerivedCategory.quotientCompQhIso Ab).hom.app K ≫ DerivedCategory.Q.map f := by
    simpa [Functor.comp_map] using
      (DerivedCategory.quotientCompQhIso Ab).hom.naturality f
  calc
    (DerivedCategory.quotientCompQhIso Ab).inv.app K ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient Ab (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso Ab).hom.app L =
      (DerivedCategory.quotientCompQhIso Ab).inv.app K ≫
        ((DerivedCategory.quotientCompQhIso Ab).hom.app K ≫ DerivedCategory.Q.map f) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ (DerivedCategory.quotientCompQhIso Ab).inv.app K ≫ k) hnat
    _ = DerivedCategory.Q.map f := by
          simpa using
            (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso Ab).app K)
              (DerivedCategory.Q.map f))

/-- Helper for Lemma 15.87.11: fix one functorial K-injective replacement on cochain complexes of
abelian groups. -/
private noncomputable def k_injective_resolution :
    CochainComplex.FunctorialComplexApproximation Ab :=
  Classical.choose (CochainComplex.exists_functorial_kInjective_resolution Ab)

/-- Helper for Lemma 15.87.11: the chosen functorial replacement is K-injective on every input
complex. -/
private theorem k_injective_resolution_isKInjective
    (M : CpxAb) :
    (k_injective_resolution.toFunctor.obj M).IsKInjective := by
  -- This is the K-injective half of the Chapter 19 functorial resolution package.
  exact (Classical.choose_spec (CochainComplex.exists_functorial_kInjective_resolution Ab)).2 M

/-- Helper for Lemma 15.87.11: the comparison map from a complex to its chosen K-injective
replacement is a quasi-isomorphism. -/
private instance k_injective_resolution_quasiIso
    (M : CpxAb) :
    QuasiIso (k_injective_resolution.ι.app M) :=
  k_injective_resolution.quasiIso_app M

/-- Helper for Lemma 15.87.11: choose a K-injective cochain-complex representative of an object
of `D(\operatorname{Ab})`. -/
private noncomputable def k_injective_preimage
    (K : DAb) : CpxAb :=
  k_injective_resolution.toFunctor.obj (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.87.11: the chosen representative of a derived object is K-injective. -/
private theorem k_injective_preimage_isKInjective
    (K : DAb) :
    (k_injective_preimage K).IsKInjective := by
  -- The fixed functorial replacement lands in K-injective complexes.
  simpa [k_injective_preimage] using
    k_injective_resolution_isKInjective (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.87.11: the chosen K-injective representative computes the original
derived object. -/
private noncomputable def k_injective_preimage_iso
    (K : DAb) :
    DerivedCategory.Q.obj (k_injective_preimage K) ≅ K :=
  -- First compare with the canonical cochain preimage, then use the standard preimage
  -- identification in the derived category.
  (asIso (DerivedCategory.Q.map (k_injective_resolution.ι.app (DerivedCategory.Q.objPreimage K)))).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso K

/-- Helper for Lemma 15.87.11: the `n`-th stage of the derived tower of the reassembled complex is
identified with the derived image of the original `n`-th complex. -/
private noncomputable def complex_of_complex_tower_stagewise_Q_component
    (I : SequentialInverseSystem CpxAb) (n : ℕ) :
    (stagewiseAbelianGroupDerivedTowerFunctor.obj
        (DerivedCategory.Q.obj (complex_of_complex_tower I))).obj (op n) ≅
      (I ⋙ DerivedCategory.Q).obj (op n) :=
  ((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategoryFactors.app
      (complex_of_complex_tower I) ≪≫
    DerivedCategory.Q.mapIso (complex_of_complex_tower_eval_iso I n)

/-- Helper for Lemma 15.87.11: the componentwise comparison between the reassembled derived tower
and the original tower is compatible with successor maps. -/
private theorem complex_of_complex_tower_stagewise_Q_component_naturality
    (I : SequentialInverseSystem CpxAb) (n : ℕ) :
    (stagewiseAbelianGroupDerivedTowerFunctor.obj
        (DerivedCategory.Q.obj (complex_of_complex_tower I))).stepMap n ≫
      (complex_of_complex_tower_stagewise_Q_component I n).hom =
        (complex_of_complex_tower_stagewise_Q_component I (n + 1)).hom ≫
          DerivedCategory.Q.map (I.stepMap n) := by
  -- Route correction: the transport square is controlled by the defining equation for
  -- `Functor.rightDerivedNatTrans` together with the strict stagewise evaluation square.
  -- Expand the comparison component and isolate the derived evaluation transition.
  dsimp [complex_of_complex_tower_stagewise_Q_component, SequentialInverseSystem.stepMap,
    stagewiseAbelianGroupDerivedTower]
  let X := complex_of_complex_tower I
  let a : ∀ m : ℕ,
      (((evaluation ℕᵒᵖ Ab).obj (op m)).mapDerivedCategory).obj (DerivedCategory.Q.obj X) ≅
        DerivedCategory.Q.obj
          ((((evaluation ℕᵒᵖ Ab).obj (op m)).mapHomologicalComplex (up ℤ)).obj X) :=
    fun m ↦
      ((evaluation ℕᵒᵖ Ab).obj (op m)).mapDerivedCategoryFactors.app X
  let τ :
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapHomologicalComplex (up ℤ)) ⟶
        (((evaluation ℕᵒᵖ Ab).obj (op n)).mapHomologicalComplex (up ℤ)) :=
    NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ Ab).map ((homOfLE (Nat.le_succ n)).op))
      (up ℤ)
  let δ :
      ((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapDerivedCategory ⟶
        ((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategory :=
    Functor.rightDerivedNatTrans
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapDerivedCategory)
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategory)
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapDerivedCategoryFactors.inv)
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso AbSeq (up ℤ))
      (Functor.whiskerRight τ DerivedCategory.Q)
  have hstep :=
    Functor.rightDerivedNatTrans_app
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapDerivedCategory)
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategory)
      (((evaluation ℕᵒᵖ Ab).obj (op (n + 1))).mapDerivedCategoryFactors.inv)
      (((evaluation ℕᵒᵖ Ab).obj (op n)).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso AbSeq (up ℤ))
      (Functor.whiskerRight τ DerivedCategory.Q)
      X
  have hstep_inv :
      δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom =
        (a (n + 1)).hom ≫ DerivedCategory.Q.map (τ.app X) := by
    -- Postcompose the defining right-derived comparison with `(a n).hom` and cancel the
    -- remaining inverse comparison on the left.
    have hstep_post_raw :
        ((a (n + 1)).inv ≫ δ.app (DerivedCategory.Q.obj X)) ≫ (a n).hom =
          (DerivedCategory.Q.map (τ.app X) ≫ (a n).inv) ≫ (a n).hom := by
      simpa [a, δ, X, Category.assoc] using
        congrArg (fun k ↦ k ≫ (a n).hom) hstep
    have hstep_post :
        (a (n + 1)).inv ≫ (δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom) =
          DerivedCategory.Q.map (τ.app X) := by
      calc
        (a (n + 1)).inv ≫ (δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom) =
            ((a (n + 1)).inv ≫ δ.app (DerivedCategory.Q.obj X)) ≫ (a n).hom := by
              simp [Category.assoc]
        _ = (DerivedCategory.Q.map (τ.app X) ≫ (a n).inv) ≫ (a n).hom := hstep_post_raw
        _ = DerivedCategory.Q.map (τ.app X) := by
              simp [Category.assoc]
    apply (cancel_epi (a (n + 1)).inv).1
    calc
      (a (n + 1)).inv ≫ (δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom) =
          DerivedCategory.Q.map (τ.app X) := hstep_post
      _ =
          (a (n + 1)).inv ≫ ((a (n + 1)).hom ≫ DerivedCategory.Q.map (τ.app X)) := by
            simp
  have hτ :
      DerivedCategory.Q.map (τ.app X) ≫
          DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I n).hom =
        DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I (n + 1)).hom ≫
          DerivedCategory.Q.map (I.stepMap n) := by
    simpa [X, τ] using derived_complex_of_complex_tower_eval_iso_naturality I n
  -- Combine the universal-property comparison for right derived functors with the strict square.
  have hcomponent :
      δ.app (DerivedCategory.Q.obj X) ≫
          (a n).hom ≫
            DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I n).hom =
        (a (n + 1)).hom ≫
          DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I (n + 1)).hom ≫
            DerivedCategory.Q.map (I.stepMap n) := by
    calc
      δ.app (DerivedCategory.Q.obj X) ≫
          (a n).hom ≫
            DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I n).hom =
          ((a (n + 1)).hom ≫ DerivedCategory.Q.map (τ.app X)) ≫
            DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I n).hom := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫ DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I n).hom)
                  hstep_inv
      _ =
          (a (n + 1)).hom ≫
            (DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I (n + 1)).hom ≫
              DerivedCategory.Q.map (I.stepMap n)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ (a (n + 1)).hom ≫ k)
                  hτ
      _ =
          (a (n + 1)).hom ≫
            DerivedCategory.Q.map (complex_of_complex_tower_eval_iso I (n + 1)).hom ≫
              DerivedCategory.Q.map (I.stepMap n) := by
                simp
  simpa [SequentialInverseSystem.stepMap, stagewiseAbelianGroupDerivedTower,
    complex_of_complex_tower_stagewise_Q_component, δ, a, X, Category.assoc] using hcomponent

/-- Helper for Lemma 15.87.11: the stagewise derived tower of the reassembled complex is
componentwise isomorphic to the original derived tower. -/
private noncomputable def complex_of_complex_tower_stagewise_Q_hom
    (I : SequentialInverseSystem CpxAb) :
    stagewiseAbelianGroupDerivedTowerFunctor.obj
        (DerivedCategory.Q.obj (complex_of_complex_tower I)) ⟶
      I ⋙ DerivedCategory.Q :=
  NatTrans.ofOpSequence
    (fun n ↦ (complex_of_complex_tower_stagewise_Q_component I n).hom)
    (complex_of_complex_tower_stagewise_Q_component_naturality I)

/-- Helper for Lemma 15.87.11: the stagewise comparison components assemble into a natural
isomorphism of towers. -/
private noncomputable def complex_of_complex_tower_stagewise_Q_iso
    (I : SequentialInverseSystem CpxAb) :
    stagewiseAbelianGroupDerivedTowerFunctor.obj
        (DerivedCategory.Q.obj (complex_of_complex_tower I)) ≅
      I ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun n ↦ complex_of_complex_tower_stagewise_Q_component I (unop n))
    (fun {_ _} f ↦ by
      -- The naturality on arbitrary arrows is inherited from the successor-by-successor
      -- natural transformation assembled above.
      simpa using (complex_of_complex_tower_stagewise_Q_hom I).naturality f)

/-- Helper for Lemma 15.87.11: each successor map in a derived tower can be strictified to a map
between the chosen K-injective representatives. -/
private theorem exists_k_injective_preimage_step_map
    (K : SequentialInverseSystem DAb) (n : ℕ) :
    ∃ f : k_injective_preimage (K.obj (op (n + 1))) ⟶
        k_injective_preimage (K.obj (op n)),
      DerivedCategory.Q.map f ≫ (k_injective_preimage_iso (K.obj (op n))).hom =
        (k_injective_preimage_iso (K.obj (op (n + 1)))).hom ≫ K.stepMap n := by
  let Q := HomotopyCategory.quotient Ab (ComplexShape.up ℤ)
  letI : (k_injective_preimage (K.obj (op n))).IsKInjective :=
    k_injective_preimage_isKInjective (K.obj (op n))
  let eNext := k_injective_preimage_iso (K.obj (op (n + 1)))
  let eNow := k_injective_preimage_iso (K.obj (op n))
  let c :=
    Iso.homCongr
      ((DerivedCategory.quotientCompQhIso Ab).app
        (k_injective_preimage (K.obj (op (n + 1)))))
      ((DerivedCategory.quotientCompQhIso Ab).app
        (k_injective_preimage (K.obj (op n))))
  let u :
      DerivedCategory.Q.obj (k_injective_preimage (K.obj (op (n + 1)))) ⟶
        DerivedCategory.Q.obj (k_injective_preimage (K.obj (op n))) :=
    eNext.hom ≫ K.stepMap n ≫ eNow.inv
  obtain ⟨g, hg⟩ :=
    (CochainComplex.IsKInjective.Qh_map_bijective
      (Q.obj (k_injective_preimage (K.obj (op (n + 1)))))
      (k_injective_preimage (K.obj (op n)))).surjective (c.symm u)
  obtain ⟨f, rfl⟩ := Q.map_surjective g
  have hQ :
      DerivedCategory.Q.map f = u := by
    calc
      DerivedCategory.Q.map f =
          c (DerivedCategory.Qh.map (Q.map f)) := by
            symm
            simpa [c] using quotientCompQhIso_homCongr_map (f := f)
      _ = c (c.symm u) := by
            simpa using congrArg c hg
      _ = u := by
            exact c.apply_symm_apply u
  refine ⟨f, ?_⟩
  -- Postcompose the strictified map with the target comparison isomorphism and cancel the inverse.
  calc
    DerivedCategory.Q.map f ≫ eNow.hom = u ≫ eNow.hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eNow.hom) hQ
    _ = eNext.hom ≫ K.stepMap n := by
      simp [u, Category.assoc]

/-- Helper for Lemma 15.87.11: package the strictified K-injective representatives into a tower of
complexes. -/
private noncomputable def k_injective_complex_tower
    (K : SequentialInverseSystem DAb) : SequentialInverseSystem CpxAb :=
  @Functor.ofOpSequence CpxAb _
    (fun n ↦ k_injective_preimage (K.obj (op n)))
    (fun n ↦ Classical.choose (exists_k_injective_preimage_step_map K n))

/-- Helper for Lemma 15.87.11: the chosen K-injective tower evaluates back to the original tower in
the derived category. -/
private noncomputable def k_injective_complex_tower_hom
    (K : SequentialInverseSystem DAb) :
    k_injective_complex_tower K ⋙ DerivedCategory.Q ⟶ K :=
  NatTrans.ofOpSequence
    (fun n ↦ (k_injective_preimage_iso (K.obj (op n))).hom)
    (fun n ↦ by
      -- The successor square is exactly the strictification equation chosen above.
      simpa [k_injective_complex_tower, SequentialInverseSystem.stepMap] using
        (Classical.choose_spec (exists_k_injective_preimage_step_map K n)))

/-- Helper for Lemma 15.87.11: the strictified K-injective tower is naturally isomorphic to the
original derived tower. -/
private noncomputable def exists_k_injective_complex_tower_lift
    (K : SequentialInverseSystem DAb) :
    ∃ I : SequentialInverseSystem CpxAb,
      (∀ n : ℕᵒᵖ, (I.obj n).IsKInjective) ∧
        Nonempty (I ⋙ DerivedCategory.Q ≅ K) := by
  refine ⟨k_injective_complex_tower K, ?_, ?_⟩
  · intro n
    simpa [k_injective_complex_tower] using
      k_injective_preimage_isKInjective (K.obj n)
  · refine ⟨NatIso.ofComponents
      (fun n ↦ k_injective_preimage_iso (K.obj n))
      (fun {_ _} f ↦ by
        -- Naturality on arbitrary arrows follows from the successor-assembled natural
        -- transformation above.
        simpa using (k_injective_complex_tower_hom K).naturality f)⟩

/-
Domain-style sampling for Lemma 15.87.11 in the sequential derived inverse-system domain:
- sampled chapter owner declarations:
  * `stagewiseAbelianGroupDerivedEvaluation`
  * `stagewiseAbelianGroupDerivedTower`
  * `stagewiseAbelianGroupDerivedTowerFunctor`
  * `Functor.EssSurj`
- source/core/bridge triage:
  * `source-facing`: a tower `(K_n)` in `D(Ab)`
  * `core/canonical`: essential surjectivity of
    `stagewiseAbelianGroupDerivedTowerFunctor : D(Ab(\mathbf N)) ⥤ \mathbf N^{op} ⥤ D(Ab)`
  * `bridge/view`: the objectwise existence statement for a fixed tower `K`

The primitive data of the present item are only the tower `K`. The stagewise tower functor is
already provided by the upstream owner file `15_87_1_1`, and objectwise existence up to
isomorphism is canonically owned by `Functor.EssSurj`. The public statement should therefore live
at that owner level rather than as a parallel existential wrapper.
-/
-- Proof sketch: Lemma 15.87.11 says exactly that every tower `K` of objects of `D(Ab)` is
-- isomorphic to one in the image of the stagewise evaluation functor from `D(Ab(\mathbf N))`.
/-- Lemma 15.87.11: the stagewise evaluation functor from `D(\operatorname{Ab}(\mathbf N))` to
sequential inverse systems in `D(\operatorname{Ab})` is essentially surjective. -/
@[stacks 0CQ9]
theorem stagewiseAbelianGroupDerivedTowerFunctor_essSurj :
    (stagewiseAbelianGroupDerivedTowerFunctor).EssSurj := by
  refine CategoryTheory.Functor.EssSurj.mk ?_
  intro K
  rcases exists_k_injective_complex_tower_lift K with ⟨I, _, ⟨eI⟩⟩
  refine ⟨DerivedCategory.Q.obj (complex_of_complex_tower I), ⟨?_⟩⟩
  -- Compose the stagewise comparison for the reassembled complex with the K-injective tower lift.
  exact complex_of_complex_tower_stagewise_Q_iso I ≪≫ eI

end

end CategoryTheory
