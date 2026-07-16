import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import stacks_proof.stacks_project.Chap13.Definition_13_11_3
import stacks_proof.stacks_project.Chap13.Definition_13_34_1
import stacks_proof.stacks_project.Chap15.Definition_15_59_13
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Lemma_15_66_5
import stacks_proof.stacks_project.Chap15.Lemma_15_88_1_FixedBase
import stacks_proof.stacks_project.Chap15.Lemma_15_88_3
import stacks_proof.stacks_project.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

private abbrev ModA := ModuleCat A
local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory (SequentialInverseSystem (ModuleCat A))

private abbrev stageSingle : ModuleCat A ⥤ DerivedCategory (ModuleCat A) :=
  (ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A))

private abbrev systemSingle :
    SequentialInverseSystem (ModuleCat A) ⥤
      DerivedCategory (SequentialInverseSystem (ModuleCat A)) :=
  (DerivedCategory.singleFunctor (SequentialInverseSystem (ModuleCat A)) (0 : ℤ) :
    SequentialInverseSystem (ModuleCat A) ⥤
      DerivedCategory (SequentialInverseSystem (ModuleCat A)))

/- Domain-style sampling for Lemma 15.103.3:
- primary domain: sequential derived inverse limits in `D(A)` and their compatibility with the
  exact tensor functor `- ⊗[A]^L K`;
- sampled owner declarations:
  * `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`
  * the fixed-base bridge owner notation `R lim(_)` from `Lemma_15_88_1_FixedBase`
  * `CategoryTheory.IsDerivedLimit`
  * `ModuleCat.single0Functor`
  * `DerivedCategory.singleFunctor`
  * `CategoryTheory.derivedTensorProduct`
- best owner abstraction: the source-facing statement remains an `IsDerivedLimit` claim for the
  tensor tower, while the chosen derived-limit object is the canonical fixed-base Chapter 15 owner
  `R lim(systemSingle.obj M)` from `Lemma_15_88_1_FixedBase`; the bridge data are the stagewise
  degree-zero embedding `stageSingle` and the system-level degree-zero embedding `systemSingle`;
- primitive vs. derived:
  primitive data are only the pseudo-coherent object `K : D(A)` and the sequential inverse system
  `M : ℕᵒᵖ ⥤ Mod_A`;
  derived API is the tower `M ⋙ stageSingle ⋙ derivedTensorProduct K` and the tensorized chosen
  derived inverse limit `(R lim(systemSingle.obj M)) ⊗[A]^L K`.

Source/core/bridge triage:
- `source-facing`: the tensor compatibility statement that
  `(R lim(systemSingle.obj M)) ⊗[A]^L K` is a derived limit of the tensor tower;
- `core/canonical`: `R lim(_)`, `IsDerivedLimit`, and `derivedTensorProduct`;
- `bridge/view`: the degree-zero embeddings `stageSingle` and `systemSingle`, and the tower
  `M ⋙ stageSingle`.
-/

-- Proof sketch: apply the Milnor distinguished triangle defining the chosen derived inverse limit
-- of `M`, then apply the exact functor `derivedTensorProduct K`. Lemma `15.66.5` identifies the
-- images of the two product terms with the corresponding products of the stagewise derived tensor
-- products because `K` is pseudo-coherent, so the resulting triangle is exactly the Milnor
-- triangle for the tensor tower.
/-- Helper for Lemma 15.103.3: a pseudo-coherent derived `A`-module lies in the bounded-above
derived category. -/
private lemma pseudoCoherent_mem_t_minus
    (K : DMod) (hK : K.IsPseudoCoherent) :
    (t.minus : ObjectProperty DMod) K := by
  rcases hK with ⟨E, ⟨b, hE⟩, -, α, hα⟩
  let e : DerivedCategory.Q.obj E ≅ K := asIso α
  have hQ : (t.minus : ObjectProperty DMod) (DerivedCategory.Q.obj E) := by
    -- The chosen finite-free model is strictly zero above `b`, so its image in `D(A)` is
    -- bounded above at the same cutoff.
    refine ⟨b, ?_⟩
    change (DerivedCategory.Q.obj E).IsLE b
    exact (DerivedCategory.isLE_Q_obj_iff E b).2 inferInstance
  exact (t.minus : ObjectProperty DMod).prop_of_iso e hQ

/-- Helper for Lemma 15.103.3: pseudo-coherence upgrades Lemma `15.66.5` to the exact
countable-family product comparison needed for the Milnor triangle of the tensor tower. -/
private lemma piComparison_single_tensor_isIso_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) (M : SeqMod)
    [HasProduct (fun n : ℕ ↦ (stageSingle ⋙ derivedTensorProduct K).obj (M.obj (Opposite.op n)))] :
    IsIso (piComparison (stageSingle ⋙ derivedTensorProduct K)
      (fun n : ℕ ↦ M.obj (Opposite.op n))) := by
  -- TODO: reindex the family through a universe-compatible copy of `ℕ` (for example `ULift ℕ`),
  -- transport the resulting product structure across the induced discrete-diagram equivalence, and
  -- then apply clause `(1) -> (2)` of Lemma `15.66.5` via `htfae.out 0 1`.
  sorry

/-- Helper for Lemma 15.103.3: stagewise evaluation on derived categories is computed by the
standard `mapDerivedCategoryFactors` comparison. -/
private local instance stagewise_evaluation_isRightDerivedFunctor (n : ℕ) :
    (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapDerivedCategory).IsRightDerivedFunctor
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso SeqMod (ComplexShape.up ℤ)) := by
  -- Reuse the canonical owner-level comparison between strict and derived stagewise evaluation.
  simpa using
    (Functor.isRightDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso SeqMod (ComplexShape.up ℤ))
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapDerivedCategory)
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapDerivedCategoryFactors))

/-- Helper for Lemma 15.103.3: the `n`th stage of the stagewise tower of `systemSingle.obj M`
is canonically `M_n[0]`. -/
private noncomputable def stagewise_systemSingle_tower_component_iso
    (M : SeqMod) (n : ℕ) :
    (stagewiseModuleDerivedLimitTower (A := A) ((systemSingle : SeqMod ⥤ DSeq).obj M)).obj
        (Opposite.op n) ≅
      (M ⋙ stageSingle).obj (Opposite.op n) :=
  -- First compute stagewise evaluation of the degree-zero derived object through the canonical
  -- `mapDerivedCategoryFactors` comparison, then rewrite strict single complexes back to `M_n[0]`.
  (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor SeqMod (0 : ℤ)).obj M)) ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex
          (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)) : SeqMod ⥤ ModuleCat A)
          (ComplexShape.up ℤ) 0).app M)) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (M.obj (Opposite.op n))

/-- Helper for Lemma 15.103.3: evaluating the degree-zero single complex of a sequential inverse
system at two consecutive stages commutes strictly with the canonical single-complex transport. -/
private theorem single_stage_transition_comm
    (M : SeqMod) (n : ℕ) :
    let τ :
        (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op (n + 1))).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⟶
          (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapHomologicalComplex
            (ComplexShape.up ℤ)) :=
      NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (ModuleCat A)).map ((homOfLE (Nat.le_succ n)).op))
        (ComplexShape.up ℤ)
    τ.app ((CochainComplex.singleFunctor SeqMod (0 : ℤ)).obj M) ≫
        (((HomologicalComplex.singleMapHomologicalComplex
          (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)) : SeqMod ⥤ ModuleCat A)
          (ComplexShape.up ℤ) 0).app M).hom) =
      (((HomologicalComplex.singleMapHomologicalComplex
          (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op (n + 1))) : SeqMod ⥤ ModuleCat A)
          (ComplexShape.up ℤ) 0).app M).hom) ≫
        ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map
          (M.map ((homOfLE (Nat.le_succ n)).op))) := by
  let τ :
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op (n + 1))).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⟶
        (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapHomologicalComplex
          (ComplexShape.up ℤ)) :=
    NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ (ModuleCat A)).map ((homOfLE (Nat.le_succ n)).op))
      (ComplexShape.up ℤ)
  -- Proof comment: both sides are morphisms between degree-zero single complexes, so it is enough
  -- to compare their components in each cochain degree.
  ext i x
  by_cases hi : i = 0
  · subst i
    simp [τ]
  · simp [τ, hi]

/-- Helper for Lemma 15.103.3: the stagewise comparison components respect the successor maps of
the derived tower and the degree-zero module tower. -/
private theorem stagewise_systemSingle_tower_component_naturality
    (M : SeqMod) (n : ℕ) :
    (stagewiseModuleDerivedLimitTower (A := A) ((systemSingle : SeqMod ⥤ DSeq).obj M)).stepMap n ≫
      (stagewise_systemSingle_tower_component_iso (A := A) M n).hom =
        (stagewise_systemSingle_tower_component_iso (A := A) M (n + 1)).hom ≫
          (M ⋙ stageSingle).map ((homOfLE (Nat.le_succ n)).op) := by
  let X := ((CochainComplex.singleFunctor SeqMod (0 : ℤ)).obj M)
  let a : ∀ m : ℕ,
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op m)).mapDerivedCategory).obj
          (DerivedCategory.Q.obj X) ≅
        DerivedCategory.Q.obj
          ((((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op m)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) :=
    fun m ↦
      ((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op m)).mapDerivedCategoryFactors.app X
  let τ :
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op (n + 1))).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⟶
        (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapHomologicalComplex
          (ComplexShape.up ℤ)) :=
    NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ (ModuleCat A)).map ((homOfLE (Nat.le_succ n)).op))
      (ComplexShape.up ℤ)
  let δ :
      ((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op (n + 1))).mapDerivedCategory ⟶
        ((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapDerivedCategory :=
    Functor.rightDerivedNatTrans
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op (n + 1))).mapDerivedCategory)
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapDerivedCategory)
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op (n + 1))).mapDerivedCategoryFactors.inv)
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso SeqMod (ComplexShape.up ℤ))
      (Functor.whiskerRight τ DerivedCategory.Q)
  let s :
      ∀ m : ℕ,
        ((((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op m)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X) ≅
          ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
            (M.obj (Opposite.op m))) :=
    fun m ↦
      ((HomologicalComplex.singleMapHomologicalComplex
        (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op m)) : SeqMod ⥤ ModuleCat A)
        (ComplexShape.up ℤ) 0).app M)
  let b : ∀ m : ℕ,
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        (M.obj (Opposite.op m))) ≅
        (M ⋙ stageSingle).obj (Opposite.op m) :=
    fun m ↦ (DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (M.obj (Opposite.op m))
  have hstep :=
    Functor.rightDerivedNatTrans_app
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op (n + 1))).mapDerivedCategory)
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapDerivedCategory)
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op (n + 1))).mapDerivedCategoryFactors.inv)
      (((evaluation ℕᵒᵖ (ModuleCat A)).obj (Opposite.op n)).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso SeqMod (ComplexShape.up ℤ))
      (Functor.whiskerRight τ DerivedCategory.Q)
      X
  have hstep_inv :
      δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom =
        (a (n + 1)).hom ≫ DerivedCategory.Q.map (τ.app X) := by
    -- Proof comment: postcompose the defining right-derived comparison and cancel the inverse
    -- `mapDerivedCategoryFactors` comparison on the left.
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
      DerivedCategory.Q.map (τ.app X) ≫ DerivedCategory.Q.map (s n).hom =
        DerivedCategory.Q.map (s (n + 1)).hom ≫
          DerivedCategory.Q.map
            ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map
              (M.map ((homOfLE (Nat.le_succ n)).op))) := by
    -- Proof comment: this is the strict chain-level stage-transition square, now lifted by `Q`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map (single_stage_transition_comm (A := A) M n)
  have hsingle :
      DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map
            (M.map ((homOfLE (Nat.le_succ n)).op))) ≫
        (b n).hom =
      (b (n + 1)).hom ≫ (M ⋙ stageSingle).map ((homOfLE (Nat.le_succ n)).op) := by
    -- Proof comment: naturality of `singleFunctorIsoCompQ` identifies the residual `Q`-image
    -- of the strict degree-zero map with the derived stage transition.
    simpa [b, stageSingle] using
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).hom.naturality
        (M.map ((homOfLE (Nat.le_succ n)).op)))
  have hcomponent :
      δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom ≫ DerivedCategory.Q.map (s n).hom ≫ (b n).hom =
        (a (n + 1)).hom ≫ DerivedCategory.Q.map (s (n + 1)).hom ≫
          (b (n + 1)).hom ≫ (M ⋙ stageSingle).map ((homOfLE (Nat.le_succ n)).op) := by
    -- Proof comment: combine the derived evaluation comparison, the strict single-complex square,
    -- and the naturality of `singleFunctorIsoCompQ`.
    calc
      δ.app (DerivedCategory.Q.obj X) ≫ (a n).hom ≫ DerivedCategory.Q.map (s n).hom ≫ (b n).hom =
          ((a (n + 1)).hom ≫ DerivedCategory.Q.map (τ.app X)) ≫
            DerivedCategory.Q.map (s n).hom ≫ (b n).hom := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ DerivedCategory.Q.map (s n).hom ≫ (b n).hom) hstep_inv
      _ =
          (a (n + 1)).hom ≫ DerivedCategory.Q.map (s (n + 1)).hom ≫
            DerivedCategory.Q.map
              ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map
                (M.map ((homOfLE (Nat.le_succ n)).op))) ≫
              (b n).hom := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ (a (n + 1)).hom ≫ k ≫ (b n).hom) hτ
      _ =
          (a (n + 1)).hom ≫ DerivedCategory.Q.map (s (n + 1)).hom ≫
            ((b (n + 1)).hom ≫ (M ⋙ stageSingle).map ((homOfLE (Nat.le_succ n)).op)) := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k ↦ (a (n + 1)).hom ≫ DerivedCategory.Q.map (s (n + 1)).hom ≫ k)
                    hsingle
      _ =
          (a (n + 1)).hom ≫ DerivedCategory.Q.map (s (n + 1)).hom ≫
            (b (n + 1)).hom ≫ (M ⋙ stageSingle).map ((homOfLE (Nat.le_succ n)).op) := by
              simp [Category.assoc]
  simpa [SequentialInverseSystem.stepMap, stagewiseModuleDerivedLimitTower,
    stagewise_systemSingle_tower_component_iso, X, a, τ, δ, s, b, Category.assoc] using
    hcomponent

/-- Helper for Lemma 15.103.3: the componentwise stagewise comparisons assemble into a morphism
of towers from the actual stagewise derived tower to the degree-zero tower `M ⋙ stageSingle`. -/
private noncomputable def stagewise_systemSingle_tower_hom
    (M : SeqMod) :
    stagewiseModuleDerivedLimitTower (A := A) ((systemSingle : SeqMod ⥤ DSeq).obj M) ⟶
      M ⋙ stageSingle :=
  NatTrans.ofOpSequence
    (fun n ↦ (stagewise_systemSingle_tower_component_iso (A := A) M n).hom)
    (stagewise_systemSingle_tower_component_naturality (A := A) M)

/-- Helper for Lemma 15.103.3: the stagewise tower of the degree-zero derived object
`systemSingle.obj M` is definitionally the tower `M ⋙ stageSingle`. -/
private def stagewise_systemSingle_tower_iso
    (M : SeqMod) :
    stagewiseModuleDerivedLimitTower (A := A) ((systemSingle : SeqMod ⥤ DSeq).obj M) ≅
      M ⋙ stageSingle :=
  -- Assemble the componentwise identifications into a tower isomorphism.
  NatIso.ofComponents
    (fun n ↦ stagewise_systemSingle_tower_component_iso (A := A) M (Opposite.unop n))
    (fun {_ _} f ↦ by
      -- Naturality on arbitrary arrows follows from the assembled tower morphism.
      simpa using (stagewise_systemSingle_tower_hom (A := A) M).naturality f)

/-- Helper for Lemma 15.103.3: a tower isomorphism induces an isomorphism between the two Milnor
product objects. -/
private noncomputable def tower_product_iso
    {Ksys Lsys : SequentialInverseSystem DMod}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys := by
  -- Transport the discrete product diagram stagewise along the given tower isomorphism.
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (Opposite.op n.as)
  exact HasLimit.isoOfNatIso eFamily

/-- Helper for Lemma 15.103.3: the product isomorphism induced by a tower isomorphism preserves
each stage projection. -/
private theorem tower_product_iso_hom_comp_π
    {Ksys Lsys : SequentialInverseSystem DMod}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) (n : ℕ) :
    (tower_product_iso e).hom ≫ Pi.π (inverseSystemFamily Lsys) n =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom := by
  -- This is the defining projection formula for `HasLimit.isoOfNatIso`.
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun m : Discrete ℕ ↦ e.app (Opposite.op m.as)
  simpa [tower_product_iso, eFamily] using
    limMap_π (α := eFamily.hom) (j := Discrete.mk n)

/-- Helper for Lemma 15.103.3: the product isomorphism induced by a tower isomorphism intertwines
the two Milnor difference maps. -/
private theorem tower_product_iso_hom_comm_difference
    {Ksys Lsys : SequentialInverseSystem DMod}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys =
      derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom := by
  -- Compare the two Milnor endomorphisms after each projection to reduce to tower naturality.
  apply Pi.hom_ext
  intro n
  calc
    ((tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys) ≫
        Pi.π (inverseSystemFamily Lsys) n =
      (tower_product_iso e).hom ≫
        (Pi.π (inverseSystemFamily Lsys) n -
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          (e.app (Opposite.op (n + 1))).hom ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Preadditive.comp_sub]
          rw [tower_product_iso_hom_comp_π]
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ Lsys.transitionMap (Nat.le_succ n))
              (tower_product_iso_hom_comp_π e (n + 1))
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫
            (e.app (Opposite.op n)).hom) := by
          -- Naturality identifies the successor-transition contribution.
          congr 1
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ t)
              (e.hom.naturality ((homOfLE (Nat.le_succ n)).op)).symm
    _ =
      (Pi.π (inverseSystemFamily Ksys) n -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n)) ≫
        (e.app (Opposite.op n)).hom := by
          rw [Preadditive.sub_comp]
          simp [Category.assoc]
    _ =
      derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n ≫
        (e.app (Opposite.op n)).hom := by
          rw [← derivedLimitDifferenceMap_comp_π_assoc]
    _ =
      ((derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom) ≫
        Pi.π (inverseSystemFamily Lsys) n) := by
          rw [Category.assoc, ← tower_product_iso_hom_comp_π, ← Category.assoc]

/-- Helper for Lemma 15.103.3: a derived-limit witness transports across an isomorphism of towers
when the limiting object is kept fixed. -/
private theorem isDerivedLimit_of_tower_iso
    {Ksys Lsys : SequentialInverseSystem DMod} {K : DMod}
    (e : Ksys ≅ Lsys)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Lsys K := by
  rcases hK with ⟨hP, ι, δ, hδ⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (Opposite.op n.as)
  let hQ : HasProduct (inverseSystemFamily Lsys) := by
    exact hasLimit_of_iso eFamily
  letI : HasProduct (inverseSystemFamily Lsys) := hQ
  let p : (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys :=
    tower_product_iso e
  let T : Triangle DMod :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle DMod :=
    Triangle.mk (ι ≫ p.hom) (derivedLimitDifferenceMap Lsys) (p.inv ≫ δ)
  have hIso : T ≅ T' := by
    -- Repackage the original Milnor triangle through the product comparison isomorphism.
    refine Triangle.isoMk _ _ (Iso.refl _) p p ?_ ?_ ?_
    · simp [T, T']
    · simpa [T, T'] using (tower_product_iso_hom_comm_difference e).symm
    · simp [T, T']
  have hT' : T' ∈ distTriang DMod := by
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hQ, ι ≫ p.hom, p.inv ≫ δ, hT'⟩

/-- Helper for Lemma 15.103.3: the canonical Milnor witness from Lemma `15.88.3`, specialized to
`systemSingle.obj M`, already gives a derived-limit witness for the tower `M ⋙ stageSingle`. -/
private lemma systemSingle_stagewise_isDerivedLimit
    (M : SeqMod) :
    IsDerivedLimit (M ⋙ stageSingle)
      (R lim((systemSingle : SeqMod ⥤ DSeq).obj M)) := by
  -- The canonical Milnor witness is already available for `systemSingle.obj M`; transport it
  -- across the stagewise tower identification assembled above.
  let F : DSeq ⥤ DMod :=
    CategoryTheory.additiveFunctorTotalRightDerived
      (CategoryTheory.Limits.lim : SeqMod ⥤ ModuleCat A)
  change IsDerivedLimit (M ⋙ stageSingle) (F.obj ((systemSingle : SeqMod ⥤ DSeq).obj M))
  let hBase :
      IsDerivedLimit
        (stagewiseModuleDerivedLimitTower (A := A)
          ((systemSingle : SeqMod ⥤ DSeq).obj M))
        (F.obj ((systemSingle : SeqMod ⥤ DSeq).obj M)) :=
    moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation (A := A)
      ((systemSingle : SeqMod ⥤ DSeq).obj M)
  exact
    isDerivedLimit_of_tower_iso
      (stagewise_systemSingle_tower_iso (A := A) M)
      hBase

/-- Helper for Lemma 15.103.3: after projecting to the `n`th factor, the pseudo-coherent
product-comparison isomorphism is the tensor-image of the `n`th product projection. -/
private lemma piComparison_single_tensor_hom_comp_π
    (K : DMod) (M : SeqMod)
    [HasProduct (fun n : ℕ ↦ M.obj (Opposite.op n))]
    [HasProduct (fun n : ℕ ↦ (stageSingle ⋙ derivedTensorProduct K).obj (M.obj (Opposite.op n)))]
    [HasProduct (inverseSystemFamily (((M ⋙ stageSingle) ⋙ derivedTensorProduct K)))]
    [IsIso (piComparison (stageSingle ⋙ derivedTensorProduct K)
      (fun n : ℕ ↦ M.obj (Opposite.op n)))]
    (n : ℕ) :
    (asIso (piComparison (stageSingle ⋙ derivedTensorProduct K)
      (fun n : ℕ ↦ M.obj (Opposite.op n)))).hom ≫
        Pi.π (inverseSystemFamily (((M ⋙ stageSingle) ⋙ derivedTensorProduct K))) n =
      (stageSingle ⋙ derivedTensorProduct K).map
        (Pi.π (fun n : ℕ ↦ M.obj (Opposite.op n)) n) := by
  -- This is the standard product-comparison projection formula specialized to the family `(M_n)`.
  simpa [inverseSystemFamily] using
    (piComparison_comp_π
      (stageSingle ⋙ derivedTensorProduct K)
      (fun n : ℕ ↦ M.obj (Opposite.op n))
      n)

/-- Helper for Lemma 15.103.3: once the product comparison is known to commute with the Milnor
difference map, tensoring the Milnor triangle for `M ⋙ stageSingle` yields the required derived
limit witness for the tensor tower. -/
private lemma isDerivedLimit_tensor_of_piComparison
    (K : DMod) (M : SeqMod)
    (hM : IsDerivedLimit (M ⋙ stageSingle)
      (R lim((systemSingle : SeqMod ⥤ DSeq).obj M)))
    [HasProduct (fun n : ℕ ↦ (stageSingle ⋙ derivedTensorProduct K).obj (M.obj (Opposite.op n)))]
    [IsIso (piComparison (stageSingle ⋙ derivedTensorProduct K)
      (fun n : ℕ ↦ M.obj (Opposite.op n)))] :
    IsDerivedLimit
      ((M ⋙ stageSingle) ⋙ derivedTensorProduct K)
      ((R lim((systemSingle : SeqMod ⥤ DSeq).obj M)) ⊗[A]^L K) := by
  -- Route correction: the source proof applies `derivedTensorProduct K` to the Milnor triangle
  -- for `M ⋙ stageSingle` and then rewrites both product terms by `piComparison`.
  -- TODO: prove that the comparison isomorphism intertwines the mapped Milnor difference map with
  -- `derivedLimitDifferenceMap (((M ⋙ stageSingle) ⋙ derivedTensorProduct K))` by comparing both
  -- sides after each projection `Pi.π ... n`, using `piComparison_single_tensor_hom_comp_π`,
  -- `derivedLimitDifferenceMap_comp_π`, and `Functor.map_sub` / `Functor.map_comp`.
  sorry

/-- Lemma 15.103.3: if `K ∈ D(A)` is pseudo-coherent and `(M_n)` is a sequential inverse system
of `A`-modules, then tensoring the chosen derived inverse limit of `(M_n[0])` with `K` gives a
derived limit of the stagewise tensor tower `((M_n[0]) \otimes_A^{\mathbf L} K)_n`. By symmetry
of the derived tensor product, this is the statement form of the textbook identity
`R\!\varprojlim_n (K \otimes_A^{\mathbf L} M_n) = K \otimes_A^{\mathbf L} R\!\varprojlim_n M_n`.
-/
@[stacks 0D2L]
lemma moduleDerivedInverseLimit_tensor_isDerivedLimit_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) (M : SeqMod) :
    IsDerivedLimit
      ((M ⋙ stageSingle) ⋙ derivedTensorProduct K)
      ((R lim((systemSingle : SeqMod ⥤ DSeq).obj M)) ⊗[A]^L K) := by
  -- Route correction: the final closure remains the textbook Milnor-triangle transport from
  -- `systemSingle_stagewise_isDerivedLimit` through `derivedTensorProduct K` and the
  -- pseudo-coherent product comparison.
  -- TODO: instantiate the countable-product object for the tensor tower without triggering the
  -- current imported-universe elaboration issue, then combine
  -- `systemSingle_stagewise_isDerivedLimit`,
  -- `piComparison_single_tensor_isIso_of_isPseudoCoherent`, and
  -- `isDerivedLimit_tensor_of_piComparison`.
  sorry

end

end CategoryTheory
