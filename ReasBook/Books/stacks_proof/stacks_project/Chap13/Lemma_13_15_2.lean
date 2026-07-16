import stacks_proof.stacks_project.Chap04.Remark_4_27_7
import stacks_proof.stacks_project.Chap04.Remark_4_27_15
import stacks_proof.stacks_project.Chap13.Definition_13_11_3
import stacks_proof.stacks_project.Chap13.Definition_13_14_10
import stacks_proof.stacks_project.Chap13.Lemma_13_10_6
import stacks_proof.stacks_project.Chap13.Lemma_13_11_5
import stacks_proof.stacks_project.Chap13.Lemma_13_11_6
import stacks_proof.stacks_project.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open HomologicalComplex
open CochainComplex
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
private abbrev Qambient :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).Q

/-- Helper for Lemma 13.15.2: the bounded-below quasi-isomorphism system inherits the canonical
left calculus of fractions from the bounded acyclic Verdier system. -/
private instance qisPlus_hasLeftCalculusOfFractions :
    (Qis⁺(𝒜)).HasLeftCalculusOfFractions := by
  rw [← boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)]
  infer_instance

/-- Helper for Lemma 13.15.2: the bounded-below quasi-isomorphism system inherits the canonical
right calculus of fractions from the bounded acyclic Verdier system. -/
private instance qisPlus_hasRightCalculusOfFractions :
    (Qis⁺(𝒜)).HasRightCalculusOfFractions := by
  rw [← boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)]
  infer_instance

/-- Helper for Lemma 13.15.2: the bounded-above quasi-isomorphism system inherits the canonical
left calculus of fractions from the bounded acyclic Verdier system. -/
private instance qisMinus_hasLeftCalculusOfFractions :
    (Qis⁻(𝒜)).HasLeftCalculusOfFractions := by
  rw [← boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)]
  infer_instance

/-- Helper for Lemma 13.15.2: the bounded-above quasi-isomorphism system inherits the canonical
right calculus of fractions from the bounded acyclic Verdier system. -/
private instance qisMinus_hasRightCalculusOfFractions :
    (Qis⁻(𝒜)).HasRightCalculusOfFractions := by
  rw [← boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)]
  infer_instance

/-- Helper for Lemma 13.15.2: after including `D⁻(ℬ)` into `D(ℬ)`, the bounded-above derived
functor agrees with the ambient one on `K⁻(𝒜)`. -/
noncomputable abbrev mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso :
    mapBoundedAboveHomotopyCategoryToDerivedAbove F ⋙
      ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ))) ≅
    ObjectProperty.ι (HomotopyCategory.minus 𝒜) ⋙ mapHomotopyCategoryToDerived F :=
  (Functor.associator
      (mapBoundedAboveHomotopyCategory F)
      mapBoundedAboveHomotopyToDerivedAbove
      (ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ))))).symm ≪≫
    Functor.isoWhiskerLeft
      (mapBoundedAboveHomotopyCategory F)
      (ObjectProperty.liftCompιIso
        (t.minus : ObjectProperty (D(ℬ)))
        (ObjectProperty.ι (HomotopyCategory.minus ℬ) ⋙ DerivedCategory.Qh)
        qh_obj_mem_t_minus) ≪≫
    Functor.associator
      (mapBoundedAboveHomotopyCategory F)
      (ObjectProperty.ι (HomotopyCategory.minus ℬ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      ((HomotopyCategory.minus ℬ).liftCompιIso
        ((HomotopyCategory.minus 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ))
        (mapHomotopyCategory_obj_mem_boundedAbove F))
      DerivedCategory.Qh

local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F

/-- Helper for Lemma 13.15.2: a denominator triangle yields the equality needed to build the
induced morphism in a costructured-arrow indexing category. -/
private theorem denominatorCostructuredArrowHomEq
    {D : Type*} [Category D] (S : MorphismProperty D)
    {X X' X'' : D}
    (s : X ⟶ X') (s' : X ⟶ X'') (hs : S s) (hs' : S s') (f : X' ⟶ X'')
    (hf : s ≫ f = s') :
    S.Q.map f ≫ (Localization.isoOfHom S.Q S s' hs').inv =
      (Localization.isoOfHom S.Q S s hs).inv := by
  -- Proof comment: localize the denominator triangle and cancel the two denominator
  -- isomorphisms to isolate the required comparison morphism.
  have hsq := congrArg
    (fun k ↦
      (Localization.isoOfHom S.Q S s hs).inv ≫ k ≫
        (Localization.isoOfHom S.Q S s' hs').inv)
    (congrArg (fun k ↦ S.Q.map k) hf)
  simpa [Functor.map_comp, Category.assoc, Localization.isoOfHom_hom] using hsq

/-- Helper for Lemma 13.15.2: a denominator triangle yields the equality needed to build the
induced morphism in a structured-arrow indexing category. -/
private theorem denominatorStructuredArrowHomEq
    {D : Type*} [Category D] (S : MorphismProperty D)
    {X X' X'' : D}
    (s : X' ⟶ X) (s' : X'' ⟶ X) (hs : S s) (hs' : S s') (f : X' ⟶ X'')
    (hf : f ≫ s' = s) :
    (Localization.isoOfHom S.Q S s hs).inv ≫ S.Q.map f =
      (Localization.isoOfHom S.Q S s' hs').inv := by
  -- Proof comment: this is the dual normalization for structured-arrow denominators.
  have hsq := congrArg
    (fun k ↦
      (Localization.isoOfHom S.Q S s hs).inv ≫ k ≫
        (Localization.isoOfHom S.Q S s' hs').inv)
    (congrArg (fun k ↦ S.Q.map k) hf)
  simpa [Functor.map_comp, Category.assoc, Localization.isoOfHom_hom] using hsq

/-- Helper for Lemma 13.15.2: every ambient right-indexing object maps to one indexed by an
actual arrow into `X`. -/
private theorem costructuredArrowExistsHomFromPlainMap
    {D : Type*} [Category D] (S : MorphismProperty D)
    [S.HasRightCalculusOfFractions]
    {X : D} (g : CostructuredArrow S.Q (S.Q.obj X)) :
    ∃ (X' : D) (s : X' ⟶ g.left) (_ : S s) (f : X' ⟶ X),
      S.Q.map s ≫ g.hom = S.Q.map f := by
  -- Proof comment: represent `g.hom` by a right fraction in the localization; its numerator
  -- and denominator give the desired plain-map presentation.
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction S.Q S g.hom
  refine ⟨ψ.X', ψ.s, ψ.hs, ψ.f, ?_⟩
  simpa [hψ] using rfl

/-- Helper for Lemma 13.15.2: a right fraction can be completed to a common-target denominator
square. -/
private theorem rightFractionExistsTargetDenominatorSquare
    {D : Type*} [Category D] (S : MorphismProperty D)
    [S.HasLeftCalculusOfFractions]
    {A X : D} (ψ : S.RightFraction A X) :
    ∃ (X' : D) (s : X ⟶ X') (_ : S s) (f : A ⟶ X'),
      ψ.s ≫ f = ψ.f ≫ s := by
  -- Proof comment: pass to the opposite left fraction and then unop the common-target square.
  obtain ⟨φ, hφ⟩ := ψ.op.exists_rightFraction
  refine ⟨Opposite.unop φ.X', φ.s.unop, φ.hs, φ.f.unop, ?_⟩
  simpa using (congrArg Quiver.Hom.unop hφ).symm

/-- Helper for Lemma 13.15.2: every ambient right-indexing object maps to one indexed by an
actual denominator. -/
private theorem costructuredArrowExistsHomToDenominator
    {D : Type*} [Category D] (S : MorphismProperty D)
    [S.HasRightCalculusOfFractions] [S.HasLeftCalculusOfFractions]
    {X : D} (g : CostructuredArrow S.Q (S.Q.obj X)) :
    ∃ (X' : D) (s : X ⟶ X') (hs : S s),
      Nonempty (g ⟶ CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) := by
  -- Proof comment: first rewrite `g` as a plain-map stage, then complete that presentation to a
  -- common-target denominator square.
  rcases costructuredArrowExistsHomFromPlainMap S g with ⟨A, t, ht, u, hu⟩
  rcases rightFractionExistsTargetDenominatorSquare S
      (MorphismProperty.RightFraction.mk t ht u) with ⟨X', s, hs, f, hsq⟩
  refine ⟨X', s, hs, ⟨CostructuredArrow.homMk f ?_⟩⟩
  have hcomp : g.hom ≫ S.Q.map s = S.Q.map f := by
    letI : IsIso (S.Q.map t) := Localization.inverts S.Q S t ht
    apply (cancel_epi (S.Q.map t)).1
    calc
      S.Q.map t ≫ (g.hom ≫ S.Q.map s) = (S.Q.map t ≫ g.hom) ≫ S.Q.map s := by
        simp [Category.assoc]
      _ = S.Q.map u ≫ S.Q.map s := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ S.Q.map s) hu
      _ = S.Q.map (u ≫ s) := by
        simp [Functor.map_comp]
      _ = S.Q.map (t ≫ f) := by
        rw [hsq]
      _ = S.Q.map t ≫ S.Q.map f := by
        simp [Functor.map_comp]
  letI : IsIso (S.Q.map s) := Localization.inverts S.Q S s hs
  apply (cancel_mono (S.Q.map s)).1
  calc
    (S.Q.map f ≫ (Localization.isoOfHom S.Q S s hs).inv) ≫ S.Q.map s = S.Q.map f := by
      simp [Category.assoc]
    _ = g.hom ≫ S.Q.map s := hcomp.symm

/-- Helper for Lemma 13.15.2: every ambient left-indexing object receives a morphism from one
indexed by an actual denominator. -/
private theorem structuredArrowExistsHomFromDenominator
    {D : Type*} [Category D] (S : MorphismProperty D)
    [S.HasRightCalculusOfFractions]
    {Y : D} (g : StructuredArrow (S.Q.obj Y) S.Q) :
    ∃ (Y' : D) (s : Y' ⟶ Y) (hs : S s),
      Nonempty (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv) ⟶ g) := by
  -- Proof comment: a right-fraction presentation of `g.hom` already has the denominator
  -- orientation needed for a morphism from a denominator stage.
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction S.Q S g.hom
  refine ⟨ψ.X', ψ.s, ψ.hs, ?_⟩
  refine ⟨StructuredArrow.homMk ψ.f ?_⟩
  calc
    (Localization.isoOfHom S.Q S ψ.s ψ.hs).inv ≫ S.Q.map ψ.f =
        ψ.map S.Q (Localization.inverts S.Q S) := by
          rfl
    _ = g.hom := hψ.symm

/-- Helper for Lemma 13.15.2: the denominator stages out of `X.obj` whose targets stay in
`K⁺(𝒜)`. -/
private abbrev boundedBelowTargetDenominatorProperty
    (X : K⁺(𝒜)) : ObjectProperty (MorphismProperty.Under Qis ⊤ X.obj) :=
  fun U ↦ HomotopyCategory.plus 𝒜 U.right

/-- Helper for Lemma 13.15.2: the bounded-target full subcategory of `X.obj / Qis` is final. -/
private theorem boundedBelowTargetDenominatorInclusionFinal
    [HasDerivedCategory 𝒜]
    (X : K⁺(𝒜)) :
    Functor.Final (ObjectProperty.ι (boundedBelowTargetDenominatorProperty X)) := by
  let P := boundedBelowTargetDenominatorProperty X
  let inclusion := ObjectProperty.ι P
  let h :
      ∀ U : MorphismProperty.Under Qis ⊤ X.obj,
        ∃ V : P.FullSubcategory, Nonempty (U ⟶ inclusion.obj V) := by
    intro U
    obtain ⟨Y, t, ht⟩ :=
      quasiIso_to_bounded_below_refinement X U.hom U.prop
    let V : P.FullSubcategory :=
      ⟨@MorphismProperty.Under.mk _ _ Qis ⊤ _ _
        (U.hom ≫ t)
        ((HomotopyCategory.quasiIso 𝒜 (up ℤ)).comp_mem _ _ U.prop ht), by
          simpa [HomotopyCategory.plus] using Y.property⟩
    refine ⟨V, ?_⟩
    -- Proof comment: postcomposing by the bounded-below refinement gives the required morphism
    -- into the good full subcategory.
    exact ⟨MorphismProperty.Under.homMk t rfl⟩
  -- Proof comment: the bounded-below refinement lemma is exactly the Stacks cofinality input.
  exact Functor.final_of_exists_of_isFiltered_of_fullyFaithful inclusion h

/-- Helper for Lemma 13.15.2: the denominator stages into `X.obj` whose sources stay in
`K⁻(𝒜)`. -/
private abbrev boundedAboveSourceDenominatorProperty
    (X : K⁻(𝒜)) : ObjectProperty (MorphismProperty.Over Qis ⊤ X.obj) :=
  fun U ↦ HomotopyCategory.minus 𝒜 U.left

/-- Helper for Lemma 13.15.2: the bounded-source full subcategory of `Qis / X.obj` is initial. -/
private theorem boundedAboveSourceDenominatorInclusionInitial
    [HasDerivedCategory 𝒜]
    (X : K⁻(𝒜)) :
    Functor.Initial (ObjectProperty.ι (boundedAboveSourceDenominatorProperty X)) := by
  let P := boundedAboveSourceDenominatorProperty X
  let inclusion := ObjectProperty.ι P
  let h :
      ∀ U : MorphismProperty.Over Qis ⊤ X.obj,
        ∃ V : P.FullSubcategory, Nonempty (inclusion.obj V ⟶ U) := by
    intro U
    obtain ⟨Y, t, ht⟩ :=
      quasiIso_from_bounded_above_refinement X U.hom U.prop
    let V : P.FullSubcategory :=
      ⟨@MorphismProperty.Over.mk _ _ Qis ⊤ _ _
        (t ≫ U.hom)
        ((HomotopyCategory.quasiIso 𝒜 (up ℤ)).comp_mem _ _ ht U.prop), by
          simpa [HomotopyCategory.minus] using Y.property⟩
    refine ⟨V, ?_⟩
    -- Proof comment: precomposing by the bounded-above refinement gives the required morphism
    -- from the good full subcategory.
    exact ⟨MorphismProperty.Over.homMk t rfl⟩
  -- Proof comment: this is the dual coinitiality statement from the source proof.
  exact Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful inclusion h

/-- Helper for Lemma 13.15.2: for any denominator system `S`, the ordinary denominator category
`X / S` maps to the ambient costructured-arrow indexing category for the pointwise right-derived
value at `X`. -/
private noncomputable def targetDenominatorToCostructuredArrow
    {D : Type*} [Category D] (S : MorphismProperty D)
    (X : D) :
    (MorphismProperty.Under S ⊤ X) ⥤ CostructuredArrow S.Q (S.Q.obj X) where
  obj U := CostructuredArrow.mk ((Localization.isoOfHom S.Q S U.hom U.prop).inv)
  map := fun {U V} f ↦
    CostructuredArrow.homMk f.right
      (denominatorCostructuredArrowHomEq S
        U.hom V.hom U.prop V.prop f.right (MorphismProperty.Under.w f))

/-- Helper for Lemma 13.15.2: for any denominator system `S`, the ordinary denominator functor
`X / S ⥤ CostructuredArrow` is final. -/
private theorem targetDenominatorToCostructuredArrow_final
    {D : Type*} [Category D] (S : MorphismProperty D)
    [S.HasRightCalculusOfFractions] [S.HasLeftCalculusOfFractions]
    (X : D) :
    Functor.Final (targetDenominatorToCostructuredArrow S X) := by
  let T := targetDenominatorToCostructuredArrow S X
  -- Proof comment: every ambient stage refines to an actual denominator stage, and two such
  -- refinements into the same denominator equalize after refining that denominator once more.
  refine Functor.final_of_exists_of_isFiltered T ?_ ?_
  · intro g
    rcases costructuredArrowExistsHomToDenominator S g with
      ⟨X', s, hs, ⟨α⟩⟩
    exact ⟨@MorphismProperty.Under.mk _ _ S ⊤ _ _ s hs, ⟨α⟩⟩
  · intro g U α β
    have hα :
        S.Q.map α.left = g.hom ≫ S.Q.map U.hom := by
      have h :=
        congrArg (fun k ↦ k ≫ S.Q.map U.hom) α.w
      simpa [T, targetDenominatorToCostructuredArrow, Category.assoc,
        Localization.isoOfHom_hom] using h
    have hβ :
        S.Q.map β.left = g.hom ≫ S.Q.map U.hom := by
      have h :=
        congrArg (fun k ↦ k ≫ S.Q.map U.hom) β.w
      simpa [T, targetDenominatorToCostructuredArrow, Category.assoc,
        Localization.isoOfHom_hom] using h
    obtain ⟨Y, t, ht, hfac⟩ :=
      (MorphismProperty.map_eq_iff_postcomp S.Q S α.left β.left).1
        (hα.trans hβ.symm)
    let V : MorphismProperty.Under S ⊤ X :=
      @MorphismProperty.Under.mk _ _ S ⊤ _ _ (U.hom ≫ t) (S.comp_mem _ _ U.prop ht)
    let γ : U ⟶ V :=
      MorphismProperty.Under.homMk t rfl
    refine ⟨V, γ, ?_⟩
    apply CostructuredArrow.hom_ext
    simpa [T, targetDenominatorToCostructuredArrow, γ, V, Category.assoc] using hfac

/-- Helper for Lemma 13.15.2: for any denominator system `S`, the ordinary denominator category
`S / X` maps to the ambient structured-arrow indexing category for the pointwise left-derived
value at `X`. -/
private noncomputable def sourceDenominatorToStructuredArrow
    {D : Type*} [Category D] (S : MorphismProperty D)
    (X : D) :
    (MorphismProperty.Over S ⊤ X) ⥤ StructuredArrow (S.Q.obj X) S.Q where
  obj U := StructuredArrow.mk ((Localization.isoOfHom S.Q S U.hom U.prop).inv)
  map := fun {U V} f ↦
    StructuredArrow.homMk f.left
      (denominatorStructuredArrowHomEq S
        U.hom V.hom U.prop V.prop f.left (MorphismProperty.Over.w f))

/-- Helper for Lemma 13.15.2: for any denominator system `S`, the ordinary denominator functor
`S / X ⥤ StructuredArrow` is initial. -/
private theorem sourceDenominatorToStructuredArrow_initial
    {D : Type*} [Category D] (S : MorphismProperty D)
    [S.HasRightCalculusOfFractions]
    (X : D) :
    Functor.Initial (sourceDenominatorToStructuredArrow S X) := by
  let T := sourceDenominatorToStructuredArrow S X
  -- Proof comment: every ambient structured-arrow stage receives a morphism from a denominator
  -- stage, and two maps out of the same denominator become equal after refining the source once.
  refine Functor.initial_of_exists_of_isCofiltered T ?_ ?_
  · intro g
    rcases structuredArrowExistsHomFromDenominator S g with
      ⟨Y', s, hs, ⟨α⟩⟩
    exact ⟨@MorphismProperty.Over.mk _ _ S ⊤ _ _ s hs, ⟨α⟩⟩
  · intro g U α β
    have hα :
        S.Q.map α.right = S.Q.map U.hom ≫ g.hom := by
      apply (cancel_epi (Localization.isoOfHom S.Q S U.hom U.prop).inv).1
      simpa [Category.assoc, Localization.isoOfHom_hom] using α.w.symm
    have hβ :
        S.Q.map β.right = S.Q.map U.hom ≫ g.hom := by
      apply (cancel_epi (Localization.isoOfHom S.Q S U.hom U.prop).inv).1
      simpa [Category.assoc, Localization.isoOfHom_hom] using β.w.symm
    obtain ⟨Y, t, ht, hfac⟩ :=
      (MorphismProperty.map_eq_iff_precomp S.Q S α.right β.right).1
        (hα.trans hβ.symm)
    let V : MorphismProperty.Over S ⊤ X :=
      @MorphismProperty.Over.mk _ _ S ⊤ _ _ (t ≫ U.hom) (S.comp_mem _ _ ht U.prop)
    let γ : V ⟶ U :=
      MorphismProperty.Over.homMk t rfl
    refine ⟨V, γ, ?_⟩
    apply StructuredArrow.hom_ext
    simpa [T, sourceDenominatorToStructuredArrow, γ, V, Category.assoc] using hfac

/-- Helper for Lemma 13.15.2: the ambient right-derived indexing stages over `X.obj` whose left
objects remain bounded below. -/
private abbrev boundedBelowAmbientCostructuredArrowProperty
    (X : K⁺(𝒜)) : ObjectProperty (CostructuredArrow Qambient (Qambient.obj X.obj)) :=
  fun g ↦ HomotopyCategory.plus 𝒜 g.left

/-- Helper for Lemma 13.15.2: the bounded-left full subcategory of the ambient right-derived
indexing category is final. -/
private theorem boundedBelowAmbientCostructuredArrowInclusionFinal
    [HasDerivedCategory 𝒜]
    (X : K⁺(𝒜)) :
    Functor.Final (ObjectProperty.ι (boundedBelowAmbientCostructuredArrowProperty X)) := by
  let P := boundedBelowAmbientCostructuredArrowProperty X
  let inclusion := ObjectProperty.ι P
  let T := targetDenominatorToCostructuredArrow Qis X.obj
  letI : Functor.Final T := targetDenominatorToCostructuredArrow_final Qis X.obj
  letI : IsFiltered (CostructuredArrow Qambient (Qambient.obj X.obj)) := IsFiltered.of_final T
  let h :
      ∀ g : CostructuredArrow Qambient (Qambient.obj X.obj),
        ∃ V : P.FullSubcategory, Nonempty (g ⟶ inclusion.obj V) := by
    intro g
    obtain ⟨Y, s, hs, ⟨α⟩⟩ :=
      costructuredArrowExistsHomToDenominator Qis g
    obtain ⟨Y', t, ht⟩ :=
      quasiIso_to_bounded_below_refinement X s hs
    let U : MorphismProperty.Under Qis ⊤ X.obj :=
      @MorphismProperty.Under.mk _ _ Qis ⊤ _ _ s hs
    let Vunder : MorphismProperty.Under Qis ⊤ X.obj :=
      @MorphismProperty.Under.mk _ _ Qis ⊤ _ _ (s ≫ t)
        ((HomotopyCategory.quasiIso 𝒜 (up ℤ)).comp_mem _ _ hs ht)
    let β : T.obj U ⟶ T.obj Vunder :=
      T.map (MorphismProperty.Under.homMk t rfl)
    let V : P.FullSubcategory :=
      ⟨T.obj Vunder, by
        -- Proof comment: the refined denominator now lands in the bounded-below homotopy category.
        simpa [P, T, targetDenominatorToCostructuredArrow, Vunder, HomotopyCategory.plus]
          using Y'.property⟩
    refine ⟨V, ?_⟩
    -- Proof comment: first move to a literal denominator stage, then postcompose with the
    -- bounded-below refinement of its target.
    refine ⟨α ≫ ?_⟩
    change T.obj U ⟶ T.obj Vunder
    exact β
  -- Proof comment: every ambient stage admits a bounded-below refinement, so the bounded-left
  -- full subcategory is cofinal in the ambient costructured-arrow indexing category.
  exact Functor.final_of_exists_of_isFiltered_of_fullyFaithful inclusion h

/-- Helper for Lemma 13.15.2: the ambient left-derived indexing stages over `X.obj` whose right
objects remain bounded above. -/
private abbrev boundedAboveAmbientStructuredArrowProperty
    (X : K⁻(𝒜)) : ObjectProperty (StructuredArrow (Qambient.obj X.obj) Qambient) :=
  fun g ↦ HomotopyCategory.minus 𝒜 g.right

/-- Helper for Lemma 13.15.2: the bounded-right full subcategory of the ambient left-derived
indexing category is initial. -/
private theorem boundedAboveAmbientStructuredArrowInclusionInitial
    [HasDerivedCategory 𝒜]
    (X : K⁻(𝒜)) :
    Functor.Initial (ObjectProperty.ι (boundedAboveAmbientStructuredArrowProperty X)) := by
  let P := boundedAboveAmbientStructuredArrowProperty X
  let inclusion := ObjectProperty.ι P
  let T := sourceDenominatorToStructuredArrow Qis X.obj
  letI : Functor.Initial T := sourceDenominatorToStructuredArrow_initial Qis X.obj
  letI : IsCofiltered (StructuredArrow (Qambient.obj X.obj) Qambient) := IsCofiltered.of_initial T
  let h :
      ∀ g : StructuredArrow (Qambient.obj X.obj) Qambient,
        ∃ V : P.FullSubcategory, Nonempty (inclusion.obj V ⟶ g) := by
    intro g
    obtain ⟨Y, s, hs, ⟨α⟩⟩ :=
      structuredArrowExistsHomFromDenominator Qis g
    obtain ⟨Y', t, ht⟩ :=
      quasiIso_from_bounded_above_refinement X s hs
    let U : MorphismProperty.Over Qis ⊤ X.obj :=
      @MorphismProperty.Over.mk _ _ Qis ⊤ _ _ s hs
    let Vover : MorphismProperty.Over Qis ⊤ X.obj :=
      @MorphismProperty.Over.mk _ _ Qis ⊤ _ _ (t ≫ s)
        ((HomotopyCategory.quasiIso 𝒜 (up ℤ)).comp_mem _ _ ht hs)
    let β : T.obj Vover ⟶ T.obj U :=
      T.map (MorphismProperty.Over.homMk t rfl)
    let V : P.FullSubcategory :=
      ⟨T.obj Vover, by
        -- Proof comment: the refined denominator now starts in the bounded-above homotopy
        -- category.
        simpa [P, T, sourceDenominatorToStructuredArrow, Vover, HomotopyCategory.minus]
          using Y'.property⟩
    refine ⟨V, ?_⟩
    -- Proof comment: precompose the literal denominator stage with the bounded-above refinement,
    -- then use the existing map from that denominator stage to the ambient one.
    refine ⟨?_ ≫ α⟩
    change T.obj Vover ⟶ T.obj U
    exact β
  -- Proof comment: every ambient structured-arrow stage receives a map from one whose source is
  -- bounded above, so the bounded-right full subcategory is coinitial.
  exact Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful inclusion h

/-- Helper for Lemma 13.15.2: the canonical inclusion `D⁺(ℬ) ↪ D(ℬ)` reflects isomorphisms. -/
lemma bounded_below_derived_inclusion_reflects_isomorphisms :
    (ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))).ReflectsIsomorphisms := by
  exact Functor.FullyFaithful.reflectsIsomorphisms
    (t.plus : ObjectProperty (D(ℬ))).fullyFaithfulι

/-- Helper for Lemma 13.15.2: the canonical inclusion `D⁻(ℬ) ↪ D(ℬ)` reflects isomorphisms. -/
lemma bounded_above_derived_inclusion_reflects_isomorphisms :
    (ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ)))).ReflectsIsomorphisms := by
  exact Functor.FullyFaithful.reflectsIsomorphisms
    (t.minus : ObjectProperty (D(ℬ))).fullyFaithfulι

/-- Helper for Lemma 13.15.2: an explicit colimit cocone on the ambient right-derived indexing
diagram packages the pointwise right-derived existence owner at the given object. -/
private lemma hasPointwiseRightDerivedFunctorAt_of_colimitCocone
    {D : Type*} [Category D]
    {S : MorphismProperty D} {D' : Type*} [Category D']
    (G : D ⥤ D') {X : D}
    (cX : ColimitCocone (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ G)) :
    G.HasPointwiseRightDerivedFunctorAt S X := by
  -- Proof comment: a pointwise right-derived value is exactly a colimit on the ambient
  -- costructured-arrow indexing diagram.
  exact ⟨show HasPointwiseLeftKanExtensionAt S.Q G (S.Q.obj X) from HasColimit.mk cX⟩

/-- Helper for Lemma 13.15.2: any explicit ambient right-derived colimit cocone identifies its
vertex with the canonical right-derived value. -/
private noncomputable def rightDerivedValueIsoOfColimitCocone
    {D : Type*} [Category D]
    {S : MorphismProperty D} {D' : Type*} [Category D']
    (G : D ⥤ D') {X : D} [G.HasPointwiseRightDerivedFunctorAt S X]
    (cX : ColimitCocone (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ G)) :
    cX.cocone.pt ≅ rightDerivedValue S G X := by
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ G
  let _ : HasColimit RX := HasPointwiseRightDerivedFunctorAt.hasColimit G S.Q S X
  -- Proof comment: compare the chosen cocone with the canonical colimit presentation of
  -- `rightDerivedValue S G X`.
  change cX.cocone.pt ≅ colimit RX
  simpa [RX, rightDerivedValue] using (colimit.isoColimitCocone cX).symm

/-- Helper for Lemma 13.15.2: an explicit limit cone on the ambient left-derived indexing
diagram packages the pointwise left-derived existence owner at the given object. -/
private lemma hasPointwiseLeftDerivedFunctorAt_of_limitCone
    {D : Type*} [Category D]
    {S : MorphismProperty D} {D' : Type*} [Category D']
    (G : D ⥤ D') {X : D}
    (cX : LimitCone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ G)) :
    G.HasPointwiseLeftDerivedFunctorAt S X := by
  -- Proof comment: dually, a pointwise left-derived value is exactly a limit on the ambient
  -- structured-arrow indexing diagram.
  exact ⟨show HasPointwiseRightKanExtensionAt S.Q G (S.Q.obj X) from HasLimit.mk cX⟩

/-- Helper for Lemma 13.15.2: any explicit ambient left-derived limit cone identifies its vertex
with the canonical left-derived value. -/
private noncomputable def leftDerivedValueIsoOfLimitCone
    {D : Type*} [Category D]
    {S : MorphismProperty D} {D' : Type*} [Category D']
    (G : D ⥤ D') {X : D} [G.HasPointwiseLeftDerivedFunctorAt S X]
    (cX : LimitCone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ G)) :
    cX.cone.pt ≅ leftDerivedValue S G X := by
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ G
  let _ : HasLimit LX := HasPointwiseLeftDerivedFunctorAt.hasLimit G S.Q S X
  -- Proof comment: compare the chosen cone with the canonical limit presentation of
  -- `leftDerivedValue S G X`.
  change cX.cone.pt ≅ limit LX
  simpa [LX, leftDerivedValue] using (limit.isoLimitCone cX).symm

/-- Helper for Lemma 13.15.2: once the ambient and bounded-below right-derived values at `X`
are identified by an isomorphism compatible with the identity legs, the computing predicates are
equivalent. -/
lemma computes_right_derived_at_iff_of_value_iso
    (X : K⁺(𝒜))
    [HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X]
    (e : rightDerivedValue Qis KtoD X.obj ≅
      (rightDerivedValue (Qis⁺(𝒜)) KplusToDplus X).obj)
    (hleg :
      rightDerivedValueLeg Qis KtoD (𝟙 X.obj) (MorphismProperty.id_mem Qis X.obj) ≫ e.hom =
        ((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F).app X).inv ≫
          (ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))).map
            (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁺(𝒜)) X))) :
    ComputesRightDerivedAt KtoD Qis X.obj ↔
      ComputesRightDerivedAt KplusToDplus (Qis⁺(𝒜)) X := by
  let plusι : D⁺(ℬ) ⥤ D(ℬ) :=
    ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))
  constructor
  · intro h
    letI : ComputesRightDerivedAt KtoD Qis X.obj := h
    have hcomp :
        IsIso
          (((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F).app X).inv ≫
            plusι.map
              (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁺(𝒜)) X))) := by
      -- Proof comment: rewrite the bounded identity leg to the ambient one.
      have hambient :
          IsIso
            (rightDerivedValueLeg Qis KtoD (𝟙 X.obj)
              (MorphismProperty.id_mem Qis X.obj) ≫ e.hom) := by
        exact
          (isIso_comp_right_iff
            (rightDerivedValueLeg Qis KtoD (𝟙 X.obj)
              (MorphismProperty.id_mem Qis X.obj))
            e.hom).2 inferInstance
      rw [← hleg]
      exact hambient
    have hplus :
        IsIso
          (plusι.map
            (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁺(𝒜)) X))) := by
      exact
        (isIso_comp_left_iff
          ((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F).app X).inv
          (plusι.map
            (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁺(𝒜)) X)))).1 hcomp
    have hbounded :
        IsIso
          (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
            (MorphismProperty.id_mem (Qis⁺(𝒜)) X)) := by
      letI : plusι.ReflectsIsomorphisms :=
        bounded_below_derived_inclusion_reflects_isomorphisms
      exact
        Functor.ReflectsIsomorphisms.reflects plusι
          (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
            (MorphismProperty.id_mem (Qis⁺(𝒜)) X))
    exact ⟨hbounded⟩
  · intro h
    letI : ComputesRightDerivedAt KplusToDplus (Qis⁺(𝒜)) X := h
    have hplus :
        IsIso
          (plusι.map
            (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁺(𝒜)) X))) := by
      infer_instance
    have hcomp :
        IsIso
          (((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F).app X).inv ≫
            plusι.map
              (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁺(𝒜)) X))) := by
      exact
        (isIso_comp_left_iff
          ((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F).app X).inv
          (plusι.map
            (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁺(𝒜)) X)))).2 hplus
    have hambient :
        IsIso
          (rightDerivedValueLeg Qis KtoD (𝟙 X.obj)
            (MorphismProperty.id_mem Qis X.obj) ≫ e.hom) := by
      rw [hleg]
      exact hcomp
    exact
      ⟨(isIso_comp_right_iff
          (rightDerivedValueLeg Qis KtoD (𝟙 X.obj)
            (MorphismProperty.id_mem Qis X.obj))
          e.hom).1 hambient⟩

/-- Helper for Lemma 13.15.2: once the ambient and bounded-above left-derived values at `X`
are identified by an isomorphism compatible with the identity projections, the computing
predicates are equivalent. -/
lemma computes_left_derived_at_iff_of_value_iso
    (X : K⁻(𝒜))
    [HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X]
    (e : leftDerivedValue Qis KtoD X.obj ≅
      (leftDerivedValue (Qis⁻(𝒜)) KminusToDminus X).obj)
    (hprojection :
      e.hom ≫
          (ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ)))).map
            (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁻(𝒜)) X)) ≫
          ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso F).app X).hom =
        leftDerivedValueProjection Qis KtoD (𝟙 X.obj) (MorphismProperty.id_mem Qis X.obj)) :
    ComputesLeftDerivedAt KtoD Qis X.obj ↔
      ComputesLeftDerivedAt KminusToDminus (Qis⁻(𝒜)) X := by
  let minusι : D⁻(ℬ) ⥤ D(ℬ) :=
    ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ)))
  constructor
  · intro h
    letI : ComputesLeftDerivedAt KtoD Qis X.obj := h
    have hcomp :
        IsIso
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X)) ≫
            ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso F).app X).hom) := by
      have hambient :
          IsIso
            (leftDerivedValueProjection Qis KtoD (𝟙 X.obj)
              (MorphismProperty.id_mem Qis X.obj)) := by
        infer_instance
      rw [hprojection]
      exact hambient
    have hmid :
        IsIso
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X))) := by
      exact
        (isIso_comp_right_iff
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X)))
          ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso F).app X).hom).1
          (by simpa [Category.assoc] using hcomp)
    have hminus :
        IsIso
          (minusι.map
            (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁻(𝒜)) X))) := by
      exact
        (isIso_comp_left_iff
          e.hom
          (minusι.map
            (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁻(𝒜)) X)))).1 hmid
    have hbounded :
        IsIso
          (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
            (MorphismProperty.id_mem (Qis⁻(𝒜)) X)) := by
      letI : minusι.ReflectsIsomorphisms :=
        bounded_above_derived_inclusion_reflects_isomorphisms
      exact
        Functor.ReflectsIsomorphisms.reflects minusι
          (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
            (MorphismProperty.id_mem (Qis⁻(𝒜)) X))
    exact ⟨hbounded⟩
  · intro h
    letI : ComputesLeftDerivedAt KminusToDminus (Qis⁻(𝒜)) X := h
    have hminus :
        IsIso
          (minusι.map
            (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁻(𝒜)) X))) := by
      infer_instance
    have hmid :
        IsIso
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X))) := by
      exact
        (isIso_comp_left_iff
          e.hom
          (minusι.map
            (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
              (MorphismProperty.id_mem (Qis⁻(𝒜)) X)))).2 hminus
    have hcomp :
        IsIso
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X)) ≫
            ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso F).app X).hom) := by
      simpa [Category.assoc] using
        (isIso_comp_right_iff
          (e.hom ≫
            minusι.map
              (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
                (MorphismProperty.id_mem (Qis⁻(𝒜)) X)))
          ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso F).app X).hom).2
          hmid
    have hambient :
        IsIso
          (leftDerivedValueProjection Qis KtoD (𝟙 X.obj)
            (MorphismProperty.id_mem Qis X.obj)) := by
      rw [← hprojection]
      simpa [Category.assoc] using hcomp
    exact ⟨hambient⟩

/-- Helper for Lemma 13.15.2: by definition, a bounded-below quasi-isomorphism is exactly an
ambient quasi-isomorphism after applying the inclusion `K⁺(𝒜) ↪ K(𝒜)`. -/
private lemma boundedBelowQuasiIso_iff_ambient
    {X Y : K⁺(𝒜)} (f : X ⟶ Y) :
    Qis⁺(𝒜) f ↔
      Qis ((ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map f) := by
  rfl

/-- Helper for Lemma 13.15.2: by definition, a bounded-above quasi-isomorphism is exactly an
ambient quasi-isomorphism after applying the inclusion `K⁻(𝒜) ↪ K(𝒜)`. -/
private lemma boundedAboveQuasiIso_iff_ambient
    {X Y : K⁻(𝒜)} (f : X ⟶ Y) :
    Qis⁻(𝒜) f ↔
      Qis ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map f) := by
  rfl

/-- Helper for Lemma 13.15.2: the identity denominator on a bounded-below object of `K(𝒜)`
already lies in the bounded-target ambient denominator subcategory. -/
private theorem boundedBelowTargetDenominatorProperty_id
    (X : K⁺(𝒜)) :
    boundedBelowTargetDenominatorProperty X
      (@MorphismProperty.Under.mk _ _ Qis ⊤ _ _
        (𝟙 X.obj) (MorphismProperty.id_mem Qis X.obj)) := by
  -- Proof comment: the identity denominator has target `X.obj`, and `X` is bounded below by
  -- hypothesis.
  simpa [boundedBelowTargetDenominatorProperty, HomotopyCategory.plus] using X.property

/-- Helper for Lemma 13.15.2: the identity denominator on a bounded-above object of `K(𝒜)`
already lies in the bounded-source ambient denominator subcategory. -/
private theorem boundedAboveSourceDenominatorProperty_id
    (X : K⁻(𝒜)) :
    boundedAboveSourceDenominatorProperty X
      (@MorphismProperty.Over.mk _ _ Qis ⊤ _ _
        (𝟙 X.obj) (MorphismProperty.id_mem Qis X.obj)) := by
  -- Proof comment: dually, the identity denominator has source `X.obj`, which is already bounded
  -- above.
  simpa [boundedAboveSourceDenominatorProperty, HomotopyCategory.minus] using X.property

/-- Helper for Lemma 13.15.2: forgetting the bounded-below source but keeping the same
denominator identifies `X / Qis⁺` with the bounded-target full subcategory of `X.obj / Qis`
on objects and morphisms. -/
private noncomputable def boundedBelowTargetDenominatorToAmbient
    (X : K⁺(𝒜)) :
    MorphismProperty.Under (Qis⁺(𝒜)) ⊤ X ⥤
      (boundedBelowTargetDenominatorProperty X).FullSubcategory where
  obj U :=
    ⟨@MorphismProperty.Under.mk _ _ Qis ⊤ _ _
        ((ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map U.hom)
        ((boundedBelowQuasiIso_iff_ambient U.hom).1 U.prop),
      by
        -- Proof comment: the target object is literally `U.right`, now viewed in the ambient
        -- homotopy category, so the bounded-below witness is unchanged.
        simpa [boundedBelowTargetDenominatorProperty, HomotopyCategory.plus] using
          U.right.property⟩
  map {U V} f :=
    ObjectProperty.homMk <|
      MorphismProperty.Under.homMk
        ((ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map f.right)
        (by
          -- Proof comment: the denominator square in `K⁺(𝒜)` remains commutative after
          -- applying the fully faithful inclusion `K⁺(𝒜) ↪ K(𝒜)`.
          simpa [Functor.map_comp] using congrArg
            (fun k ↦ (ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map k)
            (MorphismProperty.Under.w f))

/-- Helper for Lemma 13.15.2: every bounded ambient denominator stage over `X.obj` comes from a
unique denominator stage over `X` in `K⁺(𝒜)`. -/
private noncomputable def boundedBelowTargetDenominatorToAmbient_fullyFaithful
    (X : K⁺(𝒜)) :
    (boundedBelowTargetDenominatorToAmbient X).FullyFaithful := by
  let ιplus : K⁺(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.plus 𝒜)
  let hFF : ιplus.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful ιplus
  let G := boundedBelowTargetDenominatorToAmbient X
  let _ : G.Faithful := by
    constructor
    intro U V f g hfg
    apply Under.Hom.ext
    apply hFF.map_injective
    simpa [G, boundedBelowTargetDenominatorToAmbient] using congrArg (fun k ↦ k.hom.right) hfg
  let _ : G.Full := by
    constructor
    intro U V f
    refine ⟨MorphismProperty.Under.homMk
      (hFF.preimage (show ιplus.obj U.right ⟶ ιplus.obj V.right from f.1.right)) ?_, ?_⟩
    · -- Proof comment: precompose the ambient square along the fully faithful inclusion to
      -- recover the unique bounded-below morphism between denominator stages.
      apply hFF.map_injective
      simpa [Functor.map_comp] using f.1.w.symm
    · ext
      exact hFF.map_preimage (show ιplus.obj U.right ⟶ ιplus.obj V.right from f.1.right)
  exact Functor.FullyFaithful.ofFullyFaithful G

/-- Helper for Lemma 13.15.2: every bounded ambient denominator stage over `X.obj` comes from a
bounded denominator stage over `X`, together with an explicit isomorphism in the full
subcategory. -/
private theorem boundedBelowTargetDenominatorAmbientPreimage
    (X : K⁺(𝒜))
    (V : (boundedBelowTargetDenominatorProperty X).FullSubcategory) :
    (boundedBelowTargetDenominatorToAmbient X).essImage V := by
  let ιplus : K⁺(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.plus 𝒜)
  let hFF : ιplus.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful ιplus
  let Y : K⁺(𝒜) :=
    ⟨V.1.right, by
      simpa [boundedBelowTargetDenominatorProperty, HomotopyCategory.plus] using V.2⟩
  let h : X ⟶ Y := hFF.preimage (show ιplus.obj X ⟶ ιplus.obj Y from V.1.hom)
  have hh : ιplus.map h = V.1.hom := by
    dsimp [h]
    simp
  let U : MorphismProperty.Under (Qis⁺(𝒜)) ⊤ X :=
    @MorphismProperty.Under.mk _ _ (Qis⁺(𝒜)) ⊤ _ _ h
      ((boundedBelowQuasiIso_iff_ambient h).2 <| by
        have hqis : Qis (ιplus.map h) := by
          simpa [hh] using V.1.prop
        simpa using hqis)
  refine ⟨U, ⟨ObjectProperty.isoMk (boundedBelowTargetDenominatorProperty X) <|
    MorphismProperty.Under.isoMk (Iso.refl _) ?_⟩⟩
  -- Proof comment: the fully faithful preimage recovers the ambient denominator exactly, so the
  -- comparison is the identity on the target object.
  have hcomp : ιplus.map h ≫ 𝟙 V.1.right = V.1.hom := by
    rw [hh]
    exact Category.comp_id V.1.hom
  simpa [boundedBelowTargetDenominatorToAmbient, U] using hcomp

/-- Helper for Lemma 13.15.2: the bounded denominator functor is essentially surjective onto the
bounded-target ambient full subcategory. -/
private noncomputable def boundedBelowTargetDenominatorToAmbient_essSurj
    (X : K⁺(𝒜)) :
    (boundedBelowTargetDenominatorToAmbient X).EssSurj := by
  refine ⟨fun V ↦ ?_⟩
  -- Proof comment: the owner-level preimage helper packages the fully faithful pullback and the
  -- resulting `Under` isomorphism in one reusable step.
  simpa using boundedBelowTargetDenominatorAmbientPreimage X V

/-- Helper for Lemma 13.15.2: the bounded-below denominator category over `X` is equivalent to
the bounded-target full subcategory of the ambient denominator category over `X.obj`. -/
private noncomputable def boundedBelowTargetDenominatorEquivalence
    (X : K⁺(𝒜)) :
    MorphismProperty.Under (Qis⁺(𝒜)) ⊤ X ≌
      (boundedBelowTargetDenominatorProperty X).FullSubcategory := by
  let G := boundedBelowTargetDenominatorToAmbient X
  let _ : G.Full := (boundedBelowTargetDenominatorToAmbient_fullyFaithful X).full
  let _ : G.Faithful := (boundedBelowTargetDenominatorToAmbient_fullyFaithful X).faithful
  let _ : G.EssSurj := boundedBelowTargetDenominatorToAmbient_essSurj X
  let _ : G.IsEquivalence := { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  exact G.asEquivalence

/-- Helper for Lemma 13.15.2: on the bounded-below denominator category, the bounded and ambient
ordinary denominator diagrams agree after including `D⁺(ℬ)` into `D(ℬ)`. -/
private noncomputable def boundedBelowTargetDenominatorDiagramIso
    (X : K⁺(𝒜)) :
    MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
        KplusToDplus ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ))) ≅
      boundedBelowTargetDenominatorToAmbient X ⋙
        ObjectProperty.ι (boundedBelowTargetDenominatorProperty X) ⋙
        MorphismProperty.Under.forget Qis ⊤ X.obj ⋙ CategoryTheory.Under.forget X.obj ⋙ KtoD :=
  by
    refine NatIso.ofComponents
      (fun U ↦ by
        simpa [boundedBelowTargetDenominatorToAmbient] using
          (mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F).app U.right)
      ?_
    intro U V f
    -- Proof comment: both denominator diagrams act on a morphism by the same map on `f.right`;
    -- naturality is exactly the owner-level naturality of
    -- `mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso`.
    change
      ((KplusToDplus ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))).map f.right) ≫
          ((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F).app V.right).hom =
        ((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F).app U.right).hom ≫
          ((ObjectProperty.ι (HomotopyCategory.plus 𝒜) ⋙ KtoD).map f.right)
    exact (mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F).hom.naturality f.right

/-- Helper for Lemma 13.15.2: forgetting the bounded-above source but keeping the same
denominator identifies `Qis⁻ / X` with the bounded-source full subcategory of `Qis / X.obj`
on objects and morphisms. -/
private noncomputable def boundedAboveSourceDenominatorToAmbient
    (X : K⁻(𝒜)) :
    MorphismProperty.Over (Qis⁻(𝒜)) ⊤ X ⥤
      (boundedAboveSourceDenominatorProperty X).FullSubcategory where
  obj U :=
    ⟨@MorphismProperty.Over.mk _ _ Qis ⊤ _ _
        ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map U.hom)
        ((boundedAboveQuasiIso_iff_ambient U.hom).1 U.prop),
      by
        -- Proof comment: the source object is literally `U.left`, now regarded in the ambient
        -- homotopy category, so its bounded-above witness is unchanged.
        simpa [boundedAboveSourceDenominatorProperty, HomotopyCategory.minus] using
          U.left.property⟩
  map {U V} f :=
    ObjectProperty.homMk <|
      MorphismProperty.Over.homMk
        ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map f.left)
        (by
          -- Proof comment: the source-side denominator square in `K⁻(𝒜)` remains commutative
          -- after forgetting to `K(𝒜)`.
          simpa [Functor.map_comp] using congrArg
            (fun k ↦ (ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map k)
            (MorphismProperty.Over.w f))

/-- Helper for Lemma 13.15.2: every bounded ambient source denominator stage under `X.obj`
comes from a unique denominator stage under `X` in `K⁻(𝒜)`. -/
private noncomputable def boundedAboveSourceDenominatorToAmbient_fullyFaithful
    (X : K⁻(𝒜)) :
    (boundedAboveSourceDenominatorToAmbient X).FullyFaithful := by
  let ιminus : K⁻(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.minus 𝒜)
  let hFF : ιminus.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful ιminus
  let G := boundedAboveSourceDenominatorToAmbient X
  let _ : G.Faithful := by
    constructor
    intro U V f g hfg
    apply Over.Hom.ext
    apply hFF.map_injective
    simpa [G, boundedAboveSourceDenominatorToAmbient] using congrArg (fun k ↦ k.hom.left) hfg
  let _ : G.Full := by
    constructor
    intro U V f
    refine ⟨MorphismProperty.Over.homMk
      (hFF.preimage (show ιminus.obj U.left ⟶ ιminus.obj V.left from f.1.left)) ?_, ?_⟩
    · -- Proof comment: the ambient source-side square uniquely lifts through the fully faithful
      -- inclusion `K⁻(𝒜) ↪ K(𝒜)`.
      apply hFF.map_injective
      simpa [Functor.map_comp] using f.1.w
    · ext
      exact hFF.map_preimage (show ιminus.obj U.left ⟶ ιminus.obj V.left from f.1.left)
  exact Functor.FullyFaithful.ofFullyFaithful G

/-- Helper for Lemma 13.15.2: the bounded source-denominator functor is essentially surjective
onto the bounded-source ambient full subcategory. -/
private noncomputable def boundedAboveSourceDenominatorToAmbient_essSurj
    (X : K⁻(𝒜)) :
    (boundedAboveSourceDenominatorToAmbient X).EssSurj := by
  let G := boundedAboveSourceDenominatorToAmbient X
  let ιminus : K⁻(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.minus 𝒜)
  let hFF : ιminus.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful ιminus
  refine ⟨fun V ↦ ?_⟩
  let Y : K⁻(𝒜) :=
    ⟨V.1.left, by
      simpa [boundedAboveSourceDenominatorProperty, HomotopyCategory.minus] using V.2⟩
  let h : Y ⟶ X := hFF.preimage (show ιminus.obj Y ⟶ ιminus.obj X from V.1.hom)
  have hh : ιminus.map h = V.1.hom := by
    dsimp [h]
    simp
  let U : MorphismProperty.Over (Qis⁻(𝒜)) ⊤ X :=
    @MorphismProperty.Over.mk _ _ (Qis⁻(𝒜)) ⊤ _ _ h
      ((boundedAboveQuasiIso_iff_ambient h).2 <| by
        have hqis : Qis (ιminus.map h) := by simpa [hh] using V.1.prop
        simpa using hqis)
  refine ⟨U, ⟨ObjectProperty.isoMk (boundedAboveSourceDenominatorProperty X) <|
    MorphismProperty.Over.isoMk (Iso.refl _) ?_⟩⟩
  -- Proof comment: the chosen bounded-above preimage has exactly the same ambient denominator.
  simpa [G, boundedAboveSourceDenominatorToAmbient, U] using hh.symm

/-- Helper for Lemma 13.15.2: the bounded-above denominator category under `X` is equivalent to
the bounded-source full subcategory of the ambient denominator category under `X.obj`. -/
private noncomputable def boundedAboveSourceDenominatorEquivalence
    (X : K⁻(𝒜)) :
    MorphismProperty.Over (Qis⁻(𝒜)) ⊤ X ≌
      (boundedAboveSourceDenominatorProperty X).FullSubcategory := by
  let G := boundedAboveSourceDenominatorToAmbient X
  let _ : G.Full := (boundedAboveSourceDenominatorToAmbient_fullyFaithful X).full
  let _ : G.Faithful := (boundedAboveSourceDenominatorToAmbient_fullyFaithful X).faithful
  let _ : G.EssSurj := boundedAboveSourceDenominatorToAmbient_essSurj X
  let _ : G.IsEquivalence := { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  exact G.asEquivalence

/-- Helper for Lemma 13.15.2: on the bounded-above denominator category, the bounded and ambient
ordinary denominator diagrams agree after including `D⁻(ℬ)` into `D(ℬ)`. -/
private noncomputable def boundedAboveSourceDenominatorDiagramIso
    (X : K⁻(𝒜)) :
    boundedAboveSourceDenominatorToAmbient X ⋙
        ObjectProperty.ι (boundedAboveSourceDenominatorProperty X) ⋙
        MorphismProperty.Over.forget Qis ⊤ X.obj ⋙ CategoryTheory.Over.forget X.obj ⋙ KtoD ≅
      MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
        KminusToDminus ⋙ ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ))) :=
  by
    refine NatIso.ofComponents
      (fun U ↦ by
        simpa [boundedAboveSourceDenominatorToAmbient] using
          ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso F).app U.left).symm)
      ?_
    intro U V f
    -- Proof comment: dually, the ambient and bounded-above ordinary denominator diagrams differ
    -- only by the canonical codomain comparison on `f.left`.
    simpa [boundedAboveSourceDenominatorToAmbient, Functor.comp_map, Category.assoc] using
      (mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso F).inv.naturality f.left

/-- Helper for Lemma 13.15.2: pointwise right-derived existence for the bounded-below functor is
equivalent to colimit existence on the ordinary bounded denominator diagram. -/
private lemma boundedRightDerivedHasColimit_iff_targetDenominator
    (X : K⁺(𝒜)) :
    HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X ↔
      HasColimit
        (MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
          KplusToDplus) := by
  let T := targetDenominatorToCostructuredArrow (Qis⁺(𝒜)) X
  letI : Functor.Final T := targetDenominatorToCostructuredArrow_final (Qis⁺(𝒜)) X
  -- Proof comment: after importing the canonical bounded Situation 13.15.1 API, the bounded
  -- owner rewrite is identical to the ambient denominator normalization.
  rw [Functor.hasPointwiseRightDerivedFunctorAt_iff
    (F := KplusToDplus) (L := (Qis⁺(𝒜)).Q) (W := Qis⁺(𝒜)) X]
  simpa [CategoryTheory.Functor.HasPointwiseLeftKanExtensionAt,
    targetDenominatorToCostructuredArrow] using
    (Functor.Final.hasColimit_comp_iff T
      (G := CostructuredArrow.proj (Qis⁺(𝒜)).Q ((Qis⁺(𝒜)).Q.obj X) ⋙ KplusToDplus)).symm

/-- Helper for Lemma 13.15.2: after restricting the ambient denominator category to bounded
targets and using the denominator-category equivalence, ambient colimit existence is equivalent to
colimit existence on the bounded denominator diagram after including `D⁺(ℬ)` into `D(ℬ)`. -/
private lemma ambientTargetDenominatorHasColimit_iff_boundedPostcompose
    (X : K⁺(𝒜)) :
    HasColimit
        (MorphismProperty.Under.forget Qis ⊤ X.obj ⋙ CategoryTheory.Under.forget X.obj ⋙ KtoD) ↔
      HasColimit
        (MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
          KplusToDplus ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))) := by
  let P := boundedBelowTargetDenominatorProperty X
  let inclusion := ObjectProperty.ι P
  let Jambient :
      MorphismProperty.Under Qis ⊤ X.obj ⥤ D(ℬ) :=
    MorphismProperty.Under.forget Qis ⊤ X.obj ⋙ CategoryTheory.Under.forget X.obj ⋙ KtoD
  let Jrestricted : P.FullSubcategory ⥤ D(ℬ) := inclusion ⋙ Jambient
  let E := boundedBelowTargetDenominatorEquivalence X
  let Jbounded :
      MorphismProperty.Under (Qis⁺(𝒜)) ⊤ X ⥤ D(ℬ) :=
    MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
      KplusToDplus ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))
  letI : Functor.Final inclusion := boundedBelowTargetDenominatorInclusionFinal X
  -- Proof comment: first restrict the ambient ordinary denominator diagram to the bounded-target
  -- final subcategory, then replace that full subcategory by the equivalent bounded denominator
  -- category, and finally rewrite the resulting diagram by the canonical comparison iso.
  calc
    HasColimit Jambient
        ↔ HasColimit (inclusion ⋙ Jambient) := by
          simpa [Jambient, inclusion, Jrestricted] using
            (Functor.Final.hasColimit_comp_iff inclusion (G := Jambient)).symm
    _ ↔ HasColimit (E.functor ⋙ Jrestricted) := by
          simpa [E, Jrestricted] using
            (hasColimit_equivalence_comp_iff (e := E) (F := Jrestricted)).symm
    _ ↔ HasColimit Jbounded := by
          simpa [E, Jrestricted, Jbounded] using
            hasColimit_iff_of_iso (boundedBelowTargetDenominatorDiagramIso (F := F) X).symm

-- Proof sketch: pointwise right-derived existence for the bounded-below functor is equivalent
-- to existence for the same source-side functor after including `D⁺(ℬ)` into `D(ℬ)`, and the
-- latter is equivalent to the ambient existence condition by the bounded-below inclusion
-- localizer.
-- Route correction: the naive subset-theorem route would require
-- `((HomotopyCategory.plus 𝒜).ι ⋙ KtoD)` to invert all bounded-below quasi-isomorphisms, which is
-- false in general because `F` need not preserve quasi-isomorphisms. The remaining proof must
-- instead compare the ambient and bounded pointwise comma categories by:
-- (1) identifying `CostructuredArrow mapBoundedBelowHomotopyToDerivedBelow _` with the bounded-left
-- full subcategory of `CostructuredArrow Qambient _`, and
-- (2) proving that this bounded-left full subcategory is final in the ambient comma category by
-- refining an arbitrary ambient stage first to a literal denominator out of `X.obj`, then to a
-- bounded-below denominator via `quasiIso_to_bounded_below_refinement`.
/-- Helper for Lemma 13.15.2: the bounded-below ordinary denominator diagram has a colimit in
`D⁺(ℬ)` exactly when it has one after including `D⁺(ℬ)` into `D(ℬ)`. -/
private lemma boundedBelowTargetDenominatorHasColimit_of_postcomposeDerivedInclusion
    (X : K⁺(𝒜))
    (hJ :
      HasColimit
      (MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
        KplusToDplus ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))))
    (hcolimit :
      (t.plus : ObjectProperty (D(ℬ)))
        (colimit
          (MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
            KplusToDplus ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))))) :
    HasColimit
      (MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
        KplusToDplus) := by
  let P : ObjectProperty (D(ℬ)) := t.plus
  let inclusion : P.FullSubcategory ⥤ D(ℬ) := ObjectProperty.ι P
  let J :
      MorphismProperty.Under (Qis⁺(𝒜)) ⊤ X ⥤ P.FullSubcategory :=
    MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ KplusToDplus
  letI : HasColimit (J ⋙ inclusion) := hJ
  letI : CreatesColimit J inclusion :=
    createsColimitFullSubcategoryInclusion J hcolimit
  exact hasColimit_of_created J inclusion

/-- Helper for Lemma 13.15.2: every object of the bounded-below ordinary denominator diagram is
already in `t.plus` after forgetting to `D(ℬ)`. -/
private lemma boundedBelowTargetDenominatorDiagram_obj_mem_t_plus
    (X : K⁺(𝒜)) (j : MorphismProperty.Under (Qis⁺(𝒜)) ⊤ X) :
    (t.plus : ObjectProperty (D(ℬ)))
      ((MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
        KplusToDplus ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))).obj j) := by
  -- Proof comment: the bounded denominator already lands in `D⁺(ℬ)`, and the inclusion into
  -- `D(ℬ)` records exactly that `t.plus` membership.
  exact
    ((MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
      KplusToDplus).obj j).property

/-- Helper for Lemma 13.15.2: the bounded-below ordinary denominator diagram has a colimit in
`D⁺(ℬ)` exactly when it has one after including `D⁺(ℬ)` into `D(ℬ)`. -/
private lemma boundedBelowTargetDenominatorHasColimit_iff_postcomposeDerivedInclusion
    (X : K⁺(𝒜)) :
    HasColimit
        (MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
          KplusToDplus) ↔
      HasColimit
        (MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
          KplusToDplus ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))) := by
  let P : ObjectProperty (D(ℬ)) := t.plus
  let inclusion : P.FullSubcategory ⥤ D(ℬ) := ObjectProperty.ι P
  let J :
      MorphismProperty.Under (Qis⁺(𝒜)) ⊤ X ⥤ P.FullSubcategory :=
    MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ KplusToDplus
  constructor
  · intro h
    letI : HasColimit J := h
    -- Proof comment: the remaining gap is the forward preservation statement for the inclusion
    -- `D⁺(ℬ) ↪ D(ℬ)` on this exact denominator shape. The reverse created-colimit direction is
    -- now isolated in `boundedBelowTargetDenominatorHasColimit_of_postcomposeDerivedInclusion`.
    sorry
  · intro h
    -- TODO: prove that the chosen ambient colimit point of the postcomposed bounded denominator
    -- diagram lies in `t.plus`, then invoke the created-colimit helper below.
    have hcolimit :
        (t.plus : ObjectProperty (D(ℬ)))
          (colimit
            (MorphismProperty.Under.forget (Qis⁺(𝒜)) ⊤ X ⋙ CategoryTheory.Under.forget X ⋙
              KplusToDplus ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ))))) := by
      -- Proof comment: this is the exact-shape boundedness premise needed for the created-colimit
      -- lift back to `D⁺(ℬ)`. The missing owner theorem is a closure result for
      -- `t.plus` on the exact shape `Qis⁺(𝒜).Under ⊤ X`.
      sorry
    exact
      boundedBelowTargetDenominatorHasColimit_of_postcomposeDerivedInclusion
        (F := F) X h hcolimit

/-- Helper for Lemma 13.15.2: ambient pointwise right-derived existence at `X.obj` is exactly
colimit existence on the ordinary ambient denominator diagram out of `X.obj`. -/
private lemma ambientRightDerivedHasColimit_iff_targetDenominator
    (X : K⁺(𝒜)) :
    HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj ↔
      HasColimit
        (MorphismProperty.Under.forget Qis ⊤ X.obj ⋙ CategoryTheory.Under.forget X.obj ⋙
          KtoD) := by
  let T := targetDenominatorToCostructuredArrow Qis X.obj
  letI : Functor.Final T := targetDenominatorToCostructuredArrow_final Qis X.obj
  -- Proof comment: rewrite the owner-level pointwise right-derived predicate to the ambient
  -- costructured-arrow colimit, then move to ordinary denominators via the final denominator
  -- functor.
  rw [Functor.hasPointwiseRightDerivedFunctorAt_iff (F := KtoD) (L := Qambient) (W := Qis) X.obj]
  simpa [CategoryTheory.Functor.HasPointwiseLeftKanExtensionAt, Qambient,
    targetDenominatorToCostructuredArrow] using
    (Functor.Final.hasColimit_comp_iff T
      (G := CostructuredArrow.proj Qambient (Qambient.obj X.obj) ⋙ KtoD)).symm

/-- Helper for Lemma 13.15.2: ambient pointwise right-derived existence at a bounded-below object
can be tested on the bounded-left full subcategory of the ambient costructured-arrow indexing
category. -/
private lemma ambientRightDerivedHasColimit_iff_boundedAmbientCostructuredArrow
    (X : K⁺(𝒜)) :
    HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj ↔
      HasColimit
        (ObjectProperty.ι (boundedBelowAmbientCostructuredArrowProperty X) ⋙
          CostructuredArrow.proj Qambient (Qambient.obj X.obj) ⋙ KtoD) := by
  let inclusion := ObjectProperty.ι (boundedBelowAmbientCostructuredArrowProperty X)
  let RX := CostructuredArrow.proj Qambient (Qambient.obj X.obj) ⋙ KtoD
  letI : Functor.Final inclusion := boundedBelowAmbientCostructuredArrowInclusionFinal
    (𝒜 := 𝒜) X
  -- Proof comment: pointwise right-derived existence is a colimit on the ambient
  -- costructured-arrow diagram, and the bounded-left full subcategory is already final there.
  rw [Functor.hasPointwiseRightDerivedFunctorAt_iff (F := KtoD) (L := Qambient) (W := Qis) X.obj]
  simpa [CategoryTheory.Functor.HasPointwiseLeftKanExtensionAt, RX] using
    (Functor.Final.hasColimit_comp_iff inclusion (G := RX)).symm

/-- Lemma 13.15.2 (1): for a bounded-below object `X` of `K⁺(𝒜)`, the right derived functor of
`K(𝒜) ⥤ D(ℬ)` is defined at `X.obj` if and only if the right derived functor of
`K⁺(𝒜) ⥤ D⁺(ℬ)` is defined at `X`. -/
@[stacks 05T5]
theorem right_derived_defined_at_iff_bounded_below
    (X : K⁺(𝒜)) :
    HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj ↔
      HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X := by
  -- Proof comment: both source-facing owners reduce to ordinary denominator colimit statements.
  -- The denominator-category comparison is now isolated in
  -- `ambientTargetDenominatorHasColimit_iff_boundedPostcompose`, so the only remaining gap is the
  -- codomain lift between the bounded diagram in `D⁺(ℬ)` and its postcomposition to `D(ℬ)`.
  rw [ambientRightDerivedHasColimit_iff_targetDenominator,
    boundedRightDerivedHasColimit_iff_targetDenominator]
  exact
    (ambientTargetDenominatorHasColimit_iff_boundedPostcompose (F := F) X).trans
      (boundedBelowTargetDenominatorHasColimit_iff_postcomposeDerivedInclusion (F := F) X).symm

-- Proof sketch: the abstract pointwise comparison isomorphism between the ambient and bounded
-- right-derived values is already available to instance search once both pointwise derived values
-- exist; its compatibility with the identity legs is the corresponding simplification lemma.
-- TODO: build the bounded-side cocone on `boundedBelowTargetDenominatorProperty X`, prove it is
-- colimiting by transporting along the bounded pointwise-index equivalence and the final bounded
-- ambient inclusion, then compare that explicit transported cocone with the canonical ambient
-- colimit cocone using `Functor.Final.extendCocone_obj_ι_app'` and
-- `colimit.isoColimitCocone_ι_hom` at the identity bounded stage.
/-- Lemma 13.15.2 (2): when the right-derived values at a bounded-below object `X` are defined in
both settings, there is a canonical isomorphism from the ambient value in `D(ℬ)` to the
underlying object of the bounded-below value in `D⁺(ℬ)`. -/
@[stacks 05T5]
noncomputable def right_derived_value_comparison_iso_bounded_below
    (X : K⁺(𝒜))
    [HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X] :
    -- TODO: construct the bounded colimit cocone whose whiskering to `D(ℬ)` matches the ambient
    -- colimit cocone, then compare the two canonical colimit points by
    -- `rightDerivedValueIsoOfColimitCocone`.
    rightDerivedValue Qis KtoD X.obj ≅
      (rightDerivedValue (Qis⁺(𝒜)) KplusToDplus X).obj := sorry

/-- Helper for Lemma 13.15.2: the canonical right-derived value comparison intertwines the
ambient and bounded-below identity legs. -/
private lemma rightDerivedValueComparisonIso_bounded_below_hleg
    (X : K⁺(𝒜))
    [HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X] :
    -- TODO: after the comparison isomorphism is built from the explicit lifted bounded cocone,
    -- identify its identity leg via `Functor.Final.extendCocone_obj_ι_app'` and
    -- `colimit.isoColimitCocone_ι_hom`.
    rightDerivedValueLeg Qis KtoD (𝟙 X.obj) (MorphismProperty.id_mem Qis X.obj) ≫
        (right_derived_value_comparison_iso_bounded_below F X).hom =
      ((mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F).app X).inv ≫
        (ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))).map
          (rightDerivedValueLeg (Qis⁺(𝒜)) KplusToDplus (𝟙 X)
            (MorphismProperty.id_mem (Qis⁺(𝒜)) X)) := sorry

-- Proof sketch: after transporting the bounded-below identity leg to the ambient right-derived
-- value through the canonical comparison isomorphism from part (2), the computing predicates are
-- the same by direct cancellation of the comparison isomorphisms.
/-- Lemma 13.15.2 (3): a bounded-below object `X` computes the right derived functor of
`K(𝒜) ⥤ D(ℬ)` if and only if it computes the right derived functor of
`K⁺(𝒜) ⥤ D⁺(ℬ)`. -/
@[stacks 05T5]
theorem computes_right_derived_functor_at_iff_bounded_below
    (X : K⁺(𝒜)) :
    ComputesRightDerivedAt KtoD Qis X.obj ↔
      ComputesRightDerivedAt KplusToDplus (Qis⁺(𝒜)) X := by
  constructor
  · intro h
    letI : ComputesRightDerivedAt KtoD Qis X.obj := h
    letI : HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X :=
      (right_derived_defined_at_iff_bounded_below F X).1
        (show HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj from inferInstance)
    exact
      (computes_right_derived_at_iff_of_value_iso F X
        (right_derived_value_comparison_iso_bounded_below F X)
        (rightDerivedValueComparisonIso_bounded_below_hleg F X)).1 h
  · intro h
    letI : ComputesRightDerivedAt KplusToDplus (Qis⁺(𝒜)) X := h
    letI : HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj :=
      (right_derived_defined_at_iff_bounded_below F X).2
        (show HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X from inferInstance)
    exact
      (computes_right_derived_at_iff_of_value_iso F X
        (right_derived_value_comparison_iso_bounded_below F X)
        (rightDerivedValueComparisonIso_bounded_below_hleg F X)).2 h

-- Proof sketch: this is the dual comparison for bounded-above objects, again using the source
-- inclusion localizer and the automatic comparison between the bounded and ambient pointwise
-- derived values.
-- Route correction: the dual subset-theorem shortcut would wrongly require
-- `((HomotopyCategory.minus 𝒜).ι ⋙ KtoD)` to invert all bounded-above quasi-isomorphisms. The
-- actual proof has to compare the ambient and bounded source-denominator indexing categories via
-- the bounded-right full subcategory of `StructuredArrow (Qambient.obj X.obj) Qambient`, and then
-- show that this full subcategory is initial by refining any ambient stage to a literal
-- denominator into `X.obj` and then to a bounded-above denominator via
-- `quasiIso_from_bounded_above_refinement`.
/-- Helper for Lemma 13.15.2: the bounded-above ordinary denominator diagram has a limit in
`D⁻(ℬ)` exactly when it has one after including `D⁻(ℬ)` into `D(ℬ)`. -/
private lemma boundedAboveSourceDenominatorHasLimit_of_postcomposeDerivedInclusion
    (X : K⁻(𝒜))
    (hJ :
      HasLimit
      (MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
        KminusToDminus ⋙ ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ)))))
    (hlimit :
      (t.minus : ObjectProperty (D(ℬ)))
        (limit
          (MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
            KminusToDminus ⋙ ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ)))))) :
    HasLimit
      (MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
        KminusToDminus) := by
  let P : ObjectProperty (D(ℬ)) := t.minus
  let inclusion : P.FullSubcategory ⥤ D(ℬ) := ObjectProperty.ι P
  let J :
      MorphismProperty.Over (Qis⁻(𝒜)) ⊤ X ⥤ P.FullSubcategory :=
    MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ KminusToDminus
  letI : HasLimit (J ⋙ inclusion) := hJ
  letI : CreatesLimit J inclusion :=
    createsLimitFullSubcategoryInclusion J hlimit
  exact hasLimit_of_created J inclusion

/-- Helper for Lemma 13.15.2: every object of the bounded-above ordinary source denominator
diagram is already in `t.minus` after forgetting to `D(ℬ)`. -/
private lemma boundedAboveSourceDenominatorDiagram_obj_mem_t_minus
    (X : K⁻(𝒜)) (j : MorphismProperty.Over (Qis⁻(𝒜)) ⊤ X) :
    (t.minus : ObjectProperty (D(ℬ)))
      ((MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
        KminusToDminus ⋙ ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ)))).obj j) := by
  -- Proof comment: the bounded source denominator already lands in `D⁻(ℬ)`, and the inclusion
  -- into `D(ℬ)` simply forgets that bounded-above structure.
  exact
    ((MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
      KminusToDminus).obj j).property

/-- Helper for Lemma 13.15.2: the bounded-above ordinary denominator diagram has a limit in
`D⁻(ℬ)` exactly when it has one after including `D⁻(ℬ)` into `D(ℬ)`. -/
private lemma boundedAboveSourceDenominatorHasLimit_iff_postcomposeDerivedInclusion
    (X : K⁻(𝒜)) :
    HasLimit
        (MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
          KminusToDminus) ↔
      HasLimit
        (MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
          KminusToDminus ⋙ ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ)))) := by
  let P : ObjectProperty (D(ℬ)) := t.minus
  let inclusion : P.FullSubcategory ⥤ D(ℬ) := ObjectProperty.ι P
  let J :
      MorphismProperty.Over (Qis⁻(𝒜)) ⊤ X ⥤ P.FullSubcategory :=
    MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ KminusToDminus
  constructor
  · intro h
    letI : HasLimit J := h
    -- Proof comment: the unresolved dual gap is the forward preservation statement for the
    -- inclusion `D⁻(ℬ) ↪ D(ℬ)` on this exact source-denominator shape. The reverse created-limit
    -- direction is now isolated in `boundedAboveSourceDenominatorHasLimit_of_postcomposeDerivedInclusion`.
    sorry
  · intro h
    -- TODO: prove that the chosen ambient limit point of the postcomposed bounded source
    -- denominator diagram lies in `t.minus`, then invoke the created-limit helper below.
    have hlimit :
        (t.minus : ObjectProperty (D(ℬ)))
          (limit
            (MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
              KminusToDminus ⋙ ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ))))) := by
      -- Proof comment: dually, this is the exact-shape boundedness premise needed for the
      -- created-limit lift back to `D⁻(ℬ)`. The missing owner theorem is the dual closure
      -- result for `t.minus` on the exact shape `Qis⁻(𝒜).Over ⊤ X`.
      sorry
    exact
      boundedAboveSourceDenominatorHasLimit_of_postcomposeDerivedInclusion
        (F := F) X h hlimit

/-- Helper for Lemma 13.15.2: pointwise left-derived existence for the bounded-above functor is
equivalent to limit existence on the ordinary bounded source-denominator diagram. -/
private lemma boundedLeftDerivedHasLimit_iff_sourceDenominator
    (X : K⁻(𝒜)) :
    HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X ↔
      HasLimit
        (MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
          KminusToDminus) := by
  let T := sourceDenominatorToStructuredArrow (Qis⁻(𝒜)) X
  letI : Functor.Initial T := sourceDenominatorToStructuredArrow_initial (Qis⁻(𝒜)) X
  -- Proof comment: the dual bounded owner rewrite now follows from the canonical bounded
  -- calculus-of-fractions instances imported from Situation 13.15.1.
  rw [Functor.hasPointwiseLeftDerivedFunctorAt_iff
    (F := KminusToDminus) (L := (Qis⁻(𝒜)).Q) (W := Qis⁻(𝒜)) X]
  simpa [CategoryTheory.Functor.HasPointwiseRightKanExtensionAt,
    sourceDenominatorToStructuredArrow] using
    (Functor.Initial.hasLimit_comp_iff T
      (G := StructuredArrow.proj ((Qis⁻(𝒜)).Q.obj X) (Qis⁻(𝒜)).Q ⋙ KminusToDminus)).symm

/-- Helper for Lemma 13.15.2: after restricting the ambient source-denominator category to bounded
sources and using the denominator-category equivalence, ambient limit existence is equivalent to
limit existence on the bounded source-denominator diagram after including `D⁻(ℬ)` into `D(ℬ)`. -/
private lemma ambientSourceDenominatorHasLimit_iff_boundedPostcompose
    (X : K⁻(𝒜)) :
    HasLimit
        (MorphismProperty.Over.forget Qis ⊤ X.obj ⋙ CategoryTheory.Over.forget X.obj ⋙ KtoD) ↔
      HasLimit
        (MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
          KminusToDminus ⋙ ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ)))) := by
  let P := boundedAboveSourceDenominatorProperty X
  let inclusion := ObjectProperty.ι P
  let Jambient :
      MorphismProperty.Over Qis ⊤ X.obj ⥤ D(ℬ) :=
    MorphismProperty.Over.forget Qis ⊤ X.obj ⋙ CategoryTheory.Over.forget X.obj ⋙ KtoD
  let Jrestricted : P.FullSubcategory ⥤ D(ℬ) := inclusion ⋙ Jambient
  let E := boundedAboveSourceDenominatorEquivalence X
  let Jbounded :
      MorphismProperty.Over (Qis⁻(𝒜)) ⊤ X ⥤ D(ℬ) :=
    MorphismProperty.Over.forget (Qis⁻(𝒜)) ⊤ X ⋙ CategoryTheory.Over.forget X ⋙
      KminusToDminus ⋙ ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ)))
  letI : Functor.Initial inclusion := boundedAboveSourceDenominatorInclusionInitial X
  -- Proof comment: dually, pass from the ambient ordinary source denominator diagram to the
  -- bounded-source initial full subcategory, replace it by the equivalent bounded denominator
  -- category, and then rewrite the diagram by the canonical comparison iso.
  calc
    HasLimit Jambient
        ↔ HasLimit (inclusion ⋙ Jambient) := by
          simpa [Jambient, inclusion, Jrestricted] using
            (Functor.Initial.hasLimit_comp_iff inclusion (G := Jambient)).symm
    _ ↔ HasLimit (E.functor ⋙ Jrestricted) := by
          simpa [E, Jrestricted] using
            (hasLimit_equivalence_comp_iff (e := E) (F := Jrestricted)).symm
    _ ↔ HasLimit Jbounded := by
          simpa [E, Jrestricted, Jbounded] using
            hasLimit_iff_of_iso (boundedAboveSourceDenominatorDiagramIso (F := F) X)

/-- Helper for Lemma 13.15.2: ambient pointwise left-derived existence at `X.obj` is exactly
limit existence on the ordinary ambient source-denominator diagram into `X.obj`. -/
private lemma ambientLeftDerivedHasLimit_iff_sourceDenominator
    (X : K⁻(𝒜)) :
    HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj ↔
      HasLimit
        (MorphismProperty.Over.forget Qis ⊤ X.obj ⋙ CategoryTheory.Over.forget X.obj ⋙
          KtoD) := by
  let T := sourceDenominatorToStructuredArrow Qis X.obj
  letI : Functor.Initial T := sourceDenominatorToStructuredArrow_initial Qis X.obj
  -- Proof comment: rewrite the owner-level pointwise left-derived predicate to the ambient
  -- structured-arrow limit, then move to ordinary denominators via the initial denominator
  -- functor.
  rw [Functor.hasPointwiseLeftDerivedFunctorAt_iff (F := KtoD) (L := Qambient) (W := Qis) X.obj]
  simpa [CategoryTheory.Functor.HasPointwiseRightKanExtensionAt, Qambient,
    sourceDenominatorToStructuredArrow] using
    (Functor.Initial.hasLimit_comp_iff T
      (G := StructuredArrow.proj (Qambient.obj X.obj) Qambient ⋙ KtoD)).symm

/-- Helper for Lemma 13.15.2: ambient pointwise left-derived existence at a bounded-above object
can be tested on the bounded-right full subcategory of the ambient structured-arrow indexing
category. -/
private lemma ambientLeftDerivedHasLimit_iff_boundedAmbientStructuredArrow
    (X : K⁻(𝒜)) :
    HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj ↔
      HasLimit
        (ObjectProperty.ι (boundedAboveAmbientStructuredArrowProperty X) ⋙
          StructuredArrow.proj (Qambient.obj X.obj) Qambient ⋙ KtoD) := by
  let inclusion := ObjectProperty.ι (boundedAboveAmbientStructuredArrowProperty X)
  let LX := StructuredArrow.proj (Qambient.obj X.obj) Qambient ⋙ KtoD
  letI : Functor.Initial inclusion :=
    boundedAboveAmbientStructuredArrowInclusionInitial (𝒜 := 𝒜) X
  -- Proof comment: dually, pointwise left-derived existence is a limit on the ambient
  -- structured-arrow diagram, and the bounded-right full subcategory is already initial there.
  rw [Functor.hasPointwiseLeftDerivedFunctorAt_iff (F := KtoD) (L := Qambient) (W := Qis) X.obj]
  simpa [CategoryTheory.Functor.HasPointwiseRightKanExtensionAt, LX] using
    (Functor.Initial.hasLimit_comp_iff inclusion (G := LX)).symm

/-- Lemma 13.15.2 (4): for a bounded-above object `X` of `K⁻(𝒜)`, the left derived functor of
`K(𝒜) ⥤ D(ℬ)` is defined at `X.obj` if and only if the left derived functor of
`K⁻(𝒜) ⥤ D⁻(ℬ)` is defined at `X`. -/
@[stacks 05T5]
theorem left_derived_defined_at_iff_bounded_above
    (X : K⁻(𝒜)) :
    HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj ↔
      HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X := by
  -- Proof comment: both source-facing owners now reduce to ordinary source-denominator limit
  -- statements. The only remaining gap is the codomain lift between the bounded diagram in
  -- `D⁻(ℬ)` and its postcomposition to `D(ℬ)`.
  rw [ambientLeftDerivedHasLimit_iff_sourceDenominator,
    boundedLeftDerivedHasLimit_iff_sourceDenominator]
  exact
    (ambientSourceDenominatorHasLimit_iff_boundedPostcompose (F := F) X).trans
      (boundedAboveSourceDenominatorHasLimit_iff_postcomposeDerivedInclusion (F := F) X).symm

-- Proof sketch: the left-derived value comparison is again supplied by the abstract instance
-- search once both pointwise left-derived values exist, and the projection formula is its
-- defining normalization.
-- TODO: construct the dual bounded-source cone on `boundedAboveSourceDenominatorProperty X`,
-- show it is limiting by transporting across the bounded pointwise-index equivalence and the
-- initial bounded ambient inclusion, and then compare the transported cone with the canonical
-- ambient limit cone using `Functor.Initial.extendCone_obj_π_app'` and
-- `limit.isoLimitCone_inv_π` at the identity bounded stage.
/-- Lemma 13.15.2 (5): when the left-derived values at a bounded-above object `X` are defined in
both settings, there is a canonical isomorphism from the ambient value in `D(ℬ)` to the
underlying object of the bounded-above value in `D⁻(ℬ)`. -/
@[stacks 05T5]
noncomputable def left_derived_value_comparison_iso_bounded_above
    (X : K⁻(𝒜))
    [HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X] :
    -- TODO: construct the dual bounded limiting cone whose image in `D(ℬ)` is the ambient
    -- limiting cone, then compare the two canonical limit points by
    -- `leftDerivedValueIsoOfLimitCone`.
    leftDerivedValue Qis KtoD X.obj ≅
      (leftDerivedValue (Qis⁻(𝒜)) KminusToDminus X).obj := sorry

/-- Helper for Lemma 13.15.2: the canonical left-derived value comparison intertwines the
bounded-above and ambient identity projections. -/
private lemma leftDerivedValueComparisonIso_bounded_above_hprojection
    (X : K⁻(𝒜))
    [HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X] :
    -- TODO: once the comparison isomorphism comes from the explicit lifted bounded cone,
    -- rewrite its identity projection using `Functor.Initial.extendCone_obj_π_app'` and
    -- `limit.isoLimitCone_inv_π`.
    (left_derived_value_comparison_iso_bounded_above F X).hom ≫
        (ObjectProperty.ι (t.minus : ObjectProperty (D(ℬ)))).map
          (leftDerivedValueProjection (Qis⁻(𝒜)) KminusToDminus (𝟙 X)
            (MorphismProperty.id_mem (Qis⁻(𝒜)) X)) ≫
        ((mapBoundedAboveHomotopyCategoryToDerivedAboveCompιIso F).app X).hom =
      leftDerivedValueProjection Qis KtoD (𝟙 X.obj) (MorphismProperty.id_mem Qis X.obj) := sorry

-- Proof sketch: transport the bounded-above identity projection to the ambient left-derived
-- value using the comparison isomorphism from part (5), and cancel the resulting comparison
-- isomorphisms.
/-- Lemma 13.15.2 (6): a bounded-above object `X` computes the left derived functor of
`K(𝒜) ⥤ D(ℬ)` if and only if it computes the left derived functor of
`K⁻(𝒜) ⥤ D⁻(ℬ)`. -/
@[stacks 05T5]
theorem computes_left_derived_functor_at_iff_bounded_above
    (X : K⁻(𝒜)) :
    ComputesLeftDerivedAt KtoD Qis X.obj ↔
      ComputesLeftDerivedAt KminusToDminus (Qis⁻(𝒜)) X := by
  constructor
  · intro h
    letI : ComputesLeftDerivedAt KtoD Qis X.obj := h
    letI : HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X :=
      (left_derived_defined_at_iff_bounded_above F X).1
        (show HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj from inferInstance)
    exact
      (computes_left_derived_at_iff_of_value_iso F X
        (left_derived_value_comparison_iso_bounded_above F X)
        (leftDerivedValueComparisonIso_bounded_above_hprojection F X)).1 h
  · intro h
    letI : ComputesLeftDerivedAt KminusToDminus (Qis⁻(𝒜)) X := h
    letI : HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj :=
      (left_derived_defined_at_iff_bounded_above F X).2
        (show HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X from inferInstance)
    exact
      (computes_left_derived_at_iff_of_value_iso F X
        (left_derived_value_comparison_iso_bounded_above F X)
        (leftDerivedValueComparisonIso_bounded_above_hprojection F X)).2 h

end

end CategoryTheory
