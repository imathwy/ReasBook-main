import StacksProject_2024.Chap08.Lemma_8_12_8.PullbackComparison

open CategoryTheory
open CategoryTheory.Limits
open scoped FibredCategoryOver
open scoped Functor

universe u v uS vS

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{v} C] [Category.{v} D]

section Pushforward

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.8: the lifted pullback comparison is faithful on
morphisms of fibred categories. -/
theorem pushforwardPullbackFibredMorphismLift_faithful
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    (pushforwardPullbackFibredMorphismLift u X Y).Faithful := by
  constructor
  intro G₁ G₂ τ σ hτσ
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply BasedNatTrans.ext
  ext A
  let Q := (u.pushforwardFractions X.p).Q
  let A₀ := Q.objPreimage A
  let chart := pushforwardUnitSourceChart u X A₀
  have hcomp' := congrArg (fun η => η.hom) hτσ
  have hUnit :=
    pushforwardPullbackComparisonFunctorMap_unit_app_eq_of_eq u X Y hcomp' A₀.snd
  have hUnit' :
      τ.hom.hom.app ((pushforwardFibredCategoryUnit u X).obj A₀.snd) =
        σ.hom.hom.app ((pushforwardFibredCategoryUnit u X).obj A₀.snd) := by
    exact hUnit
  have hcartOwner :
      Y.p.IsStronglyCartesian
        (Y.p.map (G₂.obj.obj.map chart)) (G₂.obj.obj.map chart) := by
    exact G₂.obj.property chart (pushforwardUnitSourceChart_isStronglyCartesian_owner u X A₀)
  have hchartLift :
      Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map chart)
        (G₂.obj.obj.map chart) := by
    infer_instance
  have hcart :
      Y.p.IsStronglyCartesian ((FibredCategoryOver.pushforward u X).p.map chart)
        (G₂.obj.obj.map chart) := by
    letI :
        Y.p.IsStronglyCartesian
          (Y.p.map (G₂.obj.obj.map chart)) (G₂.obj.obj.map chart) :=
      hcartOwner
    letI :
        Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map chart)
          (G₂.obj.obj.map chart) :=
      hchartLift
    exact BasedFunctor.isStronglyCartesian_of_external_hom_lift Y.p
      (G₂.obj.obj.map chart)
  have hnatτ := τ.hom.hom.naturality chart
  have hnatσ := σ.hom.hom.naturality chart
  letI :
      Y.p.IsStronglyCartesian ((FibredCategoryOver.pushforward u X).p.map chart)
        (G₂.obj.obj.map chart) :=
    hcart
  have hpre : τ.hom.hom.app (Q.obj A₀) = σ.hom.hom.app (Q.obj A₀) := by
    exact Functor.IsStronglyCartesian.ext Y.p
      ((FibredCategoryOver.pushforward u X).p.map chart)
      (G₂.obj.obj.map chart)
      (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj A₀))) (by
        rw [← hnatτ, ← hnatσ, hUnit'])
  let eA := Q.objObjPreimageIso A
  have hnatτe := τ.hom.hom.naturality eA.hom
  have hnatσe := σ.hom.hom.naturality eA.hom
  haveI : IsIso (G₁.obj.obj.map eA.hom) := by infer_instance
  apply (cancel_epi (G₁.obj.obj.map eA.hom)).1
  calc
    G₁.obj.obj.map eA.hom ≫ τ.hom.hom.app A =
        τ.hom.hom.app (Q.obj A₀) ≫ G₂.obj.obj.map eA.hom := hnatτe
    _ = σ.hom.hom.app (Q.obj A₀) ≫ G₂.obj.obj.map eA.hom := by rw [hpre]
    _ = G₁.obj.obj.map eA.hom ≫ σ.hom.hom.app A := hnatσe.symm

/-- Helper for Lemma 8.12.8: after identifying both first components with the same object, a
pullback morphism over the identity has identity first component. -/
private theorem categoricalPullback_fst_eq_id_of_isHomLift_id
    {S : Type uS} [Category.{vS} S] (p : S ⥤ D)
    {R : C} {a b : CategoricalPullback u p} (φ : a ⟶ b)
    (ha : a.fst = R) (hb : b.fst = R)
    (hφ : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 R) φ) :
    eqToHom ha.symm ≫ φ.fst ≫ eqToHom hb = 𝟙 R := by
  -- The hom-lift equation for the first projection is exactly the desired first component
  -- equality once the endpoint equality proofs are replaced by the supplied ones.
  letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 R) φ := hφ
  have hbase :=
    IsHomLift.fac (CategoricalPullback.π₁ u p) (𝟙 R) φ
  have hdom :
      eqToHom ha.symm =
        eqToHom
          (IsHomLift.domain_eq (CategoricalPullback.π₁ u p) (𝟙 R) φ).symm := by
    congr 1
  have hcod :
      eqToHom hb =
        eqToHom (IsHomLift.codomain_eq (CategoricalPullback.π₁ u p) (𝟙 R) φ) := by
    congr 1
  rw [hdom, hcod]
  exact hbase.symm

/-- Helper for Lemma 8.12.8: any morphism between two comparison objects has the expected
pullback equation on its `Y`-component. -/
private theorem pushforwardPullbackTargetComponent_base
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ : pushforwardPullbackSourceBasedFunctorCategory u X Y}
    (η :
      pushforwardPullbackComparisonFunctorObj u X Y G₁ ⟶
        pushforwardPullbackComparisonFunctorObj u X Y G₂)
    (x : X.S) :
    u.map (𝟙 (X.p.obj x)) ≫
        ((pushforwardPullbackComparisonFunctorObj u X Y G₂).obj x).iso.hom =
      ((pushforwardPullbackComparisonFunctorObj u X Y G₁).obj x).iso.hom ≫
        Y.p.map ((η.app x).snd) := by
  -- The based-natural-transformation condition says the pullback morphism lies over the identity;
  -- after normalizing the first projection, its pullback square is exactly the desired equation.
  have hη :
      (u ᵖ Y).p.IsHomLift (𝟙 (X.p.obj x)) (η.app x) := η.isHomLift' x
  have hπ₁ :
      (η.app x).fst = 𝟙 (X.p.obj x) := by
    letI : (u ᵖ Y).p.IsHomLift (𝟙 (X.p.obj x)) (η.app x) := hη
    simpa [FibredCategoryOver.pullback_p] using
      (IsHomLift.fac' ((u ᵖ Y).p) (𝟙 (X.p.obj x)) (η.app x))
  simpa [hπ₁] using (η.app x).w

/-- Helper for Lemma 8.12.8: the `Y`-component of a comparison morphism is vertical over the
pushforward-unit object. -/
private theorem pushforwardPullbackComparisonComponent_snd_isHomLift
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom}
    (η :
      (pushforwardPullbackFibredMorphismLift u X Y).obj G₁ ⟶
        (pushforwardPullbackFibredMorphismLift u X Y).obj G₂)
    (x : X.S) :
    Y.p.IsHomLift
      (𝟙 ((FibredCategoryOver.pushforward u X).p.obj
        ((pushforwardFibredCategoryUnit u X).obj x)))
      ((η.hom.app x).snd) := by
  -- The pullback equation for the comparison component gives the projected `Y`-map; the
  -- structure isomorphisms normalize to the object equalities supplied by the based functors.
  let unit := (pushforwardFibredCategoryUnit u X).obj x
  have ha :
      Y.p.obj
          (((pushforwardPullbackFibredMorphismLift u X Y).obj G₁).obj.obj x).snd =
        (FibredCategoryOver.pushforward u X).p.obj unit := by
    simpa [unit] using Functor.congr_obj G₁.obj.obj.w unit
  have hb :
      Y.p.obj
          (((pushforwardPullbackFibredMorphismLift u X Y).obj G₂).obj.obj x).snd =
        (FibredCategoryOver.pushforward u X).p.obj unit := by
    simpa [unit] using Functor.congr_obj G₂.obj.obj.w unit
  refine IsHomLift.of_fac' Y.p
    (𝟙 ((FibredCategoryOver.pushforward u X).p.obj unit))
    ((η.hom.app x).snd) ha hb ?_
  have hbase := pushforwardPullbackTargetComponent_base u X Y η.hom x
  let sourceObj :=
    (pushforwardPullbackComparisonFunctorObj u X Y
      (((fibredCategoryOverSubTwoCategory D).hom
        (FibredCategoryOver.pushforward u X) Y).inclusion.obj G₁)).obj x
  let targetObj :=
    (pushforwardPullbackComparisonFunctorObj u X Y
      (((fibredCategoryOverSubTwoCategory D).hom
        (FibredCategoryOver.pushforward u X) Y).inclusion.obj G₂)).obj x
  have hsourceInv : sourceObj.iso.inv = eqToHom ha := by
    simp only [sourceObj, pushforwardPullbackComparisonFunctorObj,
      pushforwardPullbackComparisonSquare,
      CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback_obj_obj_iso_inv,
      eqToIso.inv, eqToHom_app]
    try congr 1
    try apply Subsingleton.elim
  have htargetHom : targetObj.iso.hom = eqToHom hb.symm := by
    simp only [targetObj, pushforwardPullbackComparisonFunctorObj,
      pushforwardPullbackComparisonSquare,
      CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback_obj_obj_iso_hom,
      eqToIso.hom, eqToHom_app]
    try congr 1
    try apply Subsingleton.elim
  have hbase' :
      targetObj.iso.hom =
        sourceObj.iso.hom ≫ Y.p.map (η.hom.app x).snd := by
    have h := hbase
    rw [Functor.map_id, Category.id_comp] at h
    simpa only [sourceObj, targetObj] using h
  have hmap :
      Y.p.map (η.hom.app x).snd = sourceObj.iso.inv ≫ targetObj.iso.hom := by
    have hcancel :
        Y.p.map (η.hom.app x).snd =
          sourceObj.iso.inv ≫ sourceObj.iso.hom ≫
            Y.p.map (η.hom.app x).snd :=
      (Iso.inv_hom_id_assoc sourceObj.iso
        (Y.p.map (η.hom.app x).snd)).symm
    have hrewrite :
        sourceObj.iso.inv ≫ sourceObj.iso.hom ≫
            Y.p.map (η.hom.app x).snd =
          sourceObj.iso.inv ≫ targetObj.iso.hom := by
      rw [← hbase']
      rfl
    exact hcancel.trans hrewrite
  rw [hmap, hsourceInv, htargetHom]
  rw [Category.id_comp]
  congr 1

-- Route correction: fullness is proved after localization, using source charts in `uₚ X`,
-- rather than by constructing a prelocalized natural transformation and descending it later.
/-- Helper for Lemma 8.12.8: a target comparison component factors uniquely through the image of a
localized source chart. -/
private theorem pushforwardPullbackFullChartFactor
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom}
    (η :
      (pushforwardPullbackFibredMorphismLift u X Y).obj G₁ ⟶
        (pushforwardPullbackFibredMorphismLift u X Y).obj G₂)
    (A : u ₚₚ X.p) :
    let Q := (u.pushforwardFractions X.p).Q
    let chart := pushforwardUnitSourceChart u X A
    ∃! χ : G₁.obj.obj.obj (Q.obj A) ⟶ G₂.obj.obj.obj (Q.obj A),
      Y.p.IsHomLift (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj A))) χ ∧
        χ ≫ G₂.obj.obj.map chart =
          G₁.obj.obj.map chart ≫ (η.hom.app A.snd).snd := by
  -- The image of the chart under `G₂` is strongly cartesian; the desired component is the
  -- universal factorization of the composite through the target comparison component.
  let Q := (u.pushforwardFractions X.p).Q
  let chart := pushforwardUnitSourceChart u X A
  have hcartOwner :
      Y.p.IsStronglyCartesian
        (Y.p.map (G₂.obj.obj.map chart)) (G₂.obj.obj.map chart) := by
    exact G₂.obj.property chart (pushforwardUnitSourceChart_isStronglyCartesian_owner u X A)
  have hchartLift :
      Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map chart)
        (G₂.obj.obj.map chart) := by
    infer_instance
  have hcart :
      Y.p.IsStronglyCartesian ((FibredCategoryOver.pushforward u X).p.map chart)
        (G₂.obj.obj.map chart) := by
    letI :
        Y.p.IsStronglyCartesian
          (Y.p.map (G₂.obj.obj.map chart)) (G₂.obj.obj.map chart) :=
      hcartOwner
    letI :
        Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map chart)
          (G₂.obj.obj.map chart) :=
      hchartLift
    exact BasedFunctor.isStronglyCartesian_of_external_hom_lift Y.p
      (G₂.obj.obj.map chart)
  have htargetLift :
      Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map chart)
        (G₁.obj.obj.map chart ≫ (η.hom.app A.snd).snd) := by
    -- First isolate the two hom-lifts which will be composed: the mapped chart for `G₁`, and
    -- the vertical `Y`-component of the comparison morphism at the chart target.
    have hG₁Lift :
        Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map chart)
          (G₁.obj.obj.map chart) := by
      infer_instance
    have hηVertical :
        Y.p.IsHomLift
          (𝟙 ((FibredCategoryOver.pushforward u X).p.obj
            ((pushforwardFibredCategoryUnit u X).obj A.snd)))
          ((η.hom.app A.snd).snd) := by
      exact pushforwardPullbackComparisonComponent_snd_isHomLift u X Y η A.snd
    letI :
        Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map chart)
          (G₁.obj.obj.map chart) :=
      hG₁Lift
    letI :
        Y.p.IsHomLift
          (𝟙 ((FibredCategoryOver.pushforward u X).p.obj
            ((pushforwardFibredCategoryUnit u X).obj A.snd)))
          ((η.hom.app A.snd).snd) :=
      hηVertical
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ Y.p _ _ _ _ _
      ((FibredCategoryOver.pushforward u X).p.map chart)
      (G₁.obj.obj.map chart)
      hG₁Lift
      ((FibredCategoryOver.pushforward u X).p.obj
        ((pushforwardFibredCategoryUnit u X).obj A.snd))
      ((η.hom.app A.snd).snd)
      hηVertical
  letI :
      Y.p.IsStronglyCartesian ((FibredCategoryOver.pushforward u X).p.map chart)
        (G₂.obj.obj.map chart) :=
    hcart
  letI :
      Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map chart)
        (G₁.obj.obj.map chart ≫ (η.hom.app A.snd).snd) :=
    htargetLift
  have hbase :
      (FibredCategoryOver.pushforward u X).p.map chart =
        𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj A)) ≫
          (FibredCategoryOver.pushforward u X).p.map chart := by
    exact (Category.id_comp _).symm
  have huniv :
      ∃! χ : G₁.obj.obj.obj (Q.obj A) ⟶ G₂.obj.obj.obj (Q.obj A),
        Y.p.IsHomLift (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj A))) χ ∧
          χ ≫ G₂.obj.obj.map chart =
            G₁.obj.obj.map chart ≫ (η.hom.app A.snd).snd := by
    exact
      @Functor.IsStronglyCartesian.universal_property _ _ _ _ Y.p
        _ _ _ _
        ((FibredCategoryOver.pushforward u X).p.map chart)
        (G₂.obj.obj.map chart)
        hcart
        _ _
        (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj A)))
        ((FibredCategoryOver.pushforward u X).p.map chart)
        hbase
        (G₁.obj.obj.map chart ≫ (η.hom.app A.snd).snd)
        htargetLift
  obtain ⟨χ, hχ, hχuniq⟩ := huniv
  exact ⟨χ, hχ, fun χ' hχ' ↦ hχuniq χ' hχ'⟩

/-- Helper for Lemma 8.12.8: the chosen factor of a comparison component through a localized
source chart. -/
private noncomputable abbrev pushforwardPullbackChartFactorComponent
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom}
    (η :
      (pushforwardPullbackFibredMorphismLift u X Y).obj G₁ ⟶
        (pushforwardPullbackFibredMorphismLift u X Y).obj G₂)
    (A : u ₚₚ X.p) :
    let Q := (u.pushforwardFractions X.p).Q
    G₁.obj.obj.obj (Q.obj A) ⟶ G₂.obj.obj.obj (Q.obj A) :=
  Classical.choose (pushforwardPullbackFullChartFactor u X Y η A)

/-- Helper for Lemma 8.12.8: the chosen chart factor is vertical and has the defining
factorization through the source chart. -/
private theorem pushforwardPullbackChartFactorComponent_spec
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom}
    (η :
      (pushforwardPullbackFibredMorphismLift u X Y).obj G₁ ⟶
        (pushforwardPullbackFibredMorphismLift u X Y).obj G₂)
    (A : u ₚₚ X.p) :
    let Q := (u.pushforwardFractions X.p).Q
    let chart := pushforwardUnitSourceChart u X A
    Y.p.IsHomLift (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj A)))
        (pushforwardPullbackChartFactorComponent u X Y η A) ∧
      pushforwardPullbackChartFactorComponent u X Y η A ≫ G₂.obj.obj.map chart =
        G₁.obj.obj.map chart ≫ (η.hom.app A.snd).snd := by
  -- The specification is the first component of the `∃!` package used to choose the factor.
  exact (Classical.choose_spec (pushforwardPullbackFullChartFactor u X Y η A)).1

/-- Helper for Lemma 8.12.8: the chosen chart factor is vertical over the identity. -/
private theorem pushforwardPullbackChartFactorComponent_isHomLift
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom}
    (η :
      (pushforwardPullbackFibredMorphismLift u X Y).obj G₁ ⟶
        (pushforwardPullbackFibredMorphismLift u X Y).obj G₂)
    (A : u ₚₚ X.p) :
    let Q := (u.pushforwardFractions X.p).Q
    Y.p.IsHomLift (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj A)))
      (pushforwardPullbackChartFactorComponent u X Y η A) := by
  -- Project the verticality half of the chosen factor specification.
  exact (pushforwardPullbackChartFactorComponent_spec u X Y η A).1

/-- Helper for Lemma 8.12.8: the chosen chart factor has the defining factorization. -/
private theorem pushforwardPullbackChartFactorComponent_fac
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom}
    (η :
      (pushforwardPullbackFibredMorphismLift u X Y).obj G₁ ⟶
        (pushforwardPullbackFibredMorphismLift u X Y).obj G₂)
    (A : u ₚₚ X.p) :
    let chart := pushforwardUnitSourceChart u X A
    pushforwardPullbackChartFactorComponent u X Y η A ≫ G₂.obj.obj.map chart =
      G₁.obj.obj.map chart ≫ (η.hom.app A.snd).snd := by
  -- Project the factorization half of the chosen factor specification.
  exact (pushforwardPullbackChartFactorComponent_spec u X Y η A).2

/-- Helper for Lemma 8.12.8: the chart factor is unique with its verticality and factorization
properties. -/
private theorem pushforwardPullbackChartFactorComponent_unique
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom}
    (η :
      (pushforwardPullbackFibredMorphismLift u X Y).obj G₁ ⟶
        (pushforwardPullbackFibredMorphismLift u X Y).obj G₂)
    (A : u ₚₚ X.p)
    (χ : let Q := (u.pushforwardFractions X.p).Q
      G₁.obj.obj.obj (Q.obj A) ⟶ G₂.obj.obj.obj (Q.obj A))
    (hχ :
      let Q := (u.pushforwardFractions X.p).Q
      let chart := pushforwardUnitSourceChart u X A
      Y.p.IsHomLift (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj A))) χ ∧
        χ ≫ G₂.obj.obj.map chart =
          G₁.obj.obj.map chart ≫ (η.hom.app A.snd).snd) :
    χ = pushforwardPullbackChartFactorComponent u X Y η A := by
  -- The second component of the `∃!` package identifies any other valid factor with the chosen one.
  exact (Classical.choose_spec (pushforwardPullbackFullChartFactor u X Y η A)).2 χ hχ

/-- Helper for Lemma 8.12.8: at a unit-source object, the chosen chart factor is the original
comparison component. -/
private theorem pushforwardPullbackChartFactorComponent_unit
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom}
    (η :
      (pushforwardPullbackFibredMorphismLift u X Y).obj G₁ ⟶
        (pushforwardPullbackFibredMorphismLift u X Y).obj G₂)
    (x : X.S) :
    pushforwardPullbackChartFactorComponent u X Y η
        ((pushforwardFibredCategoryUnitPrelocalized u X).obj x) =
      (η.hom.app x).snd := by
  -- The source chart of a unit object is the identity, so the chart-factor uniqueness principle
  -- identifies the chosen factor with the given comparison component.
  have hvalid :
      let Q := (u.pushforwardFractions X.p).Q
      let chart := pushforwardUnitSourceChart u X
        ((pushforwardFibredCategoryUnitPrelocalized u X).obj x)
      Y.p.IsHomLift (𝟙 ((FibredCategoryOver.pushforward u X).p.obj
        (Q.obj ((pushforwardFibredCategoryUnitPrelocalized u X).obj x))))
          ((η.hom.app x).snd) ∧
        (η.hom.app x).snd ≫ G₂.obj.obj.map chart =
          G₁.obj.obj.map chart ≫
            (η.hom.app ((pushforwardFibredCategoryUnitPrelocalized u X).obj x).snd).snd := by
    constructor
    · exact pushforwardPullbackComparisonComponent_snd_isHomLift u X Y η x
    · have hchart := pushforwardUnitSourceChart_unit u X x
      rw [hchart]
      erw [G₁.obj.obj.map_id, G₂.obj.obj.map_id]
      erw [Category.comp_id, Category.id_comp]
  exact (pushforwardPullbackChartFactorComponent_unique u X Y η
    ((pushforwardFibredCategoryUnitPrelocalized u X).obj x)
    ((η.hom.app x).snd) hvalid).symm

/-- Helper for Lemma 8.12.8: the chosen chart factors are natural on prelocalized source
morphisms after applying the localization functor. -/
private theorem pushforwardPullbackChartFactorComponent_naturality
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    {G₁ G₂ :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom}
    (η :
      (pushforwardPullbackFibredMorphismLift u X Y).obj G₁ ⟶
        (pushforwardPullbackFibredMorphismLift u X Y).obj G₂)
    {A B : u ₚₚ X.p} (f : A ⟶ B) :
    let Q := (u.pushforwardFractions X.p).Q
    G₁.obj.obj.map (Q.map f) ≫
        pushforwardPullbackChartFactorComponent u X Y η B =
      pushforwardPullbackChartFactorComponent u X Y η A ≫
        G₂.obj.obj.map (Q.map f) := by
  -- Both sides lift the same localized base map; postcomposing with the strongly-cartesian
  -- source chart at `B` reduces the comparison to chart-factor definitions and naturality of `η`.
  let Q := (u.pushforwardFractions X.p).Q
  change
    G₁.obj.obj.map (Q.map f) ≫
        pushforwardPullbackChartFactorComponent u X Y η B =
      pushforwardPullbackChartFactorComponent u X Y η A ≫
        G₂.obj.obj.map (Q.map f)
  let chartA := pushforwardUnitSourceChart u X A
  let chartB := pushforwardUnitSourceChart u X B
  let χA := pushforwardPullbackChartFactorComponent u X Y η A
  let χB := pushforwardPullbackChartFactorComponent u X Y η B
  have hleftLift :
      Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map (Q.map f))
        (G₁.obj.obj.map (Q.map f) ≫ χB) := by
    have hmap :
        Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map (Q.map f))
          (G₁.obj.obj.map (Q.map f)) := by
      infer_instance
    have hχB :
        Y.p.IsHomLift (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj B)))
          χB := by
      exact pushforwardPullbackChartFactorComponent_isHomLift u X Y η B
    letI :
        Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map (Q.map f))
          (G₁.obj.obj.map (Q.map f)) :=
      hmap
    letI :
        Y.p.IsHomLift (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj B)))
          χB :=
      hχB
    have hcomp :
        Y.p.IsHomLift (((FibredCategoryOver.pushforward u X).p.map (Q.map f)) ≫ 𝟙 _)
          (G₁.obj.obj.map (Q.map f) ≫ χB) := by
      infer_instance
    rwa [Category.comp_id] at hcomp
  have hrightLift :
      Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map (Q.map f))
        (χA ≫ G₂.obj.obj.map (Q.map f)) := by
    have hχA :
        Y.p.IsHomLift (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj A)))
          χA := by
      exact pushforwardPullbackChartFactorComponent_isHomLift u X Y η A
    have hmap :
        Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map (Q.map f))
          (G₂.obj.obj.map (Q.map f)) := by
      infer_instance
    letI :
        Y.p.IsHomLift (𝟙 ((FibredCategoryOver.pushforward u X).p.obj (Q.obj A)))
          χA :=
      hχA
    letI :
        Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map (Q.map f))
          (G₂.obj.obj.map (Q.map f)) :=
      hmap
    have hcomp :
        Y.p.IsHomLift (𝟙 _ ≫ ((FibredCategoryOver.pushforward u X).p.map (Q.map f)))
          (χA ≫ G₂.obj.obj.map (Q.map f)) := by
      infer_instance
    rwa [Category.id_comp] at hcomp
  have hcartOwner :
      Y.p.IsStronglyCartesian
        (Y.p.map (G₂.obj.obj.map chartB)) (G₂.obj.obj.map chartB) := by
    exact G₂.obj.property chartB (pushforwardUnitSourceChart_isStronglyCartesian_owner u X B)
  have hchartLift :
      Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map chartB)
        (G₂.obj.obj.map chartB) := by
    infer_instance
  have hcart :
      Y.p.IsStronglyCartesian ((FibredCategoryOver.pushforward u X).p.map chartB)
        (G₂.obj.obj.map chartB) := by
    letI :
        Y.p.IsStronglyCartesian
          (Y.p.map (G₂.obj.obj.map chartB)) (G₂.obj.obj.map chartB) :=
      hcartOwner
    letI :
        Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map chartB)
          (G₂.obj.obj.map chartB) :=
      hchartLift
    exact BasedFunctor.isStronglyCartesian_of_external_hom_lift Y.p
      (G₂.obj.obj.map chartB)
  have hηNat :
      G₁.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd) ≫
          (η.hom.app B.snd).snd =
        (η.hom.app A.snd).snd ≫
          G₂.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd) := by
    -- Naturality of the pullback-valued comparison, projected to the `Y`-component.
    exact congrArg CategoricalPullback.Hom.snd (η.hom.naturality f.snd)
  have hηPost :
      G₁.obj.obj.map chartA ≫
          (G₁.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd) ≫
            (η.hom.app B.snd).snd) =
        G₁.obj.obj.map chartA ≫
          ((η.hom.app A.snd).snd ≫
            G₂.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd)) :=
    congrArg (fun k ↦ G₁.obj.obj.map chartA ≫ k) hηNat
  have hηPostLeft :
      (G₁.obj.obj.map chartA ≫
          G₁.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd)) ≫
        (η.hom.app B.snd).snd =
      (G₁.obj.obj.map chartA ≫ (η.hom.app A.snd).snd) ≫
        G₂.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd) :=
    (Category.assoc _ _ _).trans (hηPost.trans (Category.assoc _ _ _).symm)
  have hpost :
      (G₁.obj.obj.map (Q.map f) ≫ χB) ≫ G₂.obj.obj.map chartB =
        (χA ≫ G₂.obj.obj.map (Q.map f)) ≫ G₂.obj.obj.map chartB := by
    -- Normalize both composites to the source-chart square and the naturality square of `η`.
    have hfacA := pushforwardPullbackChartFactorComponent_fac u X Y η A
    have hfacB := pushforwardPullbackChartFactorComponent_fac u X Y η B
    have hnatG₁ := pushforwardUnitSourceChart_map_naturality u X Y G₁ f
    have hnatG₂ := pushforwardUnitSourceChart_map_naturality u X Y G₂ f
    have hfacA' :
        χA ≫ G₂.obj.obj.map chartA =
          G₁.obj.obj.map chartA ≫ (η.hom.app A.snd).snd := by
      exact hfacA
    have hfacB' :
        χB ≫ G₂.obj.obj.map chartB =
          G₁.obj.obj.map chartB ≫ (η.hom.app B.snd).snd := by
      exact hfacB
    have hnatG₁' :
        G₁.obj.obj.map (Q.map f) ≫ G₁.obj.obj.map chartB =
          G₁.obj.obj.map chartA ≫
            G₁.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd) := by
      exact hnatG₁
    have hnatG₂' :
        G₂.obj.obj.map (Q.map f) ≫ G₂.obj.obj.map chartB =
          G₂.obj.obj.map chartA ≫
            G₂.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd) := by
      exact hnatG₂
    let a := G₁.obj.obj.map (Q.map f)
    let bB := G₁.obj.obj.map chartB
    let etaB := (η.hom.app B.snd).snd
    let bA := G₁.obj.obj.map chartA
    let u₁ := G₁.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd)
    let etaA := (η.hom.app A.snd).snd
    let u₂ := G₂.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd)
    let cA := G₂.obj.obj.map chartA
    let d := G₂.obj.obj.map (Q.map f)
    let cB := G₂.obj.obj.map chartB
    exact
      (Category.assoc a χB cB).trans
        ((congrArg (fun k ↦ a ≫ k) hfacB').trans
          (((Category.assoc a bB etaB).symm).trans
            ((congrArg (fun k ↦ k ≫ etaB) hnatG₁').trans
              (hηPostLeft.trans
                ((congrArg (fun k ↦ k ≫ u₂) hfacA'.symm).trans
                  ((Category.assoc χA cA u₂).trans
                    ((congrArg (fun k ↦ χA ≫ k) hnatG₂'.symm).trans
                      (Category.assoc χA d cB).symm)))))))
  letI :
      Y.p.IsStronglyCartesian ((FibredCategoryOver.pushforward u X).p.map chartB)
        (G₂.obj.obj.map chartB) :=
    hcart
  letI :
      Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map (Q.map f))
        (G₁.obj.obj.map (Q.map f) ≫ χB) :=
    hleftLift
  letI :
      Y.p.IsHomLift ((FibredCategoryOver.pushforward u X).p.map (Q.map f))
        (χA ≫ G₂.obj.obj.map (Q.map f)) :=
    hrightLift
  exact Functor.IsStronglyCartesian.ext Y.p
    ((FibredCategoryOver.pushforward u X).p.map chartB)
    (G₂.obj.obj.map chartB)
    ((FibredCategoryOver.pushforward u X).p.map (Q.map f))
    hpost

/-- Helper for Lemma 8.12.8: the lifted pullback comparison is full. -/
theorem pushforwardPullbackFibredMorphismLift_full
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    (pushforwardPullbackFibredMorphismLift u X Y).Full := by
  constructor
  intro G₁ G₂ η
  -- The missing construction is a based natural transformation whose component at a localized
  -- object is obtained from the source chart at a chosen preimage representative.
  -- TODO: construct the preimage component on each localized object by transporting to
  -- `Q.obj (Q.objPreimage A)`, factoring through the source chart using
  -- `pushforwardPullbackTargetComponent_base`, and descend the resulting component by
  -- source-chart naturality.
  let Q := (u.pushforwardFractions X.p).Q
  let W := u.pushforwardFractions X.p
  let F₁pre : u ₚₚ X.p ⥤ Y.S := Q ⋙ G₁.obj.obj.toFunctor
  let F₂pre : u ₚₚ X.p ⥤ Y.S := Q ⋙ G₂.obj.obj.toFunctor
  let τPre : F₁pre ⟶ F₂pre :=
    { app := fun A ↦ pushforwardPullbackChartFactorComponent u X Y η A
      naturality := by
        intro A B f
        exact pushforwardPullbackChartFactorComponent_naturality u X Y η f }
  letI : Localization.Lifting Q W F₁pre G₁.obj.obj.toFunctor :=
    ⟨Iso.refl _⟩
  letI : Localization.Lifting Q W F₂pre G₂.obj.obj.toFunctor :=
    ⟨Iso.refl _⟩
  let τNat : G₁.obj.obj.toFunctor ⟶ G₂.obj.obj.toFunctor :=
    Localization.liftNatTrans Q W F₁pre F₂pre
      G₁.obj.obj.toFunctor G₂.obj.obj.toFunctor τPre
  have τNat_app_Q (A : u ₚₚ X.p) :
      τNat.app (Q.obj A) =
        pushforwardPullbackChartFactorComponent u X Y η A := by
    have h := Localization.liftNatTrans_app Q W F₁pre F₂pre
      G₁.obj.obj.toFunctor G₂.obj.obj.toFunctor τPre A
    have h₁ :
        (Localization.Lifting.iso Q W F₁pre G₁.obj.obj.toFunctor).hom.app A =
          𝟙 _ := rfl
    have h₂ :
        (Localization.Lifting.iso Q W F₂pre G₂.obj.obj.toFunctor).inv.app A =
          𝟙 _ := rfl
    rw [h]
    rw [h₁, h₂, Category.id_comp, Category.comp_id]
  let τBased : G₁.obj.obj ⟶ G₂.obj.obj :=
    { toNatTrans := τNat
      isHomLift' := by
        intro Z
        -- The transported component is a composite of two comparison isomorphisms and the
        -- vertical chart factor; its base composite is `e.inv ≫ e.hom`, hence the identity.
        let e := Q.objObjPreimageIso Z
        let χ := pushforwardPullbackChartFactorComponent u X Y η (Q.objPreimage Z)
        have hInvLift : Y.p.IsHomLift ((u ₚ X).p.map e.inv)
            (G₁.obj.obj.map e.inv) := by
          infer_instance
        have hχLift :
            Y.p.IsHomLift (𝟙 ((u ₚ X).p.obj (Q.obj (Q.objPreimage Z)))) χ := by
          exact pushforwardPullbackChartFactorComponent_isHomLift u X Y η (Q.objPreimage Z)
        have hHomLift : Y.p.IsHomLift ((u ₚ X).p.map e.hom)
            (G₂.obj.obj.map e.hom) := by
          infer_instance
        letI : Y.p.IsHomLift ((u ₚ X).p.map e.inv) (G₁.obj.obj.map e.inv) :=
          hInvLift
        letI : Y.p.IsHomLift (𝟙 ((u ₚ X).p.obj (Q.obj (Q.objPreimage Z)))) χ :=
          hχLift
        letI : Y.p.IsHomLift ((u ₚ X).p.map e.hom) (G₂.obj.obj.map e.hom) :=
          hHomLift
        have hcomp :
            Y.p.IsHomLift (((u ₚ X).p.map e.inv ≫ 𝟙 _) ≫ (u ₚ X).p.map e.hom)
              ((G₁.obj.obj.map e.inv ≫ χ) ≫ G₂.obj.obj.map e.hom) := by
          infer_instance
        rw [Category.comp_id] at hcomp
        have hbase :
            (u ₚ X).p.map e.inv ≫ (u ₚ X).p.map e.hom =
              𝟙 ((u ₚ X).p.obj Z) := by
          simpa [FibredCategoryOver.pushforward_p] using
            pushforwardProjection_map_inv_comp_map (u := u) (p := X.p) e.hom
        rw [hbase] at hcomp
        have happQ : τNat.app (Q.obj (Q.objPreimage Z)) = χ := by
          exact τNat_app_Q (Q.objPreimage Z)
        have happZ :
            τNat.app Z = (G₁.obj.obj.map e.inv ≫ χ) ≫ G₂.obj.obj.map e.hom := by
          have hnat := τNat.naturality e.inv
          have hcancel :
              G₂.obj.obj.map e.inv ≫ G₂.obj.obj.map e.hom =
                𝟙 (G₂.obj.obj.obj Z) := by
            calc
              G₂.obj.obj.map e.inv ≫ G₂.obj.obj.map e.hom =
                  G₂.obj.obj.map (e.inv ≫ e.hom) := by
                    exact (G₂.obj.obj.map_comp e.inv e.hom).symm
              _ = G₂.obj.obj.map (𝟙 Z) := by
                    exact congrArg (fun k ↦ G₂.obj.obj.map k) e.inv_hom_id
              _ = 𝟙 (G₂.obj.obj.obj Z) := by
                    exact G₂.obj.obj.map_id Z
          calc
            τNat.app Z = τNat.app Z ≫ 𝟙 (G₂.obj.obj.obj Z) := by
              exact (Category.comp_id _).symm
            _ = τNat.app Z ≫
                (G₂.obj.obj.map e.inv ≫ G₂.obj.obj.map e.hom) := by
                  rw [hcancel]
            _ = (τNat.app Z ≫ G₂.obj.obj.map e.inv) ≫
                G₂.obj.obj.map e.hom := by
                  exact (Category.assoc _ _ _).symm
            _ = (G₁.obj.obj.map e.inv ≫ τNat.app (Q.obj (Q.objPreimage Z))) ≫
                G₂.obj.obj.map e.hom := by
                  rw [← hnat]
            _ = (G₁.obj.obj.map e.inv ≫ χ) ≫ G₂.obj.obj.map e.hom := by
                  rw [happQ]
        rw [happZ]
        exact hcomp }
  let τ : G₁ ⟶ G₂ := ⟨ObjectProperty.homMk τBased, trivial⟩
  refine ⟨τ, ?mapτ⟩
  -- The lifted natural transformation computes on unit-source objects as the chosen chart
  -- factor, and the unit chart identifies that factor with the original comparison component.
  apply ObjectProperty.hom_ext
  apply BasedNatTrans.ext
  ext x
  apply CategoricalPullback.hom_ext
  · change 𝟙 (X.p.obj x) = (η.hom.app x).fst
    -- The comparison morphism is vertical in the pullback category, so its first projection is
    -- the identity on the base object of `x`.
    have hη : (u ᵖ Y).p.IsHomLift (𝟙 (X.p.obj x)) (η.hom.app x) :=
      η.hom.isHomLift' x
    have hfst : (η.hom.app x).fst = 𝟙 (X.p.obj x) := by
      rw [FibredCategoryOver.pullback_p] at hη
      letI : (CategoricalPullback.π₁ u Y.p).IsHomLift
        (𝟙 (X.p.obj x)) (η.hom.app x) := hη
      exact
        (@IsHomLift.eq_of_isHomLift _ _ _ _ (CategoricalPullback.π₁ u Y.p)
          (((pushforwardPullbackFibredMorphismLift u X Y).obj G₁).obj.obj x)
          (((pushforwardPullbackFibredMorphismLift u X Y).obj G₂).obj.obj x)
          (𝟙 (X.p.obj x)) (η.hom.app x) hη).symm
    exact hfst.symm
  · -- On the second projection, the lifted transformation computes on unit objects as the
    -- chosen chart factor, which was already identified with the original component.
    change
      τNat.app (Q.obj ((pushforwardFibredCategoryUnitPrelocalized u X).obj x)) =
        (η.hom.app x).snd
    rw [τNat_app_Q]
    exact pushforwardPullbackChartFactorComponent_unit u X Y η x
end Pushforward

end

end CategoryTheory
