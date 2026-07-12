import Mathlib
import StacksProject_2024.Chap04.Lemma_4_35_2
import StacksProject_2024.Chap08.Lemma_8_12_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits CategoryTheory.MorphismProperty Bicategory
open scoped Bicategory

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-
Domain-style sampling for Lemma 8.12.7:
- primary domain: localized pushforward of a fibred category along a functor, with the groupoid
  structure read from the fibers of the canonical projection to `D`.
- inspected owner-level declarations:
  `Functor.pushforwardProjection`,
  `Functor.pushforwardProjection_isFibered`,
  `isFibredInGroupoids_of_isFibered_and_fiber_groupoid`,
  `MorphismProperty.Localization.exists_rightFraction`.
- best owner abstraction: the canonical owner predicate
  `IsFibredInGroupoids (u.pushforwardProjection p)`.
- primitive data: the canonical projection `u.pushforwardProjection p` and the already-canonical
  fibred structure from Lemma `8.12.6`, which itself is built from pullbacks, equalizers, and
  preservation of those two limit shapes.
- derived API: the source-facing theorem below and the derived typeclass instance.

Source/core/bridge triage:
- `source-facing`: `pushforwardProjection_isFibredInGroupoids`.
- `core/canonical`: `IsFibredInGroupoids`, `Functor.IsFibered`, and the fiberwise groupoid
  criterion from Chapter 4.
- `bridge/view`: the private fiberwise groupoid helper, whose proof uses the right-fraction
  presentation of morphisms in the localization but introduces no parallel pushforward owner. -/

namespace Functor

open scoped Functor

variable (u : C ⥤ D) (p : S ⥤ C)

/-- Helper for Lemma 8.12.7: a right fraction whose numerator also belongs to the
pushforward fraction system maps to an isomorphism in the localized pushforward category. -/
private lemma rightFractionMap_isIso_of_numerator_mem
    {X Y : u ₚₚ p} (ρ : (u.pushforwardFractions p).RightFraction X Y)
    (hf : u.pushforwardFractions p ρ.f) :
    IsIso (ρ.map (u.pushforwardFractions p).Q
      (Localization.inverts (u.pushforwardFractions p).Q (u.pushforwardFractions p))) := by
  -- The denominator is inverted by definition of a right fraction, and the extra hypothesis says
  -- the numerator is inverted as well, so the displayed composite is an isomorphism.
  have hsIso : IsIso ((u.pushforwardFractions p).Q.map ρ.s) :=
    Localization.inverts (u.pushforwardFractions p).Q (u.pushforwardFractions p) ρ.s ρ.hs
  have hfIso : IsIso ((u.pushforwardFractions p).Q.map ρ.f) :=
    Localization.inverts (u.pushforwardFractions p).Q (u.pushforwardFractions p) ρ.f hf
  dsimp [MorphismProperty.RightFraction.map]
  infer_instance

/-- Helper for Lemma 8.12.7: a localized morphism is an isomorphism when a right-fraction
representative between source charts has numerator in the inverted class. -/
private lemma localizedHom_isIso_of_rightFraction_numerator_mem
    {X Y : u ₚ p}
    (ψ : X ⟶ Y)
    {A B : u ₚₚ p}
    (eX : ((u.pushforwardFractions p).Q).obj A ≅ X)
    (eY : ((u.pushforwardFractions p).Q).obj B ≅ Y)
    (ρ : (u.pushforwardFractions p).RightFraction A B)
    (hρ :
      eX.hom ≫ ψ ≫ eY.inv =
        ρ.map ((u.pushforwardFractions p).Q)
          (Localization.inverts ((u.pushforwardFractions p).Q)
            (u.pushforwardFractions p)))
    (hf : u.pushforwardFractions p ρ.f) :
    IsIso ψ := by
  let Q := (u.pushforwardFractions p).Q
  let θ :=
    ρ.map Q (Localization.inverts Q (u.pushforwardFractions p))
  -- The represented conjugate of `ψ` is an isomorphism because both numerator and denominator are
  -- inverted; conjugating back along the object-preimage isomorphisms preserves being an iso.
  have hθ : IsIso θ :=
    rightFractionMap_isIso_of_numerator_mem (u := u) (p := p) ρ hf
  have hψ : ψ = eX.inv ≫ θ ≫ eY.hom := by
    calc
      ψ = (𝟙 X) ≫ ψ ≫ (𝟙 Y) := by simp
      _ = (eX.inv ≫ eX.hom) ≫ ψ ≫ (eY.inv ≫ eY.hom) := by
            simp
      _ = eX.inv ≫ (eX.hom ≫ ψ ≫ eY.inv) ≫ eY.hom := by
            simp [Category.assoc]
      _ = eX.inv ≫ θ ≫ eY.hom := by
            rw [hρ]
  rw [hψ]
  infer_instance

variable [IsFibredInGroupoids p]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

omit [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan u]
  [PreservesLimitsOfShape WalkingParallelPair u] in
/-- Helper for Lemma 8.12.7: once the source projection of a morphism is an identity transport,
the morphism belongs to the pushforward fraction system. -/
private lemma pushforwardFractions_of_sourceProjection_map_eq
    {A B : u ₚₚ p} (k : A ⟶ B)
    {hV : A.fst.left = B.fst.left}
    (hk : (pushforwardSourceProjection u p).map k = eqToHom hV) :
    u.pushforwardFractions p k := by
  -- The first component gives verticality, and every `S`-morphism is strongly cartesian because
  -- `p` is fibred in groupoids.
  constructor
  · have hkSource : k.fst.left = eqToHom hV := by
      simpa [pushforwardSourceProjection] using hk
    exact ⟨hV, hkSource⟩
  · exact (inferInstance : IsFibredInGroupoids p).isStronglyCartesian_map k.snd

/-- Helper for Lemma 8.12.7: every object in a fiber has a source chart whose literal
`D`-component is the fiber object. -/
private lemma pushforwardProjectionFiber_sourceChart
    (V : D) (X : (u.pushforwardProjection p).Fiber V) :
    ∃ (A : u ₚₚ p)
      (eX : ((u.pushforwardFractions p).Q).obj A ≅ X.1)
      (hA : A.fst.left = V),
        (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).inv ≫
            (u.pushforwardProjection p).map eX.hom =
          eqToHom hA ≫ eqToHom X.2.symm := by
  classical
  let F := u.pushforwardProjection p
  let Q := (u.pushforwardFractions p).Q
  let Y₀ := Q.objPreimage X.1
  let eY : Q.obj Y₀ ≅ X.1 := Q.objObjPreimageIso X.1
  let sourceBase : V ⟶ Y₀.fst.left :=
    eqToHom X.2.symm ≫ F.map eY.inv
  let A := pushforwardSourcePrecomposeObj (u := u) (p := p) Y₀ sourceBase
  let α := pushforwardSourcePrecomposeHom (u := u) (p := p) Y₀ sourceBase
  have hA : A.fst.left = V := rfl
  -- The precomposition base arrow is a composite of isomorphisms, so the strongly cartesian
  -- source-precomposition morphism is itself an isomorphism and can be transported through `Q`.
  let sourceBaseIso : V ≅ Y₀.fst.left :=
    eqToIso X.2.symm ≪≫ (F.mapIso eY).symm
  have hsourceBase : sourceBase = sourceBaseIso.hom := by
    simp [sourceBase, sourceBaseIso, F, eY]
  have hsourceIso : IsIso sourceBase := by
    rw [hsourceBase]
    infer_instance
  have hαcart :
      (pushforwardSourceProjection u p).IsStronglyCartesian sourceBase α :=
    pushforwardSource_precompose_isStronglyCartesian (u := u) (p := p) Y₀ sourceBase
  letI : IsIso sourceBase := hsourceIso
  letI : (pushforwardSourceProjection u p).IsStronglyCartesian sourceBase α := hαcart
  have hαiso : IsIso α :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso
      (pushforwardSourceProjection u p) sourceBase α
  letI : IsIso α := hαiso
  let eX : Q.obj A ≅ X.1 := Q.mapIso (asIso α) ≪≫ eY
  refine ⟨A, eX, hA, ?_⟩
  let baseA := pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A
  have hlift :
      F.IsHomLift (baseA.hom ≫ eqToHom X.2.symm) eX.hom := by
    -- This is exactly the transported precomposition lift, rewritten in the local names chosen
    -- above so the later source-chart equation can use the canonical `baseA`.
    simpa [F, Q, Y₀, eY, sourceBase, A, α, eX, baseA, Iso.trans_hom] using
      (pushforwardProjection_precompose_toIsHomLift_transported
        (u := u) (p := p) X.1 (eqToHom X.2.symm))
  have hmap : F.map eX.hom = baseA.hom ≫ eqToHom X.2.symm := by
    letI : F.IsHomLift (baseA.hom ≫ eqToHom X.2.symm) eX.hom := hlift
    simpa [F] using
      (IsHomLift.fac' F (baseA.hom ≫ eqToHom X.2.symm) eX.hom)
  -- Precompose by the inverse comparison chart; the chart cancels and leaves the fiber-base
  -- transport of `X`.
  change baseA.inv ≫ F.map eX.hom = eqToHom hA ≫ eqToHom X.2.symm
  rw [hmap]
  simp

/-- Helper for Lemma 8.12.7: the equality transports introduced by source charts and a fiber
morphism cancel to the endpoint transport. -/
private lemma eqToHom_sourceChartedHom_transport
    {A X Y B V : D} (hA : A = V) (hX : X = V) (hY : Y = V) (hB : B = V) :
    (eqToHom hA ≫ eqToHom hX.symm) ≫
        (eqToHom hX ≫ 𝟙 V ≫ eqToHom hY.symm) ≫
          (eqToHom hY ≫ eqToHom hB.symm) =
      eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm := by
  -- Reduce all endpoint identifications to reflexivity; only identity maps remain.
  cases hA
  cases hX
  cases hY
  cases hB
  simp

/-- Helper for Lemma 8.12.7: a source-chart transport composite followed by its reverse is the
identity. -/
private lemma eqToHom_sourceChart_inverse
    {A Y V : D} (hA : A = V) (hY : Y = V) :
    (eqToHom hA ≫ eqToHom hY.symm) ≫ (eqToHom hY ≫ eqToHom hA.symm) = 𝟙 A := by
  -- Reduce both endpoint identifications to reflexivity.
  cases hA
  cases hY
  simp

omit [IsFibredInGroupoids p] [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan u]
  [PreservesLimitsOfShape WalkingParallelPair u] in
/-- Helper for Lemma 8.12.7: conjugating a fiber morphism by normalized source charts has
identity base map between the literal source objects. -/
private lemma pushforwardProjectionFiber_sourceChartedHom_base
    (V : D) {X Y : (u.pushforwardProjection p).Fiber V} (φ : X ⟶ Y)
    {A B : u ₚₚ p}
    (eX : ((u.pushforwardFractions p).Q).obj A ≅ X.1)
    (eY : ((u.pushforwardFractions p).Q).obj B ≅ Y.1)
    (hA : A.fst.left = V) (hB : B.fst.left = V)
    (hX :
      (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).inv ≫
          (u.pushforwardProjection p).map eX.hom =
        eqToHom hA ≫ eqToHom X.2.symm)
    (hY :
      (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).inv ≫
          (u.pushforwardProjection p).map eY.hom =
        eqToHom hB ≫ eqToHom Y.2.symm) :
    (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).inv ≫
        (u.pushforwardProjection p).map (eX.hom ≫ φ.1 ≫ eY.inv) ≫
          (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom =
      eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm := by
  let F := u.pushforwardProjection p
  have hφlift : F.IsHomLift (𝟙 V) φ.1 := φ.2
  letI : F.IsHomLift (𝟙 V) φ.1 := hφlift
  -- The fiber morphism lies over the identity of `V`; record this in the same transport normal
  -- form as the two source charts.
  have hφ : F.map φ.1 = eqToHom X.2 ≫ 𝟙 V ≫ eqToHom Y.2.symm := by
    simpa [F] using (IsHomLift.fac' F (𝟙 V) φ.1)
  have hYinv : F.map eY.inv ≫ (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom =
      eqToHom Y.2 ≫ eqToHom hB.symm := by
    let baseB := pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B
    change F.map eY.inv ≫ baseB.hom = eqToHom Y.2 ≫ eqToHom hB.symm
    let chartY : B.fst.left ≅ F.obj Y.1 := baseB.symm ≪≫ F.mapIso eY
    have hchartY : chartY.hom = eqToHom hB ≫ eqToHom Y.2.symm := by
      simpa [chartY, F, baseB] using hY
    -- The inverse of the chart equation is now just the inverse map of the bundled composite iso.
    have hleft : chartY.hom ≫ (F.map eY.inv ≫ baseB.hom) = 𝟙 B.fst.left := by
      simpa [chartY, F, baseB, Category.assoc] using chartY.hom_inv_id
    have hright : chartY.hom ≫ (eqToHom Y.2 ≫ eqToHom hB.symm) = 𝟙 B.fst.left := by
      rw [hchartY]
      exact eqToHom_sourceChart_inverse hB Y.2
    exact (cancel_epi chartY.hom).1 (hleft.trans hright.symm)
  -- Expand the projection of the conjugated morphism and substitute the three normalized base
  -- equations; the remaining transports cancel.
  calc
    (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).inv ≫
        F.map (eX.hom ≫ φ.1 ≫ eY.inv) ≫
          (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom
        = ((pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).inv ≫ F.map eX.hom) ≫
            F.map φ.1 ≫ (F.map eY.inv ≫
              (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom) := by
          rw [Functor.map_comp F eX.hom (φ.1 ≫ eY.inv),
            Functor.map_comp F φ.1 eY.inv]
          simp only [Category.assoc]
    _ = (eqToHom hA ≫ eqToHom X.2.symm) ≫
            (eqToHom X.2 ≫ 𝟙 V ≫ eqToHom Y.2.symm) ≫
              (eqToHom Y.2 ≫ eqToHom hB.symm) := by
          rw [hX, hφ, hYinv]
          rfl
    _ = eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm := by
          simpa only [Category.assoc] using
            eqToHom_sourceChartedHom_transport hA X.2 Y.2 hB

/-- Helper for Lemma 8.12.7: a right-fraction representative of a morphism whose charted base
map is the identity has numerator in the pushforward fraction system. -/
private lemma rightFraction_numerator_mem_of_charted_base
    {V : D} {A B : u ₚₚ p}
    (hA : A.fst.left = V) (hB : B.fst.left = V)
    (ψ : ((u.pushforwardFractions p).Q).obj A ⟶ ((u.pushforwardFractions p).Q).obj B)
    (hψ :
      (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).inv ≫
          (u.pushforwardProjection p).map ψ ≫
            (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom =
        eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm)
    (ρ : (u.pushforwardFractions p).RightFraction A B)
    (hρ :
      ψ =
        ρ.map ((u.pushforwardFractions p).Q)
          (Localization.inverts ((u.pushforwardFractions p).Q)
            (u.pushforwardFractions p))) :
    u.pushforwardFractions p ρ.f := by
  let Q := (u.pushforwardFractions p).Q
  let F := u.pushforwardProjection p
  let chart :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj ρ.X') ⟶
        (pushforwardSourceProjection u p).obj ρ.X' :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj ρ.X')).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) ρ.X').hom
  let chartA :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj A) ⟶
        (pushforwardSourceProjection u p).obj A :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj A)).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).hom
  let chartB :
      pushforwardProjectionStrictObj (u := u) (p := p) (Q.obj B) ⟶
        (pushforwardSourceProjection u p).obj B :=
    ((pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj B)).symm ≪≫
      pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom
  let Fs := pushforwardProjectionStrict u p
  have hρnum : Q.map ρ.s ≫ ψ = Q.map ρ.f := by
    -- Clear the right-fraction denominator after replacing `ψ` by its chosen roof.
    calc
      Q.map ρ.s ≫ ψ =
          Q.map ρ.s ≫
            ρ.map Q (Localization.inverts Q (u.pushforwardFractions p)) := by
            rw [hρ]
      _ = Q.map ρ.f := by
            simp [Q]
  have hs :
      Fs.map (Q.map ρ.s) ≫ chartA =
        chart ≫ (pushforwardSourceProjection u p).map ρ.s := by
    -- Endpoint chart naturality reads `Q.map ρ.s` as the source projection of `ρ.s`.
    simpa [Q, Fs, chart, chartA] using
      pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
        (u := u) (p := p) (k := ρ.s)
  have hf :
      Fs.map (Q.map ρ.f) ≫ chartB =
        chart ≫ (pushforwardSourceProjection u p).map ρ.f := by
    -- The same endpoint chart naturality applies to the numerator.
    simpa [Q, Fs, chart, chartB] using
      pushforwardProjectionIsoComma_fraction_source_chart_endpoints_exact
        (u := u) (p := p) (k := ρ.f)
  have hψchart :
      Fs.map ψ ≫ chartB =
        chartA ≫ eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm := by
    -- Rewrite the strict projection of `ψ` through the localization comparison charts, then use
    -- the assumed fiber-base equation.
    let baseA := pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A
    let baseB := pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B
    let strictA := pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj A)
    let strictB := pushforwardProjectionStrictObjIso (u := u) (p := p) (Q.obj B)
    have hbase :
        F.map ψ ≫ baseB.hom =
          baseA.hom ≫ (eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm) := by
      calc
        F.map ψ ≫ baseB.hom =
            baseA.hom ≫ (baseA.inv ≫ F.map ψ ≫ baseB.hom) := by
              rw [← Category.assoc, baseA.hom_inv_id]
              simp only [Category.id_comp]
        _ = baseA.hom ≫ (eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm) := by
              exact congrArg (fun k ↦ baseA.hom ≫ k) hψ
    have hstrict :
        F.map ψ ≫ strictB.hom = strictA.hom ≫ Fs.map ψ := by
      simpa [F, Fs, strictA, strictB] using
        pushforwardProjectionStrictIso_naturality (u := u) (p := p) ψ
    have hchartA_cancel : strictA.hom ≫ chartA = baseA.hom := by
      simpa [strictA, chartA, baseA] using
        pushforwardProjectionStrict_obj_Q_obj_chart_cancel (u := u) (p := p) A
    have hchartB_cancel : strictB.hom ≫ chartB = baseB.hom := by
      simpa [strictB, chartB, baseB] using
        pushforwardProjectionStrict_obj_Q_obj_chart_cancel (u := u) (p := p) B
    apply (cancel_epi strictA.hom).1
    calc
      strictA.hom ≫ (Fs.map ψ ≫ chartB) =
          (strictA.hom ≫ Fs.map ψ) ≫ chartB := by
            simp only [Category.assoc]
      _ = (F.map ψ ≫ strictB.hom) ≫ chartB := by
            rw [← hstrict]
      _ = F.map ψ ≫ baseB.hom := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ F.map ψ ≫ k) hchartB_cancel
      _ = baseA.hom ≫ (eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm) := hbase
      _ = strictA.hom ≫ (chartA ≫ eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm) := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm)
                hchartA_cancel.symm
  have hchart :
      chart ≫ (pushforwardSourceProjection u p).map ρ.f =
        chart ≫ (pushforwardSourceProjection u p).map ρ.s ≫
          (eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm) := by
    -- Push the denominator-cleared equality through strict endpoint charts and substitute the
    -- charted base equation for `ψ`.
    calc
      chart ≫ (pushforwardSourceProjection u p).map ρ.f =
          Fs.map (Q.map ρ.f) ≫ chartB := by
            simpa using hf.symm
      _ = Fs.map (Q.map ρ.s ≫ ψ) ≫ chartB := by
            rw [hρnum]
      _ = Fs.map (Q.map ρ.s) ≫ (Fs.map ψ ≫ chartB) := by
            simp [Functor.map_comp, Category.assoc]
      _ =
          Fs.map (Q.map ρ.s) ≫
            (chartA ≫ eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm) := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ Fs.map (Q.map ρ.s) ≫ k) hψchart
      _ =
          (chart ≫ (pushforwardSourceProjection u p).map ρ.s) ≫
            eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ k ≫ eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm)
                hs
      _ =
          chart ≫ (pushforwardSourceProjection u p).map ρ.s ≫
            (eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm) := by
            simp [Category.assoc]
  have hmap :
      (pushforwardSourceProjection u p).map ρ.f =
        (pushforwardSourceProjection u p).map ρ.s ≫
          (eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm) := by
    -- The common source chart is an isomorphism, so it can be cancelled.
    have hchartAssoc :
        chart ≫ (pushforwardSourceProjection u p).map ρ.f =
          chart ≫ ((pushforwardSourceProjection u p).map ρ.s ≫
            (eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm)) := by
      simpa [Category.assoc] using hchart
    exact (cancel_epi chart).1 hchartAssoc
  have hsleft : (pushforwardSourceProjection u p).map ρ.s = ρ.s.fst.left := by
    rfl
  have hsmem :
      (pushforwardSourceProjection u p).map ρ.s = eqToHom ρ.hs.1.choose := by
    -- The denominator is already in the fraction system, so its source projection is an identity
    -- transport.
    simpa [pushforwardSourceProjection] using ρ.hs.1.choose_spec
  have htarget :
      (pushforwardSourceProjection u p).map ρ.f =
        eqToHom (ρ.hs.1.choose.trans hA) ≫ 𝟙 V ≫ eqToHom hB.symm := by
    rw [hmap, hsmem]
    simp
  -- Convert the identity-transport source projection into membership of the fraction system.
  have htargetEqToHom :
      (pushforwardSourceProjection u p).map ρ.f =
        eqToHom ((ρ.hs.1.choose.trans hA).trans hB.symm) := by
    simpa [Category.assoc] using htarget
  exact
    pushforwardFractions_of_sourceProjection_map_eq
      (u := u) (p := p) ρ.f
      (hV := (ρ.hs.1.choose.trans hA).trans hB.symm) htargetEqToHom

/-- Helper for Lemma 8.12.7: a fiber morphism admits source charts and a right-fraction
representative whose numerator belongs to the pushforward fraction system. -/
private lemma pushforwardProjectionFiber_exists_rightFraction_numerator_mem
    (V : D) {X Y : (u.pushforwardProjection p).Fiber V} (φ : X ⟶ Y) :
    ∃ (A B : u ₚₚ p)
      (eX : ((u.pushforwardFractions p).Q).obj A ≅ X.1)
      (eY : ((u.pushforwardFractions p).Q).obj B ≅ Y.1)
      (ρ : (u.pushforwardFractions p).RightFraction A B),
        eX.hom ≫ φ.1 ≫ eY.inv =
          ρ.map ((u.pushforwardFractions p).Q)
            (Localization.inverts ((u.pushforwardFractions p).Q)
              (u.pushforwardFractions p)) ∧
        u.pushforwardFractions p ρ.f := by
  let Q := (u.pushforwardFractions p).Q
  -- Route correction: choose normalized source charts over the literal fiber base before taking
  -- a right-fraction representative, so the numerator verticality is a source-side identity.
  obtain ⟨A, eX, hA, hX⟩ :=
    pushforwardProjectionFiber_sourceChart (u := u) (p := p) V X
  obtain ⟨B, eY, hB, hY⟩ :=
    pushforwardProjectionFiber_sourceChart (u := u) (p := p) V Y
  let ψ : Q.obj A ⟶ Q.obj B := eX.hom ≫ φ.1 ≫ eY.inv
  obtain ⟨ρ, hρ⟩ := Localization.exists_rightFraction Q (u.pushforwardFractions p) ψ
  have hψ :
      (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) A).inv ≫
          (u.pushforwardProjection p).map ψ ≫
            (pushforwardProjection_obj_Q_obj_base (u := u) (p := p) B).hom =
        eqToHom hA ≫ 𝟙 V ≫ eqToHom hB.symm := by
    -- The fiber equation for `φ` becomes the identity after the two source-chart rewrites.
    simpa [ψ] using
      pushforwardProjectionFiber_sourceChartedHom_base
        (u := u) (p := p) V φ eX eY hA hB hX hY
  have hf : u.pushforwardFractions p ρ.f :=
    rightFraction_numerator_mem_of_charted_base
      (u := u) (p := p) hA hB ψ hψ ρ hρ
  exact ⟨A, B, eX, eY, ρ, hρ, hf⟩

/-- Helper for Lemma 8.12.7: the underlying localized morphism of a fiber morphism is an
isomorphism. -/
private lemma pushforwardProjectionFiber_underlying_hom_isIso
    (V : D) {X Y : (u.pushforwardProjection p).Fiber V} (φ : X ⟶ Y) :
    IsIso φ.1 := by
  classical
  obtain ⟨A, B, eX, eY, ρ, hρ, hf⟩ :=
    pushforwardProjectionFiber_exists_rightFraction_numerator_mem (u := u) (p := p) V φ
  -- Once the normalized numerator is in the fraction system, the represented roof is an
  -- isomorphism and so is the original morphism after conjugating by the source charts.
  exact
    localizedHom_isIso_of_rightFraction_numerator_mem
      (u := u) (p := p) φ.1 eX eY ρ hρ hf

omit [IsFibredInGroupoids p] [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan u]
  [PreservesLimitsOfShape WalkingParallelPair u] in
/-- Helper for Lemma 8.12.7: a morphism in a fiber category is an isomorphism once its
underlying morphism is an isomorphism in the total category. -/
private lemma fiberHom_isIso_of_underlying_isIso
    {F : S ⥤ C} {V : C} {X Y : F.Fiber V} (φ : X ⟶ Y)
    [IsIso φ.1] :
    IsIso φ := by
  let hφlift : F.IsHomLift (𝟙 V) φ.1 := φ.2
  letI : F.IsHomLift (𝟙 V) φ.1 := hφlift
  let e := asIso φ.1
  have hinv : F.IsHomLift (𝟙 V) e.inv := by
    simpa [e] using (IsHomLift.lift_id_inv_isIso (p := F) V φ.1)
  -- The inverse of the underlying vertical isomorphism is again vertical, so it defines the
  -- inverse morphism in the fiber.
  refine ⟨?_⟩
  refine ⟨⟨e.inv, hinv⟩, ?_, ?_⟩
  · apply Functor.Fiber.hom_ext
    change φ.1 ≫ e.inv = 𝟙 X.1
    simp [e]
  · apply Functor.Fiber.hom_ext
    change e.inv ≫ φ.1 = 𝟙 Y.1
    simp [e]

-- Proof sketch: Lemma `8.12.6` gives that the localized projection is fibred. To upgrade from
-- fibred to fibred in groupoids, use Lemma `4.35.2`: it is enough to show that every fiber of the
-- localized projection is a groupoid. A morphism in a fiber of the localization is represented by
-- a right fraction in `u_{pp} S`. Its denominator already belongs to the fraction property, and
-- the fiber condition forces the numerator to be vertical over `D`; because `p` is fibred in
-- groupoids, that vertical numerator is also strongly cartesian, hence belongs to the same
-- fraction property and becomes invertible after localization.
/-- Helper for Lemma 8.12.7: every morphism in a fiber of the localized pushforward projection
is an isomorphism. -/
private theorem pushforwardProjectionFiber_hom_isIso
    (V : D) {X Y : (u.pushforwardProjection p).Fiber V} (φ : X ⟶ Y) :
    IsIso φ := by
  -- First prove the underlying morphism in the localized total category is invertible.
  letI : IsIso φ.1 := pushforwardProjectionFiber_underlying_hom_isIso (u := u) (p := p) V φ
  -- Package that underlying inverse as the inverse in the fiber category.
  exact fiberHom_isIso_of_underlying_isIso φ

/-- Helper for Lemma 8.12.7: the fiberwise isomorphism criterion packages each fiber as a
groupoid. -/
private theorem pushforwardProjectionFiber_isGroupoid
    (V : D) :
    IsGroupoid ((u.pushforwardProjection p).Fiber V) := by
  -- The previous helper proves every morphism in this fiber is an isomorphism, which is exactly
  -- the groupoid structure required by the Chapter 4 criterion.
  exact { all_isIso := pushforwardProjectionFiber_hom_isIso u p V }

/-- Helper for Lemma 8.12.7: each fiber of the localized pushforward projection is a
groupoid. -/
private instance pushforwardProjection_fiber_isGroupoid
    (V : D) :
    IsGroupoid ((u.pushforwardProjection p).Fiber V) :=
  pushforwardProjectionFiber_isGroupoid u p V

/-- Chap08 Lemma 8 12 7: with notation and assumptions as in Lemma `8.12.6`, if `p : S ⥤ C` is fibred in
groupoids, then the localized category `u ₚ p` is fibred in groupoids over `D` via its canonical
projection `u.pushforwardProjection p`. -/
@[stacks 04WH]
theorem pushforwardProjection_isFibredInGroupoids
    : IsFibredInGroupoids (u.pushforwardProjection p) := by
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (u.pushforwardProjection p) (pushforwardProjection_isFibered u p) ?_
  intro V
  exact pushforwardProjectionFiber_isGroupoid u p V

/-- Instance form for Lemma 8.12.7: the localized pushforward projection is fibred in
groupoids. -/
instance
    : IsFibredInGroupoids (u.pushforwardProjection p) :=
  pushforwardProjection_isFibredInGroupoids u p

end Functor

end

end CategoryTheory
