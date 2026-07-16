import stacks_proof.stacks_project.Chap08.Lemma_8_12_8.PushforwardUnit

open CategoryTheory
open CategoryTheory.Limits
open scoped FibredCategoryOver
open scoped Functor

universe u v

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{v} C] [Category.{v} D]

section Pushforward

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.8: the source-base map from a prelocalized pushforward object to the
image under `u` of its object in `X`. -/
abbrev pushforwardUnitSourceBaseMap
    (X : FibredCategoryOver C) (A : u ₚₚ X.p) :
    A.fst.left ⟶ u.obj (X.p.obj A.snd) :=
  A.fst.hom ≫ u.map A.iso.hom

/-- Helper for Lemma 8.12.8: the prelocalized chart from a source object to the corresponding
unit object of the localized pushforward. -/
abbrev pushforwardUnitSourcePrelocalizedChart
    (X : FibredCategoryOver C) (A : u ₚₚ X.p) :
    A ⟶ (pushforwardFibredCategoryUnitPrelocalized u X).obj A.snd :=
  { fst :=
      { left := pushforwardUnitSourceBaseMap u X A
        right := A.iso.hom
        w := by
          simp [pushforwardUnitSourceBaseMap, pushforwardFibredCategoryUnitPrelocalized] }
    snd := 𝟙 A.snd
    w := by
      simp [pushforwardFibredCategoryUnitPrelocalized] }

/-- Helper for Lemma 8.12.8: the localized source chart from `Q.obj A` to the unit object
associated to `A.snd`. -/
noncomputable abbrev pushforwardUnitSourceChart
    (X : FibredCategoryOver C) (A : u ₚₚ X.p) :
    (u.pushforwardFractions X.p).Q.obj A ⟶
      (pushforwardFibredCategoryUnit u X).obj A.snd :=
  (u.pushforwardFractions X.p).Q.map
    (pushforwardUnitSourcePrelocalizedChart u X A)

/-- Helper for Lemma 8.12.8: the prelocalized source chart factors through the literal
source-precomposition chart of the unit object. -/
private theorem pushforwardUnitSourcePrelocalizedChart_eq_fraction_comp_precompose
    (X : FibredCategoryOver C) (A : u ₚₚ X.p) :
    let unitA := (pushforwardFibredCategoryUnitPrelocalized u X).obj A.snd
    let sourceBase := pushforwardUnitSourceBaseMap u X A
    let delta : A ⟶
        Functor.pushforwardSourcePrecomposeObj (u := u) (p := X.p) unitA sourceBase :=
      { fst :=
          { left := 𝟙 A.fst.left
            right := A.iso.hom
            w := by
              simp [unitA, sourceBase, pushforwardUnitSourceBaseMap,
                pushforwardFibredCategoryUnitPrelocalized] }
        snd := 𝟙 A.snd
        w := by
          simp [unitA, pushforwardFibredCategoryUnitPrelocalized,
            Functor.pushforwardSourcePrecomposeObj] }
    pushforwardUnitSourcePrelocalizedChart u X A =
      delta ≫
        Functor.pushforwardSourcePrecomposeHom (u := u) (p := X.p) unitA sourceBase := by
  -- The chart is the denominator identifying `A` with the source-precomposed unit, followed by
  -- the universal source-precomposition arrow.
  dsimp
  apply CategoricalPullback.hom_ext
  · apply CategoryTheory.Comma.hom_ext
    · simp [pushforwardUnitSourceBaseMap, pushforwardFibredCategoryUnitPrelocalized,
        Functor.pushforwardSourcePrecomposeObj, Functor.pushforwardSourcePrecomposeHom]
    · simp [pushforwardUnitSourceBaseMap, pushforwardFibredCategoryUnitPrelocalized,
        Functor.pushforwardSourcePrecomposeObj, Functor.pushforwardSourcePrecomposeHom]
  · simp [pushforwardUnitSourcePrelocalizedChart,
      pushforwardUnitSourceBaseMap, pushforwardFibredCategoryUnitPrelocalized,
      Functor.pushforwardSourcePrecomposeObj, Functor.pushforwardSourcePrecomposeHom]

/-- Helper for Lemma 8.12.8: the denominator part of the source chart lies in the pushforward
fraction system. -/
private theorem pushforwardUnitSourcePrelocalizedChart_delta_mem
    (X : FibredCategoryOver C) (A : u ₚₚ X.p) :
    let unitA := (pushforwardFibredCategoryUnitPrelocalized u X).obj A.snd
    let sourceBase := pushforwardUnitSourceBaseMap u X A
    let delta : A ⟶
        Functor.pushforwardSourcePrecomposeObj (u := u) (p := X.p) unitA sourceBase :=
      { fst :=
          { left := 𝟙 A.fst.left
            right := A.iso.hom
            w := by
              simp [unitA, sourceBase, pushforwardUnitSourceBaseMap,
                pushforwardFibredCategoryUnitPrelocalized] }
        snd := 𝟙 A.snd
        w := by
          simp [unitA, pushforwardFibredCategoryUnitPrelocalized,
            Functor.pushforwardSourcePrecomposeObj] }
    u.pushforwardFractions X.p delta := by
  -- The first component is an identity, and the second component is an identity, hence strongly
  -- cartesian over its projection.
  dsimp
  constructor
  · exact ⟨rfl, rfl⟩
  · infer_instance

/-- Helper for Lemma 8.12.8: the localized source chart projects to its canonical source-base
map. -/
private theorem pushforwardUnitSourceChart_projection_map
    (X : FibredCategoryOver C) (A : u ₚₚ X.p) :
    (FibredCategoryOver.pushforward u X).p.map (pushforwardUnitSourceChart u X A) =
      pushforwardUnitSourceBaseMap u X A := by
  -- The projection of `Q.map` is computed by the construction-lift factorization, and the
  -- prelocalized chart has left component exactly the source-base map.
  simpa [FibredCategoryOver.pushforward_p, pushforwardUnitSourceChart,
    pushforwardUnitSourcePrelocalizedChart, pushforwardUnitSourceBaseMap,
    Functor.pushforwardSourceProjection, pushforwardFibredCategoryUnitPrelocalized] using
    Functor.pushforwardProjection_fac_naturality (u := u) (p := X.p)
      (pushforwardUnitSourcePrelocalizedChart u X A)

/-- Helper for Lemma 8.12.8: source charts are natural with respect to prelocalized source
morphisms. -/
theorem pushforwardUnitSourcePrelocalizedChart_naturality
    (X : FibredCategoryOver C) {A B : u ₚₚ X.p} (f : A ⟶ B) :
    f ≫ pushforwardUnitSourcePrelocalizedChart u X B =
      pushforwardUnitSourcePrelocalizedChart u X A ≫
        (pushforwardFibredCategoryUnitPrelocalized u X).map f.snd := by
  -- Naturality is checked before localization on the comma component and on the `X`-component.
  apply CategoricalPullback.hom_ext
  · apply CategoryTheory.Comma.hom_ext
    · have hleft :
          f.fst.left ≫ B.fst.hom ≫ u.map B.iso.hom =
            A.fst.hom ≫ u.map A.iso.hom ≫ u.map (X.p.map f.snd) := by
        calc
          f.fst.left ≫ B.fst.hom ≫ u.map B.iso.hom =
              A.fst.hom ≫ u.map f.fst.right ≫ u.map B.iso.hom := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ u.map B.iso.hom) f.fst.w
          _ = A.fst.hom ≫ u.map (f.fst.right ≫ B.iso.hom) := by
                simp [Functor.map_comp]
          _ = A.fst.hom ≫ u.map (A.iso.hom ≫ X.p.map f.snd) := by
                simpa using congrArg (fun k ↦ A.fst.hom ≫ u.map k) f.w
          _ = A.fst.hom ≫ u.map A.iso.hom ≫ u.map (X.p.map f.snd) := by
                simp [Functor.map_comp]
      simpa [pushforwardUnitSourcePrelocalizedChart, pushforwardUnitSourceBaseMap,
        pushforwardFibredCategoryUnitPrelocalized, Category.assoc] using hleft
    · have hright :
          f.fst.right ≫ B.iso.hom = A.iso.hom ≫ X.p.map f.snd := by
        simpa using f.w
      simpa [pushforwardUnitSourcePrelocalizedChart, pushforwardUnitSourceBaseMap,
        pushforwardFibredCategoryUnitPrelocalized, Category.assoc] using hright
  · simp [pushforwardUnitSourcePrelocalizedChart, pushforwardFibredCategoryUnitPrelocalized]

/-- Helper for Lemma 8.12.8: localized source charts are natural with respect to prelocalized
source morphisms. -/
private theorem pushforwardUnitSourceChart_naturality
    (X : FibredCategoryOver C) {A B : u ₚₚ X.p} (f : A ⟶ B) :
    (u.pushforwardFractions X.p).Q.map f ≫ pushforwardUnitSourceChart u X B =
      pushforwardUnitSourceChart u X A ≫
        (pushforwardFibredCategoryUnit u X).map f.snd := by
  -- Apply the localization functor to the prelocalized naturality square.
  simpa [pushforwardUnitSourceChart, pushforwardFibredCategoryUnit, Functor.map_comp] using
    congrArg (fun k ↦ (u.pushforwardFractions X.p).Q.map k)
      (pushforwardUnitSourcePrelocalizedChart_naturality u X f)

/-- Helper for Lemma 8.12.8: the localized source chart is strongly cartesian over its owner
projection map. -/
theorem pushforwardUnitSourceChart_isStronglyCartesian_owner
    (X : FibredCategoryOver C) (A : u ₚₚ X.p) :
    (FibredCategoryOver.pushforward u X).p.IsStronglyCartesian
      ((FibredCategoryOver.pushforward u X).p.map (pushforwardUnitSourceChart u X A))
      (pushforwardUnitSourceChart u X A) := by
  -- Factor the chart into an inverted denominator followed by the known source-precomposition
  -- chart, compose the strong-cartesian facts, and rebase to the explicit source-base map.
  let pU := (FibredCategoryOver.pushforward u X).p
  let Q := (u.pushforwardFractions X.p).Q
  let unitA := (pushforwardFibredCategoryUnitPrelocalized u X).obj A.snd
  let sourceBase := pushforwardUnitSourceBaseMap u X A
  let delta : A ⟶
      Functor.pushforwardSourcePrecomposeObj (u := u) (p := X.p) unitA sourceBase :=
    { fst :=
        { left := 𝟙 A.fst.left
          right := A.iso.hom
          w := by
            simp [unitA, sourceBase, pushforwardUnitSourceBaseMap,
              pushforwardFibredCategoryUnitPrelocalized] }
      snd := 𝟙 A.snd
      w := by
        simp [unitA, pushforwardFibredCategoryUnitPrelocalized,
          Functor.pushforwardSourcePrecomposeObj] }
  let alpha :=
    Functor.pushforwardSourcePrecomposeHom (u := u) (p := X.p) unitA sourceBase
  have hdeltaMem : u.pushforwardFractions X.p delta := by
    simpa [unitA, sourceBase, delta] using
      pushforwardUnitSourcePrelocalizedChart_delta_mem u X A
  have hdeltaIso : IsIso (Q.map delta) :=
    Localization.inverts Q (u.pushforwardFractions X.p) delta hdeltaMem
  have hdeltaLift : pU.IsHomLift (pU.map (Q.map delta)) (Q.map delta) := by
    infer_instance
  letI : IsIso (Q.map delta) := hdeltaIso
  letI : pU.IsHomLift (pU.map (Q.map delta)) (Q.map delta) := hdeltaLift
  have hdeltaStrong :
      pU.IsStronglyCartesian (pU.map (Q.map delta)) (Q.map delta) :=
    @Functor.IsStronglyCartesian.of_isIso _ _ _ _ pU _ _ _ _
      (pU.map (Q.map delta)) (Q.map delta) hdeltaLift hdeltaIso
  have halphaStrong :
      pU.IsStronglyCartesian sourceBase (Q.map alpha) := by
    simpa [pU, Q, FibredCategoryOver.pushforward_p, alpha, sourceBase] using
      pushforwardProjection_Q_sourcePrecompose_isStronglyCartesian
        (u := u) (p := X.p) unitA sourceBase
  letI : pU.IsStronglyCartesian (pU.map (Q.map delta)) (Q.map delta) := hdeltaStrong
  letI : pU.IsStronglyCartesian sourceBase (Q.map alpha) := halphaStrong
  have hcomp :
      pU.IsStronglyCartesian (pU.map (Q.map delta) ≫ sourceBase)
        (Q.map delta ≫ Q.map alpha) := by
    exact @Functor.IsStronglyCartesian.comp _ _ _ _ pU _ _ _ _ _ _ _ _ _ _ hdeltaStrong
      halphaStrong
  have hchart :
      Q.map delta ≫ Q.map alpha = pushforwardUnitSourceChart u X A := by
    rw [← Functor.map_comp]
    rw [← pushforwardUnitSourcePrelocalizedChart_eq_fraction_comp_precompose (u := u) X A]
  have hcompChart :
      pU.IsStronglyCartesian (pU.map (Q.map delta) ≫ sourceBase)
        (pushforwardUnitSourceChart u X A) := by
    exact hchart ▸ hcomp
  letI :
      pU.IsStronglyCartesian (pU.map (Q.map delta) ≫ sourceBase)
        (pushforwardUnitSourceChart u X A) :=
    hcompChart
  change pU.IsStronglyCartesian (pU.map (pushforwardUnitSourceChart u X A))
    (pushforwardUnitSourceChart u X A)
  exact @BasedFunctor.isStronglyCartesian_rebase_over_target_eq _ _ _ _ pU
    A.fst.left (u.obj (X.p.obj A.snd)) _ _ rfl
    (pU.map (Q.map delta) ≫ sourceBase)
    (pushforwardUnitSourceChart u X A) hcompChart

/-- Helper for Lemma 8.12.8: an admissible pushforward morphism sends each localized source
chart to a strongly cartesian morphism in the target fibred category. -/
private theorem pushforwardUnitSourceChart_map_isStronglyCartesian
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom)
    (A : u ₚₚ X.p) :
    Y.p.IsStronglyCartesian
      (Y.p.map (G.obj.obj.map (pushforwardUnitSourceChart u X A)))
      (G.obj.obj.map (pushforwardUnitSourceChart u X A)) := by
  -- The object `G` is a morphism of fibred categories, so it preserves the owner-form
  -- strong-cartesianness of the source chart.
  exact G.obj.property (pushforwardUnitSourceChart u X A)
    (pushforwardUnitSourceChart_isStronglyCartesian_owner u X A)

/-- Helper for Lemma 8.12.8: the image of a localized source chart is a hom-lift over its
projected base morphism. -/
private theorem pushforwardUnitSourceChart_map_isHomLift
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom)
    (A : u ₚₚ X.p) :
    Y.p.IsHomLift
      (Y.p.map (G.obj.obj.map (pushforwardUnitSourceChart u X A)))
      (G.obj.obj.map (pushforwardUnitSourceChart u X A)) := by
  -- The hom-lift field is part of the strongly cartesian structure just proved for the mapped
  -- chart.
  let hcart := pushforwardUnitSourceChart_map_isStronglyCartesian u X Y G A
  letI :
      Y.p.IsStronglyCartesian
        (Y.p.map (G.obj.obj.map (pushforwardUnitSourceChart u X A)))
        (G.obj.obj.map (pushforwardUnitSourceChart u X A)) := hcart
  infer_instance

/-- Helper for Lemma 8.12.8: mapped localized source charts are natural with respect to
prelocalized source morphisms. -/
theorem pushforwardUnitSourceChart_map_naturality
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (G :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom)
    {A B : u ₚₚ X.p} (f : A ⟶ B) :
    G.obj.obj.map ((u.pushforwardFractions X.p).Q.map f) ≫
        G.obj.obj.map (pushforwardUnitSourceChart u X B) =
      G.obj.obj.map (pushforwardUnitSourceChart u X A) ≫
        G.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd) := by
  -- Apply the admissible functor to the localized source-chart naturality square.
  calc
    G.obj.obj.map ((u.pushforwardFractions X.p).Q.map f) ≫
        G.obj.obj.map (pushforwardUnitSourceChart u X B) =
      G.obj.obj.map (((u.pushforwardFractions X.p).Q.map f) ≫
        pushforwardUnitSourceChart u X B) := by
        rw [G.obj.obj.map_comp]
    _ = G.obj.obj.map (pushforwardUnitSourceChart u X A ≫
        (pushforwardFibredCategoryUnit u X).map f.snd) := by
        exact congrArg (fun k ↦ G.obj.obj.map k)
          (pushforwardUnitSourceChart_naturality u X f)
    _ = G.obj.obj.map (pushforwardUnitSourceChart u X A) ≫
        G.obj.obj.map ((pushforwardFibredCategoryUnit u X).map f.snd) := by
        rw [G.obj.obj.map_comp]

/-- Helper for Lemma 8.12.8: the source chart of a unit object is the identity after
localization. -/
theorem pushforwardUnitSourceChart_unit
    (X : FibredCategoryOver C) (x : X.S) :
    pushforwardUnitSourceChart u X ((pushforwardFibredCategoryUnitPrelocalized u X).obj x) =
      𝟙 ((pushforwardFibredCategoryUnit u X).obj x) := by
  -- Before localization the chart has identity components on the unit object, so applying `Q`
  -- gives the identity morphism of the localized unit object.
  have hpre :
      pushforwardUnitSourcePrelocalizedChart u X
          ((pushforwardFibredCategoryUnitPrelocalized u X).obj x) =
        𝟙 ((pushforwardFibredCategoryUnitPrelocalized u X).obj x) := by
    apply CategoricalPullback.hom_ext
    · apply CategoryTheory.Comma.hom_ext
      · simp [pushforwardUnitSourceBaseMap, pushforwardFibredCategoryUnitPrelocalized]
      · simp [pushforwardFibredCategoryUnitPrelocalized]
    · simp [pushforwardFibredCategoryUnitPrelocalized]
  simpa [pushforwardUnitSourceChart, pushforwardFibredCategoryUnit] using
    congrArg (fun k ↦ (u.pushforwardFractions X.p).Q.map k) hpre

end Pushforward

end

end CategoryTheory
