module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Topology_Munkres_2000.Book.Theorem_75_2.HomotopyPrism

public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicTopology

/-- Helper for Theorem 75.2: reparameterizing a path on `TopCat.I` is continuous. -/
lemma continuous_pathTopCatMap {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) : Continuous (fun t : TopCat.I.{u} ↦ p t.down) := by
  -- Continuity follows from the path and the projection out of `ULift`.
  fun_prop

/-- Helper for Theorem 75.2: the `TopCat` morphism underlying a path, with a transparent
local spelling used by the chain-homotopy interface. -/
def pathTopCatMap' {X : Type u} [TopologicalSpace X] {x y : X} (p : Path x y) :
    TopCat.I.{u} ⟶ TopCat.of X :=
  TopCat.ofHom ⟨fun t ↦ p t.down, continuous_pathTopCatMap p⟩

/-- Helper for Theorem 75.2: the transparent path map sends zero to the source. -/
@[simp]
lemma pathTopCatMap'_zero {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) : pathTopCatMap' p 0 = x := by
  -- Reduce evaluation to the source equation of the original path.
  exact p.source

/-- Helper for Theorem 75.2: the transparent path map sends one to the target. -/
@[simp]
lemma pathTopCatMap'_one {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) : pathTopCatMap' p 1 = y := by
  -- Reduce evaluation to the target equation of the original path.
  exact p.target

/-- Helper for Theorem 75.2: an endpoint-fixed path homotopy remains continuous after
reparameterizing its path coordinate on `TopCat.I`. -/
lemma continuous_pathTopCatHomotopy {X : Type u} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (F : p.Homotopy q) :
    Continuous (fun z : unitInterval × TopCat.I.{u} ↦ F (z.1, z.2.down)) := by
  -- Compose the continuous homotopy with the continuous lifted-coordinate projection.
  fun_prop

/-- Helper for Theorem 75.2: the reparameterized path homotopy starts at its first path. -/
lemma pathTopCatHomotopy_zero {X : Type u} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (F : p.Homotopy q) (t : TopCat.I.{u}) :
    F (0, t.down) = pathTopCatMap' p t := by
  -- Use the time-zero face of the original path homotopy.
  exact F.map_zero_left t.down

/-- Helper for Theorem 75.2: the reparameterized path homotopy ends at its second path. -/
lemma pathTopCatHomotopy_one {X : Type u} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (F : p.Homotopy q) (t : TopCat.I.{u}) :
    F (1, t.down) = pathTopCatMap' q t := by
  -- Use the time-one face of the original path homotopy.
  exact F.map_one_left t.down

/-- Helper for Theorem 75.2: an endpoint-fixed homotopy of paths gives a `TopCat`
homotopy between their transparent interval maps. -/
noncomputable def pathTopCatHomotopy {X : Type u} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (F : p.Homotopy q) :
    TopCat.Homotopy (pathTopCatMap' p) (pathTopCatMap' q) :=
  { toFun := fun z ↦ F (z.1, z.2.down)
    continuous_toFun := continuous_pathTopCatHomotopy F
    map_zero_left := pathTopCatHomotopy_zero F
    map_one_left := pathTopCatHomotopy_one F }

/-- Helper for Theorem 75.2: a path regarded as the corresponding singular one-simplex
under the standard edge equivalence. -/
noncomputable def pathSingularSimplex {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 1)) :=
  TopCat.toSSetObj₁Equiv.symm (pathTopCatMap' p)

/-- Helper for Theorem 75.2: the singular one-simplex associated to a path has boundary
equal to its terminal vertex minus its initial vertex. -/
lemma pathSingularSimplex_boundary {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let SX := TopCat.toSSet.obj (TopCat.of X)
    SX.ιChainComplex (pathSingularSimplex p) ≫
        (SX.chainComplex R).d 1 0 =
      SX.ιChainComplex (TopCat.toSSetObj₀Equiv.symm y) -
        SX.ιChainComplex (TopCat.toSSetObj₀Equiv.symm x) := by
  -- Expand the degree-one simplicial boundary into its two oriented faces.
  dsimp only
  rw [SSet.ιChainComplex_d]
  rw [Fin.sum_univ_two]
  -- Naturality of the path simplex identifies those faces with its endpoints.
  unfold pathSingularSimplex
  rw [TopCat.δ_zero_toSSetObj₁Equiv.symm, TopCat.δ_one_toSSetObj₁Equiv.symm,
    pathTopCatMap'_one, pathTopCatMap'_zero]
  norm_num [sub_eq_add_neg]

/-- Helper for Theorem 75.2: the identity map of the interval represents its canonical
singular one-simplex. -/
noncomputable def intervalIdentitySimplex :
    (TopCat.toSSet.obj TopCat.I.{u}).obj (Opposite.op (SimplexCategory.mk 1)) :=
  TopCat.toSSetObj₁Equiv.symm (𝟙 TopCat.I)

/-- Helper for Theorem 75.2: mapping the interval identity simplex along a path gives
the singular simplex associated to that path. -/
lemma intervalIdentitySimplex_map {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    (TopCat.toSSet.map (pathTopCatMap' p)).app
        (Opposite.op (SimplexCategory.mk 1)) intervalIdentitySimplex =
      pathSingularSimplex p := by
  -- Compare the represented interval maps through the degree-one simplex equivalence.
  apply TopCat.toSSetObj₁Equiv.injective
  rfl

/-- Helper for Theorem 75.2: the singular-chain map induced by a path sends the interval
identity generator to the path generator. -/
lemma ιChainComplex_intervalIdentitySimplex_map {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let I := TopCat.toSSet.obj TopCat.I.{u}
    let SX := TopCat.toSSet.obj (TopCat.of X)
    I.ιChainComplex intervalIdentitySimplex ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (pathTopCatMap' p)) R).f 1 =
      SX.ιChainComplex (pathSingularSimplex p) := by
  -- Use the generator computation for a simplicial chain map and its simplex-level formula.
  dsimp only
  rw [SSet.ι_chainComplexMap_f, intervalIdentitySimplex_map]

/-- Helper for Theorem 75.2: a based loop gives a degree-one singular cycle. -/
lemma pathSingularSimplex_loop_isCycle {X : Type u} [TopologicalSpace X]
    {x₀ : X} (p : Path x₀ x₀) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let SX := TopCat.toSSet.obj (TopCat.of X)
    SX.ιChainComplex (pathSingularSimplex p) ≫
        (SX.chainComplex R).d 1 0 = 0 := by
  -- The two endpoint generators in the boundary formula cancel for a loop.
  dsimp only
  rw [pathSingularSimplex_boundary]
  exact sub_self _

/-- Helper for Theorem 75.2: degree zero is the successor index of degree one in a
chain complex indexed by `ℕ`. -/
lemma chainComplex_next_one : (ComplexShape.down ℕ).next 1 = 0 := by
  -- This is the defining predecessor computation for the chain-complex shape.
  exact ChainComplex.next_nat_succ 0

/-- Helper for Theorem 75.2: the interval generator of a based loop lifted to the
degree-one cycle object. -/
noncomputable def basedLoopCycle {X : Type u} [TopologicalSpace X]
    {x₀ : X} (p : Path x₀ x₀) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    AddCommGrpCat.of (ULift.{u} ℤ) ⟶ K.cycles 1 :=
  let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
    (AddCommGrpCat.of (ULift.{u} ℤ))
  K.liftCycles ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (pathSingularSimplex p)) 0 chainComplex_next_one
    (pathSingularSimplex_loop_isCycle p)

/-- Helper for Theorem 75.2: including the lifted based-loop cycle recovers its
singular one-simplex generator. -/
lemma basedLoopCycle_iCycles {X : Type u} [TopologicalSpace X]
    {x₀ : X} (p : Path x₀ x₀) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    basedLoopCycle p ≫ K.iCycles 1 =
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (pathSingularSimplex p) := by
  -- Apply the computation rule of `liftCycles`.
  dsimp only [basedLoopCycle]
  exact HomologicalComplex.liftCycles_i _ _ _ _ _

/-- Helper for Theorem 75.2: the coefficient morphism representing the first-homology
class of a based loop. -/
noncomputable def basedLoopHomologyCoefficient {X : Type u} [TopologicalSpace X]
    {x₀ : X} (p : Path x₀ x₀) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    AddCommGrpCat.of (ULift.{u} ℤ) ⟶ K.homology 1 :=
  let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
    (AddCommGrpCat.of (ULift.{u} ℤ))
  basedLoopCycle p ≫ K.homologyπ 1

/-- Helper for Theorem 75.2: the element of first homology represented by a based loop. -/
noncomputable def basedLoopHomologyClass {X : Type u} [TopologicalSpace X]
    {x₀ : X} (p : Path x₀ x₀) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    K.homology 1 :=
  let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
    (AddCommGrpCat.of (ULift.{u} ℤ))
  AddCommGrpCat.uliftZMultiplesAddEquiv (K.homology 1)
    (basedLoopHomologyCoefficient p)

/-- Helper for Theorem 75.2: the chain homotopy induced by an endpoint-fixed path
homotopy. -/
noncomputable def pathSingularChainHomotopy {X : Type u} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (F : p.Homotopy q) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    _root_.Homotopy
      (SSet.chainComplexMap (TopCat.toSSet.map (pathTopCatMap' p)) R)
      (SSet.chainComplexMap (TopCat.toSSet.map (pathTopCatMap' q)) R) :=
  (pathTopCatHomotopy F).singularChainComplexFunctorObjMap
    (AddCommGrpCat.of (ULift.{u} ℤ))

/-- Helper for Theorem 75.2: degree one is related to degree zero in the standard
chain-complex shape. -/
lemma chainComplex_rel_one_zero : (ComplexShape.down ℕ).Rel 1 0 := by
  -- The defining relation is `0 + 1 = 1`.
  rfl

/-- Helper for Theorem 75.2: degree two is related to degree one in the standard
chain-complex shape. -/
lemma chainComplex_rel_two_one : (ComplexShape.down ℕ).Rel 2 1 := by
  -- The defining relation is `1 + 1 = 2`.
  rfl

/-- Helper for Theorem 75.2: the degree-one chain-homotopy equation for two
endpoint-fixed homotopic paths, evaluated on the interval generator. -/
lemma pathSingularSimplex_homotopy_comm {X : Type u} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (F : p.Homotopy q) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let I := TopCat.toSSet.obj TopCat.I.{u}
    let SX := TopCat.toSSet.obj (TopCat.of X)
    let C := I.chainComplex R
    let K := SX.chainComplex R
    let H := pathSingularChainHomotopy F
    SX.ιChainComplex (pathSingularSimplex p) =
      (I.ιChainComplex intervalIdentitySimplex ≫ C.d 1 0) ≫ H.hom 0 1 +
        (I.ιChainComplex intervalIdentitySimplex ≫ H.hom 1 2) ≫ K.d 2 1 +
        SX.ιChainComplex (pathSingularSimplex q) := by
  -- Specialize the abstract chain-homotopy commutator equation to degree one.
  dsimp only
  have h := (pathSingularChainHomotopy F).comm 1
  rw [_root_.dNext_eq (pathSingularChainHomotopy F).hom chainComplex_rel_one_zero,
    _root_.prevD_eq (pathSingularChainHomotopy F).hom chainComplex_rel_two_one] at h
  -- Precompose by the interval generator and compute the two endpoint chain maps.
  have h' := congrArg
    (fun k ↦ (TopCat.toSSet.obj TopCat.I.{u}).ιChainComplex
      intervalIdentitySimplex ≫ k) h
  simpa only [Preadditive.comp_add, Category.assoc,
    ιChainComplex_intervalIdentitySimplex_map] using h'

/-- Helper for Theorem 75.2: a coproduct map induced by a function on simplices sends
each singular-chain generator to the generator indexed by its image. -/
lemma ιChainComplex_comp_sigmaMap' {X Y : SSet.{u}} (R : AddCommGrpCat.{u})
    {n m : ℕ} (f : X.obj (Opposite.op (SimplexCategory.mk n)) →
      Y.obj (Opposite.op (SimplexCategory.mk m)))
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) :
    X.ιChainComplex x ≫
        Sigma.map'
          (f := fun _ : X.obj (Opposite.op (SimplexCategory.mk n)) ↦ R)
          (g := fun _ : Y.obj (Opposite.op (SimplexCategory.mk m)) ↦ R)
          f (fun _ ↦ 𝟙 R) =
      Y.ιChainComplex (f x) := by
  -- This is the defining coproduct computation rule, in singular-chain notation.
  exact Sigma.ι_comp_map'
    (f := fun _ : X.obj (Opposite.op (SimplexCategory.mk n)) ↦ R)
    (g := fun _ : Y.obj (Opposite.op (SimplexCategory.mk m)) ↦ R)
    f (fun _ ↦ 𝟙 R) x

/-- Helper for Theorem 75.2: the degree-zero component of the path-induced chain
homotopy sends a vertex generator to the negative generator of its prism edge. -/
lemma ιChainComplex_pathSingularChainHomotopy_hom_zero {X : Type u}
    [TopologicalSpace X] {x y : X} {p q : Path x y} (F : p.Homotopy q)
    (v : (TopCat.toSSet.obj TopCat.I.{u}).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    let I := TopCat.toSSet.obj TopCat.I.{u}
    let SX := TopCat.toSSet.obj (TopCat.of X)
    I.ιChainComplex v ≫ (pathSingularChainHomotopy F).hom 0 1 =
      -SX.ιChainComplex
        ((pathTopCatHomotopy F).toSSet.toSimplicialObjectHomotopy.h 0 v) := by
  -- Unfold the fresh degree-zero component and apply the coproduct-map computation once.
  have hgenerator := ιChainComplex_comp_sigmaMap'
    (AddCommGrpCat.of (ULift.{u} ℤ))
    (fun z ↦ (pathTopCatHomotopy F).toSSet.toSimplicialObjectHomotopy.h 0 z) v
  dsimp [pathSingularChainHomotopy,
    TopCat.Homotopy.singularChainComplexFunctorObjMap,
    SSet.Homotopy.chainComplexMap,
    CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap,
    CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy,
    CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom]
  rw [Fin.sum_univ_one]
  norm_num [Preadditive.comp_neg]
  exact (Preadditive.comp_neg _ _).trans (congrArg Neg.neg hgenerator)

/-- Helper for Theorem 75.2: the singular-edge equivalence sends a mapped simplex
to postcomposition of its represented interval map. -/
lemma toSSetObj₁Equiv_map {X Y : TopCat.{u}} (f : X ⟶ Y)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 1))) :
    Y.toSSetObj₁Equiv
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 1)) s) =
      X.toSSetObj₁Equiv s ≫ f := by
  -- Both sides postcompose the continuous map represented by the singular edge.
  rfl

/-- Helper for Theorem 75.2: the singular-simplex equivalence evaluates a lifted
topological simplex by precomposing with the canonical universe lift. -/
lemma toSSetObjEquiv_uliftUp {X : TopCat.{u}} (n : SimplexCategory)
    (f : SimplexCategory.toTop.{u}.obj n ⟶ X) :
    X.toSSetObjEquiv (Opposite.op n) (ULift.up f) =
      f.hom.comp
        ⟨Homeomorph.ulift.symm, Homeomorph.ulift.symm.continuous⟩ := by
  -- This is the computation rule of the three equivalences defining singular simplices.
  rfl

/-- Helper for Theorem 75.2: the adjunction-defined interval edge represents
the identity map of `TopCat.I`. -/
lemma toSSetObj₁Equiv_yoneda_toSSetObjI :
    TopCat.I.toSSetObj₁Equiv
        (SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI.{u}) = 𝟙 TopCat.I := by
  -- Expose the adjunction transpose and read its Yoneda value as postcomposition.
  unfold SSet.stdSimplex.toSSetObjI
  rw [Adjunction.homEquiv_unit, SSet.yonedaEquiv_comp]
  refine (toSSetObj₁Equiv_map SSet.stdSimplex.toTopObjIsoI.hom
    (SSet.yonedaEquiv
      (sSetTopAdj.unit.app (SSet.stdSimplex.obj (SimplexCategory.mk 1))))).trans ?_
  have hunit :
      (uliftYonedaEquiv
        (sSetTopAdj.unit.app (SSet.stdSimplex.obj (SimplexCategory.mk 1)))).down =
        SSet.toTopSimplex.inv.app (SimplexCategory.mk 1) := by
    rw [uliftYonedaEquiv_apply]
    refine (sSetTopAdj_unit_app_app_down
      (SSet.stdSimplex.obj (SimplexCategory.mk 1))
      (Opposite.op (SimplexCategory.mk 1))
      (SSet.yonedaEquiv
        (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk 1))))).trans ?_
    rw [Equiv.symm_apply_apply]
    exact (congrArg
      (fun k ↦ SSet.toTopSimplex.inv.app (SimplexCategory.mk 1) ≫ k)
      (SSet.toTop.map_id (SSet.stdSimplex.obj (SimplexCategory.mk 1)))).trans
        (Category.comp_id _)
  have hunitLift :
      uliftYonedaEquiv
          (sSetTopAdj.unit.app (SSet.stdSimplex.obj (SimplexCategory.mk 1))) =
        ULift.up (SSet.toTopSimplex.inv.app (SimplexCategory.mk 1)) := by
    apply Equiv.ulift.injective
    exact hunit
  have hunitMap := congrArg
    (fun z ↦
      (SSet.toTop.obj (SSet.stdSimplex.obj (SimplexCategory.mk 1))).toSSetObj₁Equiv z ≫
        SSet.stdSimplex.toTopObjIsoI.hom) hunitLift
  refine hunitMap.trans ?_
  have hsimplex := toSSetObjEquiv_uliftUp (SimplexCategory.mk 1)
    (SSet.toTopSimplex.inv.app (SimplexCategory.mk 1))
  have hrepresented := congrArg
    (fun k ↦ TopCat.ofHom
      (k.comp (toContinuousMap TopCat.stdSimplexHomeomorphI.symm)) ≫
        SSet.stdSimplex.toTopObjIsoI.hom) hsimplex
  refine hrepresented.trans ?_
  -- Evaluate the two represented maps and cancel the realization comparison pointwise.
  ext t
  rw [TopCat.comp_app, TopCat.id_app, TopCat.ofHom_apply]
  unfold SSet.stdSimplex.toTopObjIsoI TopCat.isoOfHomeo
  rw [TopCat.ofHom_apply]
  unfold SimplexCategory.toTopHomeo
  let z := Homeomorph.ulift.symm (TopCat.stdSimplexHomeomorphI.{u}.symm t)
  let pre := (((SSet.toTopSimplex.inv.app (SimplexCategory.mk 1)).hom.comp
    (toContinuousMap Homeomorph.ulift.symm)).comp
      (toContinuousMap TopCat.stdSimplexHomeomorphI.{u}.symm)) t
  have hpre : pre =
      (SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1)).inv z := by
    rfl
  have hcancel :=
    (SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1)).inv_hom_id_apply z
  have htail := congrArg
    (fun w ↦ TopCat.I.homeomorph.{u}
      ((Homeomorph.ulift.trans TopCat.stdSimplexHomeomorphI.{u}) w)) hcancel
  have hnormalize :
      (((TopCat.homeoOfIso
        (SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1))).trans
          Homeomorph.ulift).trans TopCat.stdSimplexHomeomorphI.{u}) pre =
        (Homeomorph.ulift.trans TopCat.stdSimplexHomeomorphI.{u})
          ((SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1)).hom
            ((SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1)).inv z)) := by
    calc
      _ = TopCat.stdSimplexHomeomorphI.{u}
          (((TopCat.homeoOfIso
            (SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1))).trans
              Homeomorph.ulift) pre) :=
        Homeomorph.trans_apply _ _ _
      _ = TopCat.stdSimplexHomeomorphI.{u}
          (Homeomorph.ulift
            ((TopCat.homeoOfIso
              (SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1))) pre)) :=
        congrArg TopCat.stdSimplexHomeomorphI.{u}
          (Homeomorph.trans_apply _ _ _)
      _ = _ := by
        rw [hpre]
        rfl
  have harg :
      (((SSet.toTopSimplex.inv.app (SimplexCategory.mk 1)).hom.comp
        (toContinuousMap Homeomorph.ulift.symm)).comp
          (toContinuousMap TopCat.stdSimplexHomeomorphI.{u}.symm)) t = pre := by
    rfl
  have hstart := congrArg
    (fun q ↦ TopCat.I.homeomorph.{u}
      ((((TopCat.homeoOfIso
        (SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1))).trans
          Homeomorph.ulift).trans TopCat.stdSimplexHomeomorphI.{u}) q)) harg
  have hrest : TopCat.I.homeomorph.{u}
      ((((TopCat.homeoOfIso
        (SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1))).trans
          Homeomorph.ulift).trans TopCat.stdSimplexHomeomorphI.{u}) pre) =
        TopCat.I.homeomorph.{u} t := by
    calc
      _ = TopCat.I.homeomorph.{u}
          ((Homeomorph.ulift.trans TopCat.stdSimplexHomeomorphI.{u})
            ((SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1)).hom
              ((SSet.toTopSimplex.{u}.app (SimplexCategory.mk 1)).inv z))) := by
        exact congrArg TopCat.I.homeomorph.{u} hnormalize
      _ = TopCat.I.homeomorph.{u}
          ((Homeomorph.ulift.trans TopCat.stdSimplexHomeomorphI.{u}) z) := htail
      _ = TopCat.I.homeomorph.{u} t := by
        dsimp only [z]
        rw [Homeomorph.trans_apply]
        rw [Homeomorph.ulift.apply_symm_apply]
        rw [TopCat.stdSimplexHomeomorphI.{u}.apply_symm_apply]
  exact congrArg Subtype.val (hstart.trans hrest)

/-- Helper for Theorem 75.2: a degenerate singular edge represents the constant
interval map at its underlying vertex. -/
lemma toSSetObj₁Equiv_sigmaZero {X : TopCat.{u}}
    (v : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0))) :
    X.toSSetObj₁Equiv ((TopCat.toSSet.obj X).σ 0 v) =
      TopCat.const (X.toSSetObj₀Equiv v) := by
  -- Evaluate the degenerate simplex and use uniqueness of the standard zero-simplex.
  ext t
  dsimp [TopCat.toSSetObj₁Equiv, TopCat.toSSetObj₀Equiv]
  have hs := TopCat.toSSetObjEquiv_σ_apply v (0 : Fin 1)
    (TopCat.stdSimplexHomeomorphI.{u}.symm t)
  exact hs.trans (congrArg _ (Subsingleton.elim _ default))

/-- Helper for Theorem 75.2: the singular edge in `X ⊗ TopCat.I` obtained by
holding a singular vertex fixed while traversing the canonical interval edge. -/
noncomputable def topCatVertexPrismEdge {X : TopCat.{u}}
    (v : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0))) :
    (TopCat.toSSet.obj (X ⊗ TopCat.I)).obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  ((SSet.yonedaEquiv.symm v ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
    TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
    Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I).app
      (Opposite.op (SimplexCategory.mk 1)))
    (SSet.prodStdSimplex.nonDegenerateEquiv₁ (0 : Fin 1)).1

/-- Helper for Theorem 75.2: the represented interval map of a fixed-vertex
prism edge is constant in `X` and the identity in `TopCat.I`. -/
lemma topCatVertexPrismEdge_toSSetObj₁Equiv {X : TopCat.{u}}
    (v : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0))) :
    (X ⊗ TopCat.I).toSSetObj₁Equiv (topCatVertexPrismEdge v) =
      CartesianMonoidalCategory.lift
        (TopCat.const (X.toSSetObj₀Equiv v)) (𝟙 TopCat.I) := by
  let s := ((SSet.yonedaEquiv.symm v ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
    TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI).app
      (Opposite.op (SimplexCategory.mk 1)))
    (SSet.prodStdSimplex.nonDegenerateEquiv₁ (0 : Fin 1)).1
  have hμfst := congrArg
    (fun k ↦ k.app (Opposite.op (SimplexCategory.mk 1)) s)
    (Functor.Monoidal.μ_fst TopCat.toSSet X TopCat.I)
  have hμsnd := congrArg
    (fun k ↦ k.app (Opposite.op (SimplexCategory.mk 1)) s)
    (Functor.Monoidal.μ_snd TopCat.toSSet X TopCat.I)
  have hμfst' :
      (TopCat.toSSet.map (CartesianMonoidalCategory.fst X TopCat.I)).app
          (Opposite.op (SimplexCategory.mk 1))
          ((Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I).app
            (Opposite.op (SimplexCategory.mk 1)) s) = s.1 := by
    calc
      _ = (CartesianMonoidalCategory.fst (TopCat.toSSet.obj X)
          (TopCat.toSSet.obj TopCat.I)).app
            (Opposite.op (SimplexCategory.mk 1)) s := by
        simpa only [NatTrans.comp_app, types_comp_apply, TypeCat.hom_ofHom,
          TypeCat.Fun.coe_mk] using hμfst
      _ = s.1 := rfl
  have hμsnd' :
      (TopCat.toSSet.map (CartesianMonoidalCategory.snd X TopCat.I)).app
          (Opposite.op (SimplexCategory.mk 1))
          ((Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I).app
            (Opposite.op (SimplexCategory.mk 1)) s) = s.2 := by
    calc
      _ = (CartesianMonoidalCategory.snd (TopCat.toSSet.obj X)
          (TopCat.toSSet.obj TopCat.I)).app
            (Opposite.op (SimplexCategory.mk 1)) s := by
        simpa only [NatTrans.comp_app, types_comp_apply, TypeCat.hom_ofHom,
          TypeCat.Fun.coe_mk] using hμsnd
      _ = s.2 := rfl
  have hs_fst : s.1 = (TopCat.toSSet.obj X).σ 0 v := by
    rfl
  have hs_snd : s.2 = SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI.{u} := by
    have hedge :
        (SSet.prodStdSimplex.nonDegenerateEquiv₁ (0 : Fin 1)).1.2 =
          SSet.yonedaEquiv
            (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk 1))) := by
      apply SSet.stdSimplex.objEquiv.injective
      have hscoord := congrArg SSet.stdSimplex.objEquiv
        (SSet.prodStdSimplex.nonDegenerateEquiv₁_snd (0 : Fin 1))
      have hobjMk :
          SSet.stdSimplex.objEquiv
              (SSet.stdSimplex.objMk₁ (0 : Fin 1).castSucc.succ) =
            𝟙 (SimplexCategory.mk 1) := by
        ext j
        fin_cases j <;> rfl
      have hyoneda :
          SSet.stdSimplex.objEquiv.{u}
              (SSet.yonedaEquiv
                (𝟙 (SSet.stdSimplex.{u}.obj (SimplexCategory.mk 1)))) =
            𝟙 (SimplexCategory.mk 1) := by
        rfl
      exact hscoord.trans (hobjMk.trans hyoneda.symm)
    exact congrArg
      (fun e ↦ SSet.stdSimplex.toSSetObjI.app
        (Opposite.op (SimplexCategory.mk 1)) e) hedge
  have hfst :
      (TopCat.toSSet.map (CartesianMonoidalCategory.fst X TopCat.I)).app
          (Opposite.op (SimplexCategory.mk 1)) (topCatVertexPrismEdge v) =
        (TopCat.toSSet.obj X).σ 0 v := by
    exact hμfst'.trans (hs_fst)
  have hsnd :
      (TopCat.toSSet.map (CartesianMonoidalCategory.snd X TopCat.I)).app
          (Opposite.op (SimplexCategory.mk 1)) (topCatVertexPrismEdge v) =
        SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI.{u} := by
    exact hμsnd'.trans hs_snd
  -- It suffices to identify the `X` and interval projections separately.
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst, ← toSSetObj₁Equiv_map]
    rw [hfst, toSSetObj₁Equiv_sigmaZero]
  · rw [CartesianMonoidalCategory.lift_snd, ← toSSetObj₁Equiv_map]
    rw [hsnd, toSSetObj₁Equiv_yoneda_toSSetObjI]

/-- Helper for Theorem 75.2: the degree-zero combinatorial prism edge of a
`TopCat` homotopy is the topological track of the selected vertex. -/
lemma topCatHomotopy_hZero_apply {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g)
    (v : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (t : TopCat.I.{u}) :
    Y.toSSetObj₁Equiv
        (H.toSSet.toSimplicialObjectHomotopy.h 0 v) t =
      H (TopCat.I.homeomorph t, X.toSSetObj₀Equiv v) := by
  -- Route correction: normalize the prism while it is still a singular edge,
  -- before the coproduct and chain-complex constructions hide its pointwise form.
  have hedge : H.toSSet.toSimplicialObjectHomotopy.h 0 v =
      (TopCat.toSSet.map H.h).app (Opposite.op (SimplexCategory.mk 1))
        (topCatVertexPrismEdge v) := by
    rfl
  rw [hedge, toSSetObj₁Equiv_map,
    topCatVertexPrismEdge_toSSetObj₁Equiv, TopCat.comp_app,
    TopCat.Homotopy.h_hom_apply]
  rfl

/-- Helper for Theorem 75.2: for a homotopy of based loops, the degree-zero term in
the evaluated chain-homotopy equation cancels between the two interval endpoints. -/
lemma pathSingularChainHomotopy_endpointTerm_eq_zero {X : Type u} [TopologicalSpace X]
    {x₀ : X} {p q : Path x₀ x₀} (F : p.Homotopy q) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let I := TopCat.toSSet.obj TopCat.I.{u}
    let C := I.chainComplex R
    let H := pathSingularChainHomotopy F
    (I.ιChainComplex intervalIdentitySimplex ≫ C.d 1 0) ≫ H.hom 0 1 = 0 := by
  -- The two faces of the interval identity are the terminal and initial vertices.
  let I := TopCat.toSSet.obj TopCat.I.{u}
  have hfaceZero : I.δ 0 intervalIdentitySimplex =
      TopCat.toSSetObj₀Equiv.symm (1 : TopCat.I.{u}) := by
    unfold intervalIdentitySimplex
    rw [TopCat.δ_zero_toSSetObj₁Equiv.symm]
    rfl
  have hfaceOne : I.δ 1 intervalIdentitySimplex =
      TopCat.toSSetObj₀Equiv.symm (0 : TopCat.I.{u}) := by
    unfold intervalIdentitySimplex
    rw [TopCat.δ_one_toSSetObj₁Equiv.symm]
    rfl
  -- Endpoint fixation identifies the two prism edges represented by these vertices.
  have hedge :
      (pathTopCatHomotopy F).toSSet.toSimplicialObjectHomotopy.h 0
          (I.δ 0 intervalIdentitySimplex) =
        (pathTopCatHomotopy F).toSSet.toSimplicialObjectHomotopy.h 0
          (I.δ 1 intervalIdentitySimplex) := by
    apply TopCat.toSSetObj₁Equiv.injective
    ext t
    rw [topCatHomotopy_hZero_apply, topCatHomotopy_hZero_apply,
      hfaceZero, hfaceOne]
    simp only [Equiv.apply_symm_apply]
    exact (F.target (TopCat.I.homeomorph t)).trans
      (F.source (TopCat.I.homeomorph t)).symm
  -- Expand the interval boundary, compute the degree-zero homotopy on generators,
  -- and cancel the now equal edge terms.
  dsimp only
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp,
    ιChainComplex_pathSingularChainHomotopy_hom_zero]
  dsimp only [I] at hedge
  rw [hedge]
  norm_num

/-- Helper for Theorem 75.2: endpoint-fixed homotopic based loops determine one-chains
whose difference is a degree-two boundary. -/
lemma pathSingularSimplex_homotopic_modBoundary {X : Type u} [TopologicalSpace X]
    {x₀ : X} {p q : Path x₀ x₀} (F : p.Homotopy q) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let I := TopCat.toSSet.obj TopCat.I.{u}
    let SX := TopCat.toSSet.obj (TopCat.of X)
    let K := SX.chainComplex R
    let H := pathSingularChainHomotopy F
    SX.ιChainComplex (pathSingularSimplex p) -
        SX.ιChainComplex (pathSingularSimplex q) =
      (I.ιChainComplex intervalIdentitySimplex ≫ H.hom 1 2) ≫ K.d 2 1 := by
  -- Remove the relative endpoint term from the raw degree-one commutator equation.
  dsimp only
  rw [pathSingularSimplex_homotopy_comm F,
    pathSingularChainHomotopy_endpointTerm_eq_zero F]
  abel

/-- Helper for Theorem 75.2: endpoint-fixed homotopic based loops represent the same
coefficient morphism into first homology. -/
lemma basedLoopHomologyCoefficient_homotopy {X : Type u} [TopologicalSpace X]
    {x₀ : X} {p q : Path x₀ x₀} (F : p.Homotopy q) :
    basedLoopHomologyCoefficient p = basedLoopHomologyCoefficient q := by
  -- Record the chain-level boundary witness supplied by the relative prism equation.
  let R := AddCommGrpCat.of (ULift.{u} ℤ)
  let I := TopCat.toSSet.obj TopCat.I.{u}
  let SX := TopCat.toSSet.obj (TopCat.of X)
  let K := SX.chainComplex R
  let H := pathSingularChainHomotopy F
  let b := I.ιChainComplex intervalIdentitySimplex ≫ H.hom 1 2
  have hboundary :
      SX.ιChainComplex (pathSingularSimplex p) -
          SX.ιChainComplex (pathSingularSimplex q) = b ≫ K.d 2 1 :=
    pathSingularSimplex_homotopic_modBoundary F
  have hcycle :
      (SX.ιChainComplex (pathSingularSimplex p) -
          SX.ιChainComplex (pathSingularSimplex q)) ≫ K.d 1 0 = 0 := by
    rw [Preadditive.sub_comp, pathSingularSimplex_loop_isCycle,
      pathSingularSimplex_loop_isCycle, sub_zero]
  -- The difference of the two named cycle lifts is the lift of their chain difference.
  have hlift : basedLoopCycle p - basedLoopCycle q =
      K.liftCycles
        (SX.ιChainComplex (pathSingularSimplex p) -
          SX.ιChainComplex (pathSingularSimplex q)) 0 chainComplex_next_one hcycle := by
    rw [← cancel_mono (K.iCycles 1)]
    rw [Preadditive.sub_comp, basedLoopCycle_iCycles p, basedLoopCycle_iCycles q,
      HomologicalComplex.liftCycles_i]
  -- A lifted boundary maps to zero in homology, so the two coefficient maps agree.
  rw [basedLoopHomologyCoefficient, basedLoopHomologyCoefficient, ← sub_eq_zero,
    ← Preadditive.sub_comp, hlift]
  exact K.liftCycles_homologyπ_eq_zero_of_boundary
    (SX.ιChainComplex (pathSingularSimplex p) -
      SX.ιChainComplex (pathSingularSimplex q)) 0 chainComplex_next_one b hboundary

/-- Helper for Theorem 75.2: endpoint-fixed homotopic based loops represent the same
element of first homology. -/
lemma basedLoopHomologyClass_homotopy {X : Type u} [TopologicalSpace X]
    {x₀ : X} {p q : Path x₀ x₀} (F : p.Homotopy q) :
    basedLoopHomologyClass p = basedLoopHomologyClass q := by
  -- Apply the integer-generator equivalence to the equality of coefficient morphisms.
  unfold basedLoopHomologyClass
  rw [basedLoopHomologyCoefficient_homotopy F]

/-- Helper for Theorem 75.2: homotopic based loops have equal first-homology classes. -/
lemma basedLoopHomologyClass_eq_of_homotopic {X : Type u} [TopologicalSpace X]
    {x₀ : X} {p q : Path x₀ x₀} (h : p.Homotopic q) :
    basedLoopHomologyClass p = basedLoopHomologyClass q := by
  -- Choose the endpoint-fixed homotopy and apply the class-level prism invariance.
  exact basedLoopHomologyClass_homotopy h.some

/-- Helper for Theorem 75.2: the loop-class assignment descended as a function from
the fundamental group to first homology. -/
noncomputable def fundamentalGroupToFirstHomologyFunction {X : Type u}
    [TopologicalSpace X] (x₀ : X) :
    FundamentalGroup X x₀ →
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (AddCommGrpCat.of (ULift.{u} ℤ))).homology 1 :=
  Quotient.lift (fun p ↦ basedLoopHomologyClass p)
    (fun _ _ h ↦ basedLoopHomologyClass_eq_of_homotopic h)

/-- Helper for Theorem 75.2: on a represented based loop, the descended function
recovers the named first-homology class. -/
lemma fundamentalGroupToFirstHomologyFunction_mk {X : Type u} [TopologicalSpace X]
    (x₀ : X) (p : Path x₀ x₀) :
    fundamentalGroupToFirstHomologyFunction x₀
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      basedLoopHomologyClass p := by
  -- This is the quotient lift computation on a path representative.
  rfl

/-- Helper for Theorem 75.2: the boundary of an arbitrary singular one-simplex is
its terminal face minus its initial face. -/
lemma singularOneSimplex_boundary {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let SX := TopCat.toSSet.obj (TopCat.of X)
    SX.ιChainComplex σ ≫ (SX.chainComplex R).d 1 0 =
      SX.ιChainComplex (SX.δ 0 σ) - SX.ιChainComplex (SX.δ 1 σ) := by
  -- Expand the alternating two-face sum and normalize its integer coefficients.
  dsimp only
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  norm_num [sub_eq_add_neg]

/-- Helper for Theorem 75.2: the coefficient summand of a vertex maps to the chain
represented by its chosen connector from the basepoint. -/
noncomputable def vertexConnectorCoefficientHom {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (v : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    AddCommGrpCat.of (ULift.{u} ℤ) ⟶
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (AddCommGrpCat.of (ULift.{u} ℤ))).X 1 :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (pathSingularSimplex (connectors (TopCat.toSSetObj₀Equiv v)))

/-- Helper for Theorem 75.2: extend the chosen connector chains additively from
degree-zero singular generators. -/
noncomputable def connectorChainHom {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (AddCommGrpCat.of (ULift.{u} ℤ))).X 0 ⟶
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (AddCommGrpCat.of (ULift.{u} ℤ))).X 1 :=
  ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan
      (AddCommGrpCat.of (ULift.{u} ℤ)) 0).desc
    (Cofan.mk _ (fun v ↦ vertexConnectorCoefficientHom x₀ connectors v))

/-- Helper for Theorem 75.2: the connector-chain morphism has its prescribed value
on each degree-zero singular generator. -/
lemma ι_connectorChainHom {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (v : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex v ≫
        connectorChainHom x₀ connectors =
      vertexConnectorCoefficientHom x₀ connectors v := by
  -- Apply the coproduct descent computation at the chosen vertex summand.
  exact ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan
    (AddCommGrpCat.of (ULift.{u} ℤ)) 0).fac
      (Cofan.mk _ (fun w ↦ vertexConnectorCoefficientHom x₀ connectors w)) ⟨v⟩

/-- Helper for Theorem 75.2: the boundary of a connector chain is its endpoint
generator minus the basepoint generator. -/
lemma vertexConnectorCoefficientHom_boundary {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (v : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let SX := TopCat.toSSet.obj (TopCat.of X)
    vertexConnectorCoefficientHom x₀ connectors v ≫
        (SX.chainComplex R).d 1 0 =
      SX.ιChainComplex v -
        SX.ιChainComplex (TopCat.toSSetObj₀Equiv.symm x₀) := by
  -- Apply the path boundary formula and cancel the vertex equivalence round trip.
  dsimp only [vertexConnectorCoefficientHom]
  rw [pathSingularSimplex_boundary]
  simp only [Equiv.symm_apply_apply]

/-- Helper for Theorem 75.2: close every singular edge by subtracting the boundary
followed by the chosen connector-chain morphism. -/
noncomputable def closedEdgeChainMap {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    K.X 1 ⟶ K.X 1 :=
  let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
    (AddCommGrpCat.of (ULift.{u} ℤ))
  𝟙 _ - K.d 1 0 ≫ connectorChainHom x₀ connectors

/-- Helper for Theorem 75.2: the connector closure of every degree-one chain is a cycle. -/
lemma closedEdgeChainMap_comp_d {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    closedEdgeChainMap x₀ connectors ≫ K.d 1 0 = 0 := by
  -- Check the closure identity on each singular-edge coproduct generator.
  dsimp only
  apply SSet.chainComplex_hom_ext
  intro σ
  simp only [closedEdgeChainMap, Preadditive.comp_sub,
    Category.id_comp, Category.assoc, Preadditive.sub_comp, comp_zero]
  rw [singularOneSimplex_boundary]
  rw [← Category.assoc, singularOneSimplex_boundary]
  simp only [Preadditive.sub_comp]
  rw [← Category.assoc, ι_connectorChainHom,
    vertexConnectorCoefficientHom_boundary]
  rw [← Category.assoc, ι_connectorChainHom,
    vertexConnectorCoefficientHom_boundary]
  abel

/-- Helper for Theorem 75.2: the connector closure map lifted to degree-one cycles. -/
noncomputable def closedEdgeChainsToCycles {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    K.X 1 ⟶ K.cycles 1 :=
  let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
    (AddCommGrpCat.of (ULift.{u} ℤ))
  K.liftCycles (closedEdgeChainMap x₀ connectors) 0 chainComplex_next_one
    (closedEdgeChainMap_comp_d x₀ connectors)

/-- Helper for Theorem 75.2: connector closure retracts the inclusion of genuine
degree-one cycles. -/
lemma iCycles_closedEdgeChainsToCycles {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    K.iCycles 1 ≫ closedEdgeChainsToCycles x₀ connectors = 𝟙 _ := by
  -- Compare after the monic cycles inclusion, where the lift computation is explicit.
  dsimp only
  unfold closedEdgeChainsToCycles
  rw [← cancel_mono (((TopCat.toSSet.obj (TopCat.of X)).chainComplex
    (AddCommGrpCat.of (ULift.{u} ℤ))).iCycles 1)]
  rw [Category.assoc, HomologicalComplex.liftCycles_i]
  simp only [closedEdgeChainMap, Preadditive.comp_sub, Category.comp_id]
  rw [← Category.assoc, HomologicalComplex.iCycles_d, zero_comp, sub_zero]
  rw [Category.id_comp]

/-- Helper for Theorem 75.2: a surjective homomorphism to the multiplicative form of an
additive commutative group, with commutator kernel, identifies that group with the additive
form of the source abelianization. -/
noncomputable def addEquivAbelianizationOfSurjectiveKer {G : Type u} [Group G] {A : Type u}
    [AddCommGroup A] (φ : G →* Multiplicative A) (hφ : Function.Surjective φ)
    (hker : φ.ker = commutator G) : A ≃+ Additive (Abelianization G) :=
  -- First identify the multiplicative codomain with the quotient by the commutator kernel,
  -- then reinterpret that equivalence additively and remove the type tag on `A`.
  AddEquiv.toAdditive_toMultiplicative.symm.trans
    (((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).toAdditive)

/-- Helper for Theorem 75.2: the continuous map underlying a singular one-simplex,
parameterized by the unit interval. -/
noncomputable def singularEdgeMap {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 1))) :
    C(unitInterval, X) :=
  -- Transport the simplex map along the standard homeomorphism from `I` to `Δ¹`.
  (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk 1)) σ).comp
    ⟨stdSimplexHomeomorphUnitInterval.symm,
      stdSimplexHomeomorphUnitInterval.symm.continuous⟩

/-- Helper for Theorem 75.2: the initial endpoint of a singular one-simplex. -/
noncomputable def singularEdgeSource {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 1))) : X :=
  singularEdgeMap σ 0

/-- Helper for Theorem 75.2: the terminal endpoint of a singular one-simplex. -/
noncomputable def singularEdgeTarget {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 1))) : X :=
  singularEdgeMap σ 1

/-- Helper for Theorem 75.2: the initial simplicial face of a singular edge is its
topological source. -/
lemma singularEdgeSource_eq_face {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    singularEdgeSource σ = TopCat.toSSetObj₀Equiv
      ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) := by
  -- Compare the two descriptions as evaluation of the represented interval map at zero.
  rw [← TopCat.toSSetObj₁Equiv_apply_zero]
  rfl

/-- Helper for Theorem 75.2: the terminal simplicial face of a singular edge is its
topological target. -/
lemma singularEdgeTarget_eq_face {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    singularEdgeTarget σ = TopCat.toSSetObj₀Equiv
      ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) := by
  -- Compare the two descriptions as evaluation of the represented interval map at one.
  rw [← TopCat.toSSetObj₁Equiv_apply_one]
  rfl

/-- Helper for Theorem 75.2: the singular edge map starts at `singularEdgeSource σ`. -/
lemma singularEdgeMap_zero {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 1))) :
    singularEdgeMap σ 0 = singularEdgeSource σ := by
  -- The source was chosen to be evaluation at the initial endpoint.
  rfl

/-- Helper for Theorem 75.2: the singular edge map ends at `singularEdgeTarget σ`. -/
lemma singularEdgeMap_one {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 1))) :
    singularEdgeMap σ 1 = singularEdgeTarget σ := by
  -- The target was chosen to be evaluation at the terminal endpoint.
  rfl

/-- Helper for Theorem 75.2: a singular one-simplex determines a path between its endpoints. -/
noncomputable def singularEdgePath {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 1))) :
    Path (singularEdgeSource σ) (singularEdgeTarget σ) :=
  -- Package the continuous edge map with its two endpoint computations.
  ⟨singularEdgeMap σ, singularEdgeMap_zero σ, singularEdgeMap_one σ⟩

/-- Helper for Theorem 75.2: converting a singular edge to a path and back recovers
the original singular simplex. -/
lemma pathSingularSimplex_singularEdgePath {X : Type u} [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    pathSingularSimplex (singularEdgePath σ) = σ := by
  -- Compare the represented interval maps pointwise through the singular-edge equivalence.
  apply TopCat.toSSetObj₁Equiv.injective
  ext t
  rfl

/-- Helper for Theorem 75.2: converting a path to a singular edge preserves its
source endpoint. -/
lemma singularEdgeSource_pathSingularSimplex {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    singularEdgeSource (pathSingularSimplex p) = x := by
  -- Evaluate the represented path at zero.
  unfold singularEdgeSource singularEdgeMap pathSingularSimplex
    TopCat.toSSetObj₁Equiv pathTopCatMap'
  unfold TopCat.stdSimplexHomeomorphI
  simp only [Nat.reduceAdd, Homeomorph.coe_trans, Equiv.symm_trans, Equiv.symm_mk,
    Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.apply_symm_apply,
    ContinuousMap.comp_assoc, Homeomorph.toContinuousMap_comp_symm,
    ContinuousMap.comp_id, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  exact p.source

/-- Helper for Theorem 75.2: converting a path to a singular edge preserves its
target endpoint. -/
lemma singularEdgeTarget_pathSingularSimplex {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    singularEdgeTarget (pathSingularSimplex p) = y := by
  -- Evaluate the represented path at one.
  unfold singularEdgeTarget singularEdgeMap pathSingularSimplex
    TopCat.toSSetObj₁Equiv pathTopCatMap'
  unfold TopCat.stdSimplexHomeomorphI
  simp only [Nat.reduceAdd, Homeomorph.coe_trans, Equiv.symm_trans, Equiv.symm_mk,
    Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.apply_symm_apply,
    ContinuousMap.comp_assoc, Homeomorph.toContinuousMap_comp_symm,
    ContinuousMap.comp_id, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  exact p.target

/-- Helper for Theorem 75.2: after normalizing endpoints, converting a path to a
singular edge and back recovers the original path. -/
lemma singularEdgePath_pathSingularSimplex_cast {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    (singularEdgePath (pathSingularSimplex p)).cast
        (singularEdgeSource_pathSingularSimplex p).symm
        (singularEdgeTarget_pathSingularSimplex p).symm = p := by
  -- The two parametrized paths agree pointwise.
  ext t
  rfl

/-- Helper for Theorem 75.2: on a singular-edge generator, connector closure is
the edge chain minus its target connector plus its source connector. -/
lemma ι_closedEdgeChainMap {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    let SX := TopCat.toSSet.obj (TopCat.of X)
    SX.ιChainComplex σ ≫ closedEdgeChainMap x₀ connectors =
      SX.ιChainComplex (pathSingularSimplex (singularEdgePath σ)) -
        SX.ιChainComplex
          (pathSingularSimplex (connectors (singularEdgeTarget σ))) +
        SX.ιChainComplex
          (pathSingularSimplex (connectors (singularEdgeSource σ))) := by
  -- Expand closure, evaluate the edge boundary, and compute both connector summands.
  dsimp only
  unfold closedEdgeChainMap
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    singularOneSimplex_boundary, Preadditive.sub_comp]
  rw [ι_connectorChainHom]
  rw [ι_connectorChainHom]
  unfold vertexConnectorCoefficientHom
  rw [← singularEdgeTarget_eq_face, ← singularEdgeSource_eq_face]
  rw [pathSingularSimplex_singularEdgePath]
  abel

/-- Helper for Theorem 75.2: the affine parameter on `Δ²` whose restrictions
parametrize the two path pieces and their concatenation. -/
noncomputable def pathTransTriangleCoordinateReal (z : stdSimplex ℝ (Fin 3)) : ℝ :=
  z 1 / 2 + z 2

/-- Helper for Theorem 75.2: the affine concatenation parameter lies in the unit interval. -/
lemma pathTransTriangleCoordinateReal_mem (z : stdSimplex ℝ (Fin 3)) :
    pathTransTriangleCoordinateReal z ∈ Set.Icc (0 : ℝ) 1 := by
  -- Nonnegativity is coordinatewise; the upper bound follows from the barycentric sum.
  have hz₀ := z.property.1 (0 : Fin 3)
  have hz₁ := z.property.1 (1 : Fin 3)
  have hz₂ := z.property.1 (2 : Fin 3)
  have hsum := stdSimplex.sum_eq_one z
  rw [Fin.sum_univ_three] at hsum
  have htwoNonnegative : (0 : ℝ) ≤ 2 := by
    norm_num
  have hone_le_two : (1 : ℝ) ≤ 2 := by
    norm_num
  constructor
  · unfold pathTransTriangleCoordinateReal
    exact add_nonneg (div_nonneg hz₁ htwoNonnegative) hz₂
  · unfold pathTransTriangleCoordinateReal
    have hhalf : z 1 / 2 ≤ z 1 := div_le_self hz₁ hone_le_two
    calc
      z 1 / 2 + z 2 ≤ z 1 + z 2 := by
        simpa only [add_comm] using add_le_add_right hhalf (z 2)
      _ ≤ (z 0 + z 1) + z 2 :=
        by
          simpa only [add_comm] using add_le_add_right
            (show z 1 ≤ z 0 + z 1 from le_add_of_nonneg_left hz₀) (z 2)
      _ = 1 := hsum

/-- Helper for Theorem 75.2: the affine concatenation parameter as a map to
`unitInterval`. -/
noncomputable def pathTransTriangleCoordinate (z : stdSimplex ℝ (Fin 3)) : unitInterval :=
  ⟨pathTransTriangleCoordinateReal z, pathTransTriangleCoordinateReal_mem z⟩

/-- Helper for Theorem 75.2: the affine concatenation parameter is continuous. -/
lemma continuous_pathTransTriangleCoordinate :
    Continuous pathTransTriangleCoordinate := by
  -- Coordinate evaluation and affine arithmetic are continuous on the simplex.
  apply Continuous.subtype_mk
  exact (((continuous_apply 1).comp continuous_subtype_val).div_const 2).add
    ((continuous_apply 2).comp continuous_subtype_val)

/-- Helper for Theorem 75.2: the singular two-simplex filling the chain relation
between two composable paths and their concatenation. -/
noncomputable def pathTransTriangleMap {X : Type u} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    C(stdSimplex ℝ (Fin 3), X) :=
  ⟨fun s ↦ (p.trans q) (pathTransTriangleCoordinate s),
    (p.trans q).continuous.comp continuous_pathTransTriangleCoordinate⟩

/-- Helper for Theorem 75.2: the concatenation triangle map evaluates through its
affine interval coordinate. -/
lemma pathTransTriangleMap_apply {X : Type u} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z)
    (s : stdSimplex ℝ (Fin 3)) :
    pathTransTriangleMap p q s =
      (p.trans q) (pathTransTriangleCoordinate s) := by
  -- Expose the map's pointwise specification without unfolding its continuity field.
  rfl

/-- Helper for Theorem 75.2: the singular two-simplex attached to two composable paths. -/
noncomputable def pathTransTriangle {X : Type u} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2)) :=
  (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 2))).symm
      (pathTransTriangleMap p q)

/-- Helper for Theorem 75.2: on face zero of `Δ²`, the triangle coordinate runs
through the second half of the concatenated path. -/
lemma pathTransTriangleCoordinate_faceZero (s : stdSimplex ℝ (Fin 2)) :
    (pathTransTriangleCoordinate
      (stdSimplex.map (0 : Fin 3).succAbove s) : ℝ) =
      (1 + stdSimplexHomeomorphUnitInterval s) / 2 := by
  -- Compute the two retained barycentric coordinates and use their sum-one relation.
  classical
  have hparameter : (stdSimplexHomeomorphUnitInterval s : ℝ) = s 1 := rfl
  unfold pathTransTriangleCoordinate pathTransTriangleCoordinateReal
  simp only [hparameter, stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply]
  rw [Finset.sum_eq_single (0 : Fin 2), Finset.sum_eq_single (1 : Fin 2)]
  · rw [← stdSimplex.add_eq_one s]
    ring
  · simp
  · simp
  · simp
  · simp

/-- Helper for Theorem 75.2: on face one of `Δ²`, the triangle coordinate is the
ordinary interval coordinate. -/
lemma pathTransTriangleCoordinate_faceOne (s : stdSimplex ℝ (Fin 2)) :
    (pathTransTriangleCoordinate
      (stdSimplex.map (1 : Fin 3).succAbove s) : ℝ) =
      stdSimplexHomeomorphUnitInterval s := by
  -- The middle barycentric coordinate vanishes and the last one is retained.
  classical
  have hparameter : (stdSimplexHomeomorphUnitInterval s : ℝ) = s 1 := rfl
  unfold pathTransTriangleCoordinate pathTransTriangleCoordinateReal
  simp only [hparameter, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hmissing : Finset.univ.filter
      (fun x : Fin 2 ↦ (1 : Fin 3).succAbove x = 1) = ∅ := by
    decide
  have hfiber : Finset.univ.filter
      (fun x : Fin 2 ↦ (1 : Fin 3).succAbove x = 2) = {1} := by
    decide
  rw [hmissing, Finset.sum_empty, zero_div, zero_add, hfiber,
    Finset.sum_singleton]

/-- Helper for Theorem 75.2: the face-one coordinate equality also holds in the
subtype `unitInterval`. -/
lemma pathTransTriangleCoordinate_faceOne_eq (s : stdSimplex ℝ (Fin 2)) :
    pathTransTriangleCoordinate (stdSimplex.map (1 : Fin 3).succAbove s) =
      stdSimplexHomeomorphUnitInterval s := by
  -- Equality of interval points follows from the real-valued computation.
  apply Subtype.ext
  exact pathTransTriangleCoordinate_faceOne s

/-- Helper for Theorem 75.2: on face two of `Δ²`, the triangle coordinate runs
through the first half of the concatenated path. -/
lemma pathTransTriangleCoordinate_faceTwo (s : stdSimplex ℝ (Fin 2)) :
    (pathTransTriangleCoordinate
      (stdSimplex.map (2 : Fin 3).succAbove s) : ℝ) =
      stdSimplexHomeomorphUnitInterval s / 2 := by
  -- The last barycentric coordinate vanishes and the middle one is retained.
  classical
  have hparameter : (stdSimplexHomeomorphUnitInterval s : ℝ) = s 1 := rfl
  unfold pathTransTriangleCoordinate pathTransTriangleCoordinateReal
  simp only [hparameter, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hfiber : Finset.univ.filter
      (fun x : Fin 2 ↦ (2 : Fin 3).succAbove x = 1) = {1} := by
    decide
  have hmissing : Finset.univ.filter
      (fun x : Fin 2 ↦ (2 : Fin 3).succAbove x = 2) = ∅ := by
    decide
  rw [hfiber, Finset.sum_singleton, hmissing, Finset.sum_empty, add_zero]

/-- Helper for Theorem 75.2: along face zero, the concatenated path evaluates as
its second path at the ordinary interval coordinate. -/
lemma pathTrans_faceZero_apply {X : Type u} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z)
    (s : stdSimplex ℝ (Fin 2)) :
    (p.trans q)
        (pathTransTriangleCoordinate (stdSimplex.map (0 : Fin 3).succAbove s)) =
      q (stdSimplexHomeomorphUnitInterval s) := by
  -- Split at the gluing point; at equality both path endpoints are the common point.
  unfold Path.trans
  change (if (pathTransTriangleCoordinate
      (stdSimplex.map (0 : Fin 3).succAbove s) : ℝ) ≤ 1 / 2 then
        p.extend (2 * (pathTransTriangleCoordinate
          (stdSimplex.map (0 : Fin 3).succAbove s) : ℝ))
      else q.extend (2 * (pathTransTriangleCoordinate
        (stdSimplex.map (0 : Fin 3).succAbove s) : ℝ) - 1)) =
    q (stdSimplexHomeomorphUnitInterval s)
  split_ifs with hhalf
  · have hparameter : (stdSimplexHomeomorphUnitInterval s : ℝ) = 0 := by
      have hnonnegative := (stdSimplexHomeomorphUnitInterval s).property.1
      have hcoordinate := pathTransTriangleCoordinate_faceZero s
      change (pathTransTriangleCoordinate
        (stdSimplex.map (0 : Fin 3).succAbove s) : ℝ) ≤ 1 / 2 at hhalf
      rw [hcoordinate] at hhalf
      linarith
    have htime : 2 * (pathTransTriangleCoordinate
        (stdSimplex.map (0 : Fin 3).succAbove s) : ℝ) = 1 := by
      rw [pathTransTriangleCoordinate_faceZero, hparameter]
      norm_num
    have hqArgument : stdSimplexHomeomorphUnitInterval s = 0 := by
      apply Subtype.ext
      exact hparameter
    rw [htime, p.extend_one, hqArgument, q.source]
  · have htime : 2 * (pathTransTriangleCoordinate
        (stdSimplex.map (0 : Fin 3).succAbove s) : ℝ) - 1 =
          (stdSimplexHomeomorphUnitInterval s : ℝ) := by
      rw [pathTransTriangleCoordinate_faceZero]
      ring
    rw [htime]
    exact q.extend_extends' (stdSimplexHomeomorphUnitInterval s)

/-- Helper for Theorem 75.2: along face two, the concatenated path evaluates as
its first path at the ordinary interval coordinate. -/
lemma pathTrans_faceTwo_apply {X : Type u} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z)
    (s : stdSimplex ℝ (Fin 2)) :
    (p.trans q)
        (pathTransTriangleCoordinate (stdSimplex.map (2 : Fin 3).succAbove s)) =
      p (stdSimplexHomeomorphUnitInterval s) := by
  -- The face-two coordinate is always in the first half of the interval.
  have hhalf : (pathTransTriangleCoordinate
      (stdSimplex.map (2 : Fin 3).succAbove s) : ℝ) ≤ 1 / 2 := by
    rw [pathTransTriangleCoordinate_faceTwo]
    have htwoNonnegative : (0 : ℝ) ≤ 2 := by
      norm_num
    exact div_le_div_of_nonneg_right
      (stdSimplexHomeomorphUnitInterval s).property.2 htwoNonnegative
  unfold Path.trans
  change (if (pathTransTriangleCoordinate
      (stdSimplex.map (2 : Fin 3).succAbove s) : ℝ) ≤ 1 / 2 then
        p.extend (2 * (pathTransTriangleCoordinate
          (stdSimplex.map (2 : Fin 3).succAbove s) : ℝ))
      else q.extend (2 * (pathTransTriangleCoordinate
        (stdSimplex.map (2 : Fin 3).succAbove s) : ℝ) - 1)) =
    p (stdSimplexHomeomorphUnitInterval s)
  rw [if_pos hhalf]
  have htime : 2 * (pathTransTriangleCoordinate
      (stdSimplex.map (2 : Fin 3).succAbove s) : ℝ) =
        (stdSimplexHomeomorphUnitInterval s : ℝ) := by
    rw [pathTransTriangleCoordinate_faceTwo]
    ring
  rw [htime]
  exact p.extend_extends' (stdSimplexHomeomorphUnitInterval s)

/-- Helper for Theorem 75.2: face one of the concatenation triangle is the
singular simplex of the concatenated path. -/
lemma pathTransTriangle_faceOne {X : Type u} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 1 (pathTransTriangle p q) =
      pathSingularSimplex (p.trans q) := by
  -- Compare the represented maps on `Δ¹`, where both sides have identical endpoints.
  apply (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 1))).injective
  ext s
  rw [TopCat.toSSetObjEquiv_δ_apply]
  unfold pathTransTriangle
  rw [Equiv.apply_symm_apply]
  rw [pathTransTriangleMap_apply, pathTransTriangleCoordinate_faceOne_eq]
  unfold pathSingularSimplex TopCat.toSSetObj₁Equiv
  simp only [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  rfl

/-- Helper for Theorem 75.2: face zero of the concatenation triangle is the
singular simplex of the second path. -/
lemma pathTransTriangle_faceZero {X : Type u} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 0 (pathTransTriangle p q) =
      pathSingularSimplex q := by
  -- Compare the represented maps and apply the second-half evaluation formula.
  apply (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 1))).injective
  ext s
  rw [TopCat.toSSetObjEquiv_δ_apply]
  unfold pathTransTriangle
  rw [Equiv.apply_symm_apply, pathTransTriangleMap_apply,
    pathTrans_faceZero_apply]
  unfold pathSingularSimplex TopCat.toSSetObj₁Equiv
  simp only [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  rfl

/-- Helper for Theorem 75.2: face two of the concatenation triangle is the
singular simplex of the first path. -/
lemma pathTransTriangle_faceTwo {X : Type u} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 2 (pathTransTriangle p q) =
      pathSingularSimplex p := by
  -- Compare the represented maps and apply the first-half evaluation formula.
  apply (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 1))).injective
  ext s
  rw [TopCat.toSSetObjEquiv_δ_apply]
  unfold pathTransTriangle
  rw [Equiv.apply_symm_apply, pathTransTriangleMap_apply,
    pathTrans_faceTwo_apply]
  unfold pathSingularSimplex TopCat.toSSetObj₁Equiv
  simp only [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  rfl

/-- Helper for Theorem 75.2: the singular chain of a concatenated path differs
from the sum of its two pieces by the boundary of the concatenation triangle. -/
lemma pathSingularSimplex_trans_modBoundary {X : Type u} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let SX := TopCat.toSSet.obj (TopCat.of X)
    let K := SX.chainComplex R
    SX.ιChainComplex (pathSingularSimplex (p.trans q)) -
        SX.ιChainComplex (pathSingularSimplex p) -
        SX.ιChainComplex (pathSingularSimplex q) =
      (-SX.ιChainComplex (pathTransTriangle p q)) ≫ K.d 2 1 := by
  -- Expand the alternating three-face boundary and substitute the face specifications.
  dsimp only
  rw [Preadditive.neg_comp, SSet.ιChainComplex_d, Fin.sum_univ_three,
    pathTransTriangle_faceZero, pathTransTriangle_faceOne,
    pathTransTriangle_faceTwo]
  norm_num [sub_eq_add_neg]
  abel

/-- Helper for Theorem 75.2: concatenation adds the coefficient morphisms of two
based loops in first homology. -/
lemma basedLoopHomologyCoefficient_trans {X : Type u} [TopologicalSpace X]
    {x₀ : X} (p q : Path x₀ x₀) :
    basedLoopHomologyCoefficient (p.trans q) =
      basedLoopHomologyCoefficient p + basedLoopHomologyCoefficient q := by
  -- Lift the triangle boundary relation to the cycle object.
  let R := AddCommGrpCat.of (ULift.{u} ℤ)
  let SX := TopCat.toSSet.obj (TopCat.of X)
  let K := SX.chainComplex R
  let c : R ⟶ K.X 1 := SX.ιChainComplex (pathSingularSimplex (p.trans q)) -
    SX.ιChainComplex (pathSingularSimplex p) -
    SX.ιChainComplex (pathSingularSimplex q)
  let b : R ⟶ K.X 2 := -SX.ιChainComplex (pathTransTriangle p q)
  have hboundary : c = b ≫ K.d 2 1 :=
    pathSingularSimplex_trans_modBoundary p q
  have hcycle : c ≫ K.d 1 0 = 0 := by
    dsimp only [c]
    rw [Preadditive.sub_comp, Preadditive.sub_comp,
      pathSingularSimplex_loop_isCycle (p.trans q),
      pathSingularSimplex_loop_isCycle p, pathSingularSimplex_loop_isCycle q]
    abel
  have hlift : basedLoopCycle (p.trans q) - basedLoopCycle p - basedLoopCycle q =
      K.liftCycles c 0 chainComplex_next_one hcycle := by
    rw [← cancel_mono (K.iCycles 1)]
    rw [Preadditive.sub_comp, Preadditive.sub_comp,
      basedLoopCycle_iCycles (p.trans q), basedLoopCycle_iCycles p,
      basedLoopCycle_iCycles q, HomologicalComplex.liftCycles_i]
  have hzero :
      (basedLoopCycle (p.trans q) - basedLoopCycle p - basedLoopCycle q) ≫
        K.homologyπ 1 = 0 := by
    rw [hlift]
    exact K.liftCycles_homologyπ_eq_zero_of_boundary c 0
      chainComplex_next_one b hboundary
  -- Rewrite coefficient maps as cycle lifts followed by the homology projection.
  rw [← sub_eq_zero]
  rw [sub_add_eq_sub_sub]
  simpa only [basedLoopHomologyCoefficient, Preadditive.sub_comp] using hzero

/-- Helper for Theorem 75.2: concatenation adds the first-homology classes of two
based loops. -/
lemma basedLoopHomologyClass_trans {X : Type u} [TopologicalSpace X]
    {x₀ : X} (p q : Path x₀ x₀) :
    basedLoopHomologyClass (p.trans q) =
      basedLoopHomologyClass p + basedLoopHomologyClass q := by
  -- Apply the integer-generator additive equivalence to the coefficient identity.
  unfold basedLoopHomologyClass
  rw [basedLoopHomologyCoefficient_trans, map_add]

/-- Helper for Theorem 75.2: the singular chain of a connector-closed edge differs
from connector closure by triangle boundaries and one backtracking loop. -/
lemma connectorClosedLoop_chainRelation {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let SX := TopCat.toSSet.obj (TopCat.of X)
    let K := SX.chainComplex R
    let a := connectors (singularEdgeSource σ)
    let e := singularEdgePath σ
    let b := connectors (singularEdgeTarget σ)
    let loop := a.trans (e.trans b.symm)
    let w₁ := -SX.ιChainComplex (pathTransTriangle a (e.trans b.symm))
    let w₂ := -SX.ιChainComplex (pathTransTriangle e b.symm)
    let w₃ := -SX.ιChainComplex (pathTransTriangle b b.symm)
    SX.ιChainComplex (pathSingularSimplex loop) -
        SX.ιChainComplex σ ≫ closedEdgeChainMap x₀ connectors =
      (w₁ + w₂ - w₃) ≫ K.d 2 1 +
        SX.ιChainComplex (pathSingularSimplex (b.trans b.symm)) := by
  -- Replace connector closure by its three path chains.
  dsimp only
  rw [ι_closedEdgeChainMap]
  -- Expand the three concatenation relations and finish by additive normalization.
  have h₁ := pathSingularSimplex_trans_modBoundary
    (connectors (singularEdgeSource σ))
    ((singularEdgePath σ).trans
      (connectors (singularEdgeTarget σ)).symm)
  have h₂ := pathSingularSimplex_trans_modBoundary
    (singularEdgePath σ) (connectors (singularEdgeTarget σ)).symm
  have h₃ := pathSingularSimplex_trans_modBoundary
    (connectors (singularEdgeTarget σ))
    (connectors (singularEdgeTarget σ)).symm
  rw [Preadditive.sub_comp, Preadditive.add_comp, ← h₁, ← h₂, ← h₃]
  abel

/-- Helper for Theorem 75.2: the descended loop-class function sends fundamental
group multiplication to addition in first homology. -/
lemma fundamentalGroupToFirstHomologyFunction_mul {X : Type u}
    [TopologicalSpace X] (x₀ : X) (a b : FundamentalGroup X x₀) :
    fundamentalGroupToFirstHomologyFunction x₀ (a * b) =
      fundamentalGroupToFirstHomologyFunction x₀ a +
        fundamentalGroupToFirstHomologyFunction x₀ b := by
  -- Reduce both quotient classes to paths and use the concatenation formula.
  refine Quotient.inductionOn a ?_
  intro p
  refine Quotient.inductionOn b ?_
  intro q
  change fundamentalGroupToFirstHomologyFunction x₀
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (q.trans p))) =
    fundamentalGroupToFirstHomologyFunction x₀
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) +
      fundamentalGroupToFirstHomologyFunction x₀
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q))
  rw [fundamentalGroupToFirstHomologyFunction_mk,
    fundamentalGroupToFirstHomologyFunction_mk,
    fundamentalGroupToFirstHomologyFunction_mk,
    basedLoopHomologyClass_trans]
  exact add_comm _ _

/-- Helper for Theorem 75.2: the descended loop-class function sends the identity
loop class to zero in first homology. -/
lemma fundamentalGroupToFirstHomologyFunction_one {X : Type u}
    [TopologicalSpace X] (x₀ : X) :
    fundamentalGroupToFirstHomologyFunction x₀ 1 = 0 := by
  -- Apply multiplicativity to `1 * 1` and cancel the repeated summand.
  have h := fundamentalGroupToFirstHomologyFunction_mul x₀
    (1 : FundamentalGroup X x₀) 1
  rw [one_mul] at h
  have hcancellation := congrArg
    (fun z ↦ z - fundamentalGroupToFirstHomologyFunction x₀ 1) h
  simpa only [sub_self, add_sub_cancel_left] using hcancellation.symm

/-- Helper for Theorem 75.2: the degree-one Hurewicz homomorphism sends a loop
class to the first-homology class of its singular one-simplex. -/
noncomputable def degreeOneHurewiczHom {X : Type u} [TopologicalSpace X] (x₀ : X) :
    FundamentalGroup X x₀ →*
      Multiplicative (((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (AddCommGrpCat.of (ULift.{u} ℤ))).homology 1) :=
  { toFun := fundamentalGroupToFirstHomologyFunction x₀
    map_one' := fundamentalGroupToFirstHomologyFunction_one x₀
    map_mul' := fundamentalGroupToFirstHomologyFunction_mul x₀ }

/-- Helper for Theorem 75.2: the degree-one Hurewicz homomorphism with its
codomain spelled through the public singular-homology functor. -/
noncomputable def degreeOneHurewiczFunctorHom {X : Type u}
    [TopologicalSpace X] (x₀ : X) :
    FundamentalGroup X x₀ →*
      Multiplicative (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))).obj (TopCat.of X)) :=
  { toFun := fundamentalGroupToFirstHomologyFunction x₀
    map_one' := fundamentalGroupToFirstHomologyFunction_one x₀
    map_mul' := fundamentalGroupToFirstHomologyFunction_mul x₀ }

/-- Helper for Theorem 75.2: on a represented path, the Hurewicz homomorphism is
the named first-homology class. -/
lemma degreeOneHurewiczHom_fromPath {X : Type u} [TopologicalSpace X]
    (x₀ : X) (p : Path x₀ x₀) :
    degreeOneHurewiczHom x₀
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      basedLoopHomologyClass p := by
  -- Unfold only the homomorphism's underlying descended function.
  exact fundamentalGroupToFirstHomologyFunction_mk x₀ p

/-- Helper for Theorem 75.2: the constant based loop represents zero in first homology. -/
lemma basedLoopHomologyClass_refl {X : Type u} [TopologicalSpace X] (x : X) :
    basedLoopHomologyClass (Path.refl x) = 0 := by
  -- Identify the constant loop with the identity element of the fundamental group.
  rw [← fundamentalGroupToFirstHomologyFunction_mk]
  rw [Path.Homotopic.Quotient.mk_refl]
  exact fundamentalGroupToFirstHomologyFunction_one x

/-- Helper for Theorem 75.2: the coefficient morphism of the constant based loop
vanishes in first homology. -/
lemma basedLoopHomologyCoefficient_refl {X : Type u} [TopologicalSpace X] (x : X) :
    basedLoopHomologyCoefficient (Path.refl x) = 0 := by
  -- Use injectivity of evaluation at the lifted integer generator.
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  rw [map_zero]
  exact basedLoopHomologyClass_refl x

/-- Helper for Theorem 75.2: traversing a path and immediately reversing it has
zero coefficient in first homology. -/
lemma basedLoopHomologyCoefficient_trans_symm {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    basedLoopHomologyCoefficient (p.trans p.symm) = 0 := by
  -- Homotopy contracts the backtracking loop to the constant loop.
  rw [basedLoopHomologyCoefficient_homotopy (Path.Homotopic.trans_symm p).some]
  exact basedLoopHomologyCoefficient_refl x

/-- Helper for Theorem 75.2: the homology coefficient of a connector-closed
singular edge equals the coefficient obtained from the connector-closure cycle. -/
lemma basedLoopHomologyCoefficient_connectorClosedEdge {X : Type u}
    [TopologicalSpace X] (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let SX := TopCat.toSSet.obj (TopCat.of X)
    let K := SX.chainComplex R
    let loop := (connectors (singularEdgeSource σ)).trans
      ((singularEdgePath σ).trans (connectors (singularEdgeTarget σ)).symm)
    basedLoopHomologyCoefficient loop =
      (SX.ιChainComplex σ ≫ closedEdgeChainsToCycles x₀ connectors) ≫
        K.homologyπ 1 := by
  -- Name the two cycles and their chain-level difference.
  let R := AddCommGrpCat.of (ULift.{u} ℤ)
  let SX := TopCat.toSSet.obj (TopCat.of X)
  let K := SX.chainComplex R
  let a := connectors (singularEdgeSource σ)
  let e := singularEdgePath σ
  let b := connectors (singularEdgeTarget σ)
  let loop := a.trans (e.trans b.symm)
  let closedCycle : R ⟶ K.cycles 1 :=
    SX.ιChainComplex σ ≫ closedEdgeChainsToCycles x₀ connectors
  let closedChain : R ⟶ K.X 1 :=
    SX.ιChainComplex σ ≫ closedEdgeChainMap x₀ connectors
  let c : R ⟶ K.X 1 :=
    SX.ιChainComplex (pathSingularSimplex loop) - closedChain
  let w₁ : R ⟶ K.X 2 :=
    -SX.ιChainComplex (pathTransTriangle a (e.trans b.symm))
  let w₂ : R ⟶ K.X 2 :=
    -SX.ιChainComplex (pathTransTriangle e b.symm)
  let w₃ : R ⟶ K.X 2 :=
    -SX.ιChainComplex (pathTransTriangle b b.symm)
  let w : R ⟶ K.X 2 := w₁ + w₂ - w₃
  let backtrack : R ⟶ K.X 1 :=
    SX.ιChainComplex (pathSingularSimplex (b.trans b.symm))
  have hrelation : c = w ≫ K.d 2 1 + backtrack :=
    connectorClosedLoop_chainRelation x₀ connectors σ
  have hcycle : c ≫ K.d 1 0 = 0 := by
    dsimp only [c, closedChain, loop]
    rw [Preadditive.sub_comp, pathSingularSimplex_loop_isCycle]
    rw [Category.assoc, closedEdgeChainMap_comp_d, comp_zero, sub_zero]
  have hclosedCycle : closedCycle ≫ K.iCycles 1 = closedChain := by
    dsimp only [closedCycle, closedChain, closedEdgeChainsToCycles]
    rw [Category.assoc, HomologicalComplex.liftCycles_i]
  have hliftDifference : basedLoopCycle loop - closedCycle =
      K.liftCycles c 0 chainComplex_next_one hcycle := by
    rw [← cancel_mono (K.iCycles 1)]
    rw [Preadditive.sub_comp, basedLoopCycle_iCycles, hclosedCycle,
      HomologicalComplex.liftCycles_i]
  -- Separate the boundary part from the backtracking loop in the cycle object.
  let boundaryChain : R ⟶ K.X 1 := w ≫ K.d 2 1
  have hboundaryCycle : boundaryChain ≫ K.d 1 0 = 0 := by
    dsimp only [boundaryChain]
    rw [Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
  have hbacktrackCycle : backtrack ≫ K.d 1 0 = 0 := by
    dsimp only [backtrack]
    exact pathSingularSimplex_loop_isCycle (b.trans b.symm)
  have hliftDecomposition : K.liftCycles c 0 chainComplex_next_one hcycle =
      K.liftCycles boundaryChain 0 chainComplex_next_one hboundaryCycle +
        K.liftCycles backtrack 0 chainComplex_next_one hbacktrackCycle := by
    rw [← cancel_mono (K.iCycles 1)]
    rw [Preadditive.add_comp, HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
    exact hrelation
  have hboundaryZero :
      K.liftCycles boundaryChain 0 chainComplex_next_one hboundaryCycle ≫
        K.homologyπ 1 = 0 := by
    exact K.liftCycles_homologyπ_eq_zero_of_boundary boundaryChain 0
      chainComplex_next_one w rfl
  have hbacktrackZero :
      K.liftCycles backtrack 0 chainComplex_next_one hbacktrackCycle ≫
        K.homologyπ 1 = 0 := by
    have hcoefficient := basedLoopHomologyCoefficient_trans_symm b
    unfold basedLoopHomologyCoefficient at hcoefficient
    have hliftBacktrack : K.liftCycles backtrack 0 chainComplex_next_one
        hbacktrackCycle = basedLoopCycle (b.trans b.symm) := by
      rw [← cancel_mono (K.iCycles 1)]
      rw [HomologicalComplex.liftCycles_i, basedLoopCycle_iCycles]
    rw [hliftBacktrack]
    exact hcoefficient
  have hliftZero : K.liftCycles c 0 chainComplex_next_one hcycle ≫
      K.homologyπ 1 = 0 := by
    rw [hliftDecomposition, Preadditive.add_comp, hboundaryZero,
      hbacktrackZero, add_zero]
  -- The vanishing difference of cycle coefficients is the desired equality.
  change basedLoopHomologyCoefficient loop = closedCycle ≫ K.homologyπ 1
  unfold basedLoopHomologyCoefficient
  rw [← sub_eq_zero, ← Preadditive.sub_comp, hliftDifference, hliftZero]

/-- Helper for Theorem 75.2: the Hurewicz homomorphism factors additively through
the abelianization of the fundamental group. -/
noncomputable def abelianizedDegreeOneHurewiczHom {X : Type u}
    [TopologicalSpace X] (x₀ : X) :
    Additive (Abelianization (FundamentalGroup X x₀)) →+
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (AddCommGrpCat.of (ULift.{u} ℤ))).homology 1 :=
  (Abelianization.lift (degreeOneHurewiczHom x₀)).toAdditiveLeft

/-- Helper for Theorem 75.2: the abelianized Hurewicz homomorphism as a morphism
of additive commutative groups. -/
noncomputable def abelianizedDegreeOneHurewiczMorphism {X : Type u}
    [TopologicalSpace X] (x₀ : X) :
    AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x₀))) ⟶
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (AddCommGrpCat.of (ULift.{u} ℤ))).homology 1 :=
  AddCommGrpCat.ofHom (abelianizedDegreeOneHurewiczHom x₀)

/-- Helper for Theorem 75.2: the categorical Hurewicz morphism evaluates as its
underlying additive homomorphism. -/
lemma abelianizedDegreeOneHurewiczMorphism_apply {X : Type u}
    [TopologicalSpace X] (x₀ : X)
    (a : Additive (Abelianization (FundamentalGroup X x₀))) :
    abelianizedDegreeOneHurewiczMorphism x₀ a =
      abelianizedDegreeOneHurewiczHom x₀ a := by
  -- This is the coercion computation for `AddCommGrpCat.ofHom`.
  rfl

/-- Helper for Theorem 75.2: the abelianized Hurewicz map sends a projected loop
class to its degree-one Hurewicz class. -/
lemma abelianizedDegreeOneHurewiczHom_of {X : Type u} [TopologicalSpace X]
    (x₀ : X) (g : FundamentalGroup X x₀) :
    abelianizedDegreeOneHurewiczHom x₀
        (Additive.ofMul (Abelianization.of g)) =
      degreeOneHurewiczHom x₀ g := by
  -- This is the computation rule of `Abelianization.lift`, with type tags removed.
  rfl

/-- Helper for Theorem 75.2: the public-spelling Hurewicz homomorphism agrees
pointwise with the explicit-chain-complex abelianized factor. -/
lemma degreeOneHurewiczFunctorHom_factor {X : Type u} [TopologicalSpace X]
    (x₀ : X) (g : FundamentalGroup X x₀) :
    degreeOneHurewiczFunctorHom x₀ g =
      abelianizedDegreeOneHurewiczHom x₀
        (Additive.ofMul (Abelianization.of g)) := by
  -- Both constructions have the descended loop-class function as underlying map.
  rfl

/-- Helper for Theorem 75.2: evaluation at the lifted integer generator commutes
with postcomposition of additive-group morphisms. -/
lemma uliftZMultiplesAddEquiv_comp {A B : AddCommGrpCat.{u}}
    (f : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ A) (g : A ⟶ B) :
    AddCommGrpCat.uliftZMultiplesAddEquiv B (f ≫ g) =
      g (AddCommGrpCat.uliftZMultiplesAddEquiv A f) := by
  -- Both sides evaluate the composite at the universal lifted integer generator.
  rfl

/-- Helper for Theorem 75.2: chosen paths from the base point close a singular edge to a
based loop, hence to an element of the fundamental group. -/
noncomputable def basedLoopOfSingularEdge {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) : FundamentalGroup X x₀ :=
  -- Travel to the source, traverse the edge, and return from the target.
  FundamentalGroup.fromPath <| Path.Homotopic.Quotient.mk <|
    (connectors (singularEdgeSource σ)).trans
      ((singularEdgePath σ).trans (connectors (singularEdgeTarget σ)).symm)

/-- Helper for Theorem 75.2: path connectedness canonically supplies the connector paths
used to close a singular edge at the chosen base point. -/
noncomputable def pathConnectedBasedLoopOfSingularEdge {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x₀ : X)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) : FundamentalGroup X x₀ :=
  -- Specialize the connector construction to the paths chosen by path connectedness.
  basedLoopOfSingularEdge x₀ (PathConnectedSpace.somePath x₀) σ

/-- Helper for Theorem 75.2: the standard topological two-simplex is contractible. -/
lemma stdTwoSimplex_contractible : ContractibleSpace (stdSimplex ℝ (Fin 3)) := by
  -- Convexity contracts the simplex to any chosen vertex.
  exact (convex_stdSimplex ℝ (Fin 3)).contractibleSpace
    ⟨stdSimplex.vertex 0, (stdSimplex.vertex 0).property⟩

/-- Helper for Theorem 75.2: any two paths with common endpoints in the standard
two-simplex are homotopic relative to those endpoints. -/
lemma stdTwoSimplex_pathsHomotopic {x y : stdSimplex ℝ (Fin 3)}
    (p q : Path x y) : p.Homotopic q := by
  -- Contractibility supplies simple connectedness, which identifies all such paths.
  letI : ContractibleSpace (stdSimplex ℝ (Fin 3)) := stdTwoSimplex_contractible
  exact SimplyConnectedSpace.paths_homotopic p q

/-- Helper for Theorem 75.2: in the standard two-simplex, a direct path is homotopic
to any two-stage path with the same endpoints. -/
lemma stdTwoSimplex_pathTransHomotopic {x y z : stdSimplex ℝ (Fin 3)}
    (direct : Path x z) (first : Path x y) (second : Path y z) :
    direct.Homotopic (first.trans second) := by
  -- Apply the common-endpoint uniqueness lemma to the direct and concatenated paths.
  exact stdTwoSimplex_pathsHomotopic direct (first.trans second)

/-- Helper for Theorem 75.2: mapping a direct-versus-two-stage path relation out of the
standard two-simplex preserves its endpoint-fixed homotopy. -/
lemma stdTwoSimplex_mappedPathTransHomotopic {X : Type u} [TopologicalSpace X]
    {x y z : stdSimplex ℝ (Fin 3)} (f : C(stdSimplex ℝ (Fin 3), X))
    (direct : Path x z) (first : Path x y) (second : Path y z) :
    (direct.map f.continuous).Homotopic
      ((first.trans second).map f.continuous) := by
  -- Functoriality of path homotopies transports the simplex relation into the target space.
  exact (stdTwoSimplex_pathTransHomotopic direct first second).map f

/-- Helper for Theorem 75.2: the continuous parametrization of the edge opposite `i`
in the standard topological two-simplex. -/
noncomputable def stdTwoSimplexEdgeMap (i : Fin 3) :
    C(unitInterval, stdSimplex ℝ (Fin 3)) :=
  -- First identify the interval with `Δ¹`, then include the face opposite `i` into `Δ²`.
  (ContinuousMap.mk (stdSimplex.map (S := ℝ) i.succAbove)
    (stdSimplex.continuous_map i.succAbove)).comp
      ⟨stdSimplexHomeomorphUnitInterval.symm,
        stdSimplexHomeomorphUnitInterval.symm.continuous⟩

/-- Helper for Theorem 75.2: the edge opposite `i` begins at its first retained vertex. -/
lemma stdTwoSimplexEdgeMap_zero (i : Fin 3) :
    stdTwoSimplexEdgeMap i 0 = stdSimplex.vertex (S := ℝ) (i.succAbove 0) := by
  -- Compute the interval endpoint in `Δ¹`, then use functoriality on simplex vertices.
  dsimp [stdTwoSimplexEdgeMap]
  have h : stdSimplexHomeomorphUnitInterval.symm 0 = stdSimplex.vertex (S := ℝ) 0 :=
    stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_zero.symm
  rw [h, stdSimplex.map_vertex]

/-- Helper for Theorem 75.2: the edge opposite `i` ends at its second retained vertex. -/
lemma stdTwoSimplexEdgeMap_one (i : Fin 3) :
    stdTwoSimplexEdgeMap i 1 = stdSimplex.vertex (S := ℝ) (i.succAbove 1) := by
  -- Compute the interval endpoint in `Δ¹`, then use functoriality on simplex vertices.
  dsimp [stdTwoSimplexEdgeMap]
  have h : stdSimplexHomeomorphUnitInterval.symm 1 = stdSimplex.vertex (S := ℝ) 1 :=
    stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_one.symm
  rw [h, stdSimplex.map_vertex]

/-- Helper for Theorem 75.2: the oriented edge of `Δ²` opposite the vertex `i`. -/
noncomputable def stdTwoSimplexEdgePath (i : Fin 3) :
    Path (stdSimplex.vertex (S := ℝ) (i.succAbove 0))
      (stdSimplex.vertex (S := ℝ) (i.succAbove 1)) :=
  -- Package the canonical edge map with the two endpoint computations.
  ⟨stdTwoSimplexEdgeMap i, stdTwoSimplexEdgeMap_zero i, stdTwoSimplexEdgeMap_one i⟩

/-- Helper for Theorem 75.2: the continuous map represented by a singular two-simplex. -/
noncomputable def singularTwoSimplexMap {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) : C(stdSimplex ℝ (Fin 3), X) :=
  -- Use the topological realization adjunction at dimension two.
  TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk 2)) τ

/-- Helper for Theorem 75.2: the source of face `i` is the image of its first vertex. -/
lemma singularEdgeSource_face {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) (i : Fin 3) :
    singularEdgeSource ((TopCat.toSSet.obj (TopCat.of X)).δ i τ) =
      singularTwoSimplexMap τ (stdSimplex.vertex (S := ℝ) (i.succAbove 0)) := by
  -- Evaluate the face restriction at the initial endpoint of the interval.
  dsimp [singularEdgeSource, singularEdgeMap, singularTwoSimplexMap]
  rw [TopCat.toSSetObjEquiv_δ_apply]
  have h : stdSimplexHomeomorphUnitInterval.symm 0 =
      stdSimplex.vertex (S := ℝ) 0 :=
    stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_zero.symm
  rw [h, stdSimplex.map_vertex]

/-- Helper for Theorem 75.2: the target of face `i` is the image of its second vertex. -/
lemma singularEdgeTarget_face {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) (i : Fin 3) :
    singularEdgeTarget ((TopCat.toSSet.obj (TopCat.of X)).δ i τ) =
      singularTwoSimplexMap τ (stdSimplex.vertex (S := ℝ) (i.succAbove 1)) := by
  -- Evaluate the face restriction at the terminal endpoint of the interval.
  dsimp [singularEdgeTarget, singularEdgeMap, singularTwoSimplexMap]
  rw [TopCat.toSSetObjEquiv_δ_apply]
  have h : stdSimplexHomeomorphUnitInterval.symm 1 =
      stdSimplex.vertex (S := ℝ) 1 :=
    stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_one.symm
  rw [h, stdSimplex.map_vertex]

/-- Helper for Theorem 75.2: restricting a singular two-simplex to face `i` gives
the image of the standard edge opposite `i`. -/
lemma singularEdgePath_face {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) (i : Fin 3) :
    singularEdgePath ((TopCat.toSSet.obj (TopCat.of X)).δ i τ) =
      ((stdTwoSimplexEdgePath i).map (singularTwoSimplexMap τ).continuous).cast
        (singularEdgeSource_face τ i) (singularEdgeTarget_face τ i) := by
  -- The adjunction computation rule identifies both parametrized maps pointwise.
  ext t
  dsimp [singularEdgePath, singularEdgeMap, stdTwoSimplexEdgePath,
    stdTwoSimplexEdgeMap, singularTwoSimplexMap]
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rfl

/-- Helper for Theorem 75.2: the direct standard edge from vertex zero to vertex two. -/
noncomputable def stdTwoSimplexDirectPath :
    Path (stdSimplex.vertex (S := ℝ) (0 : Fin 3))
      (stdSimplex.vertex (S := ℝ) (2 : Fin 3)) :=
  -- Face one omits the middle vertex.
  stdTwoSimplexEdgePath 1

/-- Helper for Theorem 75.2: the first standard edge from vertex zero to vertex one. -/
noncomputable def stdTwoSimplexFirstPath :
    Path (stdSimplex.vertex (S := ℝ) (0 : Fin 3))
      (stdSimplex.vertex (S := ℝ) (1 : Fin 3)) :=
  -- Face two retains the first two vertices.
  stdTwoSimplexEdgePath 2

/-- Helper for Theorem 75.2: the second standard edge from vertex one to vertex two. -/
noncomputable def stdTwoSimplexSecondPath :
    Path (stdSimplex.vertex (S := ℝ) (1 : Fin 3))
      (stdSimplex.vertex (S := ℝ) (2 : Fin 3)) :=
  -- Face zero retains the last two vertices.
  stdTwoSimplexEdgePath 0

/-- Helper for Theorem 75.2: the image of a vertex under a singular two-simplex. -/
noncomputable abbrev singularTwoSimplexVertex {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) (j : Fin 3) : X :=
  -- Evaluate the represented continuous simplex map at the chosen vertex.
  singularTwoSimplexMap τ (stdSimplex.vertex (S := ℝ) j)

/-- Helper for Theorem 75.2: face one starts at vertex zero. -/
lemma singularFaceOneSource {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    singularEdgeSource ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) =
      singularTwoSimplexVertex τ 0 := by
  -- Specialize the uniform source formula and normalize `succAbove`.
  simpa [singularTwoSimplexVertex] using singularEdgeSource_face τ 1

/-- Helper for Theorem 75.2: face one ends at vertex two. -/
lemma singularFaceOneTarget {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    singularEdgeTarget ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) =
      singularTwoSimplexVertex τ 2 := by
  -- Specialize the uniform target formula and normalize `succAbove`.
  simpa [singularTwoSimplexVertex] using singularEdgeTarget_face τ 1

/-- Helper for Theorem 75.2: face two starts at vertex zero. -/
lemma singularFaceTwoSource {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    singularEdgeSource ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) =
      singularTwoSimplexVertex τ 0 := by
  -- Specialize the uniform source formula and normalize `succAbove`.
  simpa [singularTwoSimplexVertex] using singularEdgeSource_face τ 2

/-- Helper for Theorem 75.2: face two ends at vertex one. -/
lemma singularFaceTwoTarget {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    singularEdgeTarget ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) =
      singularTwoSimplexVertex τ 1 := by
  -- Record the one `succAbove` computation not discharged by simplification.
  have h : (2 : Fin 3).succAbove (1 : Fin 2) = (1 : Fin 3) := by
    decide
  rw [singularEdgeTarget_face τ 2, singularTwoSimplexVertex, h]

/-- Helper for Theorem 75.2: face zero starts at vertex one. -/
lemma singularFaceZeroSource {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    singularEdgeSource ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) =
      singularTwoSimplexVertex τ 1 := by
  -- Specialize the uniform source formula and normalize `succAbove`.
  simpa [singularTwoSimplexVertex] using singularEdgeSource_face τ 0

/-- Helper for Theorem 75.2: face zero ends at vertex two. -/
lemma singularFaceZeroTarget {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    singularEdgeTarget ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) =
      singularTwoSimplexVertex τ 2 := by
  -- Specialize the uniform target formula and normalize `succAbove`.
  simpa [singularTwoSimplexVertex] using singularEdgeTarget_face τ 0

/-- Helper for Theorem 75.2: face one is the mapped direct standard edge. -/
lemma singularFaceOnePath {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    (singularEdgePath ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ)).cast
        (singularFaceOneSource τ).symm (singularFaceOneTarget τ).symm =
      stdTwoSimplexDirectPath.map (singularTwoSimplexMap τ).continuous := by
  -- Compare the two parametrizations after normalizing to the concrete vertices.
  ext t
  dsimp [singularEdgePath, singularEdgeMap, stdTwoSimplexDirectPath,
    stdTwoSimplexEdgePath, stdTwoSimplexEdgeMap, singularTwoSimplexMap]
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rfl

/-- Helper for Theorem 75.2: face two is the mapped first standard edge. -/
lemma singularFaceTwoPath {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    (singularEdgePath ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)).cast
        (singularFaceTwoSource τ).symm (singularFaceTwoTarget τ).symm =
      stdTwoSimplexFirstPath.map (singularTwoSimplexMap τ).continuous := by
  -- Compare the two parametrizations after normalizing to the concrete vertices.
  ext t
  dsimp [singularEdgePath, singularEdgeMap, stdTwoSimplexFirstPath,
    stdTwoSimplexEdgePath, stdTwoSimplexEdgeMap, singularTwoSimplexMap]
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rfl

/-- Helper for Theorem 75.2: face zero is the mapped second standard edge. -/
lemma singularFaceZeroPath {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    (singularEdgePath ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ)).cast
        (singularFaceZeroSource τ).symm (singularFaceZeroTarget τ).symm =
      stdTwoSimplexSecondPath.map (singularTwoSimplexMap τ).continuous := by
  -- Compare the two parametrizations after normalizing to the concrete vertices.
  ext t
  dsimp [singularEdgePath, singularEdgeMap, stdTwoSimplexSecondPath,
    stdTwoSimplexEdgePath, stdTwoSimplexEdgeMap, singularTwoSimplexMap]
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rfl

/-- Helper for Theorem 75.2: in every singular two-simplex, the direct face-one edge
is homotopic relative endpoints to face two followed by face zero. -/
lemma singularTwoSimplex_edgeComposition {X : Type u} [TopologicalSpace X]
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    ((singularEdgePath ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ)).cast
        (singularFaceOneSource τ).symm (singularFaceOneTarget τ).symm).Homotopic
      (((singularEdgePath ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)).cast
          (singularFaceTwoSource τ).symm (singularFaceTwoTarget τ).symm).trans
        ((singularEdgePath ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ)).cast
          (singularFaceZeroSource τ).symm (singularFaceZeroTarget τ).symm)) := by
  -- Rewrite all three faces to the common geometric normal form.
  rw [singularFaceOnePath, singularFaceTwoPath, singularFaceZeroPath]
  -- Contractibility gives the triangle relation, and path mapping preserves concatenation.
  simpa only [singularTwoSimplexVertex, Path.map_trans] using
    stdTwoSimplex_mappedPathTransHomotopic (singularTwoSimplexMap τ)
      stdTwoSimplexDirectPath stdTwoSimplexFirstPath stdTwoSimplexSecondPath

/-- Helper for Theorem 75.2: endpoint casts normalize the connector-closed loop of a
singular edge without changing its fundamental-group element. -/
lemma basedLoopOfSingularEdge_eq_cast {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) {a b : X}
    (ha : singularEdgeSource σ = a) (hb : singularEdgeTarget σ = b) :
    basedLoopOfSingularEdge x₀ connectors σ =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((connectors a).trans
          (((singularEdgePath σ).cast ha.symm hb.symm).trans (connectors b).symm))) := by
  -- Eliminate the endpoint equalities once, leaving definitionally identical closed paths.
  subst a
  subst b
  rfl

/-- Helper for Theorem 75.2: closing a triangle of endpoint-fixed paths at a basepoint
turns path composition into the corresponding fundamental-group product. -/
lemma basedTriangle_faceRelation {X : Type u} [TopologicalSpace X]
    (x₀ a b c : X) (connectors : ∀ x : X, Path x₀ x)
    (direct : Path a c) (first : Path a b) (second : Path b c)
    (h : direct.Homotopic (first.trans second)) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((connectors a).trans (direct.trans (connectors c).symm))) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((connectors b).trans (second.trans (connectors c).symm))) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((connectors a).trans (first.trans (connectors b).symm))) := by
  -- Work in the path-class presentation, where multiplication is reversed composition.
  change Path.Homotopic.Quotient.mk
      ((connectors a).trans (direct.trans (connectors c).symm)) =
    (Path.Homotopic.Quotient.mk
      ((connectors a).trans (first.trans (connectors b).symm))).trans
      (Path.Homotopic.Quotient.mk
        ((connectors b).trans (second.trans (connectors c).symm)))
  simp only [Path.Homotopic.Quotient.mk_trans]
  rw [Path.Homotopic.Quotient.eq.mpr h]
  rw [Path.Homotopic.Quotient.mk_trans]
  -- Associate the path classes and cancel the middle connector class.
  rw [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_assoc]
  apply congrArg (Path.Homotopic.Quotient.trans
    (Path.Homotopic.Quotient.mk (connectors a)))
  rw [Path.Homotopic.Quotient.trans_assoc]
  apply congrArg (Path.Homotopic.Quotient.trans
    (Path.Homotopic.Quotient.mk first))
  rw [← Path.Homotopic.Quotient.trans_assoc]
  have hcancel :
      (Path.Homotopic.Quotient.mk (connectors b).symm).trans
          (Path.Homotopic.Quotient.mk (connectors b)) =
        Path.Homotopic.Quotient.refl b := by
    simpa only [Path.Homotopic.Quotient.mk_symm] using
      Path.Homotopic.Quotient.symm_trans
        (Path.Homotopic.Quotient.mk (connectors b))
  rw [hcancel, Path.Homotopic.Quotient.refl_trans]

/-- Helper for Theorem 75.2: closing the three faces of a singular two-simplex at a
basepoint turns the triangle homotopy into the corresponding fundamental-group relation. -/
lemma basedLoopOfSingularEdge_faceRelation {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    basedLoopOfSingularEdge x₀ connectors
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) =
      basedLoopOfSingularEdge x₀ connectors
          ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) *
        basedLoopOfSingularEdge x₀ connectors
          ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) := by
  -- Rewrite each face once to the common vertex-normalized spelling.
  rw [basedLoopOfSingularEdge_eq_cast x₀ connectors _ (singularFaceOneSource τ)
      (singularFaceOneTarget τ),
    basedLoopOfSingularEdge_eq_cast x₀ connectors _ (singularFaceZeroSource τ)
      (singularFaceZeroTarget τ),
    basedLoopOfSingularEdge_eq_cast x₀ connectors _ (singularFaceTwoSource τ)
      (singularFaceTwoTarget τ)]
  -- Apply the fixed-endpoint triangle cancellation lemma.
  exact basedTriangle_faceRelation x₀ (singularTwoSimplexVertex τ 0)
    (singularTwoSimplexVertex τ 1) (singularTwoSimplexVertex τ 2) connectors _ _ _
    (singularTwoSimplex_edgeComposition τ)

/-- Helper for Theorem 75.2: after abelianization, the three faces of a singular
two-simplex satisfy the alternating degree-two boundary relation. -/
lemma abelianizedBasedLoop_boundary {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    Additive.ofMul (Abelianization.of (basedLoopOfSingularEdge x₀ connectors
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ))) -
      Additive.ofMul (Abelianization.of (basedLoopOfSingularEdge x₀ connectors
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ))) +
      Additive.ofMul (Abelianization.of (basedLoopOfSingularEdge x₀ connectors
        ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ))) = 0 := by
  -- Map the face relation to the abelianization and read multiplication additively.
  have h := congrArg (fun g => Additive.ofMul (Abelianization.of g))
    (basedLoopOfSingularEdge_faceRelation x₀ connectors τ)
  simp only [map_mul, ofMul_mul] at h
  rw [h]
  abel

/-- Helper for Theorem 75.2: the coefficient copy of `ULift ℤ` indexed by a singular
edge maps its generator to the corresponding abelianized connector-closed loop. -/
noncomputable def singularEdgeCoefficientHom {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    AddCommGrpCat.of (ULift.{u} ℤ) ⟶
      AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x₀))) :=
  -- Use the universal additive homomorphism from the integer coefficient object.
  AddCommGrpCat.ofHom (uliftZMultiplesHom _
    (Additive.ofMul (Abelianization.of (basedLoopOfSingularEdge x₀ connectors σ))))

/-- Helper for Theorem 75.2: evaluating the coefficient morphism at the universal
integer generator recovers the chosen abelianized edge loop. -/
@[simp]
lemma singularEdgeCoefficientHom_generator {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    (AddCommGrpCat.uliftZMultiplesAddEquiv
      (AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x₀)))))
        (singularEdgeCoefficientHom x₀ connectors σ) =
      Additive.ofMul (Abelianization.of (basedLoopOfSingularEdge x₀ connectors σ)) := by
  -- This is the inverse computation rule of the integer-generator equivalence.
  exact (AddCommGrpCat.uliftZMultiplesAddEquiv _).apply_symm_apply _

/-- Helper for Theorem 75.2: degree-one singular chains map generatorwise to the
abelianized connector-closed loops of their singular edges. -/
noncomputable def degreeOneChainsToAbelianization {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (AddCommGrpCat.of (ULift.{u} ℤ))).X 1 ⟶
      AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x₀))) :=
  -- Extend the coefficient morphisms from each coproduct summand.
  ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan
      (AddCommGrpCat.of (ULift.{u} ℤ)) 1).desc
    (Cofan.mk _ (fun σ => singularEdgeCoefficientHom x₀ connectors σ))

/-- Helper for Theorem 75.2: the degree-one chain map has the prescribed value on
every singular-edge coproduct summand. -/
lemma ι_degreeOneChainsToAbelianization {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫
        degreeOneChainsToAbelianization x₀ connectors =
      singularEdgeCoefficientHom x₀ connectors σ := by
  -- Apply the coproduct computation rule at the chosen singular-edge summand.
  exact ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan
    (AddCommGrpCat.of (ULift.{u} ℤ)) 1).fac
      (Cofan.mk _ (fun edge => singularEdgeCoefficientHom x₀ connectors edge))
      ⟨σ⟩

/-- Helper for Theorem 75.2: the degree-two singular differential is killed by the
degree-one chain morphism to the abelianized fundamental group. -/
lemma degreeOneChainsToAbelianization_comp_d {X : Type u} [TopologicalSpace X]
    (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (AddCommGrpCat.of (ULift.{u} ℤ))).d 2 1 ≫
      degreeOneChainsToAbelianization x₀ connectors = 0 := by
  -- It suffices to check the equality on each singular two-simplex generator.
  apply SSet.chainComplex_hom_ext
  intro τ
  rw [← Category.assoc]
  rw [SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    ι_degreeOneChainsToAbelianization, comp_zero]
  -- Evaluate the resulting coefficient morphism at the universal integer generator.
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  simp only [map_sum, map_zsmul, map_zero]
  rw [Fin.sum_univ_three]
  rw [singularEdgeCoefficientHom_generator x₀ connectors
      ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ),
    singularEdgeCoefficientHom_generator x₀ connectors
      ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ),
    singularEdgeCoefficientHom_generator x₀ connectors
      ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)]
  norm_num [sub_eq_add_neg, add_assoc]
  have h := abelianizedBasedLoop_boundary x₀ connectors τ
  simpa only [neg_one_smul, sub_eq_add_neg, add_assoc] using h

/-- Helper for Theorem 75.2: the restriction of the degree-one comparison morphism
to cycles vanishes on degree-one boundaries. -/
lemma degreeOneCyclesToAbelianization_comp_boundaries {X : Type u}
    [TopologicalSpace X] (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    (K.toCycles 2 1 ≫ K.iCycles 1) ≫
      degreeOneChainsToAbelianization x₀ connectors = 0 := by
  -- The cycles inclusion identifies this composite with the incoming differential.
  dsimp only
  rw [HomologicalComplex.toCycles_i]
  exact degreeOneChainsToAbelianization_comp_d x₀ connectors

/-- Helper for Theorem 75.2: the connector-closed edge assignment descends to a
morphism from first singular homology to the abelianized fundamental group. -/
noncomputable def firstHomologyToFundamentalGroupAbelianization {X : Type u}
    [TopologicalSpace X] (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (AddCommGrpCat.of (ULift.{u} ℤ))).homology 1 ⟶
      AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x₀))) :=
  -- Descend the cycle restriction through the cokernel defining first homology.
  let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
    (AddCommGrpCat.of (ULift.{u} ℤ))
  (K.homologyIsCokernel 2 1 (ChainComplex.prev ℕ 1)).desc
    (CokernelCofork.ofπ
      (K.iCycles 1 ≫ degreeOneChainsToAbelianization x₀ connectors)
      (degreeOneCyclesToAbelianization_comp_boundaries x₀ connectors))

/-- Helper for Theorem 75.2: composing the homology projection with the descended
comparison map recovers its restriction to degree-one cycles. -/
lemma homologyπ_firstHomologyToFundamentalGroupAbelianization {X : Type u}
    [TopologicalSpace X] (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    K.homologyπ 1 ≫ firstHomologyToFundamentalGroupAbelianization x₀ connectors =
      K.iCycles 1 ≫ degreeOneChainsToAbelianization x₀ connectors := by
  -- Apply the cokernel computation rule for the descended homology morphism.
  dsimp [firstHomologyToFundamentalGroupAbelianization]
  exact (((TopCat.toSSet.obj (TopCat.of X)).chainComplex
    (AddCommGrpCat.of (ULift.{u} ℤ))).homologyIsCokernel 2 1
      (ChainComplex.prev ℕ 1)).fac
    (CokernelCofork.ofπ
      (((TopCat.toSSet.obj (TopCat.of X)).chainComplex
          (AddCommGrpCat.of (ULift.{u} ℤ))).iCycles 1 ≫
        degreeOneChainsToAbelianization x₀ connectors)
      (degreeOneCyclesToAbelianization_comp_boundaries x₀ connectors))
    WalkingParallelPair.one

/-- Helper for Theorem 75.2: the reverse comparison sends a based-loop homology
class to the abelianized connector closure of its singular edge. -/
lemma firstHomologyToFundamentalGroupAbelianization_basedLoopClass
    {X : Type u} [TopologicalSpace X] (x₀ : X)
    (connectors : ∀ x : X, Path x₀ x) (p : Path x₀ x₀) :
    firstHomologyToFundamentalGroupAbelianization x₀ connectors
        (basedLoopHomologyClass p) =
      Additive.ofMul (Abelianization.of
        (basedLoopOfSingularEdge x₀ connectors (pathSingularSimplex p))) := by
  -- Move evaluation to the coefficient morphism and follow it through cycles and homology.
  unfold basedLoopHomologyClass
  dsimp only
  calc
    _ = AddCommGrpCat.uliftZMultiplesAddEquiv _
          (basedLoopHomologyCoefficient p ≫
            firstHomologyToFundamentalGroupAbelianization x₀ connectors) :=
      (uliftZMultiplesAddEquiv_comp _ _).symm
    _ = _ := by
      unfold basedLoopHomologyCoefficient
      rw [Category.assoc,
        homologyπ_firstHomologyToFundamentalGroupAbelianization]
      rw [← Category.assoc, basedLoopCycle_iCycles]
      rw [ι_degreeOneChainsToAbelianization,
        singularEdgeCoefficientHom_generator]

/-- Helper for Theorem 75.2: closing a represented based loop by a chosen basepoint
connector does not change its class after abelianization. -/
lemma abelianization_basedLoopOf_pathSingularSimplex {X : Type u}
    [TopologicalSpace X] (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (p : Path x₀ x₀) :
    Abelianization.of
        (basedLoopOfSingularEdge x₀ connectors (pathSingularSimplex p)) =
      Abelianization.of
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) := by
  -- Normalize the singular edge back to `p`, leaving conjugation by the base connector.
  rw [basedLoopOfSingularEdge_eq_cast x₀ connectors _
    (singularEdgeSource_pathSingularSimplex p)
    (singularEdgeTarget_pathSingularSimplex p)]
  rw [singularEdgePath_pathSingularSimplex_cast]
  let c : FundamentalGroup X x₀ :=
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (connectors x₀))
  let g : FundamentalGroup X x₀ :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)
  change Abelianization.of (c⁻¹ * g * c) = Abelianization.of g
  -- The target is commutative, so conjugation disappears.
  rw [map_mul, map_mul, map_inv]
  rw [mul_assoc, mul_comm (Abelianization.of g) (Abelianization.of c),
    ← mul_assoc, inv_mul_cancel, one_mul]

/-- Helper for Theorem 75.2: the reverse comparison is a left inverse of the
abelianized degree-one Hurewicz map. -/
lemma firstHomologyToFundamentalGroupAbelianization_hurewicz_leftInverse
    {X : Type u} [TopologicalSpace X] (x₀ : X)
    (connectors : ∀ x : X, Path x₀ x)
    (a : Additive (Abelianization (FundamentalGroup X x₀))) :
    firstHomologyToFundamentalGroupAbelianization x₀ connectors
        (abelianizedDegreeOneHurewiczHom x₀ a) = a := by
  -- Reduce first to a fundamental-group element and then to a path representative.
  refine QuotientGroup.induction_on a ?_
  intro g
  refine Quotient.inductionOn g ?_
  intro p
  change firstHomologyToFundamentalGroupAbelianization x₀ connectors
      (abelianizedDegreeOneHurewiczHom x₀
        (Additive.ofMul (Abelianization.of
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))))) =
    Additive.ofMul (Abelianization.of
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)))
  rw [abelianizedDegreeOneHurewiczHom_of,
    degreeOneHurewiczHom_fromPath,
    firstHomologyToFundamentalGroupAbelianization_basedLoopClass]
  exact congrArg Additive.ofMul
    (abelianization_basedLoopOf_pathSingularSimplex x₀ connectors p)

/-- Helper for Theorem 75.2: applying the abelianized Hurewicz map to the
generatorwise closed-edge assignment recovers connector closure in homology. -/
lemma degreeOneChainsToAbelianization_comp_hurewicz {X : Type u}
    [TopologicalSpace X] (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    degreeOneChainsToAbelianization x₀ connectors ≫
        abelianizedDegreeOneHurewiczMorphism x₀ =
      closedEdgeChainsToCycles x₀ connectors ≫ K.homologyπ 1 := by
  -- Check the equality on each singular-edge coproduct generator.
  dsimp only
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_degreeOneChainsToAbelianization]
  -- Evaluate both coefficient morphisms at the universal lifted integer generator.
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  rw [uliftZMultiplesAddEquiv_comp,
    singularEdgeCoefficientHom_generator]
  rw [abelianizedDegreeOneHurewiczMorphism_apply,
    abelianizedDegreeOneHurewiczHom_of]
  unfold basedLoopOfSingularEdge
  rw [degreeOneHurewiczHom_fromPath]
  unfold basedLoopHomologyClass
  rw [basedLoopHomologyCoefficient_connectorClosedEdge]
  rw [Category.assoc]

/-- Helper for Theorem 75.2: the abelianized Hurewicz morphism is also a left
inverse of the reverse first-homology comparison. -/
lemma abelianizedDegreeOneHurewiczMorphism_comp_reverse {X : Type u}
    [TopologicalSpace X] (x₀ : X) (connectors : ∀ x : X, Path x₀ x) :
    firstHomologyToFundamentalGroupAbelianization x₀ connectors ≫
        abelianizedDegreeOneHurewiczMorphism x₀ = 𝟙 _ := by
  -- Cancel the epimorphic homology projection and compute on cycle representatives.
  let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
    (AddCommGrpCat.of (ULift.{u} ℤ))
  rw [← cancel_epi (K.homologyπ 1)]
  rw [← Category.assoc,
    homologyπ_firstHomologyToFundamentalGroupAbelianization]
  rw [Category.assoc, degreeOneChainsToAbelianization_comp_hurewicz]
  rw [← Category.assoc, iCycles_closedEdgeChainsToCycles,
    Category.id_comp, Category.comp_id]

/-- Helper for Theorem 75.2: the abelianized Hurewicz homomorphism sends the
reverse comparison of any first-homology class back to that class. -/
lemma abelianizedDegreeOneHurewiczHom_reverse {X : Type u}
    [TopologicalSpace X] (x₀ : X) (connectors : ∀ x : X, Path x₀ x)
    (h : ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))).homology 1) :
    abelianizedDegreeOneHurewiczHom x₀
        (firstHomologyToFundamentalGroupAbelianization x₀ connectors h) = h := by
  -- Evaluate the categorical inverse identity at `h`.
  have hinverse := ConcreteCategory.congr_hom
    (abelianizedDegreeOneHurewiczMorphism_comp_reverse x₀ connectors) h
  exact hinverse

/-- Helper for Theorem 75.2: a degree-one Hurewicz homomorphism has the two algebraic
properties needed to identify first homology with the abelianized fundamental group. -/
def IsDegreeOneHurewiczMap {X : Type u} [TopologicalSpace X] (x₀ : X)
    (φ : FundamentalGroup X x₀ →*
      Multiplicative (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))).obj (TopCat.of X))) : Prop :=
  Function.Surjective φ ∧ φ.ker = commutator (FundamentalGroup X x₀)

/-- Helper for Theorem 75.2: the degree-one Hurewicz homomorphism exists for a
path-connected space. -/
lemma existsDegreeOneHurewiczMap {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x₀ : X) :
    ∃ φ : FundamentalGroup X x₀ →*
      Multiplicative (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))).obj (TopCat.of X)),
      IsDegreeOneHurewiczMap x₀ φ := by
  -- Use the chosen path-connectedness connectors in both comparison maps.
  let connectors : ∀ x : X, Path x₀ x := PathConnectedSpace.somePath x₀
  refine ⟨degreeOneHurewiczFunctorHom x₀, ?_, ?_⟩
  · -- The reverse comparison supplies a preimage after lifting through abelianization.
    intro h
    let a : Abelianization (FundamentalGroup X x₀) :=
      Additive.toMul
        (firstHomologyToFundamentalGroupAbelianization x₀ connectors h)
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
      (commutator (FundamentalGroup X x₀)) a
    have hga : Additive.ofMul (Abelianization.of g) =
        firstHomologyToFundamentalGroupAbelianization x₀ connectors h := by
      exact congrArg Additive.ofMul hg
    refine ⟨g, ?_⟩
    rw [degreeOneHurewiczFunctorHom_factor, hga]
    exact abelianizedDegreeOneHurewiczHom_reverse x₀ connectors h
  · -- The left inverse makes the abelianized Hurewicz factor injective.
    let K := (TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (AddCommGrpCat.of (ULift.{u} ℤ))
    have hleft : Function.LeftInverse
        (fun h : K.homology 1 ↦
          firstHomologyToFundamentalGroupAbelianization x₀ connectors h)
        (abelianizedDegreeOneHurewiczHom x₀) := by
      intro a
      exact firstHomologyToFundamentalGroupAbelianization_hurewicz_leftInverse
        x₀ connectors a
    have hinjective : Function.Injective
        (abelianizedDegreeOneHurewiczHom x₀) := hleft.injective
    rw [← Abelianization.ker_of (FundamentalGroup X x₀)]
    ext g
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hg
      have hzero : abelianizedDegreeOneHurewiczHom x₀
          (Additive.ofMul (Abelianization.of g)) = 0 := by
        calc
          _ = degreeOneHurewiczFunctorHom x₀ g :=
            (degreeOneHurewiczFunctorHom_factor x₀ g).symm
          _ = (0 : K.homology 1) := hg
      have hfactor : abelianizedDegreeOneHurewiczHom x₀
          (Additive.ofMul (Abelianization.of g)) =
          abelianizedDegreeOneHurewiczHom x₀ 0 := by
        calc
          _ = 0 := hzero
          _ = _ := (map_zero _).symm
      exact hinjective hfactor
    · intro hg
      have htag : Additive.ofMul (Abelianization.of g) = 0 := by
        exact congrArg Additive.ofMul hg
      have hone : (0 : Additive (Abelianization (FundamentalGroup X x₀))) =
          Additive.ofMul (Abelianization.of (1 : FundamentalGroup X x₀)) := by
        rw [map_one]
        rfl
      have halpha : abelianizedDegreeOneHurewiczHom x₀
          (Additive.ofMul (Abelianization.of g)) =
          abelianizedDegreeOneHurewiczHom x₀
            (Additive.ofMul
              (Abelianization.of (1 : FundamentalGroup X x₀))) := by
        calc
          _ = abelianizedDegreeOneHurewiczHom x₀ 0 := congrArg _ htag
          _ = _ := congrArg _ hone
      have hfunctor : degreeOneHurewiczFunctorHom x₀ g =
          degreeOneHurewiczFunctorHom x₀ 1 :=
        (degreeOneHurewiczFunctorHom_factor x₀ g).trans
          (halpha.trans (degreeOneHurewiczFunctorHom_factor x₀ 1).symm)
      exact hfunctor.trans (map_one _)

/-- Theorem 75.2. For a path-connected space `X`, there exists an isomorphism from
the first singular homology group `H₁(X; ℤ)` to the additive form of the abelianization
of `FundamentalGroup X x₀`. -/
theorem firstHomologyIsoAbelianization {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x₀ : X) :
    Nonempty
      (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))).obj (TopCat.of X) ≅
        AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup X x₀)))) := by
  -- Obtain the comparison map and retain only its first-isomorphism-theorem interface.
  obtain ⟨φ, hsurjective, hker⟩ := existsDegreeOneHurewiczMap x₀
  -- The algebraic quotient argument supplies the required categorical isomorphism.
  exact ⟨(addEquivAbelianizationOfSurjectiveKer φ hsurjective hker).toAddCommGrpIso⟩

end AlgebraicTopology

end
