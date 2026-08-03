module

public import Topology_Munkres_2000.Book.Remark_60_1.AntipodalParity
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

public section

noncomputable section

namespace AlgebraicTopology

open unitInterval

/-- Helper for Remark 60.1: regard an untyped interval map as a path between
its own endpoints. -/
def continuousMapToPath {X : Type} [TopologicalSpace X]
    (γ : C(I, X)) : Path (γ 0) (γ 1) :=
  ⟨γ, rfl, rfl⟩

/-- Helper for Remark 60.1: monodromy of an interval map has the canonical
lifted endpoint as its underlying point. -/
lemma coe_monodromy_continuousMapToPath
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p)
    (s : ∀ x : X, p ⁻¹' {x}) (γ : C(I, X)) :
    (hp.monodromy (Path.Homotopic.Quotient.mk (continuousMapToPath γ))
        (s (γ 0)) : E) =
      hp.liftPath γ (s (γ 0) : E)
        (chosenFiberPoint_projects p s (γ 0)).symm 1 := by
  -- Unfolding monodromy on a represented path exposes the same lifted endpoint.
  rfl

/-- Helper for Remark 60.1: the Boolean transition is the fiber coordinate of
covering monodromy applied to the chosen source lift. -/
lemma boolCoverPathTransition_eq_fiberEquiv_monodromy
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x}) (γ : C(I, X)) :
    boolCoverPathTransition p hp s γ =
      hp.fiberEquivAddGroup (s (γ 1))
        (hp.isCoveringMap.monodromy
          (Path.Homotopic.Quotient.mk (continuousMapToPath γ)) (s (γ 0))) := by
  -- The fiber-coordinate specification turns the monodromy endpoint into the
  -- required deck translate of the chosen terminal point.
  apply boolCoverPathTransition_eq_of_endpoint
  calc
    hp.isCoveringMap.liftPath γ (s (γ 0) : E)
        (chosenFiberPoint_projects p s (γ 0)).symm 1 =
        (hp.isCoveringMap.monodromy
          (Path.Homotopic.Quotient.mk (continuousMapToPath γ)) (s (γ 0)) : E) :=
      (coe_monodromy_continuousMapToPath hp.isCoveringMap s γ).symm
    _ = hp.fiberEquivAddGroup (s (γ 1))
          (hp.isCoveringMap.monodromy
            (Path.Homotopic.Quotient.mk (continuousMapToPath γ))
              (s (γ 0))) +ᵥ (s (γ 1) : E) :=
      (hp.fiberEquivAddGroup_eq_iff (s (γ 1))
        (hp.isCoveringMap.monodromy
          (Path.Homotopic.Quotient.mk (continuousMapToPath γ))
            (s (γ 0))) _).mp rfl

/-- Helper for Remark 60.1: the monodromy coordinate of a typed path in a
Boolean quotient cover. -/
noncomputable def boolCoverMonodromyTransition
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x}) {x y : X} (γ : Path x y) : Bool :=
  hp.fiberEquivAddGroup (s y)
    (hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) (s x))

/-- Helper for Remark 60.1: homotopic typed paths have the same Boolean
monodromy transition. -/
lemma boolCoverMonodromyTransition_eq_of_homotopic
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x}) {x y : X} (γ γ' : Path x y)
    (h : Path.Homotopic γ γ') :
    boolCoverMonodromyTransition p hp s γ =
      boolCoverMonodromyTransition p hp s γ' := by
  -- Monodromy factors through the relative-endpoint path-homotopy quotient.
  unfold boolCoverMonodromyTransition
  exact congrArg (fun q : Path.Homotopic.Quotient x y ↦
    hp.fiberEquivAddGroup (s y) (hp.isCoveringMap.monodromy q (s x)))
    ((Path.Homotopic.Quotient.eq).mpr h)

/-- Helper for Remark 60.1: the lift-defined transition of a typed path agrees
with its monodromy fiber coordinate. -/
lemma boolCoverPathTransition_toContinuousMap
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x}) {x y : X} (γ : Path x y) :
    boolCoverPathTransition p hp s γ.toContinuousMap =
      boolCoverMonodromyTransition p hp s γ := by
  -- Normalize the endpoint indices, then apply the untyped monodromy bridge;
  -- path proof fields disappear by proof irrelevance.
  rcases γ with ⟨γ, hzero, hone⟩
  subst x
  subst y
  simpa [boolCoverMonodromyTransition, continuousMapToPath] using
    boolCoverPathTransition_eq_fiberEquiv_monodromy p hp s γ

/-- Helper for Remark 60.1: monodromy commutes with Boolean deck translation
after forgetting fiber membership proofs. -/
lemma coe_monodromy_toPermFiber
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    {p : E → X} (hp : IsAddQuotientCoveringMap p Bool)
    {x y : X} (γ : Path.Homotopic.Quotient x y)
    (b : Bool) (e : p ⁻¹' {x}) :
    (hp.isCoveringMap.monodromy γ
        (hp.toMultiplicative.toPermFiber x b e) : E) =
      b +ᵥ (hp.isCoveringMap.monodromy γ e : E) := by
  -- Apply the quotient-cover monodromy equivariance theorem and project to
  -- the total space, where the restricted action computes to `vadd`.
  exact congrArg Subtype.val (hp.monodromy_toPermFiber (γ := γ) (e := e) (g := b))

/-- Helper for Remark 60.1: the monodromy transition is additive under path
concatenation. -/
lemma boolCoverMonodromyTransition_trans
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x}) {x y z : X}
    (γ : Path x y) (γ' : Path y z) :
    boolCoverMonodromyTransition p hp s (γ.trans γ') =
      boolCoverMonodromyTransition p hp s γ +
        boolCoverMonodromyTransition p hp s γ' := by
  -- Name the two edge coordinates so the monodromy calculation stays at the
  -- canonical fiber level.
  let b := boolCoverMonodromyTransition p hp s γ
  let b' := boolCoverMonodromyTransition p hp s γ'
  have hγ : hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) (s x) =
      hp.toMultiplicative.toPermFiber y b (s y) := by
    apply Subtype.ext
    exact (hp.fiberEquivAddGroup_eq_iff (s y)
      (hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) (s x)) b).mp rfl
  have hγ' : (hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk γ') (s y) : E) =
      b' +ᵥ (s z : E) := by
    exact (hp.fiberEquivAddGroup_eq_iff (s z)
      (hp.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk γ') (s y)) b').mp rfl
  -- Composition of monodromy first follows the second edge, while deck
  -- equivariance moves the first edge's coordinate through that monodromy.
  apply (hp.fiberEquivAddGroup_eq_iff (s z)
    (hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (γ.trans γ')) (s x)) (b + b')).mpr
  calc
    (hp.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk (γ.trans γ')) (s x) : E) =
        (hp.isCoveringMap.monodromy
          ((Path.Homotopic.Quotient.mk γ).trans
            (Path.Homotopic.Quotient.mk γ')) (s x) : E) :=
      congrArg (fun q : Path.Homotopic.Quotient x z ↦
        (hp.isCoveringMap.monodromy q (s x) : E))
        (Path.Homotopic.Quotient.mk_trans γ γ')
    _ = (hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ')
        (hp.isCoveringMap.monodromy
          (Path.Homotopic.Quotient.mk γ) (s x)) : E) :=
      congrArg Subtype.val
        (hp.isCoveringMap.monodromy_trans_apply
          (Path.Homotopic.Quotient.mk γ)
          (Path.Homotopic.Quotient.mk γ') (s x))
    _ = (hp.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ')
        (hp.toMultiplicative.toPermFiber y b (s y)) : E) :=
      congrArg (fun e : p ⁻¹' {y} ↦
        (hp.isCoveringMap.monodromy
          (Path.Homotopic.Quotient.mk γ') e : E)) hγ
    _ = b +ᵥ (hp.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk γ') (s y) : E) :=
      coe_monodromy_toPermFiber hp (Path.Homotopic.Quotient.mk γ') b (s y)
    _ = b +ᵥ (b' +ᵥ (s z : E)) := congrArg (fun e : E ↦ b +ᵥ e) hγ'
    _ = (b + b') +ᵥ (s z : E) := (add_vadd b b' (s z : E)).symm

/-- Helper for Remark 60.1: the canonical interval parametrization of the
`i`th face of the standard topological two-simplex. -/
noncomputable def standardTwoSimplexFaceInterval (i : Fin 3) :
    C(I, stdSimplex ℝ (Fin 3)) :=
  (⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩ :
      C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 3))).comp
    ((toContinuousMap TopCat.stdSimplexHomeomorphI.{0}.symm).comp
      (toContinuousMap TopCat.I.homeomorph.{0}.symm))

/-- Helper for Remark 60.1: the canonical face interval starts at the first
vertex not omitted by that face. -/
lemma standardTwoSimplexFaceInterval_zero (i : Fin 3) :
    standardTwoSimplexFaceInterval i 0 =
      stdSimplex.vertex (i.succAbove 0) := by
  -- Evaluate the two interval homeomorphisms at zero, then map the vertex.
  have hzero : TopCat.I.homeomorph.{0}.symm (0 : I) = (0 : TopCat.I.{0}) := rfl
  unfold standardTwoSimplexFaceInterval
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
  calc
    stdSimplex.map i.succAbove
        (TopCat.stdSimplexHomeomorphI.{0}.symm
          (TopCat.I.homeomorph.{0}.symm 0)) =
        stdSimplex.map i.succAbove
          (TopCat.stdSimplexHomeomorphI.{0}.symm 0) :=
      congrArg (fun t : TopCat.I.{0} ↦
        stdSimplex.map i.succAbove
          (TopCat.stdSimplexHomeomorphI.{0}.symm t)) hzero
    _ = stdSimplex.vertex (i.succAbove 0) := by
      rw [TopCat.stdSimplexHomeomorphI_symm_zero, stdSimplex.map_vertex]

/-- Helper for Remark 60.1: the canonical face interval ends at the second
vertex not omitted by that face. -/
lemma standardTwoSimplexFaceInterval_one (i : Fin 3) :
    standardTwoSimplexFaceInterval i 1 =
      stdSimplex.vertex (i.succAbove 1) := by
  -- Evaluate the two interval homeomorphisms at one, then map the vertex.
  have hone : TopCat.I.homeomorph.{0}.symm (1 : I) = (1 : TopCat.I.{0}) := rfl
  unfold standardTwoSimplexFaceInterval
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
  calc
    stdSimplex.map i.succAbove
        (TopCat.stdSimplexHomeomorphI.{0}.symm
          (TopCat.I.homeomorph.{0}.symm 1)) =
        stdSimplex.map i.succAbove
          (TopCat.stdSimplexHomeomorphI.{0}.symm 1) :=
      congrArg (fun t : TopCat.I.{0} ↦
        stdSimplex.map i.succAbove
          (TopCat.stdSimplexHomeomorphI.{0}.symm t)) hone
    _ = stdSimplex.vertex (i.succAbove 1) := by
      rw [TopCat.stdSimplexHomeomorphI_symm_one, stdSimplex.map_vertex]

/-- Helper for Remark 60.1: the diagonal and first boundary edge start at the
same vertex of the standard two-simplex. -/
lemma standardTwoSimplex_faceOneZero_eq_faceTwoZero :
    standardTwoSimplexFaceInterval 1 0 =
      standardTwoSimplexFaceInterval 2 0 := by
  -- Both endpoints normalize to vertex zero.
  rw [standardTwoSimplexFaceInterval_zero,
    standardTwoSimplexFaceInterval_zero]
  exact congrArg stdSimplex.vertex (by decide)

/-- Helper for Remark 60.1: the first boundary edge ends where the second
boundary edge starts. -/
lemma standardTwoSimplex_faceTwoOne_eq_faceZeroZero :
    standardTwoSimplexFaceInterval 2 1 =
      standardTwoSimplexFaceInterval 0 0 := by
  -- Both endpoints normalize to vertex one.
  rw [standardTwoSimplexFaceInterval_one,
    standardTwoSimplexFaceInterval_zero]
  exact congrArg stdSimplex.vertex (by decide)

/-- Helper for Remark 60.1: the diagonal and second boundary edge end at the
same vertex of the standard two-simplex. -/
lemma standardTwoSimplex_faceOneOne_eq_faceZeroOne :
    standardTwoSimplexFaceInterval 1 1 =
      standardTwoSimplexFaceInterval 0 1 := by
  -- Both endpoints normalize to vertex two.
  rw [standardTwoSimplexFaceInterval_one,
    standardTwoSimplexFaceInterval_one]
  exact congrArg stdSimplex.vertex (by decide)

/-- Helper for Remark 60.1: the first standard boundary edge, with endpoints
chosen to compose with the diagonal and second edge. -/
noncomputable def standardTwoSimplexFirstBoundaryPath :
    Path (standardTwoSimplexFaceInterval 1 0)
      (standardTwoSimplexFaceInterval 2 1) :=
  (continuousMapToPath (standardTwoSimplexFaceInterval 2)).cast
    standardTwoSimplex_faceOneZero_eq_faceTwoZero rfl

/-- Helper for Remark 60.1: the second standard boundary edge, with endpoints
chosen to compose with the first edge and compare with the diagonal. -/
noncomputable def standardTwoSimplexSecondBoundaryPath :
    Path (standardTwoSimplexFaceInterval 2 1)
      (standardTwoSimplexFaceInterval 1 1) :=
  (continuousMapToPath (standardTwoSimplexFaceInterval 0)).cast
    standardTwoSimplex_faceTwoOne_eq_faceZeroZero
    standardTwoSimplex_faceOneOne_eq_faceZeroOne

/-- Helper for Remark 60.1: in the standard two-simplex, the two-edge
boundary route is homotopic relative endpoints to the diagonal. -/
lemma standardTwoSimplex_boundary_homotopic_diagonal :
    Path.Homotopic
      (standardTwoSimplexFirstBoundaryPath.trans
        standardTwoSimplexSecondBoundaryPath)
      (continuousMapToPath (standardTwoSimplexFaceInterval 1)) := by
  have hnonempty : (stdSimplex ℝ (Fin 3) : Set (Fin 3 → ℝ)).Nonempty :=
    ⟨stdSimplex.vertex 0, (stdSimplex.vertex 0).property⟩
  -- Local instance justification (regularity): convexity supplies the
  -- contractible structure used only for this standard-simplex homotopy.
  letI : ContractibleSpace (stdSimplex ℝ (Fin 3)) :=
    (convex_stdSimplex ℝ (Fin 3)).contractibleSpace hnonempty
  -- Simple connectedness of a contractible simplex identifies the two paths.
  exact SimplyConnectedSpace.paths_homotopic _ _

/-- Helper for Remark 60.1: extract the continuous map represented by a
singular two-simplex. -/
noncomputable def singularTwoSimplexMap
    {X : Type} [TopologicalSpace X]
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    C(stdSimplex ℝ (Fin 3), X) :=
  (TopCat.of X).toSSetObjEquiv _ simplex

/-- Helper for Remark 60.1: a face edge of a singular two-simplex factors
through the corresponding canonical edge of the standard two-simplex. -/
lemma singularTwoSimplex_faceInterval
    {X : Type} [TopologicalSpace X]
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) (i : Fin 3) :
    topCatIntervalMorphismToPath
        (TopCat.toSSetObj₁Equiv
          ((TopCat.toSSet.obj (TopCat.of X)).δ i simplex)) =
      (singularTwoSimplexMap simplex).comp
        (standardTwoSimplexFaceInterval i) := by
  -- Naturality of the singular-simplex equivalence identifies the face map
  -- pointwise with precomposition by `i.succAbove`.
  ext t
  rw [topCatIntervalMorphismToPath_toSSetObj₁Equiv_apply.{0},
    TopCat.toSSetObjEquiv_δ_apply]
  rfl

/-- Helper for Remark 60.1: map the first standard boundary edge through a
singular two-simplex. -/
noncomputable def singularTwoSimplexFirstBoundaryPath
    {X : Type} [TopologicalSpace X]
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :=
  standardTwoSimplexFirstBoundaryPath.map
    (singularTwoSimplexMap simplex).continuous

/-- Helper for Remark 60.1: map the second standard boundary edge through a
singular two-simplex. -/
noncomputable def singularTwoSimplexSecondBoundaryPath
    {X : Type} [TopologicalSpace X]
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :=
  standardTwoSimplexSecondBoundaryPath.map
    (singularTwoSimplexMap simplex).continuous

/-- Helper for Remark 60.1: map the standard diagonal through a singular
two-simplex. -/
noncomputable def singularTwoSimplexDiagonalPath
    {X : Type} [TopologicalSpace X]
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :=
  (continuousMapToPath (standardTwoSimplexFaceInterval 1)).map
    (singularTwoSimplexMap simplex).continuous

/-- Helper for Remark 60.1: the mapped first boundary path has the same
underlying interval map as face two of the singular simplex. -/
lemma singularTwoSimplexFirstBoundaryPath_toContinuousMap
    {X : Type} [TopologicalSpace X]
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    (singularTwoSimplexFirstBoundaryPath simplex).toContinuousMap =
      topCatIntervalMorphismToPath
        (TopCat.toSSetObj₁Equiv
          ((TopCat.toSSet.obj (TopCat.of X)).δ 2 simplex)) := by
  -- Forgetting endpoint casts leaves exactly the standard face-two interval.
  calc
    (singularTwoSimplexFirstBoundaryPath simplex).toContinuousMap =
        (singularTwoSimplexMap simplex).comp
          (standardTwoSimplexFaceInterval 2) := by
      apply ContinuousMap.ext
      intro t
      rfl
    _ = topCatIntervalMorphismToPath
        (TopCat.toSSetObj₁Equiv
          ((TopCat.toSSet.obj (TopCat.of X)).δ 2 simplex)) :=
      (singularTwoSimplex_faceInterval simplex 2).symm

/-- Helper for Remark 60.1: the mapped second boundary path has the same
underlying interval map as face zero of the singular simplex. -/
lemma singularTwoSimplexSecondBoundaryPath_toContinuousMap
    {X : Type} [TopologicalSpace X]
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    (singularTwoSimplexSecondBoundaryPath simplex).toContinuousMap =
      topCatIntervalMorphismToPath
        (TopCat.toSSetObj₁Equiv
          ((TopCat.toSSet.obj (TopCat.of X)).δ 0 simplex)) := by
  -- Forgetting endpoint casts leaves exactly the standard face-zero interval.
  calc
    (singularTwoSimplexSecondBoundaryPath simplex).toContinuousMap =
        (singularTwoSimplexMap simplex).comp
          (standardTwoSimplexFaceInterval 0) := by
      apply ContinuousMap.ext
      intro t
      rfl
    _ = topCatIntervalMorphismToPath
        (TopCat.toSSetObj₁Equiv
          ((TopCat.toSSet.obj (TopCat.of X)).δ 0 simplex)) :=
      (singularTwoSimplex_faceInterval simplex 0).symm

/-- Helper for Remark 60.1: the mapped diagonal path has the same underlying
interval map as face one of the singular simplex. -/
lemma singularTwoSimplexDiagonalPath_toContinuousMap
    {X : Type} [TopologicalSpace X]
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    (singularTwoSimplexDiagonalPath simplex).toContinuousMap =
      topCatIntervalMorphismToPath
        (TopCat.toSSetObj₁Equiv
          ((TopCat.toSSet.obj (TopCat.of X)).δ 1 simplex)) := by
  -- The diagonal has no endpoint casts, so this is the face-one factorization.
  calc
    (singularTwoSimplexDiagonalPath simplex).toContinuousMap =
        (singularTwoSimplexMap simplex).comp
          (standardTwoSimplexFaceInterval 1) := by
      apply ContinuousMap.ext
      intro t
      rfl
    _ = topCatIntervalMorphismToPath
        (TopCat.toSSetObj₁Equiv
          ((TopCat.toSSet.obj (TopCat.of X)).δ 1 simplex)) :=
      (singularTwoSimplex_faceInterval simplex 1).symm

/-- Helper for Remark 60.1: the two mapped boundary faces of a singular
two-simplex are homotopic relative endpoints to its diagonal face. -/
lemma singularTwoSimplex_facePath_homotopic
    {X : Type} [TopologicalSpace X]
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    Path.Homotopic
      ((singularTwoSimplexFirstBoundaryPath simplex).trans
        (singularTwoSimplexSecondBoundaryPath simplex))
      (singularTwoSimplexDiagonalPath simplex) := by
  -- Map the standard-simplex homotopy through the represented singular map,
  -- then normalize mapping across path concatenation.
  have hmapped := standardTwoSimplex_boundary_homotopic_diagonal.map
    (singularTwoSimplexMap simplex)
  unfold singularTwoSimplexFirstBoundaryPath
    singularTwoSimplexSecondBoundaryPath singularTwoSimplexDiagonalPath
  simpa only [Path.map_trans] using hmapped

/-- Helper for Remark 60.1: after identifying a typed path with a singular
face's interval map, its monodromy transition computes the edge transition. -/
lemma boolCoverEdgeTransition_eq_monodromyTransition
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x})
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) (i : Fin 3)
    {x y : X} (γ : Path x y)
    (hγ : γ.toContinuousMap =
      topCatIntervalMorphismToPath
        (TopCat.toSSetObj₁Equiv
          ((TopCat.toSSet.obj (TopCat.of X)).δ i simplex))) :
    boolCoverEdgeTransition p hp s
        ((TopCat.toSSet.obj (TopCat.of X)).δ i simplex) =
      boolCoverMonodromyTransition p hp s γ := by
  -- Cross from the simplicial edge API to its interval map once, replace that
  -- map by the typed path, and apply the lift-to-monodromy adapter.
  calc
    boolCoverEdgeTransition p hp s
        ((TopCat.toSSet.obj (TopCat.of X)).δ i simplex) =
        boolCoverPathTransition p hp s
          (topCatIntervalMorphismToPath
            (TopCat.toSSetObj₁Equiv
              ((TopCat.toSSet.obj (TopCat.of X)).δ i simplex))) :=
      boolCoverEdgeTransition_eq_pathTransition p hp s _
    _ = boolCoverPathTransition p hp s γ.toContinuousMap :=
      congrArg (boolCoverPathTransition p hp s) hγ.symm
    _ = boolCoverMonodromyTransition p hp s γ :=
      boolCoverPathTransition_toContinuousMap p hp s γ

/-- Helper for Remark 60.1: Boolean edge transitions satisfy the triangle
identity on every singular two-simplex. -/
lemma boolCoverEdgeTransition_triangle
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x})
    (simplex : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 2))) :
    boolCoverEdgeTransition p hp s
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 simplex) =
      boolCoverEdgeTransition p hp s
          ((TopCat.toSSet.obj (TopCat.of X)).δ 0 simplex) +
        boolCoverEdgeTransition p hp s
          ((TopCat.toSSet.obj (TopCat.of X)).δ 2 simplex) := by
  have hfirst := boolCoverEdgeTransition_eq_monodromyTransition p hp s
    simplex 2 (singularTwoSimplexFirstBoundaryPath simplex)
      (singularTwoSimplexFirstBoundaryPath_toContinuousMap simplex)
  have hsecond := boolCoverEdgeTransition_eq_monodromyTransition p hp s
    simplex 0 (singularTwoSimplexSecondBoundaryPath simplex)
      (singularTwoSimplexSecondBoundaryPath_toContinuousMap simplex)
  have hdiagonal := boolCoverEdgeTransition_eq_monodromyTransition p hp s
    simplex 1 (singularTwoSimplexDiagonalPath simplex)
      (singularTwoSimplexDiagonalPath_toContinuousMap simplex)
  -- Replace the diagonal by the homotopic boundary route, expand monodromy
  -- under concatenation, then commute the two Boolean summands.
  calc
    boolCoverEdgeTransition p hp s
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 simplex) =
        boolCoverMonodromyTransition p hp s
          (singularTwoSimplexDiagonalPath simplex) := hdiagonal
    _ = boolCoverMonodromyTransition p hp s
        ((singularTwoSimplexFirstBoundaryPath simplex).trans
          (singularTwoSimplexSecondBoundaryPath simplex)) :=
      (boolCoverMonodromyTransition_eq_of_homotopic p hp s _ _
        (singularTwoSimplex_facePath_homotopic simplex)).symm
    _ = boolCoverMonodromyTransition p hp s
          (singularTwoSimplexFirstBoundaryPath simplex) +
        boolCoverMonodromyTransition p hp s
          (singularTwoSimplexSecondBoundaryPath simplex) :=
      boolCoverMonodromyTransition_trans p hp s _ _
    _ = boolCoverEdgeTransition p hp s
          ((TopCat.toSSet.obj (TopCat.of X)).δ 2 simplex) +
        boolCoverEdgeTransition p hp s
          ((TopCat.toSSet.obj (TopCat.of X)).δ 0 simplex) :=
      congrArg₂ (fun a b : Bool ↦ a + b) hfirst.symm hsecond.symm
    _ = boolCoverEdgeTransition p hp s
          ((TopCat.toSSet.obj (TopCat.of X)).δ 0 simplex) +
        boolCoverEdgeTransition p hp s
          ((TopCat.toSSet.obj (TopCat.of X)).δ 2 simplex) := add_comm _ _

end AlgebraicTopology
