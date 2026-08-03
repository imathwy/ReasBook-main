module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Topology.Homotopy.Path

public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

/-- Helper for Theorem 75.2: the `TopCat` morphism underlying a path. -/
def pathTopCatMap {X : Type u} [TopologicalSpace X] {x y : X} (p : Path x y) :
    TopCat.I.{u} ⟶ TopCat.of X :=
  TopCat.ofHom ⟨fun t ↦ p t.down, by fun_prop⟩

/-- Helper for Theorem 75.2: the canonical singular one-simplex of the unit interval. -/
noncomputable def canonicalIntervalSingularEdge :
    (TopCat.toSSet.obj TopCat.I.{u}).obj (Opposite.op (SimplexCategory.mk 1)) :=
  SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI

/-- Helper for Theorem 75.2: a path regarded as a canonical singular one-simplex. -/
noncomputable def singularOneSimplexOfPath {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk 1)) :=
  (TopCat.toSSet.map (pathTopCatMap p)).app _ canonicalIntervalSingularEdge

/-- Helper for Theorem 75.2: the bundled path map sends zero to its source. -/
@[simp]
lemma pathTopCatMap_zero {X : Type u} [TopologicalSpace X] {x y : X} (p : Path x y) :
    pathTopCatMap p 0 = x := by
  -- Reduce to the endpoint equation of the original path.
  dsimp [pathTopCatMap]
  exact p.source

/-- Helper for Theorem 75.2: the bundled path map sends one to its target. -/
@[simp]
lemma pathTopCatMap_one {X : Type u} [TopologicalSpace X] {x y : X} (p : Path x y) :
    pathTopCatMap p 1 = y := by
  -- Reduce to the endpoint equation of the original path.
  dsimp [pathTopCatMap]
  exact p.target

/-- Helper for Theorem 75.2: the interval-to-space map sends the canonical edge to the path
simplex. -/
lemma canonicalIntervalSingularEdge_map {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    (TopCat.toSSet.map (pathTopCatMap p)).app
        (Opposite.op (SimplexCategory.mk 1)) canonicalIntervalSingularEdge =
      singularOneSimplexOfPath p := by
  -- This is the defining image of the canonical interval edge.
  rfl

/-- Helper for Theorem 75.2: the singular chain map sends the canonical interval generator to
the generator represented by the path. -/
lemma ιChainComplex_canonicalIntervalSingularEdge_map {X : Type u} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    let R := AddCommGrpCat.of (ULift.{u} ℤ)
    let I := TopCat.toSSet.obj TopCat.I.{u}
    let SX := TopCat.toSSet.obj (TopCat.of X)
    I.ιChainComplex canonicalIntervalSingularEdge ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (pathTopCatMap p)) R).f 1 =
      SX.ιChainComplex (singularOneSimplexOfPath p) := by
  -- Use the generator computation for a simplicial chain map, then normalize its image.
  dsimp only
  rw [SSet.ι_chainComplexMap_f, canonicalIntervalSingularEdge_map]

end AlgebraicTopology

end
