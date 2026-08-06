import Mathlib.Topology.Homotopy.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_1

open scoped Topology Topology.Homotopy unitInterval

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopicWith` is the ambient mathlib
-- owner for homotopies through maps satisfying a fixed predicate. The source step is stated for
-- maps of tetrads into a based triad `(X; A, B, *)`, so this file formalizes the cube-tetrad
-- conditions directly rather than replacing them by a surrogate `D^m → D^n` map.

open Set

namespace ContinuousMap

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map `f : X → Y` misses `y : Y` when `y` is not in its image. -/
def MissesPoint (f : C(X, Y)) (y : Y) : Prop :=
  y ∉ Set.range f

/-- `f.MissesPoint y` means exactly that every source point is sent away from `y`. -/
theorem missesPoint_iff (f : C(X, Y)) (y : Y) :
    f.MissesPoint y ↔ ∀ x : X, f x ≠ y := by
  constructor
  · intro hy x hxy
    exact hy ⟨x, hxy⟩
  · intro hy hy_range
    rcases hy_range with ⟨x, rfl⟩
    exact hy x rfl

/-- A map misses `y` exactly when `y` does not lie in its range. -/
@[simp] theorem missesPoint_iff_notMem_range (f : C(X, Y)) (y : Y) :
    f.MissesPoint y ↔ y ∉ Set.range f :=
  Iff.rfl

end ContinuousMap

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The cubical source `I^q = I^(q - 2) × I × I` used for the tetrad maps in Proof step 11.3.7. -/
abbrev tetradCubeIndex (q : ℕ) :=
  Fin (q - 2) ⊕ Unit ⊕ Unit

/-- The subspace `I^(q - 2) × {1} × I` of the source cube in the tetrad model. -/
def tetradCubeSubspaceA (q : ℕ) : Set (I^(tetradCubeIndex q)) :=
  { u | u (Sum.inr (Sum.inl ())) = 1 }

/-- The subspace `I^(q - 1) × {1}` of the source cube in the tetrad model. -/
def tetradCubeSubspaceB (q : ℕ) : Set (I^(tetradCubeIndex q)) :=
  { u | u (Sum.inr (Sum.inr ())) = 1 }

/-- The base subspace `J^(q - 2) × I ∪ I^(q - 1) × {0}` of the source tetrad cube. -/
def tetradCubeBase (q : ℕ) : Set (I^(tetradCubeIndex q)) :=
  { u | u ∘ Sum.inl ∈ Cube.boundary (Fin (q - 2)) ∨
        u (Sum.inr (Sum.inl ())) = 0 ∨
        u (Sum.inr (Sum.inr ())) = 0 }

/-- A map of tetrads
`(I^q; I^(q - 2) × {1} × I, I^(q - 1) × {1}, J^(q - 2) × I ∪ I^(q - 1) × {0}) → (X; A, B, *)`
is a continuous map from the cubical source to the ambient space of the triad that sends the
first distinguished source face into `A`, the second into `B`, and the base subspace to the
basepoint `x0 ∈ A ∩ B`. -/
def IsTetradCubeMap (q : ℕ) (T : Triad X) (x0 : T.intersection)
    (f : C(I^(tetradCubeIndex q), X)) : Prop :=
  (∀ u ∈ tetradCubeSubspaceA q, f u ∈ T.subspaceA) ∧
    (∀ u ∈ tetradCubeSubspaceB q, f u ∈ T.subspaceB) ∧
      ∀ u ∈ tetradCubeBase q, f u = x0

/-- Unfolding `IsTetradCubeMap` recovers the three defining tetrad-map conditions. -/
@[simp] theorem isTetradCubeMap_iff (q : ℕ) (T : Triad X) (x0 : T.intersection)
    (f : C(I^(tetradCubeIndex q), X)) :
    IsTetradCubeMap q T x0 f ↔
      (∀ u ∈ tetradCubeSubspaceA q, f u ∈ T.subspaceA) ∧
        (∀ u ∈ tetradCubeSubspaceB q, f u ∈ T.subspaceB) ∧
          ∀ u ∈ tetradCubeBase q, f u = x0 := by
  rfl

/-- A map of tetrads into `(X; A, X \ {x}, *)` sends the `A`-face into `A`, the `B`-face away
from `x`, and the base subspace to the fixed basepoint. -/
def IsTetradPointAvoidanceSourceMap (q : ℕ) (T : Triad X)
    (x0 : T.intersection)
    (x : X) (f : C(I^(tetradCubeIndex q), X)) : Prop :=
  (∀ u ∈ tetradCubeSubspaceA q, f u ∈ T.subspaceA) ∧
    (∀ u ∈ tetradCubeSubspaceB q, f u ≠ x) ∧
      ∀ u ∈ tetradCubeBase q, f u = x0

/-- Unfolding `IsTetradPointAvoidanceSourceMap` gives the three source-side tetrad conditions. -/
@[simp] theorem isTetradPointAvoidanceSourceMap_iff (q : ℕ) (T : Triad X)
    (x0 : T.intersection) (x : X) (f : C(I^(tetradCubeIndex q), X)) :
    IsTetradPointAvoidanceSourceMap q T x0 x f ↔
      (∀ u ∈ tetradCubeSubspaceA q, f u ∈ T.subspaceA) ∧
        (∀ u ∈ tetradCubeSubspaceB q, f u ≠ x) ∧
          ∀ u ∈ tetradCubeBase q, f u = x0 := by
  rfl

/-- A map of tetrads into `(X \ {y}; A, X \ {x, y}, *)` is a map into `(X; A, X \ {x}, *)` whose
entire image misses the chosen point `y`. -/
def IsTetradPointAvoidanceTargetMap (q : ℕ) (T : Triad X)
    (x0 : T.intersection)
    (x y : X) (f : C(I^(tetradCubeIndex q), X)) : Prop :=
  IsTetradPointAvoidanceSourceMap q T x0 x f ∧ f.MissesPoint y

/-- Unfolding `IsTetradPointAvoidanceTargetMap` gives the source-side conditions together with the
point-avoidance condition on the whole image. -/
@[simp] theorem isTetradPointAvoidanceTargetMap_iff (q : ℕ) (T : Triad X)
    (x0 : T.intersection) (x y : X) (f : C(I^(tetradCubeIndex q), X)) :
    IsTetradPointAvoidanceTargetMap q T x0 x y f ↔
      IsTetradPointAvoidanceSourceMap q T x0 x f ∧ f.MissesPoint y := by
  rfl

/-- Data witnessing the point-avoidance replacement required in Proof step 11.3.7. -/
structure TetradPointAvoidanceHomotopy (q : ℕ) (T : Triad X)
    (x0 : T.intersection)
    (diskM diskN : Set X) (f : C(I^(tetradCubeIndex q), X)) where
  x : X
  x_mem : x ∈ interior diskM
  y : X
  y_mem : y ∈ interior diskN
  g : C(I^(tetradCubeIndex q), X)
  homotopicWith :
    f.HomotopicWith g (IsTetradPointAvoidanceSourceMap q T x0 x)
  targetMap :
    IsTetradPointAvoidanceTargetMap q T x0 x y g

namespace TetradPointAvoidanceHomotopy

/-- The witness structure packages exactly the interior points `x ∈ diskM`, `y ∈ diskN`, and the
replacement map `g` appearing in Proof step 11.3.7. -/
theorem nonempty_iff
    (q : ℕ) (T : Triad X) (x0 : T.intersection)
    (diskM diskN : Set X) (f : C(I^(tetradCubeIndex q), X)) :
    Nonempty (TetradPointAvoidanceHomotopy q T x0 diskM diskN f) ↔
      ∃ x ∈ interior diskM, ∃ y ∈ interior diskN, ∃ g : C(I^(tetradCubeIndex q), X),
        f.HomotopicWith g (IsTetradPointAvoidanceSourceMap q T x0 x) ∧
          IsTetradPointAvoidanceTargetMap q T x0 x y g := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.x, h.x_mem, h.y, h.y_mem, h.g, h.homotopicWith, h.targetMap⟩
  · rintro ⟨x, hx, y, hy, g, hfg, hg⟩
    exact ⟨⟨x, hx, y, hy, g, hfg, hg⟩⟩

end TetradPointAvoidanceHomotopy

/-- Proof step 11.3.7: let `(X; A, B)` be a triad with
`A = (A ∩ B) ∪ D^m` and `B = (A ∩ B) ∪ D^n`, modeled by subsets `diskM` and `diskN`
homeomorphic to `unitDisk ((m : ℕ) - 1)` and `unitDisk ((n : ℕ) - 1)`. For
`2 ≤ q ≤ (m : ℕ) + (n : ℕ) - 2`, any tetrad map
`f : (I^q; I^(q - 2) × {1} × I, I^(q - 1) × {1}, J^(q - 2) × I ∪ I^(q - 1) × {0})
    → (X; A, B, *)`
admits interior points `x ∈ diskM` and `y ∈ diskN` and a replacement `g` such that, assuming
`interior diskM ⊆ T.subspaceBᶜ`, `f` is
homotopic to `g` through maps into `(X; A, X \ {x}, *)`, while `g` misses `y`. -/
theorem exists_tetradPointAvoidanceHomotopy
    (T : Triad X) (x0 : T.intersection)
    (m n : ℕ+) (q : ℕ)
    (hq₂ : 2 ≤ q) (hqmn : q ≤ (m : ℕ) + (n : ℕ) - 2)
    (diskM diskN : Set X)
    (hA : T.subspaceA = T.intersection ∪ diskM)
    (hB : T.subspaceB = T.intersection ∪ diskN)
    (hDiskM_disjoint : interior diskM ⊆ T.subspaceBᶜ)
    (hDiskM : Nonempty (Homeomorph diskM (unitDisk ((m : ℕ) - 1))))
    (hDiskN : Nonempty (Homeomorph diskN (unitDisk ((n : ℕ) - 1))))
    (f : C(I^(tetradCubeIndex q), X))
    (hf : IsTetradCubeMap q T x0 f) :
    ∃ x ∈ interior diskM, ∃ y ∈ interior diskN, ∃ g : C(I^(tetradCubeIndex q), X),
      f.HomotopicWith g (IsTetradPointAvoidanceSourceMap q T x0 x) ∧
        IsTetradPointAvoidanceTargetMap q T x0 x y g := sorry
