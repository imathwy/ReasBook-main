import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_3
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_3
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_56
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_62
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace MaximumVolumeInscribedEllipsoid

noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped EllipsoidNotation RealInnerProductSpace RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

/- Definition 5.4.5.6 lies in the inscribed-ellipsoid / convex-reformulation domain.

Sampled owner-style declarations in this domain:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective;
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` in `Chap03/Definition_3_3`, the chapter
  owner/view for epigraph reformulations over a base feasible set;
* `innerLePolyhedron` and `mem_innerLePolyhedron_iff` in `Chap03/Definition_3_62`, the chapter
  owner/view for finite half-space presentations `⟪a i, x⟫ ≤ b i`;
* `affineEllipsoid` together with the notation `E(H, x̄)` and `mem_affineEllipsoid_iff` in
  `Chap03/Definition_3_56`, the chapter owner/view for quadratic-form ellipsoids;
* `enclosingEllipsoid` in `Chap05/Definition_5_4_5_1`, the adjacent Chapter 5 precedent for
  keeping an image-form ellipsoid owner on a strict-cone shape parameter instead of collapsing it
  into a quadratic-form surrogate;
* `logDetBarrier` in `Chap05/Definition_5_4_4_5`, the chapter owner for the `-log det`
  contribution on `𝕊^n₊₊`.

Best owner abstraction:
* source-facing: the image-form inscribed ellipsoid `W(G, v)` together with the convex
  reformulation base feasible set on `(G, v)`;
* core/canonical: `SetConstrainedMinimizationProblem`, `constrainedEpigraph`,
  `innerLePolyhedron`,
  the Chapter 3 quadratic-form ellipsoid `affineEllipsoid`, and `logDetBarrier`;
* bridge/view: the comparison `W(G, v) = E(G², v)`, the triple epigraph presentation on
  `(G, v, τ)`, and the textbook formulae obtained by expanding `logDetBarrier` back to
  `-log det G`.

Primitive data:
* the half-space presentation `a`, `b`;
* the strict-cone shape parameter `G`;
* the center `v`.

Derived API:
* the source-facing ellipsoid `W(G, v)`;
* the bridge theorem `W(G, v) = E(G², v)`;
* the containment theorem for `W(G, v) ⊆ innerLePolyhedron a b`;
* the base feasible set on `(G, v)` cut out by the geometric containment
  `W(G, v) ⊆ innerLePolyhedron a b`;
* the reformulation feasible set on triples `(G, v, τ)`, realized canonically as the epigraph of
  `logDetBarrier n` over that base feasible set;
* the owner optimization problem `optimizationProblem a b`;
* the formula companions obtained by expanding `W(G, v) ⊆ innerLePolyhedron a b` into the support
  inequalities and `logDetBarrier` into `-log det G`.

There is no upstream owner for the source-facing image-form ellipsoid parameterized by the
inscribed-ellipsoid variable `G : 𝕊^n₊₊`, so this file owns `W(G, v)` directly, keeps
`affineEllipsoid` only as the quadratic bridge `W(G, v) = E(G², v)`, and builds the optimization
reformulation from the earlier chapter owners `constrainedEpigraph`, `innerLePolyhedron`, and
`logDetBarrier` directly.
-/

def inscribedEllipsoid
    (G : 𝕊^n₊₊) (v : E) : Set E :=
  {x | ∃ u : E, ‖u‖ ≤ 1 ∧ x = v + (toMatrix G).toEuclideanLin u}

namespace InscribedEllipsoidNotation

scoped notation:max "W(" G ", " v ")" => inscribedEllipsoid G v

end InscribedEllipsoidNotation

open scoped InscribedEllipsoidNotation

/-- Membership in the image-form ellipsoid `W(G, v)` is exactly the existence of a unit-ball
parameter `u` with `x = v + G u`. -/
@[simp] theorem mem_inscribedEllipsoid_iff
    {G : 𝕊^n₊₊} {v x : E} :
    x ∈ W(G, v) ↔
      ∃ u : E, ‖u‖ ≤ 1 ∧ x = v + (toMatrix G).toEuclideanLin u :=
  Iff.rfl

/-- The image-form ellipsoid `W(G, v)` is the Chapter 3 quadratic-form ellipsoid whose shape
matrix is `G²`. -/
theorem inscribedEllipsoid_eq_affineEllipsoid_sq
    (G : 𝕊^n₊₊) (v : E) :
    W(G, v) = E(toMatrix G * toMatrix G, v) := by
  sorry

-- Proof sketch: combine the source-facing image description of `W(G, v)` with
-- `mem_innerLePolyhedron_iff`. For the half-space `⟪a i, x⟫ ≤ b i`, the support value of
-- `x ↦ ⟪a i, x⟫` on `W(G, v)` is `⟪a i, v⟫ + ‖G a i‖`, so containment is equivalent to the
-- displayed norm inequalities.
/-- The ellipsoid `W(G, v)` is contained in the polyhedron
`Q = {x : ⟪a i, x⟫ ≤ b i}` exactly when the support-function inequalities
`‖G a_i‖ ≤ b_i - ⟪a_i, v⟫` hold for all `i`. -/
theorem inscribedEllipsoid_subset_innerLePolyhedron_iff
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) :
    W(G, v) ⊆ innerLePolyhedron a b ↔
      ∀ i : Fin m,
        ‖(toMatrix G).toEuclideanLin (a i)‖ ≤ b i - ⟪a i, v⟫ := sorry

/-- The base feasible set of inscribed-ellipsoid parameters `(G, v)` satisfying the geometric
containment `W(G, v) ⊆ innerLePolyhedron a b`. -/
def containmentSet
    (a : Fin m → E) (b : Fin m → ℝ) : Set (𝕊^n₊₊ × E) :=
  {Gv | W(Gv.1, Gv.2) ⊆ innerLePolyhedron a b}

/-- Membership in `containmentSet a b` is exactly the geometric containment
`W(G, v) ⊆ innerLePolyhedron a b`. -/
@[simp] theorem mem_containmentSet_iff
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) :
    (G, v) ∈ containmentSet a b ↔
      W(G, v) ⊆ innerLePolyhedron a b :=
  Iff.rfl

/-- The feasible set of the convex reformulation is the epigraph of `logDetBarrier n` over the
base containment set, presented on triples `(G, v, τ)`. -/
def feasibleSet
    (a : Fin m → E) (b : Fin m → ℝ) : Set (𝕊^n₊₊ × E × ℝ) :=
  {Gvτ | ((Gvτ.1, Gvτ.2.1), Gvτ.2.2) ∈
    constrainedEpigraph (containmentSet a b)
      (fun Gv ↦ (logDetBarrier n Gv.1 : WithTop ℝ))}

/-- Membership in `feasibleSet a b` is exactly the conjunction of `logDetBarrier n G ≤ τ` and
the geometric containment `W(G, v) ⊆ innerLePolyhedron a b`. -/
@[simp] theorem mem_feasibleSet_iff
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    (G, v, τ) ∈ feasibleSet a b ↔
      logDetBarrier n G ≤ τ ∧ W(G, v) ⊆ innerLePolyhedron a b := by
  change ((G, v), τ) ∈
      constrainedEpigraph (containmentSet a b)
        (fun Gv ↦ (logDetBarrier n Gv.1 : WithTop ℝ)) ↔
    logDetBarrier n G ≤ τ ∧ W(G, v) ⊆ innerLePolyhedron a b
  rw [mem_constrainedEpigraph_iff]
  change (G, v) ∈ containmentSet a b ∧ (logDetBarrier n G : WithTop ℝ) ≤ τ ↔
    logDetBarrier n G ≤ τ ∧ W(G, v) ⊆ innerLePolyhedron a b
  rw [mem_containmentSet_iff]
  constructor
  · rintro ⟨hcontain, hτ⟩
    exact ⟨by exact_mod_cast hτ, hcontain⟩
  · rintro ⟨hτ, hcontain⟩
    exact ⟨hcontain, by exact_mod_cast hτ⟩

/-- Expanding the owner containment `W(G, v) ⊆ innerLePolyhedron a b` rewrites feasible-set
membership back to the textbook inequalities
`‖G a_i‖ ≤ b_i - ⟪a_i, v⟫`, while expanding `logDetBarrier n G` rewrites the epigraph term back
to `-log det G ≤ τ`. -/
theorem mem_feasibleSet_iff_formula
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    (G, v, τ) ∈ feasibleSet a b ↔
      -Real.log (toMatrix G).det ≤ τ ∧
        ∀ i : Fin m,
          ‖(toMatrix G).toEuclideanLin (a i)‖ ≤ b i - ⟪a i, v⟫ := by
  rw [mem_feasibleSet_iff, inscribedEllipsoid_subset_innerLePolyhedron_iff, logDetBarrier_apply]
  simp [toMatrix_def]

/-- Definition 5.4.5.6: for the polyhedron
`Q = {x ∈ ℝⁿ : ⟪a_i, x⟫ ≤ b_i, i = 1, …, m}`, the maximum-volume inscribed ellipsoid problem is
the set-constrained minimization problem on triples `(G, v, τ)` whose feasible set is the convex
reformulation and whose objective is the epigraph variable `τ`. -/
def optimizationProblem
    (a : Fin m → E) (b : Fin m → ℝ) :
    SetConstrainedMinimizationProblem (𝕊^n₊₊ × E × ℝ) where
  feasibleSet := feasibleSet a b
  objective := Prod.snd ∘ Prod.snd

/-- Evaluating the convex reformulation objective returns the auxiliary scalar variable `τ`. -/
@[simp] theorem optimizationProblem_objective_apply
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    (optimizationProblem a b).objective (G, v, τ) = τ :=
  rfl

end

end MaximumVolumeInscribedEllipsoid
