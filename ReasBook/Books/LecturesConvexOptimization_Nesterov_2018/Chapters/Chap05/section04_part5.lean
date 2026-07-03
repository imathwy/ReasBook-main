import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_4_5_6 (from Chap05) -/
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

/-! ### Definition_5_4_5_7 (from Chap05) -/
namespace MaximumVolumeInscribedEllipsoid

noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped BigOperators RealSymmetricMatrixSpace SecondOrderCone

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

private abbrev secondOrderSlack
    (a : Fin m → E) (b : Fin m → ℝ) (G : SymmMat) (v : E) (i : Fin m) : E × ℝ :=
  ((G : Mat).toEuclideanLin (a i), b i - inner ℝ (a i) v)

/- Definition 5.4.5.7 lies in the maximum-volume-inscribed-ellipsoid / logarithmic-barrier
domain.

Sampled owner-style declarations in this domain:
* `logDetBarrier` and `logDetBarrier_apply` in `Chap05/Definition_5_4_4_5`, the chapter owner of
  the determinant contribution on `𝕊^n₊₊`;
* `secondOrderCone` and `mem_interior_secondOrderCone_iff` in `Chap05/Lemma_5_4_3_3`, the
  chapter owner/view for the strict second-order-cone inequalities `‖x‖ < t`;
* `circumscribedEllipsoidBarrierDomain` and `circumscribedEllipsoidBarrier` in
  `Chap05/Definition_5_4_5_5`, the adjacent ellipsoid-barrier owner pattern on a strict-domain
  subtype;
* `analyticBarrierDomain`, `AnalyticBarrierPoint`, and `analyticBarrier` in
  `Chap03/Definition_3_62`, the chapter precedent for keeping a barrier on its strict-domain
  carrier and any raw formula only as a bridge.

Source/core/bridge triage:
* source-facing: the strict inscribed-ellipsoid barrier domain and barrier;
* core/canonical: `logDetBarrier n` on `𝕊^n₊₊` together with `interior K₂[E]` for each
  second-order-cone slack;
* bridge/view: the raw triple formula `logarithmicBarrierAmbient` and the slack pairs
  `secondOrderSlack a b G v i`.

Primitive data:
* the half-space data `a`, `b`.

Derived API:
* the strict domain `logarithmicBarrierDomain a b`;
* the strict-domain carrier `LogarithmicBarrierPoint a b`;
* the ambient bridge domain `logarithmicBarrierAmbientDomain a b`;
* the ambient bridge formula `logarithmicBarrierAmbient a b`;
* the source-facing barrier `logarithmicBarrier a b`.

This file therefore keeps the textbook inscribed-ellipsoid barrier on its strict-domain carrier,
reuses the chapter owner `logDetBarrier` for the determinant term, reuses the chapter
second-order-cone owner for each strict slack `‖G aᵢ‖ < bᵢ - ⟪aᵢ, v⟫`, and exports only the raw
ambient pullback domain/formula as a bridge for downstream path-following statements.
-/

/-- The strict domain on which the maximum-volume inscribed ellipsoid logarithmic barrier is
defined. -/
def logarithmicBarrierDomain
    (a : Fin m → E) (b : Fin m → ℝ) : Set (𝕊^n₊₊ × E × ℝ) :=
  {Gvτ |
    0 < Gvτ.2.2 - logDetBarrier n Gvτ.1 ∧
      ∀ i : Fin m,
        secondOrderSlack a b Gvτ.1 Gvτ.2.1 i ∈ interior K₂[E]}

/-- The ambient pullback domain of the maximum-volume inscribed ellipsoid logarithmic barrier on
`𝕊ⁿ × E × ℝ`. It is a bridge/view that records strict positivity of the shape variable together
with the same strict second-order-cone inequalities used by the source-facing strict-domain owner
`logarithmicBarrierDomain a b`. -/
def logarithmicBarrierAmbientDomain
    (a : Fin m → E) (b : Fin m → ℝ) : Set (SymmMat × E × ℝ) :=
  {Gvτ |
    Gvτ.1 ∈ (𝕊^n₊₊ : Set SymmMat) ∧
      0 < Gvτ.2.2 - logDetBarrierAmbient n Gvτ.1 ∧
        ∀ i : Fin m,
          secondOrderSlack a b Gvτ.1 Gvτ.2.1 i ∈ interior K₂[E]}

/-- Membership in the barrier domain means that the shifted logarithmic argument
`τ - logDetBarrier n G = τ + log det G` is positive and every second-order-cone slack lies in the
strict branch `‖G aᵢ‖ < bᵢ - ⟪aᵢ, v⟫`. -/
theorem mem_logarithmicBarrierDomain_iff
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    (G, v, τ) ∈ logarithmicBarrierDomain a b ↔
      0 < τ - logDetBarrier n G ∧
        ∀ i : Fin m, ‖(toMatrix G).toEuclideanLin (a i)‖ < b i - inner ℝ (a i) v := by
  simp [logarithmicBarrierDomain, secondOrderSlack, mem_interior_secondOrderCone_iff, toMatrix_def]

/-- Membership in the ambient bridge domain means that the shape variable lies in the strict cone,
the shifted logarithmic argument `τ + log det G` is positive, and every second-order-cone slack
lies in the strict branch `‖G aᵢ‖ < bᵢ - ⟪aᵢ, v⟫`. -/
theorem mem_logarithmicBarrierAmbientDomain_iff
    (a : Fin m → E) (b : Fin m → ℝ) (G : SymmMat) (v : E) (τ : ℝ) :
    (G, v, τ) ∈ logarithmicBarrierAmbientDomain a b ↔
      G ∈ (𝕊^n₊₊ : Set SymmMat) ∧
        0 < τ - logDetBarrierAmbient n G ∧
          ∀ i : Fin m, ‖(G : Mat).toEuclideanLin (a i)‖ < b i - inner ℝ (a i) v := by
  simp [logarithmicBarrierAmbientDomain, secondOrderSlack, mem_interior_secondOrderCone_iff]

/-- Restricting the ambient bridge domain to a strict-cone shape recovers the source-facing
strict-domain owner. -/
@[simp] theorem mem_logarithmicBarrierAmbientDomain_iff_strict
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    ((G : SymmMat), v, τ) ∈ logarithmicBarrierAmbientDomain a b ↔
      (G, v, τ) ∈ logarithmicBarrierDomain a b := by
  simp [logarithmicBarrierAmbientDomain, logarithmicBarrierDomain, secondOrderSlack,
    mem_interior_secondOrderCone_iff, logDetBarrier, logDetBarrierAmbient]

/-- Expanding `logDetBarrier n` rewrites barrier-domain membership back to the textbook
`τ + log det G` formula. -/
theorem mem_logarithmicBarrierDomain_iff_formula
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    (G, v, τ) ∈ logarithmicBarrierDomain a b ↔
      0 < τ + Real.log (toMatrix G).det ∧
        ∀ i : Fin m, ‖(toMatrix G).toEuclideanLin (a i)‖ < b i - inner ℝ (a i) v := by
  simp [mem_logarithmicBarrierDomain_iff, toMatrix_def]

/-- The subtype of points in the strict inscribed-ellipsoid barrier domain. This is the natural
owner carrier for the logarithmic barrier. -/
abbrev LogarithmicBarrierPoint
    (a : Fin m → E) (b : Fin m → ℝ) :=
  {Gvτ : 𝕊^n₊₊ × E × ℝ // Gvτ ∈ logarithmicBarrierDomain a b}

/-- The ambient formula underlying the maximum-volume inscribed ellipsoid logarithmic barrier. It
is only a bridge view; the owner barrier is `logarithmicBarrier a b` on
`LogarithmicBarrierPoint a b`. -/
def logarithmicBarrierAmbient
    (a : Fin m → E) (b : Fin m → ℝ) : SymmMat × E × ℝ → ℝ :=
  fun Gvτ ↦
    logDetBarrierAmbient n Gvτ.1
      - Real.log (Gvτ.2.2 - logDetBarrierAmbient n Gvτ.1)
      + ∑ i : Fin m, secondOrderConeBarrier (secondOrderSlack a b Gvτ.1 Gvτ.2.1 i)

/-- Definition 5.4.5.7: the logarithmic barrier for the maximum-volume inscribed ellipsoid
reformulation is
`F(G, v, τ) = -log det G - log (τ + log det G)
  - ∑ᵢ log ((bᵢ - ⟪aᵢ, v⟫)^2 - ‖G aᵢ‖^2)`. -/
def logarithmicBarrier
    (a : Fin m → E) (b : Fin m → ℝ) :
    LogarithmicBarrierPoint a b → ℝ :=
  fun Gvτ ↦ logarithmicBarrierAmbient a b ((Gvτ.1.1 : SymmMat), Gvτ.1.2.1, Gvτ.1.2.2)

/-- Evaluating the ambient maximum-volume inscribed ellipsoid barrier recovers the owner formula
built from the chapter determinant barrier `logDetBarrier n` and the canonical
second-order-cone barrier owner on each slack pair. -/
theorem logarithmicBarrierAmbient_apply
    (a : Fin m → E) (b : Fin m → ℝ) (G : SymmMat) (v : E) (τ : ℝ) :
    logarithmicBarrierAmbient a b (G, v, τ) =
      logDetBarrierAmbient n G
        - Real.log (τ - logDetBarrierAmbient n G)
        + ∑ i : Fin m,
            secondOrderConeBarrier
              ((G : Mat).toEuclideanLin (a i), b i - inner ℝ (a i) v) := by
  simp [logarithmicBarrierAmbient, secondOrderSlack]

/-- On a strict-cone slice, the ambient inscribed-ellipsoid barrier agrees with the owner formula
built from `logDetBarrier n`. -/
theorem logarithmicBarrierAmbient_apply_strict
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    logarithmicBarrierAmbient a b ((G : SymmMat), v, τ) =
      logDetBarrier n G
        - Real.log (τ - logDetBarrier n G)
        + ∑ i : Fin m,
            secondOrderConeBarrier
              ((toMatrix G).toEuclideanLin (a i), b i - inner ℝ (a i) v) := by
  simp [logarithmicBarrierAmbient_apply, toMatrix_def, logDetBarrier, logDetBarrierAmbient]

/-- Expanding `logDetBarrier n` rewrites the ambient barrier back to the textbook
`-log det G - log (τ + log det G)` formula. -/
theorem logarithmicBarrierAmbient_apply_formula
    (a : Fin m → E) (b : Fin m → ℝ) (G : SymmMat) (v : E) (τ : ℝ) :
    logarithmicBarrierAmbient a b (G, v, τ) =
      -Real.log (G : Mat).det
        - Real.log (τ + Real.log (G : Mat).det)
        - ∑ i : Fin m,
            Real.log
              ((b i - inner ℝ (a i) v) ^ (2 : ℕ) -
                ‖(G : Mat).toEuclideanLin (a i)‖ ^ (2 : ℕ)) := by
  rw [logarithmicBarrierAmbient_apply]
  calc
    logDetBarrierAmbient n G - Real.log (τ - logDetBarrierAmbient n G)
        + ∑ i : Fin m, secondOrderConeBarrier (secondOrderSlack a b G v i)
      = logDetBarrierAmbient n G - Real.log (τ - logDetBarrierAmbient n G)
          + ∑ i : Fin m,
              (-Real.log
                ((b i - inner ℝ (a i) v) ^ (2 : ℕ) -
                  ‖(G : Mat).toEuclideanLin (a i)‖ ^ (2 : ℕ))) := by
            refine congrArg
              (fun s ↦ logDetBarrierAmbient n G - Real.log (τ - logDetBarrierAmbient n G) + s) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [secondOrderConeBarrier_apply, secondOrderSlack]
    _ = logDetBarrierAmbient n G - Real.log (τ - logDetBarrierAmbient n G)
          - ∑ i : Fin m,
              Real.log
                ((b i - inner ℝ (a i) v) ^ (2 : ℕ) -
                  ‖(G : Mat).toEuclideanLin (a i)‖ ^ (2 : ℕ)) := by
            rw [Finset.sum_neg_distrib]
            simp [sub_eq_add_neg]
    _ = -Real.log (G : Mat).det
          - Real.log (τ + Real.log (G : Mat).det)
          - ∑ i : Fin m,
              Real.log
                ((b i - inner ℝ (a i) v) ^ (2 : ℕ) -
                  ‖(G : Mat).toEuclideanLin (a i)‖ ^ (2 : ℕ)) := by
            simp [logDetBarrierAmbient]

/-- Evaluating the inscribed-ellipsoid barrier on a strict-domain point recovers its ambient
bridge formula. -/
@[simp] theorem logarithmicBarrier_apply
    (a : Fin m → E) (b : Fin m → ℝ) (Gvτ : LogarithmicBarrierPoint a b) :
    logarithmicBarrier a b Gvτ =
      logarithmicBarrierAmbient a b ((Gvτ.1.1 : SymmMat), Gvτ.1.2.1, Gvτ.1.2.2) :=
  rfl

/-- At a strict-domain triple `(G, v, τ)`, the logarithmic barrier is the owner formula built
from `logDetBarrier n` and the canonical second-order-cone barrier owner. -/
theorem logarithmicBarrier_apply_triple
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ)
    (h : (G, v, τ) ∈ logarithmicBarrierDomain a b) :
    logarithmicBarrier a b ⟨(G, v, τ), h⟩ =
      logDetBarrier n G
        - Real.log (τ - logDetBarrier n G)
        + ∑ i : Fin m,
            secondOrderConeBarrier
              ((toMatrix G).toEuclideanLin (a i), b i - inner ℝ (a i) v) := by
  simpa using logarithmicBarrierAmbient_apply_strict a b G v τ

/-- At a strict-domain triple `(G, v, τ)`, the inscribed-ellipsoid logarithmic barrier is the
textbook formula
`-log det G - log (τ + log det G) - \sum_i log ((bᵢ - ⟪aᵢ, v⟫)^2 - ‖G aᵢ‖²)`. -/
theorem logarithmicBarrier_apply_triple_formula
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ)
    (h : (G, v, τ) ∈ logarithmicBarrierDomain a b) :
    logarithmicBarrier a b ⟨(G, v, τ), h⟩ =
      -Real.log (toMatrix G).det
        - Real.log (τ + Real.log (toMatrix G).det)
        - ∑ i : Fin m,
            Real.log
              ((b i - inner ℝ (a i) v) ^ (2 : ℕ) -
                ‖(toMatrix G).toEuclideanLin (a i)‖ ^ (2 : ℕ)) := by
  simpa [toMatrix_def] using logarithmicBarrierAmbient_apply_formula a b (G : SymmMat) v τ

end

end MaximumVolumeInscribedEllipsoid

/-! ### Lemma_5_4_5_1 (from Chap05) -/
noncomputable section

open Matrix
open scoped EllipsoidNotation RealInnerProductSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Lemma 5.4.5.1 lies in the chapter's Euclidean ellipsoid / affine-support domain.

Sampled owner-style declarations:
- `affineEllipsoid` and `mem_affineEllipsoid_iff` in `Chap03/Lemma_3_2_7`, the chapter owner and
  companion view for the textbook ellipsoid `E(H, v)`;
- `center_mem_affineEllipsoid` in the same file, showing that center-membership is derived from
  that owner rather than stored as separate data;
- `isGreatest_inner_image_spdEllipsoid` in `Chap03/Lemma_3_20`, the canonical centered-ellipsoid
  support-value theorem already stated on the same owner surface.

Best owner abstraction:
- source-facing: the affine half-space inequality on the chapter ellipsoid `E(H, v)`;
- core/canonical: `affineEllipsoid` together with the centered support maximum theorem
  `isGreatest_inner_image_spdEllipsoid`;
- bridge/view: translating `E(H, v)` to `E(H, 0)` and rewriting the affine inequality in terms of
  the support value.

Primitive data:
- the linear functional vector `a`;
- the center `v`;
- the affine bound `b`;
- the positive-definite shape matrix `H`.

Derived API:
- ellipsoid membership via `x ∈ E(H, v)`;
- the centered support bound over `E(H, 0)`;
- the quadratic inequality obtained by squaring that support bound under the nonnegative
  center-slack hypothesis `0 ≤ b - ⟪a, v⟫`.

The previous statement duplicated the owner ellipsoid through its raw quadratic predicate. This
refinement keeps the source-facing inequality theorem, but moves its public surface onto the
existing chapter owner and reuses the centered support theorem upstream instead of reproving the
same geometry locally.
-/

-- Proof sketch: for the forward implication, evaluate the affine form at the boundary point
-- `v + (H *ᵥ a) / √⟪H a, a⟫`, which satisfies the boundary equation
-- `⟪H⁻¹ (x - v), x - v⟫ = 1`; for the reverse
-- implication, write `x = v + y` and apply Cauchy-Schwarz for the inner product induced by
-- `H⁻¹` to bound `⟪a, y⟫` by `√⟪H a, a⟫`.
/-- Lemma 5.4.5.1: for the ellipsoid
`W = {x | ⟪H⁻¹ (x - v), x - v⟫ ≤ 1}` cut out by a positive-definite matrix `H`, the affine
inequality `⟪a, x⟫ ≤ b` holds on all of `W` exactly when the quadratic bound
`⟪a, H a⟫ ≤ (b - ⟪a, v⟫)^2` holds. On the public surface, `W` is the chapter ellipsoid
owner `E(H, v)`. -/
theorem affine_le_on_affineEllipsoid_iff
    (a v : E) (b : ℝ) (H : Mat)
    (hβ : 0 ≤ b - ⟪a, v⟫) (hH : H.PosDef) :
    (∀ x ∈ E(H, v), ⟪a, x⟫ ≤ b) ↔
      ⟪a, H.toEuclideanLin a⟫ ≤ (b - ⟪a, v⟫) ^ (2 : ℕ) := by
  let β := b - ⟪a, v⟫
  have hβ_nonneg : 0 ≤ β := by
    simpa [β] using hβ
  have htranslate :
      (∀ x ∈ E(H, v), ⟪a, x⟫ ≤ b) ↔
        ∀ y ∈ E(H, (0 : E)), ⟪a, y⟫ ≤ β := by
    constructor
    · intro hx y hy
      have hmem : v + y ∈ E(H, v) := by
        rw [mem_affineEllipsoid_iff] at hy ⊢
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy
      have hxy : ⟪a, v⟫ + ⟪a, y⟫ ≤ b := by
        simpa [inner_add_right] using hx (v + y) hmem
      linarith
    · intro hy x hx
      have hmem : x - v ∈ E(H, (0 : E)) := by
        rw [mem_affineEllipsoid_iff] at hx ⊢
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx
      have hxy : ⟪a, x - v⟫ ≤ β := hy (x - v) hmem
      have hxsplit : ⟪a, x⟫ = ⟪a, v⟫ + ⟪a, x - v⟫ := by
        calc
          ⟪a, x⟫ = ⟪a, v + (x - v)⟫ := by simp
          _ = ⟪a, v⟫ + ⟪a, x - v⟫ := by rw [inner_add_right]
      linarith
  have hcentered :
      (∀ y ∈ E(H, (0 : E)), ⟪a, y⟫ ≤ β) ↔
        Real.sqrt ⟪a, H.toEuclideanLin a⟫ ≤ β := by
    have hmax :
        IsGreatest ((fun y : E ↦ ⟪a, y⟫) '' E(H, (0 : E)))
          (Real.sqrt ⟪a, H.toEuclideanLin a⟫) := by
      let _ : Invertible H := hH.isUnit.invertible
      simpa only [Matrix.inv_inv_of_invertible] using
        isGreatest_inner_image_spdEllipsoid H⁻¹ hH.inv a
    constructor
    · intro hy
      rcases hmax.1 with ⟨y, hy_mem, hy_eq⟩
      rw [← hy_eq]
      exact hy y hy_mem
    · intro hmax_le y hy
      exact le_trans (hmax.2 ⟨y, hy, rfl⟩) hmax_le
  have hsqrt :
      Real.sqrt ⟪a, H.toEuclideanLin a⟫ ≤ β ↔
        ⟪a, H.toEuclideanLin a⟫ ≤ β ^ (2 : ℕ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨hβ_nonneg, h⟩
  rw [htranslate, hcentered]
  simpa [β] using hsqrt

end

/-! ### Proposition_5_4_5_1 (from Chap05) -/
noncomputable section

open Matrix
open scoped BigOperators RealInnerProductSpace RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

/-
Proposition 5.4.5.1 lies in the circumscribed-ellipsoid / barrier path-following domain.

Sampled owner-style declarations in this domain:
* `circumscribedEllipsoidOptimizationProblem` and
  `mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff` in
  `Definition_5_4_5_4`, the source-facing owner of the circumscribed-ellipsoid reformulation;
* `circumscribedEllipsoidBarrierDomain`, `circumscribedEllipsoidBarrierAmbient`, and
  `circumscribedEllipsoidBarrier` in `Definition_5_4_5_5`, the source-facing strict-domain
  barrier API for the same variables;
* `logDetBarrierAmbient` in `Definition_5_4_4_5`, the chapter bridge for the `-\log \det`
  contribution on ambient symmetric matrices;
* `BarrierPathFollowingScheme` in `Definition_5_3_4_1`, the chapter owner for short-step
  path-following data.

Best owner abstraction:
* source-facing: the circumscribed-ellipsoid optimization problem and barrier on strict-cone pairs
  `(H, τ)`;
* core/canonical: `BarrierPathFollowingScheme`;
* bridge/view: the ambient symmetric-matrix product `𝕊^n × ℝ`, used only to host the objective
  direction `(0, 1)` and the self-concordant-barrier assumption.

Primitive data:
* the half-space data `a`, `b`, and the center `v`;
* the owner feasible set and owner barrier domain from `Definition_5_4_5_4` and
  `Definition_5_4_5_5`.

Derived API:
* the owner ambient barrier domain `circumscribedEllipsoidBarrierAmbientDomain a b v` and ambient
  barrier `circumscribedEllipsoidBarrierAmbient a b v` on `𝕊^n × ℝ`;
* the path-following existence and stopping statement, whose comparison points are read from the
  owner problem `circumscribedEllipsoidOptimizationProblem a b v`.

This refinement removes the parallel public decision-variable vocabulary
(`DecisionVar`, `ambientMatrix`, `ambientTau`, ...). The proposition now reuses the chapter
Frobenius geometry from `Definition_5_4_4_2` and states the path-following theorem directly on
the owner ambient barrier/problem surface from the neighboring definition files.
-/

section

variable (a : Fin m → E) (b : Fin m → ℝ) (v : E)

local notation "𝒟" => circumscribedEllipsoidBarrierAmbientDomain a b v
local notation "F" => circumscribedEllipsoidBarrierAmbient a b v
local notation "cτ" => ((0 : SymmMat), (1 : ℝ))
local notation "P" => circumscribedEllipsoidOptimizationProblem a b v

/-- Proposition 5.4.5.1: if the circumscribed-ellipsoid logarithmic barrier from
`Definition_5_4_5_5`, given directly by the owner ambient barrier `F` on the owner ambient
domain `𝒟 ⊆ 𝕊^n × ℝ`, is a `ν`-self-concordant barrier with `ν ≤ m + n + 1`, then there is a
positive iteration constant `C` such that for every `ε > 0` one can choose short-step
path-following data whose stopping iterate determines an actual feasible point `xStop` of the
owner problem `P`, with `P xStop ≤ P y + ε` for every feasible `y`, and whose stopping index is
bounded by `O(√(m + n + 1) log ((m + n) / ε))`. -/
theorem exists_circumscribedEllipsoidPathFollowingScheme
    {ν : NNReal}
    [IsSelfConcordantBarrierOnWith 𝒟 ν F]
    (hν : ν ≤ m + n + 1)
    (hstrict : Set.Nonempty 𝒟) :
    ∃ C : NNRealˣ,
      ∀ {ε : ℝ}, 0 < ε →
        ∃ β : ℝ,
          ∃ γ : ℝ,
            ∃ x0 : 𝒟,
              ∃ scheme : BarrierPathFollowingScheme
                cτ
                F
                ν
                x0 β γ ε,
                ∃ xStop :
                    (circumscribedEllipsoidOptimizationProblem a b v).feasibleSet,
                  β < 1 / 2 ∧
                    0 < γ ∧
                    (((xStop : 𝕊^n₊₊ × ℝ) : SymmMat × ℝ) =
                      scheme scheme.stopIndex) ∧
                    (∀ y ∈ (circumscribedEllipsoidOptimizationProblem a b v).feasibleSet,
                      P xStop ≤ P y + ε) ∧
                    scheme.stopIndex ≤
                      ⌈((C : NNReal) : ℝ) * Real.sqrt (m + n + 1 : ℝ) *
                        Real.log ((m + n : ℝ) / ε)⌉₊ := sorry

end

end

/-! ### Theorem_5_4_5_1 (from Chap05) -/
noncomputable section

open Matrix
open WithLp
open scoped BigOperators RealSymmetricMatrixSpace

variable {ι : Type*} [Fintype ι] {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n
local notation "TailSpace" => Eₙ × ℝ
local notation "MVEEAmbientSpace" => SymmMat × TailSpace

noncomputable local instance : SeminormedAddCommGroup TailSpace :=
  WithLp.seminormedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance : NormedAddCommGroup TailSpace :=
  WithLp.normedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance : NormedSpace ℝ TailSpace :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance : InnerProductSpace ℝ TailSpace where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 Eₙ ℝ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance : CompleteSpace TailSpace := inferInstance

noncomputable local instance : SeminormedAddCommGroup MVEEAmbientSpace :=
  WithLp.seminormedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance : NormedAddCommGroup MVEEAmbientSpace :=
  WithLp.normedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance : NormedSpace ℝ MVEEAmbientSpace :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance : InnerProductSpace ℝ MVEEAmbientSpace where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 SymmMat TailSpace x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

/- Theorem 5.4.5.1 lies in the minimum-volume enclosing-ellipsoid / barrier path-following domain.

Sampled owner-style declarations in this domain:
* `minimumVolumeEnclosingEllipsoidProblem` in `Chap05/Definition_5_4_5_1`, the source-facing
  owner of the MVEE feasible set and objective;
* `minimumVolumeEnclosingEllipsoidBarrierDomain`,
  `minimumVolumeEnclosingEllipsoidBarrierAmbient`, and
  `minimumVolumeEnclosingEllipsoidBarrier` in `Chap05/Definition_5_4_5_2`, the source-facing
  strict-domain MVEE barrier API;
* `logDetBarrierAmbient` in `Chap05/Definition_5_4_4_5`, the chapter bridge for the
  `-\log \det` contribution on symmetric matrices;
* `BarrierPathFollowingScheme` in `Chap05/Definition_5_3_4_1`, the chapter owner for the
  short-step path-following data.

Best owner abstraction:
* source-facing: the MVEE problem and barrier on strict-cone triples `(H, v, τ)`;
* core/canonical: `BarrierPathFollowingScheme`;
* bridge/view: the ambient symmetric-matrix product `𝕊^n × Eₙ × ℝ`, used only to host the
  self-concordant-barrier assumption needed by the path-following scheme.

Primitive data:
* the finite point family `a`.

Derived API:
* the raw ambient owner barrier from `Definition_5_4_5_2`, used directly on
  `𝕊^n × Eₙ × ℝ`;
* the path-following existence theorem.

This file therefore does not introduce a second public MVEE barrier owner. It uses a local
`L²` inner-product structure on the raw ambient product `𝕊^n × Eₙ × ℝ`, so that the theorem can
be stated directly on the owner ambient domain and ambient barrier from `Definition_5_4_5_2`
without exporting a parallel `WithLp` wrapper type. This is the ambient inner-product space
required by
`BarrierPathFollowingScheme`.
-/

section

variable (a : ι → Eₙ)

local notation "𝒟" => minimumVolumeEnclosingEllipsoidBarrierAmbientDomain a
local notation "F" => minimumVolumeEnclosingEllipsoidBarrierAmbient a
local notation "P" => minimumVolumeEnclosingEllipsoidProblem a

local notation "cτ" =>
  ((0 : SymmMat), (0 : Eₙ), (1 : ℝ))

-- Proof sketch: specialize the standard short-step path-following existence and complexity theory
-- to the MVEE objective vector `cτ` and to the owner ambient barrier `F` from
-- `Definition_5_4_5_2`.

/-- Theorem 5.4.5.1: if the MVEE feasible region has nonempty interior and the logarithmic
barrier from `Definition_5_4_5_2`, given directly by the owner ambient barrier `F`, is an
`(Fintype.card ι + n + 1)`-self-concordant barrier on `𝒟`, then there exists a path-following
interior-point scheme whose stopping iterate is `ε`-accurate for the MVEE problem and whose
stopping index is bounded by `O(√(Fintype.card ι + n + 1) log ((Fintype.card ι + n) / ε))`. -/
theorem exists_minimumVolumeEnclosingEllipsoidPathFollowingScheme
    [IsSelfConcordantBarrierOnWith 𝒟 (Fintype.card ι + n + 1) F]
    (hstrict : Set.Nonempty 𝒟)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ beta : ℝ,
      ∃ gamma : ℝ,
        ∃ C : NNReal,
          ∃ x0 : 𝒟,
            ∃ scheme : BarrierPathFollowingScheme
              cτ
              F
              (Fintype.card ι + n + 1)
              x0 beta gamma ε,
              scheme.stopIndex ≤
                  ⌈(C : ℝ) * Real.sqrt (Fintype.card ι + n + 1 : ℝ) *
                    Real.log ((Fintype.card ι + n : ℝ) / ε)⌉₊ ∧
                ∀ y ∈ (minimumVolumeEnclosingEllipsoidProblem a).feasibleSet,
                  (scheme scheme.stopIndex).2.2 ≤ P y + ε := sorry

end

end

/-! ### Theorem_5_4_5_2 (from Chap05) -/
namespace MaximumVolumeInscribedEllipsoid

noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "TailSpace" => E × ℝ
local notation "InscribedAmbientSpace" => SymmMat × TailSpace

noncomputable local instance : SeminormedAddCommGroup TailSpace :=
  WithLp.seminormedAddCommGroupToProd 2 E ℝ

noncomputable local instance : NormedAddCommGroup TailSpace :=
  WithLp.normedAddCommGroupToProd 2 E ℝ

noncomputable local instance : NormedSpace ℝ TailSpace :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E ℝ

noncomputable local instance : InnerProductSpace ℝ TailSpace where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E ℝ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance : CompleteSpace TailSpace := inferInstance

noncomputable local instance : SeminormedAddCommGroup InscribedAmbientSpace :=
  WithLp.seminormedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance : NormedAddCommGroup InscribedAmbientSpace :=
  WithLp.normedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance : NormedSpace ℝ InscribedAmbientSpace :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 SymmMat TailSpace

noncomputable local instance : InnerProductSpace ℝ InscribedAmbientSpace where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 SymmMat TailSpace x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

/- Theorem 5.4.5.2 lies in the maximum-volume-inscribed-ellipsoid / barrier path-following
domain.

Sampled owner-style declarations in this domain:
* `RealSymmetricMatrixSpace.frobeniusInner` and the induced Frobenius/submodule normed-space
  structure in `Chap05/Definition_5_4_4_2`, the chapter owner layer for the ambient geometry on
  `𝕊^n`;
* `optimizationProblem` in `Chap05/Definition_5_4_5_6`, the source-facing owner of the convex
  reformulation on `(G, v, τ)`;
* `logarithmicBarrierDomain`, `logarithmicBarrierAmbientDomain`, `logarithmicBarrierAmbient`, and
  `logarithmicBarrier` in `Chap05/Definition_5_4_5_7`, the source-facing strict-domain barrier
  API and its exported ambient bridge for the same variables;
* `logDetBarrierAmbient` in `Chap05/Definition_5_4_4_5`, the chapter bridge for the
  `-log det` contribution on ambient symmetric matrices;
* `BarrierPathFollowingScheme` in `Chap05/Definition_5_3_4_1`, the chapter owner for short-step
  path-following data.

Best owner abstraction:
* source-facing: the inscribed-ellipsoid optimization problem and barrier on strict-cone triples
  `(G, v, τ)`;
* core/canonical: the Chapter 5 Frobenius/submodule inner-product geometry on `𝕊^n`, together
  with `BarrierPathFollowingScheme`;
* bridge/view: the raw ambient `L²` product `𝕊^n × E × ℝ`, used only to host the objective
  direction and the self-concordant-barrier assumption.

Primitive data:
* the half-space data `a`, `b`;
* the owner feasible set and owner strict barrier domain from `Definition_5_4_5_6` and
  `Definition_5_4_5_7`.

Derived API:
* the path-following existence theorem, whose stopping iterate is bridged back to an owner
  feasible point of `optimizationProblem a b`.

This refinement reuses the exported ambient bridge from `Definition_5_4_5_7` rather than
recreating a private raw pullback inside the theorem file. The theorem therefore speaks directly
in the chapter’s public maximum-volume-inscribed-ellipsoid barrier vocabulary.
-/

section

variable (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)

local notation "𝒟" => logarithmicBarrierAmbientDomain a b
local notation "F" => logarithmicBarrierAmbient a b

local notation "cτ" => ((0 : SymmMat), (0 : E), (1 : ℝ))
local notation "P" => optimizationProblem a b

-- Proof sketch: an ambient strict barrier point already records strict positivity of the shape
-- variable and strict slack inequalities. Forgetting strictness therefore canonically yields an
-- owner feasible point of `optimizationProblem a b`.
/-- The shape component of an ambient strict barrier point canonically lies in `𝕊ⁿ₊₊`. -/
theorem ambientPoint_shape_mem
    (x : 𝒟) :
    x.1.1 ∈ (𝕊^n₊₊ : Set SymmMat) := by
  exact ((mem_logarithmicBarrierAmbientDomain_iff a b x.1.1 x.1.2.1 x.1.2.2).1 x.2).1

/-- The strict shape component of an ambient strict barrier point, viewed in the owner carrier
`𝕊ⁿ₊₊`. -/
abbrev ambientPointShape
    (x : 𝒟) : 𝕊^n₊₊ :=
  ⟨x.1.1, ambientPoint_shape_mem a b x⟩

-- Proof sketch: strict ambient-domain membership gives `τ - logDetBarrierAmbient n G > 0` and
-- strict second-order-cone inequalities. Weakening `<` to `≤` and restricting `G` to the strict
-- cone produces feasible-set membership for `optimizationProblem a b`.
/-- Every ambient strict barrier point canonically determines a feasible point of the owner
optimization problem by forgetting the strict inequalities to their nonstrict feasible-set
counterparts. -/
theorem ambientPoint_mem_feasibleSet
    (x : 𝒟) :
    (ambientPointShape a b x, x.1.2.1, x.1.2.2) ∈ (optimizationProblem a b).feasibleSet := by
  rcases (mem_logarithmicBarrierAmbientDomain_iff a b x.1.1 x.1.2.1 x.1.2.2).1 x.2 with
    ⟨_, hτ, hslack⟩
  change (ambientPointShape a b x, x.1.2.1, x.1.2.2) ∈ feasibleSet a b
  rw [mem_feasibleSet_iff]
  constructor
  · have hτ' : -Real.log (((x.1.1 : SymmMat) : Mat).det) < x.1.2.2 := by
      have hτ'' : 0 < x.1.2.2 + Real.log (((x.1.1 : SymmMat) : Mat).det) := by
        simpa [logDetBarrierAmbient] using hτ
      linarith
    exact le_of_lt (by simpa [ambientPointShape, logDetBarrier, logDetBarrierAmbient] using hτ')
  · rw [inscribedEllipsoid_subset_innerLePolyhedron_iff]
    intro i
    simpa [ambientPointShape, StrictPositiveSemidefiniteCone.toMatrix_def] using le_of_lt (hslack i)

/-- The canonical feasible point of `optimizationProblem a b` attached to an ambient strict
barrier point. -/
def ambientPointToFeasiblePoint
    (x : 𝒟) : (optimizationProblem a b).feasibleSet :=
  ⟨(ambientPointShape a b x, x.1.2.1, x.1.2.2), ambientPoint_mem_feasibleSet a b x⟩

namespace BarrierPathFollowingScheme

/-- The canonical owner feasible point determined by the stopping iterate of the inscribed-
ellipsoid path-following scheme. -/
abbrev stopFeasiblePoint
    [IsSelfConcordantBarrierOnWith 𝒟 (2 * m + n + 1) F]
    {β γ ε : ℝ} {x0 : 𝒟}
    (scheme : BarrierPathFollowingScheme cτ F (2 * m + n + 1) x0 β γ ε) :
    (optimizationProblem a b).feasibleSet :=
  ambientPointToFeasiblePoint a b
    ⟨scheme scheme.stopIndex, scheme.mem_domain scheme.stopIndex⟩

end BarrierPathFollowingScheme

-- Proof sketch: specialize the standard short-step path-following existence theory to the
-- exported ambient bridge `F` on `𝒟` from `Definition_5_4_5_7`, then bridge the stopping
-- iterate to the canonical owner feasible point
-- `BarrierPathFollowingScheme.stopFeasiblePoint a b scheme` of the optimization problem from
-- `Definition_5_4_5_6`. The iteration constant `C` is chosen uniformly, before the accuracy
-- parameter `ε`.

/-- Theorem 5.4.5.2: if the inscribed-ellipsoid logarithmic barrier from
`Definition_5_4_5_7`, given directly by the exported owner ambient barrier `F` on the exported
ambient domain `𝒟`, is a `(2m + n + 1)`-self-concordant barrier, then there exists a
positive iteration constant `C`, uniform in `ε`, such that for every `ε > 0` there exists a
path-following interior-point scheme whose stopping iterate canonically determines the owner
feasible point `BarrierPathFollowingScheme.stopFeasiblePoint a b scheme`, satisfies
`P (BarrierPathFollowingScheme.stopFeasiblePoint a b scheme) ≤ P y + ε` for every feasible `y`,
and whose stopping index is bounded by `O(√(2m + n + 1) log ((m + n) / ε))`. -/
theorem exists_maximumVolumeInscribedEllipsoidPathFollowingScheme
    [IsSelfConcordantBarrierOnWith 𝒟 (2 * m + n + 1) F]
    (hstrict : Set.Nonempty 𝒟) :
    ∃ C : NNRealˣ,
      ∀ {ε : ℝ}, 0 < ε →
        ∃ β : ℝ,
          ∃ γ : ℝ,
          ∃ x0 : 𝒟,
            ∃ scheme : BarrierPathFollowingScheme
              cτ
              F
              (2 * m + n + 1)
              x0 β γ ε,
                (∀ y ∈ (optimizationProblem a b).feasibleSet,
                  P (BarrierPathFollowingScheme.stopFeasiblePoint a b scheme) ≤ P y + ε) ∧
                scheme.stopIndex ≤
                  ⌈((C : NNReal) : ℝ) * Real.sqrt (2 * m + n + 1 : ℝ) *
                    Real.log ((m + n : ℝ) / ε)⌉₊ := sorry

end

end

end MaximumVolumeInscribedEllipsoid

/-! ### Definition_5_4_6_1 (from Chap05) -/
noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 5.4.6.1 lies in the chapter's cone-ordered second-derivative domain for
vector-valued `C³` maps.

Sampled owner declarations:
* `ConvexCone ℝ E₂`, the canonical owner for the ambient cone order;
* `ContDiffOn ℝ 3 ξ (interior Q₁)`, the canonical `C³` owner on the interior domain;
* `iteratedFDerivWithin ℝ 2 ξ (interior Q₁) x (fun _ ↦ h)`, the canonical second within-domain
  directional derivative expression;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the later owner in the same subsection that
  builds on this same derivative-level data.

Source/core/bridge triage:
* source-facing: `IsThreeTimesContDiffConcaveOnWith Q₁ K ξ`;
* core/canonical: mathlib's `ConvexCone`, `ContDiffOn`, and `iteratedFDerivWithin`;
* bridge/view: the class projections together with the inherited closedness instance for `K`.

Primitive data:
* the domain `Q₁`;
* the cone `K`;
* the map `ξ`;
* closedness and convexity of `Q₁`;
* closedness of `K`;
* `C³` regularity of `ξ` on `interior Q₁`;
* the cone-order second-derivative condition on `interior Q₁`.

Derived API:
* the field projections of `IsThreeTimesContDiffConcaveOnWith`;
* the canonical `Fact` instance supplying closedness of the cone owner `K`.

This keeps Definition 5.4.6.1 as the source-facing owner while deleting the exact-interface local
wrapper around `iteratedFDerivWithin`. Closedness of the cone is carried through the canonical
`ConvexCone` owner instead of remaining a parallel primitive projection. -/

/-- Definition 5.4.6.1: a map `ξ : Q₁ → E₂` is three times continuously differentiable and
concave with respect to the closed convex cone `K` when `Q₁` is a closed convex set, `K` is
closed, `ξ` is `C^3` on `interior Q₁`, and `-D²ξ(x)[h,h]` belongs to `K` for every
`x ∈ interior Q₁` and every direction `h`. -/
class IsThreeTimesContDiffConcaveOnWith
    (Q₁ : Set E₁) (K : ConvexCone ℝ E₂) (ξ : E₁ → E₂) : Prop
    extends Fact (IsClosed (K : Set E₂)) where
  /-- The domain set `Q₁` is closed. -/
  isClosed_domain : IsClosed Q₁
  /-- The domain set `Q₁` is convex. -/
  convex_domain : Convex ℝ Q₁
  /-- The map `ξ` is three-times continuously differentiable on `interior Q₁`. -/
  contDiffOn : ContDiffOn ℝ 3 ξ (interior Q₁)
  /-- The negated second within-domain directional derivative of `ξ` belongs to `K` at every
  interior point of `Q₁`. -/
  neg_second_directional_derivative_mem {x : E₁} (hx : x ∈ interior Q₁) (h : E₁) :
      -iteratedFDerivWithin ℝ 2 ξ (interior Q₁) x (fun _ ↦ h) ∈ K

attribute [instance] IsThreeTimesContDiffConcaveOnWith.toFact

end

/-! ### Definition_5_4_6_2 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u v

section Derivatives

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 5.4.6.2 lies in the chapter's cone-ordered higher-derivative / barrier-compatibility
domain for vector-valued maps.

Sampled owner declarations:
* mathlib `iteratedFDeriv`, the canonical multilinear owner for repeated Fréchet derivatives;
* `secondDirectionalDerivative` and `thirdDirectionalDerivative` from `Definition_5_0_10`, the
  chapter's scalar directional-derivative owners built from the same `iteratedFDeriv` data;
* `hessianLocalNorm` / notation `‖h‖[F; x]` from `Definition_5_1_1`, the chapter owner for the
  barrier-side Hessian factor;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the canonical owner for the barrier
  hypothesis.

Source/core/bridge triage:
* source-facing: `IsBetaCompatibleWith Q₁ K F β ξ`;
* core/canonical: `iteratedFDeriv` and `hessianLocalNorm`;
* bridge/view: the short vector-valued repeated-direction abbreviations below.

Primitive data:
* the domain `Q₁`, cone `K`, barrier `F`, parameter `β`, and map `ξ`;
* convexity and interior nonemptiness of `Q₁`;
* the lower bound `1 ≤ β`;
* existence of a self-concordant barrier structure on `interior Q₁`;
* `C³` regularity of `ξ` on `interior Q₁`;
* the cone-order compatibility inequality.

Derived API:
* `vectorSecondDirectionalDerivative` and `vectorThirdDirectionalDerivative`, which only package
  repeated evaluation of `iteratedFDeriv`;
* the theorem-level owner consequence exposing the defining compatibility inequality from an
  ambient instance.

The owner abstraction stays `IsBetaCompatibleWith`; only the repeated-direction bridge names are
kept as a small shared vocabulary for the subsection, so downstream files can reuse them instead
of re-declaring parallel local copies. -/

/-- The repeated second Fréchet derivative `D²ξ(x)[h, h]` of a vector-valued map `ξ`. -/
abbrev vectorSecondDirectionalDerivative (ξ : E₁ → E₂) (x h : E₁) : E₂ :=
  iteratedFDeriv ℝ 2 ξ x (fun _ ↦ h)

/-- The repeated third Fréchet derivative `D³ξ(x)[h, h, h]` of a vector-valued map `ξ`. -/
abbrev vectorThirdDirectionalDerivative (ξ : E₁ → E₂) (x h : E₁) : E₂ :=
  iteratedFDeriv ℝ 3 ξ x (fun _ ↦ h)

end Derivatives

section Compatibility

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Definition 5.4.6.2: a map `ξ : E₁ → E₂` is `β`-compatible with the barrier `F` relative to
the cone `K` when `Q₁` is convex with nonempty interior, `β ≥ 1`, `F` is a self-concordant
barrier on `interior Q₁`, `ξ` is three-times continuously differentiable on `interior Q₁`, and
for every `x ∈ interior Q₁` and every direction `h` the cone-order inequality
`D^3 ξ(x)[h,h,h] \preceq_K -3 β D^2 ξ(x)[h,h] ⟨∇²F(x) h, h⟩^{1/2}` holds, encoded as membership
of the difference in `K`. -/
class IsBetaCompatibleWith
    (Q₁ : Set E₁) (K : ConvexCone ℝ E₂) (F : E₁ → ℝ) (β : NNReal) (ξ : E₁ → E₂) : Prop where
  /-- The domain set `Q₁` is convex. -/
  convex_domain : Convex ℝ Q₁
  /-- The domain set `Q₁` has nonempty interior. -/
  interior_nonempty : (interior Q₁).Nonempty
  /-- The compatibility parameter satisfies `β ≥ 1`. -/
  one_le_parameter : 1 ≤ β
  /-- The scalar function `F` is a self-concordant barrier on `interior Q₁` for some barrier
  parameter. -/
  selfConcordantBarrier :
    ∃ ν : NNReal, IsSelfConcordantBarrierOnWith (interior Q₁) ν F
  /-- The map `ξ` is three-times continuously differentiable on `interior Q₁`. -/
  contDiffOn : ContDiffOn ℝ 3 ξ (interior Q₁)
  /-- The third derivative of `ξ` is dominated by the negated second derivative scaled by the
  local Hessian norm of the barrier, in the cone order induced by `K`. -/
  compatibility_bound {x : E₁} (hx : x ∈ interior Q₁) (h : E₁) :
      (3 * (β : ℝ) * ‖h‖[F; x]) •
          (-vectorSecondDirectionalDerivative ξ x h) -
        vectorThirdDirectionalDerivative ξ x h ∈ K

namespace IsBetaCompatibleWith

/-- A `β`-compatibility instance canonically supplies the defining cone-order derivative bound on
`interior Q₁`. -/
theorem compatibility_bound_of_mem
    {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {β : NNReal} {ξ : E₁ → E₂}
    [hβ : IsBetaCompatibleWith Q₁ K F β ξ] {x : E₁} (hx : x ∈ interior Q₁) (h : E₁) :
    (3 * (β : ℝ) * ‖h‖[F; x]) •
        (-vectorSecondDirectionalDerivative ξ x h) -
      vectorThirdDirectionalDerivative ξ x h ∈ K :=
  hβ.compatibility_bound hx h

end IsBetaCompatibleWith

end Compatibility

/-! ### Definition_5_4_6_3 (from Chap05) -/
universe u v w uR

section

variable {R : Type uR}
variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
variable [Semiring R] [PartialOrder R]
variable [AddCommGroup E₂] [SMul R E₂]

/- Definition 5.4.6.3 lies in the chapter's cone-composition feasible-set domain.

Sampled owner declarations:
* mathlib `ConvexCone R E₂`, the canonical owner for the ambient cone order;
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter's standard owner/view pattern for source-facing feasible-set constructions on product
  spaces;
* `power_cone_plus` from `Definition_5_4_7_4`, the later source-facing power-cone owner obtained
  by specializing this construction;
* `entropyEpigraphCone` from `Definition_5_4_7_8`, the later entropy-epigraph owner obtained by
  the same specialization pattern.

Source/core/bridge triage:
* source-facing: `coneCompositionFeasibleSet Q₁ K ξ Q₂`;
* core/canonical: the cone owner `ConvexCone R E₂` together with ordinary `Set` membership on
  product spaces;
* bridge/view: the membership expansion lemma.

Primitive data:
* the domain `Q₁`;
* the cone `K` at the primitive ordered-semiring action layer;
* the map `ξ`;
* the downstream feasible set `Q₂`.

Derived API:
* the canonical pair-membership expansion lemma for the owner set.

The source-facing owner here is the composed feasible set itself. The intermediate pair relation
is only implementation scaffolding, so this refinement deletes that wrapper and keeps the single
owner spelling reused downstream in `Theorem_5_4_6_13`. -/

/-- Definition 5.4.6.3: the feasible set obtained by composing `Q₂` with the cone-order
domination relation induced by `ξ` and `K`. -/
def coneCompositionFeasibleSet
    (Q₁ : Set E₁) (K : ConvexCone R E₂) (ξ : E₁ → E₂)
    (Q₂ : Set (E₂ × E₃)) : Set (E₁ × E₃) :=
  { p | ∃ y : E₂, p.1 ∈ Q₁ ∧ ξ p.1 - y ∈ K ∧ (y, p.2) ∈ Q₂ }

-- Proof sketch: unfold `coneCompositionFeasibleSet`.
/-- A pair `p` lies in `coneCompositionFeasibleSet Q₁ K ξ Q₂` exactly when there exists
`y : E₂` with `p.1 ∈ Q₁`, `ξ p.1 - y ∈ K`, and `(y, p.2) ∈ Q₂`. -/
@[simp] theorem mem_coneCompositionFeasibleSet_iff
    (Q₁ : Set E₁) (K : ConvexCone R E₂) (ξ : E₁ → E₂)
    (Q₂ : Set (E₂ × E₃)) {p : E₁ × E₃} :
    p ∈ coneCompositionFeasibleSet Q₁ K ξ Q₂ ↔
      ∃ y : E₂, p.1 ∈ Q₁ ∧ ξ p.1 - y ∈ K ∧ (y, p.2) ∈ Q₂ :=
  Iff.rfl

end

/-! ### Definition_5_4_6_4 (from Chap05) -/
open Set Topology
open scoped Gradient

noncomputable section

universe u v

/- Definition 5.4.6.4 lies in the Chapter 5 self-concordant-barrier / recession-direction /
product-gradient domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the barrier owner;
* `IsSelfConcordantBarrierOnWith.inner_gradient_nonpos_of_recession_direction` from
  `Corollary_5_3_2`, the canonical barrier-owner recession-direction consequence;
* mathlib `WithLp 2 (E₂ × E₃)` together with `WithLp.toLp` / `WithLp.ofLp`, the canonical `L²`
  product owner and its bridge back to raw pairs;
* mathlib `Convex.interior` and `Convex.add_smul_mem_interior`, the canonical convex-interior API
  that transfers recession directions from a convex set to its interior;
* `sum_partialGradient_pairings_eq_inner_gradient_pair` from `Theorem_5_4_6_4`, the chapter's
  canonical `L²` product-gradient decomposition owner theorem on an arbitrary direction `(u, v)`.

Source/core/bridge triage:
* source-facing: the cone-indexed nonpositivity statement for the `y`-gradient pairing;
* core/canonical: the barrier owner `IsSelfConcordantBarrierOnWith Q ν Φ`;
* bridge/view: mathlib's convex-interior recession-direction transfer and the slice-gradient versus
  product-gradient pairing identity.

Primitive data:
* the convex set `Q₂`;
* the source-facing barrier existence datum
  `∃ ν : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) ν Φ`;
* the cone `K` and the recession-direction hypothesis for `(s, 0)`.

Derived API:
* the internal affine-pullback barrier on the canonical `L²` product owner, obtained from
  `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` along `WithLp.ofLp`;
* the imported owner-method consequence
  `IsSelfConcordantBarrierOnWith.inner_gradient_nonpos_of_recession_direction`;
* the product-gradient bridge `sum_partialGradient_pairings_eq_inner_gradient_pair`.

The barrier recession inequality already belongs to the barrier owner in `Corollary_5_3_2`, and
the convex-to-interior recession transfer already belongs to mathlib's convex-interior API, so
this file should not keep parallel public duplicates of either fact. The source-facing theorem
below is kept only as the finite-dimensional product bridge from those owner declarations to the
`(s, 0)` recession-direction situation, matching the product-gradient API that already exists in
`Theorem_5_4_6_4`. -/

section Product

variable {E₂ : Type u} {E₃ : Type v}
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
variable [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

noncomputable local instance : SeminormedAddCommGroup (E₂ × E₃) :=
  WithLp.seminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance : NormedAddCommGroup (E₂ × E₃) :=
  WithLp.normedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance : NormedSpace ℝ (E₂ × E₃) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance : InnerProductSpace ℝ (E₂ × E₃) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E₂ E₃ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance : CompleteSpace (E₂ × E₃) := inferInstance

local notation "Z" => WithLp 2 (E₂ × E₃)
local notation "ofZ" => (WithLp.ofLp : Z → E₂ × E₃)

-- Proof sketch: apply
-- `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` to pull the source-facing barrier
-- `Φ` on `interior Q₂` back along the canonical map `WithLp.ofLp`, then apply
-- `IsSelfConcordantBarrierOnWith.inner_gradient_nonpos_of_recession_direction` to that internal
-- `L²` product-owner barrier and the direction `WithLp.toLp 2 (s, 0)`. Use
-- mathlib's
-- `Convex.interior` and `Convex.add_smul_mem_interior` to pass from recession directions of `Q₂`
-- to recession directions of `interior Q₂`, then rewrite the resulting product-space pairing with
-- `sum_partialGradient_pairings_eq_inner_gradient_pair` specialized to the direction `(s, 0)`.
/-- Definition 5.4.6.4: if every direction `(s, 0)` with `s ∈ K` is a recession direction of the
convex set `Q₂`, then at every interior point `(y, z)` the pairing of the `y`-gradient of a
barrier `Φ` with `s` is nonpositive. The existence of a self-concordant barrier parameter for `Φ`
on `interior Q₂` is the only barrier input needed here. The `L²` product owner `WithLp 2
(E₂ × E₃)` is used only
internally through the canonical affine pullback along `WithLp.ofLp`. -/
theorem barrier_yGradient_pairing_nonpos
    {Q₂ : Set (E₂ × E₃)} (hQ₂_convex : Convex ℝ Q₂) (K : ConvexCone ℝ E₂)
    {Φ : E₂ × E₃ → ℝ}
    (hΦ : ∃ ν : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) ν Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄, s ∈ (K : Set E₂) →
        ∀ ⦃p : E₂ × E₃⦄, p ∈ Q₂ → ∀ τ : ℝ, 0 ≤ τ → p + τ • (s, (0 : E₃)) ∈ Q₂)
    {y : E₂} {z : E₃} (hyz : (y, z) ∈ interior Q₂) {s : E₂} (hs : s ∈ (K : Set E₂)) :
    inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) s ≤ 0 := by
  rcases hΦ with ⟨ν, hΦ⟩
  let g : Z →ᴬ[ℝ] E₂ × E₃ :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap).toContinuousAffineMap
  let hΦZ : IsSelfConcordantBarrierOnWith (ofZ ⁻¹' interior Q₂) ν (Φ ∘ ofZ) :=
    by
      simpa [g, Function.comp] using hΦ.comp_continuousAffineMap g
  have hyzZ : WithLp.toLp 2 (y, z) ∈ ofZ ⁻¹' interior Q₂ := by
    simpa using hyz
  have hrecessionZ :
      ∀ ⦃w : Z⦄, w ∈ ofZ ⁻¹' interior Q₂ →
        ∀ τ : ℝ, 0 ≤ τ → w + τ • WithLp.toLp 2 (s, (0 : E₃)) ∈ ofZ ⁻¹' interior Q₂ := by
    intro w hw τ hτ
    let p : E₂ × E₃ := w.ofLp
    let d : E₂ × E₃ := (s, (0 : E₃))
    let x : E₂ × E₃ := p + (2 * τ) • d
    have hp : p ∈ interior Q₂ := by
      simpa [p] using hw
    have hx : x ∈ Q₂ := by
      simpa [p, d, x] using hK_recession hs (interior_subset hp) (2 * τ) (by positivity)
    have hy : x + (-(2 * τ) • d) ∈ interior Q₂ := by
      convert hp using 1
      simp [p, d, x, add_assoc]
    have hmid :=
      hQ₂_convex.add_smul_mem_interior hx hy (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioc 0 1)
    have hsum : (2 * τ) • d + -τ • d = τ • d := by
      rw [← add_smul]
      have h : (2 * τ : ℝ) + -τ = τ := by ring
      rw [h]
    have hinterior : p + τ • d ∈ interior Q₂ := by
      convert hmid using 1
      rw [show x = p + (2 * τ) • d by rfl, smul_smul]
      have hcoeff : (1 / 2 : ℝ) * (-(2 * τ)) = -τ := by ring
      rw [hcoeff]
      simpa [add_assoc] using congrArg (fun v : E₂ × E₃ ↦ p + v) hsum.symm
    simpa [p, d] using hinterior
  have hpair :
      inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) s =
        inner ℝ
          (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (y, z)))
          (WithLp.toLp 2 (s, (0 : E₃))) := by
    let hstdZ : IsStandardSelfConcordantOn (ofZ ⁻¹' interior Q₂) (Φ ∘ ofZ) :=
      hΦZ.toIsStandardSelfConcordantOn
    have hdiffZ : DifferentiableAt ℝ (Φ ∘ ofZ) (WithLp.toLp 2 (y, z)) := by
      simpa using
        (hstdZ.contDiffOn.contDiffAt (hstdZ.isOpen_domain.mem_nhds hyzZ)).differentiableAt
          (by norm_num)
    have hpair0 :
        inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) s +
            inner ℝ (∇ (fun z' : E₃ ↦ Φ (y, z')) z) (0 : E₃) =
          inner ℝ
            (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (y, z)))
            (WithLp.toLp 2 (s, (0 : E₃))) :=
      sum_partialGradient_pairings_eq_inner_gradient_pair hdiffZ
    simpa using hpair0
  calc
    inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) s =
        inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (y, z))) (WithLp.toLp 2 (s, (0 : E₃))) :=
      hpair
    _ ≤ 0 :=
      hΦZ.inner_gradient_nonpos_of_recession_direction hrecessionZ hyzZ

end Product

end

/-! ### Definition_5_4_6_5 (from Chap05) -/
noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}

/- Definition 5.4.6.5 lies in the subsection's composed-barrier domain.

Sampled owner declarations:
* ordinary product-space function evaluation, the canonical ambient owner layer for a barrier on
  `E₁ × E₃`;
* `coneCompositionFeasibleSet` from `Definition_5_4_6_3`, the adjacent source-facing set owner
  paired with this barrier later in the subsection;
* `compositionPotential` from `Definition_5_4_6_6`, the nearby source-facing owner for the
  unweighted term `(x, z) ↦ Φ (ξ x, z)`;
* the downstream canonical directional-derivative owners from `Definition_5_4_6_9`, obtained by
  applying `lineDeriv`, `secondDirectionalDerivative`, and `thirdDirectionalDerivative` to this
  barrier.

Source/core/bridge triage:
* source-facing: `coneCompositionBarrier F Φ ξ β`;
* core/canonical: the plain function `E₁ × E₃ → ℝ`;
* bridge/view: the pointwise evaluation lemma below.

Primitive data:
* the inner barrier `F`;
* the outer barrier `Φ`;
* the map `ξ`;
* the parameter `β`.

Derived API:
* the pointwise formula for evaluating the owner function.

No higher packaged abstraction is needed here: the mathematics is exactly the concrete barrier
function on the product space, so the refined owner remains the plain function with a single
atomic evaluation lemma. The redundant extensionality wrapper is deleted in favor of the owner
definition itself. -/

/-- Definition 5.4.6.5: given a barrier `F` on `Q₁`, a barrier `Φ` on `Q₂`, a map `ξ : Q₁ → E₂`,
and a compatibility parameter `β`, the composed barrier on pairs `(x, z)` is
`Ψ(x, z) = Φ(ξ(x), z) + β^3 F(x)`. -/
def coneCompositionBarrier
    (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal) : E₁ × E₃ → ℝ :=
  fun p ↦ Φ (ξ p.1, p.2) + ((β : ℝ) ^ 3) * F p.1

-- Proof sketch: unfold `coneCompositionBarrier`; the definition evaluates `Φ` at the pair
-- `(ξ x, z)` and adds the scaled barrier term `β^3 F x`.
/-- Evaluating `coneCompositionBarrier F Φ ξ β` at `(x, z)` reproduces the textbook formula
`Ψ(x, z) = Φ(ξ(x), z) + β^3 F(x)`. -/
@[simp] theorem coneCompositionBarrier_apply
    (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal) (x : E₁) (z : E₃) :
    coneCompositionBarrier F Φ ξ β (x, z) = Φ (ξ x, z) + ((β : ℝ) ^ 3) * F x :=
  rfl

end
