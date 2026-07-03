import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_4_1
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_5_6
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_5_7

-- Declarations for this item will be appended below by the statement pipeline.

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
