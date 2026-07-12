import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_4_1
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_5_4
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_5_5

-- Declarations for this item will be appended below by the statement pipeline.

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
