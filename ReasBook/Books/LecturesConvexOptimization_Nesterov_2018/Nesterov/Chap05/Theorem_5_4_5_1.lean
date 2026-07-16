import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_4_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_4_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_5_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_5_2

-- Declarations for this item will be appended below by the statement pipeline.

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
