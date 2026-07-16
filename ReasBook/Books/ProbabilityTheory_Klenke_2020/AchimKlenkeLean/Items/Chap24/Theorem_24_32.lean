import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap24.Definition_24_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

namespace ProbabilityTheory

/-- The descending list of simplex coordinates before zero-padding to an infinite sequence. -/
def orderedDirichletList {n : ℕ} (x : dirichletSimplex n) : List ℝ :=
  (List.ofFn x.1).mergeSort (fun a b ↦ decide (b ≤ a))

/-- The ordered coordinate sequence of a simplex point, padded by zeros after the first `n`
coordinates. -/
def orderedDirichletSequence {n : ℕ} (x : dirichletSimplex n) : ℕ → ℝ :=
  fun k ↦ (orderedDirichletList x).getD k 0

/-- Expanding `orderedDirichletSequence` gives the sorted-coordinate list padded with zeros. -/
theorem orderedDirichletSequence_def {n : ℕ} (x : dirichletSimplex n) :
    orderedDirichletSequence x = fun k ↦ (orderedDirichletList x).getD k 0 := rfl

-- Proof sketch: the coordinate map to a finite list is measurable, finite list sorting is a
-- measurable operation on a finite-dimensional Euclidean space, and `getD` is coordinatewise
-- measurable after padding by the constant zero tail.
/-- The ordered zero-padded coordinate map on the Dirichlet simplex is measurable. -/
theorem measurable_orderedDirichletSequence (n : ℕ) :
    Measurable (orderedDirichletSequence : dirichletSimplex n → ℕ → ℝ) := sorry

/-- The symmetric Dirichlet shape vector with all coordinates equal to `θ / n`. -/
def symmetricDirichletParameters (θ : NNReal) (n : ℕ+) : Fin (n : ℕ) → ℝ :=
  fun _ ↦ (θ : ℝ) / (n : ℝ)

-- Proof sketch: the common shape parameter is positive because `θ > 0` and the positive integer
-- `n` has positive real coercion.
/-- Positive `θ` gives positive symmetric Dirichlet shape parameters. -/
theorem symmetricDirichletParameters_pos {θ : NNReal} (hθ : 0 < θ) (n : ℕ+) :
    ∀ i, 0 < symmetricDirichletParameters θ n i := by
  intro i
  dsimp [symmetricDirichletParameters]
  refine div_pos ?_ ?_
  · exact_mod_cast hθ
  · exact_mod_cast n.pos

/-- The infinite ordered law obtained by sorting a symmetric Dirichlet sample on `n` coordinates
and padding the remaining coordinates by zero. -/
noncomputable def orderedSymmetricDirichletLaw (θ : NNReal) (hθ : 0 < θ)
    (n : ℕ+) : ProbabilityMeasure (ℕ → ℝ) :=
  ProbabilityMeasure.map
    (dirichletDistribution (symmetricDirichletParameters θ n)
      (symmetricDirichletParameters_pos hθ n))
    (measurable_orderedDirichletSequence (n : ℕ)).aemeasurable

-- Proof sketch: when `n = 1`, the symmetric Dirichlet law is concentrated on the unique simplex
-- point `(1, 0, 0, ...)`, so the ordered padded law is the corresponding Dirac measure.
/-- The one-dimensional ordered symmetric Dirichlet law is the Dirac mass at `(1, 0, 0, ...)`. -/
theorem orderedSymmetricDirichletLaw_one (θ : NNReal) (hθ : 0 < θ) :
    orderedSymmetricDirichletLaw θ hθ 1 =
      ⟨MeasureTheory.Measure.dirac (fun k : ℕ ↦ if k = 0 then 1 else 0), inferInstance⟩ := sorry

/-- The local candidate for the Poisson--Dirichlet law `PD_θ`, realized as the filter-limit value
of the ordered symmetric Dirichlet laws. -/
noncomputable def poissonDirichletLimitLaw (θ : NNReal) (hθ : 0 < θ) : ProbabilityMeasure (ℕ → ℝ) :=
  Filter.lim (Filter.map (fun n : ℕ+ ↦ orderedSymmetricDirichletLaw θ hθ n) Filter.atTop)

/-- Expanding `poissonDirichletLimitLaw` gives the filter limit of the ordered symmetric Dirichlet
laws. -/
theorem poissonDirichletLimitLaw_def (θ : NNReal) (hθ : 0 < θ) :
    poissonDirichletLimitLaw θ hθ =
      Filter.lim (Filter.map (fun n : ℕ+ ↦ orderedSymmetricDirichletLaw θ hθ n) Filter.atTop) :=
  rfl

-- Proof sketch: couple the symmetric Dirichlet vector with the normalized jump masses of the
-- gamma subordinator from Definition 24.31, use the interval-partition construction from
-- Corollary 24.28 to obtain coordinatewise lower bounds on the ordered coordinates, and then apply
-- Fatou's lemma together with conservation of total mass to upgrade `liminf` inequalities to
-- coordinatewise almost-sure convergence. Weak convergence of the laws follows by mapping almost-
-- sure convergence through the canonical law map.
/-- Theorem 24.32: for `θ > 0`, the laws of the decreasing rearrangements of symmetric Dirichlet
partitions `Dir_{θ / n; n}` converge weakly to the Poisson--Dirichlet law `PD_θ`, represented here
by the local limit law `poissonDirichletLimitLaw θ hθ`. -/
theorem tendsto_orderedSymmetricDirichletLaw_poissonDirichletLimit
    (θ : NNReal) (hθ : 0 < θ) :
    Tendsto (fun n : ℕ+ ↦ orderedSymmetricDirichletLaw θ hθ n) atTop
      (𝓝 (poissonDirichletLimitLaw θ hθ)) := sorry

end ProbabilityTheory
