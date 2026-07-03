import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_30 (from Chap03) -/
universe uE uι

variable {E : Type uE} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 3.30 is a recall-only item in the chapter's sampled affine-model aggregation domain.

Primary domain:
- convex optimization models obtained by averaging sampled affine minorants.

Sampled owner-style declarations:
- `StdSimplex.Strict` in `LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_4`, the earlier chapter owner for
  the textbook's strict-positivity side condition on simplex coefficients
- `sampledAffineMinorant` in `LecturesConvexOptimization_Nesterov_2018.Chap03.Proposition_3_26`, the chapter owner for one
  sampled affine oracle model
- the mathlib affine-map sum
  `∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i)) : E →ᵃ[ℝ] ℝ`,
  the canonical owner for the aggregated model
- `sum_smul_sampledAffineMinorant_apply` in `LecturesConvexOptimization_Nesterov_2018.Chap03.Proposition_3_26`, the evaluation
  bridge for that canonical affine-map sum

Best owner abstraction:
- `source-facing`: the textbook aggregated linear model built from sampled points
  `y₀, …, y_N`, weights, and the sampled slopes `g (y k)`
- `core/canonical`: the affine-map sum
  `∑ i, α i • sampledAffineMinorant (y i) (g i) (f (y i))`
- `bridge/view`: the simplex specialization `α = weights.weights` together with the sampled slope
  family `g ∘ y`; `StdSimplex.Strict` records the source's redundant strict-positivity side
  condition when needed, while the later affine-map owner in
  `LecturesConvexOptimization_Nesterov_2018.Chap03.Proposition_3_27` is the corresponding packaged affine view of the same
  finite averaging construction

Primitive data:
- `weights : StdSimplex ℝ (Fin (N + 1))`
- `y : Fin (N + 1) → E`
- `f : E → ℝ`
- `g : E → E`

Derived API:
- the owner specialization
  `∑ i, weights.weights i • sampledAffineMinorant (y i) (g (y i)) (f (y i))`
- the pointwise sum formula obtained by unfolding that owner definition

Source/core/bridge triage:
- `source-facing`: the sampled aggregated linear model itself
- `core/canonical`: the affine-map sum above
- `bridge/view`: evaluation of the simplex specialization by
  `sum_smul_sampledAffineMinorant_apply`

Definition 3.30 adds no new mathematical data beyond this owner specialization, so this file
checks the canonical owner expression directly and introduces no parallel public alias such as
`aggregatedLinearModel`.
-/

section

variable {N : ℕ}

variable (weights : StdSimplex ℝ (Fin (N + 1))) (y : Fin (N + 1) → E)
variable (f : E → ℝ) (g : E → E) (x : E)

/- Definition 3.30: the aggregated linear model attached to sample points `y₀, …, y_N` and a
normalized coefficient vector is the direct simplex specialization of the canonical affine-map
sum of the sampled affine minorants. The textbook additionally assumes these weights are strictly
positive, but the defining expression depends only on the normalized simplex data. -/
#check (∑ i, weights.weights i • sampledAffineMinorant (y i) (g (y i)) (f (y i)) : E →ᵃ[ℝ] ℝ)

/- Evaluating the canonical affine-map sum for Definition 3.30 recovers the weighted sum of the
sampled affine oracle models. -/
#check (sum_smul_sampledAffineMinorant_apply weights.weights y (g ∘ y) f x)

end

/-! ### Lemma_3_30 (from Chap03) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open EllipsoidMethod

attribute [local instance] Classical.decPred

/- Lemma 3.30 lies in the chapter's ellipsoid-method localization-containment domain.

Mandatory domain-style sampling before refinement:
- `feasibleSubsequence` and
  `feasibleSubsequence_count_eq_self_of_feasible` in `Definition_3_53`, the chapter owners for
  the source-facing feasible subsequence and counter `i(k)`;
- `localizationSets` in `Definition_3_52`, the source-facing recursive retained-region family;
- `GeneralCuttingPlaneScheme.selectedLocalizationSets_subset_localizer` in `Algorithm_3_6`, the
  canonical selected-feasible containment theorem for any cutting-plane localizer;
- `EllipsoidMethod.toGeneralCuttingPlaneScheme` in `Algorithm_3_8`, the bridge from the
  ellipsoid recursion to the generic cutting-plane owner;
- `EllipsoidMethod.associatedEllipsoid` in `Algorithm_3_8`, the ellipsoid localizer supplied by
  that bridge.

Best owner abstraction:
- source-facing: the selected-feasible localization stage
  `S_(i(k)) = localizationSets Q (feasibleSubsequence Q y)`
  `(problem.oracle ∘ feasibleSubsequence Q y) (i(k))`;
- core/canonical: `GeneralCuttingPlaneScheme.selectedLocalizationSets_subset_localizer`;
- bridge/view: the theorem below, which specializes that owner theorem to ellipsoids through
  `toGeneralCuttingPlaneScheme`.

Primitive data:
- the ambient convex minimization problem with separation oracle;
- the initial center and radius;
- the standard ellipsoid hypotheses `1 < n`, nonzero cut directions, initial ellipsoid cover, and
  positive definiteness of the shape matrices.

Derived API:
- the raw ellipsoid center sequence `y_k = center problem initialCenter radius k`;
- the feasible subsequence `feasibleSubsequence problem.feasibleSet y`;
- the selected feasible counter
  `i(k) = Nat.count (fun j ↦ y j ∈ problem.feasibleSet) k`;
- the associated ellipsoid sequence `E_k`;
- the ellipsoid specialization of the generic selected-stage containment theorem.

The previous version still owned this result at the ellipsoid layer. But the induction only uses
the generic cutting-plane localizer step, the oracle's infeasible-point half-space containment,
`feasibleSubsequence`, and `Nat.count`. This refinement therefore moves the actual owner theorem
to `GeneralCuttingPlaneScheme` and keeps Lemma 3.30 as the ellipsoid specialization through
`toGeneralCuttingPlaneScheme`: the selected localization set `S_(i(k))` built from feasible
queried centers still lies in the raw stage-`k` ellipsoid `E_k`.
-/

namespace EllipsoidMethod

section

/-- Lemma 3.30: let `y_k = center problem initialCenter radius k` be the ellipsoid-method query
sequence, let `i(k) = Nat.count (fun j ↦ y j ∈ problem.feasibleSet) k` be the canonical
selected-feasible counter from Definition 3.53, and let
`X = feasibleSubsequence problem.feasibleSet y` be the corresponding feasible subsequence. Then
the selected recursive localization stage `S_(i(k))` built from the feasible queried centers and
their oracle cuts is contained in the raw stage-`k` associated ellipsoid `E_k`. -/
theorem selectedLocalizationSets_subset_associatedEllipsoid
    (problem : ConvexMinimizationWithSeparationOracle (EuclideanSpace ℝ (Fin n)))
    (initialCenter : E) (radius : ℝ)
    (hn : 1 < n)
    (hcut_nonzero : ∀ k : ℕ, cuttingVector problem initialCenter radius k ≠ 0)
    (hE0_cover :
      problem.feasibleSet ⊆ associatedEllipsoid problem initialCenter radius 0)
    (hshape_pos : ∀ k : ℕ, (shape problem initialCenter radius k).PosDef)
    (k : ℕ) :
    let y : ℕ → E := center problem initialCenter radius
    let X : ℕ → E := feasibleSubsequence problem.feasibleSet y
    let S : ℕ → Set E := localizationSets problem.feasibleSet X (problem.oracle ∘ X)
    let i : ℕ → ℕ := Nat.count (fun j ↦ y j ∈ problem.feasibleSet)
    S (i k) ⊆ associatedEllipsoid problem initialCenter radius k := by
  -- View the ellipsoid recursion as the canonical cutting-plane scheme from Algorithm 3.8.
  let scheme :=
    toGeneralCuttingPlaneScheme problem initialCenter radius hn hcut_nonzero hE0_cover hshape_pos
  -- Specialize the generic selected-localization containment theorem to this ellipsoid scheme.
  simpa [scheme, toGeneralCuttingPlaneScheme] using
    scheme.selectedLocalizationSets_subset_localizer k

end

end EllipsoidMethod

/-! ### Proposition_3_30 (from Chap03) -/
noncomputable section

/- Proposition 3.30 lies in the finite-dimensional Nemirovski hard-instance minimization domain.

Mandatory domain-style sampling before refinement:
- `f_k`, `FirstKIndex`, and `firstKCoordinateFamily` in `Definition_3_35`, the chapter owner
  surface for the hard-instance objective and its first-`k` coordinate family;
- `IsMinOn` and `isMinOn_univ_iff`, the canonical owner API for unconstrained minimizers on
  `Set.univ`;
- `EuclideanSpace.equiv` and `EuclideanSpace.norm_eq`, the canonical coordinate and norm API on
  `EuclideanSpace ℝ (Fin n)`.

Best owner abstraction:
- source-facing: the explicit optimizer/value statement for `f_k`;
- core/canonical: `f_k`, `IsMinOn`, `EuclideanSpace.equiv`, and the Euclidean norm;
- bridge/view: the coordinate evaluation lemma for the explicit optimizer.

Primitive data:
- the ambient dimension `n`;
- the prefix length `k`;
- the hard-instance parameters `μ` and `γ`.

Derived API:
- the explicit vector `f_k_minimizer`;
- the coordinate formula `f_k_minimizer_apply`;
- the minimizing property, attained value, and norm formula below.

Source/core/bridge triage:
- source-facing: the explicit optimizer/value/norm formulas in Proposition 3.30;
- core/canonical: `f_k`, `IsMinOn`, `EuclideanSpace.equiv`, and `‖·‖`;
- bridge/view: the coordinate evaluation lemma for the pointwise minimizer.

This file keeps the source-facing explicit optimizer, but it no longer rebuilds the first-`k`
support through a basis-sum package. The primitive owner data is the pointwise coordinate formula,
and the explicit coordinate theorem is the public bridge back to the textbook description. -/

/-- The explicit minimizer from Proposition 3.30, with constant value `-γ / (μ k)` on the first
`k` coordinates and value `0` afterwards. -/
def f_k_minimizer (n k : ℕ) (μ γ : ℝ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i ↦ if i.1 < k then -(γ / (μ * (k : ℝ))) else 0)

/-- The coordinates of `f_k_minimizer` are constant on the first `k` slots and vanish afterwards. -/
@[simp] theorem f_k_minimizer_apply (n k : ℕ) (μ γ : ℝ) (i : Fin n) :
    f_k_minimizer n k μ γ i = if i.1 < k then -(γ / (μ * (k : ℝ))) else 0 :=
  rfl

section

variable (n k : ℕ) (μ γ : ℝ)

/-- Helper for Proposition 3.30: each of the first `k` coordinates is bounded above by the
prefix maximum. -/
theorem first_k_coordinate_le_first_k_coordinate_max
    (hk : 0 < k) (hkn : k ≤ n) (x : EuclideanSpace ℝ (Fin n)) (i : Fin k) :
    x (Fin.castLE hkn i) ≤ first_k_coordinate_max n k x := by
  let _ : Nonempty (FirstKIndex n k) := firstKIndex_nonempty (n := n) hk hkn
  -- Rewrite the real-valued maximum as the finite supremum over the restricted coordinate family.
  rw [← WithTop.coe_le_coe]
  rw [coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ (n := n) (k := k) (x := x)]
  rw [pointwiseSupremumOn_univ_eq_sup']
  let j : FirstKIndex n k := ⟨Fin.castLE hkn i, by simp [i.2]⟩
  have hj : j ∈ (Finset.univ : Finset (FirstKIndex n k)) := by
    simp [j]
  exact Finset.le_sup' (fun a : FirstKIndex n k ↦ firstKCoordinateFamily n k x a) hj

/-- Helper for Proposition 3.30: the average of the first `k` coordinates is bounded above by the
prefix maximum. -/
theorem sum_prefix_coordinates_le_mul_first_k_coordinate_max
    (hk : 0 < k) (hkn : k ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i : Fin k, x (Fin.castLE hkn i) ≤ (k : ℝ) * first_k_coordinate_max n k x := by
  have hcoord : ∀ i : Fin k, x (Fin.castLE hkn i) ≤ first_k_coordinate_max n k x := by
    -- Bound each active coordinate by the common prefix maximum.
    intro i
    exact first_k_coordinate_le_first_k_coordinate_max n k hk hkn x i
  -- Summing the coordinatewise bounds yields the textbook average-max inequality.
  calc
    ∑ i : Fin k, x (Fin.castLE hkn i) ≤ ∑ i : Fin k, first_k_coordinate_max n k x := by
      exact Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = (k : ℝ) * first_k_coordinate_max n k x := by
      simp [mul_comm]

/-- Helper for Proposition 3.30: completing the square in a single active coordinate. -/
theorem complete_square_f_k_prefix_term (hk : 0 < k) (hμ : 0 < μ) (t : ℝ) :
    (μ / 2) * t ^ 2 + (γ / (k : ℝ)) * t =
      (μ / 2) * (t + γ / (μ * (k : ℝ))) ^ 2 - γ ^ 2 / (2 * μ * (k : ℝ) ^ 2) := by
  -- The source proof uses a direct scalar square-completion identity.
  field_simp [hk.ne', hμ.ne']
  ring

/-- Helper for Proposition 3.30: the source lower bound
`-(γ^2) / (2 μ k) ≤ f_k(x)` for all `x`. -/
theorem f_k_ge_neg_sq_div_two_mul_mu_mul_k
    (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) (hγ : 0 ≤ γ)
    (x : EuclideanSpace ℝ (Fin n)) :
    -(γ ^ 2) / (2 * μ * (k : ℝ)) ≤ f_k n k μ γ x := by
  let sq : ℕ → ℝ := fun i ↦ if hi : i < n then x ⟨i, hi⟩ ^ 2 else 0
  let coord : ℕ → ℝ := fun i ↦ if hi : i < n then x ⟨i, hi⟩ else 0
  have hprefix :
      (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) ≤ γ * first_k_coordinate_max n k x := by
    -- Multiply the textbook average-max inequality by `γ / k` and simplify the right-hand side.
    have hsum := sum_prefix_coordinates_le_mul_first_k_coordinate_max n k hk hkn x
    have hscaled := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ γ / (k : ℝ))
    calc
      (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) ≤
          (γ / (k : ℝ)) * ((k : ℝ) * first_k_coordinate_max n k x) := hscaled
      _ = γ * first_k_coordinate_max n k x := by
        field_simp [hk.ne']
  have hnorm :
      ‖x‖ ^ 2 = ∑ i ∈ Finset.range n, sq i := by
    -- Rewrite the squared norm as a finite sum of coordinate squares.
    calc
      ‖x‖ ^ 2 = ∑ i : Fin n, x i ^ 2 := by
        simpa using (EuclideanSpace.real_norm_sq_eq x)
      _ = ∑ i : Fin n, sq i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [sq]
      _ = ∑ i ∈ Finset.range n, sq i := Fin.sum_univ_eq_sum_range sq n
  have hprefix_bound :
      -(γ ^ 2) / (2 * μ * (k : ℝ)) ≤
        Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i + (γ / (k : ℝ)) * coord i) := by
    -- Complete the square coordinatewise on the active prefix.
    have hconst_sum :
        Finset.sum (Finset.range k) (fun _ ↦ -(γ ^ 2) / (2 * μ * (k : ℝ) ^ 2)) =
          -(γ ^ 2) / (2 * μ * (k : ℝ)) := by
      simp
      field_simp [hk.ne', hμ.ne']
    calc
      -(γ ^ 2) / (2 * μ * (k : ℝ)) =
          Finset.sum (Finset.range k) (fun _ ↦ -(γ ^ 2) / (2 * μ * (k : ℝ) ^ 2)) := by
            rw [hconst_sum]
      _ ≤ Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i + (γ / (k : ℝ)) * coord i) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hi_lt_n : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hkn
            have hsquare :
                0 ≤ (μ / 2) * (x ⟨i, hi_lt_n⟩ + γ / (μ * (k : ℝ))) ^ 2 := by
              positivity
            have hterm :
                -(γ ^ 2) / (2 * μ * (k : ℝ) ^ 2) ≤
                  (μ / 2) * (x ⟨i, hi_lt_n⟩) ^ 2 + (γ / (k : ℝ)) * x ⟨i, hi_lt_n⟩ := by
              rw [complete_square_f_k_prefix_term (k := k) (μ := μ) (γ := γ) hk hμ
                (x ⟨i, hi_lt_n⟩)]
              calc
                -(γ ^ 2) / (2 * μ * (k : ℝ) ^ 2) =
                    (0 : ℝ) - (γ ^ 2) / (2 * μ * (k : ℝ) ^ 2) := by
                      ring
                _ ≤ (μ / 2) * (x ⟨i, hi_lt_n⟩ + γ / (μ * (k : ℝ))) ^ 2 -
                      (γ ^ 2) / (2 * μ * (k : ℝ) ^ 2) := by
                      exact sub_le_sub_right hsquare ((γ ^ 2) / (2 * μ * (k : ℝ) ^ 2))
            simpa [sq, coord, hi_lt_n] using hterm
  have htail_nonneg :
      0 ≤ Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) := by
    -- The tail contributes only nonnegative quadratic terms.
    refine Finset.sum_nonneg ?_
    intro i hi
    have hi_lt_n : i < n := (Finset.mem_Ico.mp hi).2
    have hterm : 0 ≤ (μ / 2) * x ⟨i, hi_lt_n⟩ ^ 2 := by
      positivity
    simpa [sq, hi_lt_n] using hterm
  have hsq_decomp :
      (μ / 2) * (∑ i ∈ Finset.range n, sq i) + (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) =
        Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i + (γ / (k : ℝ)) * coord i) +
          Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) := by
    -- Split the norm square into prefix and tail coordinates and collect like terms.
    have hcoord_sum :
        (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) =
          Finset.sum (Finset.range k) (fun i ↦ (γ / (k : ℝ)) * coord i) := by
      calc
        (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) =
            ∑ i : Fin k, (γ / (k : ℝ)) * coord i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i _
              have hi_lt_n : (i : ℕ) < n := lt_of_lt_of_le i.2 hkn
              have hcast : (Fin.castLE hkn i : Fin n) = ⟨i, hi_lt_n⟩ := by
                ext
                simp
              simp [coord, hi_lt_n, hcast]
        _ = Finset.sum (Finset.range k) (fun i ↦ (γ / (k : ℝ)) * coord i) := by
              simpa using (Fin.sum_univ_eq_sum_range (fun i ↦ (γ / (k : ℝ)) * coord i) k)
    calc
      (μ / 2) * (∑ i ∈ Finset.range n, sq i) + (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) =
          (μ / 2) * ((Finset.sum (Finset.range k) sq) + Finset.sum (Finset.Ico k n) sq) +
            Finset.sum (Finset.range k) (fun i ↦ (γ / (k : ℝ)) * coord i) := by
              rw [← Finset.sum_range_add_sum_Ico sq hkn, hcoord_sum]
      _ =
          Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i) +
            Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) +
            Finset.sum (Finset.range k) (fun i ↦ (γ / (k : ℝ)) * coord i) := by
              rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      _ =
          Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) +
            (Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i) +
              Finset.sum (Finset.range k) (fun i ↦ (γ / (k : ℝ)) * coord i)) := by
              ring
      _ =
          Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) +
            Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i + (γ / (k : ℝ)) * coord i) := by
              rw [← Finset.sum_add_distrib]
      _ =
          Finset.sum (Finset.range k) (fun i ↦ (μ / 2) * sq i + (γ / (k : ℝ)) * coord i) +
            Finset.sum (Finset.Ico k n) (fun i ↦ (μ / 2) * sq i) := by
              ring
  have hsquares :
      -(γ ^ 2) / (2 * μ * (k : ℝ)) ≤
        (μ / 2) * (∑ i ∈ Finset.range n, sq i) + (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) := by
    -- The completed-square lower bound plus tail nonnegativity gives the scalar lower bound.
    rw [hsq_decomp]
    nlinarith
  -- Replace the prefix average term by the larger maximum term and return to `f_k`.
  rw [f_k_def, hnorm]
  have hmain :
      (μ / 2) * (∑ i ∈ Finset.range n, sq i) + (γ / (k : ℝ)) * ∑ i : Fin k, x (Fin.castLE hkn i) ≤
        (μ / 2) * (∑ i ∈ Finset.range n, sq i) + γ * first_k_coordinate_max n k x := by
    nlinarith
  linarith

/-- Helper for Proposition 3.30: the prefix maximum of the explicit minimizer is its common active
coordinate value. -/
theorem first_k_coordinate_max_f_k_minimizer
    (hk : 0 < k) (hkn : k ≤ n) :
    first_k_coordinate_max n k (f_k_minimizer n k μ γ) = -(γ / (μ * (k : ℝ))) := by
  let _ : Nonempty (FirstKIndex n k) := firstKIndex_nonempty (n := n) hk hkn
  -- All active coordinates are equal, so the finite supremum is that same constant.
  rw [← WithTop.coe_inj]
  rw [coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ (n := n) (k := k)
    (x := f_k_minimizer n k μ γ)]
  rw [pointwiseSupremumOn_univ_eq_sup']
  have hconst :
      ∀ i : FirstKIndex n k,
        firstKCoordinateFamily n k (f_k_minimizer n k μ γ) i =
          (-(γ / (μ * (k : ℝ))) : WithTop ℝ) := by
    -- Every element of `FirstKIndex n k` lies in the constant active block of the minimizer.
    intro i
    simp [firstKCoordinateFamily, f_k_minimizer_apply, i.2]
  simp [hconst]

/-- Helper for Proposition 3.30: the explicit minimizer has the expected squared norm. -/
theorem norm_sq_f_k_minimizer
    (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) :
    ‖f_k_minimizer n k μ γ‖ ^ 2 = γ ^ 2 / (μ ^ 2 * (k : ℝ)) := by
  let sq : ℕ → ℝ := fun i ↦ if hi : i < n then (f_k_minimizer n k μ γ) ⟨i, hi⟩ ^ 2 else 0
  have hnorm :
      ‖f_k_minimizer n k μ γ‖ ^ 2 = ∑ i ∈ Finset.range n, sq i := by
    -- Rewrite the squared norm as the finite sum of coordinate squares.
    calc
      ‖f_k_minimizer n k μ γ‖ ^ 2 =
          ∑ i : Fin n, (f_k_minimizer n k μ γ) i ^ 2 := by
            simpa using (EuclideanSpace.real_norm_sq_eq (f_k_minimizer n k μ γ))
      _ = ∑ i : Fin n, sq i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [sq]
      _ = ∑ i ∈ Finset.range n, sq i := Fin.sum_univ_eq_sum_range sq n
  rw [hnorm]
  rw [← Finset.sum_range_add_sum_Ico sq hkn]
  have htail : ∑ i ∈ Finset.Ico k n, sq i = 0 := by
    -- The minimizer vanishes on all coordinates beyond the active prefix.
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_lt_n : i < n := (Finset.mem_Ico.mp hi).2
    have hk_le_i : k ≤ i := (Finset.mem_Ico.mp hi).1
    simp [sq, hi_lt_n, f_k_minimizer_apply, not_lt.mpr hk_le_i]
  rw [htail, add_zero]
  calc
    ∑ i ∈ Finset.range k, sq i = ∑ i ∈ Finset.range k, (γ / (μ * (k : ℝ))) ^ 2 := by
      -- On the active prefix, every coordinate has the same absolute value.
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi_lt_n : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hkn
      have hi_lt_k : i < k := Finset.mem_range.mp hi
      simp [sq, hi_lt_n, f_k_minimizer_apply, hi_lt_k]
    _ = (k : ℝ) * (γ / (μ * (k : ℝ))) ^ 2 := by
      simp
    _ = γ ^ 2 / (μ ^ 2 * (k : ℝ)) := by
      field_simp [hk.ne', hμ.ne']

/-- Helper for Proposition 3.30: evaluating `f_k` at the explicit minimizer gives the displayed
optimal value. -/
theorem f_k_minimizer_value_eq
    (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) :
    f_k n k μ γ (f_k_minimizer n k μ γ) = -(γ ^ 2) / (2 * μ * (k : ℝ)) := by
  -- Evaluate `f_k` by inserting the explicit norm and prefix-maximum formulas.
  rw [f_k_def]
  rw [first_k_coordinate_max_f_k_minimizer n k μ γ hk hkn]
  rw [norm_sq_f_k_minimizer n k μ γ hk hkn hμ]
  field_simp [hk.ne', hμ.ne']
  ring

-- Proof sketch: for `γ ≥ 0`, bound the first-coordinate maximum from below by the average of the
-- first `k` coordinates, complete the square, and evaluate the resulting lower bound at
-- `f_k_minimizer`.
/-- Proposition 3.30: if `0 < k ≤ n`, `μ > 0`, and `γ ≥ 0`, then the explicit vector
`f_k_minimizer n k μ γ` is a global minimizer of `f_k n k μ γ`. -/
theorem isMinOn_f_k_minimizer (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) (hγ : 0 ≤ γ) :
    IsMinOn (f_k n k μ γ) Set.univ (f_k_minimizer n k μ γ) := by
  rw [isMinOn_univ_iff]
  intro x
  -- Compare every point to the common lower bound attained by the explicit minimizer.
  have hlower := f_k_ge_neg_sq_div_two_mul_mu_mul_k n k μ γ hk hkn hμ hγ x
  have hvalue := f_k_minimizer_value_eq n k μ γ hk hkn hμ
  linarith

/-- If `0 < k ≤ n`, `μ > 0`, and `γ ≥ 0`, evaluating `f_k` at the explicit minimizer gives the
value `-γ^2 / (2 μ k)`. -/
theorem f_k_minimizer_value (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) (_hγ : 0 ≤ γ) :
    f_k n k μ γ (f_k_minimizer n k μ γ) = -(γ ^ 2) / (2 * μ * (k : ℝ)) := by
  -- This is the explicit evaluation established in the helper above.
  exact f_k_minimizer_value_eq n k μ γ hk hkn hμ

-- Proof sketch: compute the squared norm from the `k` equal nonzero coordinates and then take the
-- square root, using `k ≤ n` to identify exactly how many coordinates contribute.
/-- If `0 < k ≤ n`, `μ > 0`, and `γ ≥ 0`, the norm of the explicit minimizer is
`γ / (μ √k)`. -/
theorem f_k_minimizer_norm_eq (hk : 0 < k) (hkn : k ≤ n) (hμ : 0 < μ) (hγ : 0 ≤ γ) :
    ‖f_k_minimizer n k μ γ‖ = γ / (μ * Real.sqrt (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast hk
  have hsqrtk_ne : Real.sqrt (k : ℝ) ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr hkR
  have hsq :
      ‖f_k_minimizer n k μ γ‖ ^ 2 =
        (γ / (μ * Real.sqrt (k : ℝ))) ^ 2 := by
    -- Rewrite the squared norm into the square of the claimed closed form.
    rw [norm_sq_f_k_minimizer n k μ γ hk hkn hμ]
    field_simp [hk.ne', hμ.ne', hsqrtk_ne]
    rw [Real.sq_sqrt hkR.le]
  have hsqrt := congrArg Real.sqrt hsq
  -- Taking square roots is valid because both sides are nonnegative.
  rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ γ / (μ * Real.sqrt (k : ℝ)))] at hsqrt

end

/-! ### Theorem_3_30 (from Chap03) -/
noncomputable section

universe u v

open scoped ConvexAnalysis

variable {X : Type u} {Y : Type v}

/- Theorem 3.30 lies in the chapter's infimal-projection / extended-real approximation domain.

Sampled owner-style declarations:
- chapter `partialInfProjection` in `Theorem_3_1_2_3`
- chapter `partialInfProjection_eq_sInf` in `Theorem_3_1_2_3`
- chapter `extendedRealRealPart_le_iff` in `Definition_3_1_1_3`
- mathlib `sInf`

Best owner abstraction:
- core/canonical owner: `partialInfProjection (Q := Set.univ)` for an unconstrained fiberwise
  infimum, valued in `EReal`
- source-facing theorem surface: the order comparison
  `partialInfProjection Set.univ F x ≤ (level : EReal)`
- finite-value bridge surface:
  `{x ∈ dom (partialInfProjection Set.univ F) | partialInfProjection Set.univ F x ≤ level}`

Primitive data:
- an extended-real objective `F : X × Y → EReal`

Derived API:
- the faithful set-level `EReal` sublevel characterization for the unconstrained infimal
  projection
- its pointwise reformulation
- the secondary finite-value bridge theorem on `dom (partialInfProjection Set.univ F)`

Source/core/bridge triage:
- source-facing: the approximation formula for the unconstrained infimal projection at the
  `EReal` order level
- core/canonical: `partialInfProjection` together with the order relation
  `partialInfProjection Set.univ F x ≤ (level : EReal)`
- bridge/view: intersecting with `dom` to recover the finite-value real sublevel surface

The earlier `dom`-cut theorem excluded fibers where `partialInfProjection Set.univ F = ⊥`, so it
was only a finite-value bridge and not the faithful main statement. This file restores the
canonical `EReal` order theorem as the main public entry and keeps the finite-value
`dom`-intersected reformulation only as a secondary bridge.
-/

/-- Helper for Theorem 3.30: the unconstrained partial infimal projection is bounded above by
every slice value. -/
lemma partialInfProjection_univ_le_slice
    (F : X × Y → EReal) (x : X) (y : Y) :
    partialInfProjection Set.univ F x ≤ F (x, y) := by
  -- Rewrite the unconstrained partial infimal projection as the infimum over the fiber above `x`.
  rw [partialInfProjection_eq_sInf]
  refine sInf_le ?_
  exact Set.mem_image_of_mem F ⟨by simp, rfl⟩

/-- Helper for Theorem 3.30: a real upper bound on a slice value upgrades a witness from the
effective domain of the infimal projection to the effective domain of that slice. -/
lemma slice_mem_dom_of_partialInfProjection_mem_dom_of_le_real
    {F : X × Y → EReal} {x : X} {y : Y} {r : ℝ}
    (hx : x ∈ dom (partialInfProjection Set.univ F))
    (hxy : F (x, y) ≤ (r : EReal)) :
    x ∈ dom (fun x : X ↦ F (x, y)) := by
  -- Show directly that the slice value is neither `⊤` nor `⊥`.
  rw [mem_extendedRealEffectiveDomain_iff]
  rcases mem_extendedRealEffectiveDomain_iff.mp hx with ⟨_, hproj_ne_bot⟩
  refine ⟨?_, ?_⟩
  · intro htop
    simp [htop] at hxy
  · intro hbot
    have hproj_le_bot : partialInfProjection Set.univ F x ≤ (⊥ : EReal) := by
      simpa [hbot] using partialInfProjection_univ_le_slice F x y
    exact hproj_ne_bot (le_antisymm hproj_le_bot bot_le)

/-- Theorem 3.30: the unconstrained infimal projection lies below the real level `λ` exactly on
the intersection, over all `ε > 0`, of the unions of the `(λ + ε)`-sublevel sets of the slices
`x ↦ F (x, y)`. This faithful `EReal` statement also covers fibers where the infimal projection
equals `⊥`. -/
theorem partialInfProjection_univ_sublevelSet_eq_iInter_iUnion
    (F : X × Y → EReal) (level : ℝ) :
    {x | partialInfProjection Set.univ F x ≤ (level : EReal)} =
      ⋂ ε > 0, ⋃ y : Y, {x | F (x, y) ≤ (level + ε : EReal)} := by
  ext x
  -- Evaluate the set identity at `x` so the goal becomes the textbook pointwise approximation
  -- formula.
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · intro hx ε hε
    -- Move from `partialInfProjection ≤ level` to a strict bound by `level + ε`, then extract a
    -- witness from the fiber infimum.
    by_cases hε_top : ε = ⊤
    · have hxpp : partialInfProjection Set.univ F x ≤ (level : EReal) := by
        simpa [partialInfProjection_eq_sInf] using hx
      have hproj_ne_top : partialInfProjection Set.univ F x ≠ ⊤ := by
        intro htop
        have hxpp' := hxpp
        rw [htop] at hxpp'
        simp at hxpp'
      have hlt : partialInfProjection Set.univ F x < (⊤ : EReal) :=
        lt_top_iff_ne_top.mpr hproj_ne_top
      rw [partialInfProjection_eq_sInf] at hlt
      rcases sInf_lt_iff.mp hlt with ⟨a, ha, ha_lt⟩
      rcases ha with ⟨⟨x', y⟩, ha_mem, rfl⟩
      rcases ha_mem with ⟨_, hx'⟩
      cases hx'
      rw [hε_top]
      exact ⟨y, ha_lt.le⟩
    · have hε_bot : ε ≠ ⊥ := by
        intro hε_bot
        simp [hε_bot] at hε
      lift ε to ℝ using ⟨hε_top, hε_bot⟩
      have hε_real : 0 < ε := EReal.coe_lt_coe_iff.mp hε
      have hlevel_lt : (level : EReal) < ((level + ε : ℝ) : EReal) := by
        exact_mod_cast (lt_add_of_pos_right level hε_real)
      have hlt : partialInfProjection Set.univ F x < ((level + ε : ℝ) : EReal) :=
        lt_of_le_of_lt hx hlevel_lt
      rw [partialInfProjection_eq_sInf] at hlt
      rcases sInf_lt_iff.mp hlt with ⟨a, ha, ha_lt⟩
      rcases ha with ⟨⟨x', y⟩, ha_mem, rfl⟩
      rcases ha_mem with ⟨_, hx'⟩
      cases hx'
      exact ⟨y, ha_lt.le⟩
  · intro hx
    -- If every positive `ε` admits a witness below `level + ε`, a real point strictly between
    -- `level` and the infimum contradicts the universal lower-bound property of the infimum.
    by_contra hle
    have hlt : (level : EReal) < partialInfProjection Set.univ F x := lt_of_not_ge hle
    rcases EReal.exists_between_coe_real hlt with ⟨μ, hlevel_μ, hμ_inf⟩
    have hε : (0 : EReal) < (μ : EReal) - level := by
      exact EReal.sub_pos.mpr hlevel_μ
    rcases hx ((μ : EReal) - level) hε with ⟨y, hy⟩
    have hsum : (level : EReal) + ((μ : EReal) - level) = (μ : EReal) := by
      calc
        (level : EReal) + ((μ : EReal) - level)
            = (level : EReal) + (((μ - level : ℝ)) : EReal) := by
                rw [← EReal.coe_sub]
        _ = (((level + (μ - level) : ℝ)) : EReal) := by
                rw [← EReal.coe_add]
        _ = (μ : EReal) := by simp
    have hy' : F (x, y) ≤ (μ : EReal) := by
      simpa [hsum] using hy
    have hcontra : (μ : EReal) < (μ : EReal) :=
      lt_of_lt_of_le hμ_inf (le_trans (partialInfProjection_univ_le_slice F x y) hy')
    exact (lt_irrefl (_ : EReal)) hcontra

/-- Pointwise form of Theorem 3.30. -/
theorem partialInfProjection_univ_le_iff_forall_pos_exists_le_add
    (F : X × Y → EReal) (x : X) (level : ℝ) :
    partialInfProjection Set.univ F x ≤ (level : EReal) ↔
      ∀ ε > 0, ∃ y : Y, F (x, y) ≤ (level + ε : EReal) := by
  simpa [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion] using
    congrArg (fun s : Set X ↦ x ∈ s)
      (partialInfProjection_univ_sublevelSet_eq_iInter_iUnion F level)

/-- Secondary finite-value bridge for Theorem 3.30: intersecting the faithful `EReal` theorem
with `dom (partialInfProjection Set.univ F)` recovers the textbook real-sublevel surface, which
forgets fibers where the infimal projection equals `⊥`. -/
theorem partialInfProjection_univ_sublevelSet_eq_dom_inter_iInter_iUnion
    (F : X × Y → EReal) (level : ℝ) :
    {x | x ∈ dom (partialInfProjection Set.univ F) ∧ partialInfProjection Set.univ F x ≤ level} =
      dom (partialInfProjection Set.univ F) ∩
        ⋂ ε > 0, ⋃ y : Y, {x | x ∈ dom (fun x : X ↦ F (x, y)) ∧ F (x, y) ≤ level + ε} := by
  ext x
  -- Evaluate the set equality at `x` and separate the domain condition from the approximation
  -- condition.
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · rintro ⟨hxdom, hlevel⟩
    refine ⟨hxdom, ?_⟩
    -- For finite positive `ε`, use the approximation theorem directly; for `ε = ⊤`, reuse one
    -- fixed finite witness.
    intro ε hε
    by_cases hε_top : ε = ⊤
    · have hone : (0 : EReal) < (1 : EReal) := by norm_num
      rcases (partialInfProjection_univ_le_iff_forall_pos_exists_le_add F x level).1 hlevel 1 hone
        with ⟨y, hy⟩
      refine ⟨y, ?_, ?_⟩
      · exact slice_mem_dom_of_partialInfProjection_mem_dom_of_le_real hxdom (by
          simpa [EReal.coe_add] using hy)
      · rw [hε_top]
        exact le_top
    · have hε_bot : ε ≠ ⊥ := by
        intro hε_bot
        simp [hε_bot] at hε
      lift ε to ℝ using ⟨hε_top, hε_bot⟩
      have hε_real : 0 < ε := EReal.coe_lt_coe_iff.mp hε
      rcases (partialInfProjection_univ_le_iff_forall_pos_exists_le_add F x level).1 hlevel ε
          (by exact_mod_cast hε_real) with ⟨y, hy⟩
      refine ⟨y, ?_, ?_⟩
      · exact slice_mem_dom_of_partialInfProjection_mem_dom_of_le_real hxdom (by
          simpa [EReal.coe_add] using hy)
      · simpa [EReal.coe_add] using hy
  · rintro ⟨hxdom, happrox⟩
    refine ⟨hxdom, ?_⟩
    -- Forget the slice-domain side condition and apply the faithful pointwise theorem backwards.
    refine (partialInfProjection_univ_le_iff_forall_pos_exists_le_add F x level).2 ?_
    intro ε hε
    rcases happrox ε hε with ⟨y, hy_dom, hy⟩
    exact ⟨y, hy⟩

end
