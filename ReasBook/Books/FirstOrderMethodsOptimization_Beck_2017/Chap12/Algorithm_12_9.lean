import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_25
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_26
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_8
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp (toLp ofLp)

noncomputable section

section

variable {n p : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin p)

/- Algorithm 12.9 is `source-facing`: it specializes the finite-intersection FDPG recursion from
Algorithm 12.8 to the halfspaces `⟪a_i, x⟫ ≤ b_i` cut out by the rows of `A`.

Domain sampling in the surrounding chapter identifies the owner layers as follows.
- `source-facing`: the row normals `a_i`, the row halfspaces, and the specialized iterate families
  `u^k`, `y^k`, `w^k`;
- `core/canonical`:
  `DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication En p) 1`,
  `finite_intersection_projection_primal_point`, `finite_intersection_projection_dual_update`,
  and the iterate owners from Algorithm 12.8;
- `bridge/view`: the explicit halfspace projection formula from Chapter 6, used only to recover
  the displayed rowwise step-(b) formula under the active nonzeroness assumptions on the normals.

The primitive data are therefore the row halfspaces together with their rowwise nonemptiness
proofs, exactly matching the input layer of the finite-intersection owners. A nonempty feasible set
remains a source-facing sufficient condition, but only as a bridge theorem that derives those
rowwise hypotheses. The explicit denominator formula is derived API, not the defining owner of the
algorithm.
-/

/-- The `i`th row of `A`, viewed as the halfspace normal `a_i ∈ ℝ^n`. -/
def polyhedral_projection_halfspace_normal
    (A : Matrix (Fin p) (Fin n) ℝ) (i : Fin p) : En :=
  toLp 2 (fun j ↦ A i j)

/-- Evaluating the row-normal vector at coordinate `j` gives the matrix entry `A i j`. -/
@[simp] theorem polyhedral_projection_halfspace_normal_apply
    (A : Matrix (Fin p) (Fin n) ℝ) (i : Fin p) (j : Fin n) :
    polyhedral_projection_halfspace_normal A i j = A i j :=
  rfl

/-- Pairing the `i`th row normal with `x` recovers the `i`th coordinate of `A x`. -/
@[simp] theorem polyhedral_projection_halfspace_normal_inner
    (A : Matrix (Fin p) (Fin n) ℝ) (i : Fin p) (x : En) :
    inner ℝ (polyhedral_projection_halfspace_normal A i) x = A.toEuclideanLin x i := by
  calc
    inner ℝ (polyhedral_projection_halfspace_normal A i) x =
        dotProduct (fun j ↦ A i j) (ofLp x) := by
          simpa [polyhedral_projection_halfspace_normal, dotProduct_comm] using
            (EuclideanSpace.inner_toLp_toLp (fun j ↦ A i j) (ofLp x))
    _ = Matrix.mulVec A (ofLp x) i := by
          simp [Matrix.mulVec, dotProduct]
    _ = A.toEuclideanLin x i := by
          show Matrix.mulVec A (ofLp x) i = A.toEuclideanLin x i
          simp [Matrix.toEuclideanLin, Matrix.ofLp_toLpLin]

/-- The `i`th row halfspace `C_i = {x ∈ ℝ^n | ⟪a_i, x⟫ ≤ b_i}` associated to `A x ≤ b`. -/
def polyhedral_projection_halfspace
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (i : Fin p) : Set En :=
  halfSpace (polyhedral_projection_halfspace_normal A i) (b i)

/-- Membership in the `i`th row halfspace is exactly the `i`th scalar inequality of `A x ≤ b`. -/
@[simp] theorem mem_polyhedral_projection_halfspace_iff
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) (i : Fin p) (x : En) :
    x ∈ polyhedral_projection_halfspace A b i ↔ A.toEuclideanLin x i ≤ b i := by
  rw [polyhedral_projection_halfspace, mem_halfSpace_iff,
    polyhedral_projection_halfspace_normal_inner]

private theorem halfSpace_isClosed (a : En) (α : ℝ) :
    IsClosed (halfSpace a α) := by
  simpa [halfSpace] using isClosed_Iic.preimage (innerSL ℝ a).continuous

private theorem polyhedral_projection_halfspace_isClosed
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) :
    ∀ i, IsClosed (polyhedral_projection_halfspace A b i) := by
  intro i
  simpa [polyhedral_projection_halfspace] using
    halfSpace_isClosed (polyhedral_projection_halfspace_normal A i) (b i)

private theorem polyhedral_projection_halfspace_convex
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep) :
    ∀ i, Convex ℝ (polyhedral_projection_halfspace A b i) := by
  intro i
  simpa [polyhedral_projection_halfspace] using
    convex_halfSpace_owner (polyhedral_projection_halfspace_normal A i) (b i)

theorem polyhedral_projection_halfspace_nonempty_of_feasible_set_nonempty
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep)
    (hS_nonempty : (polyhedral_projection_feasible_set A b).Nonempty) :
    ∀ i, (polyhedral_projection_halfspace A b i).Nonempty := by
  intro i
  rcases hS_nonempty with ⟨x, hx⟩
  exact ⟨x, (mem_polyhedral_projection_halfspace_iff A b i x).2
    ((mem_polyhedral_projection_feasible_set A b).1 hx i)⟩

private theorem polyhedral_projection_halfspace_projectionPoint_eq
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep)
    (i : Fin p) (hCi_nonempty : (polyhedral_projection_halfspace A b i).Nonempty)
    (x : En) (ha : polyhedral_projection_halfspace_normal A i ≠ 0) :
    Pp[
        polyhedral_projection_halfspace A b i,
        hCi_nonempty,
        polyhedral_projection_halfspace_isClosed A b i,
        polyhedral_projection_halfspace_convex A b i] x =
      x - (((inner ℝ (polyhedral_projection_halfspace_normal A i) x - b i)⁺ /
        ‖polyhedral_projection_halfspace_normal A i‖ ^ (2 : ℕ)) •
        polyhedral_projection_halfspace_normal A i) := by
  have hx :
      Pp[
          polyhedral_projection_halfspace A b i,
          hCi_nonempty,
          polyhedral_projection_halfspace_isClosed A b i,
          polyhedral_projection_halfspace_convex A b i] x ∈
        ({x - (((inner ℝ (polyhedral_projection_halfspace_normal A i) x - b i)⁺ /
          ‖polyhedral_projection_halfspace_normal A i‖ ^ (2 : ℕ)) •
          polyhedral_projection_halfspace_normal A i)} : Set En) := by
    change Pp[
        halfSpace (polyhedral_projection_halfspace_normal A i) (b i),
        hCi_nonempty,
        halfSpace_isClosed (polyhedral_projection_halfspace_normal A i) (b i),
        convex_halfSpace_owner (polyhedral_projection_halfspace_normal A i) (b i)] x ∈
      ({x - (((inner ℝ (polyhedral_projection_halfspace_normal A i) x - b i)⁺ /
        ‖polyhedral_projection_halfspace_normal A i‖ ^ (2 : ℕ)) •
        polyhedral_projection_halfspace_normal A i)} : Set En)
    rw [← projection_mapping_halfSpace_eq_singleton_positivePartCorrection
      (polyhedral_projection_halfspace_normal A i) x (b i) ha]
    rw [projection_mapping_eq_singleton_of_nonempty_closed_convex
      (halfSpace (polyhedral_projection_halfspace_normal A i) (b i))
      hCi_nonempty
      (halfSpace_isClosed (polyhedral_projection_halfspace_normal A i) (b i))
      (convex_halfSpace_owner (polyhedral_projection_halfspace_normal A i) (b i))
      x]
    simp
  simpa using hx

/-- Algorithm 12.9: given row halfspaces `C_i = {x | ⟪a_i, x⟫ ≤ b_i}` with rowwise nonemptiness
(for example, when the full feasible set `A x ≤ b` is nonempty), an admissible constant parameter
`L ≥ p`, and an initialization `w⁰ = y⁰ = y0 ∈ (ℝ^n)^p`, the second FDPG dual sequence is the
Algorithm 12.8 specialization to those halfspaces. -/
def polyhedral_projection_second_fdpg_y
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep)
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : En)
    (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication En p) 1)
    (y0 : Fin p → En) :
    ℕ → Fin p → En :=
  finite_intersection_fdpg_y
    (polyhedral_projection_halfspace A b)
    hC_nonempty
    (polyhedral_projection_halfspace_isClosed A b)
    (polyhedral_projection_halfspace_convex A b)
    L d y0

/-- The second-FDPG extrapolated block sequence `w^k`. -/
def polyhedral_projection_second_fdpg_w
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep)
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : En)
    (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication En p) 1)
    (y0 : Fin p → En) :
    ℕ → Fin p → En :=
  finite_intersection_fdpg_w
    (polyhedral_projection_halfspace A b)
    hC_nonempty
    (polyhedral_projection_halfspace_isClosed A b)
    (polyhedral_projection_halfspace_convex A b)
    L d y0

/-- The auxiliary primal sequence `u^k = ∑ i, w_i^k + d` derived from the second FDPG iterates. -/
def polyhedral_projection_second_fdpg_u
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep)
    (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
    (d : En)
    (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication En p) 1)
    (y0 : Fin p → En) :
    ℕ → En :=
  finite_intersection_fdpg_u
    (polyhedral_projection_halfspace A b)
    hC_nonempty
    (polyhedral_projection_halfspace_isClosed A b)
    (polyhedral_projection_halfspace_convex A b)
    L d y0

section

variable (A : Matrix (Fin p) (Fin n) ℝ) (b : Ep)
variable (hC_nonempty : ∀ i, (polyhedral_projection_halfspace A b i).Nonempty)
variable (d : En)
variable (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication En p) 1)
variable (y0 : Fin p → En)

local notation "C" => polyhedral_projection_halfspace A b
local notation "hC_closed" => polyhedral_projection_halfspace_isClosed A b
local notation "hC_convex" => polyhedral_projection_halfspace_convex A b
local notation "a[" i "]" => polyhedral_projection_halfspace_normal A i
local notation "y[" k "]" => polyhedral_projection_second_fdpg_y A b hC_nonempty d L y0 k
local notation "w[" k "]" => polyhedral_projection_second_fdpg_w A b hC_nonempty d L y0 k
local notation "u[" k "]" => polyhedral_projection_second_fdpg_u A b hC_nonempty d L y0 k

include A b hC_nonempty d L y0

/-- The second-FDPG dual sequence starts from the prescribed initialization `y⁰ = y0`. -/
theorem polyhedral_projection_second_fdpg_y_zero :
    y[0] = y0 := by
  simpa using
    finite_intersection_fdpg_y_zero
      C
      hC_nonempty
      hC_closed
      hC_convex
      L d y0

/-- The second-FDPG extrapolated sequence starts from `w⁰ = y⁰ = y0`. -/
theorem polyhedral_projection_second_fdpg_w_zero :
    w[0] = y0 := by
  simpa using
    finite_intersection_fdpg_w_zero
      C
      hC_nonempty
      hC_closed
      hC_convex
      L d y0

/-- At every iteration `k`, the auxiliary point satisfies the step-(a) formula
`u^k = ∑ i, w_i^k + d`. -/
theorem polyhedral_projection_second_fdpg_u_eq
    (k : ℕ) :
    u[k] = (∑ i : Fin p, w[k] i) + d := by
  simpa using
    finite_intersection_fdpg_u_eq
      C
      hC_nonempty
      hC_closed
      hC_convex
      L d y0 k

/-- Each successor dual block vector is obtained by the shared finite-intersection halfspace
update owner applied to `u^k` and `w^k`. -/
theorem polyhedral_projection_second_fdpg_y_succ
    (k : ℕ) :
    y[k + 1] =
      finite_intersection_projection_dual_update
        C
        hC_nonempty
        hC_closed
        hC_convex
        L
        u[k]
        w[k] := by
  simpa using
    finite_intersection_fdpg_y_succ
      C
      hC_nonempty
      hC_closed
      hC_convex
      L d y0 k

/-- For each row `i`, the successor block `y_i^(k+1)` is given by the textbook halfspace update
formula; the zero-row case collapses to `0` because rowwise nonemptiness forces the corresponding
halfspace to be all of `ℝ^n`. -/
theorem polyhedral_projection_second_fdpg_y_succ_apply
    (k : ℕ) (i : Fin p) :
    y[k + 1] i =
      let ai := a[i];
      -((max
            (inner ℝ ai (u[k] - (L : ℝ) • w[k] i) - b i)
            0) /
          ((L : ℝ) * ‖ai‖ ^ (2 : ℕ))) • ai := by
  let x := u[k] - (L : ℝ) • w[k] i
  have hy :
      y[k + 1] i =
        w[k] i - (1 / L : ℝ) • u[k] +
          (1 / L : ℝ) •
            projectionPoint
              (C i)
              (hC_nonempty i)
              (hC_closed i)
              (hC_convex i)
              x := by
    simpa [x] using
      finite_intersection_fdpg_y_succ_apply
        C
        hC_nonempty
        hC_closed
        hC_convex
        L d y0 k i
  by_cases hai : a[i] = 0
  · have hbi : 0 ≤ b i := by
      rcases hC_nonempty i with ⟨z, hz⟩
      simpa [C, polyhedral_projection_halfspace, hai] using hz
    have hx_mem : x ∈ C i := by
      simp [x, C, polyhedral_projection_halfspace, hai, hbi]
    have hproj :
        projectionPoint
            (C i)
            (hC_nonempty i)
            (hC_closed i)
            (hC_convex i)
            x = x := by
      apply
        (eq_projectionPoint_of_mem_isMinOn
          (C i)
          (hC_nonempty i)
          hC_closed i
          hC_convex i
          x
          hx_mem).symm
      rw [isMinOn_iff]
      intro z hz
      have hz_nonneg : 0 ≤ ‖z - x‖ ^ (2 : ℕ) / 2 := by positivity
      simpa using hz_nonneg
    simpa [x, hai, hproj] using hy
  · have hproj :
        projectionPoint
            (C i)
            (hC_nonempty i)
            (hC_closed i)
            (hC_convex i)
            x =
          x - (((inner ℝ a[i] x - b i)⁺ / ‖a[i]‖ ^ (2 : ℕ)) • a[i]) := by
      simpa [C, x] using
        polyhedral_projection_halfspace_projectionPoint_eq A b i (hC_nonempty i) x hai
    have hL : (L : ℝ) ≠ 0 := by positivity
    have hnorm : ‖a[i]‖ ^ (2 : ℕ) ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.2 hai)
    have hcancel : w[k] i - (1 / L : ℝ) • u[k] + (1 / L : ℝ) • x = 0 := by
      calc
        w[k] i - (1 / L : ℝ) • u[k] + (1 / L : ℝ) • x
            = w[k] i - (1 / L : ℝ) • u[k] +
                ((1 / L : ℝ) • u[k] - (((1 / L : ℝ) * (L : ℝ)) • w[k] i)) := by
                  simp [x, smul_sub, smul_smul]
        _ = w[k] i - (((1 / L : ℝ) * (L : ℝ)) • w[k] i) := by
              abel
        _ = 0 := by
              field_simp [hL]
    have hscalar :
        (1 / (L : ℝ)) * ((inner ℝ a[i] x - b i)⁺ / ‖a[i]‖ ^ (2 : ℕ)) =
          (inner ℝ a[i] x - b i)⁺ / ((L : ℝ) * ‖a[i]‖ ^ (2 : ℕ)) := by
      field_simp [hL, hnorm]
      ring
    rw [hproj] at hy
    calc
      y[k + 1] i
          = w[k] i - (1 / L : ℝ) • u[k] +
              (1 / L : ℝ) •
                (x - (((inner ℝ a[i] x - b i)⁺ / ‖a[i]‖ ^ (2 : ℕ)) • a[i])) := hy
      _ = (w[k] i - (1 / L : ℝ) • u[k] + (1 / L : ℝ) • x) -
            (((1 / L : ℝ) * ((inner ℝ a[i] x - b i)⁺ / ‖a[i]‖ ^ (2 : ℕ))) • a[i]) := by
            simp [smul_sub, smul_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = -((((1 / L : ℝ) * ((inner ℝ a[i] x - b i)⁺ / ‖a[i]‖ ^ (2 : ℕ))) • a[i])) := by
            rw [hcancel, zero_sub]
      _ = -((((inner ℝ a[i] x - b i)⁺ / ((L : ℝ) * ‖a[i]‖ ^ (2 : ℕ))) • a[i])) := by
            rw [hscalar]
      _ = let ai := a[i];
          -((max (inner ℝ ai (u[k] - (L : ℝ) • w[k] i) - b i) 0) /
            ((L : ℝ) * ‖ai‖ ^ (2 : ℕ))) • ai := by
            simp [x]

/-- The first extrapolated iterate satisfies `w¹ = y¹`. -/
theorem polyhedral_projection_second_fdpg_w_one :
    w[1] = y[1] := by
  simpa using
    finite_intersection_fdpg_w_one
      C
      hC_nonempty
      hC_closed
      hC_convex
      L d y0

/-- For every `k`, the later extrapolated iterates satisfy the shifted textbook recursion
`w^(k+2) = y^(k+2) + (t_k / t_(k+2)) (y^(k+2) - y^(k+1))`. -/
theorem polyhedral_projection_second_fdpg_w_succ_succ
    (k : ℕ) :
    w[k + 2] =
      y[k + 2] +
        (fista_momentum_sequence k / fista_momentum_sequence (k + 2)) •
          (y[k + 2] - y[k + 1]) := by
  simpa using
    finite_intersection_fdpg_w_succ_succ
      C
      hC_nonempty
      hC_closed
      hC_convex
      L d y0 k

end

end
