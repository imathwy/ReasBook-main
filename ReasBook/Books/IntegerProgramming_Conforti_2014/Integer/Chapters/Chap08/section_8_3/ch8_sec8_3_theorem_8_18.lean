import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.Convex.Extreme
import Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Semantic recall note: `lean_leansearch` surfaced `instSupSetEReal` and
-- `Real.sSup_of_not_bddAbove`, matching the Chapter 8 precedent that value owners should use
-- `EReal` when unbounded-above behavior matters.
-- Local analogue note: the projection-style API follows Chapter 4 Theorem 4.39, and the
-- optimization-value surface follows the Chapter 8 relaxation-value files.

section Theorem818

variable {m n p : ℕ}
universe u v w

variable {K : Type u} {J : Type v}

/-- The right-hand side `b - A x` that appears after fixing the master variable `x` in the
Benders subproblem. -/
def benders_residual
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ b i - (A *ᵥ x) i

/-- The coordinate formula for the Benders residual `b - A x`. -/
theorem benders_residual_apply
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ)
    (i : Fin m) :
    benders_residual A b x i = b i - (A *ᵥ x) i := rfl

/-- The linear-programming Benders subproblem feasible set
`{y | G y ≤ rhs, y ≥ 0}` for a fixed right-hand side `rhs`. -/
def benders_subproblem_feasible_set
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ) : Set (Fin p → ℝ) :=
  {y | G *ᵥ y ≤ rhs ∧ ∀ i, 0 ≤ y i}

/-- Membership in the Benders subproblem feasible set is exactly the system
`G y ≤ rhs` together with nonnegativity of `y`. -/
theorem mem_benders_subproblem_feasible_set_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ)
    (y : Fin p → ℝ) :
    y ∈ benders_subproblem_feasible_set G rhs ↔
      G *ᵥ y ≤ rhs ∧ ∀ i, 0 ≤ y i := Iff.rfl

/-- The optimal value `z_LP(x)` of the Benders subproblem with right-hand side `rhs`, recorded in
`EReal` so unbounded-above subproblems have value `⊤ = +∞`. -/
noncomputable def benders_subproblem_value
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (rhs : Fin m → ℝ) : EReal :=
  sSup
    ((fun y : Fin p → ℝ ↦ ((h ⬝ᵥ y : ℝ) : EReal)) ''
      benders_subproblem_feasible_set G rhs)

/-- The dual polyhedron `Q = {v ∈ ℝ^m_+ | v G ≥ h}` of the Benders subproblem. -/
def benders_dual_polyhedron
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ) : Set (Fin m → ℝ) :=
  {v | 0 ≤ v ∧ h ≤ v ᵥ* G}

/-- Membership in `benders_dual_polyhedron G h` is exactly the conjunction `v ≥ 0` and
`v ᵥ* G ≥ h`. -/
theorem mem_benders_dual_polyhedron_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (v : Fin m → ℝ) :
    v ∈ benders_dual_polyhedron G h ↔ 0 ≤ v ∧ h ≤ v ᵥ* G :=
  Iff.rfl

/-- The cone `C = {v ∈ ℝ^m_+ | v G ≥ 0}` whose extreme rays define the Benders feasibility cuts. -/
def benders_dual_cone
    (G : Matrix (Fin m) (Fin p) ℝ) : Set (Fin m → ℝ) :=
  {v | 0 ≤ v ∧ 0 ≤ v ᵥ* G}

/-- Membership in `benders_dual_cone G` is exactly the conjunction `v ≥ 0` and `v ᵥ* G ≥ 0`. -/
theorem mem_benders_dual_cone_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (v : Fin m → ℝ) :
    v ∈ benders_dual_cone G ↔ 0 ≤ v ∧ 0 ≤ v ᵥ* G :=
  Iff.rfl

/-- A finite family `points` represents the extreme points of `P` when each listed point is an
extreme point of `P`, different indices represent different points, and every extreme point of
`P` appears in the family. -/
def IsExtremePointRepresentativeFamily
    (P : Set (Fin m → ℝ))
    {q : ℕ}
    (points : Fin q → Fin m → ℝ) : Prop :=
  (∀ k : Fin q, points k ∈ P.extremePoints ℝ) ∧
    Pairwise (fun k l ↦ points k ≠ points l) ∧
      ∀ x : Fin m → ℝ, x ∈ P.extremePoints ℝ → ∃ k : Fin q, x = points k

/-- Unfolding `IsExtremePointRepresentativeFamily P points` gives the source-facing extreme-point,
pairwise-distinct-point, and spanning conditions. -/
theorem isExtremePointRepresentativeFamily_iff
    (P : Set (Fin m → ℝ))
    {q : ℕ}
    (points : Fin q → Fin m → ℝ) :
    IsExtremePointRepresentativeFamily P points ↔
      (∀ k : Fin q, points k ∈ P.extremePoints ℝ) ∧
        Pairwise (fun k l ↦ points k ≠ points l) ∧
          ∀ x : Fin m → ℝ, x ∈ P.extremePoints ℝ → ∃ k : Fin q, x = points k :=
  Iff.rfl

/-- A finite family `rays` represents the extreme rays of `C` when each listed vector generates
an extreme ray of `C`, different indices represent different rays, and every extreme ray of `C`
is same-ray equivalent to one of the listed vectors. -/
def IsExtremeRayRepresentativeFamilyLocal
    (C : Set (Fin m → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ) : Prop :=
  (∀ t : Fin q, IsExtremeRayOfCone C (rays t)) ∧
    Pairwise (fun s t ↦ ¬ SameRay ℝ (rays s) (rays t)) ∧
      ∀ r : Fin m → ℝ, IsExtremeRayOfCone C r → ∃ t : Fin q, SameRay ℝ r (rays t)

/-- Unfolding `IsExtremeRayRepresentativeFamilyLocal C rays` gives the source-facing extreme-ray,
pairwise-distinct-ray, and spanning conditions. -/
theorem isExtremeRayRepresentativeFamilyLocal_iff
    (C : Set (Fin m → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ) :
    IsExtremeRayRepresentativeFamilyLocal C rays ↔
      (∀ t : Fin q, IsExtremeRayOfCone C (rays t)) ∧
        Pairwise (fun s t ↦ ¬ SameRay ℝ (rays s) (rays t)) ∧
          ∀ r : Fin m → ℝ, IsExtremeRayOfCone C r → ∃ t : Fin q, SameRay ℝ r (rays t) :=
  Iff.rfl

/- Core residual-parametrized Benders owners used by the linear theorem and its later variants. -/
namespace Benders

variable {α : Type w}

/-- The `x`-projection of a mixed system whose fixed-`x` right-hand side is `residual x`,
encoded as existence of a feasible subproblem solution. -/
def projectionSet
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ) : Set α :=
  {x | ∃ y, y ∈ benders_subproblem_feasible_set G (residual x)}

/-- Membership in `projectionSet residual G` means that there exists a nonnegative vector `y`
satisfying `G y ≤ residual x`. -/
theorem mem_projectionSet_iff
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (x : α) :
    x ∈ projectionSet residual G ↔
      ∃ y : Fin p → ℝ, y ∈ benders_subproblem_feasible_set G (residual x) :=
  Iff.rfl

/-- The optimality cuts generated by `u` at a fixed master point `x`, expressed through the
residual map. -/
def optimalityCutSet
    (residual : α → Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : α) : Set ℝ :=
  {η | ∀ k, η ≤ u k ⬝ᵥ residual x}

/-- Membership in the residual-based Benders optimality-cut set means satisfying every inequality
`η ≤ u^k residual x`. -/
theorem mem_optimalityCutSet_iff
    (residual : α → Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : α)
    (η : ℝ) :
    η ∈ optimalityCutSet residual u x ↔
      ∀ k, η ≤ u k ⬝ᵥ residual x :=
  Iff.rfl

/-- The supremal `η` allowed by all residual-based Benders optimality cuts at `x`, recorded in
`EReal` so the unconstrained case has value `⊤ = +∞`. -/
noncomputable def optimalityCutValue
    (residual : α → Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : α) : EReal :=
  sSup ((fun η : ℝ ↦ (η : EReal)) '' optimalityCutSet residual u x)

/-- The feasibility cuts generated by `r` on the master variable through the residual map. -/
def feasibilityCutSet
    (residual : α → Fin m → ℝ)
    (r : J → Fin m → ℝ) : Set α :=
  {x | ∀ j, 0 ≤ r j ⬝ᵥ residual x}

/-- Membership in the residual-based Benders feasibility-cut set means satisfying every inequality
`r^j residual x ≥ 0`. -/
theorem mem_feasibilityCutSet_iff
    (residual : α → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (x : α) :
    x ∈ feasibilityCutSet residual r ↔
      ∀ j, 0 ≤ r j ⬝ᵥ residual x :=
  Iff.rfl

/-- The feasible set of a mixed problem with master variable restricted to `X` and subproblem
right-hand side `residual x`. -/
def originalFeasibleSet
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α) : Set (α × (Fin p → ℝ)) :=
  {xy | xy.1 ∈ X ∧ xy.2 ∈ benders_subproblem_feasible_set G (residual xy.1)}

/-- Membership in the residual-based mixed feasible set means `x ∈ X` and `y` solves the
subproblem with right-hand side `residual x`. -/
theorem mem_originalFeasibleSet_iff
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α)
    (xy : α × (Fin p → ℝ)) :
    xy ∈ originalFeasibleSet residual G X ↔
      xy.1 ∈ X ∧ xy.2 ∈ benders_subproblem_feasible_set G (residual xy.1) :=
  Iff.rfl

/-- The source value of the residual-based mixed problem, namely the maximum of `f(x) + h y` over
the feasible pairs `(x, y)`, recorded in `EReal` so infeasible instances have value `⊥` and
unbounded-above instances have value `⊤`. -/
noncomputable def originalValue
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α)
    (f : α → ℝ)
    (h : Fin p → ℝ) : EReal :=
  sSup
    ((fun xy : α × (Fin p → ℝ) ↦ ((f xy.1 + h ⬝ᵥ xy.2 : ℝ) : EReal)) ''
      originalFeasibleSet residual G X)

/-- The feasible set of the residual-based Benders master reformulation, with optimality cuts
indexed by `K` and feasibility cuts indexed by `J`. -/
def masterFeasibleSet
    (residual : α → Fin m → ℝ)
    (X : Set α)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ) : Set (α × ℝ) :=
  {xη |
    xη.1 ∈ X ∧
      xη.2 ∈ optimalityCutSet residual u xη.1 ∧
      xη.1 ∈ feasibilityCutSet residual r}

/-- Membership in the residual-based Benders master feasible set is exactly the conjunction of the
master restriction `x ∈ X`, all optimality cuts, and all feasibility cuts. -/
theorem mem_masterFeasibleSet_iff
    (residual : α → Fin m → ℝ)
    (X : Set α)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (xη : α × ℝ) :
    xη ∈ masterFeasibleSet residual X u r ↔
      xη.1 ∈ X ∧
        (∀ k, xη.2 ≤ u k ⬝ᵥ residual xη.1) ∧
        ∀ j, 0 ≤ r j ⬝ᵥ residual xη.1 := by
  rfl

/-- The optimal value of the residual-based Benders master reformulation, namely the maximum of
`f(x) + η` over the master feasible pairs `(x, η)`, recorded in `EReal` so infeasible instances
have value `⊥` and unbounded-above instances have value `⊤`. -/
noncomputable def masterValue
    (residual : α → Fin m → ℝ)
    (X : Set α)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (f : α → ℝ) : EReal :=
  sSup
    ((fun xη : α × ℝ ↦ ((f xη.1 + xη.2 : ℝ) : EReal)) ''
      masterFeasibleSet residual X u r)

/-- Residual-based Benders reformulation principle: if the feasible master projection is exactly
the feasibility-cut region, the subproblem value is finite on the feasible master points in `X`,
and the subproblem value is exactly the supremum described by the optimality cuts, then the
original mixed problem value equals the Benders master value. -/
theorem originalValue_eq_masterValue
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α)
    (f : α → ℝ)
    (h : Fin p → ℝ)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (hproj : projectionSet residual G = feasibilityCutSet residual r)
    (hfinite :
      ∀ x : α,
        x ∈ X →
          x ∈ projectionSet residual G →
            benders_subproblem_value G h (residual x) < ⊤)
    (hsubproblem :
      ∀ x : α,
        x ∈ projectionSet residual G →
          benders_subproblem_value G h (residual x) =
            optimalityCutValue residual u x) :
    originalValue residual G X f h = masterValue residual X u r f := sorry

end Benders

/-- The `x`-projection of the mixed system `A x + G y ≤ b`, `y ≥ 0`, encoded as existence of a
subproblem solution after fixing `x`. -/
abbrev benders_projection_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  Benders.projectionSet (benders_residual A b) G

/-- Membership in the `x`-projection means that there exists a nonnegative vector `y` satisfying
`G y ≤ b - A x`. -/
theorem mem_benders_projection_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ benders_projection_set A G b ↔
      ∃ y : Fin p → ℝ, y ∈ benders_subproblem_feasible_set G (benders_residual A b x) :=
  Benders.mem_projectionSet_iff (benders_residual A b) G x

/-- The optimality cuts generated by `u` at a fixed master vector `x`. -/
abbrev benders_optimality_cut_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : Fin n → ℝ) : Set ℝ :=
  Benders.optimalityCutSet (benders_residual A b) u x

/-- Membership in the Benders optimality-cut set means satisfying every inequality
`η ≤ u^k (b - A x)`. -/
theorem mem_benders_optimality_cut_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : Fin n → ℝ)
    (η : ℝ) :
    η ∈ benders_optimality_cut_set A b u x ↔
      ∀ k, η ≤ u k ⬝ᵥ benders_residual A b x :=
  Benders.mem_optimalityCutSet_iff (benders_residual A b) u x η

/-- The supremal `η` allowed by all Benders optimality cuts at `x`. -/
noncomputable abbrev benders_optimality_cut_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : Fin n → ℝ) : EReal :=
  Benders.optimalityCutValue (benders_residual A b) u x

/-- The feasibility cuts generated by `r` on the master variable `x`. -/
abbrev benders_feasibility_cut_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r : J → Fin m → ℝ) : Set (Fin n → ℝ) :=
  Benders.feasibilityCutSet (benders_residual A b) r

/-- Membership in the Benders feasibility-cut set means satisfying every inequality
`r^j (b - A x) ≥ 0`. -/
theorem mem_benders_feasibility_cut_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ benders_feasibility_cut_set A b r ↔
      ∀ j, 0 ≤ r j ⬝ᵥ benders_residual A b x :=
  Benders.mem_feasibilityCutSet_iff (benders_residual A b) r x

/-- The feasible set of the original mixed problem (8.26), with master variable restricted to the
set `X`. -/
abbrev benders_original_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ)) : Set ((Fin n → ℝ) × (Fin p → ℝ)) :=
  Benders.originalFeasibleSet (benders_residual A b) G X

/-- Membership in the original mixed feasible set means `x ∈ X` and `y` solves the Benders
subproblem with right-hand side `b - A x`. -/
theorem mem_benders_original_feasible_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (xy : (Fin n → ℝ) × (Fin p → ℝ)) :
    xy ∈ benders_original_feasible_set A G b X ↔
      xy.1 ∈ X ∧
        xy.2 ∈ benders_subproblem_feasible_set G (benders_residual A b xy.1) :=
  Benders.mem_originalFeasibleSet_iff (benders_residual A b) G X xy

/-- The source value `z_I` of the original mixed problem (8.26), namely the maximum of
`c x + h y` over the feasible pairs `(x, y)`. -/
noncomputable abbrev benders_original_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : Fin p → ℝ) : EReal :=
  Benders.originalValue (benders_residual A b) G X (fun x ↦ c ⬝ᵥ x) h

/-- The feasible set of the Benders master reformulation (8.27), with optimality cuts indexed by
`K` and feasibility cuts indexed by `J`. -/
abbrev benders_master_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  Benders.masterFeasibleSet (benders_residual A b) X u r

/-- Membership in the Benders master feasible set is exactly the conjunction of the master
restriction `x ∈ X`, all optimality cuts, and all feasibility cuts. -/
theorem mem_benders_master_feasible_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (xη : (Fin n → ℝ) × ℝ) :
    xη ∈ benders_master_feasible_set A b X u r ↔
      xη.1 ∈ X ∧
        (∀ k, xη.2 ≤ u k ⬝ᵥ benders_residual A b xη.1) ∧
        ∀ j, 0 ≤ r j ⬝ᵥ benders_residual A b xη.1 :=
  Benders.mem_masterFeasibleSet_iff (benders_residual A b) X u r xη

/-- The optimal value of the Benders master reformulation (8.27), namely the maximum of
`η + c x` over the master feasible pairs `(x, η)`. -/
noncomputable abbrev benders_master_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (c : Fin n → ℝ) : EReal :=
  Benders.masterValue (benders_residual A b) X u r (fun x ↦ c ⬝ᵥ x)

/-- Theorem 8.18 (Benders). If the family `u` is a representative family of the extreme points
of the dual polyhedron `Q = {v ∈ ℝ^m_+ | v G ≥ h}` and the family `r` is a representative
family of the extreme rays of the cone `C = {v ∈ ℝ^m_+ | v G ≥ 0}`, then the mixed
problem (8.26) has the same value as the Benders master reformulation (8.27) with
optimality cuts
`η ≤ u^k (b - A x)` and feasibility cuts `r^j (b - A x) ≥ 0`. -/
theorem benders_original_value_eq_master_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : Fin p → ℝ)
    {qK qJ : ℕ}
    (u : Fin qK → Fin m → ℝ)
    (r : Fin qJ → Fin m → ℝ)
    (hpoints :
      IsExtremePointRepresentativeFamily (benders_dual_polyhedron G h) u)
    (hrays : IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone G) r) :
    benders_original_value A G b X c h = benders_master_value A b X u r c := sorry

end Theorem818
