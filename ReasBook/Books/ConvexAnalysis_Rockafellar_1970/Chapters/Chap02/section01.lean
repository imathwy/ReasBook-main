import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_2_1_1 (from Chap01) -/
open scoped Rockafellar

universe u v

section Pairing

variable {R : Type v}
variable {X : Type*} {Y : Type*}
variable [HasPairing X Y R] {I : Sort u}

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.1.1 says that the solution set of an arbitrary family of linear
  inequalities `⟪x, b i⟫ₚ ≤ β i` is convex.
- `core/canonical`: the owner abstraction is `Convex 𝕜 s`; the relevant canonical closure result is
  `convex_iInter`.
- `bridge/view`: the textbook set `{x | ∀ i, ⟪x, b_i⟫ₚ ≤ β_i}` is the intersection of the chapter's
  owner half-spaces `closedHalfSpaceLE (b i) (β i)`.
- Primitive data vs derived API: the family `b`, the thresholds `β`, and the corresponding closed
  half-spaces are primitive data; convexity of their common intersection is derived API and should
  remain a theorem.
- Domain-style sampling: this item reuses the chapter owner half-space constructor
  `closedHalfSpaceLE`, the owner-side membership lemma `mem_closedHalfSpaceLE_iff`, the
  owner-side convexity theorem `closedHalfSpaceLE_convex`, and the intersection closure theorem
  `convex_iInter`.
-- Layer target for `setOf_forall_pairing_le_eq_iInter_closedHalfSpaceLE`: `bridge/view`.
-- This bridge only identifies the textbook inequality presentation with the owner
-- half-space intersection, so it belongs to the primitive pairing-inequality layer
-- `[LE R] [HasPairing X Y R]`.
-/

namespace LinearConstraintRelation

/-- The indexed owner subset cut out by weak linear inequalities `⟪x, b i⟫ₚ ≤ β i`. -/
def leFeasible [LE R] (b : I → Y) (β : I → R) : Set X :=
  {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i}

/-- The owner weak feasible set is the indexed intersection of weak pairing half-spaces. -/
theorem leFeasible_eq_iInter_closedHalfSpaceLE
    [LE R]
    (b : I → Y) (β : I → R) :
    leFeasible b β = ⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X) :=
by
  ext x
  simp [leFeasible, closedHalfSpaceLE]

/-- Membership in `leFeasible b β` is exactly the pointwise weak inequality family
`⟪x, b i⟫ₚ ≤ β i`. -/
@[simp] theorem mem_leFeasible
    [LE R]
    (b : I → Y) (β : I → R) (x : X) :
    x ∈ leFeasible b β ↔ ∀ i, ⟪x, b i⟫ₚ ≤ β i :=
  Iff.rfl

/-- The weak owner feasible set is exactly the textbook pointwise weak inequality set. -/
theorem leFeasible_eq_setOf
    [LE R]
    (b : I → Y) (β : I → R) :
    leFeasible b β = {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} :=
  rfl

end LinearConstraintRelation

/-- The textbook weak-inequality feasible set is exactly the weak owner feasible set. -/
theorem setOf_forall_pairing_le_eq_leFeasible
    [LE R]
    (b : I → Y) (β : I → R) :
    {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} = (LinearConstraintRelation.leFeasible b β : Set X) := by
  simpa using (LinearConstraintRelation.leFeasible_eq_setOf (b := b) (β := β)).symm

/-- The textbook weak-inequality feasible set is exactly the intersection of the owner closed
half-spaces attached to the indexed inequalities. -/
theorem setOf_forall_pairing_le_eq_iInter_closedHalfSpaceLE [LE R]
    (b : I → Y) (β : I → R) :
    {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} = ⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X) := by
  simpa [LinearConstraintRelation.leFeasible_eq_iInter_closedHalfSpaceLE] using
    (setOf_forall_pairing_le_eq_leFeasible (b := b) (β := β))

end Pairing

section FunctionalPrimitive

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
variable [Module 𝕜 R] [PosSMulMono 𝕜 R]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X] {I : Sort u}

namespace LinearMap

/-- Canonical linear-map owner form: an indexed family of linear maps `g i`
cuts out a convex weak feasible set. -/
theorem convex_setOf_forall_le
    (g : I → X →ₗ[𝕜] R) (β : I → R) :
    Convex 𝕜 {x : X | ∀ i, g i x ≤ β i} := by
  simpa [Set.iInter_setOf] using
    (convex_iInter fun i ↦ convex_halfSpace_le (g i).isLinear (β i))

end LinearMap

/-- Intrinsic linear-inequality closure: any indexed family of linear maps
`x ↦ g i x` defines a convex weak feasible set. -/
theorem convex_setOf_forall_le_of_forall_isLinear
    (g : I → X → R) (β : I → R)
    (hlin : ∀ i, IsLinearMap 𝕜 (g i)) :
    Convex 𝕜 {x : X | ∀ i, g i x ≤ β i} := by
  let gLinear : I → X →ₗ[𝕜] R := fun i ↦ IsLinearMap.mk' (g i) (hlin i)
  simpa [gLinear] using
    (LinearMap.convex_setOf_forall_le (𝕜 := 𝕜) (R := R) (X := X) (g := gLinear) (β := β))

end FunctionalPrimitive

section LinearPrimitive

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
variable [Module 𝕜 R] [PosSMulMono 𝕜 R]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*}
variable [HasPairing X Y R] {I : Sort u}

-- Proof sketch: apply `convex_iInter` to the owner family
-- `i ↦ closedHalfSpaceLE (b i) (β i)`, using
-- `closedHalfSpaceLE_convex_of_isLinear` pointwise from the primitive linearity assumptions.
-- Then obtain the textbook set-builder statement by rewriting with
-- `LinearConstraintRelation.leFeasible_eq_setOf`.
namespace LinearConstraintRelation

/-- Canonical bundled-linear-map form: the weak owner feasible set is convex when each indexed
constraint map is presented as a linear map equal to the corresponding pairing evaluation. -/
theorem convex_leFeasible_of_forall_linearMap
    (b : I → Y) (β : I → R)
    (g : I → X →ₗ[𝕜] R)
    (hpair : ∀ i x, g i x = (⟪x, b i⟫ₚ : R)) :
    Convex 𝕜 (leFeasible b β : Set X) := by
  have hset : leFeasible b β = {x : X | ∀ i, g i x ≤ β i} := by
    ext x
    constructor
    · intro hx i
      simpa [hpair i x] using hx i
    · intro hx i
      simpa [hpair i x] using hx i
  rw [hset]
  exact LinearMap.convex_setOf_forall_le (𝕜 := 𝕜) (R := R) (X := X) (g := g) (β := β)

/-- The indexed weak owner feasible set is convex when each pairing evaluation
`x ↦ ⟪x, b i⟫ₚ` is linear. This is the primitive linear-data layer of Corollary 2.1.1. -/
theorem convex_leFeasible_of_forall_isLinear
    (b : I → Y) (β : I → R)
    (hlin : ∀ i, IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b i⟫ₚ : R))) :
    Convex 𝕜 (leFeasible b β : Set X) := by
  let gLinear : I → X →ₗ[𝕜] R := fun i ↦ IsLinearMap.mk' (fun x : X ↦ (⟪x, b i⟫ₚ : R)) (hlin i)
  exact convex_leFeasible_of_forall_linearMap (b := b) (β := β) (g := gLinear)
    (hpair := by
      intro i x
      rfl)

end LinearConstraintRelation

/-- Primitive intersection view of Corollary 2.1.1 under per-constraint linearity assumptions. -/
theorem convex_iInter_closedHalfSpaceLE_family_of_forall_isLinear
    (b : I → Y) (β : I → R)
    (hlin : ∀ i, IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b i⟫ₚ : R))) :
    Convex 𝕜 (⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X)) := by
  simpa [LinearConstraintRelation.leFeasible_eq_iInter_closedHalfSpaceLE] using
    (LinearConstraintRelation.convex_leFeasible_of_forall_isLinear
      (b := b) (β := β) hlin)

/-- Primitive textbook set-builder view of Corollary 2.1.1 under per-constraint linearity
assumptions. -/
theorem convex_setOf_forall_pairing_le_of_forall_isLinear
    (b : I → Y) (β : I → R)
    (hlin : ∀ i, IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b i⟫ₚ : R))) :
    Convex 𝕜 {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} := by
  simpa [LinearConstraintRelation.leFeasible_eq_setOf] using
    (LinearConstraintRelation.convex_leFeasible_of_forall_isLinear
      (b := b) (β := β) hlin)

end LinearPrimitive

section Linear

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [PosSMulMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort u}

namespace LinearConstraintRelation

/-- Bridge form: the indexed weak owner feasible set is convex under a linear pairing. -/
theorem convex_leFeasible (b : I → Y) (β : I → 𝕜) :
    Convex 𝕜 (leFeasible b β : Set X) := by
  exact LinearConstraintRelation.convex_leFeasible_of_forall_linearMap
    (𝕜 := 𝕜) (X := X) (Y := Y) (R := 𝕜) (b := b) (β := β)
    (g := fun i ↦ HasLinearPairing.pairingLinear.flip (b i))
    (hpair := by
      intro i x
      simp [HasLinearPairing.pairing_eq_pairingLinear])

end LinearConstraintRelation

/-- Bridge form: the owner intersection of indexed weak pairing half-spaces is convex under a
linear pairing. -/
theorem convex_iInter_closedHalfSpaceLE_family
    (b : I → Y) (β : I → 𝕜) :
    Convex 𝕜 (⋂ i, (closedHalfSpaceLE (b i) (β i) : Set X)) := by
  simpa [LinearConstraintRelation.leFeasible_eq_iInter_closedHalfSpaceLE] using
    (LinearConstraintRelation.convex_leFeasible (X := X) (b := b) (β := β))

/-- Bridge form: Corollary 2.1.1 under a linear pairing owner. -/
theorem convex_setOf_forall_pairing_le
    (b : I → Y) (β : I → 𝕜) :
    Convex 𝕜 {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} := by
  simpa [LinearConstraintRelation.leFeasible_eq_setOf] using
    (LinearConstraintRelation.convex_leFeasible (X := X) (b := b) (β := β))

/-- Corollary 2.1.1, stated coordinate-free: the common solution set of any family of linear weak
inequalities is convex. -/
theorem convex_linear_inequality_solution_set
    (b : I → Y) (β : I → 𝕜) :
    Convex 𝕜 {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ β i} :=
  convex_setOf_forall_pairing_le (X := X) (Y := Y) (b := b) (β := β)

end Linear

/-! ### Theorem_2_1 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Theorem 2.1 states that the intersection of any family of convex sets is again
  convex.
- `core/canonical`: the owner abstraction is `Convex 𝕜 s` for a set `s` at the minimal canonical
  layer `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]`; the intrinsic family-level
  closure theorem is `convex_iInter`.
- `bridge/view`: the textbook's “arbitrary collection” presentation is the concrete model
  `Set (Set E)`, which is available as the bridge theorem `convex_sInter`.
- Primitive data vs derived API: the convexity predicate is the owner notion; the intersection
  closure statement should be reused directly rather than repackaged as a second theorem.
- Domain-style sampling: the relevant owner-side declarations here are mathlib's
  `convex_iInter`, `convex_iInter₂`, and `convex_sInter`; this item recalls the canonical
  intrinsic owner theorem directly and leaves the collection-level encoding as a bridge view.
- Layer target: `core/canonical`; expose only the indexed-family owner theorem on the item
  surface.

Abstraction audit (canonicalize):
- Codomain/ambient layer over-concrete? `No`: `Convex 𝕜` is reused at the minimal ordered-semiring
  scalar layer from mathlib.
- Scalar/ambient structure stronger than needed? `No`: there is no `ℝ`-specific or
  finite-coordinate specialization in this item surface.
- Owner tied to a concrete model? `No` for the exposed theorem surface: `convex_iInter` keeps the
  owner intrinsic, while `convex_sInter` remains an available bridge encoding.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: this item is purely order/algebraic.
- Owner name/notation too heavy or too concrete? `No` on the exposed surface: canonical owner and
  standard intersection notation `⋂` are used directly.
- Upstream over-specialization to repair first? `No`: the upstream owners already sit at the
  intended abstraction layer.
-/

/- Theorem 2.1, intrinsic indexed-family form: arbitrary intersections preserve convexity at the
canonical ambient scalar layer. -/
recall convex_iInter

/-! ### Corollary_2_1_2 (from Chap01) -/
open scoped Rockafellar

universe u v

/-
Source/core/bridge triage:
- `source-facing`: Corollary 2.1.2 states that the common solution set of a mixed system of linear
  weak inequalities, strict inequalities, and equations is convex.
- `core/canonical`: the owner abstraction for the conclusion is `Convex 𝕜 s`, with intersection
  closure supplied by `convex_iInter`, and the single-constraint owner subsets are the chapter
  half-space declarations.
- `bridge/view`: the chapter owners `closedHalfSpaceLE`, `closedHalfSpaceGE`, `openHalfSpaceLT`,
  and `openHalfSpaceGT` realize the four inequality relation kinds directly. The equality relation
  is kept at the same owner layer as the level set `{x | ⟪x, b⟫ₚ = β}`, whose convexity is derived
  as the intersection of the two oriented closed half-spaces.
- Primitive data vs derived API: the relation kind, the normals `b i`, and the thresholds `β i`
  are primitive data; the single-constraint owner subsets and the convexity of their common
  solution set are derived API.
- Domain-style sampling: this item reuses the chapter owners `closedHalfSpaceLE`,
  `closedHalfSpaceGE`, `openHalfSpaceLT`, and `openHalfSpaceGT`, together with the chapter owner
  theorems `closedHalfSpaceLE_convex`, `closedHalfSpaceGE_convex`, `openHalfSpaceLT_convex`, and
  `openHalfSpaceGT_convex`, plus intersection closure for convex sets.
- Layer target: `source-facing`, with the solution-set owner layer kept on the same minimal
  order/pairing assumptions as the chapter half-space constructors, and convexity added only in
  the later ordered-semiring layer exported by `Corollary_2_1_1` (via `Corollary_2_0_4`).
-/

/-- The five linear comparison relations appearing in a textbook system of linear inequalities and
equations. -/
inductive LinearConstraintRelation
  | le
  | ge
  | lt
  | gt
  | eq

section Relation

variable {𝕜 : Type v} [LE 𝕜] [LT 𝕜]

/-- Interprets one textbook linear comparison relation between a value and a threshold. -/
def LinearConstraintRelation.holds
    (relation : LinearConstraintRelation) (value β : 𝕜) : Prop :=
  match relation with
  | .le => value ≤ β
  | .ge => β ≤ value
  | .lt => value < β
  | .gt => β < value
  | .eq => value = β

namespace LinearConstraintRelation

@[simp] theorem le_holds_iff {value β : 𝕜} :
    LinearConstraintRelation.le.holds value β ↔ value ≤ β :=
  Iff.rfl

@[simp] theorem ge_holds_iff {value β : 𝕜} :
    LinearConstraintRelation.ge.holds value β ↔ β ≤ value :=
  Iff.rfl

@[simp] theorem lt_holds_iff {value β : 𝕜} :
    LinearConstraintRelation.lt.holds value β ↔ value < β :=
  Iff.rfl

@[simp] theorem gt_holds_iff {value β : 𝕜} :
    LinearConstraintRelation.gt.holds value β ↔ β < value :=
  Iff.rfl

@[simp] theorem eq_holds_iff {value β : 𝕜} :
    LinearConstraintRelation.eq.holds value β ↔ value = β :=
  Iff.rfl

end LinearConstraintRelation

end Relation

namespace LinearConstraintRelation

/-- The mixed equality/weak-inequality relation map with equality on `eqIndices` and weak
inequality off `eqIndices`. -/
noncomputable def eqOn {I : Type u} (eqIndices : Set I) : I → LinearConstraintRelation := by
  classical
  exact fun i ↦ if i ∈ eqIndices then .eq else .le

/-- The mixed strict/weak-inequality relation map with strict inequality on `ltIndices` and weak
inequality off `ltIndices`. -/
noncomputable def ltOn {I : Type u} (ltIndices : Set I) : I → LinearConstraintRelation := by
  classical
  exact fun i ↦ if i ∈ ltIndices then .lt else .le

end LinearConstraintRelation

section

variable {𝕜 : Type v} [LE 𝕜] [LT 𝕜]
variable {X : Type*} {Y : Type*} [HasPairing X Y 𝕜] {I : Sort u}

namespace LinearConstraintRelation

/-- The owner subset cut out by one linear constraint of the given relation kind. -/
def solutionSet
    (relation : LinearConstraintRelation) (b : Y) (β : 𝕜) : Set X :=
  {x | relation.holds ⟪x, b⟫ₚ β}

/-- Membership in the owner set attached to one relation kind is exactly the corresponding
comparison relation. -/
@[simp] theorem mem_solutionSet_iff
    (relation : LinearConstraintRelation) (b : Y) (β : 𝕜) (x : X) :
    x ∈ relation.solutionSet b β ↔ relation.holds ⟪x, b⟫ₚ β :=
  Iff.rfl

end LinearConstraintRelation

namespace LinearConstraintRelation

/-- The solution set of a family of textbook linear constraints. Specializing to
the canonical weak-relation owner from Corollary 2.1.1 recovers the corresponding weak system. -/
def feasibleSet (relation : I → LinearConstraintRelation) (b : I → Y) (β : I → 𝕜) : Set X :=
  ⋂ i, (relation i).solutionSet (b i) (β i)

end LinearConstraintRelation

end

section

variable {𝕜 : Type v} [LE 𝕜] [LT 𝕜]
variable {X : Type*} {Y : Type*} [HasPairing X Y 𝕜] {I : Sort u}

namespace LinearConstraintRelation

/-- The all-`ge` owner feasible set specialized from `feasibleSet`. -/
def geFeasible (b : I → Y) (β : I → 𝕜) : Set X :=
  feasibleSet (fun _ : I ↦ .ge) b β

@[simp] theorem geFeasible_eq_feasibleSet_ge
    (b : I → Y) (β : I → 𝕜) :
    geFeasible b β = (feasibleSet (fun _ : I ↦ .ge) b β : Set X) :=
  rfl

/-- The all-`gt` owner feasible set specialized from `feasibleSet`. -/
def gtFeasible (b : I → Y) (β : I → 𝕜) : Set X :=
  feasibleSet (fun _ : I ↦ .gt) b β

@[simp] theorem gtFeasible_eq_feasibleSet_gt
    (b : I → Y) (β : I → 𝕜) :
    gtFeasible b β = (feasibleSet (fun _ : I ↦ .gt) b β : Set X) :=
  rfl

/-- The all-`lt` owner feasible set specialized from `feasibleSet`. -/
def ltFeasible (b : I → Y) (β : I → 𝕜) : Set X :=
  {x : X | ∀ i, ⟪x, b i⟫ₚ < β i}

@[simp] theorem ltFeasible_eq_feasibleSet_lt
    (b : I → Y) (β : I → 𝕜) :
    ltFeasible b β = (feasibleSet (fun _ : I ↦ .lt) b β : Set X) := by
  ext x
  simp [ltFeasible, feasibleSet, solutionSet, holds]

variable (𝕜)

/-- The homogeneous (`β = 0`) feasible set of a family of textbook linear constraints. -/
def homogeneousFeasibleSet [Zero 𝕜]
    (relation : I → LinearConstraintRelation) (b : I → Y) : Set X :=
  feasibleSet relation b (fun _ ↦ (0 : 𝕜))

/-- The homogeneous all-`le` owner feasible set specialized from
`homogeneousFeasibleSet`. -/
def homogeneousLeFeasibleSet [Zero 𝕜] (b : I → Y) : Set X :=
  homogeneousFeasibleSet 𝕜 (fun _ : I ↦ .le) b

/-- The homogeneous all-`ge` owner feasible set specialized from
`homogeneousFeasibleSet`. -/
def homogeneousGeFeasibleSet [Zero 𝕜] (b : I → Y) : Set X :=
  homogeneousFeasibleSet 𝕜 (fun _ : I ↦ .ge) b

/-- The homogeneous all-`lt` owner feasible set specialized from
`homogeneousFeasibleSet`. -/
def homogeneousLtFeasibleSet [Zero 𝕜] (b : I → Y) : Set X :=
  homogeneousFeasibleSet 𝕜 (fun _ : I ↦ .lt) b

/-- The homogeneous all-`gt` owner feasible set specialized from
`homogeneousFeasibleSet`. -/
def homogeneousGtFeasibleSet [Zero 𝕜] (b : I → Y) : Set X :=
  homogeneousFeasibleSet 𝕜 (fun _ : I ↦ .gt) b

/-- The homogeneous all-`eq` owner feasible set specialized from
`homogeneousFeasibleSet`. -/
def homogeneousEqFeasibleSet [Zero 𝕜] (b : I → Y) : Set X :=
  homogeneousFeasibleSet 𝕜 (fun _ : I ↦ .eq) b

variable {𝕜}

/-- Membership in the mixed feasible set means satisfying each indexed textbook relation. -/
@[simp] theorem mem_feasibleSet
    (relation : I → LinearConstraintRelation) (b : I → Y) (β : I → 𝕜) (x : X) :
    x ∈ feasibleSet relation b β ↔ ∀ i, (relation i).holds ⟪x, b i⟫ₚ (β i) := by
  simp [feasibleSet]

/-- Membership in `geFeasible b β` is exactly the indexed family
`β i ≤ ⟪x, b i⟫ₚ`. -/
@[simp] theorem mem_geFeasible
    (b : I → Y) (β : I → 𝕜) (x : X) :
    x ∈ geFeasible b β ↔ ∀ i, β i ≤ ⟪x, b i⟫ₚ := by
  simp [geFeasible]

/-- Membership in `gtFeasible b β` is exactly the indexed family
`β i < ⟪x, b i⟫ₚ`. -/
@[simp] theorem mem_gtFeasible
    (b : I → Y) (β : I → 𝕜) (x : X) :
    x ∈ gtFeasible b β ↔ ∀ i, β i < ⟪x, b i⟫ₚ := by
  simp [gtFeasible]

/-- Membership in the homogeneous feasible set means satisfying each indexed textbook relation at
level `0`. -/
@[simp] theorem mem_homogeneousFeasibleSet [Zero 𝕜]
    (relation : I → LinearConstraintRelation) (b : I → Y) (x : X) :
    x ∈ homogeneousFeasibleSet 𝕜 relation b ↔
      ∀ i, (relation i).holds ⟪x, b i⟫ₚ (0 : 𝕜) := by
  simp [homogeneousFeasibleSet]

/-- Membership in `homogeneousLeFeasibleSet b` is exactly the indexed family
`⟪x, b i⟫ₚ ≤ 0`. -/
@[simp] theorem mem_homogeneousLeFeasibleSet [Zero 𝕜]
    (b : I → Y) (x : X) :
    x ∈ homogeneousLeFeasibleSet 𝕜 b ↔
      ∀ i, ⟪x, b i⟫ₚ ≤ (0 : 𝕜) := by
  simp [homogeneousLeFeasibleSet]

/-- Membership in `homogeneousGeFeasibleSet b` is exactly the indexed family
`0 ≤ ⟪x, b i⟫ₚ`. -/
@[simp] theorem mem_homogeneousGeFeasibleSet [Zero 𝕜]
    (b : I → Y) (x : X) :
    x ∈ homogeneousGeFeasibleSet 𝕜 b ↔
      ∀ i, (0 : 𝕜) ≤ ⟪x, b i⟫ₚ := by
  simp [homogeneousGeFeasibleSet]

/-- Membership in `homogeneousLtFeasibleSet b` is exactly the indexed family
`⟪x, b i⟫ₚ < 0`. -/
@[simp] theorem mem_homogeneousLtFeasibleSet [Zero 𝕜]
    (b : I → Y) (x : X) :
    x ∈ homogeneousLtFeasibleSet 𝕜 b ↔
      ∀ i, ⟪x, b i⟫ₚ < (0 : 𝕜) := by
  simp [homogeneousLtFeasibleSet]

/-- Membership in `homogeneousGtFeasibleSet b` is exactly the indexed family
`0 < ⟪x, b i⟫ₚ`. -/
@[simp] theorem mem_homogeneousGtFeasibleSet [Zero 𝕜]
    (b : I → Y) (x : X) :
    x ∈ homogeneousGtFeasibleSet 𝕜 b ↔
      ∀ i, (0 : 𝕜) < ⟪x, b i⟫ₚ := by
  simp [homogeneousGtFeasibleSet]

/-- Membership in `homogeneousEqFeasibleSet b` is exactly the indexed family
`⟪x, b i⟫ₚ = 0`. -/
@[simp] theorem mem_homogeneousEqFeasibleSet [Zero 𝕜]
    (b : I → Y) (x : X) :
    x ∈ homogeneousEqFeasibleSet 𝕜 b ↔
      ∀ i, ⟪x, b i⟫ₚ = (0 : 𝕜) := by
  simp [homogeneousEqFeasibleSet]

/-- The owner mixed feasible set is exactly the textbook set of points satisfying each indexed
linear relation. -/
theorem feasibleSet_eq_setOf
    (relation : I → LinearConstraintRelation) (b : I → Y) (β : I → 𝕜) :
    feasibleSet relation b β = {x : X | ∀ i, (relation i).holds ⟪x, b i⟫ₚ (β i)} := by
  ext x
  simp

/-- The all-`ge` owner feasible set is exactly the textbook set
`{x | ∀ i, β i ≤ ⟪x, b i⟫ₚ}`. -/
theorem geFeasible_eq_setOf
    (b : I → Y) (β : I → 𝕜) :
    geFeasible b β = {x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ} := by
  ext x
  simp

/-- The all-`gt` owner feasible set is exactly the textbook set
`{x | ∀ i, β i < ⟪x, b i⟫ₚ}`. -/
theorem gtFeasible_eq_setOf
    (b : I → Y) (β : I → 𝕜) :
    gtFeasible b β = {x : X | ∀ i, β i < ⟪x, b i⟫ₚ} := by
  ext x
  simp

/-- The homogeneous all-`ge` owner feasible set is exactly the textbook set
`{x | ∀ i, 0 ≤ ⟪x, b i⟫ₚ}`. -/
theorem homogeneousGeFeasibleSet_eq_setOf [Zero 𝕜]
    (b : I → Y) :
    homogeneousGeFeasibleSet 𝕜 b =
      {x : X | ∀ i, (0 : 𝕜) ≤ ⟪x, b i⟫ₚ} := by
  ext x
  simp

/-- The homogeneous all-`le` owner feasible set is exactly the textbook set
`{x | ∀ i, ⟪x, b i⟫ₚ ≤ 0}`. -/
theorem homogeneousLeFeasibleSet_eq_setOf [Zero 𝕜]
    (b : I → Y) :
    homogeneousLeFeasibleSet 𝕜 b =
      {x : X | ∀ i, ⟪x, b i⟫ₚ ≤ (0 : 𝕜)} := by
  ext x
  simp

/-- The homogeneous all-`lt` owner feasible set is exactly the textbook set
`{x | ∀ i, ⟪x, b i⟫ₚ < 0}`. -/
theorem homogeneousLtFeasibleSet_eq_setOf [Zero 𝕜]
    (b : I → Y) :
    homogeneousLtFeasibleSet 𝕜 b =
      {x : X | ∀ i, ⟪x, b i⟫ₚ < (0 : 𝕜)} := by
  ext x
  simp

/-- The homogeneous all-`gt` owner feasible set is exactly the textbook set
`{x | ∀ i, 0 < ⟪x, b i⟫ₚ}`. -/
theorem homogeneousGtFeasibleSet_eq_setOf [Zero 𝕜]
    (b : I → Y) :
    homogeneousGtFeasibleSet 𝕜 b =
      {x : X | ∀ i, (0 : 𝕜) < ⟪x, b i⟫ₚ} := by
  ext x
  simp

/-- The homogeneous all-`eq` owner feasible set is exactly the textbook set
`{x | ∀ i, ⟪x, b i⟫ₚ = 0}`. -/
theorem homogeneousEqFeasibleSet_eq_setOf [Zero 𝕜]
    (b : I → Y) :
    homogeneousEqFeasibleSet 𝕜 b =
      {x : X | ∀ i, ⟪x, b i⟫ₚ = (0 : 𝕜)} := by
  ext x
  simp

end LinearConstraintRelation

end

section

variable {𝕜 : Type v} [LT 𝕜]
variable {X : Type*} {Y : Type*} [HasPairing X Y 𝕜] {I : Sort u}

namespace LinearConstraintRelation

/-- Membership in `ltFeasible b β` is exactly the indexed family
`⟪x, b i⟫ₚ < β i`. -/
@[simp] theorem mem_ltFeasible
    (b : I → Y) (β : I → 𝕜) (x : X) :
    x ∈ ltFeasible b β ↔ ∀ i, ⟪x, b i⟫ₚ < β i := by
  rfl

/-- The all-`lt` owner feasible set is exactly the textbook set
`{x | ∀ i, ⟪x, b i⟫ₚ < β i}`. -/
theorem ltFeasible_eq_setOf
    (b : I → Y) (β : I → 𝕜) :
    ltFeasible b β = {x : X | ∀ i, ⟪x, b i⟫ₚ < β i} := by
  rfl

end LinearConstraintRelation

end

section

variable {𝕜 : Type v} [Preorder 𝕜]
variable {X : Type*} {Y : Type*} [HasPairing X Y 𝕜] {I : Sort u}

namespace LinearConstraintRelation

/-- The weak owner `leFeasible` agrees with the mixed owner `feasibleSet` specialized to the
relation `.le`. -/
@[simp] theorem leFeasible_eq_feasibleSet_le
    (b : I → Y) (β : I → 𝕜) :
    leFeasible b β = (feasibleSet (fun _ ↦ .le) b β : Set X) := by
  ext x
  simp [leFeasible, feasibleSet, solutionSet, holds]

/-- The homogeneous all-`le` owner agrees with the weak owner at level `0`. -/
@[simp] theorem homogeneousLeFeasibleSet_eq_leFeasible_zero [Zero 𝕜]
    (b : I → Y) :
    homogeneousLeFeasibleSet 𝕜 b =
      (leFeasible b (fun _ : I ↦ (0 : 𝕜)) : Set X) := by
  rw [homogeneousLeFeasibleSet, homogeneousFeasibleSet]
  exact
    (leFeasible_eq_feasibleSet_le (b := b) (β := fun _ : I ↦ (0 : 𝕜))).symm

/-- The homogeneous all-`le` owner feasible set is exactly the indexed intersection of level-`0`
closed `≤` half-spaces. -/
theorem homogeneousLeFeasibleSet_eq_iInter_closedHalfSpaceLE_zero [Zero 𝕜]
    (b : I → Y) :
    (homogeneousLeFeasibleSet 𝕜 b : Set X) =
      (⋂ i, (closedHalfSpaceLE (b i) (0 : 𝕜) : Set X)) := by
  simpa [homogeneousLeFeasibleSet_eq_leFeasible_zero] using
    (leFeasible_eq_iInter_closedHalfSpaceLE (X := X) (b := b) (β := fun _ : I ↦ (0 : 𝕜)))

end LinearConstraintRelation

end

section

variable {𝕜 : Type v} [PartialOrder 𝕜]
variable {X : Type*} {Y : Type*} [HasPairing X Y 𝕜]

namespace LinearConstraintRelation

/-- The equality solution set is the intersection of the two closed half-spaces cut out by the
same pairing functional and level. -/
theorem eq_solutionSet_eq_inter_closedHalfSpaces (b : Y) (β : 𝕜) :
    (LinearConstraintRelation.eq.solutionSet b β : Set X) =
      (closedHalfSpaceLE b β : Set X) ∩ closedHalfSpaceGE b β := by
  ext x
  constructor
  · intro hx
    constructor
    · simpa [solutionSet, holds, closedHalfSpaceLE] using hx.le
    · simpa [solutionSet, holds, closedHalfSpaceGE] using hx.ge
  · rintro ⟨hxle, hxge⟩
    change ⟪x, b⟫ₚ = β
    exact le_antisymm
      (by simpa [closedHalfSpaceLE] using hxle)
      (by simpa [closedHalfSpaceGE] using hxge)

end LinearConstraintRelation

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedCancelAddMonoid 𝕜]
variable [PosSMulStrictMono 𝕜 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [HasPairing X Y 𝕜]

-- Proof sketch: split on the relation kind and reuse the existing owner subsets for the four
-- inequality forms. The equality case is the intersection of the two corresponding closed
-- half-spaces.
namespace LinearConstraintRelation

theorem convex_solutionSet_of_isLinear
    (relation : LinearConstraintRelation) (b : Y) (β : 𝕜)
    (hb : IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b⟫ₚ : 𝕜))) :
    Convex 𝕜 (relation.solutionSet b β : Set X) := by
  cases relation
  · have h : Convex 𝕜 (closedHalfSpaceLE b β : Set X) :=
      closedHalfSpaceLE_convex_of_isLinear b β hb
    simpa [solutionSet, holds, closedHalfSpaceLE] using h
  · have h : Convex 𝕜 (closedHalfSpaceGE b β : Set X) :=
      closedHalfSpaceGE_convex_of_isLinear b β hb
    simpa [solutionSet, holds, closedHalfSpaceGE] using h
  · have h : Convex 𝕜 (openHalfSpaceLT b β : Set X) :=
      openHalfSpaceLT_convex_of_isLinear b β hb
    simpa [solutionSet, holds, openHalfSpaceLT] using h
  · have h : Convex 𝕜 (openHalfSpaceGT b β : Set X) :=
      openHalfSpaceGT_convex_of_isLinear b β hb
    simpa [solutionSet, holds, openHalfSpaceGT] using h
  · have hEq : ((.eq : LinearConstraintRelation).solutionSet b β : Set X) =
        (closedHalfSpaceLE b β : Set X) ∩ closedHalfSpaceGE b β :=
      eq_solutionSet_eq_inter_closedHalfSpaces b β
    rw [hEq]
    have hle : Convex 𝕜 (closedHalfSpaceLE b β : Set X) :=
      closedHalfSpaceLE_convex_of_isLinear b β hb
    have hge : Convex 𝕜 (closedHalfSpaceGE b β : Set X) :=
      closedHalfSpaceGE_convex_of_isLinear b β hb
    exact hle.inter hge

variable {I : Sort u}

/-- The feasible region cut out by a family of linear constraints is convex when each pairing
evaluation map `x ↦ ⟪x, b i⟫ₚ` is linear. -/
theorem convex_feasibleSet_of_forall_isLinear
    (relation : I → LinearConstraintRelation) (b : I → Y) (β : I → 𝕜)
    (hlin : ∀ i, IsLinearMap 𝕜 (fun x : X ↦ (⟪x, b i⟫ₚ : 𝕜))) :
    Convex 𝕜 (feasibleSet relation b β : Set X) := by
  simpa [feasibleSet] using
    convex_iInter fun i ↦ (relation i).convex_solutionSet_of_isLinear (b i) (β i) (hlin i)

end LinearConstraintRelation

end

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedCancelAddMonoid 𝕜]
variable [PosSMulStrictMono 𝕜 𝕜] {I : Sort u}
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

namespace LinearConstraintRelation

/-- Bridge form: one mixed linear-constraint solution set is convex under a linear pairing owner. -/
theorem convex_solutionSet
    (relation : LinearConstraintRelation) (b : Y) (β : 𝕜) :
    Convex 𝕜 (relation.solutionSet b β : Set X) := by
  exact relation.convex_solutionSet_of_isLinear b β (HasLinearPairing.isLinear_pairing_left b)

-- Proof sketch: the displayed feasible region is the intersection of the owner subsets attached
-- to the indexed textbook constraints. Each pointwise factor is convex by
-- `LinearConstraintRelation.convex_solutionSet_of_isLinear`, and intersecting those factors gives
-- the feasible region.
/-- Bridge form: the feasible region cut out by a family of linear constraints is convex under a
linear pairing owner. -/
theorem convex_feasibleSet (relation : I → LinearConstraintRelation) (b : I → Y) (β : I → 𝕜) :
    Convex 𝕜 (feasibleSet relation b β : Set X) := by
  exact convex_feasibleSet_of_forall_isLinear relation b β
    (fun i ↦ HasLinearPairing.isLinear_pairing_left (b i))

end LinearConstraintRelation

/-- Corollary 2.1.2, stated coordinate-free: the common solution set of any family of simultaneous
linear inequalities and equations of the five displayed forms is convex. -/
theorem convex_linear_constraint_solution_set (relation : I → LinearConstraintRelation) (b : I → Y)
    (β : I → 𝕜) :
    Convex 𝕜 (LinearConstraintRelation.feasibleSet relation b β : Set X) :=
  LinearConstraintRelation.convex_feasibleSet relation b β

end

/-! ### Definition_2_1_2 (from Chap01) -/
universe u v

section

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.1.2 introduces polyhedral subsets as finite intersections of
  closed half-spaces. On the public owner surface, the primitive data should therefore be finitely
  many inequality normals and levels, not an ambient inner product model.
- `core/canonical`: the owner abstraction is an ordinary subset `s : Set E`, presented as a
  finite intersection of the chapter half-space owner `closedHalfSpaceLE` attached to a pairing
  witness type `Y` and levels `β : 𝕜`. The owner is pairing-parametric at this primitive layer,
  with linear-dual and other concrete models treated as downstream bridge specializations.
- `bridge/view`: downstream files can pass between this owner and explicit finite indexed
  inequality systems by enumerating the defining `Finset` of `(normal, level)` parameters; no
  separate subset-family owner is needed here.
- Primitive data vs derived API: the primitive source-facing data are finitely many inequality
  parameters `(y, β)` in the chosen pairing layer; convexity and closedness are derived API.
- Domain-style sampling: the relevant owner-side declarations are `closedHalfSpaceLE`,
  `mem_closedHalfSpaceLE_iff`, `convex_halfSpace_le`, `convex_iInter₂`,
  `isClosed_Iic.preimage`, and `LinearMap.continuous_of_finiteDimensional`.
-/

variable {𝕜 : Type u} {E : Type v}
variable [Preorder 𝕜]

namespace Set

variable (𝕜)

/-- Definition 2.1.2: a subset is polyhedral when it can be written as the intersection of
finitely many closed half-spaces, equivalently by finitely many weak pairing inequalities. -/
def IsPolyhedral (s : Set E) (Y : Type _) [HasPairing E Y 𝕜] : Prop :=
  ∃ S : Finset (Y × 𝕜), s = ⋂ y ∈ S, closedHalfSpaceLE y.1 y.2

/-- The intersection of two polyhedral sets is polyhedral. -/
theorem IsPolyhedral.inter {Y : Type _} [HasPairing E Y 𝕜] {s t : Set E}
    (hs : s.IsPolyhedral 𝕜 Y)
    (ht : t.IsPolyhedral 𝕜 Y) :
    (s ∩ t).IsPolyhedral 𝕜 Y := by
  classical
  rcases hs with ⟨S, rfl⟩
  rcases ht with ⟨T, rfl⟩
  refine ⟨S ∪ T, ?_⟩
  ext x
  constructor
  · rintro ⟨hxS, hxT⟩
    simp only [Set.mem_iInter] at hxS hxT ⊢
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hxS y hy
    · exact hxT y hy
  · intro hx
    simp only [Set.mem_inter_iff, Set.mem_iInter] at hx ⊢
    refine ⟨?_, ?_⟩ <;> intro y hy
    · exact hx y (Finset.mem_union.mpr <| Or.inl hy)
    · exact hx y (Finset.mem_union.mpr <| Or.inr hy)

end Set

end

section Convexity

variable {𝕜 : Type u} {E : Type v}
variable [CommSemiring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Set

/-- A finite intersection of weak closed half-spaces is convex once each appearing pairing
evaluation map is linear in the primal variable. -/
theorem convex_iInter_closedHalfSpaceLE_of_forall_isLinear {Y : Type _}
    [HasPairing E Y 𝕜] (S : Finset (Y × 𝕜))
    (hlin : ∀ y ∈ S, IsLinearMap 𝕜 (fun x : E ↦ (HasPairing.pairing x y.1 : 𝕜))) :
    Convex 𝕜 ((⋂ y ∈ S, closedHalfSpaceLE y.1 y.2) : Set E) := by
  refine convex_iInter₂ fun y hy ↦ ?_
  simpa [closedHalfSpaceLE] using
    convex_halfSpace_le (hlin y hy) y.2

/-- Convenience bridge: finite intersections of weak closed half-spaces are convex under a linear
pairing. -/
theorem convex_iInter_closedHalfSpaceLE {Y : Type (max u v)}
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜] (S : Finset (Y × 𝕜)) :
    Convex 𝕜 ((⋂ y ∈ S, closedHalfSpaceLE y.1 y.2) : Set E) :=
  convex_iInter_closedHalfSpaceLE_of_forall_isLinear (𝕜 := 𝕜) (E := E) (Y := Y) S
    (fun y _ ↦ HasLinearPairing.isLinear_pairing_left y.1)

/-- Every polyhedral set is convex once pairing evaluation is linear in the primal variable. -/
theorem IsPolyhedral.convex_of_forall_isLinear {s : Set E} {Y : Type _}
    [HasPairing E Y 𝕜]
    (hs : s.IsPolyhedral 𝕜 Y)
    (hlin : ∀ y : Y, IsLinearMap 𝕜 (fun x : E ↦ (HasPairing.pairing x y : 𝕜))) :
    Convex 𝕜 s := by
  rcases hs with ⟨S, rfl⟩
  exact convex_iInter_closedHalfSpaceLE_of_forall_isLinear
    (𝕜 := 𝕜) (E := E) (Y := Y) S (fun y _ ↦ hlin y.1)

/-- Every polyhedral set is convex. -/
theorem IsPolyhedral.convex {s : Set E}
    {Y : Type (max u v)} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]
    (hs : s.IsPolyhedral 𝕜 Y) : Convex 𝕜 s := by
  exact hs.convex_of_forall_isLinear
    (fun y ↦ HasLinearPairing.isLinear_pairing_left y)

end Set

end Convexity

section TopologicalCanonical

variable {𝕜 : Type u} {E : Type v}
variable [Preorder 𝕜] [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
variable [TopologicalSpace E]

namespace Set

/-- A finite intersection of weak closed half-spaces is closed once each appearing pairing
evaluation is continuous in the primal variable. -/
theorem isClosed_iInter_closedHalfSpaceLE {Y : Type _}
    [HasPairing E Y 𝕜] (S : Finset (Y × 𝕜))
    (hcont : ∀ y ∈ S, Continuous (fun x : E ↦ (HasPairing.pairing x y.1 : 𝕜))) :
    IsClosed ((⋂ y ∈ S, closedHalfSpaceLE y.1 y.2) : Set E) := by
  exact isClosed_biInter fun y hy ↦ by
    change IsClosed ((fun x : E ↦ (HasPairing.pairing x y.1 : 𝕜)) ⁻¹' Set.Iic y.2)
    simpa [closedHalfSpaceLE] using isClosed_Iic.preimage (hcont y hy)

/-- Convenience bridge: if pairing evaluation is globally continuous in the primal variable, then
finite intersections of weak closed half-spaces are closed. -/
theorem isClosed_iInter_closedHalfSpaceLE_of_continuousPairing {Y : Type _}
    [HasPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜] (S : Finset (Y × 𝕜)) :
    IsClosed ((⋂ y ∈ S, closedHalfSpaceLE y.1 y.2) : Set E) :=
  isClosed_iInter_closedHalfSpaceLE (𝕜 := 𝕜) (E := E) (Y := Y) S
    (fun y _ ↦ HasContinuousPairing.continuous_pairing_left (X := E) (Y := Y) (𝕜 := 𝕜) y.1)

/-- A polyhedral set is closed whenever pairing evaluation is continuous in the primal variable. -/
theorem IsPolyhedral.isClosed {s : Set E}
    {Y : Type (max u v)} [HasPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜]
    (hs : s.IsPolyhedral 𝕜 Y) : IsClosed s := by
  rcases hs with ⟨S, rfl⟩
  simpa using isClosed_iInter_closedHalfSpaceLE_of_continuousPairing
    (𝕜 := 𝕜) (E := E) (Y := Y) S

end Set

end TopologicalCanonical

section TopologicalPairingBridge

variable {𝕜 : Type u} {E : Type v}
variable [Preorder 𝕜] [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
variable [TopologicalSpace E]

namespace Set

/-- Pairing bridge: finite intersections of half-spaces are closed when each appearing pairing
functional is continuous in the primal variable. -/
theorem isClosed_iInter_closedHalfSpaceLE_of_forall_continuous
    {Y : Type _} [HasPairing E Y 𝕜] (S : Finset (Y × 𝕜))
    (hcont : ∀ y ∈ S, Continuous (fun x : E ↦ (HasPairing.pairing x y.1 : 𝕜))) :
    IsClosed ((⋂ y ∈ S, closedHalfSpaceLE y.1 y.2) : Set E) :=
  isClosed_iInter_closedHalfSpaceLE (𝕜 := 𝕜) (E := E) (Y := Y) S hcont

/-- Pairing bridge: a polyhedral set is closed when all pairing evaluations
`x ↦ ⟪x, y⟫ₚ` are continuous in the ambient topology. -/
theorem IsPolyhedral.isClosed_of_forall_continuous {Y : Type _}
    [HasPairing E Y 𝕜]
    {s : Set E} (hs : s.IsPolyhedral 𝕜 Y)
    (hcont : ∀ y : Y, Continuous (fun x : E ↦ (HasPairing.pairing x y : 𝕜))) : IsClosed s := by
  rcases hs with ⟨S, rfl⟩
  exact isClosed_iInter_closedHalfSpaceLE_of_forall_continuous (𝕜 := 𝕜) (E := E) (Y := Y) S
    (fun y hy ↦ hcont y.1)

end Set

end TopologicalPairingBridge

section TopologicalBridgeFiniteDimensional

variable {𝕜 : Type u} {E : Type v}
variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [Preorder 𝕜] [ClosedIicTopology 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [T2Space E] [FiniteDimensional 𝕜 E]
variable {Y : Type _}
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

/-- Every pairing-linear polyhedral set is closed in a finite-dimensional topological
`𝕜`-module. -/
theorem Set.IsPolyhedral.isClosed_of_finiteDimensional {s : Set E} (hs : s.IsPolyhedral 𝕜 Y) :
    IsClosed s :=
  hs.isClosed_of_forall_continuous fun y ↦ by
    have hycont : Continuous ((HasLinearPairing.pairingLinear.flip y : E →ₗ[𝕜] 𝕜)) := by
      simpa using
        (LinearMap.continuous_of_finiteDimensional
          (f := (HasLinearPairing.pairingLinear.flip y : E →ₗ[𝕜] 𝕜)))
    simpa [HasLinearPairing.pairing_eq_pairingLinear] using hycont

end TopologicalBridgeFiniteDimensional
