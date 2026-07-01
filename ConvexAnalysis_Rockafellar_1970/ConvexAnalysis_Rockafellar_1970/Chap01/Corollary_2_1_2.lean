import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_1

-- Declarations for this item will be appended below by the statement pipeline.

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
