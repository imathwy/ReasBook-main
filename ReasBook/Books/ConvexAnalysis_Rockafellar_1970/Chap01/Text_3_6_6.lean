import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable {E : Type u}
variable [One R] [Add E]

/-- Helper for Text 3.6.6: taking the height-`1` section commutes with the chapter
fiberwise-sum owner `+ᶠ`. -/
@[simp] theorem unitSection_fiberwiseSum_eq (S₁ S₂ : Set (R × E)) :
    U[R | S₁ +ᶠ S₂] = U[R | S₁] + U[R | S₂] := by
  ext x
  simp [Set.mem_fiberwiseSum, Set.mem_add]

/-- Helper for Text 3.6.6: pointwise form of `unitSection_fiberwiseSum_eq`. -/
@[simp] theorem mem_unitSection_fiberwiseSum_iff (S₁ S₂ : Set (R × E)) (x : E) :
    x ∈ U[R | S₁ +ᶠ S₂] ↔ x ∈ U[R | S₁] + U[R | S₂] := by
  simp [unitSection_fiberwiseSum_eq (R := R) (S₁ := S₁) (S₂ := S₂)]

/-- Helper for Text 3.6.6: ambient membership in a fiberwise sum at height `1` is the same as
membership in the Minkowski sum of the two height-`1` sections. -/
@[simp] theorem mem_fiberwiseSum_mk_one_iff (S₁ S₂ : Set (R × E)) (x : E) :
    ((1 : R), x) ∈ S₁ +ᶠ S₂ ↔ x ∈ U[R | S₁] + U[R | S₂] := by
  -- Rewrite the ambient pair membership as unit-section membership at height `1`.
  rw [← mem_unitSection_iff (R := R) (S := S₁ +ᶠ S₂) (x := x)]
  -- The generic unit-section/fiberwise-sum bridge now closes the goal.
  exact mem_unitSection_fiberwiseSum_iff (R := R) (S₁ := S₁) (S₂ := S₂) x

end

section

open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable {E : Type u}
variable [Monoid R] [Zero R] [LE R] [ZeroLEOneClass R]
variable [Add E] [MulAction R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.6 fixes subsets `C₁, C₂ ⊆ R^n`, forms their homogenization sets
  `K₁ = homogenizationSet C₁` and `K₂ = homogenizationSet C₂`, then considers the set `K` of pairs
  `(λ, x)` for which `x = x₁ + x₂` with `(λ, x₁) ∈ K₁` and `(λ, x₂) ∈ K₂`.
- `core/canonical`: the owner abstractions are the existing chapter declarations
  `homogenizationSet` and the binary operator `+ᶠ`; no second public set-level wrapper is needed.
- `bridge/view`: the textbook set `K` is exactly
  `homogenizationSet C₁ +ᶠ homogenizationSet C₂`, and the main content is the
  identification of its unit section with the Minkowski sum `C₁ + C₂`.
- Primitive data vs derived API: the homogenization sets and their fiberwise sum are primitive
  owner data; the unit-section equality and its pointwise membership reformulation are the needed
  derived API.
- Domain-style sampling: this item follows `homogenizationSet`,
  `mem_homogenizationSet_iff`, `unitSection`, `(+ᶠ)`, and
  `Set.mem_fiberwiseSum`.
- Layer target: `bridge/view`.
- Ambient minimization: beyond the scalar-action structure required by `homogenizationSet`, the
  only extra ambient data are the additive structure on `E` needed by the owners `+ᶠ` and
  `C₁ + C₂`, so the file should live over that owner layer rather than the concrete model
  `EuclideanSpace ℝ (Fin n)`.
- Abstraction checks:
  1. Codomain/ambient over-concrete? `Yes` before normalization: this bridge can be stated first
     for arbitrary `S₁, S₂ : Set (R × E)` and only then specialized to homogenization sets.
  2. Scalar/ambient structure too strong? `Yes` before normalization: the owner-level bridge needs
     only `[One R] [Add E]`; order and scalar-action assumptions belong only to the
     homogenization specialization.
  3. Owner tied to concrete model? `No`: owners are `unitSection`, `+ᶠ`, and `homogenizationSet`.
  4. Better intrinsic/relative topology formulation? `N/A` (non-topological statement).
  5. Owner names too concrete/heavy? `Yes` before normalization at theorem-surface spelling:
     use `fiberwiseSum` (matching owner naming) rather than mixed `fiberwise_sum`.
  6. Notation needed and used? `Yes`; theorem surfaces use `U[R | _]`, `K[R | _]`, and `+ᶠ`.
-/

/-- Helper for Text 3.6.6: the section at height `1` of the fiberwise sum of the homogenization
sets of `C₁` and `C₂` is exactly the Minkowski sum `C₁ + C₂`. -/
-- Proof sketch: unfold the fiberwise-sum owner only at height `1`. Then each witness
-- in the two section factors rewrites by the height-`1` homogenization-section bridge.
@[simp] theorem unitSection_fiberwiseSum_homogenizationSet_eq (C₁ C₂ : Set E) :
    U[R | K[R | C₁] +ᶠ K[R | C₂]] = C₁ + C₂ := by
  calc
    U[R | K[R | C₁] +ᶠ K[R | C₂]]
        = U[R | K[R | C₁]] + U[R | K[R | C₂]] :=
          unitSection_fiberwiseSum_eq (S₁ := K[R | C₁]) (S₂ := K[R | C₂])
    _ = C₁ + C₂ := by
      simp

/-- Membership in the unit section of the fiberwise sum of the homogenization sets of `C₁` and
`C₂` is equivalent to membership in the Minkowski sum `C₁ + C₂`. -/
-- Proof sketch: this is the pointwise form of
-- `unitSection_fiberwiseSum_homogenizationSet_eq`.
@[simp] theorem mem_unitSection_fiberwiseSum_homogenizationSet_iff
    (C₁ C₂ : Set E) (x : E) :
    x ∈ U[R | K[R | C₁] +ᶠ K[R | C₂]] ↔ x ∈ C₁ + C₂ := by
  simp [unitSection_fiberwiseSum_homogenizationSet_eq (C₁ := C₁) (C₂ := C₂)]

/-- Text 3.6.6: ambient membership at height `1` in the fiberwise sum of the homogenization sets
of `C₁` and `C₂` is equivalent to membership in the Minkowski sum `C₁ + C₂`. -/
theorem mem_fiberwiseSum_homogenizationSet_mk_one_iff
    (C₁ C₂ : Set E) (x : E) :
    ((1 : R), x) ∈ K[R | C₁] +ᶠ K[R | C₂] ↔ x ∈ C₁ + C₂ := by
  -- Rewrite the ambient pair-membership statement as a unit-section statement, and
  -- then apply the unit-section membership theorem already proved above.
  -- Pass through the generic height-`1` ambient-membership bridge for fiberwise sums.
  calc
    ((1 : R), x) ∈ K[R | C₁] +ᶠ K[R | C₂]
        ↔ x ∈ U[R | K[R | C₁]] + U[R | K[R | C₂]] :=
          mem_fiberwiseSum_mk_one_iff (R := R) (S₁ := K[R | C₁]) (S₂ := K[R | C₂]) x
    _ ↔ x ∈ C₁ + C₂ := by
      -- Each height-`1` section of a homogenization set collapses to the original set.
      simp

end
