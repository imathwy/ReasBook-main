import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_10

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

variable {R : Type w} [MulZeroClass R] [Preorder R] [PosMulMono R]
variable {M : Type u} {N : Type v}
variable [Sub M]
variable [SMul R N]
variable [HasPairing M N R]
variable [HasPairingSMulRight M N R]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.7.12 says the source-owned set `normalCone C a` is a convex
  cone.
- `core/canonical`: the primitive owner data are the feasibility condition `a ∈ C` and the
  pointwise nonnegativity inequalities defining `normalCone C a`.
- `bridge/view`: the source-facing notation `N(a | C)` exposes this primitive owner directly
  without forcing a bundled cone bridge.
- `Primitive data vs derived API`: the primitive public object is the source-facing set
  `normalCone C a`; both cone closure and convexity are proved directly from the primitive
  inequality owner at weak order assumptions.
- Domain-style sampling: the relevant declarations are `normalCone`,
  `Set.isCone_iff_forall_pos_smul_subset`, pairing-right linearity bridges
  (`pairing_smul_right`, `HasPairingAddRight.pairing_add_right`), and `convex_iff_add_mem`.
- Layer target: `source-facing`.
-/

open scoped Rockafellar

/-- The normal cone to any subset is a cone in the sense of Definition 2.5.9. -/
theorem normalCone_isCone (C : Set M) (a : M) :
    Set.IsCone R ((N[R](a | C)) : Set N) := by
  rw [Set.isCone_iff_forall_pos_smul_subset]
  intro c hc xStar hxStar
  rcases Set.mem_smul_set.mp hxStar with ⟨yStar, hyStar, rfl⟩
  rw [mem_normalCone_iff] at hyStar ⊢
  rcases hyStar with ⟨haC, hyStar_mem⟩
  refine ⟨haC, ?_⟩
  intro x hxC
  have hsmul :
      (⟪a - x, c • yStar⟫ₚ : R) = c * (⟪a - x, yStar⟫ₚ : R) :=
    pairing_smul_right (x := a - x) (c := c) (y := yStar)
  have hnonneg : (0 : R) ≤ c * (⟪a - x, yStar⟫ₚ : R) := by
    exact mul_nonneg (le_of_lt hc) (hyStar_mem x hxC)
  simpa [hsmul] using hnonneg

end

section

universe u v w

variable {R : Type w} [Semiring R] [PartialOrder R] [PosMulMono R] [AddLeftMono R]
variable {M : Type u} {N : Type v}
variable [Sub M]
variable [AddCommMonoid N] [SMul R N]
variable [HasPairing M N R]
variable [HasPairingSMulRight M N R]
variable [HasPairingAddRight M N R]

open scoped Rockafellar

/-- Proposition 2.7.12: the normal cone to a set `C` at `a` is convex, hence together with
`normalCone_isCone` it is a convex cone in the source sense. -/
theorem normalCone_convex (C : Set M) (a : M) :
    Convex R ((N[R](a | C)) : Set N) := by
  refine convex_iff_add_mem.2 ?_
  intro xStar hxStar yStar hyStar α β hα hβ hαβ
  rw [mem_normalCone_iff] at hxStar hyStar ⊢
  rcases hxStar with ⟨haC, hxineq⟩
  rcases hyStar with ⟨_, hyineq⟩
  refine ⟨haC, ?_⟩
  intro x hxC
  have hxα : 0 ≤ α * (⟪a - x, xStar⟫ₚ : R) := mul_nonneg hα (hxineq x hxC)
  have hyβ : 0 ≤ β * (⟪a - x, yStar⟫ₚ : R) := mul_nonneg hβ (hyineq x hxC)
  have hpair :
      (⟪a - x, α • xStar + β • yStar⟫ₚ : R)
        = α * (⟪a - x, xStar⟫ₚ : R) + β * (⟪a - x, yStar⟫ₚ : R) := by
    calc
      (⟪a - x, α • xStar + β • yStar⟫ₚ : R)
          = (⟪a - x, α • xStar⟫ₚ : R) + (⟪a - x, β • yStar⟫ₚ : R) := by
              exact HasPairingAddRight.pairing_add_right (a - x) (α • xStar) (β • yStar)
      _ = α * (⟪a - x, xStar⟫ₚ : R) + β * (⟪a - x, yStar⟫ₚ : R) := by
            rw [pairing_smul_right, pairing_smul_right]
  exact hpair ▸ add_nonneg hxα hyβ

/-- Proposition 2.7.12 in canonical source-facing owner form: the normal cone is a convex cone. -/
theorem normalCone_isConvexCone (C : Set M) (a : M) :
    Set.IsConvexCone R ((N[R](a | C)) : Set N) :=
  ⟨normalCone_isCone (C := C) (a := a), normalCone_convex (C := C) (a := a)⟩

end
