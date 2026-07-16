import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped Rockafellar

universe u v

namespace Function

/-- Helper for Text 5.5.0.3: the canonical codomain lift views a finite-valued function as
`WithTopBot`-valued. -/
abbrev toWithTopBot {E : Type u} {α : Type v} (f : E → α) : E → WithTopBot α :=
  fun x ↦ (f x : WithTopBot α)

end Function

section

variable {ι : Type u}

/-
Source/core/bridge triage:
- `source-facing`: the item evaluates the support function of the standard simplex and identifies
  it with the greatest component of `x`; textbook finite-dimensional coordinate versions are
  specializations of this owner-level statement.
- `core/canonical`: the owner abstractions are the chapter support-function declaration
  `δᵛ(x | C)` from `Defintion_4_8_2`, the owner `greatestCoordinate` from Text 5.5.0.1,
  and mathlib's simplex owner `stdSimplex 𝕜 ι : Set (ι → 𝕜)`.
- `bridge/view`: the coordinate formula `{y | ∀ i, 0 ≤ y i ∧ ∑ i, y i = 1}` is used only as a
  theorem-level bridge rewriting of the canonical owner `stdSimplex 𝕜 ι`.
- semantic guard: `stdSimplex 𝕜 ι` is empty when `ι` is empty, so the intrinsic
  `WithTopBot`-valued supremum formula is the canonical no-hypothesis surface; the
  `greatestCoordinate` surface is a nonempty-index bridge.
- Primitive data vs derived API: there is no new simplex data in this file; `stdSimplex 𝕜 ι`
  is the upstream owner.
- Domain-style sampling used here: `supportFunction`, `supportFunction_def`, `stdSimplex`,
  `single_mem_stdSimplex`, `greatestCoordinate`, and `Function.toWithTopBot`.
- Layer target: `source-facing` main theorem stated on the intrinsic simplex owner
  `stdSimplex 𝕜 ι : Set (ι → 𝕜)`, with a theorem-level coordinate bridge.
-/

section OrderedScalar

variable {𝕜 : Type v}
variable [ConditionallyCompleteLattice 𝕜]

/-- Helper for Text 5.5.0.3: the greatest coordinate of a finite family is the supremum of its
coordinate range. -/
def greatestCoordinate [Nonempty ι] : (ι → 𝕜) → 𝕜 :=
  fun x ↦ sSup (Set.range x)

/-- Helper for Text 5.5.0.3: unfolding `greatestCoordinate` exposes the supremum of the
coordinate range. -/
@[simp] theorem greatestCoordinate_apply [Nonempty ι] (x : ι → 𝕜) :
    greatestCoordinate x = sSup (Set.range x) :=
  rfl

/-- Helper for Text 5.5.0.3: coercing `greatestCoordinate` to `WithTopBot` turns the finite
coordinate supremum into the indexed supremum. -/
theorem greatestCoordinate_toWithTopBot_eq_iSup [Finite ι] [Nonempty ι] :
    greatestCoordinate.toWithTopBot =
      ⨆ i : ι, fun x : ι → 𝕜 ↦ (x i : WithTopBot 𝕜) := by
  funext x
  have hx_bdd : BddAbove (Set.range x) := Finite.bddAbove_range x
  have hx_bdd_bot : BddAbove (Set.range fun i : ι ↦ ((x i : 𝕜) : WithBot 𝕜)) :=
    Finite.bddAbove_range (fun i : ι ↦ ((x i : 𝕜) : WithBot 𝕜))
  -- Rewrite the finite owner to the supremum of the coordinate range, then move the supremum
  -- through the coercion into `WithTopBot`.
  simp only [Function.toWithTopBot, iSup_apply]
  rw [greatestCoordinate_apply, sSup_range]
  rw [WithBot.coe_iSup hx_bdd]
  rw [WithTop.coe_iSup (fun i : ι ↦ ((x i : 𝕜) : WithBot 𝕜)) hx_bdd_bot]

section FintypeIndex

variable [Fintype ι]
variable [Semiring 𝕜] [IsOrderedAddMonoid 𝕜] [PosMulMono 𝕜] [ZeroLEOneClass 𝕜]

local instance instHasPairingPiDot : HasPairing (ι → 𝕜) (ι → 𝕜) 𝕜 where
  pairing x y := y ⬝ᵥ x

-- Proof sketch: show first that every simplex point `w` gives
-- `⟪x, w⟫ₚ ≤ sSup (Set.range x)` because the coordinates of `w` are nonnegative
-- and sum to `1`,
-- so `⟪x, w⟫ₚ` is a convex combination of the coordinates of `x`. For the reverse inequality,
-- evaluate at each singleton weight `Pi.single i 1` and then take `⨆ i`.
/-- Text 5.5.0.3 on the intrinsic simplex owner: the support function of `stdSimplex 𝕜 ι` is the
greatest coordinate. This requires the index type to be nonempty. -/
theorem supportFunction_stdSimplex_eq_greatestCoordinate [Nonempty ι] :
    (fun x : ι → 𝕜 ↦ supportFunction (L := WithTopBot 𝕜) (stdSimplex 𝕜 ι) x) =
      greatestCoordinate.toWithTopBot := by
  funext x
  classical
  have hx_bdd : BddAbove (Set.range x) := Set.Finite.bddAbove (Set.toFinite (Set.range x))
  have hle_greatest : ∀ j : ι, x j ≤ greatestCoordinate x := by
    intro j
    rw [greatestCoordinate_apply]
    exact le_csSup hx_bdd (Set.mem_range_self j)
  rw [supportFunction_def]
  change
      (⨆ y : stdSimplex 𝕜 ι,
        (⟪x, (y : ι → 𝕜)⟫ₚ : WithTopBot 𝕜)) =
      greatestCoordinate.toWithTopBot x
  have hgreatest_eq_iSup :
      greatestCoordinate.toWithTopBot x = ⨆ i : ι, (x i : WithTopBot 𝕜) := by
    simpa [iSup_apply] using
      congrFun (greatestCoordinate_toWithTopBot_eq_iSup (ι := ι)) x
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro y
    have hy_nonneg : 0 ≤ (y : ι → 𝕜) := fun j ↦ y.2.1 j
    have hsum : (∑ j, (y : ι → 𝕜) j) = 1 := y.2.2
    have hinner : (⟪x, (y : ι → 𝕜)⟫ₚ : 𝕜) ≤ greatestCoordinate x := by
      calc
        ⟪x, (y : ι → 𝕜)⟫ₚ = (y : ι → 𝕜) ⬝ᵥ x := rfl
        _ ≤ (y : ι → 𝕜) ⬝ᵥ fun _ : ι ↦ greatestCoordinate x := by
          refine Finset.sum_le_sum ?_
          intro j _
          exact mul_le_mul_of_nonneg_left (hle_greatest j) (hy_nonneg j)
        _ = ∑ j, (y : ι → 𝕜) j * greatestCoordinate x := by simp [dotProduct]
        _ = (∑ j, (y : ι → 𝕜) j) * greatestCoordinate x := by rw [← Finset.sum_mul]
        _ = greatestCoordinate x := by simp [hsum]
    change (((y : ι → 𝕜) ⬝ᵥ x : 𝕜) : WithTopBot 𝕜) ≤ greatestCoordinate.toWithTopBot x
    rw [Function.toWithTopBot, WithTop.coe_le_coe, WithBot.coe_le_coe]
    exact hinner
  · calc
      greatestCoordinate.toWithTopBot x = ⨆ i : ι, (x i : WithTopBot 𝕜) := hgreatest_eq_iSup
      _ ≤ ⨆ y : stdSimplex 𝕜 ι, (⟪x, (y : ι → 𝕜)⟫ₚ : WithTopBot 𝕜) := by
        refine iSup_le ?_
        intro i
        refine le_iSup_of_le ⟨Pi.single i (1 : 𝕜), single_mem_stdSimplex 𝕜 i⟩ ?_
        change ((x i : 𝕜) : WithTopBot 𝕜) ≤
          ((((⟨Pi.single i (1 : 𝕜), single_mem_stdSimplex 𝕜 i⟩ : stdSimplex 𝕜 ι) : ι → 𝕜) ⬝ᵥ
            x : 𝕜) : WithTopBot 𝕜)
        rw [WithTop.coe_le_coe, WithBot.coe_le_coe]
        change x i ≤ (Pi.single i (1 : 𝕜)) ⬝ᵥ x
        simp [single_dotProduct]

/-- Pointwise form of `supportFunction_stdSimplex_eq_greatestCoordinate`. -/
theorem supportFunction_stdSimplex_eq_greatestCoordinate_apply [Nonempty ι] (x : ι → 𝕜) :
    supportFunction (L := WithTopBot 𝕜) (stdSimplex 𝕜 ι) x = greatestCoordinate.toWithTopBot x := by
  simpa using
    congrFun (supportFunction_stdSimplex_eq_greatestCoordinate (ι := ι)) x
 
/-- Intrinsic `WithTopBot`-valued form of Text 5.5.0.3:
the support function of `stdSimplex 𝕜 ι` is the coordinate supremum. -/
theorem supportFunction_stdSimplex_eq_iSup [Nontrivial 𝕜] :
    (fun x : ι → 𝕜 ↦ supportFunction (L := WithTopBot 𝕜) (stdSimplex 𝕜 ι) x) =
      (fun x : ι → 𝕜 ↦ ⨆ i : ι, (x i : WithTopBot 𝕜)) := by
  funext x
  classical
  by_cases hι : Nonempty ι
  · let _ : Nonempty ι := hι
    rw [supportFunction_stdSimplex_eq_greatestCoordinate_apply (ι := ι) x]
    simpa [iSup_apply] using
      congrFun (greatestCoordinate_toWithTopBot_eq_iSup (ι := ι)) x
  · let _ : IsEmpty ι := not_nonempty_iff.mp hι
    rw [supportFunction_def, stdSimplex_of_isEmpty_index (𝕜 := 𝕜) (ι := ι)]
    simp [iSup_of_empty]

/-- Pointwise form of `supportFunction_stdSimplex_eq_iSup`. -/
theorem supportFunction_stdSimplex_eq_iSup_apply [Nontrivial 𝕜] (x : ι → 𝕜) :
    supportFunction (L := WithTopBot 𝕜) (stdSimplex 𝕜 ι) x = ⨆ i : ι, (x i : WithTopBot 𝕜) := by
  simpa using congrFun (supportFunction_stdSimplex_eq_iSup (ι := ι)) x

/-- Coordinate-form intrinsic bridge for Text 5.5.0.3:
the support function of `{y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}` equals the coordinate supremum. -/
theorem supportFunction_coordinateSimplex_eq_iSup [Nontrivial 𝕜] :
    (fun x : ι → 𝕜 ↦
      supportFunction (L := WithTopBot 𝕜)
        ({y : ι → 𝕜 | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} : Set (ι → 𝕜)) x) =
      (fun x : ι → 𝕜 ↦ ⨆ i : ι, (x i : WithTopBot 𝕜)) := by
  simpa [stdSimplex] using supportFunction_stdSimplex_eq_iSup (ι := ι)

/-- Pointwise form of `supportFunction_coordinateSimplex_eq_iSup`. -/
theorem supportFunction_coordinateSimplex_eq_iSup_apply [Nontrivial 𝕜] (x : ι → 𝕜) :
    supportFunction (L := WithTopBot 𝕜)
      ({y : ι → 𝕜 | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} : Set (ι → 𝕜)) x =
      ⨆ i : ι, (x i : WithTopBot 𝕜) := by
  simpa using congrFun (supportFunction_coordinateSimplex_eq_iSup (ι := ι)) x

/-- Coordinate-form bridge for Text 5.5.0.3:
the support function of `{y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}` equals the greatest coordinate. -/
theorem supportFunction_coordinateSimplex_eq_greatestCoordinate [Nonempty ι] :
    (fun x : ι → 𝕜 ↦
      supportFunction (L := WithTopBot 𝕜)
        ({y : ι → 𝕜 | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} : Set (ι → 𝕜)) x) =
      greatestCoordinate.toWithTopBot := by
  simpa [stdSimplex] using
    supportFunction_stdSimplex_eq_greatestCoordinate (ι := ι)

/-- Pointwise form of `supportFunction_coordinateSimplex_eq_greatestCoordinate`. -/
theorem supportFunction_coordinateSimplex_eq_greatestCoordinate_apply [Nonempty ι] (x : ι → 𝕜) :
    supportFunction (L := WithTopBot 𝕜)
      ({y : ι → 𝕜 | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} : Set (ι → 𝕜)) x =
      greatestCoordinate.toWithTopBot x := by
  simpa using
    congrFun
      (supportFunction_coordinateSimplex_eq_greatestCoordinate (ι := ι)) x

end FintypeIndex

end OrderedScalar

end
