import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SimplicialObject
open SimplicialObject.Splitting
open scoped Simplicial

universe u

noncomputable section

namespace SSet

/- Domain-style sampling for 14.18.2:
- primary domain: simplicial-set splittings by nondegenerate simplices
- sampled owner API:
  `SimplicialObject.Splitting`,
  `SimplicialObject.Splitting.cofan`,
  `SimplicialObject.Split.mk'`,
  `SSet.nonDegenerate`,
  `SSet.exists_nonDegenerate`
- best owner abstraction: `SimplicialObject.Splitting U`
- primitive data: the degreewise family `U.nonDegenerate`, the inclusions `Subtype.val`, and the
  colimit witness `s.isColimit'`
- derived API: the source-facing existence theorem `split_by_nondegenerate_simplices`
- source/core/bridge triage: the source lemma is `source-facing`, but its operational owner is the
  canonical `core/canonical` object `SimplicialObject.Splitting U`; this file therefore keeps the
  canonical owner construction and derives the source-facing existence statement directly from it.
-/

private def nonDegenerateSplittingIsColimit (U : SSet.{u}) (Δ : SimplexCategoryᵒᵖ) :
    Limits.IsColimit
      (Splitting.cofan' (fun n ↦ ↥(U.nonDegenerate n)) U
        (fun n ↦ (Subtype.val : U.nonDegenerate n → U _⦋n⦌)) Δ) := by
  let N : ℕ → Type u := fun n ↦ ↥(U.nonDegenerate n)
  let ι : ∀ n, N n → U _⦋n⦌ := fun n ↦ (Subtype.val : U.nonDegenerate n → U _⦋n⦌)
  obtain ⟨Δ⟩ := Δ
  induction Δ using SimplexCategory.rec with
  | _ n =>
      let c : Limits.Cofan (summand N (op ⦋n⦌)) :=
        Splitting.cofan' N U ι (op ⦋n⦌)
      have hc : c.cofanTypes.IsColimit := by
        refine Limits.CofanTypes.isColimit_mk c.cofanTypes ?_ ?_ ?_
        · intro x
          obtain ⟨m, f, _, y, hy⟩ := U.exists_nonDegenerate x
          refine ⟨IndexSet.mk f, y, ?_⟩
          simpa [c, Splitting.cofan', Splitting.IndexSet.mk] using hy.symm
        · intro A y₁ y₂ h
          change U.nonDegenerate A.1.unop.len at y₁ y₂
          let x : U _⦋n⦌ := U.map A.e.op y₁.1
          have hy₁ : x = U.map A.e.op y₁ := rfl
          have hy₂ : x = U.map A.e.op y₂ := by
            simpa [x, c, Splitting.cofan'] using h
          exact U.unique_nonDegenerate_simplex x A.e y₁ hy₁ A.e y₂ hy₂
        · rintro ⟨Δ₁, ⟨f₁, _⟩⟩ ⟨Δ₂, ⟨f₂, _⟩⟩ y z h
          change U.nonDegenerate Δ₁.unop.len at y
          change U.nonDegenerate Δ₂.unop.len at z
          let x : U _⦋n⦌ := U.map f₁.op y.1
          have hy : x = U.map f₁.op y := rfl
          have hz : x = U.map f₂.op z := by
            simpa [x, c, Splitting.cofan'] using h
          have hlen : Δ₁.unop.len = Δ₂.unop.len :=
            U.unique_nonDegenerate_dim x f₁ y hy f₂ z hz
          have hΔ : Δ₁ = Δ₂ := by
            exact Opposite.unop_injective (by ext; exact hlen)
          subst hΔ
          have hf : f₁ = f₂ :=
            U.unique_nonDegenerate_map x f₁ y hy f₂ z hz
          simp [hf]
      exact ((Limits.Cofan.isColimit_cofanTypes_iff c).1 hc).some

variable (U : SSet.{u})

-- Proof sketch: in degree `n`, take the distinguished summand to be the type of nondegenerate
-- `n`-simplices, included by the subtype map. The colimit proof is the canonical decomposition of
-- simplices by their unique nondegenerate presentation.
/-- The canonical splitting of a simplicial set whose degree-`n` distinguished summand is the type
of nondegenerate `n`-simplices. -/
abbrev nonDegenerateSplitting : Splitting U where
  N := fun n ↦ ↥(U.nonDegenerate n)
  ι n := (Subtype.val : U.nonDegenerate n → U _⦋n⦌)
  isColimit' := nonDegenerateSplittingIsColimit U

end SSet

namespace SSet

variable (U : SSet.{u})

-- Proof sketch: use the canonical owner `U.nonDegenerateSplitting`; in degree `n`, its
-- distinguished inclusion is `Subtype.val : U.nonDegenerate n → U _⦋n⦌`, whose range is exactly
-- `U.nonDegenerate n`.
/-- Lemma 14.18.2: every simplicial set admits a splitting whose degree-`n` distinguished summand
is exactly the set of nondegenerate `n`-simplices. -/
@[stacks 017R]
theorem split_by_nondegenerate_simplices :
    ∃ s : Splitting U, ∀ n : ℕ, Set.range (s.ι n) = U.nonDegenerate n := by
  refine ⟨U.nonDegenerateSplitting, ?_⟩
  intro n
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

end SSet
