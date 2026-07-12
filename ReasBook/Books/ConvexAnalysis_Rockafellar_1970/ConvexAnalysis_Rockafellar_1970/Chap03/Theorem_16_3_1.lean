import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w z

section

open Function
open scoped Rockafellar

variable {E : Type u} {F : Type v} {EStar : Type w} {FStar : Type z}
variable {α : Type*}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [DenselyOrdered α] [NoBotOrder α] [NoTopOrder α] [Nonempty α]
variable [HasPairing E EStar α] [HasPairing F FStar α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.3.1 states that the conjugate of the image `Af` of a function `f`
  under a linear transformation is obtained by composing the conjugate `f*` with the dual-side map
  `A*`.
- `core/canonical`: the chapter owners are the image operation `A ◁ f` from Theorem 5.7 and the
  Fenchel conjugate `f⋆` from Defn 12.2.
- `bridge/view`: the duality relation is exposed directly as a pairing-side compatibility identity
  between `A` and an explicit dual map `Astar`.

Domain-style sampling used here:
- `Function.linearImage` and its scoped notation `◁` from Theorem 5.7;
- `convexConjugate` and its scoped postfix notation `⋆` from Defn 12.2;
- `HasPairing` from Chapter 1 for primal/dual evaluation;
- an explicit pairing compatibility hypothesis
  `∀ x y⋆, ⟪A x, y⋆⟫ = ⟪x, Astar y⋆⟫`.

Primitive data vs derived API:
- primitive inputs: the primal map `A`, the dual map `Astar`, the duality compatibility relation,
  and the function `f`;
- derived API: the conjugate identity itself, expressed directly as an equality of functions.

Layer target: `source-facing`, stated through the canonical chapter owners rather than by
introducing any parallel local wrapper.

Semantic note: the source presents this identity in the convex-analysis setting, but the owner-side
formula itself already makes sense for arbitrary `WithTopBot α`-valued `f`, so no extra wrapper or
auxiliary packaging is needed around the canonical statement.

Ambient note: the core owner statement only needs paired spaces and an explicit dual map satisfying
the pairing identity.
-/

-- Proof sketch: unfold `(A ◁ f)⋆` and the fiberwise definition of `A ◁ f`. For fixed `y⋆`,
-- rewrite the outer supremum over `y` and the inner infimum over the fiber `A x = y` as a single
-- supremum over `x`. Then use pairing compatibility to replace `⟪A x, y⋆⟫` by
-- `⟪x, Astar y⋆⟫`, which is exactly the defining supremum for `f⋆ (Astar y⋆)`.
/-- Theorem 16.3.1 in canonical owner form: if a primal map `A` and a dual map `Astar` satisfy
`⟪A x, y⋆⟫ = ⟪x, Astar y⋆⟫`, then the Fenchel conjugate of `A ◁ f` is `f⋆ ∘ Astar`. -/
theorem convexConjugate_linearImage_eq_comp
    (A : E → F) (Astar : FStar → EStar)
    (hA : ∀ x yStar, ⟪A x, yStar⟫ₚ = ⟪x, Astar yStar⟫ₚ)
    (f : E → WithTopBot α) :
    (A ◁ f)⋆ = f⋆ ∘ Astar := by
  ext yStar
  simp only [Function.comp_apply]
  rw [convexConjugate_eq_iSup_pairing_sub, convexConjugate_eq_iSup_pairing_sub]
  apply le_antisymm
  · refine iSup_le fun y ↦ ?_
    let s : Set (WithTopBot α) := f '' {x : E | A x = y}
    let c : WithTopBot α := ⟪y, yStar⟫ₚ
    rw [linearImage_eq_sInf_image]
    change c - sInf s ≤ ⨆ x : E, ((⟪x, Astar yStar⟫ₚ : α) : WithTopBot α) - f x
    refine (WithBotTop.le_of_forall_lt_iff_le (α := α)).2 ?_
    intro z hz
    have hz_sum : (z : WithTopBot α) + sInf s < c := by
      exact
        (WithBotTop.lt_sub_iff_add_lt
          (.inr (show (z : WithTopBot α) ≠ ⊤ by simp))
          (.inr (show (z : WithTopBot α) ≠ ⊥ by simp))).1 hz
    have hzs : sInf s < c - (z : WithTopBot α) := by
      refine
        (WithBotTop.lt_sub_iff_add_lt
          (.inl (show (z : WithTopBot α) ≠ ⊥ by simp))
          (.inl (show (z : WithTopBot α) ≠ ⊤ by simp))).2 ?_
      simpa [add_comm] using hz_sum
    rcases sInf_lt_iff.1 hzs with ⟨w, hw, hw_lt⟩
    rcases hw with ⟨x, hAx, rfl⟩
    have hw_sum : f x + (z : WithTopBot α) < c := by
      exact
        (WithBotTop.lt_sub_iff_add_lt
          (.inl (show (z : WithTopBot α) ≠ ⊥ by simp))
          (.inl (show (z : WithTopBot α) ≠ ⊤ by simp))).1 hw_lt
    have hz_term : (z : WithTopBot α) < ⟪y, yStar⟫ₚ - f x := by
      refine
        (WithBotTop.lt_sub_iff_add_lt
          (.inr (show (z : WithTopBot α) ≠ ⊤ by simp))
          (.inr (show (z : WithTopBot α) ≠ ⊥ by simp))).2 ?_
      simpa [c, add_comm] using hw_sum
    have hdual : (⟪y, yStar⟫ₚ : WithTopBot α) = ⟪x, Astar yStar⟫ₚ := by
      rw [← hAx]
      exact congrArg (fun r : α ↦ (r : WithTopBot α)) (hA x yStar)
    rw [hdual] at hz_term
    exact lt_of_lt_of_le hz_term <| le_iSup (fun x : E ↦ ⟪x, Astar yStar⟫ₚ - f x) x
  · refine iSup_le fun x ↦ ?_
    have hsInf : (A ◁ f) (A x) ≤ f x := by
      rw [linearImage_eq_sInf_image]
      exact sInf_le ⟨x, rfl, rfl⟩
    calc
      ⟪x, Astar yStar⟫ₚ - f x
          = ⟪A x, yStar⟫ₚ - f x := by
            simpa using
              congrArg (fun t : WithTopBot α ↦ t - f x)
                (congrArg (fun r : α ↦ (r : WithTopBot α)) (hA x yStar).symm)
      _ ≤ ⟪A x, yStar⟫ₚ - (A ◁ f) (A x) := by
            exact WithBotTop.sub_le_sub le_rfl hsInf
      _ ≤ ⨆ y : F, ⟪y, yStar⟫ₚ - (A ◁ f) y := by
            exact le_iSup (fun y : F ↦ ⟪y, yStar⟫ₚ - (A ◁ f) y) (A x)

end
