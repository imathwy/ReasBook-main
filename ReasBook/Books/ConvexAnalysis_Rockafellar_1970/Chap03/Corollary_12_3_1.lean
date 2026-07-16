import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open scoped Rockafellar

variable {E : Type u} {L : Type v}
variable [SupSet L] [Sub L]
variable [HasPairing E E L]

/-- Corollary 12.3.1 (canonical owner form): if `f` is fixed by Fenchel biconjugation, then
invariance of `f` under a family of pairing-compatible bijections is equivalent to invariance of
its Fenchel conjugate under the same family. -/
theorem invariant_under_equiv_iff_convexConjugate_invariant_of_biconjugate
    (f : E → L) (G : Set (E ≃ E))
    (hG_pair :
      ∀ A ∈ G, ∀ x xStar : E, (⟪A x, xStar⟫ₚ : L) = ⟪x, A.symm xStar⟫ₚ)
    (hf_biconj : f⋆⋆ = f) :
    (∀ A ∈ G, f ∘ A = f) ↔
      ∀ A ∈ G, f⋆ ∘ A = f⋆ := by
  have hconj_comp (g : E → L) (A : E ≃ E)
      (hA : ∀ x xStar : E, (⟪A x, xStar⟫ₚ : L) = ⟪x, A.symm xStar⟫ₚ) :
      (g ∘ A)⋆ = g⋆ ∘ A := by
    funext xStar
    change convexConjugate (g ∘ A) xStar = convexConjugate g (A xStar)
    rw [convexConjugate_eq_iSup_pairing_sub, convexConjugate_eq_iSup_pairing_sub]
    change
      (⨆ x : E, ((⟪x, xStar⟫ₚ : L) - g (A x))) =
        ⨆ y : E, ((⟪y, A xStar⟫ₚ : L) - g y)
    calc
      (⨆ x : E, ((⟪x, xStar⟫ₚ : L) - g (A x)))
          = ⨆ x : E, ((⟪A x, A xStar⟫ₚ : L) - g (A x)) := by
            refine iSup_congr ?_
            intro x
            congr 1
            simpa using (hA x (A xStar)).symm
      _ = ⨆ y : E, ((⟪y, A xStar⟫ₚ : L) - g y) := by
            simpa using
              (A.surjective.iSup_comp
                (g := fun y : E ↦ ((⟪y, A xStar⟫ₚ : L) - g y)))
  constructor
  · intro hf_invariant A hA
    calc
      f⋆ ∘ A = (f ∘ A)⋆ := (hconj_comp f A (hG_pair A hA)).symm
      _ = f⋆ := by rw [hf_invariant A hA]
  · intro hconj_invariant A hA
    have hbiconj_invariant : f⋆⋆ ∘ A = f⋆⋆ := by
      calc
        f⋆⋆ ∘ A = (f⋆ ∘ A)⋆ := (hconj_comp f⋆ A (hG_pair A hA)).symm
        _ = f⋆⋆ := by
          rw [hconj_invariant A hA]
          rfl
    calc
      f ∘ A = f⋆⋆ ∘ A := by
        simpa using congrArg (fun g : E → L ↦ g ∘ A) hf_biconj.symm
      _ = f⋆⋆ := hbiconj_invariant
      _ = f := hf_biconj

end
