import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

section

universe u v

variable {DGLeft : Type u} {CompR : Type v}
variable [Category DGLeft] [Category CompR]
variable (tensorCanonical tensorSource : DGLeft ⥤ CompR) (homFromRight : CompR ⥤ DGLeft)
variable (tensorOrderIso : tensorCanonical ≅ tensorSource)
variable (adj : tensorCanonical ⊣ homFromRight)
variable (M' : DGLeft) (N : CompR)

/-
Lemma 22.13.4 is source-facing at the transported tensor-Hom adjunction layer. The current
repository has no checked DG owner for the source-order tensor `M ⊗_A M'` or the internal Hom
`Hom(M, N)`, so the canonical core owner remains `Adjunction.homEquiv`; the tensor-order
comparison is the bridge/view from the canonical tensor functor to the source-facing one.
-/
recall Adjunction.homEquiv

/- Lemma 22.13.4: the displayed source-order equivalence is the symmetric form of the transported
adjunction Hom-equivalence. -/
#check ((((adj.ofNatIsoLeft tensorOrderIso).homEquiv M' N).symm) :
  (M' ⟶ homFromRight.obj N) ≃ (tensorSource.obj M' ⟶ N))

/-- Lemma 22.13.4 companion: the inverse of the displayed source-order equivalence is the
adjunction transpose after precomposing with the tensor-order comparison. -/
recall Adjunction.homEquiv_ofNatIsoLeft_apply

/-- Companion recall: the displayed source-order equivalence itself sends a transpose back to the
corresponding source-order morphism by precomposing with the inverse tensor-order comparison. -/
recall Adjunction.homEquiv_ofNatIsoLeft_symm_apply

end
