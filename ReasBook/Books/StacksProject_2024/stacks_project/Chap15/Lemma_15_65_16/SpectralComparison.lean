import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_9

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory
namespace Lemma_15_65_16

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Lemma 15.65.16: fixing the second index of the `E₁` page produces an ordinary
cochain complex in the first index. -/
def associatedPageOneComplex
    (E : CohomologicalSpectralSequence 𝒜 0) (q : ℤ) : CochainComplex 𝒜 ℤ where
  X p := (E.page 1).X (p, q)
  d p p' := (E.page 1).d (p, q) (p', q)
  shape p p' hpp' := by
    -- Proof comment: fixing `q` turns the ambient bidegree shape into the ordinary cochain shape.
    have hpq :
        ¬ (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel (p, q) (p', q) := by
      simpa [ComplexShape.up'] using hpp'
    exact (E.page 1).shape (p, q) (p', q) hpq
  d_comp_d' p p' p'' hpp' hp'p'' := by
    -- Proof comment: square-zero is inherited verbatim from the ambient `E₁` page.
    exact (E.page 1).d_comp_d (p, q) (p', q) (p'', q)

/-- Helper for Lemma 15.65.16: the short-complex view of the fixed-`q` `E₁` slice agrees with
the ambient short complex at bidegree `(p, q)`. -/
noncomputable def associatedPageOneComplexScIso
    (E : CohomologicalSpectralSequence 𝒜 0) (p q : ℤ) :
    (associatedPageOneComplex E q).sc' (p - 1) p (p + 1) ≅
      (E.page 1).sc' (p - 1, q) (p, q) (p + 1, q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [associatedPageOneComplex])
    (by simp [associatedPageOneComplex])

/-- Helper for Lemma 15.65.16: the `p`-th homology of the fixed-`q` slice is the ambient page-one
homology object at bidegree `(p, q)`. -/
noncomputable def associatedPageOneComplex_homologyIso
    (E : CohomologicalSpectralSequence 𝒜 0) (p q : ℤ) :
    (associatedPageOneComplex E q).homology p ≅ (E.page 1).homology (p, q) :=
  let hprevSlice : (ComplexShape.up ℤ).prev p = p - 1 :=
    ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hnextSlice : (ComplexShape.up ℤ).next p = p + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hprevPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).prev (p, q) = (p - 1, q) :=
    ComplexShape.prev_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  let hnextPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).next (p, q) = (p + 1, q) :=
    ComplexShape.next_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  -- Proof comment: the fixed-`q` slice keeps exactly the ambient `E₁` differential data.
  (associatedPageOneComplex E q).homologyIsoSc' (p - 1) p (p + 1) hprevSlice hnextSlice ≪≫
    ShortComplex.homologyMapIso (associatedPageOneComplexScIso E p q) ≪≫
    ((E.page 1).homologyIsoSc' (p - 1, q) (p, q) (p + 1, q) hprevPage hnextPage).symm

/-- Helper for Lemma 15.65.16: any fixed-`q` comparison of the `E₁` slice with an ordinary
cochain complex yields the corresponding `E₂`-page identification by taking `p`-th homology. -/
theorem associated_pageTwo_iso_of_pageOne_complex_iso_local
    (E : CohomologicalSpectralSequence 𝒜 0) (p q : ℤ)
    (C : CochainComplex 𝒜 ℤ)
    (e : associatedPageOneComplex E q ≅ C) :
    Nonempty ((E.page 2).X (p, q) ≅ C.homology p) := by
  refine ⟨?_⟩
  -- Proof comment: rewrite the ambient `E₂` term as page-one homology and transport along the
  -- fixed-`q` comparison and the chosen cochain-complex isomorphism.
  exact
    (E.iso 1 2 (p, q)).symm ≪≫
      (associatedPageOneComplex_homologyIso E p q).symm ≪≫
        HomologicalComplex.homologyMapIso e p

end Lemma_15_65_16
end CategoryTheory
