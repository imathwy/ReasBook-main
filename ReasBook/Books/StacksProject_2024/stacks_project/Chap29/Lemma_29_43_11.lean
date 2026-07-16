import StacksProject_2024.stacks_project.Chap29.Lemma_29_43_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
`lean_leansearch` recalled the canonical scheme-morphism notions `IsOpenImmersion` and
`IsImmersion`, but no upstream scheme-side owner for H-quasi-projective morphisms. Nearby
Chapter 29 files provide the local owners `HQuasiProjective` and `HProjective`, so the source
factorization is stated directly in that API. The Stacks tag evidence is consistent: item tag
`01WA` matches the source URL `/tag/01WA`. -/

/-- Lemma 29.43.11: every H-quasi-projective morphism factors as an open immersion followed by an
H-projective morphism. -/
@[stacks 01WA]
theorem HQuasiProjective.exists_factor_openImmersion_hProjective
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : HQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (g : X' ⟶ S)
      (_ : IsOpenImmersion i) (_ : HProjective g),
        i ≫ g = f := sorry

end AlgebraicGeometry
