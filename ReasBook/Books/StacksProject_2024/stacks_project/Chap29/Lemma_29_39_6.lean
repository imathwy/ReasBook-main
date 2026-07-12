import Mathlib
import StacksProject_2024.Chap29.Lemma_29_38_7
import StacksProject_2024.Chap29.Definition_29_43_1
import StacksProject_2024.Chap29.Lemma_29_39_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall / owner check:
-- `lean_leansearch` surfaced only generic projective-spectrum/open-cover API, while local Chapter
-- 29 precedent fixes relative very ampleness through `RelativelyVeryAmple` and
-- `RelativelyVeryAmplePresentation`. Lemma 29.39.1 supplies the affine-base projective-space
-- presentation, and Lemma 29.38.7 supplies locality on the base, so this item is recorded as the
-- source equivalence between relative very ampleness and an open-cover family of relative
-- projective-space presentations.

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- Lemma 29.39.6: let `f : X ⟶ S` be a finite-type morphism of schemes and let
`\mathcal L` be an invertible sheaf on `X`. Then `\mathcal L` is `f`-relatively very ample if and
only if there is an open cover `S = ⋃ V_j` such that, for every `j`, the inverse-image open
`X_j = f^{-1}(V_j)` admits an immersion over `V_j` into projective space
`\mathbf P^{n_j}_{V_j}` and the restriction of `\mathcal L` to `X_j` is isomorphic to the
pullback of the tautological sheaf `\mathcal O(1)`. -/
@[stacks 02NQ]
theorem relativelyVeryAmple_iff_exists_openCover_freeProjectiveBundlePresentation
    [Scheme.Modules.Invertible L] [f.FiniteType] :
    RelativelyVeryAmple f L ↔
      ∃ (ι : Type u) (V : ι → S.Opens), TopologicalSpace.IsOpenCover V ∧
        ∀ j : ι,
          ∃ (n : ℕ) (P : ProjectiveSpaceOver (V j).toScheme n)
            (i : (f ⁻¹ᵁ V j).toScheme ⟶ P.scheme)
            (hInv : Scheme.Modules.Invertible (restrictToBasePreimage f L (V j))),
            @RelativelyVeryAmplePresentation (f ⁻¹ᵁ V j).toScheme (V j).toScheme P.scheme
              (f ∣_ V j) (restrictToBasePreimage f L (V j)) hInv P.hom
              (standardProjectiveBundleModule (V j).toScheme n) P.isProjectiveBundle i := sorry

end

end AlgebraicGeometry
