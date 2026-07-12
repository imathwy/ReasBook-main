import StacksProject_2024.Chap17.Definition_17_25_9
import StacksProject_2024.Chap29.ProjectiveSpaceBasic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

-- Semantic recall: `lean_leansearch` found only the ring-theoretic Picard-group API, while
-- local Chapter 31 precedent uses `ringedSitePicardGroup`/`Pic(X.toRingedSpace)` for scheme
-- Picard groups. Local Chapter 30 records that the project has no concrete canonical owner for
-- projective twisting sheaves yet, so this statement takes the chosen family representing
-- `\mathcal O_{\mathbf P^n_R}(m)` as an explicit input.

/-- Lemma 31.28.5 (1): let `R` be a unique factorization domain and let `n > 0`. For the standard
`Proj` model of projective space `\mathbf P^n_R`, the Picard group is isomorphic to `\mathbf Z`;
more precisely, for a chosen family of twisting sheaves
`m ↦ \mathcal O_{\mathbf P^n_R}(m)`, the isomorphism sends `m` to the Picard class of that twist.
-/
@[stacks 0BXJ]
theorem projectiveSpace_picardGroup_addEquiv_int_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (n : ℕ) (hn : 0 < n)
    [MonoidalCategory (ringedSiteModuleCategory
      (Opens.grothendieckTopology (projectiveSpace R n).toTopCat)
      (projectiveSpace R n).𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory
      (Opens.grothendieckTopology (projectiveSpace R n).toTopCat)
      (projectiveSpace R n).𝒪)]
    (twistingSheaf : ℤ → ringedSiteModuleCategory
      (Opens.grothendieckTopology (projectiveSpace R n).toTopCat)
      (projectiveSpace R n).𝒪)
    [∀ m : ℤ, Functor.IsEquivalence (tensorRight (twistingSheaf m))] :
    ∃ e : ℤ ≃+ ringedSitePicardGroup
        (Opens.grothendieckTopology (projectiveSpace R n).toTopCat)
        (projectiveSpace R n).𝒪,
      ∀ m : ℤ,
        e m = ringedSitePicardGroup.mk
          (Opens.grothendieckTopology (projectiveSpace R n).toTopCat)
          (projectiveSpace R n).𝒪 (twistingSheaf m) := sorry

/-- Lemma 31.28.5 (2): in particular, for a field `k` and `n > 0`, the Picard group of
`\mathbf P^n_k` is `\mathbf Z`; with a chosen family of twisting sheaves, the displayed
isomorphism sends `m` to the Picard class of `\mathcal O_{\mathbf P^n_k}(m)`. -/
@[stacks 0BXJ]
theorem projectiveSpace_picardGroup_addEquiv_int_of_field
    (k : Type u) [Field k] (n : ℕ) (hn : 0 < n)
    [MonoidalCategory (ringedSiteModuleCategory
      (Opens.grothendieckTopology (projectiveSpace k n).toTopCat)
      (projectiveSpace k n).𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory
      (Opens.grothendieckTopology (projectiveSpace k n).toTopCat)
      (projectiveSpace k n).𝒪)]
    (twistingSheaf : ℤ → ringedSiteModuleCategory
      (Opens.grothendieckTopology (projectiveSpace k n).toTopCat)
      (projectiveSpace k n).𝒪)
    [∀ m : ℤ, Functor.IsEquivalence (tensorRight (twistingSheaf m))] :
    ∃ e : ℤ ≃+ ringedSitePicardGroup
        (Opens.grothendieckTopology (projectiveSpace k n).toTopCat)
        (projectiveSpace k n).𝒪,
      ∀ m : ℤ,
        e m = ringedSitePicardGroup.mk
          (Opens.grothendieckTopology (projectiveSpace k n).toTopCat)
          (projectiveSpace k n).𝒪 (twistingSheaf m) := sorry

end AlgebraicGeometry
