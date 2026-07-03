import Mathlib
import stacks_project.Chap17.Definition_17_17_1
import stacks_project.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory HomologicalComplex

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

variable {K L N : CochainComplex (RingedSpace.Modules X) ℤ}

/-- A factorization of `a` up to homotopy through a quasi-isomorphism `c : \mathcal N^\bullet ⟶
\mathcal L^\bullet` with K-flat source `\mathcal N^\bullet`. -/
class IsKFlatFactorizationUpToHomotopy
    (a : K ⟶ L) (b : K ⟶ N) (c : N ⟶ L) : Prop where
  /-- The morphism `a` is homotopic to the composite `b ≫ c`. -/
  homotopy : Nonempty (Homotopy a (b ≫ c))
  /-- The intermediate complex is K-flat. -/
  isKFlat : IsKFlat N
  /-- The comparison map to `\mathcal L^\bullet` is a quasi-isomorphism. -/
  quasiIso : QuasiIso c

/-- A K-flat factorization up to homotopy whose intermediate complex has flat terms. -/
class IsTermwiseFlatKFlatFactorizationUpToHomotopy
    (a : K ⟶ L) (b : K ⟶ N) (c : N ⟶ L) : Prop
    extends IsKFlatFactorizationUpToHomotopy a b c where
  /-- Every term of the intermediate complex is a flat `\mathcal O_X`-module. -/
  term_flat : ∀ n : ℤ, SheafOfModules.IsFlat (N.X n)

-- Proof sketch: choose a distinguished triangle for `a` in the homotopy category, resolve its
-- cone by a quasi-isomorphic K-flat complex with flat terms using Lemma `20.26.12`, and fit the
-- composite to `K⟦1⟧` into a distinguished triangle `K ⟶ N ⟶ M ⟶ K⟦1⟧`. Lemma `20.26.6` gives
-- that `N` is K-flat; a morphism of distinguished triangles yields `c : N ⟶ L`, and
-- two-out-of-three shows `c` is a quasi-isomorphism while the triangle comparison identifies `a`
-- with `b ≫ c` up to homotopy.
/-- Lemma 20.26.17: if `a : \mathcal K^\bullet ⟶ \mathcal L^\bullet` is a morphism of cochain
complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)` and
`\mathcal K^\bullet` is K-flat, then `a` factors up to homotopy through a quasi-isomorphism
`c : \mathcal N^\bullet ⟶ \mathcal L^\bullet` with K-flat source `\mathcal N^\bullet`. -/
theorem exists_homotopy_factorization_through_kFlat_quasiIso
    (a : K ⟶ L) (hK : IsKFlat K) :
    ∃ (N : CochainComplex (RingedSpace.Modules X) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      IsKFlatFactorizationUpToHomotopy a b c := sorry

-- Proof sketch: carry out the construction of the main factorization theorem using the split-form
-- distinguished triangle from Lemma `13.10.7`, so that each term of `N` is isomorphic to
-- `M.X n ⊞ K.X n` for the chosen K-flat replacement `M` of the cone. Since `M` has flat terms by
-- Lemma `20.26.12` and `K` is assumed termwise flat, the terms of `N` are flat as well.
/-- If the source complex has flat terms, the K-flat factorization can be chosen with flat terms as
well. -/
theorem exists_homotopy_factorization_through_kFlat_quasiIso_of_termwiseFlat
    (a : K ⟶ L) (hK : IsKFlat K)
    (hFlatK : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n)) :
    ∃ (N : CochainComplex (RingedSpace.Modules X) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      IsTermwiseFlatKFlatFactorizationUpToHomotopy a b c := sorry

end AlgebraicGeometry.RingedSpace
