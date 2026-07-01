import Mathlib
import stacks_project.Chap17.Definition_17_25_9
import stacks_project.Chap18.Definition_18_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped RingedSpacePicard

noncomputable section

namespace AlgebraicGeometry.RingedSpace

-- Proof sketch: associate to an invertible `\mathcal O_X`-module its sheaf of local generators,
-- show that this is an `\mathcal O_X^*`-torsor, and use Lemma `20.4.3` to identify torsor classes
-- with `H^1(X, \mathcal O_X^*)`; injectivity and surjectivity follow from the trivial-torsor
-- criterion of Lemma `20.4.2` and the standard reconstruction of an invertible module from a
-- torsor.
/-- Lemma 20.6.1: if all stalks of the structure sheaf of a ringed space are local rings, then
there is a canonical isomorphism of abelian groups between the first cohomology of the units sheaf
`\mathcal O_X^*` and the Picard group of `X`. -/
theorem unitsSheaf_H1_equiv_picardGroup
    (X : RingedSpace)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x))
    [MonoidalCategory (Modules X)] [SymmetricCategory (Modules X)]
    [MonoidalClosed (Modules X)] :
    Nonempty (((ringedSiteUnitsAddSheaf X.sheaf).H 1) ≃+ Pic(X)) := sorry

end AlgebraicGeometry.RingedSpace
