import StacksProject_2024.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "single0" => DerivedCategory.singleFunctor (RingedSpace.Modules X) (0 : ℤ)

-- Proof sketch: for the forward implication, apply Lemma `20.47.9` to the degree-zero derived
-- object `ℱ[0]`, whose higher cohomology sheaves vanish, to identify `H⁰(ℱ[0]) = ℱ` as a finite
-- type module. For the converse, `ℱ[0]` is locally bounded above and its only nonzero cohomology
-- sheaf is `ℱ` in degree `0`, so Lemma `20.47.8` yields `0`-pseudo-coherence.
/-- Lemma 20.47.10 (1): a sheaf of `\mathcal O_X`-modules, viewed in `D(\mathcal O_X)` as a
complex concentrated in degree `0`, is `0`-pseudo-coherent if and only if it is of finite type. -/
theorem ringedSpaceModule_isZeroPseudoCoherent_iff_isFiniteType
    (ℱ : (RingedSpace.Modules X)) :
    IsMPseudoCoherent ((single0).obj ℱ) 0 ↔ ℱ.IsFiniteType := sorry

-- Proof sketch: for the forward implication, apply Lemma `20.47.9` with `m = -1` to `ℱ[0]`; the
-- vanishing of cohomology in degrees `> 0` identifies `H⁰(ℱ[0]) = ℱ` as finitely presented. For
-- the converse, `ℱ[0]` is locally bounded above and its only nonzero homology sheaf is `ℱ` in
-- degree `0`, so Lemma `20.47.8` with `m = -1` gives `(-1)`-pseudo-coherence.
/-- Lemma 20.47.10 (2): a sheaf of `\mathcal O_X`-modules, viewed in `D(\mathcal O_X)` as a
complex concentrated in degree `0`, is `(-1)`-pseudo-coherent if and only if it is of finite
presentation. -/
theorem ringedSpaceModule_isMinusOnePseudoCoherent_iff_isFinitePresentation
    (ℱ : (RingedSpace.Modules X)) :
    IsMPseudoCoherent ((single0).obj ℱ) (-1) ↔ ℱ.IsFinitePresentation := sorry

end AlgebraicGeometry.RingedSpace
