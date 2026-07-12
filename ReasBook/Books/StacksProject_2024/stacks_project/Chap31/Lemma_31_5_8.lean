import StacksProject_2024.Chap10.Lemma_10_66_9
import StacksProject_2024.Chap31.Definition_31_2_1
import StacksProject_2024.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.IsLocallyNoetherian`; the local
-- Chapter 31 owners are `Scheme.Modules.associatedPoints` and `Scheme.Modules.weakAss`, and the
-- stalkwise algebra input is Chapter 10's
-- `isAssociatedPrime_iff_isWeaklyAssociatedToModule_of_fg`.

/-- Lemma 31.5.8 (1): if the maximal ideal `\mathfrak m_x` of the stalk `\mathcal O_{X, x}` is
finitely generated, then a point `x` is associated to a quasi-coherent `\mathcal O_X`-module
`\mathcal F` if and only if it is weakly associated to `\mathcal F`. -/
theorem mem_associatedPoints_iff_mem_weakAss_of_stalk_maximalIdeal_fg
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x : X)
    (hfg : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).FG) :
    x ∈ associatedPoints ℱ ↔ x ∈ weakAss ℱ := by
  rw [mem_associatedPoints_iff, mem_associatedPrimesOfModule_iff, mem_weakAss_iff]
  exact
    isAssociatedToModule_iff_isWeaklyAssociatedToModule_of_fg
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) hfg

/-- Lemma 31.5.8 (2): on a locally Noetherian scheme, the associated points and weakly associated
points of a quasi-coherent `\mathcal O_X`-module coincide. -/
theorem associatedPoints_eq_weakAss_of_isLocallyNoetherian
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [IsLocallyNoetherian X] :
    associatedPoints ℱ = weakAss ℱ := by
  ext x
  exact
    mem_associatedPoints_iff_mem_weakAss_of_stalk_maximalIdeal_fg ℱ x
      (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))

end AlgebraicGeometry.Scheme.Modules
