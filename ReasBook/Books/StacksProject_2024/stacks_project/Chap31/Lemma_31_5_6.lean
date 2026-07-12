import Mathlib
import StacksProject_2024.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` only surfaced general sheaf/open-restriction owners, so the
-- source-facing Chapter 31 statement is recorded against the verified local owner `ℱ.weakAss` and
-- the canonical presheaf restriction map on sections from `⊤` to the chosen open `U`.

/-- Lemma 31.5.6: let `X` be a scheme. Let `\mathcal F` be a quasi-coherent `\mathcal O_X`-module.
If `U ⊆ X` is open and `\mathrm{WeakAss}(\mathcal F) ⊆ U`, then the restriction map
`\Gamma(X, \mathcal F) \to \Gamma(U, \mathcal F)` is injective. -/
@[stacks 0B3M]
theorem injective_restrictionToOpen_of_weakAss_subset
    (U : X.Opens) (hU : ℱ.weakAss ⊆ (U : Set X)) :
    Function.Injective
      (ℱ.val.map (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op) := sorry

end AlgebraicGeometry.Scheme.Modules
