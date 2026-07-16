import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.support` and
`Scheme.IdealSheafData.mkOfMemSupportIff`; local Chapter 29 precedent represents closed
subschemes by `X.IdealSheafData` and the underlying module support by `moduleSupport`. -/

/-- Definition 29.5.5: for a finite type quasi-coherent `\mathcal O_X`-module `ℱ`, an
`IdealSheafData` closed subscheme of `X` is the scheme theoretic support of `ℱ` when its affine
open defining ideal is the annihilator of the corresponding module of sections, equivalently the
closed subscheme constructed in Lemma 29.5.4. -/
@[stacks 05JV]
def IsSchemeTheoreticSupport (I : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, I.ideal U = Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1))

/-- The affine-open annihilator characterization of the scheme theoretic support. -/
theorem isSchemeTheoreticSupport_iff (I : X.IdealSheafData) :
    IsSchemeTheoreticSupport ℱ I ↔
      ∀ U : X.affineOpens, I.ideal U = Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1)) := sorry

/-- The underlying closed set of a scheme theoretic support is the ordinary support of the
module. -/
theorem moduleSupport_eq_of_isSchemeTheoreticSupport
    (I : X.IdealSheafData) (hI : IsSchemeTheoreticSupport ℱ I) :
    moduleSupport ℱ = (I.support : Set X) := sorry

end AlgebraicGeometry.Scheme.Modules
