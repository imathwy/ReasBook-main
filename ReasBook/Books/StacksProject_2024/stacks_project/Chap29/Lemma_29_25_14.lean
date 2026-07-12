import Mathlib
import StacksProject_2024.Chap10.Lemma_10_40_4
import StacksProject_2024.Chap29.Lemma_29_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.pullback`,
`Scheme.IdealSheafData.support_comap`, and the flatness owner `AlgebraicGeometry.Flat`;
local Chapter 29 support files represent scheme-theoretic support by affine-open annihilator
ideals on `Scheme.IdealSheafData`, matching Lemma 29.5.4. -/

/-- Lemma 29.25.14: Let `f : Y ⟶ X` be a morphism of schemes. Let `ℱ` be a finite type
quasi-coherent `\mathcal O_X`-module with scheme theoretic support `Z ⊆ X`. If `f` is flat,
then `f^{-1}(Z)` is the scheme theoretic support of `f^*ℱ`. -/
@[stacks 07T9]
theorem schemeTheoreticSupport_pullback_ideal_eq_annihilator_of_flat
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens,
      I.ideal U = Module.annihilator Γ(X, U.1) (Γ(ℱ, U.1)))
    (V : Y.affineOpens) :
    (I.comap f).ideal V =
      Module.annihilator Γ(Y, V.1) (Γ((Scheme.Modules.pullback f).obj ℱ, V.1)) := sorry

end AlgebraicGeometry.Scheme.Modules
