import Mathlib
import StacksProject_2024.Chap31.Lemma_31_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

-- Semantic recall: `lean_leansearch` highlighted Mathlib's localization theorem
-- `IsLocalizedModule.isTorsionFree`; the local Chapter 31 owner is `Scheme.Modules.IsTorsionFree`,
-- and the source-facing bridge here is the corresponding stalkwise condition.

/-- Lemma 31.11.8: let `X` be an integral scheme and let `\mathcal F` be a quasi-coherent
`\mathcal O_X`-module. Then `\mathcal F` is torsion free if and only if every stalk
`\mathcal F_x` is a torsion free `\mathcal O_{X, x}`-module. -/
@[stacks 0AXW]
theorem isTorsionFree_iff_stalkwise
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsTorsionFree ℱ ↔
      ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x) (stalkModuleCat ℱ x) := sorry

namespace IsTorsionFree

/-- A torsion-free quasi-coherent `\mathcal O_X`-module on an integral scheme has torsion-free
stalks. -/
theorem stalk {ℱ : X.Modules} [ℱ.IsQuasicoherent]
    (hℱ : IsTorsionFree ℱ) (x : X) :
    Module.IsTorsionFree (X.presheaf.stalk x) (stalkModuleCat ℱ x) :=
  (isTorsionFree_iff_stalkwise ℱ).1 hℱ x

/-- Stalks of a torsion-free quasi-coherent `\mathcal O_X`-module inherit the canonical
ring-theoretic torsion-free instance. -/
instance instModuleIsTorsionFree_stalkModuleCat
    {ℱ : X.Modules} [ℱ.IsQuasicoherent] [hℱ : IsTorsionFree ℱ] (x : X) :
    Module.IsTorsionFree (X.presheaf.stalk x) (stalkModuleCat ℱ x) :=
  hℱ.stalk x

end IsTorsionFree

/-- Companion bridge: if every stalk of a quasi-coherent `\mathcal O_X`-module on an integral
scheme is torsion free, then the module is torsion free. -/
theorem isTorsionFree_of_stalkwise
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hℱ : ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x) (stalkModuleCat ℱ x)) :
    IsTorsionFree ℱ :=
  (isTorsionFree_iff_stalkwise ℱ).2 hℱ

end AlgebraicGeometry.Scheme.Modules
