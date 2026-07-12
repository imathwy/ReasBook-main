import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the canonical owners
-- `Scheme.Modules.pushforward`, `SheafOfModules.IsQuasicoherent`, and `QuasiCompact`;
-- nearby Chapter 30/31 precedent uses `[QuasiCompact f] [QuasiSeparated f]` and
-- `((Scheme.Modules.pushforward f).obj ℱ).IsQuasicoherent`.

/-- Lemma 26.24.1: let `f : X ⟶ S` be a morphism of schemes. If `f` is quasi-compact
and quasi-separated, then `f_*` sends quasi-coherent `\mathcal O_X`-modules to
quasi-coherent `\mathcal O_S`-modules. -/
@[stacks 01LC]
theorem pushforward_obj_isQuasicoherent_of_quasiCompact_quasiSeparated
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (((Modules.pushforward f).obj ℱ) : S.Modules).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme
