import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory Opposite Limits

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

-- Proof sketch: evaluate `tensorLeft ℱ` at each object `U`. The resulting functor on
-- `ModuleCat (𝒪.obj (op U))` is tensoring with the flat module `ℱ.obj (op U)`, so it preserves
-- finite limits by `Module.Flat.iff_preservesFiniteLimits_tensorLeft`. Since tensoring with `ℱ`
-- preserves all colimits by Lemma `18.27.7`, these objectwise left-exactness statements assemble
-- into the exact tensor-functor owner `PresheafOfModules.IsFlat`.
/-- Lemma 18.28.2: if each section module `\mathcal F(U)` is flat over `\mathcal O(U)`, then the
presheaf `\mathcal F` is flat. -/
theorem isFlat_of_flat_obj
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ U : C, Module.Flat (𝒪.obj (op U)) (ℱ.obj (op U))) :
    IsFlat ℱ := sorry

end PresheafOfModules
