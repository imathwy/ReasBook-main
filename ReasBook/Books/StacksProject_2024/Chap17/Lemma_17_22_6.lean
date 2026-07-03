import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import StacksProject_2024.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

universe u

/- Domain-style sampling for Lemma 17.22.6:
- primary domain: internal Hom and coherence for sheaves of modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsCoherent`,
  `AlgebraicGeometry.RingedSpace.internalHomStalkComparison_isIso_of_isFinitePresentation`,
  `CategoryTheory.Limits.kernel`;
- best owner abstraction:
  the ambient owner is `RingedSpace.Modules X`, with `IsCoherent` as the canonical public target
  property;
- primitive data:
  a finitely presented source `ℱ : RingedSpace.Modules X` and a coherent target
  `𝒢 : RingedSpace.Modules X`;
- derived API:
  the local finite-kernel presentation of `((ihom ℱ).obj 𝒢).over U` and the resulting coherence
  statement for `(ihom ℱ).obj 𝒢`.

Source/core/bridge triage:
- `source-facing`: the local kernel presentation by finite biproducts of copies of `𝒢`;
- `core/canonical`: the owner category `RingedSpace.Modules X`, the predicate `IsCoherent`, and
  categorical kernels;
- `bridge/view`: the coherence theorem deduced from the local presentation.
-/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
set_option quotPrecheck false in
local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)

-- Proof sketch: around each point, choose a local finite presentation of `ℱ` by finite free
-- `\mathcal O_U`-modules. Applying internal Hom into `𝒢|_U` turns that local presentation into a
-- left exact sequence whose first term identifies `\mathcal H\!om_{\mathcal O_U}(ℱ|_U, 𝒢|_U)` as
-- the kernel of a morphism between finite biproducts of copies of `𝒢|_U`.
/-- Lemma 17.22.6: if `\mathcal F` is finitely presented, then the internal-Hom sheaf
`\mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G)` is locally the kernel of a map
between finite direct sums of copies of `\mathcal G`, written here via the equivalent finite
biproduct presentation `∏ᶜ`. -/
theorem moduleInternalHom_locally_isKernel_of_finiteBiproductMap
    (ℱ 𝒢 : ModX) (x : X) [ℱ.IsFinitePresentation] :
    ∃ (U : Opens X) (_ : x ∈ U) (m n : ℕ)
      (φ : (∏ᶜ fun _ : Fin m ↦ 𝒢.over U) ⟶ (∏ᶜ fun _ : Fin n ↦ 𝒢.over U)),
      Nonempty ((ℱ ⟶[ModX] 𝒢).over U ≅ kernel φ) := sorry

-- Proof sketch: apply the local kernel presentation above. Finite biproducts of a coherent sheaf
-- are coherent, and Lemma `17.12.4` shows that kernels of morphisms between coherent sheaves are
-- coherent; coherence is local on the base, so the local kernel presentations glue.
/-- For a finitely presented source and coherent target, the internal-Hom sheaf is coherent. -/
theorem moduleInternalHom_isCoherent_of_isFinitePresentation
    (ℱ 𝒢 : ModX) [ℱ.IsFinitePresentation] [𝒢.IsCoherent] :
    (ℱ ⟶[ModX] 𝒢).IsCoherent := sorry

end AlgebraicGeometry.RingedSpace
