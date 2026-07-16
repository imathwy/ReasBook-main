import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import stacks_proof.stacks_project.Chap17.Definition_17_12_1
import stacks_proof.stacks_project.Chap17.Definition_17_23_1
import stacks_proof.stacks_project.Chap17.Lemma_17_12_4
import stacks_proof.stacks_project.Chap17.Lemma_17_22_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X

open scoped AnnihilatorSheaf

/- Domain-style sampling for Lemma 17.23.4:
- primary domain: coherence of annihilator sheaves for modules on a ringed space;
- sampled owner declarations:
  `SheafOfModules.annihilator`,
  `AlgebraicGeometry.RingedSpace.internalHom_isCoherent_of_isFinitePresentation`,
  `AlgebraicGeometry.RingedSpace.isCoherent_kernel`;
- best owner abstraction:
  the ambient owner is `RingedSpace.Modules X`, and this lemma should stay a bridge/view statement:
  the source-facing annihilator sheaf is already owned by `SheafOfModules.annihilator`, while its
  coherence is derived from the canonical internal-Hom coherence theorem and the canonical closure
  of coherent sheaves under kernels;
- primitive data:
  a module sheaf `ℱ : RingedSpace.Modules X`, coherence of the structure sheaf as a module, and
  coherence of `ℱ`;
- derived API:
  the coherence statement for `annihilator ℱ`.

Source/core/bridge triage:
- `source-facing`: the annihilator sheaf `annihilator ℱ`;
- `core/canonical`: `RingedSpace.Modules X`, `selfInternalHomUnitMap ℱ`, internal Hom, and
  kernels;
- `bridge/view`: the present theorem, which identifies the source-facing annihilator with a kernel
  of coherent sheaves and deduces coherence from the upstream owner API. -/

-- Proof sketch: `Ann(ℱ)` is the kernel of the canonical map
-- `\mathcal O_X → \mathcal H\!om_{\mathcal O_X}(ℱ, ℱ)`. If `ℱ` is coherent, then it is finitely
-- presented, so Lemma `17.22.6` makes the internal endomorphism sheaf coherent; with the
-- structure sheaf coherent as well, Lemma `17.12.4` identifies the kernel as coherent.
/-- Lemma 17.23.4: if the structure sheaf `\mathcal O_X`, viewed as an `\mathcal O_X`-module, and
`\mathcal F` are coherent, then the annihilator sheaf
`\operatorname{Ann}_{\mathcal O_X}(\mathcal F)` is coherent. -/
@[stacks 0H2L]
theorem annihilator_isCoherent (ℱ : ModX)
    [(SheafOfModules.unit (RingedSpace.ringCatSheaf X)).IsCoherent] [ℱ.IsCoherent] :
    (Ann(ℱ)).IsCoherent := by
  letI : ((ihom ℱ).obj ℱ).IsCoherent :=
    RingedSpace.internalHom_isCoherent_of_isFinitePresentation ℱ ℱ
  simpa [annihilator] using
    (RingedSpace.isCoherent_kernel (selfInternalHomUnitMap ℱ) :
      (kernel (selfInternalHomUnitMap ℱ)).IsCoherent)

end SheafOfModules
