import StacksProject_2024.Chap17.Definition_17_17_3
import StacksProject_2024.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.Chap21.Lemma_21_17_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X

private instance instHasColimitSequentialComplex
    (F : ℕ ⥤ CochainComplex ModX ℤ) : HasColimit F :=
  HasColimitsOfShape.has_colimit F

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `\mathcal O_X`-modules on a ringed space and their
  stability under sequential colimits;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `AlgebraicGeometry.RingedSpace.opensRingedSite`,
  `SheafOfModules.RingedSite.sequentialColimit_isKFlat`,
  `AB5 (SheafOfModules ((RingedSpace.ringCatSheaf X)))`;
- best owner abstraction: the core owner is the predicate `K.IsKFlat` on the cochain complex
  itself. The ringed-space statement is a source-facing specialization of that owner to
  `(RingedSpace.Modules X)`, obtained by viewing `X` as its opens ringed site and reusing the
  canonical ringed-site sequential-colimit theorem;
- primitive vs derived: the primitive data are only the sequential diagram `F` and the K-flatness
  hypotheses on its stages. The sequential colimit object and its K-flatness are derived from the
  ambient colimit and owner predicate, so no extra wrapper data belongs in the public API.

Source/core/bridge triage:
- `source-facing`: Lemma 20.26.10, the ringed-space closure of K-flatness under sequential
  colimits;
- `core/canonical`: `SheafOfModules.RingedSite.sequentialColimit_isKFlat` on the opens ringed site
  of `X`, together with the owner predicate `CochainComplex.IsKFlat`;
- `bridge/view`: `AlgebraicGeometry.RingedSpace.opensRingedSite`, which identifies the ringed-space
  module category with the corresponding opens-site module category. -/

-- Proof sketch: view `X` as its opens ringed site and apply the Chapter 21 ringed-site theorem.
-- This is the same source-facing mathematics, since `RingedSpace.Modules X` is the opens-site
-- module category for `X`. The site-level theorem already packages the tensor/colimit exactness
-- argument.
-- Exactness of filtered colimits in sheaves of modules then shows that the resulting tensor
-- complex is acyclic.
/-- Lemma 20.26.10: for a system `𝒦₁^• ⟶ 𝒦₂^• ⟶ ⋯` of K-flat complexes of `𝒪_X`-modules on a
ringed space `(X, 𝒪_X)`, the sequential colimit `colim_i 𝒦_i^•` is K-flat. -/
@[stacks 06YE]
theorem sequentialColimit_isKFlat
    (F : ℕ ⥤ CochainComplex ModX ℤ)
    (hF : ∀ i, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := by
  let _ : (curriedTensor ModX).Additive := inferInstance
  let _ : ∀ ℱ : ModX, ((curriedTensor ModX).obj ℱ).Additive := inferInstance
  simpa using
    (SheafOfModules.RingedSite.sequentialColimit_isKFlat F hF)

end AlgebraicGeometry.RingedSpace
