import StacksProject_2024.Chap20.Lemma_20_26_12
import StacksProject_2024.Chap21.Lemma_21_17_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

local notation "ModX" => Modules X
local notation "SiteTermwiseFlat" =>
  @IsTermwiseFlat _ _ (Opens.grothendieckTopology X) _ X.sheaf _

/- Domain-style sampling for Lemma 20.26.9:
- primary domain: K-flat cochain complexes of `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `SheafOfModules.IsFlat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.isKFlat_of_boundedAbove_of_flat`,
  `CochainComplex.minus`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`;
- best owner abstraction: the Chapter 21 owner theorem
  `SheafOfModules.RingedSite.isKFlat_of_boundedAbove_of_flat` on the opens site of `X`; the
  present file should only provide the ringed-space specialization, converting the source-facing
  degreewise flatness hypotheses to the canonical opens-site owner inside the proof;
- primitive vs derived: the primitive data are the complex `K`, its bounded-above hypothesis, and
  termwise ringed-space flatness; K-flatness is derived from the canonical ringed-site owner.

Source/core/bridge triage:
- `source-facing`: the bounded-above flat criterion for complexes of `𝒪_X`-modules;
- `core/canonical`: `SheafOfModules.RingedSite.isKFlat_of_boundedAbove_of_flat`,
  `CochainComplex.minus`, and `CochainComplex.IsKFlat`;
- `bridge/view`: the chapter-level bridge `CochainComplex.isTermwiseFlat_iff`, relating
  ringed-space degreewise flatness to the canonical owner `CochainComplex.IsTermwiseFlat`. -/

/-- Companion to Lemma 20.26.9: the bounded-above criterion can be stated directly using the
canonical opens-site termwise-flat owner `CochainComplex.IsTermwiseFlat`. -/
theorem isKFlat_of_boundedAbove_of_termwiseFlat
    (K : CochainComplex ModX ℤ)
    (hbounded : CochainComplex.minus ModX K)
    (hFlat : SiteTermwiseFlat K) :
    K.IsKFlat := by
  simpa using isKFlat_of_boundedAbove_of_flat K hbounded hFlat

/-- Lemma 20.26.9: a bounded above complex of flat `𝒪_X`-modules on a ringed space
`(X, 𝒪_X)` is K-flat. -/
@[stacks 06YD]
theorem isKFlat_of_boundedAbove_of_flat
    (K : CochainComplex ModX ℤ)
    (hbounded : CochainComplex.minus ModX K)
    (hFlat : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n)) :
    K.IsKFlat := by
  have hTermwise : SiteTermwiseFlat K := (CochainComplex.isTermwiseFlat_iff K).2 hFlat
  exact isKFlat_of_boundedAbove_of_termwiseFlat K hbounded hTermwise

end AlgebraicGeometry.RingedSpace
