import StacksProject_2024.Chap21.Definition_21_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 21.17.16:
- primary domain: K-flat acyclic cochain complexes of `𝒪`-modules on a ringed site and
  flatness of their cycles;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsKFlat`,
  `HomologicalComplex.cycles`,
  `ShortComplex.cyclesIsoKernel`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.isFlat_iff_isZero_tor_one`;
- best owner abstraction: the ambient module category is already owned by
  `ringedSiteModuleCategory J 𝒪`, and K-flatness is already owned by the predicate `K.IsKFlat` on
  `CochainComplex Mod ℤ`; for “the kernel of the differential in degree `n`”, the canonical owner
  is `K.cycles n`, with the explicit kernel object treated as a bridge/view via the standard
  cycles-to-kernel comparison;
- primitive vs derived: the primitive data are the complex `K`, the acyclicity and K-flatness
  hypotheses, and the chapter owner `K.IsTermwiseFlat`, while flatness of `K.cycles n` is the
  derived conclusion and the raw-kernel formulation is only a bridge/view consequence.

Source/core/bridge triage:
- `source-facing`: flatness of the cycle object in degree `n`;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`, `K.IsKFlat`, `K.cycles n`, and
  `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the standard comparison from `K.cycles n` to the categorical kernel of
  `K.dFrom n`. -/

-- Proof sketch: let `ℱ := K.cycles n`. Because `K` is acyclic, the brutal truncation
-- `⋯ ⟶ K^{n-2} ⟶ K^{n-1} ⟶ ℱ ⟶ 0` is a flat resolution of `ℱ`. Lemma `21.17.8` makes that
-- bounded-above termwise-flat complex K-flat, so it computes `Tor[1](ℱ, 𝒢)` for every module
-- `𝒢`. Since `K` itself is K-flat and acyclic, derived tensoring `K` with `𝒢` is zero, forcing
-- `Tor[1](ℱ, 𝒢)` to vanish; then Lemma `21.17.15` yields flatness of `ℱ`.
/-- Lemma 21.17.16: if `K` is a K-flat acyclic cochain complex of flat `𝒪`-modules on a ringed
site, then its cycles object in degree `n` is a flat `𝒪`-module. -/
@[stacks 0G7C]
theorem isFlat_cycles_of_isKFlat_of_acyclic
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    (K : CochainComplex (Mod(𝒪)) ℤ) (n : ℤ)
    (hKFlat : K.IsKFlat) (hAcyclic : K.Acyclic)
    (hFlat : IsTermwiseFlat K) :
    IsFlat 𝒪 (K.cycles n) := sorry

/-- The source-text kernel formulation of Lemma 21.17.16 follows from the canonical cycles
statement by the standard cycles-to-kernel comparison. -/
theorem isFlat_kernel_dFrom_of_isKFlat_of_acyclic
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    (K : CochainComplex (Mod(𝒪)) ℤ) (n : ℤ)
    (hKFlat : K.IsKFlat) (hAcyclic : K.Acyclic)
    (hFlat : IsTermwiseFlat K) :
    IsFlat 𝒪 (kernel (K.dFrom n)) := by
  sorry

end SheafOfModules.RingedSite
