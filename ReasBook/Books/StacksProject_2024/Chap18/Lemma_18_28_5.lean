import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/- Domain-style sampling for Lemma 18.28.5:
- primary domain: closure of flat module objects under filtered colimits and coproducts in
  presheaf and sheaf module categories;
- sampled owner declarations:
  `Module.Flat`,
  `PresheafOfModules.IsFlat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.isFlat_colimit_of_isFiltered`;
- best owner abstraction: flatness is owned by the typeclasses
  `PresheafOfModules.IsFlat` and `SheafOfModules.RingedSite.IsFlat`, so stagewise flatness should
  be supplied by instances rather than explicit functions;
- primitive data: a filtered or discrete diagram of module objects;
- derived API: the colimit-closure lemmas below.

Source/core/bridge triage:
- `source-facing`: flatness is preserved by filtered colimits and direct sums;
- `core/canonical`: the flatness owner typeclasses on the ambient module categories;
- `bridge/view`: the colimit constructions computing the direct sums and filtered colimits.

This file should therefore keep the source-facing closure statements while reusing the canonical
instance-driven flatness owners already used upstream, rather than carrying parallel explicit
stagewise flatness data.
-/

-- Proof sketch: evaluate the filtered colimit presheaf at each object of `C`. The resulting
-- filtered colimit of flat modules is flat by the module-theoretic criterion from
-- Lemma `10.8.8`, and then Lemma `18.28.2` promotes these objectwise flatness statements back to
-- flatness of the colimit presheaf.
/-- Lemma 18.28.5 (1): a filtered colimit of flat presheaves of modules over a presheaf of
commutative rings is flat. -/
theorem isFlat_colimit_of_isFiltered {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ PresheafOfModules (ringPresheaf 𝒪))
    [∀ j, IsFlat (F.obj j)] :
    IsFlat (colimit F) := sorry

-- Proof sketch: a direct sum is the coproduct of the corresponding discrete diagram. Apply the
-- filtered-colimit argument objectwise to the discrete diagram, using that direct sums of flat
-- modules are flat, and conclude by Lemma `18.28.2`.
/-- Lemma 18.28.5 (2): a direct sum of flat presheaves of modules over a presheaf of commutative
rings is flat. -/
theorem isFlat_coproduct {I : Type u}
    (F : Discrete I ⥤ PresheafOfModules (ringPresheaf 𝒪))
    [∀ i, IsFlat (F.obj ⟨i⟩)] :
    IsFlat (colimit F) := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

open PresheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

-- Proof sketch: pass to underlying presheaves, where filtered colimits are computed objectwise
-- and preserve flatness by part `(1)`. Then use the canonical ringed-site flatness owner
-- `IsFlat` for an arbitrary sheaf of commutative rings `𝒪`.
/-- Lemma 18.28.5 (3): a filtered colimit of flat sheaves of modules over a sheaf of
commutative rings `\mathcal O` on a site is flat. -/
theorem isFlat_colimit_of_isFiltered {K : Type u} [Category.{u} K] [IsFiltered K]
    {𝒪 : Sheaf J CommRingCat.{u}} (F : K ⥤ SheafOfModules (ringSheaf J 𝒪))
    [∀ k, IsFlat 𝒪 (F.obj k)] :
    IsFlat 𝒪 (colimit F) :=
  sorry

-- Proof sketch: a direct sum is the coproduct of a discrete diagram. Apply the sheaf filtered
-- colimit statement to that diagram, equivalently reason on underlying presheaves and use the
-- direct-sum preservation of flatness from part `(2)`.
/-- Lemma 18.28.5 (4): a direct sum of flat sheaves of modules over a sheaf of commutative rings
`\mathcal O` on a site is flat. -/
theorem isFlat_coproduct {I : Type u}
    {𝒪 : Sheaf J CommRingCat.{u}} (F : Discrete I ⥤ SheafOfModules (ringSheaf J 𝒪))
    [∀ i, IsFlat 𝒪 (F.obj ⟨i⟩)] :
    IsFlat 𝒪 (colimit F) :=
  sorry

end SheafOfModules.RingedSite
