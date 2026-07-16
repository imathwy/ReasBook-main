import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_31_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

namespace SheafOfModules.RingedSite

section

open CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪

namespace CochainComplex

/-
Definition 21.17.2 also uses the companion source-facing notion that a complex of `𝒪`-modules is
termwise flat. The owner belongs on the complex itself, mirroring the Chapter 15 module-valued
owner `CochainComplex.IsTermwiseFlat`.
-/

/-- A cochain complex of `𝒪`-modules on a ringed site is termwise flat if each term `K.X n` is
flat as an `𝒪`-module. -/
class IsTermwiseFlat [MonoidalCategory Mod] (K : CochainComplex Mod ℤ) : Prop where
  isFlat : ∀ n : ℤ, IsFlat 𝒪 (K.X n)

/-- A termwise-flat complex supplies a flatness instance in each degree. -/
instance [MonoidalCategory Mod] {K : CochainComplex Mod ℤ} [hK : IsTermwiseFlat K] {n : ℤ} :
    IsFlat 𝒪 (K.X n) :=
  hK.isFlat n

/-- Unfolding ringed-site termwise flatness gives the degreewise flatness condition. -/
theorem isTermwiseFlat_iff
    [MonoidalCategory Mod]
    (K : CochainComplex Mod ℤ) :
    IsTermwiseFlat K ↔ ∀ n : ℤ, IsFlat 𝒪 (K.X n) :=
  ⟨fun hK n ↦ hK.isFlat n, fun hK ↦ ⟨hK⟩⟩

end CochainComplex

end

/- Domain-style sampling for Definition 21.17.2:
- primary domain: K-flat cochain complexes of `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.isTermwiseFlat_iff`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`;
- best owner abstraction: the Chapter 15 owner predicate `CochainComplex.IsKFlat` on
  `CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ`, together with the chapter-level owner
  `CochainComplex.IsTermwiseFlat` for the companion degreewise flatness condition;
- primitive vs derived: the primitive data are only the complex `K`, while the degreewise
  flatness and preservation of acyclic complexes under totalized tensoring are exactly the
  companion theorems `CochainComplex.isTermwiseFlat_iff` and `CochainComplex.isKFlat_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook K-flatness notion for complexes of `𝒪`-modules on a
  ringed site;
- `core/canonical`: `CochainComplex.IsTermwiseFlat` and `CochainComplex.IsKFlat`;
- `bridge/view`: `CochainComplex.isTermwiseFlat_iff` and `CochainComplex.isKFlat_iff`, the
  canonical eliminators specialized to `ringedSiteModuleCategory J 𝒪`. -/

/- Definition 21.17.2: a cochain complex `K` of `𝒪`-modules on a ringed site `(C, 𝒪)` is K-flat
if for every acyclic cochain complex `F`, the totalized tensor product `Tot(F ⊗ K)` is acyclic.
This is the canonical owner `CochainComplex.IsKFlat` specialized to
`ringedSiteModuleCategory J 𝒪`. -/
recall CochainComplex.IsKFlat

/- Totalized tensoring with `K` preserves acyclic complexes exactly when `K` is K-flat; the
canonical companion theorem is `CochainComplex.isKFlat_iff`. -/
recall CochainComplex.isKFlat_iff

end SheafOfModules.RingedSite
