import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Definition_18_33_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PresheafOfModules
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

namespace SheafOfModules.RingedSite

variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable (φ : O₁ ⟶ O₂)

/- Domain-style sampling for Lemma 18.33.2:
- primary domain: sheafified relative differentials of a morphism of sheaves of commutative rings
  on a general site, together with their universal derivation;
- sampled owner declarations:
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `PresheafOfModules.DifferentialsConstruction.derivation'`,
  `PresheafOfModules.DifferentialsConstruction.isUniversal'`,
  `ringSheaf`,
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`;
- best owner abstraction: the source-facing sheaf owner `relativeDifferentials` with textbook
  notation `Ω(φ)`, obtained by sheafifying the canonical presheaf owner
  `relativeDifferentials' φ.hom`;
- primitive data: the underlying `RingCat`-valued sheaf `ringSheaf J O₂`, the sheaf
  `relativeDifferentials φ`, and its universal derivation `relativeDifferential φ`;
- derived API: the descended universal map `relativeDifferentialDesc`, its factorization and
  injectivity lemmas, the representing theorem
  `relativeDifferentials_representsDerivations`, and the predicate
  `IsUniversalRelativeDifferentials`.

Source/core/bridge triage:
- `core/canonical`: the presheaf owner
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`;
- `source-facing`: the site-level sheafified owner `relativeDifferentials` written as `Ω(φ)`;
- `bridge/view`: the sheafification-adjunction descent API carrying the presheaf universal
  derivation to sheaf targets.

This file is therefore the owner for the generic-site construction; downstream files should reuse
`relativeDifferentials`, `relativeDifferential`, and `Ω(φ)` rather than reintroducing parallel
site-specific wrapper names. -/

/-- The sheaf of relative differentials of `O₂` over `O₁`, obtained by sheafifying the canonical
presheaf of relative differentials. -/
abbrev relativeDifferentials :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J O₂).obj)).obj
    (relativeDifferentials' φ.hom)

@[inherit_doc relativeDifferentials]
scoped[SheafOfModules.RingedSite] notation:max "Ω(" φ ")" =>
  SheafOfModules.RingedSite.relativeDifferentials φ

open scoped SheafOfModules.RingedSite

/-- The sheaf of relative differentials is the sheafification of the presheaf-level relative
differentials construction. -/
theorem relativeDifferentials_def :
    Ω(φ) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf J O₂).obj)).obj
        (relativeDifferentials' φ.hom) :=
  rfl

/-- The canonical `O₁`-derivation from `O₂` to the sheaf of relative differentials on the site. -/
def relativeDifferential :
    Der[φ ; Ω(φ)] :=
  (derivation' φ.hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O₂).obj)).unit.app (relativeDifferentials' φ.hom))

/-- The morphism induced from a target derivation by the universal property of relative
differentials. -/
def relativeDifferentialDesc
    {F : SheafOfModules (ringSheaf J O₂)} (D : Der[φ ; F]) :
    Ω(φ) ⟶ F :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).homEquiv
      (relativeDifferentials' φ.hom) F).symm
    ((isUniversal' φ.hom).desc D)

-- Proof sketch: `relativeDifferentialDesc` is obtained by transporting the presheaf-level
-- universal morphism across the sheafification adjunction, so the factorization identity is the
-- adjoint form of `(isUniversal' φ.hom).fac`.
/-- The descended morphism factors the target derivation through the universal derivation. -/
theorem relativeDifferentialDesc_fac
    {F : SheafOfModules (ringSheaf J O₂)} (D : Der[φ ; F]) :
    RelativeDerivation.postcomp (relativeDifferential φ)
      (relativeDifferentialDesc φ D) = D :=
  sorry

-- Proof sketch: uniqueness is inherited from the presheaf-level universal property after applying
-- the sheafification adjunction equivalence.
/-- A morphism out of `Ω(φ)` is determined by its postcomposition with the universal derivation. -/
theorem relativeDifferential_postcomp_injective
    {F : SheafOfModules (ringSheaf J O₂)} ⦃α β : Ω(φ) ⟶ F⦄
    (h : RelativeDerivation.postcomp (relativeDifferential φ) α =
      RelativeDerivation.postcomp (relativeDifferential φ) β) :
    α = β :=
  sorry

/-- The universal property for a chosen sheaf of relative differentials on a site: every relative
derivation factors uniquely through the chosen universal derivation. -/
def IsUniversalRelativeDifferentials
    (Ω' : SheafOfModules (ringSheaf J O₂)) (d : Der[φ ; Ω']) : Prop :=
  ∀ (F : SheafOfModules (ringSheaf J O₂)) (D : Der[φ ; F]),
    ∃! α : Ω' ⟶ F, RelativeDerivation.postcomp d α = D

-- Proof sketch: combine the descended morphism with its factorization and uniqueness lemmas.
/-- Lemma 18.33.2: the functor `F ↦ Der_{O₁}(O₂, F)` on `O₂`-module sheaves is represented by
`Ω(φ)`; equivalently, every `O₁`-derivation `O₂ → F` factors uniquely through the canonical
derivation `relativeDifferential φ`. -/
theorem relativeDifferentials_representsDerivations
    (F : SheafOfModules (ringSheaf J O₂)) (D : Der[φ ; F]) :
    ∃! α : Ω(φ) ⟶ F,
      RelativeDerivation.postcomp (relativeDifferential φ) α = D := by
  refine ⟨relativeDifferentialDesc φ D, ?_, ?_⟩
  · exact relativeDifferentialDesc_fac φ D
  · intro α hα
    apply relativeDifferential_postcomp_injective φ
    calc
      RelativeDerivation.postcomp (relativeDifferential φ) α = D := hα
      _ = RelativeDerivation.postcomp (relativeDifferential φ)
            (relativeDifferentialDesc φ D) :=
        (relativeDifferentialDesc_fac φ D).symm

/-- The canonical sheaf of relative differentials with its universal derivation satisfies the
universal property of relative differentials. -/
theorem relativeDifferentials_hasUniversalProperty :
    IsUniversalRelativeDifferentials φ Ω(φ) (relativeDifferential φ) :=
  relativeDifferentials_representsDerivations φ

end SheafOfModules.RingedSite
