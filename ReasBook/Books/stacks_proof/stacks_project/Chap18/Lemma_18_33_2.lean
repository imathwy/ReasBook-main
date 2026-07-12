import Mathlib
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic
import StacksProject_2024.Chap17.Definition_17_28_1

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation

universe u v

noncomputable section

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable (φ : O₁ ⟶ O₂)

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 18.33.2:
- primary domain: sheafified relative differentials of a morphism of sheaves of commutative rings
  on a general site, together with their universal derivation;
- sampled owner declarations:
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `PresheafOfModules.DifferentialsConstruction.derivation'`,
  `PresheafOfModules.DifferentialsConstruction.isUniversal'`,
  `ringSheaf J O₂`,
  `ringedSiteModuleCategory J O₂`,
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`;
- best owner abstraction: the source-facing sheaf owner `relativeDifferentials` with textbook
  notation `Ω(φ)`, obtained by sheafifying the canonical presheaf owner
  `relativeDifferentials' φ.hom`;
- primitive data: the `RingCat`-valued structure sheaf `ringSheaf J O₂`, the ambient module
  category `Mod(O₂)`, the sheaf `relativeDifferentials φ`, and its universal derivation
  `relativeDifferential φ`;
- derived API: the descended universal map `relativeDifferentialDesc`, its factorization and
  injectivity lemmas, the representing theorem
  `relativeDifferentials_representsDerivations`, expressed using the canonical owner method
  `PresheafOfModules.Derivation.postcomp`.

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
abbrev relativeDifferentials : Mod(O₂) :=
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
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).unit.app
        (relativeDifferentials' φ.hom))

/-- The morphism induced from a target derivation by the universal property of relative
differentials. -/
def relativeDifferentialDesc
    {F : Mod(O₂)}
    (D : Der[φ ; F]) :
    Ω(φ) ⟶ F :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj)).symm
    ((isUniversal' φ.hom).desc D)

/-- Helper for Lemma 18.33.2: under the sheafification adjunction, a morphism out of the sheaf of
relative differentials corresponds to composing with the adjunction unit on the presheaf of
relative differentials. -/
theorem sheafificationHomEquiv_relativeDifferentials
    {F : Mod(O₂)}
    (f : Ω(φ) ⟶ F) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj) f =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).unit.app
        (relativeDifferentials' φ.hom)) ≫ f.val := by
  -- The sheafification equivalence is implemented by composition with the adjunction unit.
  ext X x
  rfl

-- Proof sketch: `relativeDifferentialDesc` is obtained by transporting the presheaf-level
-- universal morphism across the sheafification adjunction, so the factorization identity is the
-- adjoint form of `(isUniversal' φ.hom).fac`.
/-- The descended morphism factors the target derivation through the universal derivation. -/
theorem relativeDifferentialDesc_fac
    {F : Mod(O₂)}
    (D : Der[φ ; F]) :
    (relativeDifferential φ).postcomp (relativeDifferentialDesc φ D).val = D := by
  have hcomp :
      (relativeDifferential φ).postcomp (relativeDifferentialDesc φ D).val =
        (derivation' φ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ (relativeDifferentialDesc φ D).val) := by
    -- Both derivations have the same objectwise formula after unfolding `relativeDifferential`.
    rw [relativeDifferential]
    ext X b
    rfl
  have hdesc :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).unit.app
        (relativeDifferentials' φ.hom)) ≫ (relativeDifferentialDesc φ D).val =
        (isUniversal' φ.hom).desc D := by
    -- The descended morphism is defined as the inverse image of the presheaf universal map.
    have hdesc₀ :=
      (sheafificationHomEquiv_relativeDifferentials (φ := φ)
        (f := relativeDifferentialDesc φ D)).symm
    rw [relativeDifferentialDesc] at hdesc₀
    rw [Equiv.apply_symm_apply] at hdesc₀
    exact hdesc₀
  -- Rewrite the sheaf-level factorization back to the presheaf universal morphism.
  have hfac :
      (derivation' φ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ (relativeDifferentialDesc φ D).val) =
        D := by
    -- After replacing the descended morphism by the presheaf universal map, we can invoke `fac`.
    exact (congrArg (fun f ↦ (derivation' φ.hom).postcomp f) hdesc).trans
      ((isUniversal' φ.hom).fac D)
  exact hcomp.trans hfac

-- Proof sketch: uniqueness is inherited from the presheaf-level universal property after applying
-- the sheafification adjunction equivalence.
/-- A morphism out of `Ω(φ)` is determined by its postcomposition with the universal derivation. -/
theorem relativeDifferential_postcomp_injective
    {F : Mod(O₂)}
    ⦃α β : Ω(φ) ⟶ F⦄
    (h : (relativeDifferential φ).postcomp α.val =
      (relativeDifferential φ).postcomp β.val) :
    α = β := by
  have hα_unit :
      (derivation' φ.hom).postcomp
          (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj) α) =
        (derivation' φ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ α.val) := by
    -- Apply postcomposition to the adjunction-side description of `α`.
    exact congrArg (fun f ↦ (derivation' φ.hom).postcomp f)
      (sheafificationHomEquiv_relativeDifferentials (φ := φ) (f := α))
  have hβ_unit :
      (derivation' φ.hom).postcomp
          (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj) β) =
        (derivation' φ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ β.val) := by
    -- The same transport identifies the presheaf image of `β`.
    exact congrArg (fun f ↦ (derivation' φ.hom).postcomp f)
      (sheafificationHomEquiv_relativeDifferentials (φ := φ) (f := β))
  have hα_comp :
      (derivation' φ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ α.val) =
        (relativeDifferential φ).postcomp α.val := by
    -- Unfolding `relativeDifferential` shows both derivations are defined by the same composite.
    rw [relativeDifferential]
    ext X b
    rfl
  have hβ_comp :
      (derivation' φ.hom).postcomp
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ β.val) =
        (relativeDifferential φ).postcomp β.val := by
    -- The `β`-branch has the same objectwise comparison.
    rw [relativeDifferential]
    ext X b
    rfl
  have hα' :
      (derivation' φ.hom).postcomp
          (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj) α) =
        (relativeDifferential φ).postcomp α.val :=
    hα_unit.trans hα_comp
  have hβ' :
      (derivation' φ.hom).postcomp
          (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj) β) =
        (relativeDifferential φ).postcomp β.val :=
    hβ_unit.trans hβ_comp
  -- Transport the equality to the presheaf universal property via the sheafification equivalence.
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj)).injective
  apply (isUniversal' φ.hom).postcomp_injective
  exact hα'.trans (h.trans hβ'.symm)

-- Proof sketch: combine the descended morphism with its factorization and uniqueness lemmas.
/-- Lemma 18.33.2: the functor `F ↦ Der_{O₁}(O₂, F)` on `O₂`-module sheaves is represented by
`Ω(φ)`; equivalently, every `O₁`-derivation `O₂ → F` factors uniquely through the canonical
derivation `relativeDifferential φ`. -/
@[stacks 04BL]
theorem relativeDifferentials_representsDerivations
    (F : Mod(O₂))
    (D : Der[φ ; F]) :
    ∃! α : Ω(φ) ⟶ F,
      (relativeDifferential φ).postcomp α.val = D := by
  refine ⟨relativeDifferentialDesc φ D, ?_, ?_⟩
  · exact relativeDifferentialDesc_fac φ D
  · intro α hα
    apply relativeDifferential_postcomp_injective φ
    calc
      (relativeDifferential φ).postcomp α.val = D := hα
      _ = (relativeDifferential φ).postcomp (relativeDifferentialDesc φ D).val :=
        (relativeDifferentialDesc_fac φ D).symm

end SheafOfModules.RingedSite
