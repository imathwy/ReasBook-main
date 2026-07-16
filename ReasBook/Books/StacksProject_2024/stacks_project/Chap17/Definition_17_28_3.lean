import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open AlgebraicGeometry
open PresheafOfModules
open PresheafOfModules.DifferentialsConstruction
open TopCat.Sheaf
open RelativeDerivation
open scoped RelativeDerivation

universe u

noncomputable section

variable {X : TopCat.{u}}
variable {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X}
variable (φ : O₁ ⟶ O₂)

namespace TopCat.Sheaf

/-- A sheaf of commutative rings on `X`, viewed as the corresponding ringed space with carrier
`X`. -/
abbrev toRingedSpace (O : TopCat.Sheaf CommRingCat.{u} X) : RingedSpace :=
  { carrier := X
    presheaf := O.presheaf
    IsSheaf := O.2 }

/- Domain-style sampling for Definition 17.28.3:
- primary domain: sheafified relative differentials of sheaves of commutative rings on a
  topological space;
- sampled owner declarations:
  `PresheafOfModules.sheafification`,
  `PresheafOfModules.sheafificationAdjunction`,
  `PresheafOfModules.sheafificationHomEquiv`,
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `PresheafOfModules.DifferentialsConstruction.derivation'`,
  `PresheafOfModules.DifferentialsConstruction.isUniversal'`,
  `TopCat.Sheaf.relativeDifferentialDesc`;
- best owner abstraction: the source-facing sheafified owner
  `TopCat.Sheaf.relativeDifferentials`, obtained from the canonical presheaf differentials owner by
  sheafification;
  `relativeDifferentials' φ.hom`, the sheafified module `relativeDifferentials`, and its
  universal derivation `relativeDifferential`;
- derived API: the definitional sheafification theorem `relativeDifferentials_def`, the descended
  universal morphism `relativeDifferentialDesc`, its factorization and injectivity lemmas, and the
  representing theorem
  `relativeDifferentials_representsDerivations`.

Source/core/bridge triage:
- `core/canonical`: the presheaf owner
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`;
- `source-facing`: the sheafified owner `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: the sheafification descent API from the presheaf universal derivation to sheaf
  targets;
- this file owns the sheaf-level construction and its primitive support data, so downstream files
  should reuse these declarations rather than reintroduce local copies. -/

/-- A sheaf of commutative rings on `X`, viewed as a sheaf with values in `RingCat`. -/
abbrev ringSheaf (O : TopCat.Sheaf CommRingCat.{u} X) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).obj O

/-- The underlying morphism of `RingCat`-valued sheaves induced by a morphism of sheaves of
commutative rings. -/
abbrev ringSheafMap {O O' : TopCat.Sheaf CommRingCat.{u} X} (α : O ⟶ O') :
    ringSheaf O ⟶ ringSheaf O' :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).map α

/-- Definition 17.28.3: for a morphism `φ : 𝒪₁ ⟶ 𝒪₂` of sheaves of rings on a topological
space, the module of differentials `Ω_{𝒪₂/𝒪₁}` is the sheaf representing the functor
`ℱ ↦ Der_{𝒪₁}(𝒪₂, ℱ)`. -/
abbrev relativeDifferentials :
    SheafOfModules (ringSheaf O₂) :=
  (sheafification (𝟙 (ringSheaf O₂).obj)).obj
    (relativeDifferentials' φ.hom)

@[inherit_doc relativeDifferentials]
notation:max "Ω(" φ ")" => relativeDifferentials φ

/-- The sheaf of relative differentials is the sheafification of the presheaf of objectwise
Kähler differentials. -/
theorem relativeDifferentials_def :
    Ω(φ) =
      (sheafification (𝟙 (ringSheaf O₂).obj)).obj
        (relativeDifferentials' φ.hom) := rfl

/-- The universal `φ`-derivation from `O₂` to `Ω(φ)`. -/
def relativeDifferential :
    Der[φ ; Ω(φ)] :=
  (derivation' φ.hom).postcomp
    ((sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
      (relativeDifferentials' φ.hom))

/-- The descended morphism induced by a `φ`-derivation into a sheaf of modules. -/
def relativeDifferentialDesc
    {F : SheafOfModules (ringSheaf O₂)} (D : Der[φ ; F]) :
    Ω(φ) ⟶ F :=
  (sheafificationHomEquiv (𝟙 (ringSheaf O₂).obj)).symm ((isUniversal' φ.hom).desc D)

/-- Helper for Definition 17.28.3: under the sheafification adjunction, a morphism out of the
sheaf of relative differentials corresponds to composing with the adjunction unit on the
presheaf of relative differentials. -/
theorem sheafificationHomEquiv_relativeDifferentials
    {F : SheafOfModules (ringSheaf O₂)}
    (f : Ω(φ) ⟶ F) :
    sheafificationHomEquiv (𝟙 (ringSheaf O₂).obj) f =
      ((sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
        (relativeDifferentials' φ.hom)) ≫ f.val := by
  -- The sheafification equivalence is implemented by composition with the adjunction unit.
  ext U s
  rfl

-- Proof sketch: `relativeDifferentialDesc` is obtained by transporting the presheaf-level
-- universal morphism across the sheafification adjunction, so the factorization identity is the
-- adjoint form of `isUniversal' φ.hom |>.fac`.
/-- The descended morphism factors the target derivation through the universal derivation. -/
theorem relativeDifferentialDesc_fac
    {F : SheafOfModules (ringSheaf O₂)} (D : Der[φ ; F]) :
    (relativeDifferential φ).postcomp (relativeDifferentialDesc φ D).val = D := by
  have hcomp :
      (relativeDifferential φ).postcomp (relativeDifferentialDesc φ D).val =
        (derivation' φ.hom).postcomp
          (((sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ (relativeDifferentialDesc φ D).val) := by
    -- Unfolding `relativeDifferential` exposes the same presheaf composite on both sides.
    rw [relativeDifferential]
    ext U s
    rfl
  have hdesc :
      ((sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
        (relativeDifferentials' φ.hom)) ≫ (relativeDifferentialDesc φ D).val =
        (isUniversal' φ.hom).desc D := by
    -- `relativeDifferentialDesc` is defined as the inverse image of the presheaf universal map.
    have hdesc₀ :=
      (sheafificationHomEquiv_relativeDifferentials (φ := φ)
        (f := relativeDifferentialDesc φ D)).symm
    rw [relativeDifferentialDesc] at hdesc₀
    rw [Equiv.apply_symm_apply] at hdesc₀
    exact hdesc₀
  have hfac :
      (derivation' φ.hom).postcomp
          (((sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ (relativeDifferentialDesc φ D).val) =
        D := by
    -- After identifying the descended morphism with the presheaf universal map, invoke `fac`.
    exact (congrArg (fun f ↦ (derivation' φ.hom).postcomp f) hdesc).trans
      ((isUniversal' φ.hom).fac D)
  exact hcomp.trans hfac

-- Proof sketch: uniqueness is inherited from the presheaf-level universal property after applying
-- the sheafification adjunction equivalence.
/-- A morphism out of `Ω(φ)` is determined by its postcomposition with the universal
derivation. -/
theorem relativeDifferential_postcomp_injective
    {F : SheafOfModules (ringSheaf O₂)} ⦃α β : Ω(φ) ⟶ F⦄
    (h : (relativeDifferential φ).postcomp α.val =
      (relativeDifferential φ).postcomp β.val) :
    α = β := by
  have hα_unit :
      (derivation' φ.hom).postcomp
          (sheafificationHomEquiv (𝟙 (ringSheaf O₂).obj) α) =
        (derivation' φ.hom).postcomp
          (((sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ α.val) := by
    -- Transport `α` across the adjunction before comparing postcompositions.
    exact congrArg (fun f ↦ (derivation' φ.hom).postcomp f)
      (sheafificationHomEquiv_relativeDifferentials (φ := φ) (f := α))
  have hβ_unit :
      (derivation' φ.hom).postcomp
          (sheafificationHomEquiv (𝟙 (ringSheaf O₂).obj) β) =
        (derivation' φ.hom).postcomp
          (((sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ β.val) := by
    -- The same adjunction-side normalization applies to `β`.
    exact congrArg (fun f ↦ (derivation' φ.hom).postcomp f)
      (sheafificationHomEquiv_relativeDifferentials (φ := φ) (f := β))
  have hα_comp :
      (derivation' φ.hom).postcomp
          (((sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ α.val) =
        (relativeDifferential φ).postcomp α.val := by
    -- Unfolding `relativeDifferential` shows both sides are the same derivation.
    rw [relativeDifferential]
    ext U s
    rfl
  have hβ_comp :
      (derivation' φ.hom).postcomp
          (((sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
            (relativeDifferentials' φ.hom)) ≫ β.val) =
        (relativeDifferential φ).postcomp β.val := by
    -- The comparison for `β` is identical.
    rw [relativeDifferential]
    ext U s
    rfl
  have hα' :
      (derivation' φ.hom).postcomp
          (sheafificationHomEquiv (𝟙 (ringSheaf O₂).obj) α) =
        (relativeDifferential φ).postcomp α.val :=
    hα_unit.trans hα_comp
  have hβ' :
      (derivation' φ.hom).postcomp
          (sheafificationHomEquiv (𝟙 (ringSheaf O₂).obj) β) =
        (relativeDifferential φ).postcomp β.val :=
    hβ_unit.trans hβ_comp
  -- Move to the presheaf universal property through the sheafification equivalence.
  apply (sheafificationHomEquiv (𝟙 (ringSheaf O₂).obj)).injective
  apply (isUniversal' φ.hom).postcomp_injective
  exact hα'.trans (h.trans hβ'.symm)

/-- The sheaf of relative differentials represents `O₁`-derivations out of `O₂`. -/
theorem relativeDifferentials_representsDerivations
    (F : SheafOfModules (ringSheaf O₂)) (D : Der[φ ; F]) :
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

end TopCat.Sheaf
