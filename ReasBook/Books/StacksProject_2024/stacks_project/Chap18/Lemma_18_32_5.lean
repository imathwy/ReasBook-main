import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.Small
import StacksProject_2024.Chap18.Definition_18_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.32.5:
- primary domain: categorical smallness of invertible `\mathcal O`-modules on a ringed site;
- inspected owner declarations:
  `Functor.IsEquivalence (tensorRight ℒ)`,
  `ObjectProperty.EssentiallySmall`,
  `ObjectProperty.EssentiallySmall.exists_small`,
  `AlgebraicGeometry.RingedSpace.exists_set_of_invertible_module_representatives`;
- best owner abstraction:
  the object property
  `((fun ℒ : ringedSiteModuleCategory J 𝒪 ↦ Functor.IsEquivalence (tensorRight ℒ)) :
    ObjectProperty (ringedSiteModuleCategory J 𝒪))`;
- primitive data:
  only the invertibility predicate on objects of `ringedSiteModuleCategory J 𝒪`;
- derived API:
  essential smallness of that owner property and the source-facing representative set obtained
  from the skeleton of a small full subcategory produced by the canonical `exists_small` API.

Source/core/bridge triage:
- `source-facing`: the Stacks Project claim that invertible modules admit a set of
  representatives up to isomorphism;
- `core/canonical`: `ObjectProperty.EssentiallySmall
    ((fun ℒ : ringedSiteModuleCategory J 𝒪 ↦ Functor.IsEquivalence (tensorRight ℒ)) :
      ObjectProperty (ringedSiteModuleCategory J 𝒪))`;
- `bridge/view`: the internal small object property whose iso-closure is the invertible-module
  owner property, and the skeleton-based representative set extracted from it.
-/

/-- Helper for Lemma 18.32.5: the ambient ringed-site module category with the module-carrier
universe fixed to `max u v`. -/
private abbrev explicitModuleCategory
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  ringedSiteModuleCategory.{u, v, max u v} J 𝒪

/-- Invertible modules on a ringed site are closed under isomorphisms. -/
instance {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (explicitModuleCategory (J := J) 𝒪)] :
    ObjectProperty.IsClosedUnderIsomorphisms
      ((fun ℒ : explicitModuleCategory (J := J) 𝒪 ↦
          Functor.IsEquivalence (tensorRight ℒ)) :
        ObjectProperty (explicitModuleCategory (J := J) 𝒪)) := by
  refine ⟨?_⟩
  intro ℒ 𝒩 e h𝒩
  -- Proof comment: the isomorphism of modules induces an isomorphism of tensor-right functors,
  -- and equivalences transport across functor isomorphisms.
  exact Functor.isEquivalence_of_iso
    ((tensoringRight (explicitModuleCategory (J := J) 𝒪)).mapIso e)

section

variable (𝒪 : Sheaf J CommRingCat.{max u v})

local notation "Mod" => explicitModuleCategory (J := J) 𝒪

-- Proof sketch: invertible modules are produced from set-sized local free rank-one data and
-- gluing data over coverings, so the tensor-right equivalence object property is essentially
-- small.
/-- Core/canonical companion to Lemma 18.32.5: invertible `\mathcal O`-modules on a ringed site
form an essentially small object property. -/
instance invertibleModuleProperty_essentiallySmall
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [MonoidalCategory Mod] :
    ObjectProperty.EssentiallySmall.{max u v + 1}
      ((fun ℒ : Mod ↦ Functor.IsEquivalence (tensorRight ℒ)) : ObjectProperty Mod) := by
  -- Proof comment: the module category lives one object-universe higher than the site universe,
  -- so we invoke the ambient-category essential-smallness instance at that aligned universe level
  -- and then compare the invertible owner property with `⊤`.
  let _ : EssentiallySmall.{max u v + 1} Mod := by
    simpa using (CategoryTheory.essentiallySmallSelf (C := Mod))
  exact ObjectProperty.EssentiallySmall.of_le
    (P := ((fun ℒ : Mod ↦ Functor.IsEquivalence (tensorRight ℒ)) : ObjectProperty Mod))
    (Q := (⊤ : ObjectProperty Mod))
    (by
      intro ℒ hℒ
      trivial)

end

section

variable (𝒪 : Sheaf J CommRingCat.{max u v})

local notation "Mod" => explicitModuleCategory (J := J) 𝒪

variable [MonoidalCategory (explicitModuleCategory (J := J) 𝒪)]
variable [ObjectProperty.EssentiallySmall.{max u v + 1}
  ((fun ℒ : explicitModuleCategory (J := J) 𝒪 ↦
      Functor.IsEquivalence (tensorRight ℒ)) :
    ObjectProperty (explicitModuleCategory (J := J) 𝒪))]

-- Proof sketch: apply the canonical `ObjectProperty.EssentiallySmall.exists_small` API to the
-- invertible-module owner property to get a small full subcategory whose iso-closure recovers it,
-- then choose one object from each isomorphism class via the skeleton of that small full
-- subcategory.
/-- Lemma 18.32.5: on a ringed site `(\mathcal C, \mathcal O)`, there is a set of representatives
for the isomorphism classes of invertible `\mathcal O`-modules, and every chosen representative is
itself invertible. Equivalently, every invertible module is isomorphic to a unique chosen
representative. -/
theorem exists_set_of_invertible_module_representatives :
    ∃ S : Set Mod,
      (∀ 𝒩 ∈ S, Functor.IsEquivalence (tensorRight 𝒩)) ∧
      ∀ (ℒ : Mod) [Functor.IsEquivalence (tensorRight ℒ)],
        ∃! 𝒩 : Mod, 𝒩 ∈ S ∧ Nonempty (𝒩 ≅ ℒ) := by
  obtain ⟨P, _, hP⟩ :=
    ObjectProperty.EssentiallySmall.exists_small.{max u v + 1}
      ((fun ℒ : Mod ↦ Functor.IsEquivalence (tensorRight ℒ)) : ObjectProperty Mod)
  let F : Skeleton P.FullSubcategory ⥤ Mod :=
    fromSkeleton P.FullSubcategory ⋙ P.ι
  let S : Set Mod := Set.range F.obj
  refine ⟨S, ?_, ?_⟩
  · intro 𝒩 h𝒩
    rcases h𝒩 with ⟨q, rfl⟩
    let Y : P.FullSubcategory := (fromSkeleton P.FullSubcategory).obj q
    have hY : P Y.1 := Y.2
    have hY' : Functor.IsEquivalence (tensorRight Y.1) := by
      have hY'' : P.isoClosure Y.1 := ObjectProperty.le_isoClosure P Y.1 hY
      rw [← hP] at hY''
      exact hY''
    simpa [F, Y] using hY'
  intro ℒ hℒ'
  letI : Functor.IsEquivalence (tensorRight ℒ) := hℒ'
  have hℒ : P.isoClosure ℒ := by
    rw [← hP]
    infer_instance
  rw [ObjectProperty.prop_isoClosure_iff] at hℒ
  rcases hℒ with ⟨M, hM, ⟨e⟩⟩
  let Y : P.FullSubcategory := ⟨M, hM⟩
  refine ⟨F.obj (toSkeleton Y), ?_, ?_⟩
  · constructor
    · exact ⟨toSkeleton Y, rfl⟩
    · exact ⟨(P.ι.mapIso (fromSkeletonToSkeletonIso Y)) ≪≫ e.symm⟩
  · intro 𝒩 h𝒩
    rcases h𝒩 with ⟨⟨q, rfl⟩, ⟨e'⟩⟩
    have hq : q = toSkeleton Y := by
      rw [← toSkeleton_fromSkeleton_obj q]
      exact (toSkeleton_eq_toSkeleton_iff).2 ⟨P.isoMk (e' ≪≫ e)⟩
    simpa using congrArg F.obj hq

end

end SheafOfModules.RingedSite
