import Mathlib
import StacksProject_2024.Chap18.Lemma_18_19_2
import StacksProject_2024.Chap21.Definition_21_46_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => DerivedCategory Mod

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]

variable {a b : ℤ}

local notation "TorAmp" => fun E : DMod ↦ HasTorAmplitudeIn E a b

private instance isZero_isStableUnderRetracts (D : Type*) [Category D] :
    ObjectProperty.IsStableUnderRetracts (fun X : D ↦ IsZero X) where
  of_retract h hY := by
    refine ⟨?_, ?_⟩
    · intro Z
      refine ⟨⟨h.i ≫ hY.to_ Z⟩, ?_⟩
      intro f
      calc
        f = 𝟙 _ ≫ f := by simp
        _ = (h.i ≫ h.r) ≫ f := by rw [h.retract]
        _ = h.i ≫ (h.r ≫ f) := by simp
        _ = h.i ≫ hY.to_ Z := by
          exact congrArg (h.i ≫ ·) (hY.eq_of_src _ _)
    · intro Z
      refine ⟨⟨hY.from_ Z ≫ h.r⟩, ?_⟩
      intro f
      calc
        f = f ≫ 𝟙 _ := by simp
        _ = f ≫ (h.i ≫ h.r) := by rw [h.retract]
        _ = (f ≫ h.i) ≫ h.r := by simp
        _ = hY.from_ Z ≫ h.r := by
          exact congrArg (· ≫ h.r) (hY.eq_of_tgt _ _)

/- Domain-style sampling for Lemma 21.46.8:
- primary domain: retract-stable object properties in monoidal derived categories, specialized to
  tor-amplitude on `D(\mathcal O)`;
- sampled owner declarations:
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.prop_of_retract`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `Limits.IsZero`,
  `Retract.map`;
- best owner abstraction: the object property `TorAmp` on `D(\mathcal O)`, with retract-stability
  as the core owner-level API and the two direct-summand consequences as derived API; the
  pointwise `IsZero` condition in the definition is itself treated as a retract-stable object
  property on the target category;
- primitive vs. derived:
  primitive data are the source-facing tor-amplitude predicate `HasTorAmplitudeIn E a b`;
  the retract-stability instance and the left/right biproduct lemmas are derived consequences;
- source/core/bridge triage:
  `source-facing`: the two textbook direct-summand lemmas;
  `core/canonical`: `ObjectProperty.IsStableUnderRetracts TorAmp`;
  `bridge/view`: transport of a retract through tensoring with `ℱ[0]`, then through the homology
    functor, and finally through the generic retract-stability owner for `IsZero`.

This file therefore exposes the retract-stability instance once and derives the two source-facing
biproduct lemmas directly from the generic owner API. Inside the owner proof, both the mapped
retract and the zero-object conclusion are handled through owner-level retract transport rather
than by rebuilding the `IsZero` witness by hand. -/

/-- Objects of `D(\mathcal O)` with tor-amplitude in `[a, b]` are stable under retracts/direct
summands. -/
instance hasTorAmplitudeIn_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts TorAmp where
  of_retract h hE := by
    rw [hasTorAmplitudeIn_iff] at hE ⊢
    intro ℱ i hi
    let S := (DerivedCategory.singleFunctor Mod (0 : ℤ)).obj ℱ
    exact prop_of_retract (fun X : AddCommGrpCat.{max u v} ↦ IsZero X)
      (h.map (tensorRight S ⋙ DerivedCategory.homologyFunctor Mod i))
      (hE ℱ i hi)

-- Proof sketch: tor-amplitude in `[a, b]` is treated as the object property `TorAmp` on
-- `D(\mathcal O)`. Once this property is known to be stable under retracts, the left summand of
-- `K ⊞ L` is obtained from the canonical retract `K ↪ K ⊞ L ↠ K`, so the conclusion is the
-- generic owner lemma `of_biprod_left`.
/-- Lemma 21.46.8: if `K ⊞ L` has tor-amplitude in `[a, b]`, then `K` has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_left_of_biprod
    (K L : DMod) (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b :=
  of_biprod_left TorAmp hKL

-- Proof sketch: use the same retract-stability owner `TorAmp`; the right summand is a retract of
-- `K ⊞ L` via the canonical maps `L ↪ K ⊞ L ↠ L`, so `of_biprod_right` gives the conclusion
-- immediately.
/-- If `K ⊞ L` has tor-amplitude in `[a, b]`, then `L` has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_right_of_biprod
    (K L : DMod) (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn L a b :=
  of_biprod_right TorAmp hKL

end

end SheafOfModules.RingedSite
