import Mathlib
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_15_1 (from Chap18) -/
open CategoryTheory

universe u₁ u₂ v₁ v₂

namespace CategoryTheory
namespace Adjunction

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-
Domain-style sampling for Lemma 18.15.1:
- primary domain: adjunctions and categorical epimorphisms;
- sampled owner API:
  `Adjunction.faithful_R_of_epi_counit_app`,
  `Functor.ReflectsEpimorphisms`,
  `Functor.epi_of_epi_map`,
  `Functor.preservesEpimorphisms_of_adjunction`;
- source/core/bridge triage:
  `core/canonical`: the adjunction `L ⊣ R`;
  `bridge/view`: the Chapter 18 abelian-sheaf specialization of this adjunction theorem.

Primitive data are only the adjunction. Pointwise counit epimorphy, reflection of epimorphisms,
and faithfulness of the right adjoint are derived owner-level API, so this file should live at the
`Adjunction` owner rather than repackage the same mathematics with a separate sheaf-specific
functor triple.
-/

-- Proof sketch: if `R.map f` is epic, apply the left adjoint `L`, use naturality of the counit to
-- identify `L.map (R.map f) ≫ ε_Y` with `ε_X ≫ f`, and then cancel the epimorphic counit on the
-- left. Conversely, `R.map (ε_X)` is split epic by the triangle identity, so if `R` reflects
-- epimorphisms then `ε_X` is epic.
/-- Owner-level form of Lemma 18.15.1: for any adjunction, the counit components are epimorphisms
if and only if the right adjoint reflects epimorphisms. Applied to the inverse-image/direct-image
adjunction on abelian sheaves, this is the Stacks statement for `f⁻¹ f_* \mathcal F ⟶ \mathcal
F`. -/
theorem epi_counit_app_iff_reflectsEpimorphisms (adj : L ⊣ R) :
    (∀ X : D, Epi (adj.counit.app X)) ↔ R.ReflectsEpimorphisms := by
  constructor
  · intro hc
    refine ⟨fun {X Y} f hf ↦ ?_⟩
    haveI : Functor.PreservesEpimorphisms L := Functor.preservesEpimorphisms_of_adjunction adj
    haveI : Epi (R.map f) := hf
    have hEq : L.map (R.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f := by
      simpa using adj.counit.naturality f
    have hcomp : Epi (adj.counit.app X ≫ f) := by
      rw [← hEq]
      exact epi_comp' (inferInstance : Epi (L.map (R.map f))) (hc Y)
    exact (epi_comp_iff_of_epi (adj.counit.app X) f).1 hcomp
  · intro hR
    letI : R.ReflectsEpimorphisms := hR
    intro X
    haveI : IsSplitEpi (R.map (adj.counit.app X)) := by
      refine IsSplitEpi.mk' ⟨adj.unit.app (R.obj X), ?_⟩
      simp
    exact Functor.epi_of_epi_map R (show Epi (R.map (adj.counit.app X)) by infer_instance)

-- Proof sketch: by the previous theorem, reflection of epimorphisms makes all counit components
-- epic, and then the canonical owner theorem `Adjunction.faithful_R_of_epi_counit_app` applies.
/-- Corollary to Lemma 18.15.1: if the right adjoint reflects epimorphisms, then it is faithful.
For abelian sheaf direct images, this recovers the source-facing faithfulness consequence from the
canonical adjunction owner theorem. -/
theorem faithful_R_of_reflectsEpimorphisms (adj : L ⊣ R) (hR : R.ReflectsEpimorphisms) :
    R.Faithful := by
  have hc : ∀ X : D, Epi (adj.counit.app X) := (epi_counit_app_iff_reflectsEpimorphisms adj).2 hR
  letI (X : D) : Epi (adj.counit.app X) := hc X
  exact adj.faithful_R_of_epi_counit_app

end Adjunction
end CategoryTheory

/-! ### Lemma_18_15_2 (from Chap18) -/
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Lemma 18.15.2:
- primary domain: exactness criteria for direct-image functors on sheaves of abelian groups,
  together with site presentations of morphisms of topoi;
- sampled owner declarations:
  `Functor.sheafPushforwardContinuous`,
  `sheaf_pushforward_forget`,
  `MorphismOfTopoiIn.presentationFunctor_pushforwardIso`,
  `exactFunctor`;
- best owner abstraction:
  the canonical abelian direct-image owner for a presentation is
  `u.sheafPushforwardContinuous AddCommGrpCat J K`;
- primitive-vs-derived split:
  the primitive data are the continuous functor `u : C ⥤ D` and, for the bridge/view layer, a
  comparison isomorphism
  `ePush : u.sheafPushforwardContinuous (Type _) J K ≅ f.pushforward`
  presenting
  the set-valued direct image of a morphism of topoi `f`;
  preservation of epimorphisms, coequalizers, pushouts, and exactness are derived owner-level
  properties of the canonical pushforward functor, while the ambient abelian-sheaf
  infrastructure needed here lives only on the target site `K`;
- source/core/bridge triage:
  `source-facing`: the Stacks exactness criterion for the abelian direct image and its formulation
    for a morphism of topoi presented by a continuous functor;
  `core/canonical`: `exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat J K)`;
  `bridge/view`: the presentation isomorphism `ePush` on underlying sheaves of sets, together
    with the canonical forget-comparison from `sheaf_pushforward_forget`.

The previous public owner `MorphismOfTopoiIn.abelianPushforward` duplicated the existing Chapter 7
presentation machinery. This file now uses the canonical owner
`u.sheafPushforwardContinuous AddCommGrpCat J K` directly and keeps the morphism-of-topoi
formulation only as a bridge/view statement. -/

section ExactnessCriterion

variable (u : C ⥤ D) [u.IsContinuous J K]
variable [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]
variable [K.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]

/-- If the underlying set-valued direct image of the continuous presentation `u` preserves
epimorphisms, then the induced direct image on sheaves of abelian groups also preserves
epimorphisms. -/
theorem sheafPushforwardContinuous_preservesEpimorphisms_of_underlyingPreservesEpimorphisms
    (hpush :
      (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K).PreservesEpimorphisms) :
    (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K).PreservesEpimorphisms := sorry

/-- If the direct image on sheaves of abelian groups preserves epimorphisms, then it is exact. -/
theorem sheafPushforwardContinuous_exact_of_preservesEpimorphisms
    (hpush :
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K).PreservesEpimorphisms) :
    exactFunctor
      (Sheaf K AddCommGrpCat.{max u₁ u₂ v})
      (Sheaf J AddCommGrpCat.{max u₁ u₂ v})
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K) := sorry

/-- Lemma 18.15.2, canonical-owner form: if the direct image on sheaves of abelian groups
preserves epimorphisms, or if its underlying set-valued direct image preserves epimorphisms,
coequalizers, or pushouts, then the abelian direct image is exact. -/
theorem sheafPushforwardContinuous_exact_of_preservesEpimorphisms_or_underlyingPreservesEpimorphisms_or_coequalizers_or_pushouts
    (h :
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K).PreservesEpimorphisms ∨
        (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K).PreservesEpimorphisms ∨
          PreservesColimitsOfShape WalkingParallelPair
            (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K) ∨
            PreservesColimitsOfShape WalkingSpan
              (u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K)) :
    exactFunctor
      (Sheaf K AddCommGrpCat.{max u₁ u₂ v})
      (Sheaf J AddCommGrpCat.{max u₁ u₂ v})
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K) := sorry

end ExactnessCriterion

section PresentedExactnessCriterion

variable (f : MorphismOfTopoiIn.{u₁, u₂, v, v, max u₁ u₂ v} J K)
variable (u : C ⥤ D) [u.IsContinuous J K]
variable [HasWeakSheafify K AddCommGrpCat.{max u₁ u₂ v}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ u₂ v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]
variable [K.HasSheafCompose (forget AddCommGrpCat.{max u₁ u₂ v})]

-- Bridge/view input: `ePush` presents the underlying set-valued direct image of `f` by the
-- canonical owner `u.sheafPushforwardContinuous (Type _) J K`. Together with the Chapter 7
-- forget-comparison `sheaf_pushforward_forget`, this is the comparison data used to transport the
-- set-valued hypotheses on `f.pushforward` to the abelian pushforward owner.

/-- Lemma 18.15.2, bridge form: if `ePush` presents the underlying set-valued direct image of
`f : Sh(K) ⟶ Sh(J)` by the continuous functor `u`, and if `f _*` preserves epimorphisms,
coequalizers, or pushouts, then the induced direct image on abelian sheaves,
`u.sheafPushforwardContinuous AddCommGrpCat J K`, is exact. -/
theorem presented_sheafPushforwardContinuous_exact_of_pushforwardPreservesEpimorphisms_or_coequalizers_or_pushouts
    (ePush :
      u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K ≅
        f.pushforward)
    (h :
      f.pushforward.PreservesEpimorphisms ∨
        PreservesColimitsOfShape WalkingParallelPair f.pushforward ∨
          PreservesColimitsOfShape WalkingSpan f.pushforward) :
    exactFunctor
      (Sheaf K AddCommGrpCat.{max u₁ u₂ v})
      (Sheaf J AddCommGrpCat.{max u₁ u₂ v})
      (u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ u₂ v} J K) := sorry

end PresentedExactnessCriterion

end CategoryTheory.Functor

/-! ### Lemma_18_15_3 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 18.15.3:
- primary domain: exactness of direct-image functors on sheaves of abelian groups and on sheaves
  of modules over a ringed morphism of sites;
- sampled owner declarations:
  `Functor.sheafPushforwardContinuous`,
  `exactFunctor`,
  `SheafOfModules.pushforward`,
  `moduleSheaf_toSheaf_exact`;
- best owner abstraction:
  the abelian-sheaf exactness owner
  `exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat JC JD)`;
- primitive-vs-derived split:
  the primitive data are the continuous functor `u`, the almost-cocontinuity hypothesis, the
  two ring sheaves, and the structure-sheaf morphism `φ`;
  the weak sheafification and locally-bijective hypotheses on `JC` and `JD` are ambient
  infrastructure needed for the canonical abelian and module sheaf owners, while almost
  cocontinuity supplies the finite-connected-colimit preservation used to recover exactness of
  the abelian pushforward owner, and the module statement is then a bridge through
  `moduleSheaf_toSheaf_exact`.

Source/core/bridge triage:
- `source-facing`: the Stacks exactness statements for `f_*` on abelian sheaves and on module
  sheaves under almost cocontinuity;
- `core/canonical`: the exactness owner
  `exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat JC JD)`;
- `bridge/view`: the epimorphism-preservation step obtained from almost cocontinuity for clause
  `(1)` and the forgetful comparison through `SheafOfModules.toSheaf` for clause `(2)`.

This file should therefore keep the abelian pushforward at the canonical owner level
`exactFunctor _ _ (u.sheafPushforwardContinuous AddCommGrpCat JC JD)` and treat the module
statement as a bridge on top of that owner, rather than introducing any wrapper data. -/

section Exactness

variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JD AddCommGrpCat.{w}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{w}]

-- Proof sketch: use the canonical owner `u.sheafPushforwardContinuous AddCommGrpCat JC JD`;
-- almost cocontinuity supplies the finite-connected-colimit preservation input, and the standard
-- exact-functor criterion upgrades this to exactness.
/-- Lemma 18.15.3 (1): if `f : \mathcal D \to \mathcal C` is the morphism of sites associated to
the continuous functor `u : \mathcal C \to \mathcal D` and `u` is almost cocontinuous, then the
direct image functor `f_*`, identified here with
`u.sheafPushforwardContinuous AddCommGrpCat JC JD`, is exact on sheaves of abelian groups. -/
theorem sheafPushforwardContinuous_exact_of_isAlmostCocontinuous
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD] :
    exactFunctor (Sheaf JD AddCommGrpCat.{w}) (Sheaf JC AddCommGrpCat.{w})
      (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD) := sorry

-- Proof sketch: the module pushforward is a right adjoint, so it is left exact. To obtain right
-- exactness, first show that its composition with the faithful forgetful functor
-- `SheafOfModules.toSheaf 𝒪C` preserves epimorphisms; this composition is definitionally the
-- composite of `SheafOfModules.toSheaf 𝒪D` with the exact abelian pushforward from clause `(1)`.
-- Since `SheafOfModules.toSheaf 𝒪C` reflects epimorphisms, the module pushforward preserves epis,
-- and the standard homology criterion upgrades this to exactness.
/-- Lemma 18.15.3 (2): if `f^\sharp : f^{-1}\mathcal O_\mathcal C \to \mathcal O_\mathcal D` is
given so that `f` becomes a morphism of ringed sites, encoded in Lean by a morphism
`φ : \mathcal O_\mathcal C \to u_* \mathcal O_\mathcal D`, then the direct image functor
`f_* = SheafOfModules.pushforward φ` is exact on sheaves of modules. -/
theorem sheafOfModules_pushforward_exact_of_isAlmostCocontinuous
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{w}) (𝒪D : Sheaf JD RingCat.{w})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{w} JC JD).obj 𝒪D) :
    exactFunctor (SheafOfModules 𝒪D) (SheafOfModules 𝒪C)
      (SheafOfModules.pushforward φ) := sorry

end Exactness

end CategoryTheory.Functor
