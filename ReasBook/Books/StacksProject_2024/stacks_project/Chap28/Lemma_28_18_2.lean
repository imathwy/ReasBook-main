import StacksProject_2024.Chap26.Lemma_26_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the affine-module sheaf owner
-- `AlgebraicGeometry.tilde`; inspecting mathlib then identified the ambient counit
-- `Scheme.Modules.fromTildeΓ` on `Spec A` and the open-immersion restriction/pushforward counit
-- `Scheme.Modules.restrictAdjunction`. The source-facing canonical map is therefore the
-- restriction of `fromTildeΓ` for `j_* ℱ`, followed by the counit `j^{-1} j_* ℱ ⟶ ℱ`.

variable {A : Type u} [CommRing A]
variable {U : Scheme.{u}}

private abbrev pushforwardModuleToSpec
    (j : U ⟶ Spec (.of A)) (ℱ : U.Modules) :
    (Spec (.of A)).Modules :=
  (pushforward j).obj ℱ

/-- The `A`-module of global sections of `j_* ℱ`, canonically identified with `Γ(U, ℱ)`. -/
abbrev globalSectionsModule
    (j : U ⟶ Spec (.of A)) (ℱ : U.Modules) :
    ModuleCat A :=
  (moduleSpecΓFunctor (CommRingCat.of A)).obj (pushforwardModuleToSpec j ℱ)

/-- For a quasi-compact open immersion into an affine scheme, pushing forward a quasi-coherent
module stays quasi-coherent. This packages the canonical Chapter 26 pushforward result in the
open-immersion-to-`Spec` setting used by Lemma 28.18.2. -/
instance pushforward_obj_isQuasicoherent_of_quasiCompact_openImmersionToSpec
    (j : U ⟶ Spec (.of A)) [IsOpenImmersion j] [QuasiCompact j]
    (ℱ : U.Modules) [ℱ.IsQuasicoherent] :
    (pushforwardModuleToSpec j ℱ).IsQuasicoherent := by
  simpa using
    Scheme.pushforward_obj_isQuasicoherent_of_quasiCompact_quasiSeparated (f := j) ℱ

/-- The affine counit `\widetilde{Γ(U, \mathcal F)} \to j_* \mathcal F` obtained from
`fromTildeΓ` for the pushforward sheaf `j_* ℱ`. -/
noncomputable abbrev tildeGlobalSectionsToPushforward
    (j : U ⟶ Spec (.of A)) [IsOpenImmersion j]
    (ℱ : U.Modules) :
    tilde (globalSectionsModule j ℱ) ⟶ pushforwardModuleToSpec j ℱ :=
  fromTildeΓ (R := CommRingCat.of A) (M := pushforwardModuleToSpec j ℱ)

/-- For a quasi-compact open immersion into an affine scheme, the affine counit for `j_* ℱ` is an
isomorphism once `ℱ` is quasi-coherent. -/
theorem isIso_tildeGlobalSectionsToPushforward_of_quasiCompact_openImmersionToSpec
    (j : U ⟶ Spec (.of A)) [IsOpenImmersion j] [QuasiCompact j]
    (ℱ : U.Modules) [ℱ.IsQuasicoherent] :
    IsIso (tildeGlobalSectionsToPushforward j ℱ) := by
  change IsIso (fromTildeΓ (R := CommRingCat.of A) (M := pushforwardModuleToSpec j ℱ))
  infer_instance

/-- The canonical restriction-pushforward counit isomorphism for an open immersion. -/
noncomputable abbrev restrictPushforwardIso
    (j : U ⟶ Spec (.of A)) [IsOpenImmersion j]
    (ℱ : U.Modules) :
    (pushforwardModuleToSpec j ℱ).restrict j ≅ ℱ :=
  (asIso (restrictAdjunction j).counit).app ℱ

/-- Restrict the ambient affine counit for `j_* ℱ` back to `U`, then apply the canonical
open-immersion counit `j^{-1} j_* ℱ ⟶ ℱ`. This is the source canonical map
`\widetilde{H^0(U, \mathcal F)}|_U \to \mathcal F`. -/
noncomputable abbrev tildeGlobalSectionsRestrictMap
    (j : U ⟶ Spec (.of A)) [IsOpenImmersion j]
    (ℱ : U.Modules) :
    (tilde (globalSectionsModule j ℱ)).restrict j ⟶ ℱ :=
  (restrictFunctor j).map (tildeGlobalSectionsToPushforward j ℱ) ≫
    (restrictPushforwardIso j ℱ).hom

/-- Lemma 28.18.2: for a quasi-compact open immersion `j : U ⟶ Spec(A)` and a quasi-coherent
`\mathcal O_U`-module `\mathcal F`, the canonical map
`\widetilde{H^0(U, \mathcal F)}|_U \to \mathcal F` is an isomorphism. -/
@[stacks 0EHM]
theorem isIso_tildeGlobalSectionsRestrictMap
    (j : U ⟶ Spec (.of A)) [IsOpenImmersion j] [QuasiCompact j]
    (ℱ : U.Modules) [ℱ.IsQuasicoherent] :
    IsIso (tildeGlobalSectionsRestrictMap j ℱ) := by
  dsimp [tildeGlobalSectionsRestrictMap]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
