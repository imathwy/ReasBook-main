import Mathlib
import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap17.Lemma_17_9_4
import StacksProject_2024.Chap17.Lemma_17_9_5
import StacksProject_2024.Chap17.Lemma_17_12_6
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped ModuleRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` highlighted stalk-locality APIs such as
-- `RingedSpace.exists_res_eq_zero_of_germ_eq_zero`; local Chapter 17 precedent then verified that
-- the right source-facing scheme-level skeleton should use `RingedSpace.stalkModuleCat`,
-- `RingedSpace.moduleStalkMap`, and the restriction notation `φ |_ U`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Lemma 30.9.5 (1): let `X` be a locally Noetherian scheme, let `ℱ` be a coherent
`\mathcal O_X`-module, and let `x ∈ X`. If the stalk `ℱ_x` is zero, then there exists an open
neighbourhood `U` of `x` such that the restriction `ℱ|_U` is the zero `\mathcal O_U`-module. -/
theorem exists_open_neighborhood_restriction_isZero_of_stalk_isZero
    (ℱ : X.Modules) [ℱ.IsCoherent] (x : X)
    (hℱx : IsZero (RingedSpace.stalkModuleCat ℱ x)) :
    ∃ (U : X.Opens) (_ : x ∈ U), IsZero (ℱ.over U) :=
  AlgebraicGeometry.exists_open_neighborhood_restriction_isZero_of_stalk_isZero ℱ x hℱx

/-- Lemma 30.9.5 (2): let `X` be a locally Noetherian scheme, let `𝒢` and `ℱ` be coherent
`\mathcal O_X`-modules, let `φ : 𝒢 ⟶ ℱ`, and let `x ∈ X`. If the stalk map
`φ_x : 𝒢_x → ℱ_x` is injective, then there exists an open neighbourhood `U` of `x` such that the
restricted morphism `φ|_U : 𝒢|_U ⟶ ℱ|_U` is injective, i.e. a monomorphism. -/
theorem exists_open_neighborhood_mono_restriction_of_stalk_injective
    {𝒢 ℱ : X.Modules} [𝒢.IsCoherent] [ℱ.IsCoherent]
    (φ : 𝒢 ⟶ ℱ) (x : X)
    (hφx : Function.Injective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : X.Opens) (_ : x ∈ U), Mono (φ |_ U) :=
  AlgebraicGeometry.exists_open_neighborhood_mono_restriction_of_stalk_mono φ x <|
    (ModuleCat.mono_iff_injective _).2 <| by
      simpa [RingedSpace.moduleStalkHom] using hφx

/-- Lemma 30.9.5 (3): let `X` be a locally Noetherian scheme, let `𝒢` and `ℱ` be coherent
`\mathcal O_X`-modules, let `φ : 𝒢 ⟶ ℱ`, and let `x ∈ X`. If the stalk map
`φ_x : 𝒢_x → ℱ_x` is surjective, then there exists an open neighbourhood `U` of `x` such that the
restricted morphism `φ|_U : 𝒢|_U ⟶ ℱ|_U` is surjective, i.e. an epimorphism. -/
theorem exists_open_neighborhood_epi_restriction_of_stalk_surjective
    {𝒢 ℱ : X.Modules} [𝒢.IsCoherent] [ℱ.IsCoherent]
    (φ : 𝒢 ⟶ ℱ) (x : X)
    (hφx : Function.Surjective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : X.Opens) (_ : x ∈ U), Epi (φ |_ U) :=
  SheafOfModules.exists_open_neighborhood_epi_restriction_of_stalk_surjective φ x hφx

/-- Owner-level companion to Lemma 30.9.5 (4): if the stalk morphism
`RingedSpace.moduleStalkHom x φ : 𝒢_x ⟶ ℱ_x` is an isomorphism, then after shrinking around `x`
the restricted morphism `φ|_U : 𝒢|_U ⟶ ℱ|_U` is an isomorphism. -/
theorem exists_open_neighborhood_isIso_restriction_of_stalk_isIso
    {𝒢 ℱ : X.Modules} [𝒢.IsCoherent] [ℱ.IsCoherent]
    (φ : 𝒢 ⟶ ℱ) (x : X) (hφx : IsIso (RingedSpace.moduleStalkHom x φ)) :
    ∃ (U : X.Opens) (_ : x ∈ U), IsIso (φ |_ U) := by
  have hφx_injective : Function.Injective (RingedSpace.moduleStalkMap x φ) := by
    exact ((CategoryTheory.isIso_iff_bijective (RingedSpace.moduleStalkHom x φ)).1 hφx).1
  have hφx_surjective : Function.Surjective (RingedSpace.moduleStalkMap x φ) := by
    exact ((CategoryTheory.isIso_iff_bijective (RingedSpace.moduleStalkHom x φ)).1 hφx).2
  rcases exists_open_neighborhood_mono_restriction_of_stalk_injective φ x hφx_injective with
    ⟨U, hxU, hmonoU⟩
  rcases exists_open_neighborhood_epi_restriction_of_stalk_surjective φ x hφx_surjective with
    ⟨V, hxV, hepiV⟩
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  letI : Mono ((Scheme.Modules.restrictFunctor (homOfLE inf_le_left)).map (φ |_ U)) :=
    Functor.map_mono (Scheme.Modules.restrictFunctor (homOfLE inf_le_left)) (φ |_ U)
  letI : Epi ((Scheme.Modules.restrictFunctor (homOfLE inf_le_right)).map (φ |_ V)) :=
    Functor.map_epi (Scheme.Modules.restrictFunctor (homOfLE inf_le_right)) (φ |_ V)
  haveI : Mono (φ |_ W) := by
    simpa [W, RingedSpace.moduleRestrictionMap] using
      (inferInstance :
        Mono ((Scheme.Modules.restrictFunctor (homOfLE inf_le_left)).map (φ |_ U)))
  haveI : Epi (φ |_ W) := by
    simpa [W, RingedSpace.moduleRestrictionMap] using
      (inferInstance :
        Epi ((Scheme.Modules.restrictFunctor (homOfLE inf_le_right)).map (φ |_ V)))
  exact ⟨W, hxW, isIso_of_mono_of_epi (φ |_ W)⟩

/-- Lemma 30.9.5 (4): let `X` be a locally Noetherian scheme, let `𝒢` and `ℱ` be coherent
`\mathcal O_X`-modules, let `φ : 𝒢 ⟶ ℱ`, and let `x ∈ X`. If the stalk map
`φ_x : 𝒢_x → ℱ_x` is bijective, then there exists an open neighbourhood `U` of `x` such that the
restricted morphism `φ|_U : 𝒢|_U ⟶ ℱ|_U` is an isomorphism. -/
theorem exists_open_neighborhood_isIso_restriction_of_stalk_bijective
    {𝒢 ℱ : X.Modules} [𝒢.IsCoherent] [ℱ.IsCoherent]
    (φ : 𝒢 ⟶ ℱ) (x : X)
    (hφx : Function.Bijective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : X.Opens) (_ : x ∈ U), IsIso (φ |_ U) := by
  have hφx_iso : IsIso (RingedSpace.moduleStalkHom x φ) :=
    (CategoryTheory.isIso_iff_bijective (RingedSpace.moduleStalkHom x φ)).2 <| by
      simpa [RingedSpace.moduleStalkHom] using hφx
  exact exists_open_neighborhood_isIso_restriction_of_stalk_isIso φ x hφx_iso

end AlgebraicGeometry.Scheme.Modules
