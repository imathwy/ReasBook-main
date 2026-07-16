import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `IsClosedImmersion.overEquivIdealSheafData`;
-- local Chapter 30/31 precedent uses `X.IdealSheafData`, ideal-sheaf subobjects of the unit
-- module, finite categorical coproducts for direct sums, and the restriction notation `φ |_ U`.

/-- Lemma 30.12.2: let `X` be a Noetherian scheme, let `Z ⊆ X` be an integral closed
subscheme with generic point `ξ`, and let `ℱ` be a coherent `\mathcal O_X`-module whose stalk at
the image of `ξ` is annihilated by the maximal ideal of `\mathcal O_{X, ξ}`. Then there are a
natural number `r`, a coherent ideal sheaf `I ⊆ \mathcal O_Z`, and an injective morphism
`i_*(I^{\oplus r}) ⟶ ℱ` which is an isomorphism on some open neighbourhood of `ξ`. -/
@[stacks 01YE]
theorem exists_coherentIdeal_coproduct_pushforward_mono_isIso_near_generic
    {X : Scheme.{u}} [IsNoetherian X]
    (Z : X.IdealSheafData) [IsIntegral Z.subscheme]
    (ξ : Z.subscheme) (hξ : IsGenericPoint ξ (Set.univ : Set Z.subscheme))
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hξ_annihilated :
      ∀ a : X.presheaf.stalk (Z.subschemeι ξ),
        a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (Z.subschemeι ξ)) →
          ∀ m : (RingedSpace.stalkModuleCat ℱ (Z.subschemeι ξ)), a • m = 0) :
    ∃ (r : ℕ)
      (I : Subobject (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules)),
      ∃ _ : (Subobject.underlying.obj I : Z.subscheme.Modules).IsCoherent,
      ∃ _ : ((Scheme.Modules.pushforward Z.subschemeι).obj
          (∐ fun _ : Fin r ↦ (Subobject.underlying.obj I : Z.subscheme.Modules))).IsCoherent,
      ∃ φ : ((Scheme.Modules.pushforward Z.subschemeι).obj
          (∐ fun _ : Fin r ↦ (Subobject.underlying.obj I : Z.subscheme.Modules))) ⟶ ℱ,
        Mono φ ∧ ∃ (U : X.Opens) (_ : Z.subschemeι ξ ∈ U), IsIso (φ |_ U) := sorry

end AlgebraicGeometry.Scheme.Modules
