import Mathlib.CategoryTheory.CommSq
import StacksProject_2024.Chap14.Definition_14_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SSet.stdSimplex
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory

/- Domain-style sampling for 25.9.1.1:
- primary domain: simplicial mapping objects out of `Δ[1]` and `Δ[0]`, together with the
  simplicial-object coskeleton unit;
- sampled owner API:
  `simplicialHom`,
  `simplicialCopowerIndexHom`,
  `SimplicialObject.Truncated.cosk`,
  `SimplicialObject.coskAdj`;
- source/core/bridge triage:
  `source-facing`: the displayed square
    `Hom(Δ[1], L)_{n + 1} ⟶ (cosk_n sk_n Hom(Δ[1], L))_{n + 1}`
    over the endpoint map `Hom(Δ[1], L) ⟶ Hom(Δ[0], L) × Hom(Δ[0], L)`;
  `core/canonical`: the unit natural transformation of the adjunction
    `SimplicialObject.truncation n ⊣ SimplicialObject.Truncated.cosk n`;
  `bridge/view`: the specialization of that naturality square to the endpoint-pair morphism built
    canonically from the two endpoint inclusions `Δ[0] ⟶ Δ[1]` through the Chapter 14 canonical
    precomposition owner `simplicial_hom_precomp` for simplicial mapping objects.

This sub-item adds no new owner. The refined file therefore names only the endpoint-pair morphism
and the specialized degree-`n + 1` naturality square needed downstream, without introducing a
parallel wrapper owner. -/

variable (n : ℕ)
variable [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ Type u,
  (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
variable (L : SSet.{u})
variable
    [∀ X : SSet.{u}, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : (Δ[0] : SSet.{u}).obj Δ ↦ X.obj Δ)]
    [∀ X : SSet.{u}, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : (Δ[1] : SSet.{u}).obj Δ ↦ X.obj Δ)]

variable [Functor.IsRepresentable (simplicialHomPresheaf (Δ[0] : SSet.{u}) L)]
variable [Functor.IsRepresentable (simplicialHomPresheaf (Δ[1] : SSet.{u}) L)]

/-- The canonical endpoint-pair map `Hom(Δ[1], L) ⟶ Hom(Δ[0], L) × Hom(Δ[0], L)`. -/
def simplicialHomDeltaOneEndpointPair :
    simplicialHom (Δ[1] : SSet.{u}) L ⟶
      simplicialHom (Δ[0] : SSet.{u}) L ⨯ simplicialHom (Δ[0] : SSet.{u}) L :=
  prod.lift
    (simplicial_hom_precomp (SSet.stdSimplex.δ (1 : Fin 2)) L)
    (simplicial_hom_precomp (SSet.stdSimplex.δ (0 : Fin 2)) L)

/- The source-facing public API is the endpoint-pair square, obtained by specializing the
naturality square of the `coskAdj` unit to the canonical endpoint-pair map. -/

@[simp] theorem simplicialHomDeltaOneEndpointPair_fst :
    simplicialHomDeltaOneEndpointPair L ≫ prod.fst =
      simplicial_hom_precomp (SSet.stdSimplex.δ (1 : Fin 2)) L := by
  simpa [simplicialHomDeltaOneEndpointPair] using
    (prod.lift_fst
      (simplicial_hom_precomp (SSet.stdSimplex.δ (1 : Fin 2)) L)
      (simplicial_hom_precomp (SSet.stdSimplex.δ (0 : Fin 2)) L))

@[simp] theorem simplicialHomDeltaOneEndpointPair_snd :
    simplicialHomDeltaOneEndpointPair L ≫ prod.snd =
      simplicial_hom_precomp (SSet.stdSimplex.δ (0 : Fin 2)) L := by
  simpa [simplicialHomDeltaOneEndpointPair] using
    (prod.lift_snd
      (simplicial_hom_precomp (SSet.stdSimplex.δ (1 : Fin 2)) L)
      (simplicial_hom_precomp (SSet.stdSimplex.δ (0 : Fin 2)) L))

/-- 25.9.1.1: the source map `Hom(Δ[1], L) ⟶ L × L`, written in the project API as
`Hom(Δ[1], L) ⟶ Hom(Δ[0], L) × Hom(Δ[0], L)`, is the canonical endpoint-pair morphism given by
the product of the two endpoint precomposition maps. The displayed square is the object-level
naturality square of the unit `X ⟶ cosk_n(sk_n X)` for that endpoint-pair morphism. -/
@[stacks 01GQ]
theorem simplicialHomDeltaOneEndpointPair_coskUnit_commSq :
    CommSq
      ((simplicialHomDeltaOneEndpointPair L).app (op ⦋n + 1⦌))
      (((coskAdj n).unit.app (simplicialHom (Δ[1] : SSet.{u}) L)).app (op ⦋n + 1⦌))
      (((coskAdj n).unit.app
          (simplicialHom (Δ[0] : SSet.{u}) L ⨯ simplicialHom (Δ[0] : SSet.{u}) L)).app
        (op ⦋n + 1⦌))
      ((((SimplicialObject.cosk n).map (simplicialHomDeltaOneEndpointPair L)).app
        (op ⦋n + 1⦌))) := by
  refine CommSq.mk ?_
  simpa using
    NatTrans.congr_app
      ((coskAdj n).unit.naturality (simplicialHomDeltaOneEndpointPair L))
      (op ⦋n + 1⦌)

/-- 25.9.1.1: the degree-`n + 1` square commutes as an equality of composites. -/
@[stacks 01GQ]
theorem simplicialHomDeltaOneEndpointPair_coskUnit_commutes :
    ((simplicialHomDeltaOneEndpointPair L).app (op ⦋n + 1⦌)) ≫
        (((coskAdj n).unit.app
          (simplicialHom (Δ[0] : SSet.{u}) L ⨯ simplicialHom (Δ[0] : SSet.{u}) L)).app
          (op ⦋n + 1⦌)) =
      (((coskAdj n).unit.app (simplicialHom (Δ[1] : SSet.{u}) L)).app (op ⦋n + 1⦌)) ≫
        ((((SimplicialObject.cosk n).map (simplicialHomDeltaOneEndpointPair L)).app
          (op ⦋n + 1⦌))) :=
  (simplicialHomDeltaOneEndpointPair_coskUnit_commSq n L).w

end CategoryTheory
