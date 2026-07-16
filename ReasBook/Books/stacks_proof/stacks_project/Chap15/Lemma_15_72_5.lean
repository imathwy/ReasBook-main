import stacks_proof.stacks_project.Chap15.Lemma_15_72_1
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomologicalComplex
open MonoidalCategory
open MonoidalClosed
open BraidedCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
  [MonoidalCategory (CochainComplex (ModuleCat R) ℤ)]
  [BraidedCategory (CochainComplex (ModuleCat R) ℤ)]
  [MonoidalClosed (CochainComplex (ModuleCat R) ℤ)]
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for 15.72.5:
- primary domain: closed braided monoidal structure on cochain complexes of `R`-modules;
- sampled owner declarations:
  `MonoidalClosed.curry`,
  `MonoidalClosed.curry_eq`,
  `MonoidalClosed.pre`,
  `MonoidalClosed.uncurry_pre_app`;
- best owner abstraction: the canonical owner of the unit map is the curried braiding
  `curry ((β_ L K).hom)`, with the coevaluation composite only as its specification via
  `MonoidalClosed.curry_eq`;
- primitive data vs. derived API: the primitive data are the braiding `β_` and the closed-monoidal
  adjunction owner `curry`; the source-facing morphism `K ⟶ (L ⟶[CpxR] (K ⊗ L))` is the
  specialization of that owner to cochain complexes, while the coevaluation composite is derived
  API recording the same morphism in textbook form;
- source/core/bridge triage:
  `source-facing`: the Stacks morphism `K ⟶ (L ⟶[CpxR] (K ⊗ L))` and its naturality squares;
  `core/canonical`: `MonoidalClosed.curry`, `MonoidalClosed.uncurry`, `pre`, `(ihom L).map`,
    and `β_`;
  `bridge/view`: the source-order presentation of the curried braiding as a coevaluation composite.
-/
/- Lemma 15.72.5 is the source-facing transport of the closed-monoidal coevaluation map along the
braiding `L ⊗ K ≅ K ⊗ L`. -/

/-- Lemma 15.72.5: the canonical morphism
`K^• ⟶ (L^• ⟶[CpxR] (K^• ⊗ L^•))`
of cochain complexes of `R`-modules, obtained from the closed-monoidal coevaluation map by
transport across the braiding. -/
@[stacks 0A62]
noncomputable def tensor_totalization_internal_hom_unit
    (K L : CpxR) :
    K ⟶ (L ⟶[CpxR] (K ⊗ L)) :=
  curry ((β_ L K).hom)

/-- The canonical unit morphism is the coevaluation composite transported across the braiding. -/
theorem tensor_totalization_internal_hom_unit_spec
    (K L : CpxR) :
    tensor_totalization_internal_hom_unit K L =
      (ihom.coev L).app K ≫
        (ihom L).map (β_ L K).hom := by
  simp [tensor_totalization_internal_hom_unit, MonoidalClosed.curry_eq]

-- Proof sketch: uncurry both sides and use braiding naturality in the second variable.
/-- The canonical morphism is functorial in the left complex. -/
theorem tensor_totalization_internal_hom_unit_natural_left
    {K₁ K₂ L : CpxR} (α : K₁ ⟶ K₂) :
    CommSq
      α
      (tensor_totalization_internal_hom_unit K₁ L)
      (tensor_totalization_internal_hom_unit K₂ L)
      ((ihom L).map (α ▷ L)) := by
  -- Compare both sides after applying `MonoidalClosed.uncurry`, where the canonical map becomes
  -- the braiding `L ⊗ K ⟶ K ⊗ L`.
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  -- The owner naturality lemmas reduce the square to braiding naturality in the left variable.
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right]
  simp [tensor_totalization_internal_hom_unit]

-- Proof sketch: uncurry both sides, rewrite with `MonoidalClosed.uncurry_pre_app`, and use
-- braiding naturality in the first variable.
/-- The canonical morphism is functorial in the right complex. -/
theorem tensor_totalization_internal_hom_unit_natural_right
    (K : CpxR) {L₁ L₂ : CpxR}
    (β : L₁ ⟶ L₂) :
    CommSq
      (tensor_totalization_internal_hom_unit K L₂)
      (tensor_totalization_internal_hom_unit K L₁)
      ((pre β).app (K ⊗ L₂))
      ((ihom L₁).map (K ◁ β)) := by
  -- Compare both sides after applying `MonoidalClosed.uncurry`, where the right-variable map
  -- becomes precomposition on the internal-Hom side.
  refine CommSq.mk ?_
  apply MonoidalClosed.uncurry_injective
  -- The owner precomposition and naturality lemmas reduce the goal to braiding naturality in the
  -- right variable.
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_right]
  simp [tensor_totalization_internal_hom_unit]

end
