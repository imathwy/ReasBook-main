import Mathlib
import stacks_project.Chap14.Definition_14_26_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SimplicialObject
open MonoidalCategory
open Opposite
open SSet (const ι₀ ι₁)
open SSet.stdSimplex (asOrderHom isTerminalObj₀ obj₀Equiv objMk)
open scoped Simplicial

/- Domain-style sampling for Example 14.26.7:
- primary domain: simplicial homotopy equivalences in `SSet`, specialized to standard simplices;
- sampled owner API:
  `SimplicialObject.HomotopyEquiv`,
  `HomotopyEquiv.refl`,
  `SSet.Homotopy`,
  `SSet.const`,
  `SSet.stdSimplex.isTerminalObj₀`,
  `SSet.ι₀`,
  `SSet.ι₁`;
- best owner abstraction: the canonical owner is
  `SimplicialObject.HomotopyEquiv (Δ[m] : SSet) (Δ[0] : SSet)`;
- primitive data: the canonical terminal morphism `(SSet.stdSimplex.isTerminalObj₀).from
  (Δ[m] : SSet)`, the canonical constant map
  `SSet.const (obj₀Equiv.symm (Fin.last m)) : (Δ[0] : SSet) ⟶ Δ[m]`, and the explicit
  contraction homotopy of the composite `Δ[m] ⟶ Δ[0] ⟶ Δ[m]`;
- derived API: the strict identity on the `Δ[0]`-composite, the induced `Homotopic` witnesses,
  and the resulting morphism-level homotopy-equivalence property.

Source/core/bridge triage:
- `source-facing`: the homotopy equivalence between `Δ[m]` and `Δ[0]`;
- `core/canonical`: `SimplicialObject.HomotopyEquiv`;
- `bridge/view`: the degreewise contraction formula assembling the nontrivial homotopy datum. -/

namespace SSet.stdSimplex

-- Proof sketch: if the second simplicial coordinate has value `0`, the output follows the first
-- coordinate; once that coordinate becomes `1`, monotonicity of a simplex in `Δ[1]` forces it to
-- stay `1`, so the output is constantly the last vertex and remains monotone.
/-- Monotonicity of the pointwise formula defining the last-vertex contraction. -/
private theorem collapseToLastVertexApp_monotone (m : ℕ) (Δ : SimplexCategoryᵒᵖ)
    (z : (((Δ[m] : SSet) ⊗ Δ[1]).obj Δ)) :
    Monotone
      (fun k : Fin (Δ.unop.len + 1) ↦
        if asOrderHom z.2 k = 0 then asOrderHom z.1 k else Fin.last m) := sorry

variable (m : ℕ)

/-- The degreewise formula for collapsing `Δ[m] × Δ[1]` onto the last vertex. -/
private def collapseToLastVertexApp (Δ : SimplexCategoryᵒᵖ) :
    (((Δ[m] : SSet) ⊗ Δ[1]).obj Δ) → (Δ[m] : SSet).obj Δ :=
  fun z ↦
    objMk
      { toFun := fun k ↦
          if asOrderHom z.2 k = 0 then asOrderHom z.1 k else Fin.last m
        monotone' := collapseToLastVertexApp_monotone m Δ z }

-- Proof sketch: precomposing a pair `(φ, α)` with a simplicial operator acts on both coordinates
-- pointwise, and the defining formula `if α(k) = 0 then φ(k) else m` commutes with that
-- precomposition.
/-- Naturality of the degreewise last-vertex contraction formula. -/
private theorem collapseToLastVertex_naturality {Δ Δ' : SimplexCategoryᵒᵖ}
    (θ : Δ ⟶ Δ') (z : (((Δ[m] : SSet) ⊗ Δ[1]).obj Δ)) :
    collapseToLastVertexApp m Δ' (((Δ[m] : SSet) ⊗ Δ[1]).map θ z) =
      (Δ[m] : SSet).map θ (collapseToLastVertexApp m Δ z) := sorry

/-- The simplicial map `Δ[m] ⊗ Δ[1] ⟶ Δ[m]` that fixes the simplex at time `0`
and collapses it to the last vertex at time `1`. -/
private noncomputable def contractToLastVertexMap :
    (Δ[m] : SSet) ⊗ Δ[1] ⟶ Δ[m] where
  app Δ := collapseToLastVertexApp m Δ
  naturality := fun {_ _} θ ↦ funext (collapseToLastVertex_naturality m θ)

-- Proof sketch: along `ι₀`, the second coordinate is constantly `0`, so the defining formula
-- reduces to the first coordinate and hence to the identity on `Δ[m]`.
/-- The contraction formula restricts to the identity along the `0`-endpoint. -/
private theorem contractToLastVertexMap_h₀ :
    ι₀ ≫ contractToLastVertexMap m = 𝟙 (Δ[m] : SSet) := sorry

-- Proof sketch: along `ι₁`, the second coordinate is constantly `1`, so the defining formula
-- becomes the canonical constant simplex at the last vertex.
/-- The contraction formula restricts to the last-vertex constant map along the `1`-endpoint. -/
private theorem contractToLastVertexMap_h₁ :
    ι₁ ≫ contractToLastVertexMap m =
      isTerminalObj₀.from (Δ[m] : SSet) ≫ SSet.const (obj₀Equiv.symm (Fin.last m)) := by
  sorry

/-- The directed contraction of `Δ[m]` onto its last vertex. -/
private noncomputable def contractToLastVertexHomotopy :
    SSet.Homotopy (𝟙 (Δ[m] : SSet))
      (isTerminalObj₀.from (Δ[m] : SSet) ≫ SSet.const (obj₀Equiv.symm (Fin.last m))) where
  h := contractToLastVertexMap m
  h₀ := contractToLastVertexMap_h₀ m
  h₁ := contractToLastVertexMap_h₁ m
  rel := by
    ext Δ z
    exact False.elim z.1.2

/-- Example 14.26.7: the standard simplex `Δ[m]` is homotopy equivalent to the terminal simplex
`Δ[0]`, via the canonical terminal morphism to `Δ[0]`, the canonical constant map selecting the
last vertex, and the explicit last-vertex contraction. -/
noncomputable def homotopyEquivPoint :
    HomotopyEquiv (Δ[m] : SSet) (Δ[0] : SSet) where
  hom := isTerminalObj₀.from (Δ[m] : SSet)
  inv := SSet.const (obj₀Equiv.symm (Fin.last m))
  homotopyHomInvId := by
    simpa using
      (Homotopic.of_homotopy (contractToLastVertexHomotopy m).toSimplicialObjectHomotopy).symm
  homotopyInvHomId := by
    simpa using (Homotopic.refl (isTerminalObj₀.from (Δ[0] : SSet)))

end SSet.stdSimplex
