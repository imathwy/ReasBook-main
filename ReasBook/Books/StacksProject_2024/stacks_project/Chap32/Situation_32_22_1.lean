import Mathlib.Tactic.Recall
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Noetherian

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme) (c : Cone D) (hc : IsLimit c)
variable (i i' : I) (hii' : i ≤ i')
variable [∀ j, IsNoetherian (D.obj j)]
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]

/- Domain-style sampling for Situation 32.22.1:
- primary domain: inverse limits of scheme diagrams indexed by a directed preorder;
- canonical owners: `OrderDual I ⥤ Scheme`, `Cone D`, `IsLimit c`,
  `IsNoetherian (D.obj i)`, `IsAffineHom (D.map (homOfLE h))`, and
  `IsAffineHom (c.π.app i)`;
- source/core/bridge triage:
  `source-facing`: the directed inverse system `i ↦ S_i` together with its chosen limit scheme
    `S = lim_i S_i`;
  `core/canonical`: the diagram `D : OrderDual I ⥤ Scheme`, the limit cone `c`, and the
    typeclass owners for stagewise noetherianity and affine transition maps from
    `Mathlib.AlgebraicGeometry.AffineTransitionLimit`;
  `bridge/view`: the cone legs `c.π.app i : c.pt ⟶ D.obj i`, now equipped with their canonical
    affine owner, and the transition maps `D.map (homOfLE hii') : D.obj i' ⟶ D.obj i`.

This item only fixes ambient data and assumptions, so the correct statement-stage formalization is
a canonical recall block rather than a new wrapper structure. The owner choice was verified
against `Mathlib.AlgebraicGeometry.AffineTransitionLimit` and nearby Chapter 32 precedent.
-/

/- Situation 32.22.1: let `S = lim_i S_i` be the limit of a directed system of Noetherian
schemes with affine transition morphisms `S_{i'} ⟶ S_i` for `i ≤ i'`. In the canonical Lean
owner, this is a diagram `D : OrderDual I ⥤ Scheme`, a limit cone `c` with witness `hc`,
stagewise instances `IsNoetherian (D.obj i)`, and affine transition instances
`IsAffineHom (D.map (homOfLE hii'))`; the affine-transition-limit owner theorem
`isAffineHom_π_app` supplies the affine projection statement for `c.π.app i`. -/
#check c.pt
#check c.π.app i
#check hc
#check (inferInstance : IsNoetherian (D.obj i))
#check (D.map (homOfLE hii'))
#check (inferInstance : IsAffineHom (D.map (homOfLE hii')))
recall isAffineHom_π_app

end
