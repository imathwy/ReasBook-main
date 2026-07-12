import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable (i i' : I) (hii' : i ≤ i') (i0 : I)
variable [∀ j, CompactSpace ↥(D.obj j)]
variable [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]

-- Semantic recall: `lean_leansearch` surfaced the affine-transition limit API in
-- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`, especially `isAffineHom_π_app`; this item
-- only fixes the corresponding diagram, limit cone, qcqs stage hypotheses, and chosen index.

/- Domain-style sampling for Situation 32.4.5:
- primary domain: a directed inverse system of schemes with affine transition morphisms;
- canonical owners: `D : OrderDual I ⥤ Scheme`, `c : Cone D`, `hc : IsLimit c`,
  `CompactSpace ↥(D.obj i)`, `QuasiSeparatedSpace ↥(D.obj i)`, and
  `IsAffineHom (D.map (homOfLE hii'))`;
- source/core/bridge triage:
  `source-facing`: the limit scheme `S = lim_i S_i`, its projections `f_i : S ⟶ S_i`, and a
    chosen stage `0 ∈ I`;
  `core/canonical`: the chosen limit object `c.pt`, the cone legs `c.π.app i`, and the stagewise
    qcqs and affine-transition instances;
  `bridge/view`: the transition maps `D.map (homOfLE hii') : D.obj i' ⟶ D.obj i`.

This item only fixes ambient data and assumptions, so the correct statement-stage formalization is
a canonical recall block rather than a new wrapper structure.
-/

/- Situation 32.4.5: let `S = lim_i S_i` be the limit of a directed inverse system of schemes with
affine transition morphisms `f_{i',i} : S_{i'} ⟶ S_i`, assume every stage `S_i` is quasi-compact
and quasi-separated, denote the projections by `f_i : S ⟶ S_i`, and choose an element `0 ∈ I`.
In the canonical Lean owner, this is encoded by a diagram `D : OrderDual I ⥤ Scheme`, a limit
cone `c` with witness `hc`, stagewise instances `CompactSpace ↥(D.obj i)` and
`QuasiSeparatedSpace ↥(D.obj i)`, affine transition instances
`IsAffineHom (D.map (homOfLE hii'))`, and a chosen index `i0 : I` representing the source's
distinguished element `0 ∈ I`. -/
#check c.pt
#check c.π.app i
#check hc
#check (inferInstance : CompactSpace ↥(D.obj i))
#check (inferInstance : QuasiSeparatedSpace ↥(D.obj i))
#check (D.map (homOfLE hii'))
#check (inferInstance : IsAffineHom (D.map (homOfLE hii')))
#check i0

end
