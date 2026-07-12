import Mathlib

open CategoryTheory Limits AlgebraicGeometry

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable (i0 i : I) (hi0i : i0 ≤ i)
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
variable (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)
variable (hf0 : f0 ≫ y0 = x0)
variable [CompactSpace ↥(D.obj i0)] [QuasiSeparatedSpace ↥(D.obj i0)]
variable [CompactSpace ↥X0] [QuasiSeparatedSpace ↥X0]
variable [CompactSpace ↥Y0] [QuasiSeparatedSpace ↥Y0]

-- Semantic recall via `lean_leansearch` was unavailable in this environment. The owner choice
-- below was verified against local Chapter 32 precedent and mathlib's canonical pullback API for
-- base change of morphisms of schemes.

/- Domain-style sampling for Situation 32.8.1:
- primary domain: a morphism of schemes over a distinguished stage of a directed inverse system of
  schemes with affine transition morphisms;
- canonical owners: `D : OrderDual I ⥤ Scheme`, `c : Cone D`, `hc : IsLimit c`, the qcqs
  instances on `D.obj i0`, `X0`, and `Y0`, the affine transition instances, the structure maps
  `x0 : X0 ⟶ D.obj i0` and `y0 : Y0 ⟶ D.obj i0`, and the compatibility equation
  `hf0 : f0 ≫ y0 = x0`;
- source/core/bridge triage:
  `source-facing`: the distinguished stage `S₀ = D.obj i0`, the morphism `f0 : X0 ⟶ Y0` over
    `S₀`, its stagewise base changes along `D.map (homOfLE hi0i) : D.obj i ⟶ D.obj i0`, and its
    limit base change along `c.π.app i0 : c.pt ⟶ D.obj i0`;
  `core/canonical`: the pullback schemes `pullback y0 (D.map (homOfLE hi0i))`,
    `pullback f0 (pullback.fst y0 (D.map (homOfLE hi0i)))`,
    `pullback y0 (c.π.app i0)`, and `pullback f0 (pullback.fst y0 (c.π.app i0))`;
  `bridge/view`: the induced base-changed morphisms
    `pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))` and
    `pullback.snd f0 (pullback.fst y0 (c.π.app i0))`.

This item only fixes ambient data and the canonical pullback representatives for the stagewise and
limit base changes, so the correct statement-stage formalization is a labeled recall block rather
than a new wrapper structure. The stage-`i` base change uses an explicit comparison `hi0i : i0 ≤ i`
so that the transition map to the distinguished stage is part of the public setup.
-/

/- Situation 32.8.1: let `S = lim_i S_i` be the limit of a directed inverse system of schemes with
affine transition morphisms. Fix a distinguished stage `S₀ = D.obj i0`, a morphism
`f0 : X0 ⟶ Y0` over `S₀` encoded by structure maps `x0 : X0 ⟶ D.obj i0`,
`y0 : Y0 ⟶ D.obj i0`, and a compatibility `hf0 : f0 ≫ y0 = x0`. Assume `S₀`, `X0`, and `Y0` are
quasi-compact and quasi-separated. For a stage `i` equipped with `hi0i : i0 ≤ i`, the canonical
stagewise base changes are represented by
`pullback y0 (D.map (homOfLE hi0i)) : Scheme`,
`pullback f0 (pullback.fst y0 (D.map (homOfLE hi0i))) : Scheme`, and the induced morphism
`pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))`. The limit base change to
`S = c.pt` is represented by `pullback y0 (c.π.app i0)`, `pullback f0 (pullback.fst y0 (c.π.app i0))`,
and `pullback.snd f0 (pullback.fst y0 (c.π.app i0))`. -/
#check c.pt
#check hc
#check (inferInstance : CompactSpace ↥(D.obj i0))
#check (inferInstance : QuasiSeparatedSpace ↥(D.obj i0))
#check (inferInstance : CompactSpace ↥X0)
#check (inferInstance : QuasiSeparatedSpace ↥X0)
#check (inferInstance : CompactSpace ↥Y0)
#check (inferInstance : QuasiSeparatedSpace ↥Y0)
#check (D.map (homOfLE hi0i))
#check (inferInstance : IsAffineHom (D.map (homOfLE hi0i)))
#check hf0
#check pullback y0 (D.map (homOfLE hi0i))
#check pullback.fst y0 (D.map (homOfLE hi0i))
#check pullback.snd y0 (D.map (homOfLE hi0i))
#check pullback f0 (pullback.fst y0 (D.map (homOfLE hi0i)))
#check pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))
#check c.π.app i0
#check pullback y0 (c.π.app i0)
#check pullback.fst y0 (c.π.app i0)
#check pullback.snd y0 (c.π.app i0)
#check pullback f0 (pullback.fst y0 (c.π.app i0))
#check pullback.snd f0 (pullback.fst y0 (c.π.app i0))

end
