import StacksProject_2024.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 29.43.16 (semantic recall / owner check):
`lean_leansearch` only recalled the general scheme-morphism owners `IsProper`, `QuasiCompact`,
and `IsAffineHom`. Local Chapter 29 precedent provides the intended source-facing owners
`Projective`, `HProjective`, `QuasiProjective`, and `HQuasiProjective`, while Chapter 28
represents an ample invertible sheaf on `S` by an existential `Scheme.Modules.Invertible` witness
together with `Scheme.Modules.IsAmple`.

The direct owner imports are not dependency-closed in this item check: importing
`Definition_29_40_1` or `Definition_29_43_1` rebuilds `Definition_29_37_1`, where synthesis of
`MonoidalCategory X.Modules` fails before this item elaborates. The intended source-facing
statements, once that owner path is available, are:

`theorem Projective.toHProjective_of_exists_isAmple
  {X S : Scheme} {f : X ⟶ S}
  (hS : ∃ (L : S.Modules) (hL : Scheme.Modules.Invertible L),
    @Scheme.Modules.IsAmple S inferInstance L hL)
  (hf : Projective f) : HProjective f`

and

`theorem QuasiProjective.toHQuasiProjective_of_exists_isAmple
  {X S : Scheme} {f : X ⟶ S}
  (hS : ∃ (L : S.Modules) (hL : Scheme.Modules.Invertible L),
    @Scheme.Modules.IsAmple S inferInstance L hL)
  (hf : QuasiProjective f) : HQuasiProjective f`.

The Stacks tag evidence is consistent: item tag `087S` matches the source URL ending in
`/tag/087S`. -/

#check fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ f
#check fun {S : Scheme.{u}} [MonoidalCategory S.Modules]
    (hS : ∃ (L : S.Modules) (hL : Scheme.Modules.Invertible L),
      @Scheme.Modules.IsAmple S inferInstance L hL) ↦ hS

end AlgebraicGeometry
