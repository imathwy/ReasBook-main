import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / API check:
- the canonical owners for this item are
  `spread_out_unique_of_isGermInjective`,
  `spread_out_of_isGermInjective`, and `Scheme.IsGermInjectiveAt`;
- the source cases below are thin corollaries of those owners together with the existing
  `IsGermInjective` instances for integral and locally Noetherian schemes;
- shrinking to an open neighbourhood is expressed by an open subscheme `U : X.Opens` and its
  inclusion morphism `U.ι : U.toScheme ⟶ X`.
-/

section

variable {X Y S : Scheme.{u}} {fX : X ⟶ S} {fY : Y ⟶ S}
variable {x : X} {y : Y}
variable {f g : X ⟶ Y}

/-- Lemma 29.42.4 (1): if `X` is integral, then two morphisms `f, g : X ⟶ Y` with the same
value at `x` and the same induced stalk map at `x` agree on some open neighbourhood of `x`. -/
@[stacks 0BX6]
theorem exists_open_eq_of_stalkMap_eq_of_isIntegral
    [IsIntegral X]
    (hfgx : f x = g x)
    (hstalk : f.stalkMap x = Y.presheaf.stalkSpecializes (.of_eq hfgx.symm) ≫ g.stalkMap x) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  haveI : X.IsGermInjectiveAt x := inferInstance
  simpa using spread_out_unique_of_isGermInjective f g hfgx hstalk

/-- Lemma 29.42.4 (2): if `X` is locally Noetherian, then two morphisms `f, g : X ⟶ Y`
with the same value at `x` and the same induced stalk map at `x` agree on some open
neighbourhood of `x`. -/
@[stacks 0BX6]
theorem exists_open_eq_of_stalkMap_eq_of_isLocallyNoetherian
    [IsLocallyNoetherian X]
    (hfgx : f x = g x)
    (hstalk : f.stalkMap x = Y.presheaf.stalkSpecializes (.of_eq hfgx.symm) ≫ g.stalkMap x) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  haveI : X.IsGermInjectiveAt x := inferInstance
  simpa using spread_out_unique_of_isGermInjective f g hfgx hstalk

/-- Lemma 29.42.4 (3): if `X` is reduced with finitely many irreducible components, then two
morphisms `f, g : X ⟶ Y` with the same value at `x` and the same induced stalk map at `x`
agree on some open neighbourhood of `x`. -/
@[stacks 0BX6]
theorem exists_open_eq_of_stalkMap_eq_of_isReduced_of_finite_irreducibleComponents
    [IsReduced X] [Finite (irreducibleComponents X)]
    (hfgx : f x = g x)
    (hstalk : f.stalkMap x = Y.presheaf.stalkSpecializes (.of_eq hfgx.symm) ≫ g.stalkMap x) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  haveI : X.IsGermInjectiveAt x := by
    sorry
  simpa using spread_out_unique_of_isGermInjective f g hfgx hstalk

/-- Lemma 29.42.4 (5): if `Y` is locally of finite presentation over `S`, then any local
`\mathcal O_{S, s}`-algebra map `\mathcal O_{Y, y} → \mathcal O_{X, x}` is induced by a morphism
from an open neighbourhood of `x` to `Y`. -/
@[stacks 0BX6]
theorem exists_open_morphism_of_stalkMap_of_locallyOfFinitePresentation
    [LocallyOfFinitePresentation fY] [X.IsGermInjectiveAt x]
    (hxy : fX x = fY y)
    (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (hφ :
      fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧
        f ≫ fY = U.ι ≫ fX := by
  simpa using spread_out_of_isGermInjective fX fY hxy φ hφ

/-- Lemma 29.42.4 (6): if `Y` is locally of finite type over `S` and `X` is integral, then any
local `\mathcal O_{S, s}`-algebra map `\mathcal O_{Y, y} → \mathcal O_{X, x}` is induced by a
morphism from an open neighbourhood of `x` to `Y`. -/
@[stacks 0BX6]
theorem exists_open_morphism_of_stalkMap_of_locallyOfFiniteType_of_isIntegral
    [LocallyOfFiniteType fY] [IsIntegral X]
    (hxy : fX x = fY y)
    (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (hφ :
      fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧
        f ≫ fY = U.ι ≫ fX := by
  haveI : X.IsGermInjectiveAt x := inferInstance
  simpa using spread_out_of_isGermInjective fX fY hxy φ hφ

/-- Lemma 29.42.4 (7): if `Y` is locally of finite type over `S` and `X` is locally
Noetherian, then any local `\mathcal O_{S, s}`-algebra map `\mathcal O_{Y, y} →
\mathcal O_{X, x}` is induced by a morphism from an open neighbourhood of `x` to `Y`. -/
@[stacks 0BX6]
theorem exists_open_morphism_of_stalkMap_of_locallyOfFiniteType_of_isLocallyNoetherian
    [LocallyOfFiniteType fY] [IsLocallyNoetherian X]
    (hxy : fX x = fY y)
    (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (hφ :
      fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧
        f ≫ fY = U.ι ≫ fX := by
  haveI : X.IsGermInjectiveAt x := inferInstance
  simpa using spread_out_of_isGermInjective fX fY hxy φ hφ

/-- Lemma 29.42.4 (8): if `Y` is locally of finite type over `S` and `X` is reduced with
finitely many irreducible components, then any local `\mathcal O_{S, s}`-algebra map
`\mathcal O_{Y, y} → \mathcal O_{X, x}` is induced by a morphism from an open neighbourhood of
`x` to `Y`. -/
@[stacks 0BX6]
theorem exists_open_morphism_of_stalkMap_of_locallyOfFiniteType_of_isReduced_of_finite_irreducibleComponents
    [LocallyOfFiniteType fY] [IsReduced X] [Finite (irreducibleComponents X)]
    (hxy : fX x = fY y)
    (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (hφ :
      fY.stalkMap y ≫ φ = S.presheaf.stalkSpecializes (.of_eq hxy) ≫ fX.stalkMap x) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧
        f ≫ fY = U.ι ≫ fX := by
  haveI : X.IsGermInjectiveAt x := by
    sorry
  simpa using spread_out_of_isGermInjective fX fY hxy φ hφ

end

end AlgebraicGeometry
