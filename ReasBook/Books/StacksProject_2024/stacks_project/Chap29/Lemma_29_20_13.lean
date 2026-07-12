import StacksProject_2024.Chap29.Definition_29_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme owners `LocallyQuasiFinite` and
  `Scheme.Hom.QuasiFiniteAt`, plus ring-level base-change stability for quasi-finiteness.
- Local Chapter 29 precedent records base change of `f : X ⟶ S` along `g : S' ⟶ S` as
  `pullback.snd f g`, with projection to `X` given by `pullback.fst f g`, and records the
  Stacks-facing global owner as `Scheme.Hom.QuasiFinite`.
- The Stacks tag evidence is consistent: item tag `01TM` and source URL
  `https://stacks.math.columbia.edu/tag/01TM`.
-/

/-- Lemma 29.20.13 (1): for a locally finite type morphism `f : X ⟶ S`, after base change by
`g : S' ⟶ S`, the quasi-finite locus of the base-changed morphism `pullback.snd f g` is exactly
the inverse image of the quasi-finite locus of `f` under the projection `pullback.fst f g`. -/
@[stacks 01TM]
theorem quasiFiniteAt_locus_pullback_snd [LocallyOfFiniteType f] :
    {x' : (pullback f g : Scheme) | (pullback.snd f g).QuasiFiniteAt x'} =
      (pullback.fst f g) ⁻¹' {x : X | f.QuasiFiniteAt x} := sorry

/-- Lemma 29.20.13 (2): any base change of a locally quasi-finite morphism of schemes is locally
quasi-finite. -/
@[stacks 01TM]
theorem locallyQuasiFinite_baseChange [LocallyQuasiFinite f] :
    LocallyQuasiFinite (pullback.snd f g) := sorry

/-- Any base change of a locally quasi-finite morphism is locally quasi-finite. -/
@[stacks 01TM, instance]
instance instLocallyQuasiFinitePullbackSndOfLocallyQuasiFinite [LocallyQuasiFinite f] :
    LocallyQuasiFinite (pullback.snd f g) := sorry

namespace Scheme.Hom

/-- Lemma 29.20.13 (3): any base change of a quasi-finite morphism of schemes is quasi-finite. -/
@[stacks 01TM]
theorem quasiFinite_baseChange [QuasiFinite f] :
    QuasiFinite (pullback.snd f g) := sorry

/-- Any base change of a quasi-finite morphism is quasi-finite. -/
@[stacks 01TM, instance]
instance instQuasiFinitePullbackSndOfQuasiFinite [QuasiFinite f] :
    QuasiFinite (pullback.snd f g) := sorry

end Scheme.Hom

end

end AlgebraicGeometry
