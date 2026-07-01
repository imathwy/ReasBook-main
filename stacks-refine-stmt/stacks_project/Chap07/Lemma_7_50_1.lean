import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Presheaf

universe v u

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {U : C} (S : Sieve U)

/- Domain-style sampling for Lemma 7.50.1:
- primary domain: Grothendieck-topology local equivalences and sieve inclusions into representable
  presheaves;
- sampled owner API:
  `Sieve.functorInclusion`,
  `Sieve.shrinkFunctor`,
  `Presieve.isSheafFor_iff_yonedaSheafCondition`,
  `Sieve.sieveOfUliftSubfunctor_uliftFunctorInclusion`,
  `GrothendieckTopology.mem_iff_isSheafFor_closedSieves`;
- source/core/bridge triage:
  `source-facing`: the covering condition `S ∈ J U` for a sieve `S` on `U`;
  `core/canonical`: the owner predicate `J.W` on presheaf morphisms, i.e. becoming an
    isomorphism after sheafification;
  `bridge/view`: the canonical sieve inclusion `S.functorInclusion : S.functor ⟶ yoneda.obj U`;
    the universe-lifted inclusion `S.uliftFunctorInclusion` is only an internal proof bridge for
    the large-universe local-bijectivity API.

Primitive data are only the sieve `S` and its canonical inclusion into the representable presheaf.
The sheaf condition for a sieve is derived API via `Presieve.isSheafFor_iff_yonedaSheafCondition`,
and `J.W` is the canonical owner predicate for the resulting extension bijection against sheaves.
The universe-lifted inclusion is useful only internally to access large-universe sheaf machinery in
the reverse implication; it should not remain on the public theorem surface.
-/

private theorem imageSieve_uliftFunctorInclusion_id :
    imageSieve S.uliftFunctorInclusion
        (show (CategoryTheory.uliftYoneda.obj.{u} U).obj (op U) from ULift.up (𝟙 U)) =
      S := by
  ext V g
  constructor
  · rintro ⟨t, ht⟩
    change ULift.up t.down.1 = ULift.up (g ≫ 𝟙 U) at ht
    have ht' : t.down.1 = g := by
      simpa using congrArg ULift.down ht
    simpa [ht'] using t.down.2
  · intro hg
    refine ⟨ULift.up ⟨g, by simpa using hg⟩, ?_⟩
    change ULift.up g = ULift.up (g ≫ 𝟙 U)
    simp

private theorem imageSieve_uliftFunctorInclusion_eq_pullback {V : C} (g : V ⟶ U) :
    imageSieve S.uliftFunctorInclusion
        (show (CategoryTheory.uliftYoneda.obj.{u} U).obj (op V) from ULift.up g) =
      S.pullback g := by
  let s : (CategoryTheory.uliftYoneda.obj.{u} U).obj (op U) := ULift.up (𝟙 U)
  have hpull := pullback_imageSieve S.uliftFunctorInclusion s g
  rw [imageSieve_uliftFunctorInclusion_id S] at hpull
  have hmap :
      imageSieve S.uliftFunctorInclusion
          (show (CategoryTheory.uliftYoneda.obj.{u} U).obj (op V) from ULift.up g) =
        imageSieve S.uliftFunctorInclusion ((CategoryTheory.uliftYoneda.obj.{u} U).map g.op s) :=
    by
    ext W h
    simp [imageSieve, s]
  exact hmap.trans hpull.symm

private theorem covering_of_W_uliftFunctorInclusion
    (hW :
      J.W
        (S.uliftFunctorInclusion :
          Sieve.uliftFunctor.{u} S ⟶ CategoryTheory.uliftYoneda.obj.{u} U)) :
    S ∈ J U := by
  let f : Sieve.uliftFunctor.{u} S ⟶ CategoryTheory.uliftYoneda.obj.{u} U :=
    S.uliftFunctorInclusion
  have hSurj : Presheaf.IsLocallySurjective J f :=
    hW.isLocallySurjective
  let s : (CategoryTheory.uliftYoneda.obj.{u} U).obj (op U) := ULift.up (𝟙 U)
  have hmem : imageSieve f s ∈ J U :=
    hSurj.imageSieve_mem s
  rw [imageSieve_uliftFunctorInclusion_eq_pullback S (𝟙 U), Sieve.pullback_id] at hmem
  exact hmem

private theorem W_uliftFunctorInclusion_of_W_functorInclusion
    (hW : J.W S.functorInclusion) :
    J.W
      (S.uliftFunctorInclusion :
        Sieve.uliftFunctor.{u} S ⟶ CategoryTheory.uliftYoneda.obj.{u} U) := by
  sorry

/-- Lemma 7.50.1: a sieve `S` on `U` is covering if and only if its canonical inclusion
`S.functorInclusion : S.functor ⟶ yoneda.obj U` becomes an isomorphism after sheafification. -/
theorem covering_iff_functorInclusion_becomes_iso_after_sheafification :
    S ∈ J U ↔ J.W S.functorInclusion := by
  constructor
  · intro hS P hP
    have hSheafFor : Presieve.IsSheafFor P S.arrows :=
      hP.isSheafFor S hS
    simpa [Presieve.YonedaSheafCondition, Function.bijective_iff_existsUnique] using
      Presieve.isSheafFor_iff_yonedaSheafCondition.1 hSheafFor
  · intro hW
    exact covering_of_W_uliftFunctorInclusion J S
      (W_uliftFunctorInclusion_of_W_functorInclusion J S hW)

end

end CategoryTheory.GrothendieckTopology
