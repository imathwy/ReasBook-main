import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ModuleCat

universe u v

/-!
Domain-style sampling:
- primary domain: injective objects in `ModuleCat R`, obtained from injective abelian groups by the
  change-of-rings adjunction `restrictScalars ⊣ coextendScalars`;
- sampled owner declarations:
  `AddCommGrpCat.injective_of_divisible`,
  `AddCommGrpCat.injective_as_module_iff`,
  `ModuleCat.restrictCoextendScalarsAdj`,
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`;
- best owner abstraction:
  `source-facing`: `jModule R M`;
  `core/canonical`: categorical `Injective` in `ModuleCat`, together with preservation of
    injective objects by `coextendScalars (algebraMap ℤ R)`;
  `bridge/view`: `Module.injective_iff_injective_object`;
- primitive data: the ring `R` and the additive group `M`; the `R`-module structure on `M` does
  not enter the construction of `J(M)`;
- derived API: injectivity of `jModule R M` as an `R`-module.
-/

section

variable (R : Type u) [Ring R]
variable (M : Type v) [AddCommGroup M]

/-- The textbook module `J(M)`, realized by coextending scalars from the injective abelian group
of `ULift (ℚ/ℤ)`-valued functions on the character module `Mᵛ`. -/
noncomputable abbrev jModule : ModuleCat R :=
  (ModuleCat.coextendScalars (algebraMap ℤ R)).obj
    (ModuleCat.of ℤ (CharacterModule M → ULift.{max u v} (AddCircle (1 : ℚ))))

-- Proof sketch: the abelian group `(Mᵛ → ULift (ℚ/ℤ))` is a product of injective abelian groups,
-- so it is injective in `AddCommGrpCat`. The right adjoint `coextendScalars (algebraMap ℤ R)`
-- preserves injective objects, hence its image `jModule R M` is injective as an `R`-module.
/-- Lemma 15.55.8: for every `R`-module `M`, the module `J(M)`, formalized as `jModule R M`, is
injective. -/
@[stacks 01DC]
theorem jModule_injective :
    Module.Injective R (jModule R M) := by
  let A := CharacterModule M → ULift.{max u v} (AddCircle (1 : ℚ))
  let source : ModuleCat.{max u v} ℤ := ModuleCat.of ℤ A
  have hSource : Injective source := by
    let hGroup : Injective (AddCommGrpCat.of A) := AddCommGrpCat.injective_of_divisible A
    simpa [source, A] using (AddCommGrpCat.injective_as_module_iff A).mpr hGroup
  let res : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} ℤ :=
    restrictScalars (algebraMap ℤ R)
  let coext : ModuleCat.{max u v} ℤ ⥤ ModuleCat.{max u v} R :=
    coextendScalars (algebraMap ℤ R)
  have adj : res ⊣ coext := by
    simpa [res, coext] using restrictCoextendScalarsAdj (algebraMap ℤ R)
  have hTarget : Injective (coext.obj source) := by
    let _ : res.PreservesMonomorphisms := by infer_instance
    let _ : coext.PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
    exact coext.injective_obj_of_injective hSource
  simpa [jModule, source, A, coext, Module.injective_iff_injective_object R] using hTarget

end
