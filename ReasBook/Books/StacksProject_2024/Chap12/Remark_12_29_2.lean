import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap12.Lemma_12_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ModuleCat

universe u

section

variable {R S : Type u} [Ring R] [Ring S]
variable (f : R →+* S)

/- Source/core/bridge triage for Remark 12.29.2:
- primary domain: change of rings for module categories, organized around exact restriction of
  scalars and adjunction criteria for preserving injective objects
- sampled owner declarations:
  * `ModuleCat.restrictScalars`
  * `ModuleCat.restrictCoextendScalarsAdj`
  * `CategoryTheory.rightExactFunctor_iff`
  * `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`
- best owner abstraction: for an arbitrary ring map, the owner is `restrictScalars f`; when the
  source speaks about a left adjoint, the faithful owner-level formulation is an abstract
  adjunction `v ⊣ restrictScalars f`, and the commutative tensor functor `extendScalars f` enters
  only as a bridge specialization
- primitive data: the ring map `f`
- derived API: exactness of `restrictScalars f`, right exactness of any left adjoint to it,
  preservation of injective objects under an exact left adjoint, and the commutative
  `extendScalars`/flatness specialization

Source/core/bridge triage:
- `source-facing`: the general change-of-rings remark for an arbitrary ring map, phrased at the
  owner `restrictScalars f` and an abstract left adjoint when needed
- `core/canonical`: `restrictScalars f`, `rightExactFunctor`, `exactFunctor`, and
  `CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`
- `bridge/view`: the commutative-ring specialization `extendScalars f ⊣ restrictScalars f`, its
  exactness under flatness, and the resulting flatness criterion for preservation of injectives
-/

/- Companion recall: module-theoretic injectivity agrees with the chapter owner notion
`CategoryTheory.Injective` in `ModuleCat`. -/
recall Module.injective_iff_injective_object

/-- Remark 12.29.2 (1): restriction of scalars along `f` is exact. -/
theorem restrictScalars_exact :
    exactFunctor (ModuleCat.{u} S) (ModuleCat.{u} R) (restrictScalars.{u} f) := by
  let G : ModuleCat.{u} R ⥤ AddCommGrpCat.{u} := forget₂ _ AddCommGrpCat
  have hlim : PreservesFiniteLimits (restrictScalars.{u} f) := by
    have : PreservesFiniteLimits (restrictScalars.{u} f ⋙ G) := by
      change PreservesFiniteLimits (forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u})
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves (restrictScalars.{u} f) G
  have hcolim : PreservesFiniteColimits (restrictScalars.{u} f) := by
    have : PreservesFiniteColimits (restrictScalars.{u} f ⋙ G) := by
      change PreservesFiniteColimits (forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u})
      infer_instance
    exact preservesFiniteColimits_of_reflects_of_preserves (restrictScalars.{u} f) G
  exact (exactFunctor_iff (restrictScalars.{u} f)).2 ⟨hlim, hcolim⟩

/-- Remark 12.29.2 (2): any left adjoint to restriction of scalars along `f` is right exact. -/
theorem rightExact_of_leftAdjoint_to_restrictScalars
    {v : ModuleCat.{u} R ⥤ ModuleCat.{u} S}
    (adj : v ⊣ restrictScalars.{u} f) :
    rightExactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S) v := by
  let _ : PreservesColimits v := adj.leftAdjoint_preservesColimits
  simpa [rightExactFunctor_iff] using (show PreservesFiniteColimits v from inferInstance)

/- Remark 12.29.2 (3): if a left adjoint to restriction of scalars along `f` is exact, then
restriction of scalars along `f` preserves injective objects. This is the canonical owner theorem
`CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint`, specialized to
`adj : v ⊣ restrictScalars f`. -/
recall CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint

end

section

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S)

/- Companion recall: in the commutative specialization, the canonical tensor left adjoint is
`extendScalars f`. -/
recall extendScalars

/- Companion recall: for a commutative ring map `f : R →+* S`, the abstract left adjoint from
Remark 12.29.2 is realized by `extendScalars f ⊣ restrictScalars f`. -/
recall extendRestrictScalarsAdj

/-- Companion bridge: in the commutative specialization, the left adjoint from Remark 12.29.2 (2)
is the canonical tensor functor `extendScalars f`, hence right exact. -/
theorem extendScalars_rightExact :
    rightExactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S) (extendScalars.{u, u, u} f) := by
  exact rightExact_of_leftAdjoint_to_restrictScalars f (extendRestrictScalarsAdj f)

/- Companion recall: flat ring maps make extension of scalars left exact. -/
recall preservesFiniteLimits_extendScalars_of_flat

/-- Companion bridge: a flat commutative ring map makes the tensor left adjoint exact. -/
theorem extendScalars_exact_of_flat (hf : f.Flat) :
    exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S) (extendScalars.{u, u, u} f) := by
  have hleft : PreservesFiniteLimits (extendScalars.{u, u, u} f) :=
    preservesFiniteLimits_extendScalars_of_flat hf
  exact (exactFunctor_iff (extendScalars.{u, u, u} f)).2
    ⟨hleft, (rightExactFunctor_iff (extendScalars.{u, u, u} f)).1 (extendScalars_rightExact f)⟩

/-- Companion bridge: if the commutative tensor left adjoint is exact, then restriction of scalars
preserves injective objects. -/
theorem restrictScalars_preservesInjectiveObjects_of_exact_extendScalars
    (hexact : exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S) (extendScalars.{u, u, u} f)) :
    (restrictScalars.{u} f).PreservesInjectiveObjects := by
  exact CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint
    (extendRestrictScalarsAdj f) hexact

/-- Companion bridge: if the commutative ring map `f` is flat, then restriction of scalars along
`f` preserves injective objects. -/
theorem restrictScalars_preservesInjectiveObjects_of_flat
    (hf : f.Flat) :
    (restrictScalars.{u} f).PreservesInjectiveObjects := by
  exact restrictScalars_preservesInjectiveObjects_of_exact_extendScalars f
    (extendScalars_exact_of_flat f hf)

/-- Companion bridge: over commutative rings, Remark 12.29.2 is equivalently the flatness of the
ring map `f`. -/
-- Proof sketch: `RingHom.Flat` is exactly the statement that `S` is flat as an `R`-module via the
-- ring map `f`; the forward implication is the classical injective-preservation criterion, and
-- the converse is the flat-base-change implication above.
theorem restrictScalars_preservesInjectiveObjects_iff_ringHomFlat :
    (restrictScalars.{u} f).PreservesInjectiveObjects ↔ f.Flat := sorry

end

section

/-- Over the field `ZMod p`, the object `ModuleCat.of (ZMod p) (ZMod p)` is injective. -/
-- Proof sketch: when `p` is prime, `ZMod p` is a field, so the underlying module is injective;
-- then use `Module.injective_iff_injective_object` to pass to the categorical owner statement.
theorem zmod_injective_as_self_object (p : ℕ) [Fact p.Prime] :
    Injective (ModuleCat.of (ZMod p) (ZMod p)) := sorry

/-- For prime `p`, the object `ModuleCat.of ℤ (ZMod p)` is not injective. -/
-- Proof sketch: identify `ZMod p` with `ℤ / pℤ` and use Baer's criterion to show that a nonzero
-- finite torsion abelian group is not injective; then translate with
-- `Module.injective_iff_injective_object`.
theorem zmod_not_injective_as_int_object (p : ℕ) [Fact p.Prime] :
    ¬ Injective (ModuleCat.of ℤ (ZMod p)) := sorry

/-- Counterexample in Remark 12.29.2: for the quotient map `ℤ → ℤ/pℤ`, restriction of scalars does
not preserve injective objects. -/
-- Proof sketch: `ZMod p` is injective over itself because it is a field, but it is not injective
-- as a `ℤ`-module. So the restriction-of-scalars functor along `ℤ → ℤ/pℤ` cannot preserve
-- injective objects.
theorem restrictScalars_intToZMod_not_preservesInjectiveObjects (p : ℕ) [Fact p.Prime] :
    ¬ (restrictScalars.{0} (Int.castRingHom (ZMod p))).PreservesInjectiveObjects := by
  intro hpres
  let F : ModuleCat.{0} (ZMod p) ⥤ ModuleCat.{0} ℤ :=
    restrictScalars.{0} (Int.castRingHom (ZMod p))
  letI : F.PreservesInjectiveObjects := hpres
  let X : ModuleCat.{0} (ZMod p) := ModuleCat.of (ZMod p) (ZMod p)
  have hX : Injective X := by
    simpa [X] using zmod_injective_as_self_object p
  have hbase : Injective (F.obj X) := F.injective_obj_of_injective hX
  let e : F.obj X ≅ ModuleCat.of ℤ (ZMod p) :=
    (show (F.obj X : Type) ≃ₗ[ℤ] ZMod p from
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun n x ↦ by
          simpa using
            int_smul_eq_zsmul
              (Module.compHom (ZMod p) (Int.castRingHom (ZMod p))) n x }).toModuleIso
  exact zmod_not_injective_as_int_object p <| Injective.of_iso e hbase

end
