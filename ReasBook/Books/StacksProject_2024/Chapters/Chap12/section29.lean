import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_12_29_1 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Lemma 12.29.1:
- primary domain: adjunctions, exact functors, monomorphism preservation, and injective-object
  preservation in abelian and preadditive categories;
- sampled owner declarations:
  * `exactFunctor_iff`
  * `Functor.preservesHomology_of_preservesMonos_and_cokernels`
  * `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`
  * `Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`
- best owner abstraction: an adjunction `adj : v ⊣ u` together with the owner predicates
  `exactFunctor _ _ v`, `v.PreservesMonomorphisms`, and `u.PreservesInjectiveObjects`;
- primitive data: only the adjunction `adj`; additivity and exactness/mono/injective preservation
  remain owner-level properties rather than bundled local data;
- derived API: the source-facing bridges in parts `(1)` and `(2)`, and the direct owner recall in
  part `(3)`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma relating exactness of an additive left adjoint to preservation
  of monomorphisms, and then deducing preservation of injective objects for the right adjoint;
- `core/canonical`: `exactFunctor`, `Functor.PreservesMonomorphisms`,
  `Functor.PreservesInjectiveObjects`, and the owner adjunction criteria in mathlib;
- `bridge/view`: parts `(1)` and `(2)` below, which restate the textbook implications directly in
  terms of the owner predicates, while part `(3)` is the canonical owner theorem recalled as-is.
-/

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

variable {u : A ⥤ B} {v : B ⥤ A} [v.Additive]

/-- Lemma 12.29.1 (1): for additive functors `v ⊣ u` between abelian categories, `v` preserves
monomorphisms if and only if `v` is exact. -/
-- Proof sketch: a left adjoint preserves finite colimits by
-- `Adjunction.leftAdjoint_preservesColimits`. If `v` preserves monomorphisms, then this right
-- exactness, together with additivity and
-- `Functor.preservesHomology_of_preservesMonos_and_cokernels`, shows that `v` preserves finite
-- limits as well, hence is exact by `exactFunctor_iff`. Conversely, an exact functor preserves
-- finite limits, hence preserves monomorphisms.
theorem preservesMonomorphisms_iff_exact_of_leftAdjoint
    (adj : v ⊣ u)
    : v.PreservesMonomorphisms ↔ exactFunctor _ _ v := by
  constructor
  · intro hv
    letI : v.PreservesMonomorphisms := hv
    letI : PreservesColimits v := adj.leftAdjoint_preservesColimits
    letI : v.PreservesHomology := v.preservesHomology_of_preservesMonos_and_cokernels
    exact (exactFunctor_iff v).2 ⟨v.preservesFiniteLimits_of_preservesHomology, inferInstance⟩
  · intro hExact
    letI : PreservesFiniteLimits v := (exactFunctor_iff v).1 hExact |>.1
    infer_instance

end

section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {u : A ⥤ B} {v : B ⥤ A}

/-- Lemma 12.29.1 (2): if the left adjoint `v` is exact, then the right adjoint `u` preserves
injective objects. -/
-- Proof sketch: by part (1), exactness of the left adjoint `v` implies that `v` preserves
-- monomorphisms. Then
-- `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms` applied to
-- `adj : v ⊣ u` shows that `u` maps injective objects to injective objects.
theorem preservesInjectiveObjects_of_exact_leftAdjoint
    (adj : v ⊣ u)
    (hExact : exactFunctor _ _ v) :
    u.PreservesInjectiveObjects := by
  letI : v.PreservesMonomorphisms := by
    letI : PreservesFiniteLimits v := (exactFunctor_iff v).1 hExact |>.1
    infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

end

/- Lemma 12.29.1 (3): if `A` has enough injectives and the right adjoint `u` preserves injective
objects, then the left adjoint `v` preserves monomorphisms. This is exactly the canonical
adjunction criterion `Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`.
-/
recall Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects

end CategoryTheory

/-! ### Remark_12_29_2 (from Chap12) -/
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

/-! ### Lemma_12_29_3 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-
Domain-style sampling for Lemma 12.29.3:
- primary domain: adjunctions, exact functors, faithfulness / reflected monomorphisms, and enough
  injectives in abelian categories;
- sampled owner declarations:
  * `EnoughInjectives.of_adjunction`
  * `preservesMonomorphisms_iff_exact_of_leftAdjoint`
  * `Functor.faithful_of_exact_of_kernel_le_isZero`
  * the canonical instance `Functor.ReflectsMonomorphisms` from faithfulness;
- best owner abstraction: the adjunction `adj : v ⊣ u` together with the owner predicates
  `v.PreservesMonomorphisms`, `v.Faithful`, and `EnoughInjectives`;
- primitive data: `adj`, monomorphism preservation for `v`, and the source-facing zero-object
  detection hypothesis `hzero`;
- derived API: internally, exactness and faithfulness of `v`, with reflected monomorphisms coming
  from the canonical faithful-functor instance before applying `EnoughInjectives.of_adjunction`.

Source/core/bridge triage:
- `source-facing`: the Stacks criterion transferring enough injectives across an adjunction under
  the extra zero-object detection hypothesis;
- `core/canonical`: `EnoughInjectives.of_adjunction`;
- `bridge/view`: the internal derivation of `v.Faithful` from `hzero`.
-/

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {u : A ⥤ B} {v : B ⥤ A} [v.Additive]

/-- Lemma 12.29.3: if `u` is right adjoint to `v`, if `v` preserves monomorphisms, if `A` has
enough injectives, and if `v.obj X` being zero forces `X` to be zero, then `B` has enough
injectives. -/
-- Proof sketch: by Lemma 12.29.1 (1), the left adjoint `v` is exact. Exactness together with the
-- zero-detection hypothesis makes `v` faithful by
-- `Functor.faithful_of_exact_of_kernel_le_isZero`; the canonical faithful-functor instance then
-- gives `v.ReflectsMonomorphisms`. The owner theorem `EnoughInjectives.of_adjunction adj`
-- transfers enough injectives from `A` to `B`.
lemma enoughInjectives_of_rightAdjoint_of_preservesMonomorphisms
    (adj : v ⊣ u) [v.PreservesMonomorphisms] [EnoughInjectives A]
    (hzero : ∀ X : B, IsZero (v.obj X) → IsZero X) :
    EnoughInjectives B := by
  let hExact : exactFunctor B A v :=
    (preservesMonomorphisms_iff_exact_of_leftAdjoint adj).1 inferInstance
  letI : PreservesFiniteLimits v := (exactFunctor_iff v).1 hExact |>.1
  letI : PreservesFiniteColimits v := (exactFunctor_iff v).1 hExact |>.2
  letI : v.Faithful :=
    Functor.faithful_of_exact_of_kernel_le_isZero v <| show v.kernel ≤ IsZero from hzero
  exact EnoughInjectives.of_adjunction adj

end CategoryTheory

/-! ### Remark_12_29_4 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-
Domain-style sampling for Remark 12.29.4:
- primary domain: adjunctions, exact functors, faithfulness, and zero-object detection in abelian
  categories;
- sampled owner declarations:
  * `preservesMonomorphisms_iff_exact_of_leftAdjoint`
  * `Functor.faithful_of_exact_of_kernel_le_isZero`
  * `Functor.Faithful.map_injective`
  * `Functor.isZero`
- best owner abstraction: an adjunction `adj : v ⊣ u` together with the owner predicates
  `v.PreservesMonomorphisms` and `v.Faithful`; the textbook zero-object detection condition is the
  source-facing bridge to the faithful owner.
- primitive data: the adjunction `adj`, additivity of `v`, monomorphism preservation for `v`, and
  for the concrete zero-functor example a single nonzero object of `ModuleCat (ZMod 2)`; the
  adjunction between the two zero functors is a private bridge used only to verify the hypotheses
  of the example.
- derived API: exactness of `v`, preservation of zero morphisms by faithful left adjoints, and the
  concrete zero-functor counterexample on `ModuleCat (ZMod 2)`.

Source/core/bridge triage:
- `source-facing`: the remark's zero-object detection criterion and the counterexample via the zero
  functor;
- `core/canonical`: `exactFunctor`, `Functor.Faithful`, `Functor.isZero`, and the owner theorem
  `preservesMonomorphisms_iff_exact_of_leftAdjoint`;
- `bridge/view`: the iff theorem below, which translates the source wording into the canonical
  faithful-functor owner, plus the private zero-functor adjunction used in the counterexample.
-/

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

section

/-- The zero functors between abelian categories are adjoint. -/
private noncomputable def zeroAdjunction : (0 : B ⥤ A) ⊣ (0 : A ⥤ B) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        { toFun := fun _ ↦ 0
          invFun := fun _ ↦ 0
          left_inv := fun f ↦ (Functor.zero_obj X).eq_of_src _ _
          right_inv := fun g ↦ (Functor.zero_obj Y).eq_of_tgt _ _ }
      homEquiv_naturality_left_symm := by aesop_cat
      homEquiv_naturality_right := by aesop_cat }

/-- The zero functor between abelian categories preserves monomorphisms because it is exact. -/
private theorem zeroFunctor_preservesMonomorphisms : (0 : B ⥤ A).PreservesMonomorphisms := by
  let hZeroFunctor : IsZero (0 : B ⥤ A) :=
    Functor.isZero _ fun _ ↦ by simp
  letI : PreservesLimitsOfSize.{v₂, u₂} (0 : B ⥤ A) :=
    Functor.preservesLimitsOfSize_of_isZero _ hZeroFunctor
  letI : PreservesColimitsOfSize.{v₂, u₂} (0 : B ⥤ A) :=
    Functor.preservesColimitsOfSize_of_isZero _ hZeroFunctor
  let hExact : exactFunctor B A (0 : B ⥤ A) :=
    (exactFunctor_iff (0 : B ⥤ A)).2
      ⟨PreservesLimitsOfSize.preservesFiniteLimits (0 : B ⥤ A),
        PreservesColimitsOfSize.preservesFiniteColimits (0 : B ⥤ A)⟩
  exact (preservesMonomorphisms_iff_exact_of_leftAdjoint zeroAdjunction).2 hExact

/-- Remark 12.29.4: under the adjunction and monomorphism-preserving hypotheses of Lemma
12.29.3, the first sentence says that the condition that `v.obj X` being zero forces `X` to be
zero is equivalent to `v` being faithful. -/
-- Proof sketch: if `v` is faithful, then additivity gives preservation of zero morphisms, so
-- `v.map (𝟙 X) = 0` implies `𝟙 X = 0`, hence `X` is zero. Conversely, conditions (1) and (2)
-- imply that `v` is exact, and exactness plus the zero-object detection hypothesis force any
-- morphism mapped to zero by `v` to have zero coimage, hence to be the zero morphism.
theorem zeroObjectDetection_iff_faithful_of_rightAdjoint_of_preservesMonomorphisms
    (u : A ⥤ B) (v : B ⥤ A) [v.Additive] (adj : v ⊣ u)
    [v.PreservesMonomorphisms] :
    (∀ X : B, IsZero (v.obj X) → IsZero X) ↔ v.Faithful := by
  constructor
  · intro hzero
    let hExact : exactFunctor B A v :=
      (preservesMonomorphisms_iff_exact_of_leftAdjoint adj).1 inferInstance
    letI : PreservesFiniteLimits v := (exactFunctor_iff v).1 hExact |>.1
    letI : PreservesFiniteColimits v := (exactFunctor_iff v).1 hExact |>.2
    exact Functor.faithful_of_exact_of_kernel_le_isZero v <| show v.kernel ≤ IsZero from hzero
  · intro hfaithful
    letI : v.Faithful := hfaithful
    letI : v.IsLeftAdjoint := adj.isLeftAdjoint
    intro X hX
    refine (IsZero.iff_id_eq_zero X).2 <| v.zero_of_map_zero (𝟙 X) <| by
      simpa using (IsZero.iff_id_eq_zero (v.obj X)).1 hX

end

section ConcreteCounterexample

/-- Remark 12.29.4: taking both functors to be zero on `ModuleCat (ZMod 2)` gives a concrete
counterexample. The zero functor is adjoint to itself and preserves monomorphisms, but it neither
detects zero objects nor is faithful. -/
theorem zeroFunctor_counterexample :
    (0 : ModuleCat.{0} (ZMod 2) ⥤ ModuleCat.{0} (ZMod 2)).IsLeftAdjoint ∧
      (0 : ModuleCat.{0} (ZMod 2) ⥤ ModuleCat.{0} (ZMod 2)).PreservesMonomorphisms ∧
        (¬ ∀ X : ModuleCat.{0} (ZMod 2),
            IsZero (((0 : ModuleCat.{0} (ZMod 2) ⥤ ModuleCat.{0} (ZMod 2)).obj X)) → IsZero X) ∧
        ¬ (0 : ModuleCat.{0} (ZMod 2) ⥤ ModuleCat.{0} (ZMod 2)).Faithful := by
  let C := ModuleCat.{0} (ZMod 2)
  let X : C := ModuleCat.of (ZMod 2) (ZMod 2)
  have hX : ¬ IsZero X := by
    letI : Simple X := by infer_instance
    exact Simple.not_isZero X
  refine ⟨zeroAdjunction.isLeftAdjoint, zeroFunctor_preservesMonomorphisms, ?_, ?_⟩
  · intro hzero
    exact hX <| hzero X (Functor.zero_obj X)
  · intro hfaithful
    have hmap : (0 : C ⥤ C).map (𝟙 X) = (0 : C ⥤ C).map (0 : X ⟶ X) := by simp
    exact hX <| (IsZero.iff_id_eq_zero X).2 <| hfaithful.map_injective hmap

end ConcreteCounterexample

end CategoryTheory

/-! ### Lemma_12_29_5 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-
Source/core/bridge triage for Lemma 12.29.5:
- source-facing: the final construction of `HasFunctorialInjectiveEmbeddings B`.
- core/canonical: `Adjunction.injectivePresentationOfMap`, the owner
  `HasFunctorialInjectiveEmbeddings A`, and the exactness/faithfulness package from
  `enoughInjectives_of_rightAdjoint_of_preservesMonomorphisms`.
- bridge/view: the transferred arrow functor on `B`, obtained by applying the right adjoint `u` to
  the chosen injective targets of `v.obj X`.

The owner abstraction is `HasFunctorialInjectiveEmbeddings B`. The transferred arrow functor is
real mathematical bridge data here, so this file should construct it directly rather than routing
through the non-canonical intermediate statement `EnoughInjectives B`. -/

noncomputable section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (u : A ⥤ B) (v : B ⥤ A) [v.Additive] (adj : v ⊣ u)
variable [v.PreservesMonomorphisms] [HasFunctorialInjectiveEmbeddings A]

/-- The injective target in `B` obtained by applying the right adjoint to the chosen injective
target of `v.obj X`. -/
private noncomputable abbrev adjointInjectiveUnder (X : B) : B :=
  u.obj (HasFunctorialInjectiveEmbeddings.under (v.obj X))

/-- The transferred injective embedding of `X`. -/
private noncomputable abbrev adjointInjectiveι (X : B) :
    X ⟶ adjointInjectiveUnder u v X :=
  adj.homEquiv X _ (HasFunctorialInjectiveEmbeddings.ι (v.obj X))

/-- The morphism between transferred injective targets induced by `f`. -/
private noncomputable abbrev adjointInjectiveUnderMap {X Y : B} (f : X ⟶ Y) :
    adjointInjectiveUnder u v X ⟶ adjointInjectiveUnder u v Y :=
  u.map (HasFunctorialInjectiveEmbeddings.underMap (v.map f))

omit [Abelian A] [Abelian B] [v.Additive] [v.PreservesMonomorphisms] in
/-- Naturality of the transferred injective embeddings. -/
private lemma adjointInjectiveι_naturality {X Y : B} (f : X ⟶ Y) :
    CommSq
      f
      (adjointInjectiveι u v adj X)
      (adjointInjectiveι u v adj Y)
      (adjointInjectiveUnderMap u v f) := by
  have h :
      (adj.homEquiv X (HasFunctorialInjectiveEmbeddings.under (v.obj Y))).symm
          (f ≫ adjointInjectiveι u v adj Y) =
        (adj.homEquiv X (HasFunctorialInjectiveEmbeddings.under (v.obj Y))).symm
          (adjointInjectiveι u v adj X ≫ adjointInjectiveUnderMap u v f) := by
    rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm]
    simpa [adjointInjectiveι, adjointInjectiveUnderMap] using
      (HasFunctorialInjectiveEmbeddings.ι_naturality (v.map f)).w
  exact CommSq.mk <|
    (adj.homEquiv X (HasFunctorialInjectiveEmbeddings.under (v.obj Y))).symm.injective h

/-- The transferred injective-presentation arrow of `X`. -/
private noncomputable abbrev adjointInjectiveArrow (X : B) : Arrow B :=
  Arrow.mk (adjointInjectiveι u v adj X)

/-- The commutative square on transferred injective embeddings induced by `f`. -/
private noncomputable def adjointInjectiveArrowMap {X Y : B} (f : X ⟶ Y) :
    adjointInjectiveArrow u v adj X ⟶ adjointInjectiveArrow u v adj Y :=
  Arrow.homMk f (adjointInjectiveUnderMap u v f) (adjointInjectiveι_naturality u v adj f).w

/-- Lemma 12.29.5: if `u` is right adjoint to `v`, if `v` preserves monomorphisms, if `A`
has functorial injective embeddings, and if `v.obj X` being zero forces `X` to be zero, then `B`
has functorial injective embeddings. The separate enough-injectives hypothesis is absorbed by the
existing instance coming from functorial injective embeddings on `A`. -/
@[reducible]
def hasFunctorialInjectiveEmbeddings_of_rightAdjoint_of_preservesMonomorphisms
    (hzero : ∀ X : B, IsZero (v.obj X) → IsZero X) :
    HasFunctorialInjectiveEmbeddings B := by
  let hExact : exactFunctor B A v :=
    (preservesMonomorphisms_iff_exact_of_leftAdjoint adj).1 inferInstance
  letI : PreservesFiniteLimits v := (exactFunctor_iff v).1 hExact |>.1
  letI : PreservesFiniteColimits v := (exactFunctor_iff v).1 hExact |>.2
  letI : v.Faithful :=
    Functor.faithful_of_exact_of_kernel_le_isZero v <| show v.kernel ≤ IsZero from hzero
  refine
    { J :=
        { obj := adjointInjectiveArrow u v adj
          map := adjointInjectiveArrowMap u v adj
          map_id := by
            intro X
            ext
            · rfl
            ·
              simpa [adjointInjectiveArrowMap, adjointInjectiveUnderMap,
                HasFunctorialInjectiveEmbeddings.underMap]
                using congrArg Arrow.Hom.right (HasFunctorialInjectiveEmbeddings.J.map_id (v.obj X))
          map_comp := by
            intro X Y Z f g
            ext
            · rfl
            ·
              simpa [adjointInjectiveArrowMap, adjointInjectiveUnderMap,
                HasFunctorialInjectiveEmbeddings.underMap, Functor.map_comp]
                using congrArg Arrow.Hom.right
                  (HasFunctorialInjectiveEmbeddings.J.map_comp (v.map f) (v.map g)) }
      leftFunc_comp_J := rfl
      mono_obj := ?_
      injective_obj := ?_ }
  · intro X
    simpa [adjointInjectiveι] using
      (adj.injectivePresentationOfMap X
        (HasFunctorialInjectiveEmbeddings.presentation (v.obj X))).mono
  · intro X
    simpa [adjointInjectiveUnder] using
      adj.map_injective (HasFunctorialInjectiveEmbeddings.under (v.obj X))
        (HasFunctorialInjectiveEmbeddings.under_injective (v.obj X))

end

end CategoryTheory

/-! ### Lemma_12_29_6 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [HasColimitsOfShape WalkingParallelPair A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

namespace CategoryTheory.Functor

/-
Source/core/bridge triage for Lemma 12.29.6:
- source-facing: the Stacks hypothesis that an object property `P` generates `B` by quotients,
  together with corepresentability of `Hom_B(P₀, u(-))` for `P₀ ∈ P`;
- core/canonical: the Chapter 12 owner `ObjectProperty.HasEpiCover`, the owner predicate
  `u.leftAdjointObjIsDefined`, and the adjointness criterion
  `Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top`;
- bridge/view: the quotient presentation of an arbitrary `Y : B` by two objects of `P`, used to
  promote the source-facing hypothesis `P ≤ u.leftAdjointObjIsDefined` to
  `u.leftAdjointObjIsDefined = ⊤`.

Primitive data here are only the functor `u`, the object property `P`, the canonical
quotient-generating owner `[P.HasEpiCover]`, and the owner predicate on `P`. The cokernel
presentation of an arbitrary object is derived bridge data, so it should stay internal to the
proof of the owner equality rather than becoming a parallel public wrapper. -/

/-- If an object property `P` on `B` has epi covers and every object of `P` lies in the domain of
definition of the partial left adjoint of `u`, then the owner predicate
`u.leftAdjointObjIsDefined` is all of `B`. -/
theorem leftAdjointObjIsDefined_eq_top_of_hasEpiCover
    (u : A ⥤ B) (P : ObjectProperty B) [P.HasEpiCover]
    (hdefined : P ≤ u.leftAdjointObjIsDefined) :
    u.leftAdjointObjIsDefined = ⊤ := by
  ext Y
  constructor
  · intro _
    trivial
  · intro _
    have hcover : P.HasEpiCover := inferInstance
    obtain ⟨P₁, hP₁, f, hf⟩ := hcover.exists_epi Y
    haveI : Epi f := hf
    obtain ⟨P₂, hP₂, e, he⟩ := hcover.exists_epi (Limits.kernel f)
    haveI : Epi e := he
    let g : P₂ ⟶ P₁ := e ≫ Limits.kernel.ι f
    have hg : g ≫ f = 0 := by
      dsimp [g]
      simp
    have hc : IsColimit (CokernelCofork.ofπ f hg) := by
      refine CokernelCofork.IsColimit.ofπ' f hg ?_
      intro Z k hk
      have hkernel : Limits.kernel.ι f ≫ k = 0 := by
        apply (cancel_epi e).1
        simpa [g, Category.assoc] using hk
      exact ⟨Abelian.epiDesc f k hkernel, Abelian.comp_epiDesc f k hkernel⟩
    exact u.leftAdjointObjIsDefined_of_isColimit hc
      (fun j ↦ by
        cases j with
        | zero => exact hdefined _ hP₂
        | one => exact hdefined _ hP₁)

/-- Lemma 12.29.6: if an object property `P` on `B` generates `B` by quotients and the functors
`Hom_B(P₀, u(-))` are corepresentable for all objects `P₀` satisfying `P`, then `u` admits a
left adjoint. -/
theorem isRightAdjoint_of_quotient_generating_set_and_leftAdjointObjIsDefined
    (u : A ⥤ B) (P : ObjectProperty B) [P.HasEpiCover]
    (hdefined : P ≤ u.leftAdjointObjIsDefined) :
    u.IsRightAdjoint := by
  exact isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (leftAdjointObjIsDefined_eq_top_of_hasEpiCover u P hdefined)

end CategoryTheory.Functor
