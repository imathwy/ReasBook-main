import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap12.Lemma_12_7_2
import stacks_proof.stacks_project.Chap12.Lemma_12_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ModuleCat
open Module.Baer

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
@[stacks 03B8]
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
@[stacks 03B8]
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

/-- Helper for Remark 12.29.2: if restriction of scalars preserves injective objects, then the
ring map is flat. -/
private theorem flat_of_restrictScalars_preservesInjectiveObjects
    (hpres : (restrictScalars.{u} f).PreservesInjectiveObjects) :
    f.Flat := by
  -- Recover preservation of monomorphisms for the tensor left adjoint from the injective
  -- preservation hypothesis on restriction of scalars.
  letI : (restrictScalars.{u} f).PreservesInjectiveObjects := hpres
  have hExtendRightExact :
      rightExactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S) (extendScalars.{u, u, u} f) :=
    extendScalars_rightExact f
  letI : (extendScalars.{u, u, u} f).Additive :=
    CategoryTheory.functor_additive_of_leftExact_or_rightExact _ (.inr hExtendRightExact)
  letI : (extendScalars.{u, u, u} f).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
      (extendRestrictScalarsAdj f)
  -- Lemma 12.29.1 then upgrades mono preservation to exactness of extension of scalars.
  have hexact : exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
      (extendScalars.{u, u, u} f) := by
    exact
      (CategoryTheory.preservesMonomorphisms_iff_exact_of_leftAdjoint
        (adj := extendRestrictScalarsAdj f)).1 inferInstance
  -- Exactness gives finite-limit preservation, and after restricting scalars this is exactly
  -- preservation of finite limits by tensoring with `S` over `R`.
  letI : PreservesFiniteLimits (extendScalars.{u, u, u} f) :=
    (exactFunctor_iff (extendScalars.{u, u, u} f)).1 hexact |>.1
  have hcomp : PreservesFiniteLimits
      (extendScalars.{u, u, u} f ⋙ restrictScalars.{u} f) := by
    infer_instance
  have htensor : PreservesFiniteLimits
      (MonoidalCategory.tensorLeft ((restrictScalars.{u} f).obj (ModuleCat.of S S))) := by
    simpa using hcomp
  simpa [RingHom.Flat] using
    (Module.Flat.iff_preservesFiniteLimits_tensorLeft
      ((restrictScalars.{u} f).obj (ModuleCat.of S S))).2 htensor

/-- Companion bridge: over commutative rings, Remark 12.29.2 is equivalently the flatness of the
ring map `f`. -/
-- Proof sketch: `RingHom.Flat` is exactly the statement that `S` is flat as an `R`-module via the
-- ring map `f`; the forward implication is the classical injective-preservation criterion, and
-- the converse is the flat-base-change implication above.
theorem restrictScalars_preservesInjectiveObjects_iff_ringHomFlat :
    (restrictScalars.{u} f).PreservesInjectiveObjects ↔ f.Flat := by
  constructor
  · -- The source-faithful reverse direction runs through the adjunction criterion of Lemma 12.29.1.
    intro hpres
    exact flat_of_restrictScalars_preservesInjectiveObjects f hpres
  · -- Flatness gives exactness of extension of scalars, hence injective preservation on the right adjoint.
    intro hf
    exact restrictScalars_preservesInjectiveObjects_of_flat f hf

end

section

/-- Helper for Remark 12.29.2: a field is injective as a module over itself. -/
private theorem self_module_injective_of_field (K : Type u) [Field K] :
    Module.Injective K K := by
  -- Baer's criterion reduces injectivity to extending maps from ideals of the field.
  refine (Module.Baer.iff_injective).1 ?_
  intro I g
  rcases Ideal.eq_bot_or_top I with hI | hI
  · -- When the ideal is zero, the zero map is the unique extension.
    refine ⟨0, ?_⟩
    intro x hx
    have hxbot : x ∈ (⊥ : Ideal K) := by
      simpa [hI] using hx
    have hx0 : x = 0 := by
      simpa using hxbot
    have hsub : (⟨x, hx⟩ : I) = 0 := by
      ext
      exact hx0
    calc
      0 = g 0 := by simp
      _ = g ⟨x, hx⟩ := by rw [← hsub]
  · -- When the ideal is the whole field, evaluate `g` on the unique chosen representative.
    have hx_top : ∀ x : K, x ∈ I := by
      intro x
      simpa [hI]
    let gFun : K → K := fun x ↦ g ⟨x, hx_top x⟩
    have gFun_add : ∀ x y : K, gFun (x + y) = gFun x + gFun y := by
      intro x y
      simpa [gFun] using
        map_add g (⟨x, hx_top x⟩ : I) ⟨y, hx_top y⟩
    have gFun_smul : ∀ c x : K, gFun (c • x) = c • gFun x := by
      intro c x
      simpa [gFun] using
        map_smul g c (⟨x, hx_top x⟩ : I)
    let g' : K →ₗ[K] K :=
      { toFun := gFun
        map_add' := gFun_add
        map_smul' := gFun_smul }
    refine ⟨g', ?_⟩
    intro x hx
    have hsub : (⟨x, hx⟩ : I) = ⟨x, hx_top x⟩ := by
      apply Subtype.ext
      rfl
    simp [g', gFun, hsub]

/-- Over the field `ZMod p`, the object `ModuleCat.of (ZMod p) (ZMod p)` is injective. -/
-- Proof sketch: when `p` is prime, `ZMod p` is a field, so the underlying module is injective;
-- then use `Module.injective_iff_injective_object` to pass to the categorical owner statement.
theorem zmod_injective_as_self_object (p : ℕ) [Fact p.Prime] :
    Injective (ModuleCat.of (ZMod p) (ZMod p)) := by
  -- Prime residue fields are injective as modules over themselves by the field case above.
  have hmod : Module.Injective (ZMod p) (ZMod p) :=
    self_module_injective_of_field (ZMod p)
  exact (Module.injective_iff_injective_object (ZMod p) (ZMod p)).mp hmod

/-- Helper for Remark 12.29.2: an injective `ℤ`-module has surjective multiplication by every
nonzero integer. -/
private theorem surjective_zsmul_of_injective_int_module
    (J : Type u) [AddCommGroup J] (hJ : Module.Injective ℤ J) (n : ℤ) (hn : n ≠ 0) :
    Function.Surjective (n • · : J → J) := by
  intro x
  let I : Ideal ℤ := Ideal.span ({n} : Set ℤ)
  have hspan : ∀ m : ℤ, m * n ∈ I := by
    intro m
    refine Ideal.mem_span_singleton.mpr ?_
    refine ⟨m, ?_⟩
    ring
  let f : ℤ →ₗ[ℤ] I :=
    LinearMap.codRestrict I (LinearMap.toSpanSingleton ℤ ℤ n) hspan
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hmul : a * n = b * n := by
      simpa [f, LinearMap.toSpanSingleton_apply] using congrArg Subtype.val hab
    exact Int.eq_of_mul_eq_mul_right hn hmul
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton.mp y.2
    refine ⟨m, ?_⟩
    ext
    change m * n = y.1
    simpa [mul_comm] using hm.symm
  let e : ℤ ≃ₗ[ℤ] I := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let g : I →ₗ[ℤ] J := LinearMap.toSpanSingleton ℤ J x ∘ₗ e.symm.toLinearMap
  -- Evaluate the chosen generator of the principal ideal through the equivalence.
  have he1 : e 1 = ⟨n, Ideal.mem_span_singleton_self n⟩ := by
    apply Subtype.ext
    change (f 1 : ℤ) = n
    simp [f, I, LinearMap.toSpanSingleton_apply]
  have hgen : e.symm ⟨n, Ideal.mem_span_singleton_self n⟩ = 1 := by
    rw [← he1]
    exact e.left_inv 1
  have hg : g ⟨n, Ideal.mem_span_singleton_self n⟩ = x := by
    change e.symm ⟨n, Ideal.mem_span_singleton_self n⟩ • x = x
    rw [hgen]
    simp
  have hBaer : Module.Baer ℤ J := Module.Baer.of_injective hJ
  obtain ⟨h, hh⟩ := (iff_surjective.mp hBaer I) g
  refine ⟨h 1, ?_⟩
  -- Applying the extension identity at the generator `n` produces the desired preimage.
  have hx : h n = x := by
    have hcomp := congrArg (fun k : I →ₗ[ℤ] J ↦ k ⟨n, Ideal.mem_span_singleton_self n⟩) hh
    simpa [LinearMap.lcomp_apply, g] using hcomp.trans hg
  have hmap : h n = n • h 1 := by
    simpa using map_zsmul h n (1 : ℤ)
  exact hmap.symm.trans hx

/-- Helper for Remark 12.29.2: multiplication by `p` on `ZMod p` is not surjective. -/
private theorem zmod_prime_zsmul_not_surjective (p : ℕ) [Fact p.Prime] :
    ¬ Function.Surjective (((p : ℤ) • ·) : ZMod p → ZMod p) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj 1
  have hzero : ((p : ℤ) • x : ZMod p) = 0 := by
    calc
      ((p : ℤ) • x : ZMod p) = (p : ZMod p) * x := by
        simpa using (zsmul_eq_mul x (p : ℤ))
      _ = 0 := by simp
  have hone : (1 : ZMod p) = 0 := hx.symm.trans hzero
  exact one_ne_zero hone

/-- For prime `p`, the object `ModuleCat.of ℤ (ZMod p)` is not injective. -/
-- Proof sketch: identify `ZMod p` with `ℤ / pℤ` and use Baer's criterion to show that a nonzero
-- finite torsion abelian group is not injective; then translate with
-- `Module.injective_iff_injective_object`.
theorem zmod_not_injective_as_int_object (p : ℕ) [Fact p.Prime] :
    ¬ Injective (ModuleCat.of ℤ (ZMod p)) := by
  intro hI
  letI : Injective (ModuleCat.of ℤ (ZMod p)) := hI
  have hmod : Module.Injective ℤ (ZMod p) :=
    Module.injective_module_of_injective_object ℤ (ZMod p)
  have hp_ne_zero : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsurj : Function.Surjective (((p : ℤ) • ·) : ZMod p → ZMod p) :=
    surjective_zsmul_of_injective_int_module (ZMod p) hmod (p : ℤ) hp_ne_zero
  exact zmod_prime_zsmul_not_surjective p hsurj

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
