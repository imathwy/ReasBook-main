import Mathlib
import stacks_project.Chap15.Definition_15_37_3
import stacks_project.Chap15.Lemma_15_40_6

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open AdicCompletion
open IsLocalRing
open scoped TensorProduct

universe u v w

section

variable {A : Type u} {A' : Type v} {B : Type w}
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
variable [IsNoetherianRing A] [IsCompleteLocalRing A]
variable [IsNoetherianRing A'] [IsCompleteLocalRing A']
variable [IsNoetherianRing B] [IsCompleteLocalRing B]
variable [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A' B)]

local notation "κA" => ResidueField A
local notation "κA'" => ResidueField A'
local notation "ClosedFiberB" => Ideal.Fiber (maximalIdeal A') B
local notation "𝔪ClosedFiberB" => Ideal.map (algebraMap B ClosedFiberB) (maximalIdeal B)

variable (A) (A') in
private abbrev completedBaseChangeIdeal [CommRing A] [CommRing A'] [Algebra A A'] [IsLocalRing A]
    (C : Type*) [CommRing C] [Algebra A C] :
    Ideal (C ⊗[A] A') :=
  Ideal.map (algebraMap A (C ⊗[A] A')) (maximalIdeal A)

/-- The completed base change of an `A`-algebra `C` along the local map `A → A'`, completed with
respect to the ideal induced by `maximalIdeal A`. -/
abbrev completedBaseChange (A : Type u) (A' : Type v) [CommRing A] [CommRing A']
    [Algebra A A'] [IsLocalRing A] (C : Type*) [CommRing C] [Algebra A C] :=
  AdicCompletion (completedBaseChangeIdeal A A' C) (C ⊗[A] A')

/- Domain-style sampling for Remark 15.40.7:
- primary domain: complete local lifts with prescribed formally smooth closed fiber under a local
  base change with residue-field identification;
- sampled owner declarations:
  `Ideal.Fiber`,
  `Ideal.ResidueField.mapₐ`,
  `Algebra.TensorProduct.productMap`,
  `algebraMap A (C ⊗[A] A')`,
  `RingHom.adicCompletionMap`,
  `AdicCompletion.ofAlgEquiv`,
  `RingHom.formally_smooth_for_adic`,
  `exists_completeLocal_formallySmooth_lift_with_closedFiber`;
- best owner abstraction: the closed fiber should stay on the canonical owner
  `ClosedFiberB = Ideal.Fiber (maximalIdeal A') B`, and the comparison with
  the completed base change of `C` along `A → A'` should be the canonical `maximalIdeal A`-adic
  completion of `C ⊗[A] A'`, with comparison map induced by `algebraMap C B` and
  `algebraMap A' B`, not a separate wrapper predicate;
- primitive data: the local maps `A → A' → B`, the induced residue-field comparison
  on the maximal-ideal residue fields, and the adic formal smoothness of
  `κ(A') → ClosedFiberB`;
- derived API: the lifted complete local `A`-algebra `C`, the canonical completed base-change map
  `completedBaseChange C → B`, its surjectivity, and the surjective/finite/flat consequences.

Source/core/bridge triage:
- `source-facing`: the base-change variant of the complete-local lifting statement;
- `core/canonical`: `Ideal.Fiber`, `RingHom.formally_smooth_for_adic`, and
  `exists_completeLocal_formallySmooth_lift_with_closedFiber`, together with the completion owner
  `RingHom.adicCompletionMap`;
- `bridge/view`: the residue-field comparison on the closed fiber and the tensor-product
  presentation of the `maximalIdeal A`-adic completed base change before completion.
-/

variable (A) (A') (B) in
private abbrev tensorProductToTarget
    (C : Type*) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] :
    C ⊗[A] A' →+* B :=
  (Algebra.TensorProduct.productMap
    ((Algebra.ofId C B).restrictScalars A)
    ((Algebra.ofId A' B).restrictScalars A)).toRingHom

omit [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNoetherianRing A'] [IsCompleteLocalRing A']
  [IsNoetherianRing B] [IsCompleteLocalRing B] [IsLocalHom (algebraMap A A')]
  [IsLocalHom (algebraMap A' B)] in
private theorem tensorProductToTarget_comp_algebraMap
    {C : Type*} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] :
    (tensorProductToTarget A A' B C).comp
        (algebraMap A (C ⊗[A] A')) =
      algebraMap A B := by
  ext x
  simp [tensorProductToTarget]

omit [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNoetherianRing A']
  [IsCompleteLocalRing A'] [IsNoetherianRing B] [IsCompleteLocalRing B] in
private theorem baseChangeIdeal_le_comap_maximalIdeal
    {C : Type*} [CommRing C] [IsLocalRing A] [IsLocalRing B]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B] [hAA' : IsLocalHom (algebraMap A A')]
    [hA'B : IsLocalHom (algebraMap A' B)] :
    completedBaseChangeIdeal A A' C ≤
      Ideal.comap (tensorProductToTarget A A' B C)
        (maximalIdeal B) := by
  let _ : IsLocalHom (algebraMap A A') := hAA'
  let _ : IsLocalHom (algebraMap A' B) := hA'B
  letI : IsLocalHom (algebraMap A B) := by
    simpa [IsScalarTower.algebraMap_eq A A' B] using
      (RingHom.isLocalHom_comp (algebraMap A' B) (algebraMap A A') :
        IsLocalHom ((algebraMap A' B).comp (algebraMap A A')))
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, tensorProductToTarget_comp_algebraMap]
  exact Ideal.map_le_iff_le_comap.mp (IsLocalRing.map_maximalIdeal_le (algebraMap A B))

omit [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNoetherianRing A']
  [IsCompleteLocalRing A'] [IsNoetherianRing B] [IsCompleteLocalRing B]
  [IsLocalHom (algebraMap A A')] in
private theorem tensorProductToTarget_continuous
    {C : Type*} [CommRing C] [IsLocalRing A] [IsLocalRing B]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B] [hAA' : IsLocalHom (algebraMap A A')]
    [hA'B : IsLocalHom (algebraMap A' B)] :
    letI : TopologicalSpace (C ⊗[A] A') :=
      Ideal.adicTopology (completedBaseChangeIdeal A A' C)
    letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
    Continuous (tensorProductToTarget A A' B C) := by
  let _ : IsLocalHom (algebraMap A A') := hAA'
  let _ : IsLocalHom (algebraMap A' B) := hA'B
  rw [RingHom.continuous_adic_iff_exists_pow_map_le]
  refine ⟨1, ?_⟩
  have hle :
      completedBaseChangeIdeal A A' C ≤
        Ideal.comap (tensorProductToTarget A A' B C) (maximalIdeal B) :=
    baseChangeIdeal_le_comap_maximalIdeal
  simpa [pow_one] using Ideal.map_le_iff_le_comap.mpr hle

/-- The canonical completed base-change map
`completedBaseChange C → B` induced by `C → B` and `A' → B`. -/
noncomputable def completedBaseChangeMap (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B]
    [IsScalarTower A A' B] [IsLocalRing A] [IsCompleteLocalRing B]
    [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A' B)]
    (C : Type*) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] :
    completedBaseChange A A' C →+* B :=
  (AdicCompletion.ofAlgEquiv (maximalIdeal B)).symm.toRingHom.comp
    (RingHom.adicCompletionMap
      (tensorProductToTarget A A' B C)
      (completedBaseChangeIdeal A A' C) (maximalIdeal B)
      tensorProductToTarget_continuous)

-- Proof sketch: apply Lemma `15.40.6` to the formally smooth special fiber over the common residue
-- field, obtaining a Noetherian complete local `A`-algebra `C` with the required closed fiber.
-- Then use Lemma `15.37.5` to lift the special-fiber map into `B`, producing the arrow `C → B`,
-- hence the canonical `maximalIdeal A`-adic completed base-change map `completedBaseChange C → B`.
/-- Remark 15.40.7: for local homomorphisms `A → A' → B` of Noetherian complete local rings, if
`A → A'` induces an isomorphism on residue fields and the special fiber
`ClosedFiberB = Ideal.Fiber (maximalIdeal A') B`, canonically presented by `κ(A') ⊗[A'] B`, is
formally smooth over `κ(A')` for the adic topology defined by
`𝔪ClosedFiberB = Ideal.map (algebraMap B ClosedFiberB) (maximalIdeal B)`, then there exists a
Noetherian complete local `A`-algebra `C` together with a local map `C → B` such that `A → C` is
formally smooth for the `maximalIdeal C`-adic topology and the canonical
`maximalIdeal A`-adic completed base-change map `completedBaseChange C → B` is surjective. -/
theorem exists_completeLocal_formallySmooth_lift_over_local_baseChange
    (hκ : Function.Bijective (ResidueField.map (algebraMap A A')))
    (hfs :
      (algebraMap κA' ClosedFiberB).formally_smooth_for_adic 𝔪ClosedFiberB) :
    ∃ (C : Type*) (_ : CommRing C) (_ : Algebra A C) (_ : IsNoetherianRing C)
      (_ : IsCompleteLocalRing C) (_ : IsLocalHom (algebraMap A C)) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (_ : IsLocalHom (algebraMap C B)),
      (algebraMap A C).formally_smooth_for_adic (maximalIdeal C) ∧
        Function.Surjective (completedBaseChangeMap A A' B C) := sorry

-- Proof sketch: Nakayama's lemma applied to the identified closed fibers shows that the map on
-- successive quotients modulo powers of `maximalIdeal A` are surjective. When `A → A'` itself is
-- surjective, the zeroth stage already forces `C → B` to be surjective.
/-- If the base change `A → A'` is surjective, then surjectivity of the canonical completed
base-change map `completedBaseChange C → B` forces `C → B` to be surjective. -/
theorem surjective_of_surjective_base_of_completedBaseChangeMap
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C))
    (hAA' : Function.Surjective (algebraMap A A')) :
    Function.Surjective (algebraMap C B) := sorry

-- Proof sketch: first obtain surjectivity on all Artinian quotients from the closed-fiber
-- surjectivity of the completed base-change map by Nakayama. If `A'` is finite over `A`, the
-- completed-quotient argument identifies `B` as a finite `C`-module.
/-- If the intermediate extension `A → A'` is finite, then surjectivity of the canonical
completed base-change map makes `B` finite over `C`. -/
theorem finite_of_finite_base_of_completedBaseChangeMap
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C))
    [Module.Finite A A'] :
    Module.Finite C B := sorry

-- Proof sketch: once the completed base-change map is surjective, flatness of `A' → B` kills its
-- kernel on all Artinian quotients, so the map is bijective.
/-- If `A' → B` is flat, then a surjective canonical completed base-change map is bijective. -/
theorem completedBaseChangeMap_bijective_of_flat
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hflat : (algebraMap A' B).Flat)
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C)) :
    Function.Bijective (completedBaseChangeMap A A' B C) := sorry

/-- In the flat case, the canonical completed base-change map is an isomorphism. -/
noncomputable def completedBaseChangeRingEquivOfFlat
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hflat : (algebraMap A' B).Flat)
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C)) :
    completedBaseChange A A' C ≃+* B :=
  RingEquiv.ofBijective (completedBaseChangeMap A A' B C)
    (completedBaseChangeMap_bijective_of_flat hflat hbaseChange)

end
