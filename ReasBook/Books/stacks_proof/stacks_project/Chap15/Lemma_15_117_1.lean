import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_116_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u v w x y z

/-
Domain-style sampling for Lemma 15.117.1:
- primary domain: finite tower stability of the Chapter 15 solution predicate for extensions of
  discrete valuation rings, with branchwise formal smoothness on reduced tensor-product integral
  closures;
- sampled owner declarations:
  `IsSolutionFor`,
  `formallySmoothForAdic_localization_baseChange_integralClosure`,
  `Localization.localRingHom`,
  `RingHom.formally_smooth_for_adic`;
- best owner abstraction: the source-facing theorem should remain stated directly with the owner
  predicate `IsSolutionFor`; the localized branch formal-smoothness statement is derived API and
  should be reused from `Lemma_15_115_3` rather than rebuilt through a local branch wrapper;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, the fraction
  fields `K ⊂ L`, and the finite tower `K ⊂ K₁ ⊂ K₂`; the branch localizations and their
  formal-smoothness properties are derived API.

Source/core/bridge triage:
- `source-facing`: `solutionFor_of_finite_extension`;
- `core/canonical`: `IsSolutionFor`, `Localization.localRingHom`,
  `RingHom.formally_smooth_for_adic`;
- `bridge/view`: `formallySmoothForAdic_localization_baseChange_integralClosure`.
-/

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y} {K2 : Type z}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra K K1] [Algebra A K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]
variable [Field K2] [Algebra K1 K2] [Algebra K K2] [Algebra A K2]
variable [IsScalarTower K K1 K2] [IsScalarTower A K K2] [IsScalarTower A K1 K2]
variable [FiniteDimensional K1 K2]

local notation "A1" => integralClosure A K1
local notation "A2" => integralClosure A K2
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "L2" => (L ⊗[K] K2) ⧸ nilradical (L ⊗[K] K2)
local notation "B1" => integralClosure B L1
local notation "B2" => integralClosure B L2

local instance : CommRing L1 :=
  Ideal.Quotient.commRing _

local instance : CommRing L2 :=
  Ideal.Quotient.commRing _

/-- Helper for Lemma 15.117.1: the field tower `K ⊂ K₁ ⊂ K₂` induces the canonical map on the
source integral closures `integralClosure A K₁ → integralClosure A K₂`. -/
noncomputable def sourceIntegralClosureTowerMap : A1 →ₐ[A] A2 :=
  (IsScalarTower.toAlgHom A K1 K2).mapIntegralClosure

/-- Helper for Lemma 15.117.1: the unreduced tensor tower map is induced by the identity on `L`
and the field extension map `K₁ → K₂`. -/
private noncomputable abbrev reducedTensorUnreducedTowerMap :
    (L ⊗[K] K1) →ₐ[B] (L ⊗[K] K2) :=
  (Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K K1 K2)).restrictScalars B

/-- Helper for Lemma 15.117.1: quotienting the unreduced tensor tower map by the nilradical of
the target gives the canonical map from the unreduced `K₁`-fiber to `L₂`. -/
private noncomputable abbrev reducedTensorTowerMapToQuotient :
    (L ⊗[K] K1) →ₐ[B] L2 :=
  (Ideal.Quotient.mkₐ B (nilradical (L ⊗[K] K2))).comp reducedTensorUnreducedTowerMap

/-- Helper for Lemma 15.117.1: the unreduced tensor tower map sends nilpotents to nilpotents, so
it kills the nilradical after quotienting to `L₂`. -/
private theorem reducedTensorUnreducedTowerMap_nilradical_maps_to_zero
    (x : L ⊗[K] K1) (hx : x ∈ nilradical (L ⊗[K] K1)) :
    (reducedTensorTowerMapToQuotient : (L ⊗[K] K1) →ₐ[B] L2) x = 0 := by
  -- Membership in the nilradical is exactly nilpotence, which is preserved by algebra maps.
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [mem_nilradical]
  rcases mem_nilradical.mp hx with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Compute in the unreduced target first; the quotient only enters when turning nilpotence into
  -- vanishing modulo the nilradical.
  simpa [reducedTensorUnreducedTowerMap, map_pow] using
    congrArg
      (fun y ↦
        (reducedTensorUnreducedTowerMap : (L ⊗[K] K1) →ₐ[B] (L ⊗[K] K2)) y) hn

/-- Helper for Lemma 15.117.1: the field tower `K ⊂ K₁ ⊂ K₂` induces the canonical reduced tensor
map `L₁ → L₂`. -/
private noncomputable abbrev reducedTensorQuotientTowerMap : L1 →ₐ[B] L2 :=
  Ideal.Quotient.liftₐ (R₁ := B) (I := nilradical (L ⊗[K] K1))
    reducedTensorTowerMapToQuotient
    reducedTensorUnreducedTowerMap_nilradical_maps_to_zero

/-- Helper for Lemma 15.117.1: the reduced tensor tower map induces the canonical map on the
integral closures over `B`. -/
noncomputable def reduced_tensor_integralClosure_tower_map : B1 →ₐ[B] B2 :=
  reducedTensorQuotientTowerMap.mapIntegralClosure

/-- Helper for Lemma 15.117.1: the second source integral closure is integral over the first one
along the canonical tower map. -/
private lemma sourceIntegralClosure_tower_isIntegral :
    let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
    Algebra.IsIntegral A1 A2 := by
  -- Every element of `A₂` is already integral over `A`, hence also integral over `A₁`.
  let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
  exact Algebra.IsIntegral.tower_top A

/-- Helper for Lemma 15.117.1: contracting a maximal ideal of `integralClosure A K₂` to
`integralClosure A K₁` along the canonical tower map stays maximal. -/
private lemma contracted_source_isMaximal
    (p2 : Ideal A2) [p2.IsMaximal] :
    let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
    (p2.under A1).IsMaximal := by
  -- View the contraction as a comap along the integral map `A₁ → A₂`.
  let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
  let _ : Algebra.IsIntegral A1 A2 := sourceIntegralClosure_tower_isIntegral
  simpa [Ideal.under_def, sourceIntegralClosureTowerMap] using
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p2 :
      (Ideal.comap (algebraMap A1 A2) p2).IsMaximal)

/-- Helper for Lemma 15.117.1: the two canonical routes `A₁ → B₂` through the source and target
towers agree pointwise. -/
private lemma source_to_target_tower_map_commutes (x : A1) :
    let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
    reduced_tensor_integralClosure_tower_map
        (reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K1) x) =
      reducedTensorBaseChangeIntegralClosureMap
        (A := A) (B := B) (K := K) (L := L) (K1 := K2)
        (sourceIntegralClosureTowerMap x) := by
  let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
  -- Compare both sides in the ambient reduced tensor field `L₂`; after unfolding the tower maps,
  -- both routes are literally induced by the same right tensor-factor inclusion `K₁ → K₂`.
  ext
  change
    reducedTensorQuotientTowerMap
        (((reducedTensorBaseChangeIntegralClosureMap
            (A := A) (B := B) (K := K) (L := L) (K1 := K1) x : B1) : L1)) =
      (((reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K2)
          (sourceIntegralClosureTowerMap x) : B2) : L2))
  -- Route correction: normalize both codomain-restricted maps to their ambient reduced-tensor
  -- values before unfolding the tower maps on the right tensor factor.
  dsimp [reducedTensorBaseChangeIntegralClosureMap, sourceIntegralClosureTowerMap,
    reducedTensorQuotientTowerMap, reducedTensorTowerMapToQuotient, reducedTensorUnreducedTowerMap]
  rfl

/-- Helper for Lemma 15.117.1: the two canonical owner maps `A₁ → B₂` through `B₁` and `A₂`
agree as ring homomorphisms. -/
private lemma source_to_target_tower_map_comp_eq :
    let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
    reduced_tensor_integralClosure_tower_map.toRingHom.comp
        (reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K1)).toRingHom =
      (reducedTensorBaseChangeIntegralClosureMap
        (A := A) (B := B) (K := K) (L := L) (K1 := K2)).toRingHom.comp
        sourceIntegralClosureTowerMap.toRingHom := by
  let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
  -- Promote the pointwise commutative square to an equality of the underlying ring maps.
  ext x
  simpa [RingHom.comp_apply] using
    (source_to_target_tower_map_commutes
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) x)

/-- Helper for Lemma 15.117.1: after composing with the inclusion `B₂ → L₂`, the two canonical
routes `A₁ → B₂` become equal as ring homomorphisms into the ambient reduced tensor field `L₂`. -/
private lemma source_to_target_tower_map_comp_val_eq :
    let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
    (((integralClosure B L2).val).toRingHom.comp
        reduced_tensor_integralClosure_tower_map.toRingHom).comp
        (reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K1)).toRingHom =
      (((integralClosure B L2).val).toRingHom.comp
        (reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K2)).toRingHom).comp
        sourceIntegralClosureTowerMap.toRingHom := by
  let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
  -- The ambient `L₂` comparison is just the pointwise commutative square, promoted by `ext`.
  ext x
  change
    (((reduced_tensor_integralClosure_tower_map
        (reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K1) x) : B2) : L2)) =
      (((reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K2)
          (sourceIntegralClosureTowerMap x) : B2) : L2))
  simpa using congrArg (fun y : B2 ↦ (y : L2)) (source_to_target_tower_map_commutes (x := x))

/-- Helper for Lemma 15.117.1: once the canonical source tower algebra structure is installed,
the map `A₁ → A₂` is definitionally the ambient algebra map. -/
private lemma sourceIntegralClosureTowerMap_eq_algebraMap :
    let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
    sourceIntegralClosureTowerMap.toRingHom = algebraMap A1 A2 := by
  let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
  rfl

/-- Helper for Lemma 15.117.1: the canonical reduced-tensor map `A₁ → B₁` is definitionally the
ambient `A₁`-algebra map. -/
private lemma reducedTensorBaseChangeIntegralClosureMap_eq_algebraMap_source :
    (reducedTensorBaseChangeIntegralClosureMap
      (A := A) (B := B) (K := K) (L := L) (K1 := K1)).toRingHom = algebraMap A1 B1 := by
  rfl

/-- Helper for Lemma 15.117.1: the canonical reduced-tensor map `A₂ → B₂` is definitionally the
ambient `A₂`-algebra map. -/
private lemma reducedTensorBaseChangeIntegralClosureMap_eq_algebraMap_target :
    (reducedTensorBaseChangeIntegralClosureMap
      (A := A) (B := B) (K := K) (L := L) (K1 := K2)).toRingHom = algebraMap A2 B2 := by
  rfl

/-- Helper for Lemma 15.117.1: once the canonical target tower algebra structure is installed,
the map `B₁ → B₂` is definitionally the ambient algebra map. -/
private lemma reduced_tensor_integralClosure_tower_map_eq_algebraMap :
    let _ : Algebra B1 B2 := reduced_tensor_integralClosure_tower_map.toAlgebra
    reduced_tensor_integralClosure_tower_map.toRingHom = algebraMap B1 B2 := by
  let _ : Algebra B1 B2 := reduced_tensor_integralClosure_tower_map.toAlgebra
  rfl

/-- Helper for Lemma 15.117.1: the canonical target tower map agrees with the ambient base map on
elements coming from `B`. -/
private lemma reduced_tensor_integralClosure_tower_map_commutes_base (b : B) :
    reduced_tensor_integralClosure_tower_map (algebraMap B B1 b) = algebraMap B B2 b := by
  -- The target tower map is a `B`-algebra homomorphism, so it commutes with the base map by
  -- definition.
  exact (reduced_tensor_integralClosure_tower_map : B1 →ₐ[B] B2).commutes b

/-- Helper for Lemma 15.117.1: contracting a maximal `K₂`-branch along the canonical target
tower `B₁ → B₂` preserves maximality. -/
private lemma contracted_target_isMaximal_under_tower
    (q2 : Ideal B2) [q2.IsMaximal] :
    (Ideal.comap
      (reduced_tensor_integralClosure_tower_map
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2)).toRingHom q2).IsMaximal := by
  let F : B1 →ₐ[B] B2 :=
    reduced_tensor_integralClosure_tower_map
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2)
  let _ : Algebra B1 B2 := F.toAlgebra
  let _ : IsScalarTower B B1 B2 := by
    -- The canonical target-tower map extends the base map `B → B₂`.
    refine IsScalarTower.of_algebraMap_eq fun b ↦ ?_
    simpa [reduced_tensor_integralClosure_tower_map_eq_algebraMap
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2)] using
      (reduced_tensor_integralClosure_tower_map_commutes_base
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) b).symm
  have hIntegral :
      F.toRingHom.IsIntegral := by
    intro z
    -- Every element of `B₂` is integral over `B`, hence also over `B₁` through the local tower.
    exact (show IsIntegral B z from z.2).tower_top
  let _ : Algebra.IsIntegral B1 B2 := hIntegral
  simpa [reduced_tensor_integralClosure_tower_map_eq_algebraMap
    (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2)] using
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q2 :
      (Ideal.comap (algebraMap B1 B2) q2).IsMaximal)

/-- Helper for Lemma 15.117.1: contracting a `K₂`-branch first to `B₁` and then to `A₁` agrees
with contracting the source branch first to `A₂` and then to `A₁`. -/
private lemma contracted_target_under_eq_source_contraction
    (p2 : Ideal A2) (q2 : Ideal B2) [q2.LiesOver p2] :
    let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
    let _ : Algebra B1 B2 := reduced_tensor_integralClosure_tower_map.toAlgebra
    ((q2.under B1).under A1) = p2.under A1 := by
  let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
  let _ : Algebra B1 B2 := reduced_tensor_integralClosure_tower_map.toAlgebra
  have hsquare :
      reduced_tensor_integralClosure_tower_map.toRingHom.comp
          (reducedTensorBaseChangeIntegralClosureMap
            (A := A) (B := B) (K := K) (L := L) (K1 := K1)).toRingHom =
        (reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := B) (K := K) (L := L) (K1 := K2)).toRingHom.comp
          sourceIntegralClosureTowerMap.toRingHom := by
    -- Compare the two owner routes `A₁ → B₂` directly before expanding contractions.
    exact
      (source_to_target_tower_map_comp_eq
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2))
  -- After expanding both contractions as iterated comaps, the square identity and the lies-over
  -- equality for `q₂` identify the two resulting ideals of `A₁`.
  calc
    ((q2.under B1).under A1) =
        Ideal.comap
          (reduced_tensor_integralClosure_tower_map.toRingHom.comp
            (reducedTensorBaseChangeIntegralClosureMap
              (A := A) (B := B) (K := K) (L := L) (K1 := K1)).toRingHom) q2 := by
          rw [Ideal.under_def, Ideal.under_def, Ideal.comap_comap]
          rw [reduced_tensor_integralClosure_tower_map_eq_algebraMap]
          rw [reducedTensorBaseChangeIntegralClosureMap_eq_algebraMap_source]
    _ = Ideal.comap
          ((reducedTensorBaseChangeIntegralClosureMap
            (A := A) (B := B) (K := K) (L := L) (K1 := K2)).toRingHom.comp
            sourceIntegralClosureTowerMap.toRingHom) q2 := by
          rw [hsquare]
    _ = Ideal.comap sourceIntegralClosureTowerMap.toRingHom
          (Ideal.comap
            (reducedTensorBaseChangeIntegralClosureMap
              (A := A) (B := B) (K := K) (L := L) (K1 := K2)).toRingHom q2) := by
          rw [Ideal.comap_comap]
    _ = p2.under A1 := by
          have hq2_over :
              Ideal.comap
                  (reducedTensorBaseChangeIntegralClosureMap
                    (A := A) (B := B) (K := K) (L := L) (K1 := K2)).toRingHom q2 = p2 := by
            simpa [reducedTensorBaseChangeIntegralClosureMap_eq_algebraMap_target
              (A := A) (B := B) (K := K) (L := L) (K2 := K2), Ideal.under_def] using
              (q2.over_def p2).symm
          rw [hq2_over]
          change Ideal.comap sourceIntegralClosureTowerMap.toRingHom p2 =
            Ideal.comap (algebraMap A1 A2) p2
          rw [sourceIntegralClosureTowerMap_eq_algebraMap]

/-- Helper for Lemma 15.117.1: contracting a maximal `K₂`-branch along the global tower
`B₁ → B₂` gives a maximal `K₁`-branch lying over the contracted source branch. -/
private lemma contracted_branch_liesOver_via_tower
    (p2 : Ideal A2) [p2.IsMaximal]
    (q2 : Ideal B2) [q2.IsMaximal] [q2.LiesOver p2] :
    let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
    let _ : Algebra B1 B2 :=
      reduced_tensor_integralClosure_tower_map.toAlgebra
    let p1 : Ideal A1 := p2.under A1
    let q1 : Ideal B1 := q2.under B1
    p1.IsMaximal ∧ q1.IsMaximal ∧ q1.LiesOver p1 := by
  let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
  let _ : Algebra B1 B2 := reduced_tensor_integralClosure_tower_map.toAlgebra
  let p1 : Ideal A1 := p2.under A1
  let q1 : Ideal B1 := q2.under B1
  have hp1 : p1.IsMaximal := by
    -- Contracting the chosen source branch along `A₁ → A₂` preserves maximality.
    simpa [p1] using contracted_source_isMaximal p2
  have hq1 : q1.IsMaximal := by
    -- Contracting the chosen target branch along `B₁ → B₂` preserves maximality as well.
    simpa [q1, Ideal.under_def] using contracted_target_isMaximal_under_tower q2
  have hq1_under_raw : ((q2.under B1).under A1) = p2.under A1 := by
    -- First record the already-proved tower-square contraction identity without any local rewrites.
    exact contracted_target_under_eq_source_contraction p2 q2
  have hq1_under : q1.under A1 = p1 := by
    -- The tower square already proved above identifies the doubly contracted branch.
    change ((q2.under B1).under A1) = p2.under A1
    exact hq1_under_raw
  have hq1_over : q1.LiesOver p1 := by
    -- Reinterpret the contraction identity as the lies-over equality on `A₁`.
    rw [Ideal.liesOver_iff]
    change p2.under A1 = ((q2.under B1).under A1)
    exact hq1_under_raw.symm
  exact ⟨hp1, hq1, hq1_over⟩

-- Proof sketch: for each maximal branch of the integral-closure base change over `K1 / K`, the
-- hypothesis gives formal smoothness of the corresponding localized extension. Apply
-- Lemma `15.115.3` to each such localized map after the finite extension `K2 / K1`; this yields
-- formal smoothness for every branch over `K2 / K`, which is exactly the definition of being a
-- solution.
/-- Lemma 15.117.1: if `K₁ / K` is a solution for the extension `A ⊂ B` of discrete valuation
rings, then every finite extension `K₂ / K₁` is again a solution for `A ⊂ B`, viewed as a finite
extension of `K`. -/
@[stacks 0GLR]
theorem solutionFor_of_finite_extension
    (hK1 : IsSolutionFor A B K L K1) :
    IsSolutionFor A B K L K2 := by
  -- Route correction: first contract a `K₂`-branch to the `K₁`-level; the remaining step is the
  -- branchwise base-change comparison needed to invoke Lemma `15.115.3`.
  intro p2 hp2 q2 hq2 hq2_over
  let _ : Algebra A1 A2 := sourceIntegralClosureTowerMap.toAlgebra
  let _ : Algebra B1 B2 := reduced_tensor_integralClosure_tower_map.toAlgebra
  let p1 : Ideal A1 := p2.under A1
  let q1 : Ideal B1 := q2.under B1
  have hcontract :
      p1.IsMaximal ∧ q1.IsMaximal ∧ q1.LiesOver p1 := by
    -- First contract the chosen `K₂`-branch to the `K₁`-level branch dictated by the source proof.
    simpa [p1, q1] using
      contracted_branch_liesOver_via_tower
        (A := A) (B := B) (K := K) (L := L) (K1 := K1) (K2 := K2) p2 q2
  rcases hcontract with ⟨hp1, hq1, hq1_over⟩
  let _ : p1.IsMaximal := hp1
  let _ : q1.IsMaximal := hq1
  let _ : q1.LiesOver p1 := hq1_over
  have hfs1 :
      (Localization.localRingHom p1 q1 (algebraMap A1 B1) (q1.over_def p1)).formally_smooth_for_adic
        (maximalIdeal (Localization.AtPrime q1)) := by
    -- The hypothesis says exactly that every contracted `K₁`-branch is formally smooth.
    exact hK1 p1 q1
  -- TODO: apply Lemma `15.115.3` to the localized formally smooth branch over `K₁`, then prove
  -- the final normalization identifying the resulting `K₂`-branch map with
  -- `Localization.localRingHom p2 q2 (algebraMap A2 B2) (q2.over_def p2)`.
  let _ := hfs1
  let _ := hK1
  let _ := hp2
  let _ := hq2
  let _ := hq2_over
  sorry

end
