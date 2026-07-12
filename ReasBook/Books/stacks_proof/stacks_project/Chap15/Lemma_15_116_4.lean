import Mathlib
import StacksProject_2024.Chap15.Definition_15_116_1
import StacksProject_2024.Chap15.Lemma_15_112_3
import StacksProject_2024.Chap15.Lemma_15_112_5
import StacksProject_2024.Chap15.Remark_15_115_1_core

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped TensorProduct

universe u v w x y z

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling for Lemma 15.116.4:
- primary domain: finite base change of extensions of discrete valuation rings, organized around
  the chapter solution predicates and the canonical branches of the reduced tensor product;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `IsSolutionFor`,
  `MaximalSpectrum`,
  `isExtensionOfDiscreteValuationRings_localizationBranch`;
- best owner abstraction: the source-facing solution predicates are already owned by
  `Definition_15_116_1`, so this file should reuse `IsWeakSolutionFor` / `IsSolutionFor` directly;
  the reduced tensor-product hypotheses should therefore quantify directly over the canonical
  branch owner `m : MaximalSpectrum ((L ⊗[K] K₁)_red)`, with branch field
  `((L ⊗[K] K₁)_red) ⧸ m.asIdeal`;
- primitive-vs-derived split: the primitive data are the DVR tower `A ⊂ B ⊂ C`, fraction fields
  `K ⊂ L ⊂ M`, the finite extension `K₁ / K`, and the canonical maximal ideals of
  `((L ⊗[K] K₁)_red)`; the weak/solution conditions on the branch quotients are derived API via
  the chapter owners.

Source/core/bridge triage:
- `source-facing`: the four ascent/descent theorems of Lemma `15.116.4`;
- `core/canonical`: `IsWeakSolutionFor`, `IsSolutionFor`, and the branch owner
  `m : MaximalSpectrum ((L ⊗[K] K₁)_red)`;
- `bridge/view`: the quotient branch field `((L ⊗[K] K₁)_red) ⧸ m.asIdeal`, which feeds the
  canonical chapter solution predicates for `B ⊂ C`.
-/

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable [IsExtensionOfDiscreteValuationRings A C]
variable {K : Type x} {L : Type y} {M : Type z} {K1 : Type (max x y z)}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra B M] [Algebra C M] [Algebra K M] [Algebra L M]
variable [IsFractionRing C M]
variable [IsScalarTower A C M] [IsScalarTower A K M]
variable [IsScalarTower B C M] [IsScalarTower B L M]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "M1" => (M ⊗[K] K1) ⧸ nilradical (M ⊗[K] K1)
local notation "B1" => integralClosure B L1
local notation "C1" => integralClosure C M1

local instance : CommRing L1 :=
  Ideal.Quotient.commRing _

local instance : CommRing M1 :=
  Ideal.Quotient.commRing _

noncomputable local instance (m : MaximalSpectrum L1) : Field (L1 ⧸ m.asIdeal) :=
  Ideal.Quotient.field m.asIdeal

/-- Helper for Lemma 15.116.4: the reduced tensor product `L₁` is reduced by construction. -/
private theorem reducedTensorBaseChange_isReduced :
    IsReduced L1 := by
  -- The quotient by the nilradical is the standard reduced replacement of the tensor product.
  exact Ideal.Quotient.isReduced_quotient_nilradical (L ⊗[K] K1)

/-- Helper for Lemma 15.116.4: the reduced tensor product `L₁` stays finite-dimensional over `L`.
-/
private theorem reducedTensorBaseChange_finiteDimensional :
    FiniteDimensional L L1 := by
  -- First view the unreduced tensor product as finite-dimensional over `L`, then pass to the
  -- quotient by the nilradical.
  let _ : FiniteDimensional L (L ⊗[K] K1) := by infer_instance
  infer_instance

/-- Helper for Lemma 15.116.4: the reduced tensor product `L₁` is Artinian. -/
private theorem reducedTensorBaseChange_isArtinian :
    IsArtinianRing L1 := by
  let _ : FiniteDimensional L L1 :=
    reducedTensorBaseChange_finiteDimensional (K := K) (L := L) (K1 := K1)
  -- Finite-dimensional algebras over a field are Artinian.
  exact IsArtinianRing.of_finite L L1

/-- Helper for Lemma 15.116.4: the Artinian product decomposition of `L₁` evaluates at a maximal
ideal by the corresponding quotient map. -/
private theorem reducedTensorBaseChange_equivPi_apply_eq_quotient_mk
    (m : MaximalSpectrum L1) (x : L1) :
    (IsArtinianRing.equivPi L1) x m = Ideal.Quotient.mk m.asIdeal x := by
  let _ : IsReduced L1 :=
    reducedTensorBaseChange_isReduced (K := K) (L := L) (K1 := K1)
  let _ : IsArtinianRing L1 :=
    reducedTensorBaseChange_isArtinian (K := K) (L := L) (K1 := K1)
  -- The canonical Artinian decomposition is the tuple of quotient maps to the branch fields.
  have hcomm :
      IsArtinianRing.equivPi L1 x =
        algebraMap L1 ((J : MaximalSpectrum L1) → L1 ⧸ J.asIdeal) x := by
    simpa using (IsArtinianRing.equivPi L1).commutes x
  simpa using congrArg (fun f : (J : MaximalSpectrum L1) → L1 ⧸ J.asIdeal ↦ f m) hcomm

/-- Helper for Lemma 15.116.4: the reduced tensor product splits as the product of its branch
field quotients. -/
private noncomputable theorem reduced_tensor_base_change_equiv_pi_quotients :
    L1 ≃ₐ[B] ∀ m : MaximalSpectrum L1, L1 ⧸ m.asIdeal := by
  let _ : IsReduced L1 :=
    reducedTensorBaseChange_isReduced (K := K) (L := L) (K1 := K1)
  let _ : IsArtinianRing L1 :=
    reducedTensorBaseChange_isArtinian (K := K) (L := L) (K1 := K1)
  -- Restrict scalars from the canonical Artinian product decomposition to the base DVR `B`.
  exact (IsArtinianRing.equivPi L1).restrictScalars B

/-- Helper for Lemma 15.116.4: for a fixed base ring `B`, an element of a finite product belongs
to the integral closure over `B` exactly when each coordinate does. -/
private theorem mem_integralClosure_pi_iff_of_constant_base
    {ι : Type*} [Finite ι] {S : ι → Type*}
    [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)] {s : ∀ i, S i} :
    s ∈ integralClosure B (∀ i, S i) ↔ ∀ i, s i ∈ integralClosure B (S i) := by
  constructor
  · intro hs i
    let evalAlgHom : (∀ j, S j) →ₐ[B] S i :=
      { toRingHom := Pi.evalRingHom S i
        commutes' := fun b ↦ rfl }
    -- Evaluating an integral equation on one coordinate preserves integrality.
    exact hs.map evalAlgHom
  · intro hs
    have hs_integral : ∀ i, IsIntegral B (s i) := by
      intro i
      simpa [mem_integralClosure_iff] using hs i
    have hs_pi : IsIntegral (∀ i, B) s := by
      simpa using
        (IsIntegral.pi_iff (R := fun _ : ι ↦ B) (S := S) (s := s)).2 hs_integral
    let _ : Module.Finite B (∀ i, B) := by infer_instance
    let _ : Algebra.IsIntegral B (∀ i, B) := by infer_instance
    -- The diagonal product ring is finite and integral over `B`, so integrality descends back
    -- from `∏ i, B` to the original base ring `B`.
    simpa [mem_integralClosure_iff] using isIntegral_trans s hs_pi

/-- Helper for Lemma 15.116.4: the integral closure of a finite product over a fixed base ring
splits coordinatewise. -/
private noncomputable theorem integralClosure_pi_equiv
    {ι : Type*} [Finite ι] {S : ι → Type*}
    [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)] :
    integralClosure B (∀ i, S i) ≃ₐ[B] ∀ i, integralClosure B (S i) := by
  refine
    { toFun := fun x i ↦
        ⟨x.1 i,
          (mem_integralClosure_pi_iff_of_constant_base (B := B) (s := x.1)).1 x.2 i⟩
      invFun := fun x ↦
        ⟨fun i ↦ (x i : S i),
          (mem_integralClosure_pi_iff_of_constant_base (B := B) (s := fun i ↦ (x i : S i))).2
            (fun i ↦ (x i).2)⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_one' := ?_
      commutes' := ?_ }
  · intro x
    ext i
    rfl
  · intro x
    ext i
    rfl
  · intro x y
    ext i
    rfl
  · intro x y
    ext i
    rfl
  · ext i
    rfl
  · ext i
    rfl
  · intro b
    ext i
    rfl

/-- Helper for Lemma 15.116.4: the intermediate normalization `B₁` splits as the product of the
normalizations over the branch fields of `L₁`. -/
private noncomputable theorem intermediate_normalization_equiv_pi_factor_integral_closures :
    B1 ≃ₐ[B] ∀ m : MaximalSpectrum L1, integralClosure B (L1 ⧸ m.asIdeal) := by
  let _ : IsArtinianRing L1 :=
    reducedTensorBaseChange_isArtinian (K := K) (L := L) (K1 := K1)
  let eTensor : L1 ≃ₐ[B] ∀ m : MaximalSpectrum L1, L1 ⧸ m.asIdeal :=
    reduced_tensor_base_change_equiv_pi_quotients (B := B) (K := K) (L := L) (K1 := K1)
  refine
    { toFun := fun x m ↦ ?_
      invFun := fun x ↦ ?_
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_one' := ?_
      commutes' := ?_ }
  · have hx_pi :
        eTensor x.1 ∈ integralClosure B (∀ m : MaximalSpectrum L1, L1 ⧸ m.asIdeal) := by
      have hx_mem : x.1 ∈ integralClosure B L1 := x.2
      rw [mem_integralClosure_iff] at hx_mem ⊢
      exact hx_mem.map eTensor.toAlgHom
    -- Move one integral element of `B₁` to the product decomposition, then read off the chosen
    -- coordinate.
    exact
      ⟨(eTensor x.1) m,
        (mem_integralClosure_pi_iff_of_constant_base
          (B := B) (s := eTensor x.1)).1 hx_pi m⟩
  · have hx_pi :
        (fun m : MaximalSpectrum L1 ↦ ((x m : integralClosure B (L1 ⧸ m.asIdeal)) :
          L1 ⧸ m.asIdeal)) ∈
          integralClosure B (∀ m : MaximalSpectrum L1, L1 ⧸ m.asIdeal) := by
      exact
        (mem_integralClosure_pi_iff_of_constant_base
          (B := B)
          (s := fun m : MaximalSpectrum L1 ↦
            ((x m : integralClosure B (L1 ⧸ m.asIdeal)) : L1 ⧸ m.asIdeal))).2
          (fun m ↦ (x m).2)
    have hx_mem :
        eTensor.symm
            (fun m : MaximalSpectrum L1 ↦
              ((x m : integralClosure B (L1 ⧸ m.asIdeal)) : L1 ⧸ m.asIdeal)) ∈
          integralClosure B L1 := by
      rw [mem_integralClosure_iff] at hx_pi ⊢
      exact hx_pi.map eTensor.symm.toAlgHom
    -- Reassemble a tuple of integral coordinates into one integral element of `L₁`.
    exact
      ⟨eTensor.symm
          (fun m : MaximalSpectrum L1 ↦
            ((x m : integralClosure B (L1 ⧸ m.asIdeal)) : L1 ⧸ m.asIdeal)),
        hx_mem⟩
  · intro x
    ext m
    rfl
  · intro x
    ext m
    rfl
  · intro x y
    ext m
    rfl
  · intro x y
    ext m
    rfl
  · ext m
    rfl
  · ext m
    rfl
  · intro b
    ext m
    rfl

/-- Helper for Lemma 15.116.4: a maximal branch `q ⊂ B₁` canonically determines the maximal
branch field `L₁ ⧸ m.asIdeal` of the reduced tensor product lying underneath it. -/
private noncomputable def intermediate_branch_coordinate
    (q : Ideal B1) [q.IsMaximal] : MaximalSpectrum L1 :=
  ⟨Ideal.comap (algebraMap L1 B1) q,
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q⟩

/-- Helper for Lemma 15.116.4: the extension `L ⊂ M` induces the canonical unreduced tensor map
`L ⊗[K] K₁ → M ⊗[K] K₁`. -/
private noncomputable abbrev reducedTensorUnreducedCompMap :
    (L ⊗[K] K1) →ₐ[B] (M ⊗[K] K1) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K1 K1)).restrictScalars B

/-- Helper for Lemma 15.116.4: the unreduced tensor comparison map is injective because `M` is
flat over `K`, so tensoring the injective field map `L → M` with `K₁` preserves injectivity. -/
private theorem reducedTensorUnreducedCompMap_injective :
    Function.Injective
      (reducedTensorUnreducedCompMap
        (B := B) (K := K) (L := L) (M := M) (K1 := K1)) := by
  let _ : Module.Flat K L := by infer_instance
  let _ : Module.Flat K K1 := by infer_instance
  have hmap :=
    TensorProduct.map_injective_of_flat_flat
      (IsScalarTower.toAlgHom K L M).toLinearMap
      (LinearMap.id : K1 →ₗ[K] K1)
      (IsScalarTower.toAlgHom K L M).injective
      (fun _ _ h ↦ h)
  simpa [reducedTensorUnreducedCompMap] using hmap

/-- Helper for Lemma 15.116.4: quotienting the unreduced tensor map by the nilradical of the
target gives the ambient map from `L ⊗[K] K₁` to `M₁`. -/
private noncomputable abbrev reducedTensorCompMapToQuotient :
    (L ⊗[K] K1) →ₐ[B] M1 :=
  (Ideal.Quotient.mkₐ B (nilradical (M ⊗[K] K1))).comp reducedTensorUnreducedCompMap

/-- Helper for Lemma 15.116.4: the tensor comparison map kills the nilradical of
`L ⊗[K] K₁`, so it descends to the reduced tensor products. -/
private theorem reducedTensorUnreducedCompMap_nilradical_maps_to_zero
    (x : L ⊗[K] K1) (hx : x ∈ nilradical (L ⊗[K] K1)) :
    (reducedTensorCompMapToQuotient : (L ⊗[K] K1) →ₐ[B] M1) x = 0 := by
  -- Nilpotence is preserved by algebra maps, so every element of the source nilradical vanishes
  -- after passing to the reduced quotient of the target tensor product.
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Ideal.mem_nilradical]
  rcases Ideal.mem_nilradical.mp hx with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [reducedTensorUnreducedCompMap, map_pow] using
    congrArg
      (fun y ↦
        (reducedTensorUnreducedCompMap : (L ⊗[K] K1) →ₐ[B] (M ⊗[K] K1)) y) hn

/-- Helper for Lemma 15.116.4: the extension `L ⊂ M` induces the canonical reduced tensor map
`L₁ → M₁`. -/
private noncomputable abbrev reducedTensorCompMap : L1 →ₐ[B] M1 :=
  Ideal.Quotient.liftₐ (R₁ := B) (I := nilradical (L ⊗[K] K1))
    reducedTensorCompMapToQuotient
    reducedTensorUnreducedCompMap_nilradical_maps_to_zero

/-- Helper for Lemma 15.116.4: an element of the reduced tensor product maps to zero in `M₁` iff
it was already zero in `L₁`. -/
private theorem reducedTensorCompMap_eq_zero_iff
    (x : L1) :
    reducedTensorCompMap (B := B) (K := K) (L := L) (M := M) (K1 := K1) x = 0 ↔ x = 0 := by
  refine Ideal.Quotient.inductionOn' x fun a ↦ ?_
  constructor
  · intro hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.mem_nilradical]
    have hnil :
        (reducedTensorUnreducedCompMap
          (B := B) (K := K) (L := L) (M := M) (K1 := K1)) a ∈
          nilradical (M ⊗[K] K1) := by
      simpa [reducedTensorCompMap, reducedTensorCompMapToQuotient] using
        (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    rcases Ideal.mem_nilradical.mp hnil with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpow :
        (reducedTensorUnreducedCompMap
          (B := B) (K := K) (L := L) (M := M) (K1 := K1)) (a ^ n) = 0 := by
      simpa [map_pow] using hn
    exact
      reducedTensorUnreducedCompMap_injective
        (B := B) (K := K) (L := L) (M := M) (K1 := K1) hpow
  · intro hx
    simpa [hx]

/-- Helper for Lemma 15.116.4: the reduced tensor comparison map is injective. -/
private theorem reducedTensorCompMap_injective :
    Function.Injective
      (reducedTensorCompMap
        (B := B) (K := K) (L := L) (M := M) (K1 := K1)) := by
  intro x y hxy
  have hsub :
      reducedTensorCompMap (B := B) (K := K) (L := L) (M := M) (K1 := K1) (x - y) = 0 := by
    simpa [map_sub, hxy]
  exact sub_eq_zero.mp ((reducedTensorCompMap_eq_zero_iff
    (B := B) (K := K) (L := L) (M := M) (K1 := K1) (x - y)).1 hsub)

/-- Helper for Lemma 15.116.4: the top normalization `C₁` is canonically a `B₁`-algebra through
the reduced tensor map `L₁ → M₁`. -/
private noncomputable local instance integralClosure_tower_algebra :
    Algebra B1 C1 :=
  reducedTensorCompMap.mapIntegralClosure.toAlgebra

/-- Helper for Lemma 15.116.4: the normalization tower `B ⊂ B₁ ⊂ C₁` is compatible with the
ambient DVR tower `B ⊂ C`. -/
private local instance integralClosure_tower_isScalarTower :
    IsScalarTower B B1 C1 := by
  -- The induced map `B₁ → C₁` was defined from a `B`-algebra map on the ambient reduced fibers,
  -- so both routes `B → C₁` agree on the nose.
  refine IsScalarTower.of_algebraMap_eq fun b ↦ ?_
  ext
  simpa [RingHom.algebraMap_toAlgebra] using
    (reducedTensorCompMap.mapIntegralClosure.commutes b)

/-- Helper for Lemma 15.116.4: the top normalization is integral over the intermediate
normalization. -/
private local instance integralClosure_tower_isIntegral :
    Algebra.IsIntegral B1 C1 :=
  Algebra.IsIntegral.tower_top B

/-- Helper for Lemma 15.116.4: the normalization map `B₁ → C₁` is injective because it is induced
from the injective reduced tensor map `L₁ → M₁`. -/
private theorem integralClosure_tower_map_injective :
    Function.Injective (algebraMap B1 C1) := by
  intro x y hxy
  ext
  exact
    reducedTensorCompMap_injective
      (B := B) (K := K) (L := L) (M := M) (K1 := K1) <| by
        simpa [RingHom.algebraMap_toAlgebra] using
          congrArg (fun z : C1 ↦ ((z : C1) : M1)) hxy

/-- Helper for Lemma 15.116.4: the direct map `A₁ → C₁` agrees pointwise with the route through
the intermediate normalization `B₁ → C₁`. -/
private lemma source_to_top_via_intermediate_eq
    (x : A1) :
    (algebraMap B1 C1) (algebraMap A1 B1 x) = algebraMap A1 C1 x := by
  -- Compare both routes inside the ambient reduced tensor product `M₁`; they are induced by the
  -- same right tensor-factor inclusion `K₁ → M ⊗[K] K₁`.
  ext
  change
    reducedTensorCompMap
        (((reducedTensorBaseChangeIntegralClosureMap
            (A := A) (B := B) (K := K) (L := L) (K1 := K1) x : B1) : L1)) =
      (((reducedTensorBaseChangeIntegralClosureMap
          (A := A) (B := C) (K := K) (L := M) (K1 := K1) x : C1) : M1))
  dsimp [reducedTensorBaseChangeIntegralClosureMap, reducedTensorCompMap,
    reducedTensorCompMapToQuotient, reducedTensorUnreducedCompMap]
  rfl

/-- Helper for Lemma 15.116.4: after choosing a branch chain `p ⊂ q ⊂ r`, the direct localized
map `A₁_p → C₁_r` is the composite of the branch maps `A₁_p → B₁_q → C₁_r`. -/
private theorem localRingHom_comp_eq_of_branch_chain
    (p : Ideal A1) [p.IsMaximal]
    (q : Ideal B1) [q.IsMaximal]
    (r : Ideal C1) [r.IsMaximal]
    [q.LiesOver p] [r.LiesOver q] :
    let _ : r.LiesOver p := Ideal.LiesOver.trans r q p
    (Localization.localRingHom p r (algebraMap A1 C1) (r.over_def p)) =
      (Localization.localRingHom q r (algebraMap B1 C1) (r.over_def q)).comp
        (Localization.localRingHom p q (algebraMap A1 B1) (q.over_def p)) := by
  let _ : r.LiesOver p := Ideal.LiesOver.trans r q p
  -- Both localized maps are induced by the same composite `A₁ → C₁`, so uniqueness of
  -- `Localization.localRingHom` reduces the comparison to base elements of `A₁`.
  refine Localization.localRingHom_unique p r (algebraMap A1 C1) (r.over_def p) fun x ↦ ?_
  simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
  -- Rewrite the composite route through `B₁` using the pointwise comparison of the two global
  -- maps `A₁ → C₁`.
  rw [source_to_top_via_intermediate_eq (A := A) (B := B) (C := C) (K := K) (L := L)
    (M := M) (K1 := K1) x]

/-- Helper for Lemma 15.116.4: localizing at a prime ideal commutes with transport across a ring
equivalence, provided the target prime is the image ideal. -/
private noncomputable theorem localization_atPrime_ringEquiv_of_map_prime
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal R) [q.IsPrime] :
    Localization.AtPrime q ≃+* Localization.AtPrime (Ideal.map e.toRingHom q) := by
  have hPrimeCompl :
      Submonoid.map e.toMonoidHom q.primeCompl =
        (Ideal.map e.toRingHom q).primeCompl := by
    -- The prime complement is carried exactly by the ambient ring equivalence.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hy
      rcases hy with ⟨z, hz, hzx⟩
      exact hx (e.injective hzx ▸ hz)
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      intro hx
      exact hy (Ideal.mem_map_of_mem e.toRingHom hx)
  -- Once the prime complements agree, the localization universal property gives the equivalence.
  exact
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime q)
      (Localization.AtPrime (Ideal.map e.toRingHom q))
      e hPrimeCompl

/-- Helper for Lemma 15.116.4: maximality is preserved when an ideal is transported along a ring
equivalence. -/
private theorem ideal_map_isMaximal_of_ringEquiv
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal R) [q.IsMaximal] :
    (Ideal.map e.toRingHom q).IsMaximal := by
  -- Surjectivity of the equivalence map transfers maximal ideals, and the kernel is trivial.
  refine Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := e.toRingHom) e.surjective ?_
  simpa using (show RingHom.ker e.toRingHom ≤ q from by simp)

/-- Helper for Lemma 15.116.4: after transporting an ideal across a compatible ring equivalence,
its contraction agrees with the original contraction. -/
private theorem ideal_map_comap_eq_of_ringEquiv_comp
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) (e : S ≃+* T)
    (he : e.toRingHom.comp f = g) (q : Ideal S) :
    (Ideal.map e.toRingHom q).comap g = q.comap f := by
  ext x
  -- Rewrite the target contraction through `e`; surjectivity then recovers the original ideal.
  rw [Ideal.mem_comap, ← he, RingHom.comp_apply]
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact e.injective hyx ▸ hy
  · intro hx
    exact ⟨f x, hx, rfl⟩

/-- Helper for Lemma 15.116.4: lies-over is preserved when a branch ideal is transported across a
compatible ring equivalence. -/
private theorem ideal_map_liesOver_of_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃+* T)
    (he : e.toRingHom.comp (algebraMap R S) = algebraMap R T)
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] :
    (Ideal.map e.toRingHom q).LiesOver p := by
  -- Compare contractions through the equivalence, then reuse the original lies-over equality.
  rw [Ideal.liesOver_iff]
  simpa [Ideal.liesOver_iff] using
    (ideal_map_comap_eq_of_ringEquiv_comp
      (f := algebraMap R S) (g := algebraMap R T) e he q).trans (q.over_def p)

/-- Helper for Lemma 15.116.4: once the global branch map is identified with a factor branch by a
compatible ring equivalence, the localized branch maps are conjugate. -/
private theorem localization_localRingHom_conjugation_of_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃+* T)
    (he : e.toRingHom.comp (algebraMap R S) = algebraMap R T)
    (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsMaximal] [q.LiesOver p] :
    let qT : Ideal T := Ideal.map e.toRingHom q
    let _ : qT.IsMaximal := ideal_map_isMaximal_of_ringEquiv e q
    let _ : qT.LiesOver p := ideal_map_liesOver_of_ringEquiv e he p q
    let eLoc : Localization.AtPrime q ≃+* Localization.AtPrime qT :=
      localization_atPrime_ringEquiv_of_map_prime e q
    eLoc.toRingHom.comp
        (Localization.localRingHom p q
          (algebraMap R S) (q.over_def p)) =
      Localization.localRingHom p qT
        (algebraMap R T) (qT.over_def p) := by
  let qT : Ideal T := Ideal.map e.toRingHom q
  let _ : qT.IsMaximal := ideal_map_isMaximal_of_ringEquiv e q
  let _ : qT.LiesOver p := ideal_map_liesOver_of_ringEquiv e he p q
  let eLoc : Localization.AtPrime q ≃+* Localization.AtPrime qT :=
    localization_atPrime_ringEquiv_of_map_prime e q
  -- Both local maps are characterized by the same induced map `R → T` after transport by `e`.
  refine Localization.localRingHom_unique
    p qT (algebraMap R T) (qT.over_def p) fun x ↦ ?_
  simp only [eLoc, RingHom.comp_apply, Localization.localRingHom_to_map]
  simpa using congrArg (fun f : R →+* T ↦ f x) he

/-- Helper for Lemma 15.116.4: the residue fields in a tower of local discrete valuation rings
form a scalar tower. -/
private theorem residueField_isScalarTower_of_dvr_tower
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S T]
    [IsExtensionOfDiscreteValuationRings R T] :
    let hRS : maximalIdeal R = Ideal.comap (algebraMap R S) (maximalIdeal S) :=
      (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
    let hST : maximalIdeal S = Ideal.comap (algebraMap S T) (maximalIdeal T) :=
      (IsLocalRing.maximalIdeal_comap (algebraMap S T)).symm
    let hRT : maximalIdeal R = Ideal.comap (algebraMap R T) (maximalIdeal T) :=
      (IsLocalRing.maximalIdeal_comap (algebraMap R T)).symm
    let _ : Algebra (ResidueField R) (ResidueField S) :=
      (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S) hRS).toAlgebra
    let _ : Algebra (ResidueField S) (ResidueField T) :=
      (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal T) (algebraMap S T) hST).toAlgebra
    let _ : Algebra (ResidueField R) (ResidueField T) :=
      (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal T) (algebraMap R T) hRT).toAlgebra
    IsScalarTower (ResidueField R) (ResidueField S) (ResidueField T) := by
  -- Compare the two residue-field maps on residue classes coming from the base ring `R`.
  let hRS : maximalIdeal R = Ideal.comap (algebraMap R S) (maximalIdeal S) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
  let hST : maximalIdeal S = Ideal.comap (algebraMap S T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap S T)).symm
  let hRT : maximalIdeal R = Ideal.comap (algebraMap R T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R T)).symm
  let _ : Algebra (ResidueField R) (ResidueField S) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S) hRS).toAlgebra
  let _ : Algebra (ResidueField S) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal T) (algebraMap S T) hST).toAlgebra
  let _ : Algebra (ResidueField R) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal T) (algebraMap R T) hRT).toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  obtain ⟨a, rfl⟩ := (maximalIdeal R).algebraMap_residueField_surjective x
  rw [Ideal.ResidueField.map_algebraMap (maximalIdeal R) (maximalIdeal T) (algebraMap R T) hRT a,
    Ideal.ResidueField.map_algebraMap (maximalIdeal R) (maximalIdeal S) (algebraMap R S) hRS a]
  rw [IsScalarTower.algebraMap_apply R S T]
  exact
    (Ideal.ResidueField.map_algebraMap (maximalIdeal S) (maximalIdeal T) (algebraMap S T)
      hST ((algebraMap R S) a)).symm

/-- Helper for Lemma 15.116.4: weakly unramifiedness descends along a tower of extensions of
discrete valuation rings. -/
private theorem weakly_unramified_left_of_dvr_tower
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S T]
    [IsExtensionOfDiscreteValuationRings R T]
    (hRT : WeaklyUnramified R T) :
    WeaklyUnramified R S := by
  -- Compare ramification indices in the tower and read off the lower factor from the equality
  -- `e(R,T) = 1`.
  have hRT_one :
      IsExtensionOfDiscreteValuationRings.ramificationIndex R T = 1 :=
    (weaklyUnramified_iff_ramificationIndex_eq_one (A := R) (B := T)).1 hRT
  have hmul :
      IsExtensionOfDiscreteValuationRings.ramificationIndex R S *
        IsExtensionOfDiscreteValuationRings.ramificationIndex S T = 1 := by
    calc
      IsExtensionOfDiscreteValuationRings.ramificationIndex R S *
          IsExtensionOfDiscreteValuationRings.ramificationIndex S T =
        IsExtensionOfDiscreteValuationRings.ramificationIndex R T := by
          symm
          exact
            IsExtensionOfDiscreteValuationRings.ramificationIndex_algebra_tower
              (A := R) (B := S) (C := T)
      _ = 1 := hRT_one
  have hRS_one :
      IsExtensionOfDiscreteValuationRings.ramificationIndex R S = 1 :=
    Nat.eq_one_of_dvd_one ⟨IsExtensionOfDiscreteValuationRings.ramificationIndex S T, hmul⟩
  -- Repackage the ramification-index equality as weakly unramifiedness.
  exact
    (weaklyUnramified_iff_ramificationIndex_eq_one (A := R) (B := S)).2 hRS_one

/-- Helper for Lemma 15.116.4: formal smoothness for the maximal-ideal-adic topology descends
along a tower of extensions of discrete valuation rings. -/
private theorem formally_smooth_left_of_dvr_tower
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S T]
    [IsExtensionOfDiscreteValuationRings R T]
    (hRT : (algebraMap R T).formally_smooth_for_adic (maximalIdeal T)) :
    (algebraMap R S).formally_smooth_for_adic (maximalIdeal S) := by
  -- Unpack formal smoothness on the composite branch into weakly unramifiedness plus residue-field
  -- separability, then descend each factor separately along the DVR tower.
  rw [formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField] at hRT ⊢
  let hRS : maximalIdeal R = Ideal.comap (algebraMap R S) (maximalIdeal S) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
  let hST : maximalIdeal S = Ideal.comap (algebraMap S T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap S T)).symm
  let hRT' : maximalIdeal R = Ideal.comap (algebraMap R T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R T)).symm
  let _ : Algebra (ResidueField R) (ResidueField S) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S) hRS).toAlgebra
  let _ : Algebra (ResidueField S) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal T) (algebraMap S T) hST).toAlgebra
  let _ : Algebra (ResidueField R) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal T) (algebraMap R T) hRT').toAlgebra
  let _ : IsScalarTower (ResidueField R) (ResidueField S) (ResidueField T) :=
    residueField_isScalarTower_of_dvr_tower (R := R) (S := S) (T := T)
  refine ⟨weakly_unramified_left_of_dvr_tower hRT.1, ?_⟩
  -- Separability descends through the residue-field tower `κ(R) ⊂ κ(S) ⊂ κ(T)`.
  exact Algebra.isSeparable_tower_bot_of_isSeparable
    (ResidueField R) (ResidueField S) (ResidueField T)

/-- Helper for Lemma 15.116.4: localizing the injective normalization map `B₁ → C₁` preserves
injectivity on each branch `q ⊂ r`. -/
private theorem localized_middle_branch_algebraMap_injective
    (q : Ideal B1) [q.IsMaximal]
    (r : Ideal C1) [r.IsMaximal] [r.LiesOver q] :
    Function.Injective (algebraMap (Localization.AtPrime q) (Localization.AtPrime r)) := by
  -- The branch map is exactly the localization of the injective normalization map `B₁ → C₁`.
  simpa [RingHom.algebraMap_toAlgebra, Localization.localRingHom] using
    (IsLocalization.map_injective_of_injective'
      q.primeCompl
      C1
      (Localization.AtPrime r)
      (Localization.le_comap_primeCompl_iff.mpr (ge_of_eq (r.over_def q)))
      (show (0 : C1) ∉ Ideal.primeCompl r by simp [Ideal.primeCompl])
      (integralClosure_tower_map_injective
        (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1)))

/-- Helper for Lemma 15.116.4: the localized middle branch `(B₁)_q → (C₁)_r` is an extension of
discrete valuation rings. -/
private theorem localized_middle_branch_isExtensionOfDiscreteValuationRings
    (q : Ideal B1) [q.IsMaximal]
    (r : Ideal C1) [r.IsMaximal] [r.LiesOver q] :
    IsExtensionOfDiscreteValuationRings (Localization.AtPrime q) (Localization.AtPrime r) := by
  -- Package the localized normalization map as an injective local hom between DVR branches.
  refine
    { toIsLocalHom := ?_
      algebraMap_injective := ?_ }
  · simpa [RingHom.algebraMap_toAlgebra, Localization.localRingHom] using
      (Localization.isLocalHom_localRingHom q r (algebraMap B1 C1) (r.over_def q))
  · exact
      localized_middle_branch_algebraMap_injective
        (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) q r

/-- Helper for Lemma 15.116.4: the localized intermediate branch `A₁_p → B₁_q` carries the
canonical algebra structure coming from the branch map. -/
private noncomputable local instance localized_left_branch_algebra
    (p : Ideal A1) [p.IsPrime]
    (q : Ideal B1) [q.IsPrime] [q.LiesOver p] :
    Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
  (Localization.localRingHom p q (algebraMap A1 B1) (q.over_def p)).toAlgebra

/-- Helper for Lemma 15.116.4: the localized top branch `A₁_p → C₁_r` carries the canonical
algebra structure coming from the branch map. -/
private noncomputable local instance localized_top_branch_algebra
    (p : Ideal A1) [p.IsPrime]
    (r : Ideal C1) [r.IsPrime] [r.LiesOver p] :
    Algebra (Localization.AtPrime p) (Localization.AtPrime r) :=
  (Localization.localRingHom p r (algebraMap A1 C1) (r.over_def p)).toAlgebra

/-- Helper for Lemma 15.116.4: the localized middle branch `B₁_q → C₁_r` carries the canonical
algebra structure coming from the branch map. -/
private noncomputable local instance localized_middle_branch_algebra
    (q : Ideal B1) [q.IsPrime]
    (r : Ideal C1) [r.IsPrime] [r.LiesOver q] :
    Algebra (Localization.AtPrime q) (Localization.AtPrime r) :=
  (Localization.localRingHom q r (algebraMap B1 C1) (r.over_def q)).toAlgebra

/-- Helper for Lemma 15.116.4: the localized middle branch `B₁_q → C₁_r` inherits the extension
of discrete valuation rings structure. -/
private local instance localized_middle_branch_isExtension
    (q : Ideal B1) [q.IsMaximal]
    (r : Ideal C1) [r.IsMaximal] [r.LiesOver q] :
    IsExtensionOfDiscreteValuationRings (Localization.AtPrime q) (Localization.AtPrime r) :=
  localized_middle_branch_isExtensionOfDiscreteValuationRings
    (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) q r

/-- Helper for Lemma 15.116.4: after choosing a branch chain `p ⊂ q ⊂ r`, the localized branches
form a scalar tower. -/
private local instance localized_branch_scalarTower_of_chain
    (p : Ideal A1) [p.IsMaximal]
    (q : Ideal B1) [q.IsMaximal]
    (r : Ideal C1) [r.IsMaximal]
    [q.LiesOver p] [r.LiesOver q] :
    IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) (Localization.AtPrime r) := by
  -- The two routes from `(A₁)_p` to `(C₁)_r` agree because the localized branch maps compose to
  -- the direct localization of `A₁ → C₁`.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  let _ : r.LiesOver p := Ideal.LiesOver.trans r q p
  change
    Localization.localRingHom q r (algebraMap B1 C1) (r.over_def q)
        (Localization.localRingHom p q (algebraMap A1 B1) (q.over_def p) x) =
      Localization.localRingHom p r (algebraMap A1 C1) (r.over_def p) x
  simpa [RingHom.comp_apply] using
    congrArg
      (fun f : Localization.AtPrime p →+* Localization.AtPrime r ↦ f x)
      (localRingHom_comp_eq_of_branch_chain
        (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) p q r)

/-- Helper for Lemma 15.116.4: weakly unramifiedness composes along a tower of extensions of
discrete valuation rings. -/
private theorem weakly_unramified_of_dvr_tower
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S T]
    [IsExtensionOfDiscreteValuationRings R T]
    (hRS : WeaklyUnramified R S) (hST : WeaklyUnramified S T) :
    WeaklyUnramified R T := by
  -- Convert both hypotheses to ramification-index-one identities and multiply them in the tower.
  have hRS_one :
      IsExtensionOfDiscreteValuationRings.ramificationIndex R S = 1 :=
    (weaklyUnramified_iff_ramificationIndex_eq_one (A := R) (B := S)).1 hRS
  have hST_one :
      IsExtensionOfDiscreteValuationRings.ramificationIndex S T = 1 :=
    (weaklyUnramified_iff_ramificationIndex_eq_one (A := S) (B := T)).1 hST
  have hRT_one :
      IsExtensionOfDiscreteValuationRings.ramificationIndex R T = 1 := by
    calc
      IsExtensionOfDiscreteValuationRings.ramificationIndex R T =
          IsExtensionOfDiscreteValuationRings.ramificationIndex R S *
            IsExtensionOfDiscreteValuationRings.ramificationIndex S T := by
              symm
              exact
                IsExtensionOfDiscreteValuationRings.ramificationIndex_algebra_tower
                  (A := R) (B := S) (C := T)
      _ = 1 * 1 := by rw [hRS_one, hST_one]
      _ = 1 := by simp
  -- Repackage the ramification-index computation as weakly unramifiedness of the composite.
  exact
    (weaklyUnramified_iff_ramificationIndex_eq_one (A := R) (B := T)).2 hRT_one

/-- Helper for Lemma 15.116.4: formal smoothness for the maximal-ideal-adic topology composes
along a tower of extensions of discrete valuation rings. -/
private theorem formally_smooth_of_dvr_tower
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings S T]
    [IsExtensionOfDiscreteValuationRings R T]
    (hRS : (algebraMap R S).formally_smooth_for_adic (maximalIdeal S))
    (hST : (algebraMap S T).formally_smooth_for_adic (maximalIdeal T)) :
    (algebraMap R T).formally_smooth_for_adic (maximalIdeal T) := by
  -- Unpack both formally smooth branch maps into weak ramification plus separable residue fields.
  rw [formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField] at
    hRS hST ⊢
  let hRS' : maximalIdeal R = Ideal.comap (algebraMap R S) (maximalIdeal S) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
  let hST' : maximalIdeal S = Ideal.comap (algebraMap S T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap S T)).symm
  let hRT' : maximalIdeal R = Ideal.comap (algebraMap R T) (maximalIdeal T) :=
    (IsLocalRing.maximalIdeal_comap (algebraMap R T)).symm
  let _ : Algebra (ResidueField R) (ResidueField S) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S) hRS').toAlgebra
  let _ : Algebra (ResidueField S) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal T) (algebraMap S T) hST').toAlgebra
  let _ : Algebra (ResidueField R) (ResidueField T) :=
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal T) (algebraMap R T) hRT').toAlgebra
  let _ : IsScalarTower (ResidueField R) (ResidueField S) (ResidueField T) :=
    residueField_isScalarTower_of_dvr_tower (R := R) (S := S) (T := T)
  refine ⟨weakly_unramified_of_dvr_tower hRS.1 hST.1, ?_⟩
  -- Residue-field separability is transitive along the same local tower.
  letI : Algebra.IsSeparable (ResidueField R) (ResidueField S) := hRS.2
  letI : Algebra.IsSeparable (ResidueField S) (ResidueField T) := hST.2
  exact Algebra.IsSeparable.trans (ResidueField R) (ResidueField S) (ResidueField T)

-- TODO: prove this source-faithful branch-lifting statement by decomposing `L₁` as the finite
-- product of its branch fields, applying Remark `15.115.1` factorwise to the induced maps
-- `integralClosure B F → integralClosure C ((M ⊗[L] F)_red)`, and then transporting the chosen
-- factor branch back to the global normalization `C₁`.
/-- Helper for Lemma 15.116.4: every maximal branch of the intermediate normalization `B₁`
lifts to a maximal branch of the top normalization `C₁`. -/
private theorem exists_maximal_over_intermediate_branch
    (q : Ideal B1) [q.IsMaximal] :
    ∃ r : Ideal C1, r.IsMaximal ∧ r.LiesOver q := by
  -- The canonical map `B₁ → C₁` is integral, so ordinary lying over produces a maximal branch
  -- of `C₁` above the chosen maximal branch `q` of `B₁`.
  obtain ⟨r, hrmax, hrover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := C1) q
  exact ⟨r, hrmax, hrover⟩

/-- Helper for Lemma 15.116.4: once the chosen global branch `r ⊂ C₁` is identified with the
corresponding factor branch over some `m : MaximalSpectrum L₁`, the factor hypothesis yields
weakly unramifiedness of the actual localized middle branch `(B₁)_q → (C₁)_r`. -/
private theorem weakly_unramified_of_factor_branch_transport
    (q : Ideal B1) [q.IsMaximal]
    (r : Ideal C1) [r.IsMaximal] [r.LiesOver q]
    (hBC :
      ∀ m : MaximalSpectrum L1,
        let F := L1 ⧸ m.asIdeal
        let _ : Field F := Ideal.Quotient.field m.asIdeal
        let _ : Algebra B F := inferInstance
        let _ : Algebra L F := inferInstance
        let _ : IsScalarTower B L F := inferInstance
        let _ : FiniteDimensional L F := inferInstance
        IsWeakSolutionFor B C L M F) :
    WeaklyUnramified (Localization.AtPrime q) (Localization.AtPrime r) := by
  -- TODO: contract `r` to the branch coordinate `m : MaximalSpectrum L₁`, transport the actual
  -- local branch `(B₁)_q → (C₁)_r` across the corresponding factor-side localization conjugation,
  -- and then apply the factor hypothesis `hBC m` on that transported branch.
  sorry

/-- Helper for Lemma 15.116.4: once the chosen global branch `r ⊂ C₁` is identified with the
corresponding factor branch over some `m : MaximalSpectrum L₁`, the factor hypothesis yields
formal smoothness of the actual localized middle branch `(B₁)_q → (C₁)_r`. -/
private theorem formally_smooth_of_factor_branch_transport
    (q : Ideal B1) [q.IsMaximal]
    (r : Ideal C1) [r.IsMaximal] [r.LiesOver q]
    (hBC :
      ∀ m : MaximalSpectrum L1,
        let F := L1 ⧸ m.asIdeal
        let _ : Field F := Ideal.Quotient.field m.asIdeal
        let _ : Algebra B F := inferInstance
        let _ : Algebra L F := inferInstance
        let _ : IsScalarTower B L F := inferInstance
        let _ : FiniteDimensional L F := inferInstance
        IsSolutionFor B C L M F) :
    (algebraMap (Localization.AtPrime q) (Localization.AtPrime r)).formally_smooth_for_adic
      (maximalIdeal (Localization.AtPrime r)) := by
  -- TODO: use the same branch-to-factor localization conjugation as in the weakly-unramified
  -- transport lemma, then pull the factor-side formal smoothness statement `hBC m` back to the
  -- actual branch `(B₁)_q → (C₁)_r`.
  sorry

-- Proof sketch: localize the integral closure `A1 = integralClosure A K1` at a maximal ideal and
-- compare the corresponding branches of `A1 ⊗[A] B` and `A1 ⊗[A] C`. If the branch over `C` is
-- weakly unramified, then every intermediate local extension of discrete valuation rings remains
-- weakly unramified by multiplicativity of ramification indices in towers.
/-- Lemma 15.116.4 (1): if `K1 / K` is a weak solution for `A → C`, then it is a weak solution for
`A → B`. -/
@[stacks 09ES]
theorem weakSolutionFor_of_weakSolutionFor_comp
    (hK1 : IsWeakSolutionFor A C K M K1) :
    IsWeakSolutionFor A B K L K1 := by
  intro p hp q hq hq_over
  -- Route correction: once a branch `r` of `C₁` above `q` is available, the source proof descends
  -- weakly unramifiedness from `(A₁)_p → (C₁)_r` to `(A₁)_p → (B₁)_q` along the local tower,
  -- using the canonical localization tower instances instead of reopening the factor decomposition.
  let _ : p.IsMaximal := hp
  let _ : q.IsMaximal := hq
  let _ : q.LiesOver p := hq_over
  obtain ⟨r, hrmax, hrover⟩ :=
    exists_maximal_over_intermediate_branch
      (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) q
  let _ : r.IsMaximal := hrmax
  let _ : r.LiesOver q := hrover
  let _ : r.LiesOver p := Ideal.LiesOver.trans r q p
  let _ : IsExtensionOfDiscreteValuationRings
      (Localization.AtPrime q) (Localization.AtPrime r) :=
    localized_middle_branch_isExtensionOfDiscreteValuationRings
      (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) q r
  -- Apply weak-unramified descent to the localized branch tower `A₁_p → B₁_q → C₁_r`.
  simpa using
    (weakly_unramified_left_of_dvr_tower
      (R := Localization.AtPrime p)
      (S := Localization.AtPrime q)
      (T := Localization.AtPrime r)
      (hK1 p r))

-- Proof sketch: use the weak-solution descent from the previous clause together with
-- Lemma `15.112.5`: separability of the residue-field extension for the branch over `C` implies
-- separability for the intermediate branch over `B`, so every solution branch over `C` yields a
-- solution branch over `B`.
/-- Lemma 15.116.4 (2): if `K1 / K` is a solution for `A → C`, then it is a solution for `A → B`.
-/
@[stacks 09ES]
theorem solutionFor_of_solutionFor_comp
    (hK1 : IsSolutionFor A C K M K1) :
    IsSolutionFor A B K L K1 := by
  intro p hp q hq hq_over
  -- The source route is the same as in clause `(1)`, with formal smoothness descending from the
  -- composite local branch to the intermediate local branch through the same `p-q-r` tower.
  let _ : p.IsMaximal := hp
  let _ : q.IsMaximal := hq
  let _ : q.LiesOver p := hq_over
  obtain ⟨r, hrmax, hrover⟩ :=
    exists_maximal_over_intermediate_branch
      (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) q
  let _ : r.IsMaximal := hrmax
  let _ : r.LiesOver q := hrover
  let _ : r.LiesOver p := Ideal.LiesOver.trans r q p
  let _ : IsExtensionOfDiscreteValuationRings
      (Localization.AtPrime q) (Localization.AtPrime r) :=
    localized_middle_branch_isExtensionOfDiscreteValuationRings
      (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) q r
  -- Apply formal-smoothness descent to the localized branch tower `A₁_p → B₁_q → C₁_r`.
  simpa using
    (formally_smooth_left_of_dvr_tower
      (R := Localization.AtPrime p)
      (S := Localization.AtPrime q)
      (T := Localization.AtPrime r)
      (hK1 p r))

-- Proof sketch: treat `L1 = ((L ⊗[K] K1)_red)` branchwise via its canonical maximal ideals. For
-- each branch field `L1 ⧸ m.asIdeal`, combine the given weak solution branch for `B → C` with the
-- weak solution branches for `A → B`. The local tower criterion for ramification indices then
-- shows that the induced branches for `A → C` are weakly unramified.
/-- Lemma 15.116.4 (3): if `K1 / K` is a weak solution for `A → B` and
every canonical branch field `((L ⊗[K] K1)_red) ⧸ m.asIdeal` is a weak solution for `B → C`, then
`K1 / K` is a weak solution for `A → C`. -/
@[stacks 09ES]
theorem weakSolutionFor_comp_of_weakSolutionFor_of_reducedTensorProductFactors
    (hAB : IsWeakSolutionFor A B K L K1)
    (hBC :
      ∀ m : MaximalSpectrum L1,
        let F := L1 ⧸ m.asIdeal
        let _ : Field F := Ideal.Quotient.field m.asIdeal
        let _ : Algebra B F := inferInstance
        let _ : Algebra L F := inferInstance
        let _ : IsScalarTower B L F := inferInstance
        let _ : FiniteDimensional L F := inferInstance
        IsWeakSolutionFor B C L M F) :
    IsWeakSolutionFor A C K M K1 := by
  intro p hp r hr hr_over
  -- Route correction: follow the source proof literally. Start from the actual target branch
  -- `r ⊂ C₁`, contract it to `q ⊂ B₁`, use `hAB` on `A₁_p → B₁_q`, transport `hBC` to
  -- `B₁_q → C₁_r`, and then compose along the localized `p-q-r` tower.
  let _ : p.IsMaximal := hp
  let _ : r.IsMaximal := hr
  let _ : r.LiesOver p := hr_over
  let q : Ideal B1 := Ideal.comap (algebraMap B1 C1) r
  have hq_max : q.IsMaximal := by
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal r
  let _ : q.IsMaximal := hq_max
  have hq_over : q.LiesOver p := by
    -- The contraction of `r` to `B₁` still contracts to `p` inside `A₁` because the two global
    -- maps `A₁ → C₁` agree through the intermediate normalization.
    rw [Ideal.liesOver_iff]
    ext x
    change (algebraMap B1 C1 (algebraMap A1 B1 x) ∈ r) ↔ algebraMap A1 C1 x ∈ r
    rw [source_to_top_via_intermediate_eq
      (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) x]
  let _ : q.LiesOver p := hq_over
  have hr_over_q : r.LiesOver q := by
    -- By definition, `q` is the contraction of `r` along `B₁ → C₁`.
    rw [Ideal.liesOver_iff, q]
  let _ : r.LiesOver q := hr_over_q
  have hleft :
      WeaklyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    hAB p q
  have hmiddle :
      WeaklyUnramified (Localization.AtPrime q) (Localization.AtPrime r) :=
    weakly_unramified_of_factor_branch_transport
      (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) q r hBC
  -- The remaining branch is the composite of the two localized DVR extensions just assembled.
  exact
    weakly_unramified_of_dvr_tower
      (R := Localization.AtPrime p)
      (S := Localization.AtPrime q)
      (T := Localization.AtPrime r)
      hleft hmiddle

-- Proof sketch: refine the preceding branchwise ascent argument with Lemma `15.112.5`: the
-- canonical branch fields for `B → C` have separable residue-field extensions, and separability
-- is preserved when passing to the composite local branch over `A`. Together with weakly
-- unramifiedness, this yields a solution branch for `A → C`.
/-- Lemma 15.116.4 (4): if `K1 / K` is a solution for `A → B` and every canonical branch field
`((L ⊗[K] K1)_red) ⧸ m.asIdeal` is a solution for `B → C`, then `K1 / K` is a solution for
`A → C`. -/
@[stacks 09ES]
theorem solutionFor_comp_of_solutionFor_of_reducedTensorProductFactors
    (hAB : IsSolutionFor A B K L K1)
    (hBC :
      ∀ m : MaximalSpectrum L1,
        let F := L1 ⧸ m.asIdeal
        let _ : Field F := Ideal.Quotient.field m.asIdeal
        let _ : Algebra B F := inferInstance
        let _ : Algebra L F := inferInstance
        let _ : IsScalarTower B L F := inferInstance
        let _ : FiniteDimensional L F := inferInstance
        IsSolutionFor B C L M F) :
    IsSolutionFor A C K M K1 := by
  intro p hp r hr hr_over
  -- Route correction: use the same source-faithful `p-q-r` tower as in clause `(3)`, now with
  -- formal smoothness on the left and middle branches.
  let _ : p.IsMaximal := hp
  let _ : r.IsMaximal := hr
  let _ : r.LiesOver p := hr_over
  let q : Ideal B1 := Ideal.comap (algebraMap B1 C1) r
  have hq_max : q.IsMaximal := by
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal r
  let _ : q.IsMaximal := hq_max
  have hq_over : q.LiesOver p := by
    -- Contracting the chosen top branch back to `B₁` preserves the original branch over `p`.
    rw [Ideal.liesOver_iff]
    ext x
    change (algebraMap B1 C1 (algebraMap A1 B1 x) ∈ r) ↔ algebraMap A1 C1 x ∈ r
    rw [source_to_top_via_intermediate_eq
      (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) x]
  let _ : q.LiesOver p := hq_over
  have hr_over_q : r.LiesOver q := by
    -- By construction, `q` is exactly the contraction of `r` along `B₁ → C₁`.
    rw [Ideal.liesOver_iff, q]
  let _ : r.LiesOver q := hr_over_q
  have hleft :
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)).formally_smooth_for_adic
        (maximalIdeal (Localization.AtPrime q)) :=
    hAB p q
  have hmiddle :
      (algebraMap (Localization.AtPrime q) (Localization.AtPrime r)).formally_smooth_for_adic
        (maximalIdeal (Localization.AtPrime r)) :=
    formally_smooth_of_factor_branch_transport
      (A := A) (B := B) (C := C) (K := K) (L := L) (M := M) (K1 := K1) q r hBC
  -- Once the middle branch has been transported from the correct factor, formal smoothness
  -- composes along the same localized DVR tower.
  exact
    formally_smooth_of_dvr_tower
      (R := Localization.AtPrime p)
      (S := Localization.AtPrime q)
      (T := Localization.AtPrime r)
      hleft hmiddle

end
