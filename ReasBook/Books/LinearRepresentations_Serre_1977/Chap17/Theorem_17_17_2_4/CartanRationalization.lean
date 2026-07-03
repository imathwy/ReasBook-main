import Mathlib
import Serre.Chap16.Corollary_16_16_1_6
import Serre.Chap17.Corollary_17_17_2_2.Index
import Serre.Chap17.Theorem_17_17_2_4.ScalarMultipleDescent

open scoped MonoidAlgebra Representation TensorProduct
open CategoryTheory

noncomputable section

universe u

namespace Representation

section ProjectiveRow

variable (k : Type u) [Field k]
variable (G : Type u) [Group G] [Finite G]

local instance : AddCommMonoid (P₀[k](G)) :=
  (QuotientAddGroup.Quotient.addCommGroup
    (finiteProjectiveGroupAlgebraGrothendieckRelations k G)).toAddCommMonoid

local instance : AddCommGroup (P₀[k](G)) :=
  QuotientAddGroup.Quotient.addCommGroup
    (finiteProjectiveGroupAlgebraGrothendieckRelations k G)

local instance : Module ℤ (P₀[k](G)) := AddCommGroup.toIntModule (P₀[k](G))

local instance : AddCommMonoid (R₀[k](G)) :=
  (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)).toAddCommMonoid

local instance : AddCommGroup (R₀[k](G)) :=
  QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k G)

local instance : Module ℤ (R₀[k](G)) := AddCommGroup.toIntModule (R₀[k](G))

/-- Helper for Theorem 17-17.2-4: the canonical `p`-part/prime-to-`p` factorization of
`Nat.card G` coming from `ordProj` and `ordCompl`. -/
private theorem card_eq_ordProj_mul_ordCompl_and_coprime
    {p : ℕ} [CharP k p] [Fact p.Prime] :
    let n := Nat.factorization (Nat.card G) p
    let m := ordCompl[p] (Nat.card G)
    Nat.card G = p ^ n * m ∧ Nat.Coprime p m := by
  dsimp
  constructor
  · simpa using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
  · simpa using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) Nat.card_pos.ne'

/-- Helper for Theorem 17-17.2-4: in characteristic zero, every finite-dimensional class comes
from an actual finite projective class under the Cartan map. -/
private theorem exists_projective_preimage_of_fdrep_charZero [CharZero k] (V : FDRep k G) :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G, cartanHom k G [P]ₚ₀ = [V]₀ := by
  -- Route correction: reuse Maschke semisimplicity on the honest finite-dimensional owner before
  -- descending to the Grothendieck quotient.
  let ρ : Rep k G := (forget₂ (FDRep k G) (Rep k G)).obj V
  let W0 : ModuleCat k[G] := Rep.toModuleMonoidAlgebra.obj ρ
  let _ : Module k W0 := Module.compHom W0 (algebraMap k k[G])
  let _ : IsScalarTower k k[G] W0 := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hρfinite : Module.Finite k ρ := by
    simpa [ρ] using (show Module.Finite k V from inferInstance)
  let f : ρ →ₗ[k] W0 :=
    { toFun := ρ.ρ.asModuleEquiv.symm
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change ρ.ρ.asModuleEquiv.symm (r • x) = ((algebraMap k k[G]) r) • ρ.ρ.asModuleEquiv.symm x
        exact ρ.ρ.asModuleEquiv_symm_map_smul r x }
  let _ : Module.Finite k W0 :=
    Module.Finite.of_surjective f fun y : W0 ↦ ⟨ρ.ρ.asModuleEquiv y, by rfl⟩
  let _ : Module.Finite k[G] W0 := Module.Finite.of_restrictScalars_finite k k[G] W0
  let W : FGModuleCat k[G] := by
    refine ⟨W0, ?_⟩
    change Module.Finite k[G] W0
    infer_instance
  letI : NeZero (Nat.card G : k) := by
    refine ⟨Nat.cast_ne_zero.mpr ?_⟩
    exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  have hproj : Module.Projective k[G] W := by
    -- Maschke makes the underlying finite `k[G]`-module projective.
    change Module.Projective k[G] W0
    exact Module.projective_of_isSemisimpleRing _ _
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨W, hproj⟩
  refine ⟨P, ?_⟩
  rw [cartanHom_projectiveClass_eq]
  let σ := P.toFiniteRep
  let eRep :
      ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≅
        ((forget₂ (FDRep k G) (Rep k G)).obj V) := by
    simpa [σ, P, W, W0, ρ, FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      (Rep.unitIso ρ).symm
  let e : σ ≅ V := by
    refine ⟨(FDRep.forget₂HomLinearEquiv σ V) eRep.hom,
      (FDRep.forget₂HomLinearEquiv V σ) eRep.inv, ?_, ?_⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  -- The projective model is isomorphic to `V`, so it defines the same Grothendieck class.
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) ⟨e⟩

/-- Helper for Theorem 17-17.2-4: in characteristic zero the Cartan range is all of the ordinary
Grothendieck group. -/
private theorem cartan_range_eq_top_of_charZero [CharZero k] :
    (cartanHom k G).range = ⊤ := by
  -- Reduce the quotient owner to honest finite-dimensional generators and replace each one by its
  -- projective Maschke model.
  rw [AddMonoidHom.range_eq_top]
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro V
    rcases exists_projective_preimage_of_fdrep_charZero (k := k) (G := G) V with ⟨P, hP⟩
    exact ⟨[P]ₚ₀, hP⟩
  · intro a ha
    rcases ha with ⟨y, hy⟩
    exact ⟨-y, by simpa [hy]⟩
  · intro a b ha hb
    rcases ha with ⟨ya, hya⟩
    rcases hb with ⟨yb, hyb⟩
    exact ⟨ya + yb, by simpa [map_add, hya, hyb]⟩

/-- Helper for Theorem 17-17.2-4: a `DFinsupp` map built from componentwise `ℚ`-linear
isomorphisms is itself bijective. -/
lemma dfinsupp_mapRange_bijective_of_bijective
    {ι : Type*}
    {β₁ β₂ : ι → Type*}
    [∀ i, AddCommGroup (β₁ i)] [∀ i, Module ℚ (β₁ i)]
    [∀ i, AddCommGroup (β₂ i)] [∀ i, Module ℚ (β₂ i)]
    (f : ∀ i, β₁ i →ₗ[ℚ] β₂ i)
    (hf : ∀ i, Function.Bijective (f i)) :
    Function.Bijective (DFinsupp.mapRange.linearMap f) := by
  -- Upgrade each componentwise bijection to a linear equivalence, then use the canonical
  -- `DFinsupp.mapRange.linearEquiv`.
  let e : ∀ i, β₁ i ≃ₗ[ℚ] β₂ i := fun i ↦ LinearEquiv.ofBijective (f i) (hf i)
  simpa [e] using (DFinsupp.mapRange.linearEquiv e).bijective

/-- Helper for Theorem 17-17.2-4: the integral Cartan map viewed as a `ℤ`-linear map. -/
private abbrev integral_cartan_linearMap :=
  (cartanHom k G).toIntLinearMap

/-- Helper for Theorem 17-17.2-4: the rationalized Cartan map as the literal base change of the
integral Cartan homomorphism. -/
private abbrev rationalized_cartan_linearMap :=
  (integral_cartan_linearMap (k := k) (G := G)).baseChange ℚ

/-- Helper for Theorem 17-17.2-4: a pure tensor of an integral multiple rewrites as the same
integral multiple of the corresponding rationalized pure tensor. -/
private theorem tmul_nsmul_eq_nsmul_tmul
    (q : ℚ) (y : R₀[k](G)) (N : ℕ) :
    q ⊗ₜ[ℤ] (N • y) = (N : ℚ) • (q ⊗ₜ[ℤ] y) := by
  induction N with
  | zero =>
      -- The zero multiple gives the zero tensor on both sides.
      simp
  | succ N ih =>
      -- Peel off one copy of `y` and rewrite the remaining multiple by the induction hypothesis.
      rw [succ_nsmul, TensorProduct.tmul_add, ih, Nat.cast_add, Nat.cast_one, add_smul, one_smul]

/-- Helper for Theorem 17-17.2-4: the tensorized Cartan map hits a nonzero integer multiple of
every rationalized ordinary Grothendieck class. -/
private theorem rationalized_cartan_hits_nonzero_multiple
    (x : ℚ ⊗[ℤ] R₀[k](G)) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∃ y : ℚ ⊗[ℤ] P₀[k](G),
        rationalized_cartan_linearMap (k := k) (G := G) y = (N : ℚ) • x := by
  by_cases hchar0 : ringChar k = 0
  · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero (R := k)).mp hchar0
    have hrange : (cartanHom k G).range = ⊤ :=
      cartan_range_eq_top_of_charZero (k := k) (G := G)
    have hsurj : Function.Surjective (integral_cartan_linearMap (k := k) (G := G)) := by
      -- In characteristic zero the integral Cartan map is already onto, so its rationalization
      -- hits the target exactly with multiplier `1`.
      rw [AddMonoidHom.range_eq_top] at hrange
      intro y
      rcases hrange y with ⟨z, hz⟩
      exact ⟨z, by simpa [integral_cartan_linearMap] using hz⟩
    have hsurjQ :
        Function.Surjective (rationalized_cartan_linearMap (k := k) (G := G)) := by
      -- Tensoring a surjective integral map with `ℚ` keeps it surjective.
      simpa [rationalized_cartan_linearMap, LinearMap.baseChange_eq_ltensor] using
        (LinearMap.lTensor_surjective (Q := ℚ) hsurj)
    rcases hsurjQ x with ⟨y, hy⟩
    exact ⟨1, one_ne_zero, y, by simpa using hy⟩
  · let p := ringChar k
    letI : CharP k p := ringChar.charP (R := k)
    have hp_ne_zero : p ≠ 0 := hchar0
    have hp_ne_one : p ≠ 1 := CharP.char_ne_one k p
    have hp_two_le : 2 ≤ p := by
      omega
    letI : Fact p.Prime := ⟨CharP.char_is_prime_of_two_le k p hp_two_le⟩
    let n := Nat.factorization (Nat.card G) p
    let m := ordCompl[p] (Nat.card G)
    have hcard_hm := card_eq_ordProj_mul_ordCompl_and_coprime (k := k) (G := G) (p := p)
    -- In positive characteristic, Serre's source route provides one fixed `p`-power multiple of
    -- every integral target class inside the Cartan image; tensor induction lifts that to `ℚ`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · refine ⟨1, one_ne_zero, 0, ?_⟩
      simp [rationalized_cartan_linearMap]
    · intro q y
      rcases
          cartanHom_surjective_on_p_part_multiples
            (p := p) (k := k) (G := G) n m hcard_hm.1 hcard_hm.2 y with
        ⟨z, hz⟩
      refine ⟨p ^ n, pow_ne_zero _ (Nat.Prime.ne_zero Fact.out), q ⊗ₜ[ℤ] z, ?_⟩
      calc
        rationalized_cartan_linearMap (k := k) (G := G) (q ⊗ₜ[ℤ] z) =
            q ⊗ₜ[ℤ] integral_cartan_linearMap (k := k) (G := G) z := by
              rw [rationalized_cartan_linearMap, LinearMap.baseChange_tmul]
        _ = q ⊗ₜ[ℤ] cartanHom k G z := by
              simp [integral_cartan_linearMap]
        _ = q ⊗ₜ[ℤ] ((p ^ n) • y) := by
              rw [hz]
        _ = (((p ^ n : ℕ) : ℚ)) • (q ⊗ₜ[ℤ] y) := by
              exact tmul_nsmul_eq_nsmul_tmul (k := k) (G := G) q y (p ^ n)
    · intro x y hx hy
      rcases hx with ⟨Nx, hNx, ξx, hξx⟩
      rcases hy with ⟨Ny, hNy, ξy, hξy⟩
      let N := Nx * Ny
      refine ⟨N, Nat.mul_ne_zero hNx hNy, (Ny : ℚ) • ξx + (Nx : ℚ) • ξy, ?_⟩
      -- Clear the two fixed multiples simultaneously and then add the resulting identities.
      calc
        rationalized_cartan_linearMap (k := k) (G := G)
            ((Ny : ℚ) • ξx + (Nx : ℚ) • ξy) =
              (Ny : ℚ) • rationalized_cartan_linearMap (k := k) (G := G) ξx +
                (Nx : ℚ) • rationalized_cartan_linearMap (k := k) (G := G) ξy := by
                  rw [map_add, map_smul, map_smul]
        _ = (Ny : ℚ) • ((Nx : ℚ) • x) + (Nx : ℚ) • ((Ny : ℚ) • y) := by
              rw [hξx, hξy]
        _ = ((N : ℕ) : ℚ) • (x + y) := by
              simp [N, smul_add, smul_smul, mul_comm]

/-- Helper for Theorem 17-17.2-4: the tensorized Cartan map is bijective over `ℚ`. -/
theorem rationalized_cartan_linearMap_bijective :
    Function.Bijective (rationalized_cartan_linearMap (k := k) (G := G)) := by
  refine ⟨?_, ?_⟩
  · -- Injectivity survives base change because `ℚ` is flat over `ℤ`.
    simpa [rationalized_cartan_linearMap, LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap
        (M := ℚ) (integral_cartan_linearMap (k := k) (G := G))
        (by simpa [integral_cartan_linearMap] using (cartanHom_injective (k := k) (G := G))))
  · -- Surjectivity follows from the fixed-multiple witness and division by that nonzero integer.
    exact
      surjective_of_exists_nat_smul_preimage
        (rationalized_cartan_linearMap (k := k) (G := G))
        (rationalized_cartan_hits_nonzero_multiple (k := k) (G := G))

/-- Helper for Theorem 17-17.2-4: the rationalized Cartan map viewed only as the tensorized
integral Cartan homomorphism. -/
noncomputable abbrev rationalizedCartanLinearEquiv :
    (ℚ ⊗[ℤ] P₀[k](G)) ≃ₗ[ℚ] ℚ ⊗[ℤ] R₀[k](G) :=
  -- Package the rationalized Cartan map as the actual base-changed linear map together with its
  -- explicit bijectivity proof.
  LinearEquiv.ofBijective
    (rationalized_cartan_linearMap (k := k) (G := G))
    (rationalized_cartan_linearMap_bijective (k := k) (G := G))

/-- Helper for Theorem 17-17.2-4: the rationalized Cartan equivalence acts on pure tensors by the
tensorized integral Cartan map. -/
theorem rationalizedCartanLinearEquiv_apply_tmul
    (q : ℚ) (x : P₀[k](G)) :
    rationalizedCartanLinearEquiv (k := k) (G := G) (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] cartanHom k G x := by
  -- The equivalence was defined from the base-changed Cartan map, so the pure-tensor formula is
  -- exactly the standard `baseChange_tmul` computation.
  calc
    rationalizedCartanLinearEquiv (k := k) (G := G) (q ⊗ₜ[ℤ] x) =
        q ⊗ₜ[ℤ] integral_cartan_linearMap (k := k) (G := G) x := by
          simpa [rationalizedCartanLinearEquiv] using
            (LinearMap.baseChange_tmul
              (f := integral_cartan_linearMap (k := k) (G := G)) (A := ℚ) q x)
    _ = q ⊗ₜ[ℤ] cartanHom k G x := by
          simp [integral_cartan_linearMap]

end ProjectiveRow

end Representation
