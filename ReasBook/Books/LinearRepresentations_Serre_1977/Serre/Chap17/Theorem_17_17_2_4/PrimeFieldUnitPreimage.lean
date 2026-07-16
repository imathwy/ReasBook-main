import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_4.CharacterTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_4.ScalarExtensionInduction
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.DecompositionUnit
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.DecompositionInductionBridge
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.HindComplete
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2

/-!
# Unit preimage for the positive-characteristic cyclic Artin theorem

For a field `k` of positive characteristic `p`, the ring unit of `ℚ ⊗ R₀[k](G)` lies in the
image of rationalized induction from cyclic subgroups.  This is the genuine content of Serre's
Theorem 40 in positive characteristic.

The route is Serre's own: descend the characteristic-zero cyclic Artin theorem through the
decomposition homomorphism of a `p`-modular system, then transport along the prime-field
inclusion `𝔽_p ⊆ k`.  Concretely we use the Witt-vector `p`-modular system over the lifted prime
field `ULift (ZMod p)`, whose residue field is `𝔽_p` and admits the canonical ring map to any
field of characteristic `p`.
-/

noncomputable section

universe u

open scoped Representation TensorProduct
open CategoryTheory

namespace Representation

/-- Pin the canonical additive monoid structure on `R₀[F](H)` (matching the one baked into
`cyclic_rationalized_induction_lsum`) so rationalized objects share a single instance term. -/
private local instance instR0Monoid {F : Type u} [Field F] {H : Type u} [Group H] [Finite H] :
    AddCommMonoid (R₀[F](H)) :=
  (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations F H)).toAddCommMonoid

private local instance instR0Group {F : Type u} [Field F] {H : Type u} [Group H] [Finite H] :
    AddCommGroup (R₀[F](H)) :=
  QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations F H)

private local instance instR0IntModule {F : Type u} [Field F] {H : Type u} [Group H] [Finite H] :
    Module ℤ (R₀[F](H)) :=
  AddCommGroup.toIntModule (R₀[F](H))

/-- The Witt vectors over the lifted prime field have characteristic zero. -/
instance instCharZeroWittPrime (p : ℕ) [Fact p.Prime] :
    CharZero (WittVector p (ULift.{u} (ZMod p))) := by
  refine charZero_of_inj_zero ?_
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · exact hn0
      have hconst : (n : ULift.{u} (ZMod p)) = 0 := by
        simpa using congrArg
          (WittVector.constantCoeff : WittVector p (ULift.{u} (ZMod p)) →+* ULift.{u} (ZMod p)) hn
      have hpdvd : p ∣ n := (CharP.cast_eq_zero_iff (ULift.{u} (ZMod p)) p n).mp hconst
      rcases hpdvd with ⟨m, rfl⟩
      have hm_mul_zero :
          ((m : WittVector p (ULift.{u} (ZMod p))) *
            (p : WittVector p (ULift.{u} (ZMod p)))) = 0 := by
        simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hn
      have hm_zero : (m : WittVector p (ULift.{u} (ZMod p))) = 0 :=
        WittVector.eq_zero_of_p_mul_eq_zero (p := p) (k := ULift.{u} (ZMod p))
          (x := (m : WittVector p (ULift.{u} (ZMod p)))) hm_mul_zero
      have hm0 : m ≠ 0 := fun hm0 => hn0 (by simp [hm0])
      have hm_lt : m < p * m := by
        calc
          m = 1 * m := by simp
          _ < p * m :=
              Nat.mul_lt_mul_of_pos_right (show 1 < p from (Fact.out : Nat.Prime p).one_lt)
                (Nat.pos_of_ne_zero hm0)
      have hm_eq_zero : m = 0 := ih m hm_lt hm_zero
      simp [hm_eq_zero]

section PrimeFieldModel

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The `p`-modular system: Witt vectors over the lifted prime field. -/
abbrev wittA : Type u := WittVector p (ULift.{u} (ZMod p))

/-- Fraction field of the Witt DVR (characteristic zero). -/
abbrev wittK : Type u := FractionRing (wittA p)

/-- The residue field of the Witt DVR is canonically the lifted prime field. -/
def wittResidueEquiv :
    IsLocalRing.ResidueField (wittA p) ≃+* ULift.{u} (ZMod p) :=
  have hker :
      RingHom.ker (WittVector.constantCoeff : wittA p →+* ULift.{u} (ZMod p)) =
        IsLocalRing.maximalIdeal (wittA p) :=
    IsLocalRing.ker_eq_maximalIdeal
      (WittVector.constantCoeff : wittA p →+* ULift.{u} (ZMod p))
      (WittVector.constantCoeff_surjective (p := p))
  (Ideal.quotEquivOfEq hker.symm).trans <|
    RingHom.quotientKerEquivOfSurjective (WittVector.constantCoeff_surjective (p := p))

/-- The canonical ring map from the residue field `𝔽_p` of the Witt DVR to the
characteristic-`p` field `k`. -/
def wittResidueToField : IsLocalRing.ResidueField (wittA p) →+* k :=
  (ZMod.castHom (dvd_refl p) k).comp
    (ULift.ringEquiv.toRingHom.comp (wittResidueEquiv p).toRingHom)

/-- `k` is an algebra over the residue field `𝔽_p` via `wittResidueToField`. -/
@[reducible] def wittResidueAlgebra : Algebra (IsLocalRing.ResidueField (wittA p)) k :=
  (wittResidueToField (k := k) p).toAlgebra

end PrimeFieldModel

section Bridges

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

attribute [local instance] wittResidueAlgebra

/-- The decomposition homomorphism commutes with subgroup induction (the `hind` bridge from
Theorem 17-17.2-1, here for the Witt `p`-modular system and an arbitrary subgroup). -/
theorem decompositionHom_cyclicInduction (H : Subgroup G) (x : R₀[wittK p](H)) :
    decompositionHom (wittA p) (wittK p) G
        (Representation.Subgroup.finiteRepGrothendieckGroupInduction (wittK p) H x) =
      Representation.Subgroup.finiteRepGrothendieckGroupInduction
        (IsLocalRing.ResidueField (wittA p)) H
        (decompositionHom (wittA p) (wittK p) H x) :=
  decompositionHom_subgroupInduction_of_bridge (A := wittA p) (K := wittK p) H
    (hind_complete (A := wittA p) (K := wittK p) H) x

/-- The integral transport `R₀[K](H') → R₀[k](H')`: decompose to the residue field `𝔽_p`,
then scalar-extend to `k`. -/
def transHom (H' : Type u) [Group H'] [Finite H'] : R₀[wittK p](H') →+ R₀[k](H') :=
  (finiteRepGrothendieckScalarExtensionHom (IsLocalRing.ResidueField (wittA p)) k H').comp
    (decompositionHom (wittA p) (wittK p) H')

/-- The integral transport commutes with subgroup induction. -/
theorem transHom_cyclicInduction (H : Subgroup G) (x : R₀[wittK p](H)) :
    transHom (k := k) p G (Representation.Subgroup.finiteRepGrothendieckGroupInduction
        (wittK p) H x) =
      Representation.Subgroup.finiteRepGrothendieckGroupInduction k H
        (transHom (k := k) p H x) := by
  simp only [transHom, AddMonoidHom.comp_apply]
  rw [decompositionHom_cyclicInduction p H x]
  exact finiteRepGrothendieckScalarExtensionHom_subgroupInduction
    (F := IsLocalRing.ResidueField (wittA p)) (k := k) H
    (decompositionHom (wittA p) (wittK p) H x)

end Bridges

section UnitPreimage

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

attribute [local instance] wittResidueAlgebra

private local instance : DecidableEq ↥(_root_.Subgroup.cyclicSubgroups G) := Classical.decEq _

/-- The rationalized integral transport at a group. -/
def transRat (H' : Type u) [Group H'] [Finite H'] :
    (ℚ ⊗[ℤ] R₀[wittK p](H')) →ₗ[ℚ] (ℚ ⊗[ℤ] R₀[k](H')) :=
  (transHom (k := k) p H').toIntLinearMap.baseChange ℚ

/-- The rationalized transport commutes with rationalized subgroup induction (componentwise). -/
theorem transRat_cyclicInduction (H : Subgroup G) (x : ℚ ⊗[ℤ] R₀[wittK p](H)) :
    Representation.Subgroup.finiteRepGrothendieckGroupRationalizedInduction k H
        (transRat (k := k) p H x) =
      transRat (k := k) p G
        (Representation.Subgroup.finiteRepGrothendieckGroupRationalizedInduction (wittK p) H x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q y =>
      simp only [Representation.Subgroup.finiteRepGrothendieckGroupRationalizedInduction, transRat,
        LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap]
      rw [transHom_cyclicInduction p H y]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The lsum-level transport square: rationalized cyclic induction over `k` of the transported
family equals the transport of the rationalized cyclic induction over `K`. -/
theorem lsum_transRat
    (ξ : Π₀ H : _root_.Subgroup.cyclicSubgroups G, ℚ ⊗[ℤ] R₀[wittK p](H.1)) :
    cyclic_rationalized_induction_lsum k G
        (DFinsupp.mapRange.linearMap (fun H : _root_.Subgroup.cyclicSubgroups G =>
          transRat (k := k) p H.1) ξ) =
      transRat (k := k) p G
        (cyclic_rationalized_induction_lsum (wittK p) G ξ) := by
  let f : ∀ H : _root_.Subgroup.cyclicSubgroups G,
      (ℚ ⊗[ℤ] R₀[wittK p](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] R₀[k](H.1)) :=
    fun H => transRat (k := k) p H.1
  let hP : ∀ H : _root_.Subgroup.cyclicSubgroups G,
      (ℚ ⊗[ℤ] R₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] R₀[k](G)) :=
    fun H => Representation.Subgroup.finiteRepGrothendieckGroupRationalizedInduction k H.1
  have hmaps :
      (DFinsupp.lsum ℚ fun H => (hP H).comp (f H)) =
        (transRat (k := k) p G).comp (cyclic_rationalized_induction_lsum (wittK p) G) := by
    apply DFinsupp.lhom_ext
    intro H x
    simpa [f, hP, LinearMap.comp_apply] using transRat_cyclicInduction p H.1 x
  calc
    cyclic_rationalized_induction_lsum k G
        (DFinsupp.mapRange.linearMap (fun H : _root_.Subgroup.cyclicSubgroups G =>
          transRat (k := k) p H.1) ξ)
        = (DFinsupp.lsum ℚ fun H => (hP H).comp (f H)) ξ := by
            simpa [f, hP] using
              (DFinsupp.sum_mapRange_index.linearMap (f := f) (h := hP) (l := ξ))
    _ = (transRat (k := k) p G).comp (cyclic_rationalized_induction_lsum (wittK p) G) ξ := by
          simpa [LinearMap.comp_apply] using congrArg (fun e => e ξ) hmaps
    _ = transRat (k := k) p G (cyclic_rationalized_induction_lsum (wittK p) G ξ) := by
          rw [LinearMap.comp_apply]

/-- The transport sends the trivial-representation class over `K` to the trivial class over `k`. -/
theorem transHom_trivial :
    transHom (k := k) p G [FDRep.of (Representation.trivial (wittK p) G (wittK p))]₀ =
      [FDRep.of (Representation.trivial k G k)]₀ := by
  simp only [transHom, AddMonoidHom.comp_apply]
  rw [finiteRepGrothendieckClass_trivial_eq_one (G := G) (wittK p), decompositionHom_one,
    ← finiteRepGrothendieckClass_trivial_eq_one (G := G) (IsLocalRing.ResidueField (wittA p))]
  exact finiteRepGrothendieckScalarExtensionHom_trivial_class

include p in
/-- **Unit preimage (positive characteristic).** The ring unit `1 ⊗ [trivial]` of
`ℚ ⊗ R₀[k](G)` lies in the image of rationalized cyclic-subgroup induction. -/
theorem cyclic_rationalized_unit_preimage :
    ∃ ξ : Π₀ H : _root_.Subgroup.cyclicSubgroups G, ℚ ⊗[ℤ] R₀[k](H.1),
      cyclic_rationalized_induction_lsum k G ξ =
        (1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) := by
  obtain ⟨ξ, hξ⟩ :=
    cyclic_rationalized_induction_lsum_surjective_of_charZero (k := wittK p) (G := G)
      ((1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial (wittK p) G (wittK p))]₀ : R₀[wittK p](G)))
  refine ⟨DFinsupp.mapRange.linearMap (fun H : _root_.Subgroup.cyclicSubgroups G =>
    transRat (k := k) p H.1) ξ, ?_⟩
  rw [lsum_transRat, hξ]
  show transRat (k := k) p G
      ((1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial (wittK p) G (wittK p))]₀)) = _
  simp only [transRat, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap]
  rw [transHom_trivial]

end UnitPreimage

end Representation
