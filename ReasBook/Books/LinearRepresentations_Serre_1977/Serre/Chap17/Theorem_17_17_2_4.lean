import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap17.Corollary_17_17_2_2.ElementarySubgroupInduction
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.DecompositionUnit
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.ProjectiveProjectionFormula
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_4.CharacterTransport
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_4.CyclicUnitDescent
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_4.ScalarMultipleDescent
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_4.PrimeFieldUnitPreimage
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_4.OrdinaryUnitSurjectivity

open scoped MonoidAlgebra Representation TensorProduct

noncomputable section

universe u

namespace Representation

section OrdinaryRow

variable (k : Type u) [Field k]
variable (G : Type u) [Group G] [Finite G]

/-- Helper for Theorem 17-17.2-4: the ordinary Grothendieck group carries its canonical additive
commutative monoid structure. -/
private local instance ordinary_finiteRepGrothendieckAddCommMonoid
    (H : Type u) [Group H] [Finite H] : AddCommMonoid (R₀[k](H)) :=
  (QuotientAddGroup.Quotient.addCommGroup
    (finiteRepGrothendieckRelations k H)).toAddCommMonoid

/-- Helper for Theorem 17-17.2-4: the ordinary Grothendieck group carries its canonical additive
group structure. -/
private local instance ordinary_finiteRepGrothendieckAddCommGroup
    (H : Type u) [Group H] [Finite H] : AddCommGroup (R₀[k](H)) :=
  QuotientAddGroup.Quotient.addCommGroup
    (finiteRepGrothendieckRelations k H)

/-- Helper for Theorem 17-17.2-4: the ordinary Grothendieck group carries its canonical
`ℤ`-module structure. -/
private local instance ordinary_finiteRepGrothendieckIntModule
    (H : Type u) [Group H] [Finite H] : Module ℤ (R₀[k](H)) :=
  AddCommGroup.toIntModule (R₀[k](H))

local instance instDecEqCyclic_t1724a : DecidableEq ↥(_root_.Subgroup.cyclicSubgroups G) :=
  Classical.decEq _

/-- Helper for Theorem 17-17.2-4: the only unresolved ordinary-row branch is Serre's positive-
characteristic mixed-character descent. -/
private theorem cyclic_rationalized_induction_lsum_surjective_of_positiveChar_local
    (hchar : ringChar k ≠ 0) :
    Function.Surjective (cyclic_rationalized_induction_lsum k G) := by
  -- Serre's fixed-unit route, in positive characteristic.  Let `p = ringChar k`.  The
  -- characteristic-zero cyclic Artin theorem over the fraction field of the Witt-vector
  -- `p`-modular system, descended through the decomposition homomorphism and then transported
  -- along the prime-field inclusion `𝔽_p ⊆ k`, produces a preimage of the ring unit
  -- `1 ⊗ [trivial]` (see `cyclic_rationalized_unit_preimage`).  The image of induction is an ideal
  -- (projection formula), so containing the unit makes it everything.
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_prime_of_ne_zero k hchar⟩
  haveI : CharP k (ringChar k) := ringChar.charP k
  obtain ⟨ξ, hξ⟩ :=
    Representation.cyclic_rationalized_unit_preimage (k := k) (G := G) (ringChar k)
  exact
    Representation.cyclic_ordinary_rationalized_induction_surjective_of_unit_preimage
      k G ξ hξ

/-- Helper for Theorem 17-17.2-4: the characteristic-zero branch still needs the local
Grothendieck-character transport that used to live in the theorem-local support import. -/
private theorem cyclic_rationalized_induction_lsum_surjective_of_charZero_local [CharZero k] :
    Function.Surjective (cyclic_rationalized_induction_lsum k G) := by
  exact cyclic_rationalized_induction_lsum_surjective_of_charZero (k := k) (G := G)

/-- Theorem 17-17.2-4 (1): if `T` is the set of cyclic subgroups of `G`, then the induction map
`ℚ ⊗ Ind : ⨁_{H ∈ T} (ℚ ⊗ R_k(H)) → ℚ ⊗ R_k(G)` is surjective; in Lean the direct sum is
realized as a `DFinsupp` over `Subgroup.cyclicSubgroups G`. -/
theorem cyclicSubgroupRationalizedFiniteRepGrothendieckInduction_surjective :
    Function.Surjective
      (cyclic_rationalized_induction_lsum k G) := by
  by_cases hchar : ringChar k = 0
  · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero (R := k)).mp hchar
    -- The characteristic-zero branch is a separate transport problem from Chapter `12`.
    exact cyclic_rationalized_induction_lsum_surjective_of_charZero_local (k := k) (G := G)
  · -- Route correction: keep the remaining positive-characteristic frontier isolated in a single
    -- helper so the characteristic-zero branch and the projective-row transport remain compiled.
    exact
      cyclic_rationalized_induction_lsum_surjective_of_positiveChar_local
        (k := k) (G := G) hchar

end OrdinaryRow

section ProjectiveRow

variable (k : Type u) [Field k]
variable (G : Type u) [Group G] [Finite G]

/-- Helper for Theorem 17-17.2-4: the projective Grothendieck group has its canonical additive
commutative monoid structure. -/
private local instance projective_finiteProjectiveGrothendieckAddCommMonoid
    (H : Type u) [Group H] [Finite H] : AddCommMonoid (P₀[k](H)) :=
  (QuotientAddGroup.Quotient.addCommGroup
    (finiteProjectiveGroupAlgebraGrothendieckRelations k H)).toAddCommMonoid

/-- Helper for Theorem 17-17.2-4: the projective Grothendieck group has its canonical additive
group structure. -/
private local instance projective_finiteProjectiveGrothendieckAddCommGroup
    (H : Type u) [Group H] [Finite H] : AddCommGroup (P₀[k](H)) :=
  QuotientAddGroup.Quotient.addCommGroup
    (finiteProjectiveGroupAlgebraGrothendieckRelations k H)

/-- Helper for Theorem 17-17.2-4: the projective Grothendieck group carries the induced
`ℤ`-module structure. -/
private local instance projective_finiteProjectiveGrothendieckIntModule
    (H : Type u) [Group H] [Finite H] : Module ℤ (P₀[k](H)) :=
  AddCommGroup.toIntModule (P₀[k](H))

local instance instDecEqCyclic_t1724b : DecidableEq ↥(_root_.Subgroup.cyclicSubgroups G) :=
  Classical.decEq _

/-- Helper for Theorem 17-17.2-4: multiplying a fixed projective class by an ordinary
Grothendieck class is an integral linear map. -/
private def projective_smul_intLinearMap (z : P₀[k](G)) :
    R₀[k](G) →ₗ[ℤ] P₀[k](G) where
  toFun a := a • z
  map_add' := by
    intro a b
    exact add_smul a b z
  map_smul' := by
    intro n a
    rw [← Int.cast_smul_eq_zsmul (R := R₀[k](G)) (n := n) (b := a)]
    rw [smul_assoc]
    rw [Int.cast_smul_eq_zsmul (R := R₀[k](G)) (n := n) (b := a • z)]
    simp

/-- Helper for Theorem 17-17.2-4: the rationalized projective action of the ordinary unit is the
identity on pure projective tensors. -/
private theorem baseChange_projective_smul_unit_tmul
    (q : ℚ) (z : P₀[k](G)) :
    ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
        (q ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G))) =
      q ⊗ₜ[ℤ] z := by
  calc
    ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
        (q ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G))) =
        q ⊗ₜ[ℤ]
          (([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) • z) := by
            rw [LinearMap.baseChange_tmul]
            rfl
    _ = q ⊗ₜ[ℤ] z := by
      rw [finiteRepGrothendieckClass_trivial_eq_one (G := G) k]
      simp

/-- Helper for Theorem 17-17.2-4: the projective projection formula after rationalizing both
ordinary and projective Grothendieck groups. -/
private theorem rationalized_projective_projection_formula
    (H : _root_.Subgroup.cyclicSubgroups G)
    (a : ℚ ⊗[ℤ] R₀[k](H.1)) (z : P₀[k](G)) :
    ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
        ((Subgroup.finiteRepGrothendieckGroupRationalizedInduction
          (k := k) (G := G) H.1) a) =
      (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
          (k := k) (G := G) H.1)
        (((projective_smul_intLinearMap
            (k := k) (G := H.1)
            (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction
              (k := k) (G := G) H.1 z)).baseChange ℚ) a) := by
  refine TensorProduct.induction_on a ?_ ?_ ?_
  · simp [Subgroup.finiteRepGrothendieckGroupRationalizedInduction,
      Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction]
  · intro q x
    calc
      ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
          ((Subgroup.finiteRepGrothendieckGroupRationalizedInduction
            (k := k) (G := G) H.1) (q ⊗ₜ[ℤ] x)) =
          q ⊗ₜ[ℤ]
            ((Subgroup.finiteRepGrothendieckGroupInduction k H.1 x) • z) := by
              rw [Subgroup.finiteRepGrothendieckGroupRationalizedInduction,
                LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
              rfl
      _ =
          q ⊗ₜ[ℤ]
            (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction k H.1
              (x •
                Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction
                  (k := k) (G := G) H.1 z)) := by
            rw [finiteProjectiveGroupAlgebraGrothendieckGroupInduction_smul H.1 x z]
      _ =
          (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
              (k := k) (G := G) H.1)
            (((projective_smul_intLinearMap
                (k := k) (G := H.1)
                (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction
                  (k := k) (G := G) H.1 z)).baseChange ℚ) (q ⊗ₜ[ℤ] x)) := by
              rw [Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction,
                LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
              rfl
  · intro x y hx hy
    simpa [map_add] using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Theorem 17-17.2-4: the direct-sum version of the rationalized projective
projection formula. -/
private theorem cyclic_projective_lsum_mapRange_eq_projective_smul_lsum
    (ξ : Π₀ H : _root_.Subgroup.cyclicSubgroups G, ℚ ⊗[ℤ] R₀[k](H.1))
    (z : P₀[k](G)) :
    (DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦
        (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
          (k := k) (G := G) H.1 :
          (ℚ ⊗[ℤ] P₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] P₀[k](G))))
      (DFinsupp.mapRange.linearMap
        (fun H : _root_.Subgroup.cyclicSubgroups G =>
          ((projective_smul_intLinearMap
            (k := k) (G := H.1)
            (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction
              (k := k) (G := G) H.1 z)).baseChange ℚ)) ξ) =
      ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
        ((cyclic_rationalized_induction_lsum k G) ξ) := by
  let f :
      ∀ H : _root_.Subgroup.cyclicSubgroups G,
        (ℚ ⊗[ℤ] R₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] P₀[k](H.1)) :=
    fun H =>
      ((projective_smul_intLinearMap
        (k := k) (G := H.1)
        (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction
          (k := k) (G := G) H.1 z)).baseChange ℚ)
  let hP :
      ∀ H : _root_.Subgroup.cyclicSubgroups G,
        (ℚ ⊗[ℤ] P₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] P₀[k](G)) :=
    fun H =>
      (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
        (k := k) (G := G) H.1 :
        (ℚ ⊗[ℤ] P₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] P₀[k](G)))
  have hmaps :
      (DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦ (hP H).comp (f H)) =
        ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ).comp
          (cyclic_rationalized_induction_lsum k G) := by
    apply DFinsupp.lhom_ext
    intro H x
    simpa [f, hP, LinearMap.comp_apply] using
      (rationalized_projective_projection_formula (k := k) (G := G) H x z).symm
  calc
    (DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦
        (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
          (k := k) (G := G) H.1 :
          (ℚ ⊗[ℤ] P₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] P₀[k](G))))
      (DFinsupp.mapRange.linearMap
        (fun H : _root_.Subgroup.cyclicSubgroups G =>
          ((projective_smul_intLinearMap
            (k := k) (G := H.1)
            (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction
              (k := k) (G := G) H.1 z)).baseChange ℚ)) ξ) =
        (DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦ (hP H).comp (f H)) ξ := by
          simpa [f, hP] using
            (DFinsupp.sum_mapRange_index.linearMap
              (f := f) (h := hP) (l := ξ))
    _ =
        ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
          ((cyclic_rationalized_induction_lsum k G) ξ) := by
            simpa [LinearMap.comp_apply] using congrArg (fun e => e ξ) hmaps

/-- Helper for Theorem 17-17.2-4: Serre's projection-formula argument in the projective row,
reduced to a preimage of the ordinary rationalized unit. -/
private theorem cyclic_projective_rationalized_induction_surjective_of_ordinary_unit_preimage
    (ξ : Π₀ H : _root_.Subgroup.cyclicSubgroups G, ℚ ⊗[ℤ] R₀[k](H.1))
    (hξ :
      (cyclic_rationalized_induction_lsum k G) ξ =
        ((1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)))) :
    Function.Surjective
      (DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦
        (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
          (k := k) (G := G) H.1 :
          (ℚ ⊗[ℤ] P₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] P₀[k](G)))) := by
  intro p
  refine TensorProduct.induction_on p ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro q z
    let η : Π₀ H : _root_.Subgroup.cyclicSubgroups G, ℚ ⊗[ℤ] P₀[k](H.1) :=
      DFinsupp.mapRange.linearMap
        (fun H : _root_.Subgroup.cyclicSubgroups G =>
          ((projective_smul_intLinearMap
            (k := k) (G := H.1)
            (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction
              (k := k) (G := G) H.1 z)).baseChange ℚ))
        ((q : ℚ) • ξ)
    refine ⟨η, ?_⟩
    have hunit :
          ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
              ((cyclic_rationalized_induction_lsum k G) ((q : ℚ) • ξ)) =
            q ⊗ₜ[ℤ] z := by
      calc
        ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
            ((cyclic_rationalized_induction_lsum k G) ((q : ℚ) • ξ)) =
            ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
              (q • ((cyclic_rationalized_induction_lsum k G) ξ)) := by
                rw [map_smul]
        _ =
            ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
              (q • ((1 : ℚ) ⊗ₜ[ℤ]
                ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)))) := by
                  rw [hξ]
        _ =
            ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
              (q ⊗ₜ[ℤ]
                ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G))) := by
                  rw [TensorProduct.smul_tmul']
                  simp
        _ = q ⊗ₜ[ℤ] z := by
          exact baseChange_projective_smul_unit_tmul (k := k) (G := G) q z
    calc
      (DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦
          (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
            (k := k) (G := G) H.1 :
            (ℚ ⊗[ℤ] P₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] P₀[k](G))) ) η =
          ((projective_smul_intLinearMap (k := k) (G := G) z).baseChange ℚ)
            ((cyclic_rationalized_induction_lsum k G) ((q : ℚ) • ξ)) := by
            simpa [η] using
              cyclic_projective_lsum_mapRange_eq_projective_smul_lsum
                (k := k) (G := G) ((q : ℚ) • ξ) z
      _ = q ⊗ₜ[ℤ] z := hunit
  · intro x y hx hy
    rcases hx with ⟨vx, hvx⟩
    rcases hy with ⟨vy, hvy⟩
    exact ⟨vx + vy, by simp [map_add, hvx, hvy]⟩

/-- Theorem 17-17.2-4 (2): if `T` is the set of cyclic subgroups of `G`, then the induction map
`ℚ ⊗ Ind : ⨁_{H ∈ T} (ℚ ⊗ P_k(H)) → ℚ ⊗ P_k(G)` is surjective; in Lean the direct sum is
realized as a `DFinsupp` over `Subgroup.cyclicSubgroups G`. -/
theorem cyclicSubgroupRationalizedFiniteProjectiveRepGrothendieckInduction_surjective :
    Function.Surjective
      (DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦
        (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
          (k := k) (G := G) H.1 :
          (ℚ ⊗[ℤ] P₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] P₀[k](G)))) := by
  rcases cyclicSubgroupRationalizedFiniteRepGrothendieckInduction_surjective (k := k) (G := G)
      ((1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G))) with
    ⟨ξ, hξ⟩
  exact
    cyclic_projective_rationalized_induction_surjective_of_ordinary_unit_preimage
      (k := k) (G := G) ξ hξ

end ProjectiveRow

end Representation
