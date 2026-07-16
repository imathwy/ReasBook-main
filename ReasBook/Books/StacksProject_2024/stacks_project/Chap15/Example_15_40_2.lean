import Mathlib
import StacksProject_2024.stacks_project.Chap10.Remark_10_160_9
import StacksProject_2024.stacks_project.Chap15.Definition_15_37_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_37_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_39_1
import StacksProject_2024.stacks_project.Chap15.Proposition_15_35_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open PowerSeries
open IsLocalRing
open KaehlerDifferential
open scoped RatFunc
open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

universe u

section

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [ExpChar K p] [PerfectRing K p]
variable [Algebra (RatFunc (ZMod p)) K]
variable [IsPerfectClosure (algebraMap (RatFunc (ZMod p)) K) p]

local notation "k" => RatFunc (ZMod p)
local notation "A" => PowerSeries K

/- Domain-style sampling for Example 15.40.2:
- primary domain: adic formal smoothness of coefficient maps into one-variable power series rings
  over perfect closures in characteristic `p`;
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`,
  * `RingHom.formally_smooth_for_adic_baseChange`,
  * `regularLocalRing_formallySmooth_for_maximalIdeal_adic_tfae_by_characteristic`,
  * `zmod_to_mvPowerSeries_formally_smooth_for_madic`;
- best owner abstraction: the source-facing datum is still the specific ring homomorphism
  `f : RatFunc (ZMod p) →+* PowerSeries K` together with the condition on `f RatFunc.X`, but the
  topology owner on `PowerSeries K` should be the canonical local-ring ideal
  `maximalIdeal (PowerSeries K)` rather than the ad hoc presentation `Ideal.span {X}`;
- primitive data: the perfect-closure field `K`, the ring map `f`, and the equation
  `f RatFunc.X = C(t) + X`;
- derived API: adic formal smoothness of `f` for the one-variable power series target.

Source/core/bridge triage:
- `source-facing`: the Stacks example for the map sending `s` to `t + x`;
- `core/canonical`: `RingHom.formally_smooth_for_adic` and `maximalIdeal (PowerSeries K)`;
- `bridge/view`: the characteristic-`p` formal-smoothness criterion from Theorem `15.40.1`,
  specialized to this explicit map.
-/

-- Proof sketch: apply condition (5) of Theorem `15.40.1` through the differential criterion
-- described in the example. The source field `RatFunc (ZMod p)` has `Ω` free on `dX`, the chosen
-- map sends `X` to `t + x`, and hence `dX` maps to `dx`. Since `Ω[K[[x]]/𝔽_p]` is free on `dx`,
-- the induced map on differentials is injective, giving formal smoothness for the `(x)`-adic
-- topology.
/-- Helper for Example 15.40.2: one-variable power series over a field form a regular local ring. -/
lemma powerSeries_isRegularLocalRing : IsRegularLocalRing A := by
  -- This is the regular-local input for the characteristic-`p` criterion.
  infer_instance

/-- Helper for Example 15.40.2: the residue-level derivative detector sends
`1 ⊗ D(d(t + x))` to `1`. -/
lemma powerSeries_residue_derivative_tmul_D_shift :
    letI : CharP K p := by
      obtain hzero | ⟨q, hq, hchar⟩ := CharP.exists' K
      · letI : CharZero K := hzero
        letI : CharP K 0 := CharP.ofCharZero K
        have hp1 : p = 1 := expChar_one_of_char_zero K p
        exact False.elim (Nat.not_prime_one (hp1 ▸ Fact.out))
      · exact (ExpChar.eq (inferInstance : ExpChar K p) (ExpChar.prime hq.out)) ▸ hchar
    letI : CharP A p := charP_of_injective_algebraMap (algebraMap K A).injective p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) A := ZMod.algebra A p
    letI : IsScalarTower (ZMod p) K A :=
      IsScalarTower.of_algebraMap_eq fun x ↦
        RingHom.congr_fun
          (Subsingleton.elim (algebraMap (ZMod p) A)
            ((algebraMap K A).comp (algebraMap (ZMod p) K))) x
    let residueDerivative : Ω[A⁄ZMod p] →ₗ[A] ResidueField A :=
      (Ideal.Quotient.mkₐ A (maximalIdeal A)).toLinearMap.comp
        (((PowerSeries.derivative K).liftKaehlerDifferential).comp
          (KaehlerDifferential.map (ZMod p) K A A))
    let residueTensorDerivative :
        ResidueField A ⊗[A] Ω[A⁄ZMod p] →ₗ[ResidueField A] ResidueField A :=
      LinearMap.liftBaseChange (ResidueField A) residueDerivative
    residueTensorDerivative
        ((1 : ResidueField A) ⊗ₜ[A]
          D (ZMod p) A (C (algebraMap k K RatFunc.X) + X)) =
      1 := by
  letI : CharP K p := by
    obtain hzero | ⟨q, hq, hchar⟩ := CharP.exists' K
    · letI : CharZero K := hzero
      letI : CharP K 0 := CharP.ofCharZero K
      have hp1 : p = 1 := expChar_one_of_char_zero K p
      exact False.elim (Nat.not_prime_one (hp1 ▸ Fact.out))
    · exact (ExpChar.eq (inferInstance : ExpChar K p) (ExpChar.prime hq.out)) ▸ hchar
  letI : CharP A p := charP_of_injective_algebraMap (algebraMap K A).injective p
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : Algebra (ZMod p) A := ZMod.algebra A p
  letI : IsScalarTower (ZMod p) K A :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      RingHom.congr_fun
        (Subsingleton.elim (algebraMap (ZMod p) A)
          ((algebraMap K A).comp (algebraMap (ZMod p) K))) x
  let residueDerivative : Ω[A⁄ZMod p] →ₗ[A] ResidueField A :=
    (Ideal.Quotient.mkₐ A (maximalIdeal A)).toLinearMap.comp
      (((PowerSeries.derivative K).liftKaehlerDifferential).comp
        (KaehlerDifferential.map (ZMod p) K A A))
  let residueTensorDerivative :
      ResidueField A ⊗[A] Ω[A⁄ZMod p] →ₗ[ResidueField A] ResidueField A :=
    LinearMap.liftBaseChange (ResidueField A) residueDerivative
  -- Evaluate the tensorized detector on the distinguished differential class.
  change (LinearMap.liftBaseChange (ResidueField A) residueDerivative)
      ((1 : ResidueField A) ⊗ₜ[A]
        D (ZMod p) A (C (algebraMap k K RatFunc.X) + X)) =
    1
  simp only [LinearMap.liftBaseChange_tmul, one_smul]
  -- Split `d(C(t) + X)` into its constant and variable parts before evaluating.
  have hsplit :
      residueDerivative (D (ZMod p) A (C (algebraMap k K RatFunc.X) + X)) =
        residueDerivative (D (ZMod p) A (C (algebraMap k K RatFunc.X))) +
          residueDerivative (D (ZMod p) A X) := by
    rw [map_add, map_add]
  have hconst :
      residueDerivative (D (ZMod p) A (C (algebraMap k K RatFunc.X))) = 0 := by
    -- Constants have zero formal derivative after passing to the `K`-relative differential.
    change
      (Ideal.Quotient.mkₐ A (maximalIdeal A)).toLinearMap
          (((PowerSeries.derivative K).liftKaehlerDifferential)
            (KaehlerDifferential.map (ZMod p) K A A
              (D (ZMod p) A (C (algebraMap k K RatFunc.X))))) =
        0
    rw [KaehlerDifferential.map_D]
    simp
  have hvar :
      residueDerivative (D (ZMod p) A X) = 1 := by
    -- The `X`-term survives with derivative `1`.
    change
      (Ideal.Quotient.mkₐ A (maximalIdeal A)).toLinearMap
          (((PowerSeries.derivative K).liftKaehlerDifferential)
            (KaehlerDifferential.map (ZMod p) K A A (D (ZMod p) A X))) =
        1
    rw [KaehlerDifferential.map_D]
    simp
  rw [hsplit, hconst, hvar]
  simp

/-- Helper for Example 15.40.2: the polynomial generator maps to `RatFunc.X` under localization. -/
lemma polynomial_X_maps_to_ratFunc_X :
    algebraMap (Polynomial (ZMod p)) k Polynomial.X = RatFunc.X := by
  -- This is the canonical identification of the polynomial variable with the rational-function
  -- transcendental generator.
  simpa using (RatFunc.algebraMap_X (K := ZMod p))

/-- Helper for Example 15.40.2: the formal derivative on `Polynomial (ZMod p)` satisfies the
Leibniz rule as a `(ZMod p)`-derivation. -/
lemma polynomial_derivation_leibniz (a b : Polynomial (ZMod p)) :
    Polynomial.derivative (a * b) =
      a • Polynomial.derivative b + b • Polynomial.derivative a := by
  -- Rewrite the formal derivative product rule in module notation for later use with `Ω`.
  simp [smul_eq_mul, Polynomial.derivative_mul, add_comm, mul_comm]

/-- Helper for Example 15.40.2: the formal derivative defines the distinguished
`(ZMod p)`-derivation on `Polynomial (ZMod p)`. -/
noncomputable def polynomial_derivation :
    Derivation (ZMod p) (Polynomial (ZMod p)) (Polynomial (ZMod p)) :=
  Derivation.mk' Polynomial.derivative polynomial_derivation_leibniz

/-- Helper for Example 15.40.2: every polynomial differential is a multiple of `dX`. -/
lemma polynomial_D_mem_span_dX (f : Polynomial (ZMod p)) :
    D (ZMod p) (Polynomial (ZMod p)) f ∈
      (Polynomial (ZMod p)) ∙ D (ZMod p) (Polynomial (ZMod p)) Polynomial.X := by
  classical
  -- Induct on the polynomial presentation so the Leibniz rule only meets multiplication by `X`.
  refine Polynomial.induction_on f ?_ ?_ ?_
  · intro a
    simp
  · intro f g hf hg
    rw [map_add]
    exact Submodule.add_mem _ hf hg
  · intro n a ha
    have hX :
        D (ZMod p) (Polynomial (ZMod p)) Polynomial.X ∈
          (Polynomial (ZMod p)) ∙ D (ZMod p) (Polynomial (ZMod p)) Polynomial.X := by
      exact Submodule.mem_span_singleton.2 ⟨1, by simp⟩
    have hstep :
        D (ZMod p) (Polynomial (ZMod p)) (Polynomial.C a * Polynomial.X ^ (n + 1)) =
          ((Polynomial.C a * Polynomial.X ^ n : Polynomial (ZMod p))) •
              D (ZMod p) (Polynomial (ZMod p)) Polynomial.X +
            ((Polynomial.X : Polynomial (ZMod p))) •
              D (ZMod p) (Polynomial (ZMod p)) (Polynomial.C a * Polynomial.X ^ n) := by
      -- Rewrite the next monomial as the previous one times `X`, then apply Leibniz.
      calc
        D (ZMod p) (Polynomial (ZMod p)) (Polynomial.C a * Polynomial.X ^ (n + 1)) =
            D (ZMod p) (Polynomial (ZMod p))
              ((Polynomial.C a * Polynomial.X ^ n) * Polynomial.X) := by
              rw [pow_succ, mul_assoc]
        _ =
            ((Polynomial.C a * Polynomial.X ^ n : Polynomial (ZMod p))) •
                D (ZMod p) (Polynomial (ZMod p)) Polynomial.X +
              ((Polynomial.X : Polynomial (ZMod p))) •
                D (ZMod p) (Polynomial (ZMod p)) (Polynomial.C a * Polynomial.X ^ n) := by
              rw [Derivation.leibniz]
    rw [hstep]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hX) (Submodule.smul_mem _ _ ha)

/-- Helper for Example 15.40.2: `Ω[Polynomial (ZMod p)⁄ZMod p]` is generated by `dX`. -/
lemma polynomial_span_dX :
    (Polynomial (ZMod p)) ∙ D (ZMod p) (Polynomial (ZMod p)) Polynomial.X = ⊤ := by
  -- The universal differential module is spanned by the image of `D`, so it suffices to control
  -- each `D(f)` by the previous lemma.
  refine top_unique ?_
  rw [← KaehlerDifferential.span_range_derivation (ZMod p) (Polynomial (ZMod p))]
  refine Submodule.span_le.2 ?_
  intro y hy
  rcases hy with ⟨f, rfl⟩
  exact polynomial_D_mem_span_dX f

/-- Helper for Example 15.40.2: `Ω[Polynomial (ZMod p)⁄ZMod p]` is free of rank one on `dX`. -/
noncomputable def polynomial_kaehler_coordinate :
    Ω[Polynomial (ZMod p)⁄ZMod p] ≃ₗ[Polynomial (ZMod p)] Polynomial (ZMod p) := by
  let θ : Ω[Polynomial (ZMod p)⁄ZMod p] →ₗ[Polynomial (ZMod p)] Polynomial (ZMod p) :=
    polynomial_derivation.liftKaehlerDifferential
  let ι : Polynomial (ZMod p) →ₗ[Polynomial (ZMod p)] Ω[Polynomial (ZMod p)⁄ZMod p] :=
    LinearMap.smulRight (LinearMap.id : Polynomial (ZMod p) →ₗ[Polynomial (ZMod p)]
      Polynomial (ZMod p)) (D (ZMod p) (Polynomial (ZMod p)) Polynomial.X)
  refine LinearEquiv.ofLinear θ ι ?_ ?_
  · -- The source generator `dX` maps to `1`, so the candidate inverse is a right inverse.
    apply LinearMap.ext
    intro a
    simp [θ, ι, polynomial_derivation, Derivation.liftKaehlerDifferential_comp_D]
  · -- Every differential is a multiple of `dX`, so the same candidate is also a left inverse.
    apply LinearMap.ext
    intro y
    have hy :
        y ∈ (Polynomial (ZMod p)) ∙ D (ZMod p) (Polynomial (ZMod p)) Polynomial.X := by
      have hyTop : y ∈ (⊤ : Submodule (Polynomial (ZMod p)) Ω[Polynomial (ZMod p)⁄ZMod p]) := by
        simp
      rw [← polynomial_span_dX] at hyTop
      exact hyTop
    rcases Submodule.mem_span_singleton.1 hy with ⟨a, rfl⟩
    simp [θ, ι, polynomial_derivation, Derivation.liftKaehlerDifferential_comp_D]

/-- Helper for Example 15.40.2: the polynomial Kähler coordinate sends `dX` to `1`. -/
lemma polynomial_kaehler_coordinate_apply_D_X :
    polynomial_kaehler_coordinate
        (D (ZMod p) (Polynomial (ZMod p)) Polynomial.X) = 1 := by
  -- This records the distinguished generator value needed for the later localization step.
  change polynomial_derivation.liftKaehlerDifferential
      (D (ZMod p) (Polynomial (ZMod p)) Polynomial.X) = 1
  simp [polynomial_derivation, Derivation.liftKaehlerDifferential_comp_D]

/-- Helper for Example 15.40.2: base change along `Polynomial (ZMod p) → RatFunc (ZMod p)` sends
`1 ⊗ dX` to `d(RatFunc.X)`. -/
lemma ratFunc_kaehler_generator_from_polynomial :
    KaehlerDifferential.mapBaseChange (ZMod p) (Polynomial (ZMod p)) k
        (((1 : k) ⊗ₜ[Polynomial (ZMod p)]
          D (ZMod p) (Polynomial (ZMod p)) Polynomial.X)) =
      D (ZMod p) k RatFunc.X := by
  -- Rewrite the localized tensor generator through the canonical base-change formula.
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  simpa using polynomial_X_maps_to_ratFunc_X (p := p)

/-- Helper for Example 15.40.2: `Ω[k⁄ZMod p]` is one-dimensional on `d(RatFunc.X)`. -/
noncomputable def ratFunc_kaehler_coordinate :
    Ω[k⁄ZMod p] ≃ₗ[k] k := by
  letI : Algebra.FormallyEtale (Polynomial (ZMod p)) k :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := k)
      (nonZeroDivisors (Polynomial (ZMod p)))
  let sourceEquiv :
      k ⊗[Polynomial (ZMod p)] Ω[Polynomial (ZMod p)⁄ZMod p] ≃ₗ[k] Ω[k⁄ZMod p] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale (ZMod p) (Polynomial (ZMod p)) k
  let coordinateBaseChange :
      k ⊗[Polynomial (ZMod p)] Ω[Polynomial (ZMod p)⁄ZMod p] ≃ₗ[k]
        k ⊗[Polynomial (ZMod p)] Polynomial (ZMod p) :=
    LinearEquiv.baseChange (Polynomial (ZMod p)) k
      Ω[Polynomial (ZMod p)⁄ZMod p] (Polynomial (ZMod p))
      polynomial_kaehler_coordinate
  let scalarCollapse :
      k ⊗[Polynomial (ZMod p)] Polynomial (ZMod p) ≃ₗ[k] k :=
    TensorProduct.AlgebraTensorModule.rid (Polynomial (ZMod p)) k k
  -- Compose the formally étale comparison with the base-changed polynomial coordinate.
  exact sourceEquiv.symm.trans (coordinateBaseChange.trans scalarCollapse)

/-- Helper for Example 15.40.2: the rational-function Kähler coordinate sends
`d(RatFunc.X)` to `1`. -/
lemma ratFunc_kaehler_coordinate_apply_D_X :
    ratFunc_kaehler_coordinate (p := p)
        (D (ZMod p) k RatFunc.X) = 1 := by
  letI : Algebra.FormallyEtale (Polynomial (ZMod p)) k :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := k)
      (nonZeroDivisors (Polynomial (ZMod p)))
  let sourceEquiv :
      k ⊗[Polynomial (ZMod p)] Ω[Polynomial (ZMod p)⁄ZMod p] ≃ₗ[k] Ω[k⁄ZMod p] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale (ZMod p) (Polynomial (ZMod p)) k
  let coordinateBaseChange :
      k ⊗[Polynomial (ZMod p)] Ω[Polynomial (ZMod p)⁄ZMod p] ≃ₗ[k]
        k ⊗[Polynomial (ZMod p)] Polynomial (ZMod p) :=
    LinearEquiv.baseChange (Polynomial (ZMod p)) k
      Ω[Polynomial (ZMod p)⁄ZMod p] (Polynomial (ZMod p))
      polynomial_kaehler_coordinate
  let scalarCollapse :
      k ⊗[Polynomial (ZMod p)] Polynomial (ZMod p) ≃ₗ[k] k :=
    TensorProduct.AlgebraTensorModule.rid (Polynomial (ZMod p)) k k
  -- Evaluate the composed coordinate on the distinguished rational-function differential.
  have hsource :
      sourceEquiv.symm (D (ZMod p) k RatFunc.X) =
        ((1 : k) ⊗ₜ[Polynomial (ZMod p)]
          D (ZMod p) (Polynomial (ZMod p)) Polynomial.X) := by
    apply (LinearEquiv.symm_apply_eq (e := sourceEquiv)).2
    change D (ZMod p) k RatFunc.X =
      KaehlerDifferential.mapBaseChange (ZMod p) (Polynomial (ZMod p)) k
        (((1 : k) ⊗ₜ[Polynomial (ZMod p)]
          D (ZMod p) (Polynomial (ZMod p)) Polynomial.X))
    simpa using (ratFunc_kaehler_generator_from_polynomial (p := p)).symm
  change scalarCollapse
      (coordinateBaseChange
        (sourceEquiv.symm (D (ZMod p) k RatFunc.X))) = 1
  rw [hsource]
  rw [LinearEquiv.baseChange_tmul, polynomial_kaehler_coordinate_apply_D_X]
  simp [scalarCollapse]

/-- Helper for Example 15.40.2: a codomain ring equivalence carrying one adic ideal to another
preserves adic formal smoothness. -/
lemma formally_smooth_for_adic_of_codomain_ringEquiv_local
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (e : S ≃+* T) {J : Ideal S} {K : Ideal T}
    (hK : Ideal.map e.toRingHom J = K)
    (hf : f.formally_smooth_for_adic J) :
    (e.toRingHom.comp f).formally_smooth_for_adic K := by
  rw [RingHom.formally_smooth_for_adic_iff] at hf ⊢
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : TopologicalSpace S := Ideal.adicTopology J
  letI : TopologicalSpace T := Ideal.adicTopology K
  -- The equivalence is continuous in both directions because it sends the defining ideal to the
  -- defining ideal.
  have he_cont : Continuous e.toRingHom := by
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨1, ?_⟩
    simpa [pow_one] using hK.le
  have hsymm_map : Ideal.map e.symm.toRingHom K = J := by
    calc
      Ideal.map e.symm.toRingHom K =
          Ideal.map e.symm.toRingHom (Ideal.map e.toRingHom J) := by
            rw [hK]
      _ = Ideal.map (e.symm.toRingHom.comp e.toRingHom) J := by
            rw [Ideal.map_map]
      _ = J := by
            rw [show e.symm.toRingHom.comp e.toRingHom = RingHom.id S by
              ext x
              simpa using e.left_inv x]
            simp
  have he_symm_cont : Continuous e.symm.toRingHom := by
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    refine ⟨1, ?_⟩
    simpa [pow_one] using hsymm_map.le
  refine
    { toContinuous := he_cont.comp hf.toContinuous
      lift_condition := ?_ }
  intro B _ _ _ L _ hL g hg g0 hg0 hcomm
  let gS : S →+* B ⧸ L := g.comp e.toRingHom
  have hgS : Continuous gS := hg.comp he_cont
  have hcommS : (Ideal.Quotient.mk L).comp g0 = gS.comp f := by
    simpa [gS, RingHom.comp_assoc] using hcomm
  -- Conjugate the lifting problem across the codomain equivalence.
  obtain ⟨φS, hφScont, hφSquot, hφSbase⟩ :=
    RingHom.FormallySmoothTopologically.exists_lift hf L hL gS hgS g0 hg0 hcommS
  let φ : T →+* B := φS.comp e.symm.toRingHom
  have hφcont : Continuous φ := hφScont.comp he_symm_cont
  refine ⟨φ, hφcont, ?_, ?_⟩
  · ext t
    simpa [φ, gS] using DFunLike.congr_fun hφSquot (e.symm t)
  · ext r
    simpa [φ, RingHom.comp_assoc] using DFunLike.congr_fun hφSbase r

/-- Helper for Example 15.40.2: the shifted map is formally smooth for the `x`-adic topology by
descending from the split base change `K ⊗[k] A ≃ K`. -/
lemma ratFunc_to_powerSeries_shift_formally_smooth_core
    (f : k →+* A)
    (hfX : f RatFunc.X = C (algebraMap k K RatFunc.X) + X) :
    f.formally_smooth_for_adic (maximalIdeal A) := by
  -- Route correction: the tensor-collapse route should be restated over an explicit `[Algebra k A]`
  -- context with hypothesis `algebraMap k A RatFunc.X = C(t) + X`; the current attempt forced that
  -- structure through `letI`-dependent helper signatures, and Lean now loses the ring/algebra
  -- instances needed for `K ⊗[k] A` and the coefficient-field action.
  -- TODO: reintroduce the base-change helpers in the owner-stable form
  -- `∀ [Algebra k A], algebraMap k A RatFunc.X = C(t) + X → ...`, prove the explicit collapse
  -- `K ⊗[k] A ≃ₐ[K] K`, and then descend formal smoothness using
  -- `RingHom.formally_smooth_for_adic_of_split_baseChange`.
  sorry

/-- Example 15.40.2: let `k = RatFunc (ZMod p) = 𝔽_p(s)` and let `K` be a perfect closure of `k`,
modeling `𝔽_p(t)^{perf}`. If `f : k →+* K[[x]]`, formalized as
`f : RatFunc (ZMod p) →+* PowerSeries K`, sends the transcendental generator `s = RatFunc.X` to
`t + x`, where `t` is the image of `s` in `K`, then `f` is formally smooth for the `(x)`-adic
topology on `K[[x]]`; since `K` is a field, this is equivalently the
`maximalIdeal (PowerSeries K)`-adic topology. -/
theorem ratFunc_to_powerSeries_shift_formally_smooth_for_xadic
    (f : RatFunc (ZMod p) →+* PowerSeries K)
    (hfX :
      f RatFunc.X = C (algebraMap (RatFunc (ZMod p)) K RatFunc.X) + X) :
    f.formally_smooth_for_adic (maximalIdeal (PowerSeries K)) := by
  exact ratFunc_to_powerSeries_shift_formally_smooth_core (K := K) f hfX

end
