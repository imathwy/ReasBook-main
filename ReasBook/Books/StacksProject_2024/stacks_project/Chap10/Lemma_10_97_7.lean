import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_9
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IsLocalRing Ideal AdicCompletion

universe u v

section maximalIdealCompletionComparison

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "BCompletion" => AdicCompletion (maximalIdeal B) B

/-- Under a local homomorphism, every power of the source maximal ideal maps into the corresponding
power of the target maximal ideal. -/
theorem pow_maximalIdeal_le_comap_pow_maximalIdeal (f : A →+* B) [IsLocalHom f] (n : ℕ) :
    maximalIdeal A ^ n ≤ (maximalIdeal B ^ n).comap f := sorry

private def maximalIdealCompletionQuotientMap (f : A →+* B) [IsLocalHom f] (n : ℕ) :
    ACompletion →+* B ⧸ maximalIdeal B ^ n :=
  (Ideal.quotientMap (maximalIdeal B ^ n) f (pow_maximalIdeal_le_comap_pow_maximalIdeal f n)).comp
    (AdicCompletion.evalₐ (maximalIdeal A) n)

/-- The quotient maps defining the canonical map on maximal-ideal completions are compatible with
the transition maps in the inverse system for the target completion. -/
private theorem maximalIdealCompletionQuotientMap_compatible (f : A →+* B) [IsLocalHom f]
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) h).comp
        (maximalIdealCompletionQuotientMap f n) =
      maximalIdealCompletionQuotientMap f m := sorry

/-- The canonical map on maximal-ideal completions induced by a local homomorphism of local rings.
-/
noncomputable def maximalIdealCompletionMap (f : A →+* B) [IsLocalHom f] :
    ACompletion →+* BCompletion :=
  AdicCompletion.liftRingHom (maximalIdeal B) (maximalIdealCompletionQuotientMap f)
    (maximalIdealCompletionQuotientMap_compatible f)

/-- The canonical map on maximal-ideal completions extends the original local homomorphism. -/
theorem maximalIdealCompletionMap_comp (f : A →+* B) [IsLocalHom f] :
    (maximalIdealCompletionMap f).comp (algebraMap A ACompletion) =
      RingHom.comp (algebraMap B BCompletion) f := sorry

end maximalIdealCompletionComparison

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-
Domain-style sampling:
* primary domain: adic completions of local rings along the maximal ideal and its extension.
* source-facing layer: the maximal-ideal completion `S^∧` of `S` and its finiteness over `R^∧`.
* core/canonical owner: `AdicCompletion`, especially `adicCompletionLinearEquivOfPowLe` from
  Lemma `10.96.9` and `moduleFinite_of_finite_quotient_of_isHausdorff` from Lemma `10.96.12`.
* sampled upstream declarations:
  `maximalIdealCompletionMap`,
  `adicCompletionLinearEquivOfPowLe`,
  `adicCompletionLinearEquivOfPowLe_of`,
  `isAdicComplete_iff_of_pow_le`,
  `moduleFinite_of_finite_quotient_of_isHausdorff`.
* primitive data: the local rings `R`, `S`, the ideals `maximalIdeal R`, `maximalIdeal S`,
  `Ideal.map (algebraMap R S) (maximalIdeal R)`, and the quotient-finiteness hypothesis.
* derived API: the canonical completion map `R^∧ → S^∧`, the comparison between the two
  completions of `S`, and the finiteness bridge through the `mR S`-adic completion.
-/
local notation "mR" => maximalIdeal R
local notation "mS" => maximalIdeal S
local notation "mRS" => Ideal.map (algebraMap R S) mR
local notation "RCompletion" => AdicCompletion mR R
local notation "SCompletion" => AdicCompletion mS S
local notation "SmCompletion" => AdicCompletion mRS S

noncomputable instance maximalIdealCompletionAlgebra : Algebra RCompletion SCompletion :=
  (maximalIdealCompletionMap (algebraMap R S)).toAlgebra

/-- The quotient-level maps from `R^∧` to the quotients `S / (m_R S)^n` induced by `R → S`. -/
private def completionBaseQuotientMap (n : ℕ) : RCompletion →ₐ[R] S ⧸ mRS ^ n :=
  (Ideal.quotientMapₐ (mRS ^ n) (Algebra.ofId R S)
    ((Ideal.pow_right_mono (Ideal.le_comap_map : mR ≤ Ideal.comap (algebraMap R S) mRS) n).trans
      (Ideal.le_comap_pow (algebraMap R S) n))).comp
    (AdicCompletion.evalₐ mR n)

-- Proof sketch: reduce to a Cauchy sequence representative `f`; on the `m`-th quotient, the
-- compatibility condition is exactly the statement that `f n` and `f m` become equal modulo
-- `mR ^ m`, and mapping along `R → S` sends this congruence to one modulo `(mR S) ^ m`.
-- The quotient-level maps from `R^∧` to the quotients `S / (mR S)^n` are compatible with the
-- transition maps in the inverse system.
/-- The quotient-level maps `R^∧ → S / (m_R S)^n` are compatible with the transition maps of the
inverse system defining the `m_R S`-adic completion of `S`. -/
private theorem completionBaseQuotientMap_compatible {m n : ℕ} (h : m ≤ n) :
    ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h) :
      S ⧸ mRS ^ n →ₐ[R] S ⧸ mRS ^ m)).comp (completionBaseQuotientMap n) =
      completionBaseQuotientMap m := sorry

-- The canonical algebra morphism from `R^∧` to the `mR S`-adic completion of `S`.
/-- The canonical algebra morphism from `R^∧` to the `m_R S`-adic completion of `S`. -/
private def completionBaseAlgHom : RCompletion →ₐ[R] SmCompletion :=
  AdicCompletion.liftAlgHom mRS completionBaseQuotientMap completionBaseQuotientMap_compatible

private noncomputable instance completionBaseAlgebra : Algebra RCompletion SmCompletion :=
  completionBaseAlgHom.toAlgebra

/-- Evaluating `completionBaseAlgHom` modulo `(m_R S)^n` recovers the quotient map used to define
it. -/
private theorem completionBaseAlgHom_evalₐ (n : ℕ) (x : RCompletion) :
    AdicCompletion.evalₐ mRS n (completionBaseAlgHom x) = completionBaseQuotientMap n x := by
  simp [completionBaseAlgHom]

-- Proof sketch: the finite residue-fibre hypothesis makes the maximal ideal of
-- `S / mR S` nilpotent, hence some power of `maximalIdeal S` lies in `mR S`.
/-- Under the hypotheses of Lemma `10.97.7`, some positive power of `maximalIdeal S` is contained
in the extended maximal ideal `mR S`. This is the bridge needed to compare the two adic
filtrations on `S`. -/
theorem exists_pow_maximalIdeal_le_map_maximalIdeal
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    ∃ n : ℕ, 0 < n ∧ mS ^ n ≤ mRS := sorry

private noncomputable def maximalIdealCompletionExponent
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) : ℕ := by
  classical
  exact
    Nat.find
      (exists_pow_maximalIdeal_le_map_maximalIdeal hmR hfinite_quotient)

private theorem maximalIdealCompletionExponent_pos
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    0 < maximalIdealCompletionExponent hmR hfinite_quotient := by
  classical
  exact
    (Nat.find_spec
      (exists_pow_maximalIdeal_le_map_maximalIdeal hmR hfinite_quotient)).1

private theorem maximalIdealCompletionExponent_pow_le
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    mS ^ maximalIdealCompletionExponent hmR hfinite_quotient ≤ mRS := by
  classical
  exact
    (Nat.find_spec
      (exists_pow_maximalIdeal_le_map_maximalIdeal hmR hfinite_quotient)).2

/-- Lemma 10.97.7 comparison map: under the usual finiteness hypotheses, the maximal-ideal
completion `S^∧ = AdicCompletion (maximalIdeal S) S` is canonically identified, as an `S`-algebra,
with the `mR S`-adic completion of `S`. This keeps the source-facing completion comparison public,
while realizing it through the chapter's completion-comparison API from Lemma `10.96.9`. -/
noncomputable def maximalIdealCompletionAlgEquivMadicCompletion
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    SCompletion ≃ₐ[S] SmCompletion := by
  let e : SCompletion ≃ₗ[S] SmCompletion :=
    adicCompletionLinearEquivOfPowLe S mS mRS S
      (maximalIdealCompletionExponent hmR hfinite_quotient) 1
      (maximalIdealCompletionExponent_pos hmR hfinite_quotient)
      Nat.one_pos
      (maximalIdealCompletionExponent_pow_le hmR hfinite_quotient)
      (by
        simpa [pow_one] using IsLocalRing.map_maximalIdeal_le (algebraMap R S))
  let f : SCompletion →ₐ[S] SmCompletion :=
    { toFun := e
      map_zero' := e.map_zero
      map_one' := sorry
      map_add' := e.map_add
      map_mul' := sorry
      commutes' := sorry }
  exact AlgEquiv.ofBijective f e.bijective

@[simp]
theorem maximalIdealCompletionAlgEquivMadicCompletion_of
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS))
    (x : S) :
    maximalIdealCompletionAlgEquivMadicCompletion hmR hfinite_quotient (of mS S x) =
      of mRS S x := by
  change
    adicCompletionLinearEquivOfPowLe S mS mRS S
        (maximalIdealCompletionExponent hmR hfinite_quotient) 1
        (maximalIdealCompletionExponent_pos hmR hfinite_quotient)
        Nat.one_pos
        (maximalIdealCompletionExponent_pow_le hmR hfinite_quotient)
        (by
          simpa [pow_one] using IsLocalRing.map_maximalIdeal_le (algebraMap R S))
        (of mS S x) =
      of mRS S x
  exact
    adicCompletionLinearEquivOfPowLe_of S mS mRS S
      (maximalIdealCompletionExponent hmR hfinite_quotient) 1
      (maximalIdealCompletionExponent_pos hmR hfinite_quotient)
      Nat.one_pos
      (maximalIdealCompletionExponent_pow_le hmR hfinite_quotient)
      (by
        simpa [pow_one] using IsLocalRing.map_maximalIdeal_le (algebraMap R S))
      x

-- Proof sketch: `R^∧` is complete for `mR`, and by construction `SmCompletion` is complete for
-- `mR S`. The quotient modulo `mR` identifies with `S / mR S`, which is finite over `R / mR`.
-- Apply the owner-facing finite-generation criterion from Lemma `10.96.12`.
/-- Bridge companion for Lemma `10.97.7`: the `mR S`-adic completion of `S` is finite over
`R^∧`. -/
theorem madicCompletion_finite
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    Module.Finite RCompletion SmCompletion := sorry

/-- Lemma 10.97.7: for a local homomorphism `R → S` of local rings, if `mR` is finitely generated
and `S / mR S` is finite over `R / mR`, then the maximal-ideal completion `S^∧` is finite over
the maximal-ideal completion `R^∧`. -/
theorem maximalIdealCompletion_finite
    (hmR : (maximalIdeal R).FG)
    (hfinite_quotient : Module.Finite (R ⧸ mR) (S ⧸ mRS)) :
    Module.Finite RCompletion SCompletion := by
  let eS := (maximalIdealCompletionAlgEquivMadicCompletion hmR hfinite_quotient).toLinearEquiv
  let e : SCompletion ≃ₗ[RCompletion] SmCompletion :=
    { toFun := eS
      invFun := eS.symm
      map_add' := eS.map_add
      map_smul' := by
        intro c x
        sorry
      left_inv := eS.left_inv
      right_inv := eS.right_inv }
  letI : Module.Finite RCompletion SmCompletion :=
    madicCompletion_finite hmR hfinite_quotient
  exact Module.Finite.equiv e.symm

end
