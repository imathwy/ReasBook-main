import Mathlib
import StacksProject_2024.Chap15.Definition_15_92_4
import StacksProject_2024.Chap15.Lemma_15_92_6
import StacksProject_2024.Chap15.Proposition_15_92_5
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Polynomial
open scoped PrincipalIdeal BigOperators

section

variable (p : ℕ) [Fact p.Prime]

local notation "Zp" => ℤ_[p]
local notation "ZpPoly" => Polynomial Zp
local notation:max "(p)" => principalIdeal (p : Zp)
local notation "ZpPolyHat" => AdicCompletion (p) ZpPoly

/- Domain-style sampling:
- primary domain: `(p)`-adic completions of `ℤ_[p][X]`, module-category cokernels, and
  derived/adic completeness for the resulting example module;
- sampled owner-side declarations:
  `principalIdeal` together with the owner notation `(f)`,
  `AdicCompletion.map`,
  `cokernel`,
  `ModuleCat.cokernelIsoRangeQuotient`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the chapter owner `principalIdeal` for the ambient ideal `(p)`,
  together with the categorical cokernel of the completed substitution morphism; the
  quotient-by-range description remains only a bridge;
- primitive data: the principal ideal `(p)` in `ℤ_[p]` and the completed substitution linear map
  induced by `X ↦ pX`;
- derived API: the quotient-model bridge, derived completeness, the named geometric-series class in
  the cokernel, and failure of adic completeness.

Layer triage:
- `source-facing`: the completed substitution map and the example module defined as its cokernel;
- `core/canonical`: `AdicCompletion.map`, `cokernel`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`, `IsAdicComplete`, and `principalIdeal`/`(p)`;
- `bridge/view`: `ModuleCat.cokernelIsoRangeQuotient`, identifying the categorical cokernel with
  the explicit quotient by the image. -/

/-- The map on ordinary `p`-adic completions induced by the substitution
`ℤ_[p][X] → ℤ_[p][X]`, `X ↦ pX`. -/
abbrev padicPolynomialCompletionMap :
    ZpPolyHat →ₗ[Zp] ZpPolyHat :=
  (AdicCompletion.map (p)
      ((aeval (C (p : Zp) * X) : ZpPoly →ₐ[Zp] ZpPoly).toLinearMap)).restrictScalars Zp

/-- Example 15.94.4: the example module is the cokernel of the map on ordinary `p`-adic
completions induced by `ℤ_[p][x] → ℤ_[p][y]`, `x ↦ py`; using the common polynomial ring
`ℤ_[p][X]`, Lean takes the categorical cokernel of the completed substitution morphism
`X ↦ pX`. -/
@[stacks 0G3F]
abbrev padicPolynomialCompletionCokernel : ModuleCat Zp :=
  cokernel (ModuleCat.ofHom (padicPolynomialCompletionMap p))

-- Proof sketch: Proposition `15.92.5` gives derived completeness for the completed polynomial
-- modules, and Lemma `15.92.6` shows that the cokernel of a morphism between derived-complete
-- modules is again derived complete.
/-- The cokernel of the completed substitution map `X ↦ pX` is derived complete as a
`ℤ_[p]`-module with respect to `(p)`. -/
theorem padicPolynomialCompletionCokernel_isDerivedComplete :
    (padicPolynomialCompletionCokernel p).IsDerivedCompleteWithRespectTo
      (p) :=
  by
  let P : ObjectProperty (ModuleCat Zp) :=
    ModuleCat.derivedCompleteObjectProperty (p)
  letI : IsWeakSerreClass P := derivedCompleteObjectProperty_isWeakSerreClass (p)
  have hcompleteSource : P (ModuleCat.of Zp ZpPolyHat) := by
    -- Proof comment: the completed polynomial module is `(p)`-adically complete, so Proposition
    -- `15.92.5` supplies derived completeness with respect to `(p)`.
    exact ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete
      (ModuleCat.of Zp ZpPolyHat)
      (AdicCompletion.isAdicComplete (I := (p)) (M := ZpPoly) (principalIdeal_fg (p : Zp)))
  let f : ModuleCat.of Zp ZpPolyHat ⟶ ModuleCat.of Zp ZpPolyHat :=
    ModuleCat.ofHom (padicPolynomialCompletionMap p)
  have hcokernel : P (cokernel f) := by
    -- Proof comment: derived-complete modules form a weak Serre class, hence are closed under
    -- cokernels of morphisms between derived-complete modules.
    have hk :
        IsColimit (colimit.cocone (parallelPair f 0)) :=
      colimit.isColimit (parallelPair f 0)
    exact P.prop_of_isColimit_cokernelCofork hk hcompleteSource hcompleteSource
  simpa [P, f, padicPolynomialCompletionCokernel] using hcokernel

private abbrev padicPolynomialCompletionGeometricSeriesTruncation (n : ℕ) : ZpPoly :=
  ∑ i ∈ Finset.range n, C ((p : Zp) ^ i) * X ^ i

private abbrev padicPolynomialCompletionGeometricSeriesToQuotient (n : ℕ) :
    Zp →ₗ[Zp] (ZpPoly ⧸ (((p) ^ n) • (⊤ : Submodule Zp ZpPoly))) :=
  (Submodule.mkQ (((p) ^ n) • (⊤ : Submodule Zp ZpPoly))).comp <|
    LinearMap.smulRight (LinearMap.id : Zp →ₗ[Zp] Zp)
      (padicPolynomialCompletionGeometricSeriesTruncation p n)

/-- Helper for Example 15.94.4: the `(n + 1)`-st truncation is obtained by adjoining the
degree-`n` term to the `n`-th truncation. -/
private theorem padicPolynomialCompletionGeometricSeriesTruncation_succ
    (n : ℕ) :
    padicPolynomialCompletionGeometricSeriesTruncation p (n + 1) =
      padicPolynomialCompletionGeometricSeriesTruncation p n +
        C ((p : Zp) ^ n) * X ^ n := by
  -- Proof comment: this is the finite geometric-series recursion on the polynomial truncations.
  simp [padicPolynomialCompletionGeometricSeriesTruncation, Finset.sum_range_succ, add_comm]

/-- Helper for Example 15.94.4: passing from stage `n + 1` to stage `n` removes only the last
truncation term of the geometric-series family, and that last term is already killed modulo
`(p)^n`. -/
private theorem padicPolynomialCompletionGeometricSeriesToQuotient_compatible_succ
    (n : ℕ) :
    AdicCompletion.transitionMap (p) ZpPoly (Nat.le_succ n)
        (padicPolynomialCompletionGeometricSeriesToQuotient p (n + 1) 1) =
      padicPolynomialCompletionGeometricSeriesToQuotient p n 1 := by
  let Pn : Submodule Zp ZpPoly := ((p) ^ n) • (⊤ : Submodule Zp ZpPoly)
  have hp_mem : ((p : Zp) ^ n) ∈ ((p) : Ideal Zp) ^ n := by
    have hp : (p : Zp) ∈ ((p) : Ideal Zp) := by
      exact Ideal.subset_span (by simp)
    exact Ideal.pow_mem_pow hp n
  have htail_mem : C ((p : Zp) ^ n) * X ^ n ∈ Pn := by
    -- Proof comment: the new tail term carries a visible factor `p^n`, so it already vanishes in
    -- the stage-`n` quotient.
    simpa [Pn, smul_eq_C_mul] using
      (Submodule.smul_mem_smul hp_mem
        (show (X ^ n : ZpPoly) ∈ (⊤ : Submodule Zp ZpPoly) by simp))
  have htail_zero :
      Submodule.mkQ Pn (C ((p : Zp) ^ n) * X ^ n : ZpPoly) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero Pn).2 htail_mem
  calc
    AdicCompletion.transitionMap (p) ZpPoly (Nat.le_succ n)
        (padicPolynomialCompletionGeometricSeriesToQuotient p (n + 1) 1)
      = Submodule.mkQ Pn (padicPolynomialCompletionGeometricSeriesTruncation p (n + 1)) := by
          simp [padicPolynomialCompletionGeometricSeriesToQuotient, AdicCompletion.transitionMap]
    _ = Submodule.mkQ Pn
          (padicPolynomialCompletionGeometricSeriesTruncation p n +
            C ((p : Zp) ^ n) * X ^ n) := by
          rw [padicPolynomialCompletionGeometricSeriesTruncation_succ (p := p)]
    _ = Submodule.mkQ Pn (padicPolynomialCompletionGeometricSeriesTruncation p n) +
          Submodule.mkQ Pn (C ((p : Zp) ^ n) * X ^ n : ZpPoly) := by
          simpa using
            (map_add (Submodule.mkQ Pn)
              (padicPolynomialCompletionGeometricSeriesTruncation p n)
              (C ((p : Zp) ^ n) * X ^ n : ZpPoly))
    _ = Submodule.mkQ Pn (padicPolynomialCompletionGeometricSeriesTruncation p n) := by
          rw [htail_zero, add_zero]
    _ = padicPolynomialCompletionGeometricSeriesToQuotient p n 1 := by
          simp [padicPolynomialCompletionGeometricSeriesToQuotient]

/-- Helper for Example 15.94.4: after evaluating at a fixed scalar, the geometric-series
truncation family is compatible with all transition maps in the inverse system. -/
private theorem padicPolynomialCompletionGeometricSeriesToQuotient_compatible_apply
    {m n : ℕ} (hmn : m ≤ n) (x : Zp) :
    AdicCompletion.transitionMap (p) ZpPoly hmn
        (padicPolynomialCompletionGeometricSeriesToQuotient p n x) =
      padicPolynomialCompletionGeometricSeriesToQuotient p m x := by
  let stages :
      (k : ℕ) → ZpPoly ⧸ ((((p) : Ideal Zp) ^ k) • (⊤ : Submodule Zp ZpPoly)) :=
    fun k ↦ padicPolynomialCompletionGeometricSeriesToQuotient p k x
  have hanti :
      Antitone fun k ↦ ((((p) : Ideal Zp) ^ k) • (⊤ : Submodule Zp ZpPoly)) := by
    intro a b hab
    exact Submodule.pow_smul_top_le (I := ((p) : Ideal Zp)) (M := ZpPoly) hab
  have hsucc :
      ∀ k,
        stages k =
          AdicCompletion.transitionMap (p) ZpPoly (Nat.le_succ k) (stages (k + 1)) := by
    intro k
    simpa [stages, padicPolynomialCompletionGeometricSeriesToQuotient] using
      congrArg (fun y ↦ x • y)
        ((padicPolynomialCompletionGeometricSeriesToQuotient_compatible_succ (p := p) k).symm)
  -- Proof comment: once the one-step truncation identity is known, the general compatibility is
  -- the standard transitive quotient-factor statement for powers of a fixed ideal.
  simpa [stages, AdicCompletion.transitionMap, Submodule.factorPow] using
    (Submodule.eq_factor_of_eq_factor_succ hanti stages hsucc hmn).symm

private theorem padicPolynomialCompletionGeometricSeriesToQuotient_compatible
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap (p) ZpPoly hmn ∘ₗ
        padicPolynomialCompletionGeometricSeriesToQuotient p n =
      padicPolynomialCompletionGeometricSeriesToQuotient p m := by
  apply LinearMap.ext
  intro r
  simpa using
    (padicPolynomialCompletionGeometricSeriesToQuotient_compatible_apply (p := p) hmn r)

/-- Helper for Example 15.94.4: on dense polynomial points, the completed substitution map is
still given by polynomial evaluation at `pX`. -/
private theorem padicPolynomialCompletionMap_of (q : ZpPoly) :
    padicPolynomialCompletionMap p (AdicCompletion.of (p) ZpPoly q) =
      AdicCompletion.of (p) ZpPoly
        (((aeval (C (p : Zp) * X) : ZpPoly →ₐ[Zp] ZpPoly) q)) := by
  -- Proof comment: the completion map extends the original polynomial substitution, so it agrees
  -- with it on the dense image of `ZpPoly`.
  simp [padicPolynomialCompletionMap]

private noncomputable abbrev padicPolynomialCompletionGeometricSeries : ZpPolyHat :=
  (AdicCompletion.lift (p) (padicPolynomialCompletionGeometricSeriesToQuotient p)
    fun hle ↦ padicPolynomialCompletionGeometricSeriesToQuotient_compatible p hle) 1

/-- Helper for Example 15.94.4: evaluating the completed substitution map at stage `n` reduces to
the quotient class of the substituted polynomial representative. -/
private theorem padicPolynomialCompletionMap_eval_stage
    (n : ℕ) (xhat : ZpPolyHat) (q : ZpPoly)
    (hq : AdicCompletion.eval (p) ZpPoly n xhat =
      Submodule.mkQ (((p) ^ n) • (⊤ : Submodule Zp ZpPoly)) q) :
    AdicCompletion.eval (p) ZpPoly n ((padicPolynomialCompletionMap p) xhat) =
      Submodule.mkQ (((p) ^ n) • (⊤ : Submodule Zp ZpPoly))
        (((aeval (C (p : Zp) * X) : ZpPoly →ₐ[Zp] ZpPoly) q)) := by
  -- Proof comment: evaluate the completed map stagewise, then use the quotient-level formula for
  -- the induced map `reduceModIdeal`.
  change
    (AdicCompletion.map (p)
      ((aeval (C (p : Zp) * X) : ZpPoly →ₐ[Zp] ZpPoly).toLinearMap) xhat).val n = _
  rw [AdicCompletion.map_val_apply, hq]
  simpa using
    (LinearMap.reduceModIdeal_apply
      (I := ((p : Ideal Zp) ^ n))
      ((aeval (C (p : Zp) * X) : ZpPoly →ₐ[Zp] ZpPoly).toLinearMap)
      q)

/-- Helper for Example 15.94.4: the completion element defined by the compatible truncation family
has stage-`n` value equal to the `n`-th geometric-series truncation class. -/
private theorem padicPolynomialCompletionGeometricSeries_eval_stage
    (n : ℕ) :
    AdicCompletion.eval (p) ZpPoly n (padicPolynomialCompletionGeometricSeries p) =
      Submodule.mkQ (((p) ^ n) • (⊤ : Submodule Zp ZpPoly))
        (padicPolynomialCompletionGeometricSeriesTruncation p n) := by
  -- Proof comment: the completion element was built by lifting the compatible truncation family,
  -- so stage evaluation just reads off the `n`-th truncation.
  rw [padicPolynomialCompletionGeometricSeries]
  simpa [padicPolynomialCompletionGeometricSeriesToQuotient] using
    (AdicCompletion.eval_lift_apply
      (I := (p))
      (f := padicPolynomialCompletionGeometricSeriesToQuotient p)
      (h := fun hle ↦ padicPolynomialCompletionGeometricSeriesToQuotient_compatible p hle)
      n
      (1 : Zp))

/-- Helper for Example 15.94.4: substituting `pX` into the `n`-th partial sum recovers the
`n`-th geometric-series truncation on the dense polynomial locus. -/
private theorem padicPolynomialCompletionMap_partial_sum
    (n : ℕ) :
    padicPolynomialCompletionMap p
        (AdicCompletion.of (p) ZpPoly (∑ i in Finset.range n, X ^ i)) =
      AdicCompletion.of (p) ZpPoly
        (padicPolynomialCompletionGeometricSeriesTruncation p n) := by
  -- Proof comment: on dense polynomial points the completion map is still substitution
  -- `X ↦ pX`, and each monomial `X^i` becomes `p^i X^i`, exactly the `i`-th truncation term.
  rw [padicPolynomialCompletionMap_of]
  congr 1
  simp [padicPolynomialCompletionGeometricSeriesTruncation, mul_pow, mul_comm, mul_left_comm,
    mul_assoc]

/-- Helper for Example 15.94.4: the truncation at `n + m` splits into the first `n` terms plus
the shifted `m`-term tail. -/
private theorem padicPolynomialCompletionGeometricSeriesTruncation_split
    (n m : ℕ) :
    padicPolynomialCompletionGeometricSeriesTruncation p (n + m) =
      padicPolynomialCompletionGeometricSeriesTruncation p n +
        (C ((p : Zp) ^ n) * X ^ n) *
          padicPolynomialCompletionGeometricSeriesTruncation p m := by
  induction m with
  | zero =>
      -- Proof comment: the zero-tail case is the empty sum, so only the first `n` terms remain.
      simp [padicPolynomialCompletionGeometricSeriesTruncation]
  | succ m ihm =>
      -- Proof comment: append the `(n + m)`-th term, then factor the common shifted head.
      calc
        padicPolynomialCompletionGeometricSeriesTruncation p (n + (m + 1))
          = padicPolynomialCompletionGeometricSeriesTruncation p (n + m) +
              C ((p : Zp) ^ (n + m)) * X ^ (n + m) := by
                rw [Nat.add_assoc, padicPolynomialCompletionGeometricSeriesTruncation_succ]
        _ =
            (padicPolynomialCompletionGeometricSeriesTruncation p n +
              (C ((p : Zp) ^ n) * X ^ n) *
                padicPolynomialCompletionGeometricSeriesTruncation p m) +
              C ((p : Zp) ^ (n + m)) * X ^ (n + m) := by
                rw [ihm]
        _ =
            padicPolynomialCompletionGeometricSeriesTruncation p n +
              ((C ((p : Zp) ^ n) * X ^ n) *
                  padicPolynomialCompletionGeometricSeriesTruncation p m +
                C ((p : Zp) ^ (n + m)) * X ^ (n + m)) := by
                  rw [add_assoc]
        _ =
            padicPolynomialCompletionGeometricSeriesTruncation p n +
              ((C ((p : Zp) ^ n) * X ^ n) *
                  padicPolynomialCompletionGeometricSeriesTruncation p m +
                (C ((p : Zp) ^ n) * X ^ n) *
                  (C ((p : Zp) ^ m) * X ^ m)) := by
                  congr 1
                  simp [pow_add, mul_assoc, mul_left_comm, mul_comm]
        _ =
            padicPolynomialCompletionGeometricSeriesTruncation p n +
              (C ((p : Zp) ^ n) * X ^ n) *
                (padicPolynomialCompletionGeometricSeriesTruncation p m +
                  C ((p : Zp) ^ m) * X ^ m) := by
                    rw [mul_add]
        _ =
            padicPolynomialCompletionGeometricSeriesTruncation p n +
              (C ((p : Zp) ^ n) * X ^ n) *
                padicPolynomialCompletionGeometricSeriesTruncation p (m + 1) := by
                    rw [padicPolynomialCompletionGeometricSeriesTruncation_succ]

/-- Helper for Example 15.94.4: at stage `k`, any shifted polynomial with a visible factor
`p^n` vanishes once `k ≤ n`. -/
private theorem padicPolynomialCompletionStageMonomial_zero_of_le
    {k n : ℕ} (hkn : k ≤ n) (q : ZpPoly) :
    Submodule.mkQ (((p) ^ k) • (⊤ : Submodule Zp ZpPoly))
      (((C ((p : Zp) ^ n) * X ^ n) * q : ZpPoly)) = 0 := by
  -- TODO: show the scalar `p^n` already lies in the stage-`k` ideal power and then rewrite the
  -- polynomial as the scalar action of `p^n` on `(X^n) * q`.
  sorry

/-- Helper for Example 15.94.4: reducing a longer truncation to stage `k` forgets exactly the
terms carrying a visible factor of `p^k`. -/
private theorem padicPolynomialCompletionGeometricSeriesTruncation_eq_stage_of_le
    {k n : ℕ} (hkn : k ≤ n) :
    Submodule.mkQ (((p) ^ k) • (⊤ : Submodule Zp ZpPoly))
      (padicPolynomialCompletionGeometricSeriesTruncation p n) =
    Submodule.mkQ (((p) ^ k) • (⊤ : Submodule Zp ZpPoly))
      (padicPolynomialCompletionGeometricSeriesTruncation p k) := by
  -- TODO: write `n = k + m`, split the longer truncation by
  -- `padicPolynomialCompletionGeometricSeriesTruncation_split`, and kill the shifted tail with
  -- `padicPolynomialCompletionStageMonomial_zero_of_le`.
  sorry

/-- Helper for Example 15.94.4: evaluating the completed partial sum at stage `k` gives the
quotient class of the corresponding truncation polynomial. -/
private theorem padicPolynomialCompletionMap_partial_sum_eval_stage
    (n k : ℕ) :
    AdicCompletion.evalₐ (p) k
      (padicPolynomialCompletionMap p
        (AdicCompletion.of (p) ZpPoly (∑ i in Finset.range n, X ^ i))) =
      Submodule.mkQ (((p) ^ k) • (⊤ : Submodule Zp ZpPoly))
        (padicPolynomialCompletionGeometricSeriesTruncation p n) := by
  -- TODO: rewrite by `padicPolynomialCompletionMap_partial_sum` and then evaluate the dense
  -- polynomial representative with `AdicCompletion.evalₐ_of`.
  sorry

/-- Helper for Example 15.94.4: evaluating the shifted geometric series at stage `k` reduces to
the shifted truncation polynomial. -/
private theorem padicPolynomialCompletionGeometricSeries_shift_eval_stage
    (n k : ℕ) :
    AdicCompletion.evalₐ (p) k
      (((p : Zp) ^ n) • ((AdicCompletion.of (p) ZpPoly (X ^ n)) *
        padicPolynomialCompletionGeometricSeries p)) =
      Submodule.mkQ (((p) ^ k) • (⊤ : Submodule Zp ZpPoly))
        (((C ((p : Zp) ^ n) * X ^ n) *
          padicPolynomialCompletionGeometricSeriesTruncation p k : ZpPoly)) := by
  -- Proof comment: stage evaluation is multiplicative and `Zp`-linear, so it is enough to
  -- evaluate the dense monomial and the compatible truncation family separately.
  -- TODO: rewrite `evalₐ` across the scalar and product, then normalize the dense monomial stage
  -- with `AdicCompletion.evalₐ_of` and the geometric-series stage with
  -- `padicPolynomialCompletionGeometricSeries_eval_stage`.
  sorry

/-- Helper for Example 15.94.4: at stage `n + m`, the shifted geometric series keeps exactly the
first `m` tail terms after the visible `p^n X^n` factor is pulled out. -/
private theorem padicPolynomialCompletionGeometricSeries_tail_stage
    (n m : ℕ) :
    AdicCompletion.evalₐ (p) (n + m)
      (((p : Zp) ^ n) • ((AdicCompletion.of (p) ZpPoly (X ^ n)) *
        padicPolynomialCompletionGeometricSeries p)) =
      Submodule.mkQ (((p) ^ (n + m)) • (⊤ : Submodule Zp ZpPoly))
        (((C ((p : Zp) ^ n) * X ^ n) *
          padicPolynomialCompletionGeometricSeriesTruncation p m : ZpPoly)) := by
  let Pnm : Submodule Zp ZpPoly := ((p) ^ (n + m)) • (⊤ : Submodule Zp ZpPoly)
  -- Proof comment: evaluate the shifted completion element first, then split the long truncation
  -- into an `m`-term head plus a tail carrying the extra visible factor `p^m`.
  -- TODO: use `padicPolynomialCompletionGeometricSeries_shift_eval_stage`, then rewrite the long
  -- truncation by `padicPolynomialCompletionGeometricSeriesTruncation_split` and kill the extra
  -- tail term with `padicPolynomialCompletionStageMonomial_zero_of_le`.
  sorry

/-- Helper for Example 15.94.4: in the completion, the geometric series is the sum of its first
`n` substituted terms and the shifted tail multiplied by `p^n`. -/
private theorem padicPolynomialCompletionGeometricSeries_tail_identity
    (n : ℕ) :
    padicPolynomialCompletionGeometricSeries p =
      padicPolynomialCompletionMap p
        (AdicCompletion.of (p) ZpPoly (∑ i in Finset.range n, X ^ i)) +
      ((p : Zp) ^ n) •
        ((AdicCompletion.of (p) ZpPoly (X ^ n)) * padicPolynomialCompletionGeometricSeries p) := by
  let _ : Module ZpPoly ZpPolyHat := Algebra.toModule
  apply AdicCompletion.ext_evalₐ
  intro k
  by_cases hkn : k ≤ n
  · -- Proof comment: below stage `n`, the partial sum already matches the geometric series and the
    -- shifted tail is killed by the visible factor `p^n`.
    -- TODO: compare both sides with the common stage-`k` truncation and kill the visible
    -- `p^n`-tail term by `padicPolynomialCompletionStageMonomial_zero_of_le`.
    sorry
  · have hnk : n ≤ k := Nat.le_of_not_ge hkn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnk
    let Pnm : Submodule Zp ZpPoly := ((p) ^ (n + m)) • (⊤ : Submodule Zp ZpPoly)
    -- Proof comment: above stage `n`, split the truncation into its first `n` terms plus the
    -- visible tail, and compare that tail with the shifted completion element.
    -- TODO: rewrite the stage-`(n + m)` value of the geometric series by
    -- `padicPolynomialCompletionGeometricSeriesTruncation_split`, then replace the shifted tail by
    -- `padicPolynomialCompletionGeometricSeries_tail_stage`.
    sorry

-- Proof sketch: represent the formal series `1 + pX + p^2 X^2 + ⋯` by its compatible system of
-- truncations in the completed target polynomial ring. Its class in the cokernel is nonzero, and
-- multiplying by any power `p^n` shifts the series so that the class remains in `p^n M`.
/-- The class of `1 + pX + p^2 X^2 + ⋯` in the cokernel of the completed substitution map
`X ↦ pX`. -/
noncomputable abbrev padicPolynomialCompletionCokernelGeometricSeries :
    padicPolynomialCompletionCokernel p :=
  (cokernel.π (ModuleCat.ofHom (padicPolynomialCompletionMap p))).hom
    (padicPolynomialCompletionGeometricSeries p)

/-- The geometric-series class in the example cokernel is nonzero. -/
theorem padicPolynomialCompletionCokernelGeometricSeries_ne_zero :
    padicPolynomialCompletionCokernelGeometricSeries p ≠ 0 :=
  by
  -- Route correction: the bookkeeping lemmas for stagewise evaluation are now isolated above, so
  -- the remaining work is the source-faithful range obstruction using a fixed stage-`1`
  -- representative and its impossible mod-`p` coefficient pattern.
  -- TODO: identify the cokernel with the quotient by the image of `padicPolynomialCompletionMap p`,
  -- assume the geometric-series class vanishes, and use
  -- `padicPolynomialCompletionMap_eval_stage` together with
  -- `padicPolynomialCompletionGeometricSeries_eval_stage` to force a fixed mod-`p` polynomial
  -- representative to have coefficient `1` in arbitrarily large degrees, contradicting finite
  -- support.
  sorry

/-- The geometric-series class in the example cokernel lies in every submodule `p^n M`. -/
theorem padicPolynomialCompletionCokernelGeometricSeries_mem_p_pow_smul_top (n : ℕ) :
    padicPolynomialCompletionCokernelGeometricSeries p ∈
      ((p) ^ n) • (⊤ : Submodule Zp (padicPolynomialCompletionCokernel p)) :=
  by
  -- Route correction: the stagewise model of the geometric series is now explicit, so the only
  -- missing step is the direct source-style tail decomposition in the completion.
  -- TODO: project `padicPolynomialCompletionGeometricSeries_tail_identity` to the cokernel,
  -- use `cokernel.condition` to kill the dense partial-sum term, and then conclude by
  -- `Submodule.smul_mem_smul`.
  sorry

-- Proof sketch: the geometric-series class is nonzero and lies in `⋂ n, p^n M`, so the module is
-- not Hausdorff for the `(p)`-adic topology. Since `IsAdicComplete` includes Hausdorffness, the
-- cokernel cannot be `p`-adically complete.
/-- The example cokernel is not `p`-adically complete as a `ℤ_[p]`-module. -/
theorem padicPolynomialCompletionCokernel_not_isAdicComplete :
    ¬ IsAdicComplete (p) (padicPolynomialCompletionCokernel p) :=
  by
  intro hcomplete
  obtain ⟨_, hsep⟩ :=
    (ModuleCat.isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_iInf_pow_smul_eq_bot
      (M := padicPolynomialCompletionCokernel p)
      (I := (p))
      (principalIdeal_fg (p : Zp))).mp hcomplete
  have hmem :
      padicPolynomialCompletionCokernelGeometricSeries p ∈
        (⨅ n : ℕ,
          (((p) ^ n) • (⊤ : Submodule Zp (padicPolynomialCompletionCokernel p)) :
            Submodule Zp (padicPolynomialCompletionCokernel p)) := by
    -- Proof comment: the geometric-series witness lies in every `(p)^n`-multiple, hence in the
    -- intersection of those powers.
    rw [Submodule.mem_iInf]
    intro n
    exact padicPolynomialCompletionCokernelGeometricSeries_mem_p_pow_smul_top (p := p) n
  have hzero : padicPolynomialCompletionCokernelGeometricSeries p = 0 := by
    -- Proof comment: separatedness identifies the full intersection with `⊥`, so any element in
    -- that intersection must vanish.
    simpa [hsep] using hmem
  exact padicPolynomialCompletionCokernelGeometricSeries_ne_zero (p := p) hzero

end
