import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped StandardSimplex

/- Lemma 6.3 lives in the finite simplex / entropy prox-geometry domain.

Sampled owner declarations:
* mathlib `stdSimplex`, via the Chapter 6 notation `Δ[n]`;
* mathlib `stdSimplex.barycenter` and `stdSimplex.barycenter_apply`, the canonical simplex center;
* project `entropyFunction` in `Chap02/Proposition_2_5`, the entropy owner on `Fin n → ℝ`;
* project `simplexL1Seminorm` and
  `entropyFunction_strongConvexOnWith_l1_stdSimplex` in `Chap02/Proposition_2_5`, the owner
  strong-convexity API on `Δ[n]`;
* project `EuclideanSpace.l1Seminorm` and
  `EuclideanSpace.entropyFunction_strongConvexOnWith_l1_preimage_stdSimplex` in
  `Chap02/Proposition_2_5`, the Euclidean-coordinate bridge;
* project `normalizedEntropyProxFunction` in `Chap06/Definition_6_14`.

Best owner abstraction:
* source-facing: the three textbook entropy-prox facts of Lemma 6.3, evaluated at the simplex
  center `(1 / n) \bar e_n`;
* core/canonical: `Δ[n]`, `stdSimplex.barycenter`, `entropyFunction`,
  `normalizedEntropyProxFunction`, `simplexL1Seminorm`, `StrongConvexOnWith`, and `IsGreatest`;
* bridge/view: the Euclidean-coordinate realization of the canonical simplex barycenter and the
  Euclidean pullback of the simplex owner theorem.

Primitive data:
* the positive dimension `n : ℕ+`;
* the canonical simplex barycenter `(stdSimplex.barycenter : Δ[n])`.

Derived API:
* the Euclidean-coordinate bridge `stdSimplexBarycenterEuclidean`;
* the simplex-owner strong-convexity theorem for the ambient normalized entropy formula on
  `Δ[n]`;
* the Euclidean-coordinate bridge theorem for that owner statement;
* the value-at-center and maximal-value statements for `normalizedEntropyProxFunction`.

Source/core/bridge triage:
* source-facing: the three entropy-prox statements from Lemma 6.3;
* core/canonical owners reused directly: `Δ[n]`, `stdSimplex.barycenter`, `entropyFunction`,
  `normalizedEntropyProxFunction`, `simplexL1Seminorm`, `StrongConvexOnWith`, and `IsGreatest`;
* bridge/view kept here: `stdSimplexBarycenterEuclidean` and the Euclidean-coordinate transport of
  the simplex owner theorem.

The previous local duplicates `probabilitySimplex`, `simplexEntropyProxFunction`, and
`IsOneStronglyConvexOnProbabilitySimplex` have been deleted. Their mathematical content is already
owned canonically upstream by the simplex owner `Δ[n]`, the entropy owner `entropyFunction`, the
normalized entropy prox owner `normalizedEntropyProxFunction`, and the seminorm-based strong
convexity owner `StrongConvexOnWith`.
-/

/-- The Euclidean-coordinate realization of the canonical barycenter of `Δ_n`. -/
abbrev stdSimplexBarycenterEuclidean (n : ℕ+) : EuclideanSpace ℝ (Fin (n : ℕ)) :=
  (EuclideanSpace.equiv (Fin (n : ℕ)) ℝ).symm (stdSimplex.barycenter : Δ[n])

-- Proof sketch: Proposition 2.5 gives the owner strong-convexity statement for `entropyFunction`
-- on `Δ[n]`; adding the constant `log n` yields the ambient formula whose restriction to `Δ[n]`
-- is `normalizedEntropyProxFunction n`.
/-- Lemma 6.3 (1): on the simplex owner `Δ_n`, the ambient normalized entropy formula underlying
`normalizedEntropyProxFunction n` is `1`-strongly convex with respect to the canonical `ℓ₁`
seminorm. -/
theorem normalizedEntropyProxFunction_strongConvexOnWith_l1_stdSimplex (n : ℕ+) :
    StrongConvexOnWith
      (simplexL1Seminorm (n : ℕ)) 1
      Δ[n]
      (fun x ↦ Real.log (n : ℝ) + entropyFunction (n : ℕ) x) := sorry

-- Proof sketch: transport the simplex-owner strong-convexity statement along the coordinate
-- equivalence `EuclideanSpace.equiv (Fin n) ℝ`.
/-- Euclidean-coordinate bridge for Lemma 6.3 (1). -/
theorem normalizedEntropyProxFunction_strongConvexOnWith_l1_preimage_stdSimplex (n : ℕ+) :
    StrongConvexOnWith
      (EuclideanSpace.l1Seminorm (n : ℕ)) 1
      ((EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) ⁻¹' Δ[n])
      (fun x : EuclideanSpace ℝ (Fin (n : ℕ)) ↦
        Real.log (n : ℝ) +
          entropyFunction (n : ℕ) ((EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) x)) := sorry

-- Proof sketch: evaluate the normalized entropy prox-function at the canonical simplex barycenter;
-- the entropy sum consists of `n` equal terms `(1 / n) * log (1 / n)`, and the added `log n`
-- cancels the total.
/-- Lemma 6.3 (2): the normalized entropy prox-function vanishes at the canonical barycenter
`(1 / n) \bar e_n` of `Δ_n`. -/
theorem normalizedEntropyProxFunction_barycenter_eq_zero (n : ℕ+) :
    normalizedEntropyProxFunction n (stdSimplex.barycenter : Δ[n]) = 0 := sorry

-- Proof sketch: the entropy contribution is nonpositive on `Δ[n]`, so
-- `normalizedEntropyProxFunction n x ≤ log n` for all simplex points `x`; equality is attained at
-- any simplex vertex.
/-- Lemma 6.3 (3): the normalized entropy prox-function has maximal value `log n` on `Δ_n`. -/
theorem isGreatest_range_normalizedEntropyProxFunction_eq_log (n : ℕ+) :
    IsGreatest (Set.range (normalizedEntropyProxFunction n)) (Real.log (n : ℝ)) := sorry

/-- The supremum of the normalized entropy prox-function on `Δ_n` is `log n`. -/
theorem sSup_range_normalizedEntropyProxFunction_eq_log (n : ℕ+) :
    sSup (Set.range (normalizedEntropyProxFunction n)) = Real.log (n : ℝ) := by
  simpa using (isGreatest_range_normalizedEntropyProxFunction_eq_log n).csSup_eq
