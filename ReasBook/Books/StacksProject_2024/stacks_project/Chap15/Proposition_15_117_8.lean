import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_42_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_116_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_46_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_112_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_116_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_116_8
import StacksProject_2024.stacks_project.Chap15.Lemma_15_117_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_117_7
import StacksProject_2024.stacks_project.Chap15.Theorem_15_116_18_Epp

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] [Algebra.EssFiniteType A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

/-- Helper for Proposition 15.117.8: over a perfect field, every algebraic field extension is
separable. -/
private theorem residueField_isSeparable_of_perfectField_of_isAlgebraic
    {k : Type*} {E : Type*} [Field k] [PerfectField k] [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E] :
    Algebra.IsSeparable k E := by
  -- First upgrade the perfect-base hypothesis to the Stacks Project separability owner.
  let hsepOver : Algebra.IsSeparableOver k E :=
    Algebra.IsSeparableOver.of_perfectField (F := k) (E := E)
  -- Then specialize that owner back to the algebraic separability statement.
  exact Algebra.IsSeparableOver.isSeparable (F := k) (E := E) hsepOver

/-- Helper for Proposition 15.117.8: Epp's residue-field hypothesis is vacuous when the source
residue field has characteristic zero. -/
private theorem epp_hypothesis_of_residueCharZero
    (hchar0 : ringChar (ResidueField A) = 0) :
    ringChar (ResidueField A) ≠ 0 →
      ∀ x : ResidueField B,
        x ∈ ⋂ n : ℕ+, Set.range
          (fun y : ResidueField B ↦ y ^ (ringChar (ResidueField A) ^ (n : ℕ))) →
          IsSeparable (ResidueField A) x := by
  -- In residue characteristic zero the antecedent is contradictory, so the hypothesis is automatic.
  intro hpos x hx
  exact False.elim (hpos (by simpa [hchar0]))

/-- Helper for Proposition 15.117.8: in positive residue characteristic, choose the source
`p`-basis and lifts in `A` that the textbook perfection construction starts from. -/
private theorem exists_residueField_pBasis_with_lifts_of_positive_residueChar
    (hchar : ringChar (ResidueField A) ≠ 0) :
    ∃ (ι : Type*) (x : ι → ResidueField A) (xLift : ι → A),
      IsPBasis (ringChar (ResidueField A))
        (ZMod (ringChar (ResidueField A))) (ResidueField A) x ∧
      ∀ i, IsLocalRing.residue A (xLift i) = x i := by
  let p := ringChar (ResidueField A)
  have hp_ne_zero : p ≠ 0 := by
    simpa [p] using hchar
  letI : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero (ResidueField A) hp_ne_zero⟩
  letI : CharP (ResidueField A) p := ringChar.charP (ResidueField A)
  -- First choose the source `p`-basis exactly as in Lemma `15.46.2`.
  obtain ⟨ι, x, hx⟩ :=
    exists_isPBasis (p := p) (k := ZMod p) (K := ResidueField A)
  -- Then lift each residue-class generator back to the DVR `A`.
  choose xLift hxLift using fun i : ι ↦ IsLocalRing.residue_surjective (x i)
  exact ⟨ι, x, xLift, by simpa [p] using hx, hxLift⟩

/-- Helper for Proposition 15.117.8: after fixing one algebraic closure of `K`, every chosen
lift in `A` admits a `p^n`-root there. -/
private theorem exists_pPower_root_of_lift_in_algClosure
    {ι : Type*} {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (xLift : ι → A) (i : ι) (n : ℕ) :
    ∃ z : Ω, z ^ (ringChar (ResidueField A) ^ n) =
      algebraMap K Ω (algebraMap A K (xLift i)) := by
  let c : Ω := algebraMap K Ω (algebraMap A K (xLift i))
  let f : Polynomial Ω := Polynomial.X ^ (ringChar (ResidueField A) ^ n) - Polynomial.C c
  -- The fixed algebraic closure of `K` contains a root of the displayed Kummer polynomial.
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero f
  use z
  have hz' : z ^ (ringChar (ResidueField A) ^ n) - c = 0 := by
    simpa [f, c] using hz
  exact sub_eq_zero.mp hz'

/-- Helper for Proposition 15.117.8: in one algebraic closure of `K`, each chosen lift admits a
compatible chain of successive `p`th roots. -/
private theorem exists_compatible_p_root_chain_in_algClosure
    (hchar : ringChar (ResidueField A) ≠ 0)
    {ι : Type*} {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (xLift : ι → A) :
    ∃ beta : ι → ℕ → Ω,
      (∀ i, beta i 0 = algebraMap K Ω (algebraMap A K (xLift i))) ∧
      ∀ i n, beta i (n + 1) ^ ringChar (ResidueField A) = beta i n := by
  classical
  let p := ringChar (ResidueField A)
  let _ := hchar
  -- Choose one `p`th root at a time inside the fixed algebraic closure.
  have hstep : ∀ z : Ω, ∃ y : Ω, y ^ p = z := by
    intro z
    let f : Polynomial Ω := Polynomial.X ^ p - Polynomial.C z
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero f
    use y
    have hy' : y ^ p - z = 0 := by
      simpa [f] using hy
    exact sub_eq_zero.mp hy'
  let stepChoice : Ω → Ω := fun z ↦ Classical.choose (hstep z)
  have hstepChoice : ∀ z : Ω, stepChoice z ^ p = z := by
    intro z
    exact Classical.choose_spec (hstep z)
  let beta : ι → ℕ → Ω := fun i ↦
    Nat.rec
      (algebraMap K Ω (algebraMap A K (xLift i)))
      (fun _ z ↦ stepChoice z)
  refine ⟨beta, ?_, ?_⟩
  · intro i
    simp [beta]
  · intro i n
    simp [beta, hstepChoice, p]

/-- Helper for Proposition 15.117.8: a compatible chain of successive `p`th roots recovers the
`p^n`-root relation for the original lift. -/
private theorem compatible_p_root_chain_pow_eq_lift
    {ι : Type*} {Ω : Type*} [Field Ω] [Algebra K Ω]
    (xLift : ι → A) (beta : ι → ℕ → Ω)
    (hbeta0 : ∀ i, beta i 0 = algebraMap K Ω (algebraMap A K (xLift i)))
    (hbetaStep : ∀ i n, beta i (n + 1) ^ ringChar (ResidueField A) = beta i n) :
    ∀ i n,
      beta i n ^ (ringChar (ResidueField A) ^ n) =
        algebraMap K Ω (algebraMap A K (xLift i)) := by
  let p := ringChar (ResidueField A)
  intro i n
  induction n with
  | zero =>
      -- At stage `0` the chain starts at the original lifted element.
      simpa [hbeta0 i, p]
  | succ n ihn =>
      -- Each successor relation converts one `p`th-root step into the expected `p^(n+1)` formula.
      calc
        beta i (n + 1) ^ (p ^ (n + 1))
            = beta i (n + 1) ^ (p ^ n * p) := by
                rw [pow_succ]
        _ = beta i (n + 1) ^ (p * p ^ n) := by
              rw [Nat.mul_comm]
        _ = (beta i (n + 1) ^ p) ^ (p ^ n) := by
              rw [pow_mul]
        _ = beta i n ^ (p ^ n) := by
              rw [hbetaStep i n]
        _ = algebraMap K Ω (algebraMap A K (xLift i)) := ihn

/-- Helper for Proposition 15.117.8: each successor in the compatible root chain is a root of the
one-step adjunction polynomial over the previous stage. -/
private theorem compatible_p_root_chain_aeval_eq_zero
    {ι : Type*} {Ω : Type*} [Field Ω] [Algebra K Ω]
    (beta : ι → ℕ → Ω)
    (hbetaStep : ∀ i n, beta i (n + 1) ^ ringChar (ResidueField A) = beta i n)
    (i : ι) (n : ℕ) :
    aeval (beta i (n + 1))
      (Polynomial.X ^ ringChar (ResidueField A) - Polynomial.C (beta i n) : Polynomial Ω) = 0 := by
  -- The chosen successor satisfies exactly the defining one-step polynomial equation.
  simpa [hbetaStep i n]

/-- Helper for Proposition 15.117.8: if a successor root already lies in an intermediate field,
then so does the previous root in the compatible chain. -/
private theorem compatible_p_root_chain_previous_mem_of_successor_mem
    {ι : Type*} {Ω : Type*} [Field Ω] [Algebra K Ω]
    (beta : ι → ℕ → Ω)
    (hbetaStep : ∀ i n, beta i (n + 1) ^ ringChar (ResidueField A) = beta i n)
    {i : ι} {n : ℕ} {E : IntermediateField K Ω}
    (hmem : beta i (n + 1) ∈ E) :
    beta i n ∈ E := by
  -- Raising an element of an intermediate field to the residue characteristic keeps it inside.
  have hpow :
      beta i (n + 1) ^ ringChar (ResidueField A) ∈ E := by
    exact E.pow_mem hmem _
  -- The compatibility relation identifies that power with the previous stage.
  simpa [hbetaStep i n] using hpow

/-- Helper for Proposition 15.117.8: adjoining one chosen compatible root to an intermediate
field produces a finite-dimensional next stage containing that root. -/
private theorem exists_simple_adjoin_stage_containing_root
    {ι : Type*} {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (beta : ι → ℕ → Ω) (i : ι) (n : ℕ) (E : IntermediateField K Ω) :
    ∃ E' : IntermediateField K Ω,
      E ≤ E' ∧ beta i (n + 1) ∈ E' ∧ FiniteDimensional E E' := by
  let E' : IntermediateField K Ω := IntermediateField.adjoin E ({beta i (n + 1)} : Set Ω)
  let _ : Algebra.IsAlgebraic E Ω := inferInstance
  let _ : Algebra.IsIntegral E Ω := Algebra.IsAlgebraic.isIntegral
  have hroot_integral : IsIntegral E (beta i (n + 1)) := by
    -- Every element of the fixed algebraic closure is algebraic, hence integral, over the stage.
    exact Algebra.IsIntegral.isIntegral (beta i (n + 1))
  have hfinite : FiniteDimensional E E' := by
    -- A simple adjunction of an integral element is finite-dimensional.
    simpa [E'] using IntermediateField.adjoin.finiteDimensional hroot_integral
  refine ⟨E', ?_, ?_, hfinite⟩
  · -- The new stage extends the old stage by construction.
    simpa [E'] using IntermediateField.le_adjoin E ({beta i (n + 1)} : Set Ω)
  · -- The chosen compatible root is one of the adjoined generators.
    exact IntermediateField.subset_adjoin (by simp [E'])

/-- Helper for Proposition 15.117.8: once a positive-characteristic source `p`-basis and lifts in
`A` are fixed, the remaining source-faithful work is to build the finite `p`-root stages from
Lemma `15.116.8`, pass to the perfected weakly-unramified base, solve branchwise there, and
descend the resulting solution to a finite extension of `K`. -/
private theorem exists_solution_of_positive_residueChar_via_perfected_base
    (hchar : ringChar (ResidueField A) ≠ 0)
    {ι : Type*} (x : ι → ResidueField A) (xLift : ι → A)
    (hxPBasis :
      IsPBasis (ringChar (ResidueField A))
        (ZMod (ringChar (ResidueField A))) (ResidueField A) x)
    (hxLift : ∀ i, IsLocalRing.residue A (xLift i) = x i) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSolutionFor A B K L K1 := by
  classical
  -- Proof comment: the first source-controlled object is the finite tower of `p^n`-root stages
  -- attached to the chosen `p`-basis lifts, where each nontrivial successor uses Lemma `15.116.8`.
  let _ := hchar
  let _ := hxPBasis
  let _ := hxLift
  let Ω := AlgebraicClosure K
  let _ : Field Ω := inferInstance
  let _ : Algebra K Ω := inferInstance
  let _ : IsAlgClosure K Ω := inferInstance
  obtain ⟨beta, hbeta0, hbetaStep⟩ :=
    exists_compatible_p_root_chain_in_algClosure
      (A := A) (K := K) (Ω := Ω) hchar xLift
  have hbetaPow :
      ∀ i n,
        beta i n ^ (ringChar (ResidueField A) ^ n) =
          algebraMap K Ω (algebraMap A K (xLift i)) := by
    -- Recover the older `p^n`-root interface from the source-faithful one-step chain.
    exact
      compatible_p_root_chain_pow_eq_lift
        (A := A) (K := K) (Ω := Ω) xLift beta hbeta0 hbetaStep
  have hbetaAeval :
      ∀ i n,
        aeval (beta i (n + 1))
          (Polynomial.X ^ ringChar (ResidueField A) - Polynomial.C (beta i n) : Polynomial Ω) = 0 :=
    compatible_p_root_chain_aeval_eq_zero
      (A := A) (K := K) (Ω := Ω) beta hbetaStep
  -- Proof comment: after forming the perfected weakly-unramified base, the residue field becomes
  -- perfect, so branchwise weak solutions upgrade to solutions via the generic perfect-field
  -- argument already proved above.
  -- Proof comment: the source-faithful compatible root chain is now in place, and `hbetaAeval`
  -- is exactly the polynomial-root datum needed to embed each `Lemma 15.116.8` one-step
  -- `AdjoinRoot` successor back into the fixed algebraic closure.
  let _ := beta
  let _ := hbeta0
  let _ := hbetaStep
  let _ := hbetaPow
  let _ := hbetaAeval
  have hSimpleStage :
      ∀ i n (E : IntermediateField K Ω),
        ∃ E' : IntermediateField K Ω,
          E ≤ E' ∧ beta i (n + 1) ∈ E' ∧ FiniteDimensional E E' := by
    intro i n E
    -- First package the algebraic part of the successor step as a simple finite adjunction.
    exact exists_simple_adjoin_stage_containing_root
      (A := A) (K := K) (Ω := Ω) beta i n E
  let _ := hSimpleStage
  -- TODO: upgrade `hSimpleStage` to the source-faithful successor-or-stay package from Agent C's
  -- plan. The remaining blocker is not algebraicity or finite-dimensionality of the next stage,
  -- but the missing earlier-API lemma showing that after adjoining the chosen compatible root,
  -- the integral closure over `A` is still a DVR and weakly unramified by a `Lemma 15.116.8`
  -- argument with the correct residue-field non-`p`th-power hypothesis coming from the chosen
  -- `p`-basis.
  sorry

section SolutionUpgrade

variable {K1 : Type*}
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance : CommRing L1 :=
  Ideal.Quotient.commRing _

/-- Helper for Proposition 15.117.8: each branch residue-field extension in the finite
reduced-tensor normalization is algebraic. -/
private theorem branch_residueField_isAlgebraic_of_essentiallyFiniteType
    (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal] [q.LiesOver p] :
    Algebra.IsAlgebraic (ResidueField (Localization.AtPrime p))
      (ResidueField (Localization.AtPrime q)) := by
  let _ : Module.Finite A A1 := IsIntegralClosure.finite A K K1 A1
  let hA1Noetherian : IsNoetherianRing A1 := inferInstance
  let qSpec : PrimeSpectrum B1 := ⟨q, inferInstance⟩
  let _ :
      Algebra.FiniteType (ResidueField (Localization.AtPrime p))
        (ResidueField (Localization.AtPrime q)) := by
    -- Clause `(3)` of Lemma `15.117.7` packages the branch residue-field map as finite type.
    simpa using
      (residueField_finiteType_of_reducedTensorProduct_baseChange
        (A := A) (B := B) (K := K) (L := L) (K' := K1) hA1Noetherian qSpec)
  -- Over fields, finite type already forces algebraicity.
  infer_instance

/-- Helper for Proposition 15.117.8: residue characteristic zero makes every source branch
residue field perfect. -/
private theorem branch_source_residueField_isPerfect_of_residueCharZero
    (hchar0 : ringChar (ResidueField A) = 0)
    (p : Ideal A1) [p.IsMaximal] :
    PerfectField (ResidueField (Localization.AtPrime p)) := by
  -- Characteristic is preserved along the localized branch residue-field extension.
  have hpChar0 : ringChar (ResidueField (Localization.AtPrime p)) = 0 := by
    calc
      ringChar (ResidueField (Localization.AtPrime p))
          = ringChar (ResidueField A) := by
              symm
              exact ringChar.eq
                (R := ResidueField A)
                (S := ResidueField (Localization.AtPrime p))
      _ = 0 := hchar0
  letI : CharZero (ResidueField (Localization.AtPrime p)) :=
    (CharP.ringChar_zero_iff_CharZero _).mp hpChar0
  exact PerfectField.ofCharZero

/-- Helper for Proposition 15.117.8: if `ResidueField A` is perfect, then every source branch
residue field is perfect as well. -/
private theorem branch_source_residueField_isPerfect_of_perfectResidueField
    [PerfectField (ResidueField A)]
    (p : Ideal A1) [p.IsMaximal] :
    PerfectField (ResidueField (Localization.AtPrime p)) := by
  -- The source branch residue field is algebraic over `ResidueField A`, and algebraic
  -- extensions of perfect fields remain perfect.
  let _ :
      Algebra.IsAlgebraic (ResidueField A) (ResidueField (Localization.AtPrime p)) :=
    inferInstance
  infer_instance

/-- Helper for Proposition 15.117.8: once every source branch residue field is perfect, a weak
solution upgrades branchwise to a genuine solution. -/
private theorem weakSolution_isSolution_of_perfect_branch_residueFields
    (hPerfect :
      ∀ (p : Ideal A1), p.IsMaximal →
        PerfectField (ResidueField (Localization.AtPrime p)))
    (hWeak : IsWeakSolutionFor A B K L K1) :
    IsSolutionFor A B K L K1 := by
  intro p
  intro q
  -- Install the perfectness hypothesis on the current source branch before invoking Lemma
  -- `15.112.5`.
  letI : PerfectField (ResidueField (Localization.AtPrime p)) :=
    hPerfect p inferInstance
  -- Lemma `15.112.5` reduces formal smoothness to weak ramification plus residue separability.
  rw [formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField]
  have hWeakBranch :
      IsExtensionOfDiscreteValuationRings.WeaklyUnramified
        (Localization.AtPrime p) (Localization.AtPrime q) :=
    hWeak p q
  refine ⟨hWeakBranch, ?_⟩
  have hAlg :
      Algebra.IsAlgebraic (ResidueField (Localization.AtPrime p))
        (ResidueField (Localization.AtPrime q)) :=
    branch_residueField_isAlgebraic_of_essentiallyFiniteType
      (A := A) (B := B) (K := K) (L := L) (K1 := K1) p q
  -- Over a perfect source branch, algebraic residue-field extensions are separable.
  exact
    residueField_isSeparable_of_perfectField_of_isAlgebraic
      (k := ResidueField (Localization.AtPrime p))
      (E := ResidueField (Localization.AtPrime q))

/-- Helper for Proposition 15.117.8: a perfect source residue field upgrades any weak solution to
a genuine solution for an essentially finite type DVR extension. -/
private theorem weakSolution_isSolution_of_perfect_source_residueField
    [PerfectField (ResidueField A)]
    (hWeak : IsWeakSolutionFor A B K L K1) :
    IsSolutionFor A B K L K1 := by
  -- First prove perfectness on each source branch residue field, then invoke the branchwise
  -- weak-to-solution upgrade.
  exact
    weakSolution_isSolution_of_perfect_branch_residueFields
      (A := A) (B := B) (K := K) (L := L) (K1 := K1)
      (fun p hp ↦ by
        letI : p.IsMaximal := hp
        exact
          branch_source_residueField_isPerfect_of_perfectResidueField
            (A := A) p)
      hWeak

end SolutionUpgrade

/-
Domain-style sampling for Proposition 15.117.8:
- primary domain: existence of finite solution fields for essentially finite type extensions of
  discrete valuation rings, organized around the Chapter 15 solution owner;
- sampled owner declarations:
  `IsSolutionFor`,
  `exists_ramificationEliminationSquare`,
  `exists_finite_extension_weakSolution_of_epp_hypothesis`,
  `formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField`;
- best owner abstraction: the proposition is `source-facing`, but its mathematical content is
  still owned by the predicate `IsSolutionFor A B K L K1`; the ramification-elimination square,
  the Epp weak-solution existence theorem, and the branchwise upgrade from weakly unramified to
  formally smooth are proof-level bridge inputs rather than parallel public wrappers;
- primitive-vs-derived split: the primitive data are the essentially finite type DVR extension
  `A ⊂ B` and the chosen fraction fields `K ⊂ L`; the finite extension `K₁ / K` witnessing the
  solution property is derived API recorded directly through `IsSolutionFor`.

Source/core/bridge triage:
- `source-facing`: `exists_finite_extension_solution_of_essentiallyFiniteType`;
- `core/canonical`: `IsSolutionFor`;
- `bridge/view`: `exists_ramificationEliminationSquare`,
  `exists_finite_extension_weakSolution_of_epp_hypothesis`, and
  `formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField`.
-/

-- Proof sketch: follow the textbook argument by first applying Epp's theorem to obtain a finite
-- weak solution after passing to a DVR with perfect residue field, use Lemma `15.112.5` to
-- identify weak solutions with solutions over the perfect-residue-field base, and then descend
-- the resulting formally smooth local branches to a finite stage using Lemma `15.117.7` and the
-- finite-type hypothesis on `B`.
/-- Proposition 15.117.8: if `A ⊂ B` is an essentially finite type extension of discrete valuation
rings with fraction fields `K ⊂ L`, then there exists a finite extension `K₁ / K` which is a
solution for `A ⊂ B` in the sense of Definition `15.116.1`. -/
theorem exists_finite_extension_solution_of_essentiallyFiniteType :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSolutionFor A B K L K1 := by
  -- Route correction: follow the source proof by splitting on the residue characteristic of `A`.
  -- The characteristic-zero branch already reaches Epp's weak solution, while the positive-
  -- characteristic branch must still pass through the source-faithful perfect-residue-field
  -- base change before descending to a finite stage.
  by_cases hchar0 : ringChar (ResidueField A) = 0
  · rcases exists_finite_extension_weakSolution_of_epp_hypothesis
        (A := A) (B := B) (K := K) (L := L)
        (epp_hypothesis_of_residueCharZero (A := A) (B := B) hchar0) with
      ⟨K1, hK1Field, hAK1, hKK1, hTower, hFinite, hWeak⟩
    letI : Field K1 := hK1Field
    letI : Algebra A K1 := hAK1
    letI : Algebra K K1 := hKK1
    letI : IsScalarTower A K K1 := hTower
    letI : FiniteDimensional K K1 := hFinite
    letI : CharZero (ResidueField A) :=
      (CharP.ringChar_zero_iff_CharZero _).mp hchar0
    letI : PerfectField (ResidueField A) := PerfectField.ofCharZero
    -- The characteristic-zero branch now factors through the generic perfect-residue-field
    -- upgrade, which will also be the closing step after the positive-characteristic perfection
    -- construction is in place.
    exact ⟨K1, hK1Field, hAK1, hKK1, hTower, hFinite,
      weakSolution_isSolution_of_perfect_source_residueField
        (A := A) (B := B) (K := K) (L := L) hWeak⟩
  · have hcharpos : ringChar (ResidueField A) ≠ 0 := hchar0
    -- Proof comment: start the positive-characteristic source route by fixing the `p`-basis and
    -- chosen lifts in `A`; these are the controlled generators for the finite `p`-root stages.
    obtain ⟨ι, x, xLift, hxPBasis, hxLift⟩ :=
      exists_residueField_pBasis_with_lifts_of_positive_residueChar
        (A := A) (B := B) hcharpos
    -- Proof comment: the remaining source-faithful frontier is the perfected-base construction
    -- from these chosen lifts; isolate it in one helper theorem so the main theorem follows the
    -- textbook characteristic split cleanly.
    exact
      exists_solution_of_positive_residueChar_via_perfected_base
        (A := A) (B := B) (K := K) (L := L)
        hcharpos x xLift hxPBasis hxLift

end
