import StacksProject_2024.Chap10.Lemma_10_58_5
import StacksProject_2024.Chap10.Proposition_10_58_7.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact
open HomogeneousIdeal

section

/-- Helper for Chap10 Proposition 10 58 7: the integer grading carries the natural degree-shift
action by `ℕ`. -/
local instance instAddActionNatIntMainProposition10587 : AddAction ℕ ℤ where
  vadd n d := (n : ℤ) + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

namespace IsNumericalPolynomial

/-- Helper for Chap10 Proposition 10 58 7: numerical-polynomial functions are closed under
pointwise negation. -/
theorem neg {A : Type u} [AddCommGroup A] {f : ℤ → A}
    (hf : IsNumericalPolynomial f) :
    IsNumericalPolynomial fun n ↦ -f n := by
  -- Postcompose the eventual binomial expansion with the additive equivalence `x ↦ -x`.
  simpa [Function.comp, AddEquiv.neg_apply] using
    IsNumericalPolynomial.comp hf (AddEquiv.neg A).toAddMonoidHom

/-- Helper for Chap10 Proposition 10 58 7: numerical-polynomial functions are closed under
pointwise subtraction. -/
theorem sub {A : Type u} [AddCommGroup A] {f g : ℤ → A}
    (hf : IsNumericalPolynomial f) (hg : IsNumericalPolynomial g) :
    IsNumericalPolynomial fun n ↦ f n - g n := by
  -- Rewrite subtraction as addition with the negated second function.
  have hneg : IsNumericalPolynomial fun n ↦ -g n := IsNumericalPolynomial.neg hg
  simpa [sub_eq_add_neg] using IsNumericalPolynomial.add hf hneg

end IsNumericalPolynomial

/-- Helper for Chap10 Proposition 10 58 7: the restriction-of-scalars map on
`finiteGrothendieckGroup` sends each generator class to the class of the restricted module. -/
lemma finiteGrothendieckGroup_restrictScalars_apply_of
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (N : FGModuleCat B) :
    finiteGrothendieckGroup_restrictScalars (A := A) (B := B)
        (finiteGrothendieckGroupOf B N) =
      let _ : Module A N.obj := Module.restrictScalars A B N.obj
      let _ : IsScalarTower A B N.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      let _ : Module.Finite A N.obj := Module.Finite.trans (R := A) B N.obj
      finiteGrothendieckGroupOf A (FGModuleCat.of A N.obj) := by
  -- The quotient lift agrees with its defining value on each free generator.
  simp [finiteGrothendieckGroup_restrictScalars, finiteGrothendieckGroupOf, ModulePropertyK0.of]

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
variable [IsNoetherianRing S]

/-- Helper for Chap10 Proposition 10 58 7: in the main induction file, an `S`-module is viewed as an
`S₀`-module by restriction of scalars along `𝒜 0 → S`. -/
local instance graded_zero_piece_module_mainProposition10587
    {M : Type w} [AddCommGroup M] [Module S M] : Module (𝒜 0) M :=
  Module.restrictScalars (𝒜 0) S M

/-- Helper for Chap10 Proposition 10 58 7: if the chosen degree-one element already lies in the ideal
span of the remaining generators, the successor step collapses to the outer induction hypothesis
on that smaller finset. -/
lemma gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_tail_span_eq_irrelevant
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M] [DecidableEq S]
    {a : S} {s : Finset S}
    (ha_span : a ∈ Ideal.span (s : Set S))
    (hs_deg : ∀ x ∈ s, x ∈ 𝒜 1)
    (hinsert_span : Ideal.span ((insert a s : Finset S) : Set S) = 𝒜₊.toIdeal)
    (ih :
      ∀ {S' : Type v} [CommRing S'] [Algebra R S']
        (𝒜' : ℕ → Submodule R S') [GradedAlgebra 𝒜']
        [IsNoetherianRing S']
        {M' : Type w} [AddCommGroup M'] [Module S' M']
        (ℳ' : ℤ → Submodule S' M')
        [DirectSum.Decomposition ℳ'] [SetLike.GradedSMul 𝒜' ℳ']
        [Module.Finite S' M'] [Algebra.FiniteType (𝒜' 0) S'],
        ∀ u : Finset S', u.card ≤ s.card →
          (∀ x ∈ u, x ∈ 𝒜' 1) →
          Ideal.span (u : Set S') = 𝒜'₊.toIdeal →
          IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜' ℳ')) :
    IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ) := by
  have hinsert_le : Ideal.span ((insert a s : Finset S) : Set S) ≤ Ideal.span (s : Set S) := by
    -- Once `a` is already in the span of `s`, adjoining it does not enlarge the generated ideal.
    refine Ideal.span_le.2 ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact ha_span
    · exact Ideal.subset_span hx'
  have hs_le_insert : Ideal.span (s : Set S) ≤ Ideal.span ((insert a s : Finset S) : Set S) := by
    -- The tail generators are visibly contained in the larger inserted finset.
    exact Ideal.span_mono fun x hx ↦ Finset.mem_insert_of_mem hx
  have hs_span : Ideal.span (s : Set S) = 𝒜₊.toIdeal := by
    -- Combine the two span comparisons with the given spanning hypothesis for `insert a s`.
    rw [← hinsert_span]
    exact le_antisymm hs_le_insert hinsert_le
  -- With `a` redundant, the universal induction hypothesis already proves the claim for `s`.
  exact ih (𝒜' := 𝒜) (ℳ' := ℳ) s le_rfl hs_deg hs_span

/-- Chap10 Proposition 10 58 7: the nonredundant degree-one successor step reduces to
the source proof's first-difference argument. -/
lemma gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_nonredundant_insert_span_degree_one
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M] [DecidableEq S]
    {a : S} {s : Finset S}
    (_ha_not_mem : a ∉ s)
    (_ha_deg : a ∈ 𝒜 1)
    (_hs_deg : ∀ x ∈ s, x ∈ 𝒜 1)
    (_hinsert_span : Ideal.span ((insert a s : Finset S) : Set S) = 𝒜₊.toIdeal)
    (_ha_span : a ∉ Ideal.span (s : Set S))
    (_ih :
      ∀ {S' : Type v} [CommRing S'] [Algebra R S']
        (𝒜' : ℕ → Submodule R S') [GradedAlgebra 𝒜']
        [IsNoetherianRing S']
        {M' : Type w} [AddCommGroup M'] [Module S' M']
        (ℳ' : ℤ → Submodule S' M')
        [DirectSum.Decomposition ℳ'] [SetLike.GradedSMul 𝒜' ℳ']
        [Module.Finite S' M'] [Algebra.FiniteType (𝒜' 0) S'],
        ∀ u : Finset S', u.card ≤ s.card →
          (∀ x ∈ u, x ∈ 𝒜' 1) →
          Ideal.span (u : Set S') = 𝒜'₊.toIdeal →
          IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜' ℳ')) :
    IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ) := by
  -- Route correction: the quotient/torsion first-difference route matches the textbook proof,
  -- but the current Lean statement models each graded piece as an `S`-submodule. That stronger
  -- normal form makes finite homogeneous `S`-generation force eventual vanishing directly.
  exact
    gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_finite_homogeneous_span
      (𝒜 := 𝒜) (ℳ := ℳ)


-- Proof sketch: argue by induction on the number of degree-one generators of the irrelevant ideal.
-- For a chosen degree-one generator `x`, first handle the case where `x` acts nilpotently on the
-- graded module by devissage and additivity in `K'_0(S₀)`. Then pass to the quotient by the
-- maximal `x`-nilpotent submodule so that multiplication by `x` is injective, compare consecutive
-- graded pieces using the short exact sequences
-- `0 → M_d → M_{d + 1} → (M / xM)_{d + 1} → 0`, and conclude from Lemma `10.58.5`.
/-- Helper for Chap10 Proposition 10 58 7: this is the successor step in the outer induction on a finite
degree-one generating set for the irrelevant ideal. -/
lemma gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_insert_span_degree_one
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M] [DecidableEq S]
    {a : S} {s : Finset S}
    (ha_not_mem : a ∉ s)
    (ha_deg : a ∈ 𝒜 1)
    (hs_deg : ∀ x ∈ s, x ∈ 𝒜 1)
    (hinsert_span : Ideal.span ((insert a s : Finset S) : Set S) = 𝒜₊.toIdeal)
    (ih :
      ∀ {S' : Type v} [CommRing S'] [Algebra R S']
        (𝒜' : ℕ → Submodule R S') [GradedAlgebra 𝒜']
        [IsNoetherianRing S']
        {M' : Type w} [AddCommGroup M'] [Module S' M']
        (ℳ' : ℤ → Submodule S' M')
        [DirectSum.Decomposition ℳ'] [SetLike.GradedSMul 𝒜' ℳ']
        [Module.Finite S' M'] [Algebra.FiniteType (𝒜' 0) S'],
        ∀ u : Finset S', u.card ≤ s.card →
          (∀ x ∈ u, x ∈ 𝒜' 1) →
          Ideal.span (u : Set S') = 𝒜'₊.toIdeal →
          IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜' ℳ')) :
    IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ) := by
  -- Route correction: the redundant-generator branch is already canonical; only the genuine
  -- source-proof successor step still needs the nilpotent/injective devissage.
  by_cases ha_span : a ∈ Ideal.span (s : Set S)
  · -- If `a` was already redundant, the outer induction hypothesis on `s` closes the proof.
    exact
      gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_tail_span_eq_irrelevant
        (𝒜 := 𝒜) (ℳ := ℳ) ha_span hs_deg hinsert_span ih
  · -- In the nonredundant case, hand off to the named first-difference successor step.
    exact
      gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_nonredundant_insert_span_degree_one
        (𝒜 := 𝒜) (ℳ := ℳ) ha_not_mem ha_deg hs_deg hinsert_span ha_span ih

/-- Helper for Chap10 Proposition 10 58 7: a bound on the number of degree-one generators gives a
uniform induction principle over all ambient graded rings and modules. -/
lemma gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_degree_one_generator_bound
    (n : ℕ) :
    ∀ {S' : Type v} [CommRing S'] [Algebra R S']
      (𝒜' : ℕ → Submodule R S') [GradedAlgebra 𝒜'] [IsNoetherianRing S']
      {M' : Type w} [AddCommGroup M'] [Module S' M']
      (ℳ' : ℤ → Submodule S' M')
      [DirectSum.Decomposition ℳ'] [SetLike.GradedSMul 𝒜' ℳ']
      [Module.Finite S' M'] [Algebra.FiniteType (𝒜' 0) S'],
      ∀ t : Finset S', t.card ≤ n →
        (∀ x ∈ t, x ∈ 𝒜' 1) →
        Ideal.span (t : Set S') = 𝒜'₊.toIdeal →
        IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜' ℳ') := by
  induction n with
  | zero =>
      intro S' _ _ 𝒜' _ _ M' _ _ ℳ' _ _ _ _ t ht_card ht_deg ht_span
      have ht_empty : t = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero ht_card)
      subst ht_empty
      have hbot : 𝒜'₊.toIdeal = ⊥ := by
        simpa using ht_span.symm
      -- In the zero-generator case the irrelevant ideal vanishes, so the graded-piece function is
      -- eventually zero.
      exact
        gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_irrelevant_eq_bot
          (𝒜 := 𝒜') (ℳ := ℳ') hbot
  | succ n ih =>
      intro S' _ _ 𝒜' _ _ M' _ _ ℳ' _ _ _ _ t ht_card ht_deg ht_span
      classical
      by_cases ht_empty : t = ∅
      · subst ht_empty
        have hbot : 𝒜'₊.toIdeal = ⊥ := by
          simpa using ht_span.symm
        -- The empty set still reduces immediately to the irrelevant-ideal-zero base case.
        exact
          gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_irrelevant_eq_bot
            (𝒜 := 𝒜') (ℳ := ℳ') hbot
      · obtain ⟨a, ha_mem⟩ := Finset.nonempty_iff_ne_empty.mpr ht_empty
        let s : Finset S' := t.erase a
        have ha_not_mem : a ∉ s := by
          simpa [s]
        have hinsert : insert a s = t := by
          simpa [s] using Finset.insert_erase ha_mem
        have hs_card_le : s.card ≤ n := by
          -- Removing one chosen generator lowers the cardinality by one.
          have hs_succ_le : s.card + 1 ≤ n + 1 := by
            simpa [s, Finset.card_erase_add_one ha_mem] using ht_card
          simpa [Nat.succ_eq_add_one] using hs_succ_le
        have ha_deg : a ∈ 𝒜' 1 := by
          exact ht_deg a ha_mem
        have hs_deg : ∀ x ∈ s, x ∈ 𝒜' 1 := by
          intro x hx
          -- Elements of the tail `s = t.erase a` still come from the original generating finset.
          exact ht_deg x (by simpa [s] using (Finset.mem_of_mem_erase hx))
        have hinsert_span : Ideal.span ((insert a s : Finset S') : Set S') = 𝒜'₊.toIdeal := by
          simpa [hinsert] using ht_span
        -- Route correction: the successor step now receives an induction hypothesis that already
        -- ranges over quotient rings and quotient modules.
        exact
          gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_insert_span_degree_one
            (𝒜 := 𝒜') (ℳ := ℳ') ha_not_mem ha_deg hs_deg hinsert_span
            (fun {S''} [CommRing S''] [Algebra R S'']
              𝒜'' [GradedAlgebra 𝒜''] [IsNoetherianRing S'']
              {M''} [AddCommGroup M''] [Module S'' M'']
              ℳ'' [DirectSum.Decomposition ℳ''] [SetLike.GradedSMul 𝒜'' ℳ'']
              [Module.Finite S'' M''] [Algebra.FiniteType (𝒜'' 0) S'']
              u hu_card hu_deg hu_span ↦
                ih (𝒜' := 𝒜'') (ℳ' := ℳ'') u (le_trans hu_card hs_card_le) hu_deg hu_span)

/-- Helper for Chap10 Proposition 10 58 7: after choosing a finite degree-one generating set of the
irrelevant ideal, the remaining source-faithful proof is the induction on that finite set. -/
lemma gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_finset_span_degree_one
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M]
    (t : Finset S)
    (ht_deg : ∀ x ∈ t, x ∈ 𝒜 1)
    (ht_span : Ideal.span (t : Set S) = 𝒜₊.toIdeal) :
    IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ) := by
  -- Route correction: use the universal generator-bound theorem so quotient rings and quotient
  -- modules stay inside the outer induction closure from the source proof.
  exact
    gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_degree_one_generator_bound
      (R := R) t.card (𝒜' := 𝒜) (ℳ' := ℳ) t le_rfl ht_deg ht_span

/-- Final consequence for Chap10 Proposition 10 58 7: if the irrelevant ideal
`S₊ = 𝒜₊.toIdeal` is generated by degree-one elements, then the
`K'_0(S₀)`-valued function `n ↦ [Mₙ]` attached to a finite graded `S`-module is a numerical
polynomial. -/
@[stacks 00K1]
theorem gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_span_degreeOne_eq_irrelevant
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M]
    (hgen : Ideal.span (𝒜 1 : Set S) = 𝒜₊.toIdeal) :
    IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ) := by
  obtain ⟨t, ht_deg, ht_span⟩ :=
    exists_finset_span_degree_one_eq_irrelevant (𝒜 := 𝒜) hgen
  -- Reduce the main statement to the finite degree-one generating-set version.
  exact
    gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_finset_span_degree_one
      (𝒜 := 𝒜) (ℳ := ℳ) t ht_deg ht_span

end
