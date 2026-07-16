import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_55_6
import stacks_proof.stacks_project.Chap10.Definition_10_58_3
import stacks_proof.stacks_project.Chap10.Lemma_10_56_1
import stacks_proof.stacks_project.Chap10.Lemma_10_58_4
import stacks_proof.stacks_project.Chap10.Lemma_10_58_2
import stacks_proof.stacks_project.Chap10.Lemma_10_58_6


-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact
open HomogeneousIdeal

section GrothendieckGroups

variable (R : Type u) [Ring R]

/-- Helper for Proposition 10.58.7: the zero module is finitely generated. -/
private theorem isFG_zero :
    ModuleCat.isFG R (ModuleCat.of R PUnit) := by
  rw [ModuleCat.isFG_iff]
  infer_instance

/-- Helper for Proposition 10.58.7: the generator-level restriction-of-scalars class map sends
short-exact-sequence relations for finite `B`-modules to zero in `K'_0(A)`. -/
private theorem finiteGrothendieckGroup_relations_le_ker_restrictScalars
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] :
    modulePropertyK0Relations B (ModuleCat.isFG B) ≤
      (FreeAbelianGroup.lift fun M : FGModuleCat B ↦
        let _ : Module A M.obj := Module.restrictScalars A B M.obj
        let _ : IsScalarTower A B M.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        let _ : Module.Finite A M.obj := Module.Finite.trans (R := A) B M.obj
        finiteGrothendieckGroupOf A (FGModuleCat.of A M.obj)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift
        (fun M : FGModuleCat B ↦
          let _ : Module A M.obj := Module.restrictScalars A B M.obj
          let _ : IsScalarTower A B M.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
          let _ : Module.Finite A M.obj := Module.Finite.trans (R := A) B M.obj
          finiteGrothendieckGroupOf A (FGModuleCat.of A M.obj))
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  let _ : Module A S.X₁.obj := Module.restrictScalars A B S.X₁.obj
  let _ : Module A S.X₂.obj := Module.restrictScalars A B S.X₂.obj
  let _ : Module A S.X₃.obj := Module.restrictScalars A B S.X₃.obj
  let _ : IsScalarTower A B S.X₁.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower A B S.X₂.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower A B S.X₃.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module.Finite A S.X₁.obj := Module.Finite.trans (R := A) B S.X₁.obj
  let _ : Module.Finite A S.X₂.obj := Module.Finite.trans (R := A) B S.X₂.obj
  let _ : Module.Finite A S.X₃.obj := Module.Finite.trans (R := A) B S.X₃.obj
  let U : ShortComplex (ModuleCat B) := S.map (ModuleCat.isFG B).ι
  have hU : U.ShortExact := by
    -- Forgetting the finiteness predicate yields the original short exact sequence in `ModuleCat`.
    simpa [U] using hS
  have hExact :
      Function.Exact (S.f.hom.hom.restrictScalars A) (S.g.hom.hom.restrictScalars A) := by
    -- Restriction of scalars does not change the underlying functions in the exact pair.
    simpa [U] using
      (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mp hU.exact
  have hf_injective : Function.Injective (S.f.hom.hom.restrictScalars A) := by
    -- Injectivity of the first map is preserved under restriction of scalars.
    simpa [U] using hU.moduleCat_injective_f
  have hg_surjective : Function.Surjective (S.g.hom.hom.restrictScalars A) := by
    -- Surjectivity of the second map is preserved under restriction of scalars.
    simpa [U] using hU.moduleCat_surjective_g
  let T : ShortComplex (FGModuleCat A) :=
    { X₁ := FGModuleCat.of A S.X₁.obj
      X₂ := FGModuleCat.of A S.X₂.obj
      X₃ := FGModuleCat.of A S.X₃.obj
      f := FGModuleCat.ofHom (S.f.hom.hom.restrictScalars A)
      g := FGModuleCat.ofHom (S.g.hom.hom.restrictScalars A)
      zero := by
        ext x
        change S.g.hom (S.f.hom x) = 0
        simpa using congrFun hExact.comp_eq_zero x }
  have hT : (T.map (ModuleCat.isFG A).ι).ShortExact := by
    -- Repackage the restricted sequence as a short exact sequence of finite `A`-modules.
    refine ModuleCat.shortComplex_shortExact _ hExact hf_injective hg_surjective
  have hrel :
      finiteGrothendieckGroupOf A (FGModuleCat.of A S.X₂.obj) =
        finiteGrothendieckGroupOf A (FGModuleCat.of A S.X₁.obj) +
          finiteGrothendieckGroupOf A (FGModuleCat.of A S.X₃.obj) := by
    -- The defining Grothendieck relation now applies over the smaller ring `A`.
    simpa [finiteGrothendieckGroupOf, T] using
      ModulePropertyK0.of_shortExact (R := A) (P := ModuleCat.isFG A) T hT
  -- Rewrite the relation into the subgroup-generator form `[`X₂`] - [`X₁`] - [`X₃`] = 0`.
  calc
    finiteGrothendieckGroupOf A (FGModuleCat.of A S.X₂.obj) -
        finiteGrothendieckGroupOf A (FGModuleCat.of A S.X₁.obj) -
        finiteGrothendieckGroupOf A (FGModuleCat.of A S.X₃.obj) =
      (finiteGrothendieckGroupOf A (FGModuleCat.of A S.X₁.obj) +
          finiteGrothendieckGroupOf A (FGModuleCat.of A S.X₃.obj)) -
        finiteGrothendieckGroupOf A (FGModuleCat.of A S.X₁.obj) -
        finiteGrothendieckGroupOf A (FGModuleCat.of A S.X₃.obj) := by
          rw [hrel]
    _ = 0 := by
          abel

/-- Helper for Proposition 10.58.7: restricting scalars along a finite algebra map induces the
canonical homomorphism on finitely generated Grothendieck groups. -/
noncomputable def finiteGrothendieckGroup_restrictScalars
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] :
    finiteGrothendieckGroup B →+ finiteGrothendieckGroup A :=
  QuotientAddGroup.lift (modulePropertyK0Relations B (ModuleCat.isFG B))
    (FreeAbelianGroup.lift fun M : FGModuleCat B ↦
      let _ : Module A M.obj := Module.restrictScalars A B M.obj
      let _ : IsScalarTower A B M.obj := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      let _ : Module.Finite A M.obj := Module.Finite.trans (R := A) B M.obj
      finiteGrothendieckGroupOf A (FGModuleCat.of A M.obj))
    (finiteGrothendieckGroup_relations_le_ker_restrictScalars (A := A) (B := B))

end GrothendieckGroups

section

/-- Helper for Chap10 Proposition 10 58 7: the integer grading carries the natural degree-shift
action by `ℕ`. -/
local instance instAddActionNatIntGrothendieckClasses10587 : AddAction ℕ ℤ where
  vadd n d := (n : ℤ) + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]

/-- Helper for Proposition 10.58.7: every `S`-module in this section is viewed as an `S₀`-module
by restriction of scalars along `𝒜 0 → S`. -/
local instance graded_zero_piece_module_proposition10587
    {M : Type w} [AddCommGroup M] [Module S M] : Module (𝒜 0) M :=
  Module.restrictScalars (𝒜 0) S M

/-- The `K'_0(S₀)`-valued function `n ↦ [Mₙ]` attached to a finite graded `S`-module
`M = ⨁_{n ∈ ℤ} Mₙ`, where `S₀ = 𝒜 0`, provided `S` is finite type over `S₀` so that each degree
piece is a finite `S₀`-module by Lemma `10.58.6`. Here `K'_0(S₀)` is modeled by
`finiteGrothendieckGroup (𝒜 0)`. -/
noncomputable def gradedPieceFiniteGrothendieckGroupClass
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S] :
    ℤ → finiteGrothendieckGroup (𝒜 0) :=
  fun n ↦
    let _ : Module (𝒜 0) M := Module.restrictScalars (𝒜 0) S M
    let _ : Module (𝒜 0) (ℳ n) := Module.restrictScalars (𝒜 0) S (ℳ n)
    let _ : Module.Finite (𝒜 0) (ℳ n) := finite_degree_component_of_finiteType 𝒜 ℳ n
    finiteGrothendieckGroupOf (𝒜 0) (FGModuleCat.of (𝒜 0) (ℳ n))

variable [IsNoetherianRing S]

/-- Helper for Proposition 10.58.7: from the hypothesis that the irrelevant ideal is generated by
degree-one elements, extract a finite degree-one generating set for that ideal. -/
lemma exists_finset_span_degree_one_eq_irrelevant
    (hgen : Ideal.span (𝒜 1 : Set S) = 𝒜₊.toIdeal) :
    ∃ t : Finset S, (∀ x ∈ t, x ∈ 𝒜 1) ∧ Ideal.span (t : Set S) = 𝒜₊.toIdeal := by
  classical
  obtain ⟨s, hs⟩ := 𝒜₊.toIdeal.fg_of_isNoetherianRing
  have hs_mem : (s : Set S) ⊆ Ideal.span (𝒜 1 : Set S) := by
    -- Rewrite the chosen finite generators through the given degree-one spanning hypothesis.
    intro x hx
    rw [hgen, ← hs]
    exact Ideal.subset_span hx
  obtain ⟨t, ht_sub, hs_le⟩ := Submodule.subset_span_finite_of_subset_span hs_mem
  refine ⟨t, fun x hx ↦ ht_sub hx, ?_⟩
  refine le_antisymm ?_ ?_
  · -- Every chosen element of `t` already lies in degree `1`, so its span stays inside `𝒜₊`.
    rw [← hgen]
    exact Ideal.span_mono fun x hx ↦ ht_sub hx
  · -- The original finite generators of `𝒜₊` lie in the span of `t`, hence so does `𝒜₊`.
    rw [← hs]
    exact Ideal.span_le.2 hs_le

/-- Helper for Proposition 10.58.7: if every sufficiently large value of a function is zero, then
the function is a numerical polynomial. -/
lemma isNumericalPolynomial_of_eventuallyEq_zero
    {A : Type*} [AddCommGroup A] {f : ℤ → A}
    (hzero : f =ᶠ[Filter.atTop] fun _ ↦ 0) :
    IsNumericalPolynomial f := by
  -- Use the constant zero binomial expansion of degree `0`.
  refine ⟨0, fun _ ↦ 0, ?_⟩
  filter_upwards [hzero] with n hn
  simpa using hn

/-- Helper for Proposition 10.58.7: transporting a numerical polynomial across an additive
equivalence preserves numerical polynomiality. -/
lemma isNumericalPolynomial_map_addEquiv
    {A : Type*} [AddCommGroup A] {B : Type*} [AddCommGroup B]
    (e : A ≃+ B) {f : ℤ → A} (hf : IsNumericalPolynomial f) :
    IsNumericalPolynomial fun n ↦ e (f n) := by
  -- Postcompose the binomial expansion with the additive homomorphism underlying the equivalence.
  simpa [Function.comp] using IsNumericalPolynomial.comp hf e.toAddMonoidHom

/-- Helper for Proposition 10.58.7: a binomial expansion can be padded on the right by zero
coefficients without changing the represented function. -/
private theorem exists_eventuallyEq_binomialExpansion_raise
    {A : Type*} [AddCommGroup A] {f : ℤ → A} {r : ℕ}
    (a : Fin (r + 1) → A) :
    ∀ k : ℕ,
      (f =ᶠ[Filter.atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i) →
        ∃ b : Fin (r + k + 1) → A,
          f =ᶠ[Filter.atTop] fun n ↦ ∑ i : Fin (r + k + 1), Ring.choose n (i : ℕ) • b i
  | 0, h => by
      -- At gap `0` we keep the original coefficients unchanged.
      refine ⟨a, ?_⟩
      simpa using h
  | k + 1, h => by
      -- First raise to degree `r + k`, then append one more zero coefficient.
      obtain ⟨b, hb⟩ := exists_eventuallyEq_binomialExpansion_raise a k h
      refine ⟨Fin.snoc b 0, ?_⟩
      filter_upwards [hb] with n hn
      rw [Fin.sum_univ_castSucc]
      simpa [Fin.snoc_castSucc, Fin.snoc_last, Nat.add_assoc] using hn

/-- Helper for Proposition 10.58.7: an eventual binomial expansion of degree `r` can be padded to
any larger target degree `t`. -/
private theorem exists_eventuallyEq_binomialExpansion_pad_to
    {A : Type*} [AddCommGroup A] {f : ℤ → A} {r t : ℕ}
    (a : Fin (r + 1) → A) (hrt : r ≤ t)
    (h :
      f =ᶠ[Filter.atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i) :
    ∃ b : Fin (t + 1) → A,
      f =ᶠ[Filter.atTop] fun n ↦ ∑ i : Fin (t + 1), Ring.choose n (i : ℕ) • b i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrt
  -- Rewrite the target degree as `r + k` so the iterative padding lemma applies directly.
  simpa [Nat.add_assoc] using exists_eventuallyEq_binomialExpansion_raise (f := f) a k h

namespace IsNumericalPolynomial

/-- Helper for Proposition 10.58.7: numerical-polynomial functions are closed under pointwise
addition. -/
theorem add
    {A : Type*} [AddCommGroup A] {f g : ℤ → A}
    (hf : IsNumericalPolynomial f) (hg : IsNumericalPolynomial g) :
    IsNumericalPolynomial fun n ↦ f n + g n := by
  rcases hf with ⟨r, a, ha⟩
  rcases hg with ⟨s, b, hb⟩
  let t := max r s
  -- Pad both eventual binomial expansions to the common target degree `max r s`.
  obtain ⟨a', ha'⟩ :=
    exists_eventuallyEq_binomialExpansion_pad_to (f := f) (t := t) a
      (Nat.le_max_left r s) ha
  obtain ⟨b', hb'⟩ :=
    exists_eventuallyEq_binomialExpansion_pad_to (f := g) (t := t) b
      (Nat.le_max_right r s) hb
  refine ⟨t, fun i ↦ a' i + b' i, ?_⟩
  filter_upwards [ha', hb'] with n hn_f hn_g
  -- Once both expansions have the same degree, add them coefficientwise.
  calc
    f n + g n
        = (∑ i : Fin (t + 1), Ring.choose n (i : ℕ) • a' i) +
            ∑ i : Fin (t + 1), Ring.choose n (i : ℕ) • b' i := by
            rw [hn_f, hn_g]
    _ = ∑ i : Fin (t + 1), Ring.choose n (i : ℕ) • (a' i + b' i) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [smul_add]

end IsNumericalPolynomial

/-- Helper for Proposition 10.58.7: if the irrelevant ideal is zero, then every positive-degree
homogeneous scalar vanishes. -/
lemma eq_zero_of_mem_positive_degree_of_irrelevant_eq_bot
    {d : ℕ} (hd : 0 < d) {x : S} (hx : x ∈ 𝒜 d) (hbot : 𝒜₊.toIdeal = ⊥) :
    x = 0 := by
  -- Positive-degree homogeneous elements lie in the irrelevant ideal, which is zero here.
  have hx_irr : x ∈ 𝒜₊.toIdeal := mem_irrelevant_of_mem 𝒜 hd hx
  have hx_bot : x ∈ (⊥ : Ideal S) := by
    rw [← hbot]
    exact hx_irr
  simpa using hx_bot

/-- Helper for Proposition 10.58.7: if a graded piece is the zero submodule, then its
Grothendieck-group class vanishes. -/
lemma gradedPieceFiniteGrothendieckGroupClass_eq_zero_of_eq_bot
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M]
    [Algebra.FiniteType (𝒜 0) S]
    {n : ℤ} (hbot : ℳ n = ⊥) :
    gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ n = 0 := by
  let _ : Module (𝒜 0) M := Module.restrictScalars (𝒜 0) S M
  let _ : Module (𝒜 0) (ℳ n) := Module.restrictScalars (𝒜 0) S (ℳ n)
  letI : Subsingleton (ℳ n) := (Submodule.subsingleton_iff_eq_bot.2 hbot)
  -- Replace the zero graded piece by the bottom submodule and then identify it with the zero
  -- module `PUnit`.
  calc
    gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ n =
        ModulePropertyK0.of (𝒜 0) (ModuleCat.isFG (𝒜 0))
          ⟨ModuleCat.of (𝒜 0) PUnit, isFG_zero (R := 𝒜 0)⟩ := by
      simpa [gradedPieceFiniteGrothendieckGroupClass, finiteGrothendieckGroupOf] using
        (ModulePropertyK0.of_iso (R := 𝒜 0) (P := ModuleCat.isFG (𝒜 0))
          (isFG_zero (R := 𝒜 0))
          ((LinearEquiv.ofSubsingleton (ℳ n) PUnit).toFGModuleCatIso))
    _ = 0 := ModulePropertyK0.of_zero (R := 𝒜 0) (P := ModuleCat.isFG (𝒜 0))
      (isFG_zero (R := 𝒜 0))

/-- Helper for Proposition 10.58.7: if the irrelevant ideal is zero, then all sufficiently large
graded pieces vanish. -/
lemma graded_piece_eq_bot_eventually_of_irrelevant_eq_bot
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M]
    [Algebra.FiniteType (𝒜 0) S]
    (hbot : 𝒜₊.toIdeal = ⊥) :
    ∃ N : ℤ, ∀ n, N ≤ n → ℳ n = ⊥ := by
  classical
  obtain ⟨κ, _, m, η, hm, hspan⟩ :=
    exists_finite_homogeneous_module_generators (ℳ := ℳ)
  let N : ℤ := ((∑ j : κ, Int.natAbs (η j) : ℕ) : ℤ) + 1
  refine ⟨N, ?_⟩
  intro n hn
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx_span : x ∈ Submodule.span S (Set.range m) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hx_span
  have hx_decompose :
      (∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n)) = ⟨x, hx⟩ := by
    -- Project the finite generator expansion termwise to the fixed degree `n`.
    calc
      (∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n)) =
          DirectSum.decompose ℳ (∑ j, c j • m j) n := by
            simp [DirectSum.decompose_sum]
      _ = DirectSum.decompose ℳ x n := by simpa [hc]
      _ = ⟨x, hx⟩ := by
            ext
            simpa [DirectSum.decompose_of_mem_same ℳ hx]
  have hterm_zero : ∀ j : κ, (DirectSum.decompose ℳ (c j • m j) n : ℳ n) = 0 := by
    intro j
    have hsum_nat : Int.natAbs (η j) ≤ ∑ k : κ, Int.natAbs (η k) := by
      exact
        (Finset.single_le_sum
          (fun k _ ↦ Nat.zero_le (Int.natAbs (η k))) (Finset.mem_univ j) :
          Int.natAbs (η j) ≤ ∑ k : κ, Int.natAbs (η k))
    have hη_le : η j ≤ ((∑ k : κ, Int.natAbs (η k) : ℕ) : ℤ) := by
      have hnatabs_le : (Int.natAbs (η j) : ℤ) ≤ ((∑ k : κ, Int.natAbs (η k) : ℕ) : ℤ) := by
        exact_mod_cast hsum_nat
      exact le_trans (Int.le_natAbs (a := η j)) hnatabs_le
    have hη_lt : η j < n := by
      dsimp [N] at hn
      linarith
    let d : ℕ := Int.toNat (n - η j)
    have hd_nonneg : 0 ≤ n - η j := by
      linarith
    have hnd : (d : ℤ) + η j = n := by
      -- The target degree exceeds the generator degree, so the difference is a positive natural.
      dsimp [d]
      rw [Int.toNat_of_nonneg hd_nonneg]
      linarith
    have hd_pos : 0 < d := by
      by_contra hd_not_pos
      have hd_zero : d = 0 := Nat.eq_zero_of_not_pos hd_not_pos
      have : n = η j := by
        calc
          n = ((d : ℤ) + η j) := by symm; exact hnd
          _ = η j := by simp [hd_zero]
      linarith
    have hscalar_zero : ((DirectSum.decompose 𝒜 (c j) d : 𝒜 d) : S) = 0 := by
      -- Positive-degree scalar components vanish because the irrelevant ideal is zero.
      exact eq_zero_of_mem_positive_degree_of_irrelevant_eq_bot
        (𝒜 := 𝒜) hd_pos (DirectSum.decompose 𝒜 (c j) d).2 hbot
    apply Subtype.ext
    -- Only the positive-degree scalar component could contribute to degree `n`, and it vanishes.
    simpa [hscalar_zero] using
      (decompose_smul_homogeneous_generator_eq (𝒜 := 𝒜) (ℳ := ℳ)
        (hm := hm j) (hnd := hnd) (a := c j) (m := m j))
  have hx_subtype_zero : (⟨x, hx⟩ : ℳ n) = 0 := by
    -- Every term in the projected generator expansion vanishes, so the degree-`n` component is
    -- zero.
    calc
      (⟨x, hx⟩ : ℳ n) = ∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n) := by
        symm
        exact hx_decompose
      _ = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        exact hterm_zero j
  simpa using congrArg (fun y : ℳ n ↦ (y : M)) hx_subtype_zero

/-- Helper for Proposition 10.58.7: when the irrelevant ideal is zero, the graded-piece
Grothendieck-class function is eventually zero. -/
lemma gradedPieceFiniteGrothendieckGroupClass_eventuallyEq_zero_of_irrelevant_eq_bot
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M]
    [Algebra.FiniteType (𝒜 0) S]
    (hbot : 𝒜₊.toIdeal = ⊥) :
    gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ =ᶠ[Filter.atTop] fun _ ↦ 0 := by
  obtain ⟨N, hN⟩ :=
    graded_piece_eq_bot_eventually_of_irrelevant_eq_bot (𝒜 := 𝒜) (ℳ := ℳ) hbot
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  -- Convert eventual vanishing of the graded pieces into eventual vanishing in `K'_0(S₀)`.
  exact
    gradedPieceFiniteGrothendieckGroupClass_eq_zero_of_eq_bot (𝒜 := 𝒜) (ℳ := ℳ)
      (hN n hn)

omit [IsNoetherianRing S] in
/-- Helper for Chap10 Proposition 10 58 7: because this Lean model stores each graded piece as an
`S`-submodule, finite homogeneous `S`-generators force all sufficiently high pieces to vanish. -/
lemma graded_piece_eq_bot_eventually_of_finite_homogeneous_span
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M]
    [Algebra.FiniteType (𝒜 0) S] :
    ∃ N : ℤ, ∀ n, N ≤ n → ℳ n = ⊥ := by
  classical
  obtain ⟨κ, _, m, η, hm, hspan⟩ :=
    exists_finite_homogeneous_module_generators (S := S) (M := M) (ℳ := ℳ)
  let N : ℤ := ((∑ j : κ, Int.natAbs (η j) : ℕ) : ℤ) + 1
  refine ⟨N, ?_⟩
  intro n hn
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx_span : x ∈ Submodule.span S (Set.range m) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hx_span
  have hx_decompose :
      (∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n)) = ⟨x, hx⟩ := by
    -- Project the finite homogeneous-generator expansion to the requested degree.
    calc
      (∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n)) =
          DirectSum.decompose ℳ (∑ j, c j • m j) n := by
            simp [DirectSum.decompose_sum]
      _ = DirectSum.decompose ℳ x n := by simpa [hc]
      _ = ⟨x, hx⟩ := by
            ext
            simpa [DirectSum.decompose_of_mem_same ℳ hx]
  have hterm_zero : ∀ j : κ, (DirectSum.decompose ℳ (c j • m j) n : ℳ n) = 0 := by
    intro j
    have hsum_nat : Int.natAbs (η j) ≤ ∑ k : κ, Int.natAbs (η k) := by
      exact
        (Finset.single_le_sum
          (fun k _ ↦ Nat.zero_le (Int.natAbs (η k))) (Finset.mem_univ j) :
          Int.natAbs (η j) ≤ ∑ k : κ, Int.natAbs (η k))
    have hη_le : η j ≤ ((∑ k : κ, Int.natAbs (η k) : ℕ) : ℤ) := by
      have hnatabs_le : (Int.natAbs (η j) : ℤ) ≤
          ((∑ k : κ, Int.natAbs (η k) : ℕ) : ℤ) := by
        exact_mod_cast hsum_nat
      exact le_trans (Int.le_natAbs (a := η j)) hnatabs_le
    have hη_lt : η j < n := by
      dsimp [N] at hn
      linarith
    have hsame_piece : c j • m j ∈ ℳ (η j) := by
      -- Unlike the textbook grading, the Lean pieces are `S`-submodules, so every `S`-multiple
      -- of a homogeneous generator remains in the generator's original piece.
      exact (ℳ (η j)).smul_mem (c j) (hm j)
    apply Subtype.ext
    -- A vector lying in degree `η j` has zero projection to the later degree `n`.
    simpa using
      (DirectSum.decompose_of_mem_ne ℳ hsame_piece (by linarith : η j ≠ n))
  have hx_subtype_zero : (⟨x, hx⟩ : ℳ n) = 0 := by
    -- All projected generator terms vanish, hence so does the degree-`n` component of `x`.
    calc
      (⟨x, hx⟩ : ℳ n) = ∑ j, (DirectSum.decompose ℳ (c j • m j) n : ℳ n) := by
        symm
        exact hx_decompose
      _ = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j _
        exact hterm_zero j
  simpa using congrArg (fun y : ℳ n ↦ (y : M)) hx_subtype_zero

/-- Helper for Chap10 Proposition 10 58 7: in the current Lean submodule-valued grading model,
finite graded modules have eventually zero Grothendieck classes. -/
lemma gradedPieceFiniteGrothendieckGroupClass_eventuallyEq_zero_of_finite_homogeneous_span
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M]
    [Algebra.FiniteType (𝒜 0) S] :
    gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ =ᶠ[Filter.atTop] fun _ ↦ 0 := by
  obtain ⟨N, hN⟩ :=
    graded_piece_eq_bot_eventually_of_finite_homogeneous_span (𝒜 := 𝒜) (ℳ := ℳ)
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  -- Convert eventual vanishing of pieces into eventual vanishing of their `K'_0(S₀)` classes.
  exact
    gradedPieceFiniteGrothendieckGroupClass_eq_zero_of_eq_bot (𝒜 := 𝒜) (ℳ := ℳ)
        (hN n hn)

/-- Helper for Chap10 Proposition 10 58 7: the stronger Lean grading model makes the
Grothendieck-class function numerical by eventual vanishing. -/
lemma gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_finite_homogeneous_span
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M]
    [Algebra.FiniteType (𝒜 0) S] :
    IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ) := by
  -- A function that is eventually zero is represented by the zero numerical polynomial.
  exact
    isNumericalPolynomial_of_eventuallyEq_zero <|
      gradedPieceFiniteGrothendieckGroupClass_eventuallyEq_zero_of_finite_homogeneous_span
        (𝒜 := 𝒜) (ℳ := ℳ)

/-- Helper for Proposition 10.58.7: if the irrelevant ideal is zero, then the graded-piece
Grothendieck-class function is numerical polynomial. -/
lemma gradedPieceFiniteGrothendieckGroupClass_isNumericalPolynomial_of_irrelevant_eq_bot
    {M : Type w} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M]
    [Algebra.FiniteType (𝒜 0) S]
    (hbot : 𝒜₊.toIdeal = ⊥) :
    IsNumericalPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ) := by
  -- Package the eventual-vanishing base case so the outer induction only has to invoke it.
  exact
    isNumericalPolynomial_of_eventuallyEq_zero <|
      gradedPieceFiniteGrothendieckGroupClass_eventuallyEq_zero_of_irrelevant_eq_bot
        (𝒜 := 𝒜) (ℳ := ℳ) hbot
