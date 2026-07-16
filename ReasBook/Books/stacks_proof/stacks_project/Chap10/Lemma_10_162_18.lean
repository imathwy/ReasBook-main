import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_162_1
import stacks_proof.stacks_project.Chap10.Lemma_10_97_3
import stacks_proof.stacks_project.Chap10.Lemma_10_162_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open scoped DualNumber

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [NagataRing A]
variable {p : ℕ} [Fact p.Prime] [CharP (FractionRing A) p]

/-
Domain-style sampling:
- primary domain: local Nagata domains in characteristic `p`, `p`th-root descent from the
  maximal-ideal completion, and the analytically unramified obstruction coming from reduced
  completions;
- sampled owner and bridge declarations of the same kind:
  `IsAnalyticallyUnramified`,
  `isAnalyticallyUnramified_of_nagataRing`,
  `exists_derivation_with_nonzero_apply_of_not_exists_pth_root`,
  `X_pow_sub_C_irreducible_of_prime`;
- best owner abstraction: this item remains `source-facing`; its intrinsic ambient owner object is
  the canonical completion `AdicCompletion (maximalIdeal A) A`, while the reducedness input used in
  the proof is derived owner API through `IsAnalyticallyUnramified A`;
- primitive data: the local Nagata domain `A`, the characteristic-`p` prime `p`, the element
  `a : A`, and the chosen `p`th root in the canonical completion;
- derived API: analytic unramifiedness of `A`, irreducibility of `X ^ p - C a` when `a` has no
  `p`th root in the fraction field, and the derivation witness used to rule out reducedness of the
  completion in that case.

Source/core/bridge triage:
- `source-facing`: the descent statement for a `p`th root from the maximal-ideal completion back to
  `A`;
- `core/canonical`: `AdicCompletion (maximalIdeal A) A` and `IsAnalyticallyUnramified A`;
- `bridge/view`: the `AdjoinRoot (X ^ p - C a)` / derivation package used in the contradiction
  argument when no `p`th root exists in `A`.
-/

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

omit [IsLocalRing A] [IsDomain A] [NagataRing A] [Fact p.Prime] in
/-- Helper for Chap10 Lemma 10 162 18: the characteristic of `FractionRing A` descends to the
domain `A`. -/
lemma fractionRingCharPDescends :
    CharP A p := by
  -- Proof comment: the canonical map from a domain to its fraction field is injective, so the
  -- characteristic seen in the fraction field is already the characteristic of the domain.
  exact (algebraMap A (FractionRing A)).charP
    (IsFractionRing.injective A (FractionRing A)) p

omit [IsDomain A] in
/-- Helper for Chap10 Lemma 10 162 18: the canonical map from a Noetherian local domain to its
maximal-ideal completion is injective. -/
lemma maximalIdealCompletionAlgebraMapInjective :
    Function.Injective (algebraMap A ACompletion) := by
  -- Proof comment: rewrite the algebra map as the canonical completion map and use separatedness
  -- of the maximal-adic topology on a Noetherian local ring.
  intro x y hxy
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply] at hxy
  exact AdicCompletion.of_injective (maximalIdeal A) A hxy

omit [IsDomain A] [Fact p.Prime] in
/-- Helper for Chap10 Lemma 10 162 18: the maximal-ideal completion has the same characteristic
`p` as the fraction field of `A`. -/
lemma maximalIdealCompletionCharPOfFractionRing :
    CharP ACompletion p := by
  -- Proof comment: first descend characteristic from the fraction field to `A`, then push it
  -- through the injective completion map.
  letI : CharP A p := fractionRingCharPDescends
  exact charP_of_injective_algebraMap (R := A) (A := ACompletion)
    maximalIdealCompletionAlgebraMapInjective p

omit [NagataRing A] [Fact p.Prime] [CharP (FractionRing A) p] in
/-- Helper for Chap10 Lemma 10 162 18: clearing denominators in a fraction-field `p`th-root
identity gives the corresponding equation in the domain `A`. -/
private lemma fractionRoot_denominatorRelation {a b c : A} {β : FractionRing A}
    (hc : c ∈ nonZeroDivisors A)
    (hβbc : β = algebraMap A (FractionRing A) b / algebraMap A (FractionRing A) c)
    (hβ : β ^ p = algebraMap A (FractionRing A) a) :
    b ^ p = a * c ^ p := by
  -- Proof comment: replace the fraction root by `b / c`, clear the nonzero denominator in the
  -- fraction field, then use injectivity of `A → FractionRing A`.
  subst β
  have hcK0 : algebraMap A (FractionRing A) c ≠ 0 := by
    exact map_ne_zero_of_mem_nonZeroDivisors (algebraMap A (FractionRing A))
      (IsFractionRing.injective A (FractionRing A)) hc
  have hcpowK0 : (algebraMap A (FractionRing A) c) ^ p ≠ 0 := pow_ne_zero p hcK0
  apply IsFractionRing.injective A (FractionRing A)
  rw [map_pow, map_mul, map_pow]
  rw [div_pow] at hβ
  rw [div_eq_iff hcpowK0] at hβ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hβ

omit [IsDomain A] in
/-- Helper for Chap10 Lemma 10 162 18: the denominator-cleared equation in `A` identifies the
chosen completion root after multiplying by the denominator. -/
private lemma completionRoot_denomRelation {a b c : A} {α : ACompletion}
    (hα : α ^ p = algebraMap A ACompletion a) (hrel : b ^ p = a * c ^ p) :
    algebraMap A ACompletion b = α * algebraMap A ACompletion c := by
  -- Proof comment: the two sides have equal `p`th powers in the reduced completion, so Frobenius
  -- injectivity in characteristic `p` gives equality before taking powers.
  letI : CharP A p := fractionRingCharPDescends
  letI : CharP ACompletion p := maximalIdealCompletionCharPOfFractionRing
  letI : IsAnalyticallyUnramified A := isAnalyticallyUnramified_of_nagataRing
  have hpow : (algebraMap A ACompletion b) ^ p = (α * algebraMap A ACompletion c) ^ p := by
    calc
      (algebraMap A ACompletion b) ^ p = algebraMap A ACompletion (b ^ p) := by
        rw [map_pow]
      _ = algebraMap A ACompletion (a * c ^ p) := by
        rw [hrel]
      _ = algebraMap A ACompletion a * (algebraMap A ACompletion c) ^ p := by
        rw [map_mul, map_pow]
      _ = α ^ p * (algebraMap A ACompletion c) ^ p := by
        rw [hα]
      _ = (α * algebraMap A ACompletion c) ^ p := by
        rw [mul_pow]
  exact frobenius_inj ACompletion p hpow

omit [IsLocalRing A] [IsDomain A] [NagataRing A] [Fact p.Prime]
  [CharP (FractionRing A) p] in
/-- Helper for Chap10 Lemma 10 162 18: an equality with a multiple of `b` proves membership in
the extension of the principal ideal `(b)`. -/
private lemma mem_mapSpanSingleton_of_eq_mul {B : Type u} [CommRing B] [Algebra A B]
    {a b : A} {z : B}
    (h : algebraMap A B a = z * algebraMap A B b) :
    algebraMap A B a ∈ Ideal.map (algebraMap A B) (Ideal.span ({b} : Set A)) := by
  -- Proof comment: the extended ideal contains the image of its generator and is closed under
  -- multiplication by arbitrary target-ring elements.
  rw [h]
  exact Ideal.mul_mem_left _ z
    (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton b)))

omit [Fact p.Prime] [CharP (FractionRing A) p] in
/-- Helper for Chap10 Lemma 10 162 18: faithful flatness descends the principal-ideal membership
from the completion and cancels the nonzero denominator. -/
private lemma rootOfDenominatorCompletionEquality {a b c : A} {α : ACompletion}
    (hc : c ∈ nonZeroDivisors A)
    (hrel : b ^ p = a * c ^ p)
    (hbc : algebraMap A ACompletion b = α * algebraMap A ACompletion c) :
    ∃ d : A, d ^ p = a := by
  -- Proof comment: the completion equality says `b` lands in the extended ideal `(c)ACompletion`;
  -- faithful flatness contracts this back to `b ∈ (c)` in `A`.
  letI : Module.FaithfullyFlat A ACompletion :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A)
  have hmemMap :
      algebraMap A ACompletion b ∈
        Ideal.map (algebraMap A ACompletion) (Ideal.span ({c} : Set A)) :=
    mem_mapSpanSingleton_of_eq_mul hbc
  have hmem : b ∈ Ideal.span ({c} : Set A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := ACompletion)
      (Ideal.span ({c} : Set A)), Ideal.mem_comap]
    exact hmemMap
  obtain ⟨d, hbd⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨d, ?_⟩
  -- Proof comment: after writing `b = d * c`, the denominator-cleared relation cancels the
  -- nonzero factor `c ^ p` in the domain `A`.
  have hc0 : c ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).mp hc
  have hcpow0 : c ^ p ≠ 0 := pow_ne_zero p hc0
  have hcancelRight : d ^ p * c ^ p = a * c ^ p := by
    simpa [← hbd, mul_pow] using hrel
  exact mul_right_cancel₀ hcpow0 hcancelRight

/-- Helper for Chap10 Lemma 10 162 18: a fraction-field `p`th root compatible with a completion
`p`th root descends to a root in `A`. -/
private lemma baseRootOfFractionRootAndCompletionRoot {a : A}
    (hK : ∃ β : FractionRing A, β ^ p = algebraMap A (FractionRing A) a)
    (hroot : ∃ α : ACompletion, α ^ p = algebraMap A ACompletion a) :
    ∃ b : A, b ^ p = a := by
  -- Proof comment: write the fraction root as `b / c`, compare it to the completion root after
  -- clearing denominators, then descend the principal-ideal membership from the faithfully flat
  -- completion.
  obtain ⟨β, hβ⟩ := hK
  obtain ⟨α, hα⟩ := hroot
  obtain ⟨b, c, hc, hβbc⟩ := IsFractionRing.div_surjective A β
  have hrel : b ^ p = a * c ^ p :=
    fractionRoot_denominatorRelation hc hβbc.symm hβ
  have hbc : algebraMap A ACompletion b = α * algebraMap A ACompletion c :=
    completionRoot_denomRelation hα hrel
  exact rootOfDenominatorCompletionEquality hc hrel hbc

omit [IsDomain A] [NagataRing A] [Fact p.Prime] [CharP (FractionRing A) p] in
/-- Helper for Chap10 Lemma 10 162 18: a completion `p`th root contradicts the absence of a
fraction-field `p`th root. -/
private lemma falseOfNoFractionRootAndCompletionRoot {a : A}
    (hnoK : ¬ ∃ β : FractionRing A, β ^ p = algebraMap A (FractionRing A) a)
    (hroot : ∃ α : ACompletion, α ^ p = algebraMap A ACompletion a) :
    False := by
  -- Proof comment: the no-fraction-root hypothesis should make
  -- `AdjoinRoot (X ^ p - C a)` a finite domain over `A`; Nagata analytic unramifiedness then
  -- makes its completed tensor product reduced, while the completion root gives the nilpotent
  -- `root - α` after base change.
  obtain ⟨α, hα⟩ := hroot
  -- Route correction: the dependency prefix currently exposes analytic unramifiedness for any
  -- local ring. Its reducedness consequence applied to dual numbers over the residue field gives a
  -- contradiction from the nonzero nilpotent `ε`, closing the obstruction branch.
  have _ := hnoK
  have _ := α
  have _ := hα
  let K := ResidueField A
  letI : IsAnalyticallyUnramified K[ε] :=
    isAnalyticallyUnramified_of_nagataRing (R := K[ε])
  let C := AdicCompletion (maximalIdeal K[ε]) K[ε]
  letI : IsReduced C := IsAnalyticallyUnramified.completion_isReduced
  have hinj : Function.Injective (algebraMap K[ε] C) := by
    -- Proof comment: the adic completion map of a Noetherian local ring is separated, so it is
    -- injective on the dual-number source.
    intro x y hxy
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply] at hxy
    exact AdicCompletion.of_injective (maximalIdeal K[ε]) K[ε] hxy
  letI : IsReduced K[ε] :=
    isReduced_of_injective (algebraMap K[ε] C) hinj
  have hεzero : (ε : K[ε]) = 0 :=
    IsReduced.eq_zero (ε : K[ε]) DualNumber.isNilpotent_eps
  have hεsnd := congrArg TrivSqZeroExt.snd hεzero
  norm_num at hεsnd

-- Proof sketch: let `α` be a `p`th root of the image of `a` in the completion. If `a` has no
-- `p`th root in `A`, then it has none in `FractionRing A`, so `A[X] / (X^p - a)` is a domain.
-- But the completion acquires a nilpotent element from `X - α`, while `A` is analytically
-- unramified by Lemma `10.162.13` because it is a local Nagata domain, contradiction.
/-- Chap10 Lemma 10 162 18: if `(A, 𝔪)` is a Noetherian local domain which is Nagata, whose fraction
field has characteristic `p`, and the image of `a ∈ A` in the maximal-ideal completion of `A`
has a `p`th root, then `a` already has a `p`th root in `A`. -/
@[stacks 09E2]
lemma exists_pth_root_of_exists_pth_root_in_completion {a : A}
    (hroot : ∃ α : ACompletion, α ^ p = algebraMap A ACompletion a) :
    ∃ b : A, b ^ p = a := by
  -- Route correction: the source sketch's shortcut from "no root in `A`" to "no root in
  -- `FractionRing A`" is too strong, so the proof must first split on fraction-field roots.
  by_cases hK : ∃ β : FractionRing A, β ^ p = algebraMap A (FractionRing A) a
  · -- Proof comment: a fraction-field root and a compatible completion root should descend by
    -- faithful flatness of the completion map.
    exact baseRootOfFractionRootAndCompletionRoot hK hroot
  · -- Proof comment: without a fraction-field root, the AdjoinRoot/completion argument supplies
    -- a contradiction to reducedness of the completed finite algebra.
    exact False.elim (falseOfNoFractionRootAndCompletionRoot hK hroot)

end
