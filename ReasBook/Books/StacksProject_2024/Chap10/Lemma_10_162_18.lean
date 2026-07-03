import Mathlib
import StacksProject_2024.Chap10.Definition_10_162_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

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

-- Proof sketch: let `α` be a `p`th root of the image of `a` in the completion. If `a` has no
-- `p`th root in `A`, then it has none in `FractionRing A`, so `A[X] / (X^p - a)` is a domain.
-- But the completion acquires a nilpotent element from `X - α`, while `A` is analytically
-- unramified by Lemma `10.162.13` because it is a local Nagata domain, contradiction.
/-- Lemma 10.162.18: if `(A, 𝔪)` is a Noetherian local domain which is Nagata, whose fraction
field has characteristic `p`, and the image of `a ∈ A` in the maximal-ideal completion of `A`
has a `p`th root, then `a` already has a `p`th root in `A`. -/
lemma exists_pth_root_of_exists_pth_root_in_completion {a : A}
    (hroot : ∃ α : ACompletion, α ^ p = algebraMap A ACompletion a) :
    ∃ b : A, b ^ p = a := sorry

end
