import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Length

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/- Domain triage:
- `source-facing`: the lemma packages the textbook equivalence between simplicity, length `1`,
  and being a quotient by a maximal ideal.
- `core/canonical`: the owner abstraction is mathlib's `IsSimpleModule R M`.
- `bridge/view`: this file's theorem is the TFAE packaging of the two canonical characterizations
  `Module.length_eq_one_iff` and `isSimpleModule_iff_quot_maximal`.
- Primitive data vs derived API: there is no extra primitive data here beyond the owner notion;
  the length-one and quotient-by-a-maximal-ideal clauses are derived API.
-/
/-- Lemma 10.52.10: for an `R`-module `M`, the following are equivalent: `M` is simple,
`Module.length R M = 1`, and `M` is linearly isomorphic to `R ⧸ m` for some maximal ideal
`m` of `R`. -/
@[stacks 00J2]
theorem isSimpleModule_tfae_length_eq_one_quotient_maximal :
    List.TFAE
      [IsSimpleModule R M,
        Module.length R M = 1,
        ∃ m : Ideal R, m.IsMaximal ∧ Nonempty (M ≃ₗ[R] R ⧸ m)] := by
  tfae_have 1 ↔ 2 := Module.length_eq_one_iff.symm
  tfae_have 1 ↔ 3 := isSimpleModule_iff_quot_maximal
  tfae_finish

end Length
