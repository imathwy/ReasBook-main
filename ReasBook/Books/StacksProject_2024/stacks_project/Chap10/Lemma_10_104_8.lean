import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_1
import StacksProject_2024.Chap10.Lemma_10_5_3
import StacksProject_2024.Chap10.Lemma_10_72_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : ShortComplex (ModuleCat.{u} R)}

/-
Domain-style sampling:
* primary domain: module depth in short exact sequences over Noetherian local Cohen-Macaulay rings;
* sampled owner declarations:
  `moduleDepth`,
  `Module.CohenMacaulay`,
  `Module.Free`,
  `Module.Finite`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min`;
* best owner abstraction: the short exact complex `S` with `hS : S.ShortExact`; the finite free
  middle term is expressed intrinsically by `[Module.Free R S.X₂]` and
  `[Module.Finite R S.X₂]`;
* source/core/bridge triage:
  this theorem remains `source-facing`, because it records the special trichotomy for an exact
  sequence whose middle term is finite free over a Cohen-Macaulay local ring;
  the exact-sequence data itself is `core/canonical`, carried by `hS : S.ShortExact`;
  any coordinate identification of `S.X₂` with a finite product of copies of `R` is only the
  `bridge/view`, obtained internally from `Module.Free.chooseBasis R S.X₂`;
* primitive data: `hS`, the Cohen-Macaulay owner hypothesis `hCM : Module.CohenMacaulay R R`, the
  dimension equality `hdim`, and the intrinsic finite-free owner data on `S.X₂`;
* derived API: `S.X₃` is finite because it is a quotient of the finite middle term, and then `S.X₁`
  is finite by the canonical exact-sequence owner theorem `Module.Finite.of_exact_of_finitePresentation`;
  the depth comparisons belong to the existing owner lemmas from Lemma `10.72.6`, while any basis
  choice and transfer of depth across the resulting linear equivalence are proof-level derived data.
-/

-- Proof sketch: if `S.X₃ = 0`, this is the first alternative. Otherwise `S.X₂` is nonzero because
-- `hS.moduleCat_surjective_g` is onto. Choose a basis of the finite free module `S.X₂`, whose
-- finite index type is derived from `[Module.Finite R S.X₂]`, and use the induced linear
-- equivalence with a finite product of copies of `R` to identify `moduleDepth R S.X₂` with `d`
-- from `hCM` and `hdim`. Then apply the canonical short-exact depth inequalities from
-- Lemma `10.72.6` to compare `moduleDepth R S.X₁` and `moduleDepth R S.X₃`, obtaining either a
-- strict increase or equality at the top value `d`.
/-- Lemma 10.104.8: let `R` be a Noetherian local Cohen-Macaulay ring of dimension `d`, and let
`0 → K → P → M → 0` be a short exact sequence of `R`-modules with `P` finite free. In the
chapter's canonical owner language, this is a short exact complex `S` whose middle term `S.X₂`
carries `[Module.Free R S.X₂]` and `[Module.Finite R S.X₂]`; the endpoint finiteness needed for
`moduleDepth` is derived internally from `hS`. Then either `M = 0`, or `depth(K) > depth(M)`, or
`depth(K) = depth(M) = d`. -/
theorem moduleDepth_kernel_trichotomy_of_exact_free_over_cohenMacaulayLocalRing
    {d : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hS : S.ShortExact) [Module.Free R S.X₂] [Module.Finite R S.X₂] :
    letI : Module.Finite R S.X₃ := Module.Finite.of_surjective S.g.hom hS.moduleCat_surjective_g
    letI : Module.Finite R S.X₁ := by
      letI : Module.FinitePresentation R S.X₃ := Module.finitePresentation_of_finite R S.X₃
      exact Module.Finite.of_exact_of_finitePresentation S.f.hom S.g.hom
        hS.moduleCat_injective_f hS.moduleCat_surjective_g
        ((moduleCat_exact_iff_function_exact S).mp hS.exact)
    Subsingleton S.X₃ ∨ moduleDepth R S.X₁ > moduleDepth R S.X₃ ∨
      (moduleDepth R S.X₁ = d ∧ moduleDepth R S.X₃ = d) := by
  sorry

end

end ShortExact
end ShortComplex
end CategoryTheory
