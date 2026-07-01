import Mathlib
import stacks_project.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory Sequence IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module

/- 
Domain-style sampling:
* primary domain: regular sequences, depth/support dimension, and Cohen-Macaulay quotients over
  Noetherian local rings;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.depth_le_supportDim`,
  `IsRegular.exists_append_eq_moduleDepth`,
  `RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular`;
* best owner abstraction: the source-facing owner in this file is the predicate
  `IsGoodWithRespectTo M g fs`, built from the canonical quotient/support-dimension API
  `QuotSMulTop` and `supportDim`; the primitive ambient owner data are `Module.Finite R M` and
  `IsRegular M fs`, while `CohenMacaulay R M` is derived internally from the maximal-length
  regular sequence hypothesis `supportDim R M = fs.length`;

Source/core/bridge triage:
* source-facing: the predicate `IsGoodWithRespectTo M g fs` formalizes the source notion that
  `g ∈ maximalIdeal R` is good with respect to the maximal regular sequence `fs`;
* core/canonical: `Module.Finite R M`, `moduleDepth R M`, `CohenMacaulay R M`,
  `RingTheory.Sequence.IsRegular M fs`, `QuotSMulTop g`, and `supportDim R`;
* bridge/view: the source notion is expressed through the canonical support-dimension equalities
  for the prefix quotients, and the Cohen-Macaulay owner condition is recovered from
  `depth_le_supportDim` and `IsRegular.exists_append_eq_moduleDepth` rather than stored as
  primitive input data.
-/

variable [Module.Finite R M] {fs : List R} {g : R}

/-- `g` is good with respect to the finite module `M` and the sequence `fs` when
`g ∈ maximalIdeal R` and each prefix quotient
`M ⧸ (Ideal.ofList (fs.take i) • (⊤ : Submodule R M))` has support dimension lowered by exactly
`1` after quotienting by `g`. This is the quotient-module form of the source condition
`dim (Supp(M/(f₁, …, fᵢ)M) ∩ V(g)) = d - i - 1`. -/
def IsGoodWithRespectTo (M : Type v) [AddCommGroup M] [Module R M] (g : R) (fs : List R) : Prop :=
  g ∈ maximalIdeal R ∧
    ∀ i : Fin fs.length,
      supportDim R
          (QuotSMulTop g
            (M ⧸ (Ideal.ofList (fs.take i) • (⊤ : Submodule R M)))) =
        ((fs.length - i - 1 : ℕ) : WithBot ℕ∞)

-- Proof sketch: first derive `CohenMacaulay R M` internally from `hfs` and `hMdim`. The regular
-- sequence gives `Nontrivial M`, `depth_le_supportDim` yields
-- `moduleDepth R M ≤ supportDim R M = fs.length`, and
-- `IsRegular.exists_append_eq_moduleDepth hfs` forces the reverse inequality, so
-- `supportDim R M = .some (moduleDepth R M)`. Then induct on `fs.length`, exactly as in the
-- source. For the inductive step, the `i.succ` instances of `hgood` identify `g` as good with
-- respect to the tail sequence on the quotient by `f₁`, so induction gives that `g` is a
-- nonzerodivisor on `M / f₁M` and that `M / (g, f₁)M` is Cohen-Macaulay with regular sequence
-- `fs.tail.take (fs.length - 2)`. Then
-- `RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular` upgrades this to the
-- stated regularity and Cohen-Macaulay consequences on `M` and `M / gM`.
/-- Lemma 10.103.2 (a): if `fs` is an `M`-regular sequence with
`supportDim R M = fs.length`, `0 < fs.length`, and `g` is good with respect to `(M, fs)`, then
`g` is a nonzerodivisor on `M`. The Cohen-Macaulay condition on `M` is derived internally from the
maximal-length regular sequence hypothesis. -/
theorem isSMulRegular_of_isGoodWithRespectTo
    (hMdim : supportDim R M = fs.length)
    (hpos : 0 < fs.length)
    (hfs : IsRegular M fs)
    (hgood : IsGoodWithRespectTo M g fs) :
    IsSMulRegular M g := sorry

-- Proof sketch: apply part (a) after deriving `CohenMacaulay R M` internally from `hMdim` and
-- `hfs`. The tail part of `hgood` is the corresponding goodness condition for the quotient by the
-- first element of `fs`, so the inductive argument gives Cohen-Macaulayness of `M / (g, f₁)M`
-- together with regularity of the shortened sequence on that quotient. Appending back `f₁` shows
-- that `fs.take (fs.length - 1)` is regular on `M / gM`, and `hgood` at `i = 0` gives the
-- support-dimension formula for `QuotSMulTop g M`.
/-- Lemma 10.103.2 (b): under the same hypotheses, `M / gM`, written as `QuotSMulTop g M`, is
Cohen--Macaulay with maximal regular sequence `fs.take (fs.length - 1)`. The `i = 0` case of
`hgood` yields the support-dimension equality
`supportDim R (QuotSMulTop g M) = fs.length - 1`, and the Cohen-Macaulay hypothesis on `M` is
again derived internally from `hMdim` and `hfs`. -/
theorem cohenMacaulay_quotSMulTop_and_isRegular_take_of_isGoodWithRespectTo
    (hMdim : supportDim R M = fs.length)
    (hpos : 0 < fs.length)
    (hfs : IsRegular M fs)
    (hgood : IsGoodWithRespectTo M g fs) :
    CohenMacaulay R (QuotSMulTop g M) ∧
      IsRegular (QuotSMulTop g M) (fs.take (fs.length - 1)) ∧
      supportDim R (QuotSMulTop g M) = ((fs.length - 1 : ℕ) : WithBot ℕ∞) := sorry

end Module

end
