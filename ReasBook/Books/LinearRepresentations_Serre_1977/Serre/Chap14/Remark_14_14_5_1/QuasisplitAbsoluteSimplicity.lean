import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.AbsoluteSimplicity
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.CharZeroAbsoluteSimplicity
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_5_1.SemisimpleSchur

/-!
# Quasisplit ⟹ absolute simplicity (the representation-level form of Serre's `d_E = 1`)

This module assembles Serre's own argument for `d_E = 1` (Remark 14-14.5-1) at the level of
representations, in characteristic `0`.

Serre offers two faithful routes to "`d_E = 1` when `K` is sufficiently large":
* (1) reduce `d` mod `𝔪` from Theorem 24 (`R_K(G) = R(G)`, Brauer induction);
* (2) use that Schur indices over `k` are `1`, which "reduces the proof to showing that characters
  of representations of `G` over an extension of `k` always have values in `k`".

Both share the same hinge: over a sufficiently large characteristic-`0` field, the intrinsic and
ordinary character rings coincide — Serre's **quasisplit** identity `R[k](G) = R̄[k](G)` (Theorem
24). The present lemma turns that ring identity into the geometric statement it encodes: every
simple `k[G]`-representation stays irreducible after extension to the algebraic closure
(absolute simplicity, i.e. `d_E = 1`). It is the missing public wiring between the quasisplit
hypothesis and absolute irreducibility.

The proof is a clean assembly of already-proven, axiom-clean inputs:
* `finrank_intertwiningMap_eq_one_of_quasisplit` (Serre's `d_E = 1` as a dimension count): quasisplit
  forces `dim_k End_{k[G]}(S) = 1`;
* `finrank_intertwiningMap_eq_scalarExtension` (flat End base change): hence
  `dim_k̄ End_{k̄[G]}(S ⊗ k̄) = 1`;
* Maschke (characteristic `0`): `S ⊗ k̄` is a semisimple `k̄[G]`-representation;
* `isIrreducible_of_isSemisimpleRepresentation_of_finrank_intertwiningMap_eq_one`: a semisimple
  representation with one-dimensional self-intertwiners is irreducible.

The only classical input still missing for the field-level splitting theorem
`scalarExtension_isIrreducible_of_isSplittingField` is precisely the quasisplit identity
`hquasi` itself — Serre's Theorem 24 over an arbitrary characteristic-`0` base field — which the
repository currently proves only over a base admitting an embedding into `ℂ`
(`Exercise_12_12_3_3`, via the `ℂ`-bound Brauer-induction stack `Theorem_12_12_3_1`).
-/

noncomputable section

universe u

open scoped Representation TensorProduct

open CategoryTheory

namespace Representation

section CharZeroQuasisplit

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type u} [Group G] [Finite G]

/-- **Quasisplit ⟹ absolute simplicity (Serre's `d_E = 1`, representation level).** Over a
characteristic-`0` field `k` with enough roots of unity for the exponent of `G`, the quasisplit
identity `R[k](G) = R̄[k](G)` (Serre's Theorem 24) forces every simple `k[G]`-representation `S`
to remain irreducible after extending scalars to the algebraic closure `k̄`. -/
theorem scalarExtension_isIrreducible_of_quasisplit
    [HasEnoughRootsOfUnity k (Monoid.exponent G)]
    (hquasi : R[k](G) = R̄[k](G))
    (S : FDRep k G) [Simple S] :
    Representation.IsIrreducible
      (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ) := by
  -- Serre's `d_E = 1`, as a dimension count over `k`.
  have hk : Module.finrank k (Representation.IntertwiningMap S.ρ S.ρ) = 1 :=
    finrank_intertwiningMap_eq_one_of_quasisplit hquasi S
  -- Flat End base change transports it to the algebraic closure.
  have hkbar :
      Module.finrank (AlgebraicClosure k)
        (Representation.IntertwiningMap
          (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ)
          (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ)) = 1 := by
    rw [finrank_intertwiningMap_eq_scalarExtension S.ρ, hk]
  -- Characteristic `0` makes `|G|` invertible in `k̄`, so Maschke applies to `S ⊗ k̄`.
  haveI : NeZero (Nat.card G : AlgebraicClosure k) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  -- A semisimple representation with one-dimensional self-intertwiners is irreducible.
  exact isIrreducible_of_isSemisimpleRepresentation_of_finrank_intertwiningMap_eq_one
    (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ) hkbar

end CharZeroQuasisplit

end Representation
