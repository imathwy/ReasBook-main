import Mathlib

/-!
Source/core/bridge triage:

- `source-facing`: Definition 36.4.1 introduces the inverse bifunction `F_*`, characterized by
  `(F_* x) u = - (F u) x`.
- `core/canonical`: the primitive mathematical content is the canonical function expression
  `-Function.swap F`.
- `bridge/view`: this file uses textbook notation `F_*` directly for that canonical expression,
  without introducing a separate wrapper owner.

Domain-style sampling used here:
- `Bifunction.adjoint` from `Chap06.Lemma_31_0_8`, which keeps a source-facing bifunction
  owner while defining it as a thin bridge to canonical function-level operations;
- `Bifunction.objective` from `Chap06.Definition_6_29_12`, which exposes a chapter owner with only
  atomic companion lemmas;
- `Bifunction.lowerClosure_swap_apply` from `Chap07.Defn_34_1`, which already uses
  `Function.swap` as the chapter's canonical variable-exchange bridge;
- the canonical primitive `Function.swap`, which already supplies the underlying variable exchange.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → L`;
- primitive core expression: `-Function.swap F`;
- derived API: the defining application formula and the involution law.

Layer target: `source-facing`.

Notation decision:
- the source writes `F_*`; this file therefore exposes that textbook surface as scoped notation
  directly on the canonical expression `-Function.swap F`;
- nearby theorem surfaces use the corresponding Lean notation `F _*` explicitly.
-/

universe u v w

noncomputable section

namespace Rockafellar

/- Textbook notation for the inverse bifunction from Definition 36.4.1. -/
scoped[Rockafellar] notation:max F " _*" => -Function.swap F

end Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {L : Type w}

open scoped Rockafellar

/- Primitive bridge from the textbook inverse notation to the canonical core expression. -/
theorem inverse_eq_neg_swap
    [Neg L] (F : U → X → L) :
    F _* = -Function.swap F :=
  rfl

@[simp] theorem inverse_apply
    [Neg L] (F : U → X → L) (x : X) (u : U) :
    F _* x u = -F u x :=
  rfl

/- The notation-level inverse maps are mutual inverses between swapped bifunction spaces. -/
theorem inverse_leftInverse
    [InvolutiveNeg L] :
    Function.LeftInverse
      (fun G : X → U → L => G _*)
      (fun F : U → X → L => F _*) := by
  intro F
  funext u x
  simp

/- Symmetric notation-level inverse law with swapped source/target spaces. -/
theorem inverse_rightInverse
    [InvolutiveNeg L] :
    Function.RightInverse
      (fun G : X → U → L => G _*)
      (fun F : U → X → L => F _*) :=
  inverse_leftInverse

@[simp] theorem inverse_inverse
    [InvolutiveNeg L] (F : U → X → L) :
    (F _*) _* = F :=
  inverse_leftInverse F

end

end Bifunction
