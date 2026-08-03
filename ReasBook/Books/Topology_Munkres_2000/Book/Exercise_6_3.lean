module

public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Equiv.Defs

public section

namespace BinarySequence

/-- The set of infinite binary sequences whose initial value is `false`. -/
@[expose] def zeroHead : Set (ℕ → Bool) :=
  {x | x 0 = false}

/-- Prefix an infinite binary sequence with `false`. -/
@[expose] def prependFalse (x : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => x n

/-- Prefixing with `false` produces a sequence in `zeroHead`. -/
@[simp] theorem prependFalse_mem (x : ℕ → Bool) : prependFalse x ∈ zeroHead := rfl

/-- Prefix an infinite binary sequence with `false`, viewed in `zeroHead`. -/
@[expose] def prependFalseInto (x : ℕ → Bool) : zeroHead :=
  ⟨prependFalse x, prependFalse_mem x⟩

/-- Remove the initial coordinate from an infinite binary sequence. -/
@[expose] def dropFirst (x : ℕ → Bool) (n : ℕ) : Bool :=
  x (n + 1)

/-- Removing the coordinate added by `prependFalseInto` recovers the original sequence. -/
@[simp] theorem dropFirst_prependFalseInto (x : ℕ → Bool) :
    dropFirst (prependFalseInto x) = x := by
  funext n
  rfl

/-- Prefixing the tail of a zero-head sequence recovers that sequence. -/
@[simp] theorem prependFalseInto_dropFirst (x : zeroHead) :
    prependFalseInto (dropFirst x) = x := by
  apply Subtype.ext
  funext n
  cases n with
  | zero => exact x.property.symm
  | succ n => rfl

/-- Exercise 6.3: Taking `Bool` as `{0, 1}` with `false` representing `0`, infinite binary
sequences correspond bijectively to those whose initial value is zero. -/
@[expose] def equivZeroHead : (ℕ → Bool) ≃ zeroHead where
  toFun := prependFalseInto
  invFun := fun x ↦ dropFirst x
  left_inv := dropFirst_prependFalseInto
  right_inv := prependFalseInto_dropFirst

/-- The equivalence prefixes a binary sequence with `false`. -/
@[simp] theorem equivZeroHead_apply (x : ℕ → Bool) :
    equivZeroHead x = prependFalseInto x := rfl

/-- The set of binary sequences whose initial value is zero is a proper subset of all infinite
binary sequences. -/
theorem zeroHead_ssubset : zeroHead ⊂ (Set.univ : Set (ℕ → Bool)) := by
  refine ⟨Set.subset_univ zeroHead, ?_⟩
  intro h
  have h_true : (fun _ ↦ true) ∈ zeroHead := h (Set.mem_univ _)
  exact Bool.noConfusion h_true

end BinarySequence
