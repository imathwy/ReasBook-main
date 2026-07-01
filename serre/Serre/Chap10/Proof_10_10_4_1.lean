import Mathlib
import Serre.Chap10.Definition_10_10_1_3
import Serre.Chap10.Theorem_10_10_2_2
import Serre.Chap12.CharacterRingOverFieldScalarExtension

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Representation
open scoped Representation TensorProduct SubgroupInduction

universe v

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [Algebra A ℂ]

local instance : Fintype G := Fintype.ofFinite G

/-- Helper for Proof 10-10.4-1: Serre's tensor owner `A ⊗ V_p` for the ambient finite group `G`.
-/
scoped[Representation] notation:max A " ⊗V[" p "](" G ")" => TensorProduct ℤ A (V[p](G))

/-- Helper for Proof 10-10.4-1: the canonical inclusion of Brauer's subgroup `V_p` into the
ambient space of complex-valued class functions on `G`. -/
abbrev pElementaryInducedCharacterToFunction
    (p : ℕ) (G : Type) [Group G] [Finite G] :
    V[p](G) →ₗ[ℤ] G → ℂ :=
  ((R[ℂ](G)).toSubmodule.subtype).comp (V[p](G)).subtype

/-- Helper for Proof 10-10.4-1: the canonical realization of `A ⊗ V_p` as a complex-valued class
function on `G`. -/
abbrev tensorPElementaryInducedCharacterToFunction
    (A : Type v) [CommRing A] [Algebra A ℂ]
    (p : ℕ) (G : Type) [Group G] [Finite G] :
    A ⊗V[p](G) →ₗ[A] G → ℂ :=
  (pElementaryInducedCharacterToFunction p G).liftBaseChange A

/-- Helper for Proof 10-10.4-1: elements of `A ⊗ V_p` act as complex-valued functions on `G`
through the canonical tensor realization map. -/
instance : CoeFun (A ⊗V[p](G)) (fun _ ↦ G → ℂ) where
  coe := tensorPElementaryInducedCharacterToFunction A p G

/-- Helper for Proof 10-10.4-1: a pure tensor acts by scalar multiplication on the underlying
class function attached to its `V_p` factor. -/
@[simp] theorem coe_tmul_pElementaryInducedCharacter
    (a : A) (χ : V[p](G)) :
    ((a ⊗ₜ[ℤ] χ : A ⊗V[p](G)) : G → ℂ) = a • ((χ : R[ℂ](G)) : G → ℂ) := by
  -- Unfold the tensor realization map and evaluate the base-changed pure tensor.
  simp [tensorPElementaryInducedCharacterToFunction, pElementaryInducedCharacterToFunction]

section

variable {p : ℕ} [Fact p.Prime]

omit [Finite G] in
/-- Helper for Proof 10-10.4-1: scaling the trivial character by the prime-to-`p` factor `l`
realizes the constant class function with value `l`. -/
lemma smul_trivialCharacter_eq_constant (l : ℕ) :
    (((l • (1 : R[ℂ](G)) : R[ℂ](G)) : G → ℂ)) = fun _ ↦ (l : ℂ) := by
  -- Evaluate the trivial character pointwise; it is constantly `1`, so the scalar multiple is
  -- constantly `l`.
  funext g
  simp

-- Route correction: the proof now reuses the existing Chapter 10.2 theorem `l • 1 ∈ V_p`,
-- while keeping only the small local tensor-realization bridge needed to evaluate `1 ⊗ (l • 1)`.
/-- Proof 10-10.4-1: if `|G| = p^n l` with `l` prime to `p`, then the constant class function with
value `l` is realized by an element of Serre's tensor product `A ⊗V[p](G)`. -/
theorem exists_constant_tensorPElementaryInducedCharacter_of_primeToPart_card
    (n l : ℕ) (hcard : Nat.card G = p ^ n * l) (hl : Nat.Coprime p l) :
    ∃ ψ : A ⊗V[p](G), (ψ : G → ℂ) = fun _ ↦ (l : ℂ) := by
  -- Import the Chapter 10.2 membership statement as the structural core of the argument.
  have hχ : l • (1 : R[ℂ](G)) ∈ V[p](G) := by
    simpa using
      primeToPart_card_smul_trivialCharacter_mem_pElementaryInducedCharacterSpan
        (G := G) p n l hcard hl
  let χp : V[p](G) := ⟨l • (1 : R[ℂ](G)), hχ⟩
  refine ⟨(1 : A) ⊗ₜ[ℤ] χp, ?_⟩
  -- Realize the chosen `V_p` element as a pure tensor and compute the resulting class function.
  rw [coe_tmul_pElementaryInducedCharacter]
  -- The underlying `V_p` element is exactly the constant character with value `l`.
  simpa [χp] using (smul_trivialCharacter_eq_constant (G := G) l)

end

end
