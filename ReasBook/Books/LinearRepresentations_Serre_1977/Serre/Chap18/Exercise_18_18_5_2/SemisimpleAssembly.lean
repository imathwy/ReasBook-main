import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.SemisimpleCompleteness
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.PrimeFieldTransport
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

/-!
# Semisimple-branch assembly for Exercise 18.5.2

Assembles the completeness of `s4_explicit_family k` (`SemisimpleCompleteness.lean`) with the
prime-field character transport (`PrimeFieldTransport.lean`) into the semisimple branch of the
completeness sub-lemma: when `(2 : k) ≠ 0` and `(3 : k) ≠ 0`, every irreducible
`S₄`-representation over the algebraically closed field `k` is equivalent to the scalar extension,
from the prime subfield, of one of Serre's five explicit prime-field models.

The genuinely new generic tool is `nonempty_equiv_of_char_eq_isIrr`: over a semisimple
algebraically closed field, two irreducible representations with equal character are equivalent
(robust in every characteristic that makes the order invertible, since `char_orthonormal` only
compares against `1` vs `0`).

The single remaining gap (see `scalarExtension_isIrreducible_of_isIrreducible_primeField`) is the
*absolute irreducibility* of the prime-field models: that the scalar extension to the algebraically
closed field `k` of a representation irreducible over the prime subfield stays irreducible.
Everything else in the semisimple branch — completeness of the native family, the transport from
`ULift S₄` to `S₄`, the character bridge, and character ⟹ isomorphism — is proven.
-/

attribute [-instance] Field.henselian

noncomputable section

open CategoryTheory
open Representation

namespace Representation

section

local notation "S4" => Equiv.Perm (Fin 4)

universe u

variable {k : Type u} [Field k]

/-- Over a semisimple algebraically closed field, two irreducible representations with equal
character are equivalent.  (`char_orthonormal` compares only against `1` vs `0`, so this is robust
in every characteristic that makes the order invertible.) -/
theorem nonempty_equiv_of_char_eq_isIrr [IsAlgClosed k]
    [Invertible (Nat.card S4 : k)]
    {V W : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k S4 V) [ρ.IsIrreducible]
    (σ : Representation k S4 W) [σ.IsIrreducible]
    (hchar : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  classical
  have hself : (Nat.card S4 : k)⁻¹ * ∑ g : S4, ρ.character g * ρ.character g⁻¹ = (1 : k) := by
    have h := char_orthonormal (ρ := ρ) (σ := ρ)
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at h
    simpa using h
  have key := char_orthonormal (ρ := ρ) (σ := σ)
  rw [← hchar, hself] at key
  -- key : (1 : k) = if Nonempty (σ.Equiv ρ) then ↑1 else ↑0
  by_cases hcase : Nonempty (σ.Equiv ρ)
  · exact hcase.elim fun e ↦ ⟨e.symm⟩
  · rw [if_neg hcase] at key
    exact absurd key (by simpa using (one_ne_zero : (1 : k) ≠ 0))

/-- Transport from the `ULift S₄` family to `S₄`: if `ρ.comp ulift` matches the lifted slot of a
native model `ρn`, then `ρ` and `ρn` have the same character on `S₄`. -/
theorem rho_char_eq_of_lift
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Wn : Type u} [AddCommGroup Wn] [Module k Wn] [FiniteDimensional k Wn]
    (ρ : Representation k S4 V) (ρn : Representation k S4 Wn) (j : Fin 5)
    (hfam : s4_explicit_family k j = FDRep.of (ulift_group_carrier_representation ρn))
    (hlift : (FDRep.of (ρ.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom)).character
      = (s4_explicit_family k j).character) :
    ρ.character = ρn.character := by
  set ι := (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4) with hι
  funext h
  have hcl := congrFun hlift (ι.symm h)
  rw [hfam] at hcl
  have hL : (FDRep.of (ρ.comp ι.toMonoidHom)).character (ι.symm h) = ρ.character h := by
    show ρ.character (ι (ι.symm h)) = ρ.character h
    rw [MulEquiv.apply_symm_apply]
  have hR : (FDRep.of (ulift_group_carrier_representation ρn)).character (ι.symm h)
      = ρn.character h := by
    show (ulift_group_carrier_representation ρn).character (ι.symm h) = ρn.character h
    rw [ulift_group_carrier_character_apply]
    show ρn.character (ι (ι.symm h)) = ρn.character h
    rw [MulEquiv.apply_symm_apply]
  rw [hL, hR] at hcl
  exact hcl

/-- **Absolute irreducibility via Schur.**  If the native model `ρn` over `k` is irreducible and
the scalar extension `scalarExtension ρ₀` has the same character and the same dimension as `ρn`,
then `scalarExtension ρ₀` is irreducible.  (A nonzero intertwiner `ρn → scalarExtension ρ₀` exists
because the character self-pairing is `1 ≠ 0`; it is injective since `ρn` is simple, and surjective
since the dimensions agree, hence an isomorphism.)  This is char-`p`-robust: it only uses that the
intertwiner dimension is *nonzero* in `k`. -/
theorem scalarExtension_isIrreducible_of_native [IsAlgClosed k] [Invertible (Nat.card S4 : k)]
    {W₀ : Type u} [AddCommGroup W₀] [Module ↥(⊥ : Subfield k) W₀]
    [FiniteDimensional ↥(⊥ : Subfield k) W₀]
    {Wn : Type u} [AddCommGroup Wn] [Module k Wn] [FiniteDimensional k Wn]
    (ρ₀ : Representation ↥(⊥ : Subfield k) S4 W₀)
    (ρn : Representation k S4 Wn) [ρn.IsIrreducible]
    (hdim : Module.finrank k (TensorProduct ↥(⊥ : Subfield k) k W₀) = Module.finrank k Wn)
    (hchar : (Representation.scalarExtension (k := k) ρ₀).character = ρn.character) :
    (Representation.scalarExtension (k := k) ρ₀).IsIrreducible := by
  classical
  -- the intertwiner dimension `ρn → scalarExtension ρ₀` equals `1` in `k`
  have hkey : (Module.finrank k (IntertwiningMap ρn (Representation.scalarExtension (k := k) ρ₀)) : k)
      = 1 := by
    rw [← card_inv_mul_sum_char_mul_char_eq_finrank ρn
          (Representation.scalarExtension (k := k) ρ₀), hchar,
        card_inv_mul_sum_char_mul_char_eq_finrank ρn ρn,
        IsIrreducible.finrank_intertwiningMap_self]
    norm_num
  have hpos : 0 < Module.finrank k (IntertwiningMap ρn (Representation.scalarExtension (k := k) ρ₀)) := by
    rcases Nat.eq_zero_or_pos
        (Module.finrank k (IntertwiningMap ρn (Representation.scalarExtension (k := k) ρ₀)))
      with h0 | h0
    · rw [h0] at hkey; norm_num at hkey
    · exact h0
  -- a nonzero intertwiner
  obtain ⟨f, hf⟩ :
      ∃ f : IntertwiningMap ρn (Representation.scalarExtension (k := k) ρ₀), f ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp hpos
  -- it is injective (`ρn` simple)
  have hkerbot : f.ker = ⊥ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top f.ker with h | h
    · exact h
    · exfalso
      apply hf
      have hzero : ∀ v, f v = 0 := by
        intro v
        have hv : v ∈ f.ker := by rw [h]; trivial
        simpa using hv
      exact DFunLike.ext _ _ fun v ↦ by simpa using hzero v
  have hinj : Function.Injective f.toLinearMap := by
    rw [← LinearMap.ker_eq_bot]
    have := congrArg Subrepresentation.toSubmodule hkerbot
    simpa using this
  -- it is surjective (equal dimensions)
  have hsurj : Function.Surjective f.toLinearMap := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hinj]
    exact hdim.symm
  -- hence an isomorphism, so `scalarExtension ρ₀` is irreducible
  exact isIrreducible_of_equiv_overField (ρ := ρn)
    (σ := Representation.scalarExtension (k := k) ρ₀) (f.ofBijective ⟨hinj, hsurj⟩)

/-- One disjunct of the semisimple branch: given a native model `ρn` over `k` that is the lifted
slot `j` of the family, a prime-field model `ρ₀` whose scalar extension is irreducible and has the
same character as `ρn`, and the matched lift of `ρ`, produce the equivalence `ρ ≅ scalarExtension ρ₀`.

The irreducibility of `scalarExtension ρ₀` is taken as a hypothesis: for the five explicit models it
is their *absolute* irreducibility (true because `S₄` is a rational group), which is the single
remaining atom of the semisimple branch (`scalarExtension_explicit_models_isIrreducible`). -/
theorem finish_branch [IsAlgClosed k] [Invertible (Nat.card S4 : k)]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W₀ : Type u} [AddCommGroup W₀] [Module ↥(⊥ : Subfield k) W₀]
    [FiniteDimensional ↥(⊥ : Subfield k) W₀]
    {Wn : Type u} [AddCommGroup Wn] [Module k Wn] [FiniteDimensional k Wn]
    (ρ : Representation k S4 V) [ρ.IsIrreducible]
    (ρ₀ : Representation ↥(⊥ : Subfield k) S4 W₀)
    (hscIrr : (Representation.scalarExtension (k := k) ρ₀).IsIrreducible)
    (ρn : Representation k S4 Wn) (j : Fin 5)
    (hfam : s4_explicit_family k j = FDRep.of (ulift_group_carrier_representation ρn))
    (hbridge : (Representation.scalarExtension (k := k) ρ₀).character = ρn.character)
    (hcharlift : (FDRep.of (ρ.comp (MulEquiv.ulift.{0, u} : ULift.{u} S4 ≃* S4).toMonoidHom)).character
      = (s4_explicit_family k j).character) :
    Nonempty (ρ.Equiv (Representation.scalarExtension (k := k) ρ₀)) := by
  letI : (Representation.scalarExtension (k := k) ρ₀).IsIrreducible := hscIrr
  have hρn : ρ.character = ρn.character := rho_char_eq_of_lift ρ ρn j hfam hcharlift
  have hρsc : ρ.character = (Representation.scalarExtension (k := k) ρ₀).character := by
    rw [hρn, ← hbridge]
  exact nonempty_equiv_of_char_eq_isIrr ρ (Representation.scalarExtension (k := k) ρ₀) hρsc

end

end Representation
