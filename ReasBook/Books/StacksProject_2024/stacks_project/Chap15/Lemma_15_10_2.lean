import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalProperties.Basic
import StacksProject_2024.stacks_project.Chap10.IdempotentMap
import StacksProject_2024.stacks_project.Chap10.Lemma_10_23_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open LocalizedModule (AtPrime mkLinearMap)

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: commutative-ring idempotents under quotient maps, controlled by the Jacobson
  radical and tested on maximal localizations;
- sampled owner declarations: `RingHom.idempotentMap`, `element_zero_localization_tfae`,
  `Localization.AtPrime.map_eq_maximalIdeal`, `Ring.jacobson_le_of_isMaximal`,
  `IsIdempotentElem.iff_eq_one_of_isUnit`;
- best owner abstraction: the induced map on the canonical idempotent subtype, with maximal
  localization and local-ring unit dichotomy supplying the proof core, and Chapter 10's
  local-to-global owner theorem closing the argument;
- primitive data: the ring homomorphism on elements and the Jacobson-radical containment `I ≤
  Ring.jacobson A`;
- derived API: injectivity of the quotient-induced idempotent map.

Layer triage:
- `source-facing`: injectivity for the quotient map `A → A ⧸ I`;
- `core/canonical`: maximal localization and local-ring Jacobson APIs;
- `bridge/view`: the owner-level map `RingHom.idempotentMap` on the idempotent subtype. -/

private theorem eq_zero_or_one_of_isIdempotentElem
    {R : Type*} [CommRing R] [IsLocalRing R] {x : R} (hx : IsIdempotentElem x) :
    x = 0 ∨ x = 1 := by
  rcases isUnit_or_isUnit_one_sub_self x with hx_unit | hx_unit
  · exact Or.inr <| (IsIdempotentElem.iff_eq_one_of_isUnit hx_unit).mp hx
  · exact Or.inl <| sub_eq_self.mp <|
      (IsIdempotentElem.iff_eq_one_of_isUnit hx_unit).mp hx.one_sub

private theorem eq_of_sub_mem_jacobson_of_isIdempotentElem
    {e₁ e₂ : A} (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (hd : e₁ - e₂ ∈ Ring.jacobson A) : e₁ = e₂ := by
  -- Localize at each maximal ideal and show the difference vanishes there.
  have hlocal :
      ∀ (P : Ideal A) [P.IsMaximal],
        algebraMap A (Localization.AtPrime P) (e₁ - e₂) = 0 := by
    intro P _
    let x₁ : Localization.AtPrime P := algebraMap A (Localization.AtPrime P) e₁
    let x₂ : Localization.AtPrime P := algebraMap A (Localization.AtPrime P) e₂
    have hx₁ : IsIdempotentElem x₁ := by
      simpa [x₁] using he₁.map (algebraMap A (Localization.AtPrime P))
    have hx₂ : IsIdempotentElem x₂ := by
      simpa [x₂] using he₂.map (algebraMap A (Localization.AtPrime P))
    have hsub_mem :
        x₁ - x₂ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      -- Jacobson-radical elements map into every maximal localization ideal.
      have hmap_mem :
          algebraMap A (Localization.AtPrime P) (e₁ - e₂) ∈
            Ideal.map (algebraMap A (Localization.AtPrime P)) (Ring.jacobson A) :=
        Ideal.mem_map_of_mem _ hd
      have hmap_le :
          Ideal.map (algebraMap A (Localization.AtPrime P)) (Ring.jacobson A) ≤
            IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal (R := A) (I := P)]
        exact Ideal.map_mono (Ring.jacobson_le_of_isMaximal P)
      simpa [x₁, x₂, map_sub] using hmap_le hmap_mem
    -- In a local ring, each idempotent is `0` or `1`, so the maximal-ideal condition excludes
    -- the mixed cases.
    rcases eq_zero_or_one_of_isIdempotentElem hx₁ with hx₁_zero | hx₁_one
    · rcases eq_zero_or_one_of_isIdempotentElem hx₂ with hx₂_zero | hx₂_one
      · simpa [x₁, x₂, map_sub, hx₁_zero, hx₂_zero]
      · exfalso
        have hneg_one_mem : (-1 : Localization.AtPrime P) ∈
            IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
          simpa [hx₁_zero, hx₂_one] using hsub_mem
        have hneg_one_unit : IsUnit (-1 : Localization.AtPrime P) := by
          simpa using (isUnit_one.neg : IsUnit (-1 : Localization.AtPrime P))
        have hmax_ne_top :
            (IsLocalRing.maximalIdeal (Localization.AtPrime P) :
              Ideal (Localization.AtPrime P)) ≠ ⊤ :=
          (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime P)).1.1
        exact hmax_ne_top <|
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)).eq_top_of_isUnit_mem
            hneg_one_mem hneg_one_unit
    · rcases eq_zero_or_one_of_isIdempotentElem hx₂ with hx₂_zero | hx₂_one
      · exfalso
        have hone_mem : (1 : Localization.AtPrime P) ∈
            IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
          simpa [hx₁_one, hx₂_zero] using hsub_mem
        have hmax_ne_top :
            (IsLocalRing.maximalIdeal (Localization.AtPrime P) :
              Ideal (Localization.AtPrime P)) ≠ ⊤ :=
          (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime P)).1.1
        exact hmax_ne_top <|
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)).eq_top_of_isUnit_mem
            hone_mem isUnit_one
      · simpa [x₁, x₂, map_sub, hx₁_one, hx₂_one]
  -- The local vanishing criterion now identifies the two elements globally.
  have hzero : e₁ - e₂ = 0 := by
    exact Module.eq_zero_of_localization_maximal
      (Mₚ := fun P _ ↦ Localization.AtPrime P)
      (f := fun P _ ↦ Algebra.linearMap A (Localization.AtPrime P))
      (e₁ - e₂) hlocal
  exact sub_eq_zero.mp hzero

-- Proof sketch: if two idempotents of `A` have the same image in `A ⧸ I`, then their difference
-- lies in `I`, hence in the Jacobson radical by hypothesis. By Lemma
-- `10.23.1`, an idempotent is determined by the maximal ideals where it vanishes, so two
-- idempotents differing by a Jacobson-radical element must coincide.
/-- Lemma 15.10.2: if `(A, I)` is a Zariski pair, then the canonical map `A → A ⧸ I` induces an
injective map from idempotents of `A` to idempotents of `A ⧸ I`. -/
theorem quotientMk_injective_on_idempotents_of_le_jacobson (I : Ideal A)
    (hI : I ≤ Ring.jacobson A) :
    Function.Injective (Ideal.Quotient.mk I).idempotentMap := by
  intro e₁ e₂ h
  apply Subtype.ext
  apply eq_of_sub_mem_jacobson_of_isIdempotentElem e₁.2 e₂.2
  exact hI <| by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [map_sub] using sub_eq_zero.mpr (congrArg Subtype.val h)

end
