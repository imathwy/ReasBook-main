import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum

section

variable {R : Type u} [CommRing R]

namespace Ideal

/- Domain-style sampling:
* primary domain: commutative algebra of pure ideals and the localization at `1 + I`;
* sampled owner declarations:
  `Ideal.Pure`,
  `Ideal.inf_eq_mul_of_pure`,
  `Ideal.Pure.of_inf_eq_mul`,
  `Ideal.exists_eq_mul_of_pure`;
* best owner abstraction: the chapter item is source-facing `TFAE` data for the canonical owner
  `Ideal.Pure I`;
* layer triage:
  - `source-facing`: the Stacks equivalence package for a fixed ideal `I`;
  - `core/canonical`: the mathlib owner `Ideal.Pure` and its canonical derived lemmas;
  - `bridge/view`: the source-facing localization submonoid `1 + I`, implemented by the local
    owner `Ideal.oneAdd`;
* primitive data: the ideal `I` and the source-facing submonoid `1 + I`;
* derived API: the inf-equals-product criteria, the pointwise idempotence criterion, the local
  prime-support criterion, and the quotient/localization formulations.
-/

-- Proof sketch: write `a = 1 + x` and `b = 1 + y` with `x, y ∈ I`; then
-- `(1 + x) * (1 + y) = 1 + (x + y + x * y)` and the parenthesized term lies in `I` because `I`
-- is closed under addition and multiplication by ring elements.
/-- If `a` and `b` are of the form `1 + i` with `i ∈ I`, then so is `a * b`. -/
private theorem exists_mem_and_eq_one_add_of_mul {I : Ideal R} (a b : R)
    (ha : ∃ x ∈ I, a = 1 + x) (hb : ∃ y ∈ I, b = 1 + y) :
    ∃ z ∈ I, a * b = 1 + z := by
  rcases ha with ⟨x, hx, rfl⟩
  rcases hb with ⟨y, hy, rfl⟩
  refine ⟨x + y + x * y, I.add_mem (I.add_mem hx hy) (I.mul_mem_right y hx), ?_⟩
  ring

/-- The multiplicative subset `1 + I` associated to the ideal `I`. -/
def oneAdd (I : Ideal R) : Submonoid R where
  carrier := { x : R | ∃ y ∈ I, x = 1 + y }
  one_mem' := ⟨0, I.zero_mem, (add_zero 1).symm⟩
  mul_mem' := fun {a b} ha hb ↦
    show a * b ∈ { x : R | ∃ y ∈ I, x = 1 + y } from
      exists_mem_and_eq_one_add_of_mul a b ha hb

/-
Lean cannot export the raw textbook notation `1 + I` as an ordinary parser notation here without
capturing genuine ring expressions `1 + x`, so the source-facing multiplicative subset is exposed
through the short owner `Ideal.oneAdd`.
-/

-- Proof sketch: this is immediate from the definition of `Ideal.oneAdd`.
/-- Membership in `1 + I` means being congruent to `1` modulo `I`. -/
@[simp] theorem mem_oneAdd_iff {I : Ideal R} {x : R} :
    x ∈ I.oneAdd ↔ ∃ y ∈ I, x = 1 + y := by
  simp [oneAdd]

-- Proof sketch: combine the flatness criterion for pure ideals from Lemma `10.39.5` with the
-- canonical statements in `Mathlib/RingTheory/Ideal/Pure.lean`. The implications between the
-- finite-family, localization, support, kernel, and localization-quotient formulations follow the
-- Stacks proof by comparing `I` with its localizations and the localization at the multiplicative
-- subset `1 + I`.
/-- Lemma 10.108.2: for an ideal `I` of a commutative ring `R`, the following are equivalent:
`I` is pure; intersections with `I` agree with ideal products for all ideals, for finitely
generated ideals, and for principal ideals; each element or finite family of elements of `I` is
fixed by multiplication by some element of `I`; every localization of `I` at a prime is either
zero or the unit ideal; `Supp(I) = Spec(R) \ V(I)`; `I` is the kernel of the map
`R → (1 + I)⁻¹R`; `R ⧸ I` is isomorphic to a localization of `R`; and specifically
`R ⧸ I ≃ (1 + I)⁻¹R` as `R`-algebras. Clauses `(2)`, `(3)`, `(4)`, and `(5)` are stated in the
same canonical orientation as the owner lemmas
`Ideal.inf_eq_mul_of_pure`, `Ideal.Pure.of_inf_eq_mul`, and `Ideal.exists_eq_mul_of_pure`. -/
theorem pure_tfae (I : Ideal R) :
    List.TFAE
      [ I.Pure
      , ∀ J : Ideal R, I ⊓ J = I * J
      , ∀ ⦃J : Ideal R⦄, J.FG → I ⊓ J = I * J
      , ∀ x : R, I ⊓ Ideal.span ({x} : Set R) = I * Ideal.span ({x} : Set R)
      , ∀ x : R, x ∈ I → ∃ y ∈ I, x = x * y
      , ∀ s : Finset R, (∀ x ∈ s, x ∈ I) → ∃ y ∈ I, ∀ x ∈ s, x = x * y
      , ∀ p : PrimeSpectrum R,
          Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I = ⊥ ∨
            Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I = ⊤
      , Module.support R I = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ
      , RingHom.ker (algebraMap R (Localization I.oneAdd)) = I
      , ∃ S : Submonoid R, Nonempty ((R ⧸ I) ≃ₐ[R] Localization S)
      , Nonempty ((R ⧸ I) ≃ₐ[R] Localization I.oneAdd)
      ] := sorry

end Ideal

end
