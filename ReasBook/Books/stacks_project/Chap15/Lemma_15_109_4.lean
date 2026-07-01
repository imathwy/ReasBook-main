import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsNoetherianRing A]
variable [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
variable [CommRing C] [Algebra A C]

variable (I : Ideal A)

local notation "Bhat" => AdicCompletion (Ideal.map (algebraMap A B) I) B

/- Domain-style sampling for Lemma 15.109.4:
- primary domain: algebraization of quotients of adic completions of finite type algebras under
  conormal control by the cotangent module of the kernel;
- sampled owner declarations:
  `AdicCompletion`,
  `Algebra.FiniteType`,
  `Ideal.Cotangent`,
  `exists_quotient_factor_of_localizationAway_idempotent_on_fg_ideal`;
- best owner abstraction: the source-facing theorem should stay on the canonical owners
  `AdicCompletion (Ideal.map (algebraMap A B) I) B`, `Algebra.FiniteType A _`, and
  `(RingHom.ker φ).Cotangent`; the local quotient-factor statement from Lemma `15.109.3` is only a
  bridge step in the proof, not a second public owner here;
- primitive data: the finite type `A`-algebra `B`, the completion surjection `φ : Bhat →ₐ[A] C`,
  and the annihilation condition on the kernel cotangent module;
- derived API: existence of a finite type `A`-algebra whose `I`-adic completion is `A`-algebra
  isomorphic to `C`.

Source/core/bridge triage:
- `source-facing`: the algebraization existence theorem below;
- `core/canonical`: `AdicCompletion`, `Algebra.FiniteType`, and `Ideal.Cotangent`;
- `bridge/view`: Lemma `15.109.3` and the idempotent-splitting argument used in the proof sketch. -/

-- Proof sketch: apply Lemma `15.109.3` to complement the local idempotent factor defined by the
-- surjection `Bhat → C`, glue the resulting finite algebra over `B`, then use henselian lifting of
-- idempotents after an étale neighborhood to split the finite algebra into two factors whose
-- `I`-adic completions are `C` and its complement.
/-- Lemma 15.109.4: let `A` be a Noetherian ring, `I` an ideal of `A`, and `B` a finite type
`A`-algebra. If `φ : Bhat →ₐ[A] C` is a surjective `A`-algebra map from the `I`-adic completion
`Bhat` of `B`, and if a power `I ^ c` annihilates the conormal module
`(RingHom.ker φ).Cotangent = J / J^2` of its kernel, then `C` is `A`-algebra isomorphic to the
`I`-adic completion of some finite type `A`-algebra. -/
theorem exists_finiteType_algebra_with_completion_algEquiv_of_kernelCotangent_annihilated
    (φ : Bhat →ₐ[A] C) (hφ : Function.Surjective φ) (c : ℕ)
    (hker :
      Ideal.map (algebraMap A Bhat) (I ^ c) ≤
        Module.annihilator Bhat (RingHom.ker φ).Cotangent) :
    ∃ (D : Type x) (_ : CommRing D) (_ : Algebra A D) (_ : Algebra.FiniteType A D),
      Nonempty (AdicCompletion (Ideal.map (algebraMap A D) I) D ≃ₐ[A] C) := sorry

end
