import stacks_proof.stacks_project.Chap15.Lemma_15_9_14
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
* sampled owner declarations:
  `exists_etale_lift_to_quotient_of_smooth`,
  `IsIdempotentElem`,
  `Ideal.Quotient.mk`;
* `source-facing`: the étale-local lifting statement for one idempotent in `A ⧸ I`;
* `core/canonical`: the smooth lifting owner `exists_etale_lift_to_quotient_of_smooth`;
* `bridge/view`: this theorem is the idempotent-specialized consequence obtained from that owner
  by applying it to the standard smooth algebra carrying a universal idempotent section.

Primitive data: the quotient idempotent `ebar`.
Derived API: the quotient isomorphism `eIso` and the lifted idempotent `e'`.

To match the surrounding Chapter 15 owner surface, the quotient isomorphism is exposed as a primary
binder, not hidden inside a trailing nested existential after `e'`.
-/

-- Proof sketch: apply the smooth lifting owner theorem `exists_etale_lift_to_quotient_of_smooth`
-- to the standard smooth `A`-algebra representing an idempotent section reducing to `ebar`. The
-- resulting étale algebra `A'`, quotient isomorphism `eIso`, and lifted section `e'` give the
-- desired idempotent lift.
/-- Helper for Lemma 15.9.2: the polynomial `X^2 - X` is monic. -/
lemma idempotent_polynomial_monic :
    (((Polynomial.X : Polynomial A) ^ 2) - Polynomial.X).Monic := by
  -- The universal idempotent polynomial is monic because its lower-degree term is `X`.
  simpa using
    (Polynomial.monic_X_pow_sub (R := A) (p := (Polynomial.X : Polynomial A)) (n := 2) (by
      exact lt_of_le_of_lt (Polynomial.degree_X_le (R := A))
        (by decide)))

/-- Helper for Lemma 15.9.2: `X^2 - X` and `1` satisfy the standard-étale Bezout relation. -/
lemma idempotent_standard_etale_relation :
    ∃ p₁ p₂ : Polynomial A, ∃ n : ℕ,
      Polynomial.derivative ((((Polynomial.X : Polynomial A) ^ 2) - Polynomial.X)) * p₁ +
          ((((Polynomial.X : Polynomial A) ^ 2) - Polynomial.X) * p₂) =
            (1 : Polynomial A) ^ n := by
  have hder :
      Polynomial.derivative ((((Polynomial.X : Polynomial A) ^ 2) - Polynomial.X)) =
        Polynomial.X + Polynomial.X - 1 := by
    -- The derivative of `X^2 - X` is `2X - 1`.
    simp [pow_two]
  refine
    ⟨Polynomial.derivative ((((Polynomial.X : Polynomial A) ^ 2) - Polynomial.X)),
      (-4 : Polynomial A), 0, ?_⟩
  -- Expanding the derivative reduces the Bezout identity to a polynomial ring computation.
  rw [hder]
  ring

/-- Helper for Lemma 15.9.2: the standard-étale algebra with universal idempotent generator. -/
noncomputable def idempotent_standard_etale_pair (A : Type u) [CommRing A] : StandardEtalePair A :=
  { f := ((Polynomial.X : Polynomial A) ^ 2) - Polynomial.X
    monic_f := idempotent_polynomial_monic (A := A)
    g := 1
    cond := idempotent_standard_etale_relation (A := A) }

/-- Helper for Lemma 15.9.2: an idempotent in `A ⧸ I` defines a map from the universal
idempotent standard-étale algebra. -/
lemma universal_idempotent_hasMap (I : Ideal A) (ebar : A ⧸ I) (hebar : IsIdempotentElem ebar) :
    (idempotent_standard_etale_pair A).HasMap ebar := by
  constructor
  · -- Evaluating `X^2 - X` at `ebar` is exactly the idempotence equation.
    change Polynomial.aeval ebar ((((Polynomial.X : Polynomial A) ^ 2) - Polynomial.X)) = 0
    simpa [pow_two] using (sub_eq_zero.mpr hebar.eq)
  · -- The auxiliary polynomial is `1`, so its value is automatically a unit.
    change IsUnit (Polynomial.aeval ebar (1 : Polynomial A))
    simpa using (show IsUnit (1 : A ⧸ I) from isUnit_one)

/-- Helper for Lemma 15.9.2: the universal generator in the standard-étale pair is idempotent. -/
lemma universal_idempotent_generator_is_idempotent :
    IsIdempotentElem (idempotent_standard_etale_pair A).X := by
  -- The defining polynomial relation for the universal generator is `X^2 - X = 0`.
  have hroot :
      Polynomial.aeval (idempotent_standard_etale_pair A).X
        ((((Polynomial.X : Polynomial A) ^ 2) - Polynomial.X)) = 0 := by
    simpa [idempotent_standard_etale_pair] using
      (idempotent_standard_etale_pair A).hasMap_X.1
  simpa [sub_eq_zero, pow_two, IsIdempotentElem] using hroot

/-- Lemma 15.9.2: for an idempotent `ebar` in the quotient ring `A ⧸ I`, there exists an étale
`A`-algebra `A'` whose reduction modulo `I` is canonically isomorphic to `A ⧸ I`, together with an
idempotent `e' ∈ A'` mapping to `ebar` under that isomorphism. -/
@[stacks 07LY]
theorem exists_etale_idempotent_lift_of_quotient (I : Ideal A) (ebar : A ⧸ I)
    (hebar : IsIdempotentElem ebar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I)) (e' : A'),
      IsIdempotentElem e' ∧
        eIso ebar = Ideal.Quotient.mk (Ideal.map (algebraMap A A') I) e' := by
  let P : StandardEtalePair A := idempotent_standard_etale_pair A
  have hHasMap : P.HasMap ebar := by
    -- The quotient idempotent gives the source map into the smooth lifting theorem.
    simpa [P] using universal_idempotent_hasMap (A := A) I ebar hebar
  let φ : P.Ring →ₐ[A] A ⧸ I := P.lift ebar hHasMap
  -- Apply the smooth lifting theorem to the universal idempotent algebra.
  obtain ⟨A', hA', hAlg, hEt, eIso, φ', hcomp⟩ :=
    exists_etale_lift_to_quotient_of_smooth (A := A) (B := P.Ring) I φ
  refine ⟨A', hA', hAlg, hEt, eIso, φ' P.X, ?_⟩
  constructor
  · -- Idempotence is preserved under the lifted algebra map.
    simpa [P] using (universal_idempotent_generator_is_idempotent (A := A)).map φ'
  · -- Evaluating the compatibility equality at the universal generator recovers the quotient lift.
    have happly := congrArg (fun f => f P.X) hcomp
    simpa [P, φ, Ideal.Quotient.mkₐ_eq_mk] using happly.symm

end

end Algebra
