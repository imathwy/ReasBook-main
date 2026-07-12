import Mathlib
import StacksProject_2024.Chap10.Lemma_10_97_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing Ideal AdicCompletion
open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Algebra.FiniteType R S]
variable (q : Ideal S) [q.IsPrime]
variable [Algebra.QuasiFiniteAt R q]

local notation "R_qR" => Localization.AtPrime (q.under R)
local notation "S_q" => Localization.AtPrime q
local notation "R_qR^" => AdicCompletion (maximalIdeal R_qR) R_qR
local notation "S_q^" => AdicCompletion (maximalIdeal S_q) S_q

noncomputable local instance completedLocalRingAlgebra : Algebra R_qR^ S_q^ :=
  (maximalIdealCompletionMap
    (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)).toAlgebra

/- Domain triage:
* primary domain: quasi-finite finite-type algebras at a chosen prime, reduced by Zariski's Main
  Theorem to the finite case and then analyzed by completed tensor-product decomposition;
* sampled owner declarations:
  `Ideal.under`,
  `Algebra.QuasiFiniteAt`,
  `Localization.localRingHom`,
  `maximalIdealCompletionMap`,
  `exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties`,
  `completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion`,
  `RingEquiv.piEquivPiSubtypeProd`;
* best owner abstraction: the finite-case completion/product decomposition is owned upstream by
  `completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion`, while the present item
  stays `source-facing`: quasi-finiteness at the chosen prime `q` produces some complementary
  factor after reducing to that finite owner case;
* primitive data: the algebra `R → S`, the target prime `q`, its canonical base prime
  `q.under R`, and the local quasi-finite owner `Algebra.QuasiFiniteAt R q`;
* derived API: the canonical completed-local-ring comparison carried directly by
  `maximalIdealCompletionMap (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)` and
  the resulting source-facing splitting of `R_qR^ ⊗[R] S` into the distinguished factor `S_q^`
  and a complementary `R_qR^`-algebra. The complementary factor is genuinely non-canonical before
  the Zariski-main reduction, so only that factor remains existential; the distinguished
  projection should be recorded explicitly instead of hidden inside `Nonempty`.
-/

-- Proof sketch: use Lemma `10.123.14` to replace the quasi-finite finite-type algebra by a finite
-- subalgebra with the same localization at `q`, apply Lemma `10.97.8` to that finite algebra
-- after base change to the completion of `R_(q∩R)`, and identify the factor cut out by `q` with
-- `S_q^` because the chosen element becomes a unit in that factor; then split off the distinguished
-- `q`-factor and record that its projection agrees with the canonical maps from `R_(q∩R)^` and
-- `S`.
/-- Lemma 10.124.3: if `R → S` is finite type, `R` is Noetherian, and `q` is a prime of `S`
such that `R → S` is quasi-finite at `q`, then the completed base change
`R_(q∩R)^∧ ⊗[R] S` splits, as an `R_(q∩R)^∧`-algebra, as the product of the completed local ring
`S_q^∧` and another factor; moreover the first projection restricts to the canonical
completed-local-ring
map on `R_(q∩R)^∧` and to the localization-completion map on `S`. -/
theorem exists_completionTensorProduct_algEquiv_completedLocalRing_prod :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R_qR^ B)
      (e : (R_qR^ ⊗[R] S) ≃ₐ[R_qR^] (S_q^ × B)),
      (∀ x : R_qR^,
        (RingHom.fst S_q^ B) (e (x ⊗ₜ[R] 1)) =
          maximalIdealCompletionMap
            (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) x) ∧
      ∀ s : S,
        (RingHom.fst S_q^ B) (e (1 ⊗ₜ[R] s)) = algebraMap S S_q^ s := by
  sorry

end
