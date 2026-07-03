import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_124_1 (from Chap10) -/
noncomputable section

open scoped BigOperators
open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]
variable [FiniteDimensional (FractionRing A) (FractionRing B)]

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

/- Domain-style sampling:
- primary domain: one-dimensional Noetherian local domains, local orders of vanishing, and the
  residue-field-degree weighted sum over maximal localizations of a finite-type algebra with finite
  fraction-field extension;
- sampled owner declarations:
  `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`,
  `Ring.ordFrac`,
  `Ring.ordFrac_eq_ord`,
  `ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac`,
  `Module.Finite`;
- best owner abstraction: `Ring.ordFrac` is the canonical valuation owner, and
  `ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac` is the chapter owner for the weighted
  maximal-spectrum sum, while
  `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension` is the owner for the
  semilocality conclusion; this file should expose only the source-facing ring-level
  reformulations in terms of `Ring.ord`, not a parallel public owner for that sum;
- source/core/bridge triage:
  `source-facing`: the semilocality conclusion for `B`, together with the textbook inequality and
    equality criterion for the weighted sum of local orders of an element `x : A`;
  `core/canonical`: `Ring.ordFrac`, `Module.finrank`, and the chapter theorem
    `ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac`, together with the semilocality
    owner `finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`;
  `bridge/view`: `Ring.ordFrac_eq_ord` translates the fraction-field owner to the ring-level local
    orders that appear in the source statement;
- primitive data: the algebra tower and the chosen element `x : A`;
- derived API: finiteness of `MaximalSpectrum B`, the induced residue-field extensions, and the
  canonical weighted maximal-spectrum sum.
-/

/- Lemma 10.124.1 first asserts that `B` is semilocal. This is exactly the chapter owner theorem
`finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension`. -/
recall finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension

-- Proof sketch: let `B'` be the integral closure of `A` in `B`, choose the finite intermediate
-- `A`-subalgebra `C ⊂ B'` supplied by Lemma `10.123.14`, and apply Lemma `10.121.8` to `C`. The
-- localizations of `C` at the primes lying under the maximal ideals of `B` agree with the
-- corresponding localizations of `B`, while the extra maximal ideals of `C` contribute a
-- nonnegative remainder term, giving the inequality. The source-facing hypotheses
-- `x ∈ maximalIdeal A` and `x ≠ 0` are not part of this canonical inequality statement; they
-- appear only in the later equality criterion.
/-- The weighted sum of local orders of `x` over the maximal ideals of `B` is bounded above by the
fraction-field degree times its order on `A`. -/
theorem sum_residueFieldDegree_mul_local_ord_le_fractionFieldDegree_mul_ord
    (x : A) :
    (let _ : Finite (MaximalSpectrum B) :=
      finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
    let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
    ∑ m : MaximalSpectrum B,
      (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) x)) ≤
      (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x := by
  sorry

-- Proof sketch: the inequality above comes from the finite intermediate subalgebra `C`. Equality
-- holds exactly when there are no extra maximal ideals of `C` beyond those coming from maximal
-- ideals of `B`; then `C → B` induces a bijection on maximal ideals and is an isomorphism after
-- localizing at each maximal ideal, forcing `B = C`, hence `B` is finite over `A`. Conversely, if
-- `A → B` is finite, the equality is exactly Lemma `10.121.8` applied to `B`. The source-facing
-- hypotheses are the primitive conditions `x ∈ maximalIdeal A` and `x ≠ 0`, rather than the
-- derived inequalities `0 < Ring.ord A x` and `Ring.ord A x < ⊤`.
/-- Lemma 10.124.1: for a finite-type extension of domains `A ⊂ B` with `A` a one-dimensional
Noetherian local domain and finite fraction-field extension, once the semilocality conclusion for
`B` is recalled above, equality between the global order term `[Frac(B) : Frac(A)] ord_A(x)` and
the weighted sum of local orders over the maximal ideals of `B` holds exactly when `A → B` is
finite, for `x ∈ maximalIdeal A` nonzero. -/
theorem sum_residueFieldDegree_mul_local_ord_eq_fractionFieldDegree_mul_ord_iff_moduleFinite
    (x : A) (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0) :
    (let _ : Finite (MaximalSpectrum B) :=
      finite_maximalSpectrum_of_finiteType_of_finiteFractionRingExtension A
    let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
    ∑ m : MaximalSpectrum B,
      (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℕ∞) *
        Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) x)) =
      (Module.finrank (FractionRing A) (FractionRing B) : ℕ∞) * Ring.ord A x ↔
      Module.Finite A B := by
  sorry

end

/-! ### Lemma_10_124_2 (from Chap10) -/
open IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [Algebra.EssFiniteType R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/-
Domain-style sampling:
- primary domain: local quasi-finite algebra maps and Zariski-main finiteness over local rings;
- sampled owner declarations:
  `Ideal.Fiber`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.EssFiniteType`,
  `Algebra.EssFiniteType.essFiniteType_iff_exists_subalgebra`,
  `exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties`;
- best owner abstraction: the closed fiber is the canonical owner `Ideal.Fiber`, and the decisive
  local finiteness condition is the owner predicate `Algebra.QuasiFiniteAt R (maximalIdeal S)`,
  while the source-facing finite-localization conclusion is organized through `Subalgebra R S`
  together with `IsLocalization`;
- source/core/bridge triage:
  `source-facing`: the existence of a finite `R`-subalgebra of `S` whose localization is `S`;
  `core/canonical`: `Ideal.Fiber`, `Algebra.QuasiFiniteAt`, `Algebra.EssFiniteType`,
    `Subalgebra R S`, and `IsLocalization`;
  `bridge/view`: the local closed-fiber hypotheses imply the canonical quasi-finite owner at
  `maximalIdeal S`, which then feeds the Zariski-main finite-localization argument;
- primitive data: the local map, the essentially finite type owner, the finite residue-field
  extension `ResidueField R → ResidueField S`, and the canonical closed fiber `ClosedFiber`;
- derived API: quasi-finiteness at `maximalIdeal S` and the resulting finite-subalgebra
  localization witness.
-/

/-- The local source hypotheses, including the finite residue-field extension
`ResidueField R → ResidueField S`, make `R → S` quasi-finite at the maximal ideal of `S`. -/
-- Proof sketch: write `S` as a localization of the canonical finite-type subalgebra supplied by
-- `Algebra.EssFiniteType`. Because `ClosedFiber` is a finite-type `ResidueField R`-algebra,
-- the hypothesis `hκ` and `ringKrullDim ClosedFiber = 0` match clause `(6)` of the isolated-point
-- criterion from Lemmas `10.122.1` and `10.122.4` for the unique point of the local closed fiber,
-- which is exactly the owner predicate `Algebra.QuasiFiniteAt R (maximalIdeal S)`.
theorem quasiFiniteAt_maximalIdeal_of_closedFiber_dimZero
    (hκ : Module.Finite (ResidueField R) (ResidueField S))
    (hdim : ringKrullDim ClosedFiber = 0) :
    Algebra.QuasiFiniteAt R (maximalIdeal S) := sorry

/-- Lemma 10.124.2: if `R → S` is a local homomorphism of local rings, `S` is essentially of
finite type over `R`, and the canonical closed fiber `ClosedFiber = κ(R) ⊗[R] S`, equivalently
`S ⧸ maximalIdeal R • S`, has Krull dimension zero, and the induced residue-field extension
`ResidueField R → ResidueField S` is finite, then `S` is the localization of a finite
`R`-subalgebra of `S`. -/
-- Proof sketch: first apply the previous theorem to obtain the canonical owner
-- `Algebra.QuasiFiniteAt R (maximalIdeal S)`. Present `S` by the canonical finite-type
-- subalgebra coming from `Algebra.EssFiniteType`, use Lemma `10.123.13` to shrink to a basic open
-- neighborhood on which the map is quasi-finite, and then apply Lemma `10.123.14` to replace
-- that neighborhood by the localization of a finite `R`-subalgebra of `S`.
theorem exists_finite_algebra_localization_of_essFiniteType_of_closedFiber_dimZero
    (hκ : Module.Finite (ResidueField R) (ResidueField S))
    (hdim : ringKrullDim ClosedFiber = 0) :
    ∃ (A : Subalgebra R S) (M : Submonoid A),
      Module.Finite R A ∧ IsLocalization M S := sorry

end

/-! ### Lemma_10_124_3 (from Chap10) -/
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
