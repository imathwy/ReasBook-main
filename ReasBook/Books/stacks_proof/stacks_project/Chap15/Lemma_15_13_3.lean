import StacksProject_2024.Chap15.Lemma_15_11_6
import StacksProject_2024.Chap15.Lemma_15_9_14
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v} {A : Type v}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A]

/-
Domain-style sampling:
- primary domain: lifting maps from smooth algebras over a quotient along the henselian étale
  section property;
- sampled owner declarations:
  `Algebra.Smooth.baseChange`,
  `exists_etale_lift_to_quotient_of_smooth`,
  `Ideal.HasEtaleLiftProperty`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`;
- best owner abstraction: the primitive lifting input is the Chapter 15 owner
  `Ideal.HasEtaleLiftProperty`; the henselian hypothesis is derived API here via the chapter TFAE,
  while smoothness is still owned canonically by `Algebra.Smooth`;
- primitive data: the ideal `I`, the smooth `R`-algebra `S`, the quotient map
  `f : S →ₐ[R] A ⧸ I`, and the étale-section owner `I.HasEtaleLiftProperty`;
- derived API: the source-facing henselian corollary obtained by extracting
  `I.HasEtaleLiftProperty` from `HenselianRing A I`.

Source/core/bridge triage:
- `source-facing`: `smooth_exists_lift_of_henselianRing`;
- `core/canonical`: `Algebra.Smooth` and `Ideal.HasEtaleLiftProperty`;
- `bridge/view`: the corollary from `HenselianRing A I` via
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`.
-/

-- Proof sketch: base change `S` from `R` to `A` to obtain the smooth `A`-algebra `S ⊗[R] A`.
-- Apply the étale lifting statement for smooth algebras modulo `I` to the induced map
-- `S ⊗[R] A → A ⧸ I`, then use the henselian lifting property for étale `A`-algebras to get a
-- section back to `A`. Precompose the resulting composite with `TensorProduct.includeLeft` to
-- obtain the desired lift `S →ₐ[R] A`. The core input used from the target pair is exactly the
-- chapter owner `I.HasEtaleLiftProperty`.
/-- Helper for Lemma 15.13.3: the tensor-product map induced by the quotient map on `A` and the
given map `f : S → A ⧸ I` is compatible with the `A`-algebra structure on `A ⊗[R] S`. -/
private theorem tensor_baseChange_to_quotient_commutes (I : Ideal A)
    (f : S →ₐ[R] A ⧸ I) :
    ∀ a : A,
      (Algebra.TensorProduct.productMap (Ideal.Quotient.mkₐ R I) f)
          ((algebraMap A (A ⊗[R] S)) a) =
        algebraMap A (A ⧸ I) a := by
  -- Proof comment: the left tensor factor is the canonical `A`-algebra structure on the base
  -- change, so the product map restricts to the quotient map on that factor.
  intro a
  simp [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.includeLeft_apply]

/-- Helper for Lemma 15.13.3: the induced map on the smooth base change
`A ⊗[R] S → A ⧸ I`. -/
private def tensor_baseChange_to_quotient (I : Ideal A)
    (f : S →ₐ[R] A ⧸ I) :
    A ⊗[R] S →ₐ[A] A ⧸ I :=
  { toRingHom := (Algebra.TensorProduct.productMap (Ideal.Quotient.mkₐ R I) f).toRingHom
    commutes' := tensor_baseChange_to_quotient_commutes (R := R) (S := S) (A := A) I f }

/-- Helper for Lemma 15.13.3: restricting the base-changed quotient map along `includeRight`
recovers the original map `f : S → A ⧸ I`. -/
private theorem tensor_baseChange_to_quotient_comp_includeRight_eq (I : Ideal A)
    (f : S →ₐ[R] A ⧸ I) :
    ((tensor_baseChange_to_quotient (R := R) (S := S) (A := A) I f).restrictScalars R).comp
        (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) =
      f := by
  -- Proof comment: `includeRight` inserts `s` as `1 ⊗ s`, and the product map sends that tensor
  -- generator to `f s`.
  ext s
  simp [tensor_baseChange_to_quotient, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.productMap_apply_tmul]

/-- If `S` is a smooth `R`-algebra and reduction modulo `I` on `A` has the étale section lifting
property, then every `R`-algebra map `S → A ⧸ I` lifts to an `R`-algebra map `S → A`. -/
theorem smooth_exists_lift_of_hasEtaleLiftProperty (I : Ideal A) [Algebra.Smooth R S]
    (hI : I.HasEtaleLiftProperty) (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := by
  let T : Type v := A ⊗[R] S
  let _ : CommRing T := inferInstance
  let _ : Algebra A T := inferInstance
  let _ : Algebra.Smooth A T := inferInstance
  let φT : T →ₐ[A] A ⧸ I :=
    tensor_baseChange_to_quotient (R := R) (S := S) (A := A) I f
  -- Proof comment: smoothness of the base change gives an étale neighborhood over `A` lifting the
  -- quotient map `φT`.
  obtain ⟨A', _, _, _, eIso, φ', hφ'⟩ :=
    exists_etale_lift_to_quotient_of_smooth (A := A) (B := T) I φT
  let I' : Ideal A' := Ideal.map (algebraMap A A') I
  let g : A' →ₐ[A] A ⧸ I :=
    (eIso.symm.toAlgHom.restrictScalars A).comp (Ideal.Quotient.mkₐ A' I')
  -- Proof comment: the henselian input gives a section of this étale `A`-algebra map back to `A`.
  obtain ⟨σ, hσ⟩ := hI (A' := A') g
  have hdescend :
      ((Ideal.Quotient.mkₐ A I).comp σ).comp φ' = φT := by
    -- Proof comment: compare the two quotient maps to `A ⧸ I`, then cancel the quotient
    -- equivalence `eIso`.
    calc
      ((Ideal.Quotient.mkₐ A I).comp σ).comp φ'
          = g.comp φ' := by
              rw [hσ]
      _ = (eIso.symm.toAlgHom.restrictScalars A).comp
            (((Ideal.Quotient.mkₐ A' I').restrictScalars A).comp φ') := by
              rw [AlgHom.comp_assoc]
      _ = (eIso.symm.toAlgHom.restrictScalars A).comp
            ((eIso.toAlgHom.restrictScalars A).comp φT) := by
              rw [hφ']
      _ = ((eIso.symm.toAlgHom.restrictScalars A).comp
            (eIso.toAlgHom.restrictScalars A)).comp φT := by
              rw [AlgHom.comp_assoc]
      _ = φT := by
              simp
  have hdescendR :
      (((((Ideal.Quotient.mkₐ A I).comp σ).comp φ').restrictScalars R)) =
        φT.restrictScalars R := by
    -- Proof comment: the quotient comparison is an `A`-algebra identity, so it remains valid
    -- after forgetting to `R`.
    exact congrArg (fun ψ : T →ₐ[A] A ⧸ I ↦ ψ.restrictScalars R) hdescend
  refine
    ⟨(σ.restrictScalars R).comp
        ((φ'.restrictScalars R).comp
          (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S)),
      ?_⟩
  -- Proof comment: compose the lifted map on the smooth base change with the henselian section and
  -- then restrict back to `S` through the right tensor inclusion.
  calc
    (Ideal.Quotient.mkₐ R I).comp
        ((σ.restrictScalars R).comp
          ((φ'.restrictScalars R).comp
            (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S)))
        = (((((Ideal.Quotient.mkₐ A I).comp σ).comp φ').restrictScalars R)).comp
            (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) := by
              rfl
    _ = (φT.restrictScalars R).comp
          (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) := by
            rw [hdescendR]
    _ = f := by
            simpa [φT] using
              tensor_baseChange_to_quotient_comp_includeRight_eq
                (R := R) (S := S) (A := A) I f

/-- Lemma 15.13.3: if `S` is a smooth `R`-algebra, `A` is an `R`-algebra, and `(A, I)` is a
henselian pair, then every `R`-algebra map `S → A ⧸ I` lifts to an `R`-algebra map `S → A`. -/
@[stacks 0H74]
theorem smooth_exists_lift_of_henselianRing (I : Ideal A) [Algebra.Smooth R S]
    [HenselianRing A I] (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := by
  -- This is the `HenselianRing A I → I.HasEtaleLiftProperty` bridge from
  -- `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`.
  have hI : I.HasEtaleLiftProperty := by
    let Q : Ideal A → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{v, v}
    let P : Ideal A → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{v, v}
    let T (J : Ideal A) : List Prop :=
      [ HenselianRing A J
      , J.HasEtaleLiftProperty
      , Q J
      , P J
      , J.SatisfiesGabberRootCriterion
      ]
    have hTfae : List.TFAE (T I) := by
      -- Proof comment: package the chapter theorem in the local five-clause list notation.
      simpa [T, Q, P] using
        Ideal.henselianRing_tfae_etaleLift_idempotents_gabberCriterion (A := A) I
    have hiff : HenselianRing A I ↔ I.HasEtaleLiftProperty := by
      -- Proof comment: clause `(1) ↔ (2)` is the exact bridge needed here.
      simpa [T] using hTfae.out 0 1
    exact hiff.mp inferInstance
  exact smooth_exists_lift_of_hasEtaleLiftProperty I hI f

end

end Algebra
