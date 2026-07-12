import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_150_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {S' : Type w} [CommRing S'] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']

/- Domain-style sampling:
- primary domain: Kähler differentials, diagonal ideals in tensor products, and formally étale
  base change for quotient thickenings;
- sampled owner declarations:
  `KaehlerDifferential.ideal`,
  `KaehlerDifferential.mapBaseChange`,
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`,
  `Algebra.TensorProduct.map`;
- best owner abstraction:
  the canonical owner for part (2) is the linear equivalence
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'`; its underlying linear map is
  `KaehlerDifferential.mapBaseChange R S S'`, so bare bijectivity belongs only to derived API.
  For part (1), the diagonal ideal owner is `KaehlerDifferential.ideal R S'`, and the
  quotient-thickening map is only a bridge/view built from `Algebra.TensorProduct.map` and
  `Ideal.quotientMap`;
- primitive data vs. derived API:
  primitive data are the tower `R → S → S'` and the canonical diagonal ideal
  `KaehlerDifferential.ideal R S'`, together with the owner equivalence
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'`;
  the underlying map `KaehlerDifferential.mapBaseChange R S S'`, the pulled-back diagonal ideal in
  `S' ⊗[R] S`, and the induced quotient map are derived bridge-level constructions and should not
  remain as separate public owner declarations;
- source/core/bridge triage:
  `source-facing`: the bijectivity statements on nilpotent thickenings and on
    `KaehlerDifferential.mapBaseChange`;
  `core/canonical`: `KaehlerDifferential.ideal R S'`,
    `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'`;
  `bridge/view`: the underlying map `KaehlerDifferential.mapBaseChange R S S'`, the
    tensor-product comparison `S' ⊗[R] S → S' ⊗[R] S'`, its pulled-back diagonal ideal, and the
    induced quotient map. -/

-- Proof sketch: identify the source
-- `S' ⊗[S] ((S ⊗[R] S) / J^(k + 1))` with the quotient of `S' ⊗[R] S` by the pulled-back
-- diagonal ideal, then apply Lemma `10.150.6` to the canonical tensor-product map
-- `S' ⊗[R] S → S' ⊗[R] S'` and the diagonal ideal `KaehlerDifferential.ideal R S'`.
/-- Lemma 10.150.7 (1): if `S → S'` is formally étale, then the canonical quotient map
`(S' ⊗[R] S) / (Icomap)^(k + 1) → (S' ⊗[R] S') / (Jdiag)^(k + 1)`, where
`tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S'` is the canonical tensor comparison,
`Jdiag = KaehlerDifferential.ideal R S'`, and `Icomap = Ideal.comap tensorComparison Jdiag`,
is bijective for every `k`. This is the canonical tensor/quotient form of the textbook comparison
`S' ⊗[S] ((S ⊗[R] S) / J^(k + 1)) → (S' ⊗[R] S') / (J')^(k + 1)`. -/
theorem formallyEtale_tensorProduct_quotientMap_pow_bijective
    [Algebra.FormallyEtale S S'] (k : ℕ) :
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom R S S') :
        S' ⊗[R] S →+* S' ⊗[R] S')
    let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
    let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison Jdiag
    Function.Bijective
      ((Ideal.quotientMap (Jdiag ^ (k + 1)) tensorComparison
          (Jdiag.le_comap_pow tensorComparison (k + 1))) :
        (S' ⊗[R] S) ⧸ (Icomap ^ (k + 1)) →+* (S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1))) := by
  let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
    (Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom R S S') :
      S' ⊗[R] S →+* S' ⊗[R] S')
  let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
  let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison Jdiag
  have hsurj : Function.Surjective ((Ideal.Quotient.mk Jdiag).comp tensorComparison) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨(Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[R] S)
        ((Algebra.TensorProduct.lmul' R) y), ?_⟩
    change
      Ideal.Quotient.mk Jdiag
          (tensorComparison (((Algebra.TensorProduct.lmul' R) y) ⊗ₜ[R] (1 : S))) =
        Ideal.Quotient.mk Jdiag y
    rw [Ideal.Quotient.eq]
    rw [show tensorComparison (((Algebra.TensorProduct.lmul' R) y) ⊗ₜ[R] (1 : S)) =
        ((Algebra.TensorProduct.lmul' R) y) ⊗ₜ[R] (1 : S') by
      simp [tensorComparison]]
    rw [RingHom.mem_ker]
    simp
  simpa [tensorComparison, Jdiag, Icomap] using
    RingHom.formallyEtale_quotientMap_pow_bijective tensorComparison Jdiag (k + 1)

/- Lemma 10.150.7 (2): for a formally étale map `S → S'`, the canonical map
`S' ⊗[S] Ω[S⁄R] → Ω[S'⁄R]` is exactly the owner equivalence
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'`. -/
recall KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale

/-- Companion to Lemma 10.150.7 (2): the underlying linear map
`KaehlerDifferential.mapBaseChange R S S'` is bijective. -/
theorem formallyEtale_kaehlerDifferential_mapBaseChange_bijective
    [Algebra.FormallyEtale S S'] :
    Function.Bijective (KaehlerDifferential.mapBaseChange R S S') := by
  simpa using (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S').bijective

end
