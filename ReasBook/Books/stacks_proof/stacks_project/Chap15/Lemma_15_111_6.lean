import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_111_4

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped TensorProduct

universe u v w

/- Domain-style sampling for Lemma 15.111.6:
- primary domain: invariant theory for finite group actions on a tensor-product base change
- sampled owner declarations:
  `FixedPoints.subring`,
  `FixedPoints.subalgebra`,
  `MulSemiringAction.compHom`,
  `Algebra.TensorProduct.map`
- best owner abstraction: the fixed-object owners `FixedPoints.subring` / `FixedPoints.subalgebra`,
  with the induced tensor action treated only as the bridge obtained from
  `Algebra.TensorProduct.map` and `MulSemiringAction.compHom`
- primitive data: a `G`-action on `R`, an `R^G`-algebra `A`, and the canonical base-change ring
  `A ⊗[R^G] R`
- derived API: the induced right-factor `G`-action on `A ⊗[R^G] R`, its fixed subalgebra, and the
  orbit-polynomial consequences for invariant elements

Layer triage:
- `source-facing`: the two orbit-polynomial statements for invariant elements and kernel elements
- `core/canonical`: `FixedPoints.subring`, `FixedPoints.subalgebra`, `MulSemiringAction.compHom`,
  and `Algebra.TensorProduct.map`
- `bridge/view`: the induced action on `A ⊗[R^G] R`, acting trivially on `A` and through the given
  `G`-action on `R`

The source-facing theorems should stay here, but the bridge layer should reuse the canonical tensor
and fixed-point owners instead of carrying a longer hand-rolled action API than needed.
-/

section

variable {R : Type u} {G : Type v}
variable [CommRing R] [Group G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

-- Proof sketch: if `r ∈ R^G`, then every `g : G` fixes `r`; therefore `g • (r * x) = r * (g • x)`
-- for all `x : R`, so the action is `R^G`-linear.
/-- Fixed scalars from `R^G` commute with the given `G`-action on `R`. -/
instance fixedPointsSubring_smulCommClass :
    SMulCommClass G RFix R where
  smul_comm g x r := by
    -- Rewrite the scalar from `R^G` to `R` and use that it is fixed by every group element.
    change (MulSemiringAction.toRingHom G R g) ((x : R) * r) = (x : R) * (g • r)
    rw [map_mul]
    simpa using congrArg (fun t : R => t * (g • r)) (x.2 g)

end

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

local notation "RFix" => FixedPoints.subring R G
local notation "BaseChange" => A ⊗[RFix] R

private noncomputable abbrev tensorBaseChangeRightAlgHom (g : G) :
    BaseChange →ₐ[RFix] BaseChange :=
  Algebra.TensorProduct.map (AlgHom.id RFix A) (MulSemiringAction.toAlgHom RFix R g)

private noncomputable def tensorBaseChangeRightAction :
    G →* (BaseChange →+* BaseChange) where
  toFun g := (tensorBaseChangeRightAlgHom g).toRingHom
  map_one' := by
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · ext a
      simp [tensorBaseChangeRightAlgHom]
    · ext r
      simp [tensorBaseChangeRightAlgHom]
  map_mul' g h := by
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · ext a
      simp [tensorBaseChangeRightAlgHom]
    · ext r
      simp [tensorBaseChangeRightAlgHom, mul_smul]

/-- The induced `G`-action on `A ⊗[R^G] R`, acting on the right tensor factor and trivially on
`A`. -/
noncomputable instance tensorBaseChangeRightMulSemiringAction :
    MulSemiringAction G BaseChange :=
  MulSemiringAction.compHom BaseChange
    (tensorBaseChangeRightAction : G →* (BaseChange →+* BaseChange))

@[simp]
theorem tensorBaseChangeRight_smul_tmul (g : G) (a : A) (r : R) :
    g • ((a ⊗ₜ[RFix] r : BaseChange)) = a ⊗ₜ[RFix] (g • r) := by
  change
    ((tensorBaseChangeRightAction : G →* (BaseChange →+* BaseChange)) g) (a ⊗ₜ[RFix] r) =
    a ⊗ₜ[RFix] (g • r)
  rfl

instance tensorBaseChangeRight_smulCommClass :
    SMulCommClass G RFix BaseChange where
  smul_comm g x z := by
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro a r
      simp [TensorProduct.smul_tmul']
    · intro z w hz hw
      simp [hz, hw]

/-- Helper for Lemma 15.111.6: the coefficientwise `G`-action on the presentation ring
`MvPolynomial A R`. -/
private noncomputable def mvPolynomialCoeffAction :
    G →* (MvPolynomial A R →+* MvPolynomial A R) where
  toFun g := MvPolynomial.map (MulSemiringAction.toRingHom G R g)
  map_one' := by
    -- The coefficientwise action is determined by its effect on constants and variables.
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro a
      simp
  map_mul' g h := by
    -- Composition acts on coefficients by the group product.
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mul_smul]
    · intro a
      simp

/-- Helper for Lemma 15.111.6: the coefficientwise action on `MvPolynomial A R` is the ambient
`G`-action used for fixed points of the presentation ring. -/
private noncomputable instance mvPolynomialCoeffMulSemiringAction :
    MulSemiringAction G (MvPolynomial A R) :=
  MulSemiringAction.compHom (MvPolynomial A R)
    (mvPolynomialCoeffAction (R := R) (G := G) (A := A))

/-- Helper for Lemma 15.111.6: a polynomial fixed by the coefficientwise action has coefficients in
`R^G`. -/
private theorem mvPolynomial_coeff_fixed_of_action_fixed
    (p : MvPolynomial A R)
    (hp : ∀ g : G, (mvPolynomialCoeffAction (R := R) (G := G) (A := A) g) p = p) :
    ∀ d, p.coeff d ∈ RFix := by
  intro d g
  -- Read the fixedness relation on the `d`-th coefficient.
  have hcoeff := congrArg (fun q : MvPolynomial A R => MvPolynomial.coeff d q) (hp g)
  simpa [mvPolynomialCoeffAction, MvPolynomial.coeff_map] using hcoeff

/-- Helper for Lemma 15.111.6: a presentation polynomial with coefficients in `R^G` descends to a
polynomial over `R^G`. -/
private noncomputable def mvPolynomial_descendToFixed
    (p : MvPolynomial A R) (hp : ∀ d, p.coeff d ∈ RFix) :
    MvPolynomial A RFix :=
  p.support.sum fun d ↦ MvPolynomial.monomial d ⟨p.coeff d, hp d⟩

/-- Helper for Lemma 15.111.6: mapping the descended fixed-coefficient polynomial back to `R`
recovers the original polynomial. -/
private theorem mvPolynomial_map_descendToFixed
    (p : MvPolynomial A R) (hp : ∀ d, p.coeff d ∈ RFix) :
    MvPolynomial.map ((FixedPoints.subring R G).subtype : RFix →+* R)
      (mvPolynomial_descendToFixed (R := R) (G := G) (A := A) p hp) = p := by
  -- Compare coefficients term-by-term on the finite support of `p`.
  ext d
  by_cases hd : d ∈ p.support
  · simp [mvPolynomial_descendToFixed]
  · have hcoeff_zero : p.coeff d = 0 := by
      -- Outside the support, the coefficient must vanish.
      by_contra hne
      exact hd ((MvPolynomial.mem_support_iff).2 hne)
    simp [mvPolynomial_descendToFixed, hcoeff_zero]

/-- Helper for Lemma 15.111.6: coefficient extension from `R^G` to `R` lands in the fixed
subring of `MvPolynomial A R`. -/
private noncomputable def fixedPresentationToMvPolynomialFixedSubring :
    MvPolynomial A RFix →+* FixedPoints.subring (MvPolynomial A R) G :=
  RingHom.codRestrict
    (MvPolynomial.map ((FixedPoints.subring R G).subtype : RFix →+* R))
    (FixedPoints.subring (MvPolynomial A R) G) fun p g ↦ by
      -- Compare coefficients after applying the coefficientwise action.
      ext d
      simp [mvPolynomialCoeffAction, MvPolynomial.coeff_map]

/-- Helper for Lemma 15.111.6: coefficient extension from `R^G` to `R` identifies
`MvPolynomial A (R^G)` with the fixed subring of `MvPolynomial A R`. -/
private theorem fixedPresentationToMvPolynomialFixedSubring_bijective :
    Function.Bijective
      (fixedPresentationToMvPolynomialFixedSubring (R := R) (G := G) (A := A)) := by
  constructor
  · intro p q hpq
    -- Forget to the ambient polynomial ring and use injectivity of coefficient extension.
    exact MvPolynomial.map_injective
      ((FixedPoints.subring R G).subtype : RFix →+* R) Subtype.val_injective <|
      congrArg Subtype.val hpq
  · intro p
    -- Descend the coefficients of a fixed polynomial back to `R^G`.
    let hp :
        ∀ d, p.1.coeff d ∈ RFix :=
      mvPolynomial_coeff_fixed_of_action_fixed (R := R) (G := G) (A := A) p.1 fun g ↦ by
        simpa using p.2 g
    refine ⟨mvPolynomial_descendToFixed (R := R) (G := G) (A := A) p.1 hp, ?_⟩
    apply Subtype.ext
    -- The descended fixed-coefficient polynomial maps back to the original fixed polynomial.
    simpa [fixedPresentationToMvPolynomialFixedSubring] using
      mvPolynomial_map_descendToFixed (R := R) (G := G) (A := A) p.1 hp

/-- Helper for Lemma 15.111.6: the fixed subring of the coefficientwise action on
`MvPolynomial A R` is canonically the fixed-coefficient presentation `MvPolynomial A (R^G)`. -/
private noncomputable def mvPolynomial_fixedSubring_equiv_fixedPresentation :
    FixedPoints.subring (MvPolynomial A R) G ≃+* MvPolynomial A RFix :=
  (RingEquiv.ofBijective
      (fixedPresentationToMvPolynomialFixedSubring (R := R) (G := G) (A := A))
      (fixedPresentationToMvPolynomialFixedSubring_bijective
        (R := R) (G := G) (A := A))).symm

end

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

local notation "RFix" => FixedPoints.subring R G
local notation "BaseChange" => A ⊗[RFix] R
local notation "BaseChangeFixed" => FixedPoints.subalgebra RFix BaseChange G
local notation "PresentationPoly" => MvPolynomial A R

/-- Helper for Lemma 15.111.6: elements coming from the left tensor factor are fixed by the
induced right-factor action. -/
private theorem includeLeft_fixed (a : A) :
    ∀ g : G,
      g • ((Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) a) =
        (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) a := by
  intro g
  -- Rewrite `includeLeft a` as `a ⊗ₜ 1` and use the defining action formula on pure tensors.
  simpa [Algebra.TensorProduct.includeLeft_apply] using
    (tensorBaseChangeRight_smul_tmul (R := R) (G := G) (A := A) g a (1 : R))

/-- Helper for Lemma 15.111.6: the induced right-factor action on the tensor product sends the
right inclusion of `r` to the right inclusion of `g • r`. -/
private theorem includeRight_smul (g : G) (r : R) :
    g • ((Algebra.TensorProduct.includeRight : R →ₐ[RFix] BaseChange) r) =
      (Algebra.TensorProduct.includeRight : R →ₐ[RFix] BaseChange) (g • r) := by
  -- Rewrite `includeRight r` as `1 ⊗ₜ r` and use the defining tensor action formula.
  simpa [Algebra.TensorProduct.includeRight_apply] using
    (tensorBaseChangeRight_smul_tmul (R := R) (G := G) (A := A) g (1 : A) r)

/-- Helper for Lemma 15.111.6: evaluate the presentation polynomial ring
`MvPolynomial A R` on the canonical left and right tensor-factor inclusions. -/
private noncomputable def mvPolynomial_tensor_evaluation :
    PresentationPoly →+* BaseChange :=
  MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeRight : R →ₐ[RFix] BaseChange).toRingHom
    fun a ↦ (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) a

/-- Helper for Lemma 15.111.6: every element of `A ⊗[R^G] R` is obtained by evaluating a
polynomial in the presentation ring `MvPolynomial A R`. -/
private theorem mvPolynomial_tensor_evaluation_surjective :
    Function.Surjective (mvPolynomial_tensor_evaluation (R := R) (G := G) (A := A)) := by
  intro z
  -- Reduce surjectivity to pure tensors and lift `a ⊗ₜ r` to `X a * C r`.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp [mvPolynomial_tensor_evaluation]⟩
  · intro a r
    refine ⟨MvPolynomial.X a * MvPolynomial.C r, ?_⟩
    -- The chosen polynomial evaluates to the corresponding pure tensor.
    simpa [mvPolynomial_tensor_evaluation, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, mul_comm]
  · intro x y hx hy
    rcases hx with ⟨px, rfl⟩
    rcases hy with ⟨py, rfl⟩
    -- Surjectivity is stable under addition because evaluation is a ring homomorphism.
    exact ⟨px + py, by simp [mvPolynomial_tensor_evaluation]⟩

/-- Helper for Lemma 15.111.6: `MvPolynomial.algebraTensorAlgEquiv` sends the tensor-side
`includeRight` branch to coefficient extension along `R^G ↪ R`. -/
private theorem mvPolynomial_algebraTensorAlgEquiv_apply_includeRight
    (p : MvPolynomial A RFix) :
    MvPolynomial.algebraTensorAlgEquiv RFix R
      ((Algebra.TensorProduct.includeRight :
          MvPolynomial A RFix →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix) p) =
        MvPolynomial.map ((FixedPoints.subring R G).subtype : RFix →+* R) p := by
  -- Unfold the owner equivalence once; its `includeRight` branch is coefficient extension.
  simp [MvPolynomial.algebraTensorAlgEquiv]
  -- The remaining coefficient map is just the fixed-subring subtype.
  simpa using congrArg (fun f : RFix →+* R => MvPolynomial.map f p)
    (show algebraMap RFix R = (FixedPoints.subring R G).subtype from rfl)

/-- Helper for Lemma 15.111.6: view `MvPolynomial.algebraTensorAlgEquiv` as an `R^G`-algebra map
from the tensor presentation to the presentation ring over `R`. -/
private noncomputable def tensor_mvPolynomial_algHom :
    (R ⊗[RFix] MvPolynomial A RFix) →ₐ[RFix] MvPolynomial A R :=
  { toRingHom := (MvPolynomial.algebraTensorAlgEquiv RFix R).toRingHom
    commutes' := by
      intro r
      -- The owner equivalence respects the left `R^G`-algebra structure.
      simp [MvPolynomial.algebraTensorAlgEquiv] }

/-- Helper for Lemma 15.111.6: after quotienting by an ideal `J` in the fixed-coefficient
presentation ring, the tensor-side quotient still maps canonically to the presentation quotient
over `R`. -/
private noncomputable def tensor_mvPolynomial_quotientMap
    (J : Ideal (MvPolynomial A RFix)) :
    (R ⊗[RFix] MvPolynomial A RFix) ⧸
        Ideal.map
          ((Algebra.TensorProduct.includeRight :
              MvPolynomial A RFix →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix).toRingHom)
          J →ₐ[RFix]
      MvPolynomial A R ⧸
        Ideal.map (MvPolynomial.map ((FixedPoints.subring R G).subtype : RFix →+* R)) J := by
  refine Ideal.quotientMapₐ _ (tensor_mvPolynomial_algHom (R := R) (G := G) (A := A)) ?_
  -- It suffices to check that a quotient representative coming from `J` still lands in the
  -- extended ideal after applying the tensor/MvPolynomial bridge.
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change
    MvPolynomial.algebraTensorAlgEquiv RFix R
      ((Algebra.TensorProduct.includeRight :
          MvPolynomial A RFix →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix) x) ∈
      Ideal.map (MvPolynomial.map ((FixedPoints.subring R G).subtype : RFix →+* R)) J
  rw [mvPolynomial_algebraTensorAlgEquiv_apply_includeRight]
  exact Ideal.mem_map_of_mem _ hx

/-- Helper for Lemma 15.111.6: the fixed-coefficient presentation
`MvPolynomial A (R^G)` evaluates canonically onto `A`. -/
private noncomputable def fixedPresentationEvaluation :
    MvPolynomial A RFix →ₐ[RFix] A :=
  MvPolynomial.aeval id

/-- Helper for Lemma 15.111.6: the fixed-coefficient presentation map is surjective because each
generator `X a` already evaluates to `a`. -/
private theorem fixedPresentationEvaluation_surjective :
    Function.Surjective (fixedPresentationEvaluation (R := R) (G := G) (A := A)) := by
  intro a
  -- The variable `X a` is a direct preimage of `a`.
  refine ⟨MvPolynomial.X a, ?_⟩
  simp [fixedPresentationEvaluation]

/-- Helper for Lemma 15.111.6: the source presentation of `A` is the quotient of
`MvPolynomial A (R^G)` by the kernel of `aeval id`. -/
private noncomputable def fixedPresentationQuotientToA :
    (MvPolynomial A RFix ⧸
        RingHom.ker (fixedPresentationEvaluation (R := R) (G := G) (A := A)).toRingHom) ≃ₐ[RFix]
      A :=
  Ideal.quotientKerAlgEquivOfSurjective
    (fixedPresentationEvaluation_surjective (R := R) (G := G) (A := A))

/-- Helper for Lemma 15.111.6: under the presentation quotient equivalence, the class of `X a`
maps to `a`. -/
private theorem fixedPresentationQuotientToA_mk_X (a : A) :
    fixedPresentationQuotientToA (R := R) (G := G) (A := A)
        (Ideal.Quotient.mk _ (MvPolynomial.X a)) = a := by
  -- Unfold the quotient equivalence on representatives and evaluate the generator.
  simpa [fixedPresentationQuotientToA, fixedPresentationEvaluation] using
    (Ideal.quotientKerAlgEquivOfSurjective_mk
      (fixedPresentationEvaluation_surjective (R := R) (G := G) (A := A))
      (MvPolynomial.X a))

/-- Helper for Lemma 15.111.6: under the same quotient equivalence, constants evaluate through the
`R^G`-algebra structure on `A`. -/
private theorem fixedPresentationQuotientToA_mk_C (r : RFix) :
    fixedPresentationQuotientToA (R := R) (G := G) (A := A)
        (Ideal.Quotient.mk _ (MvPolynomial.C r)) = algebraMap RFix A r := by
  -- Constants are carried by `aeval` through the coefficient algebra map.
  simpa [fixedPresentationQuotientToA, fixedPresentationEvaluation] using
    (Ideal.quotientKerAlgEquivOfSurjective_mk
      (fixedPresentationEvaluation_surjective (R := R) (G := G) (A := A))
      (MvPolynomial.C r))

/-- Helper for Lemma 15.111.6: in the tensor base change, the left image of a base scalar agrees
with its right image. -/
private theorem tensorBaseChange_includeLeft_algebraMap_eq_includeRight
    (r : RFix) :
    (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) (algebraMap RFix A r) =
      (Algebra.TensorProduct.includeRight : R →ₐ[RFix] BaseChange)
        ((FixedPoints.subring R G).subtype r) := by
  -- Rewrite both pure tensors as the common scalar action of `r` on `1 ⊗ 1`.
  calc
    (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) (algebraMap RFix A r) =
        r • ((1 : A) ⊗ₜ[RFix] (1 : R)) := by
          simpa [Algebra.TensorProduct.includeLeft_apply, Algebra.algebraMap_eq_smul_one] using
            (TensorProduct.smul_tmul' (R := RFix) r (1 : A) (1 : R)).symm
    _ = (1 : A) ⊗ₜ[RFix] (r • (1 : R)) := by
          simpa using (TensorProduct.tmul_smul (R := RFix) r (1 : A) (1 : R)).symm
    _ =
        (Algebra.TensorProduct.includeRight : R →ₐ[RFix] BaseChange)
          ((FixedPoints.subring R G).subtype r) := by
          simpa [Algebra.TensorProduct.includeRight_apply] using
            congrArg (fun x : R => (1 : A) ⊗ₜ[RFix] x) (Algebra.algebraMap_eq_smul_one r).symm

/-- Helper for Lemma 15.111.6: tensoring the fixed-coefficient presentation evaluation and then
commuting the tensor factors gives a canonical map from the tensor presentation to
`A ⊗[R^G] R`. -/
private noncomputable def tensorFixedPresentationEvaluation :
    R ⊗[RFix] MvPolynomial A RFix →ₐ[RFix] BaseChange :=
  (Algebra.TensorProduct.comm RFix R A).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id RFix R)
      (fixedPresentationEvaluation (R := R) (G := G) (A := A)))

/-- Helper for Lemma 15.111.6: the tensor-side fixed presentation map sends the left tensor
generator from `R` to the right inclusion into `A ⊗[R^G] R`. -/
private theorem tensorFixedPresentationEvaluation_includeLeft (r : R) :
    tensorFixedPresentationEvaluation (R := R) (G := G) (A := A)
        ((Algebra.TensorProduct.includeLeft : R →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix) r) =
      (Algebra.TensorProduct.includeRight : R →ₐ[RFix] BaseChange) r := by
  -- Expand the tensor map on a pure tensor and commute the factors once.
  change
    (Algebra.TensorProduct.comm RFix R A)
      ((Algebra.TensorProduct.map (AlgHom.id RFix R)
        (fixedPresentationEvaluation (R := R) (G := G) (A := A)))
          (r ⊗ₜ[RFix] (1 : MvPolynomial A RFix))) = (1 : A) ⊗ₜ[RFix] r
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.TensorProduct.comm_tmul]

/-- Helper for Lemma 15.111.6: the tensor-side fixed presentation map sends the right tensor
generator from `MvPolynomial A (R^G)` to the left inclusion of its evaluation in `A`. -/
private theorem tensorFixedPresentationEvaluation_includeRight
    (p : MvPolynomial A RFix) :
    tensorFixedPresentationEvaluation (R := R) (G := G) (A := A)
        ((Algebra.TensorProduct.includeRight :
            MvPolynomial A RFix →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix) p) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange)
        (fixedPresentationEvaluation (R := R) (G := G) (A := A) p) := by
  -- Expand the tensor map on a pure tensor and commute the factors once.
  change
    (Algebra.TensorProduct.comm RFix R A)
      ((Algebra.TensorProduct.map (AlgHom.id RFix R)
        (fixedPresentationEvaluation (R := R) (G := G) (A := A)))
          ((1 : R) ⊗ₜ[RFix] p)) =
      (fixedPresentationEvaluation (R := R) (G := G) (A := A) p) ⊗ₜ[RFix] (1 : R)
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]

/-- Helper for Lemma 15.111.6: `MvPolynomial.algebraTensorAlgEquiv` sends the left tensor-side
`R`-generator to the constant polynomial with coefficient `r`. -/
private theorem mvPolynomial_algebraTensorAlgEquiv_apply_includeLeft
    (r : R) :
    MvPolynomial.algebraTensorAlgEquiv RFix R
      ((Algebra.TensorProduct.includeLeft : R →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix) r) =
        MvPolynomial.C r := by
  -- Unfold the owner equivalence once; the left branch is the constant polynomial inclusion.
  simp [MvPolynomial.algebraTensorAlgEquiv]

/-- Helper for Lemma 15.111.6: transporting the tensored fixed-coefficient presentation
evaluation across `MvPolynomial.algebraTensorAlgEquiv` recovers the concrete evaluation map on
`MvPolynomial A R`. -/
private theorem mvPolynomial_tensor_evaluation_comp_tensor_mvPolynomial_algHom :
    (mvPolynomial_tensor_evaluation (R := R) (G := G) (A := A)).comp
        (tensor_mvPolynomial_algHom (R := R) (G := G) (A := A)).toRingHom =
      (tensorFixedPresentationEvaluation (R := R) (G := G) (A := A)).toRingHom := by
  refine Algebra.TensorProduct.ringHom_ext ?_ ?_
  · ext r
    -- The left tensor generator becomes a constant polynomial and then evaluates on coefficients.
    change
      mvPolynomial_tensor_evaluation (R := R) (G := G) (A := A)
        (MvPolynomial.algebraTensorAlgEquiv RFix R
          ((Algebra.TensorProduct.includeLeft : R →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix) r)) =
      tensorFixedPresentationEvaluation (R := R) (G := G) (A := A)
        ((Algebra.TensorProduct.includeLeft : R →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix) r)
    rw [mvPolynomial_algebraTensorAlgEquiv_apply_includeLeft,
      tensorFixedPresentationEvaluation_includeLeft]
    simp [mvPolynomial_tensor_evaluation]
  · apply MvPolynomial.ringHom_ext
    · intro r
      -- For coefficients from `R^G`, compare the two branches through the base scalar relation.
      change
        mvPolynomial_tensor_evaluation (R := R) (G := G) (A := A)
          (MvPolynomial.algebraTensorAlgEquiv RFix R
            ((Algebra.TensorProduct.includeRight :
                MvPolynomial A RFix →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix)
              (MvPolynomial.C r))) =
        tensorFixedPresentationEvaluation (R := R) (G := G) (A := A)
            ((Algebra.TensorProduct.includeRight :
              MvPolynomial A RFix →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix)
            (MvPolynomial.C r))
      rw [mvPolynomial_algebraTensorAlgEquiv_apply_includeRight,
        tensorFixedPresentationEvaluation_includeRight]
      simpa [mvPolynomial_tensor_evaluation, fixedPresentationEvaluation] using
        (tensorBaseChange_includeLeft_algebraMap_eq_includeRight
          (R := R) (G := G) (A := A) r).symm
    · intro a
      -- For variables `X a`, both branches land in the left tensor inclusion of `a`.
      change
        mvPolynomial_tensor_evaluation (R := R) (G := G) (A := A)
          (MvPolynomial.algebraTensorAlgEquiv RFix R
            ((Algebra.TensorProduct.includeRight :
                MvPolynomial A RFix →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix)
              (MvPolynomial.X a))) =
        tensorFixedPresentationEvaluation (R := R) (G := G) (A := A)
          ((Algebra.TensorProduct.includeRight :
              MvPolynomial A RFix →ₐ[RFix] R ⊗[RFix] MvPolynomial A RFix)
            (MvPolynomial.X a))
      rw [mvPolynomial_algebraTensorAlgEquiv_apply_includeRight,
        tensorFixedPresentationEvaluation_includeRight]
      simp [mvPolynomial_tensor_evaluation, fixedPresentationEvaluation]

/-- Helper for Lemma 15.111.6: the presentation evaluation
`MvPolynomial A R → A ⊗[R^G] R` is equivariant for the coefficientwise action on the source and
the right-factor action on the target. -/
private noncomputable def mvPolynomial_tensor_evaluationMulSemiringActionHom :
    PresentationPoly →+*[G] BaseChange where
  toRingHom := mvPolynomial_tensor_evaluation (R := R) (G := G) (A := A)
  map_smul' := by
    intro g p
    -- Check equivariance on constants, variables, and ring operations.
    refine MvPolynomial.induction_on p ?_ ?_ ?_
    · intro r
      simp [mvPolynomial_tensor_evaluation, includeRight_smul, mvPolynomialCoeffAction]
    · intro p q hp hq
      simp [hp, hq]
    · intro a p hp
      simp [mvPolynomial_tensor_evaluation, hp]

/-- Helper for Lemma 15.111.6: if a presentation polynomial already has coefficients in `R^G`,
then evaluating it in `A ⊗[R^G] R` is the same as evaluating it in `A` and then using the left
tensor inclusion. -/
private theorem mvPolynomial_tensor_evaluation_map_fixedPresentation
    (p : MvPolynomial A RFix) :
    mvPolynomial_tensor_evaluation (R := R) (G := G) (A := A)
        (MvPolynomial.map ((FixedPoints.subring R G).subtype : RFix →+* R) p) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange)
        (fixedPresentationEvaluation (R := R) (G := G) (A := A) p) := by
  -- Compare the two ring homomorphisms on constants, variables, and multiplication.
  refine MvPolynomial.induction_on p ?_ ?_ ?_
  · intro r
    -- Fixed scalars can be evaluated on either tensor factor.
    rw [MvPolynomial.map_C, map_C, fixedPresentationEvaluation]
    simpa [mvPolynomial_tensor_evaluation] using
      tensorBaseChange_includeLeft_algebraMap_eq_includeRight
        (R := R) (G := G) (A := A) r
  · intro p q hp hq
    -- Both routes are ring homomorphisms.
    simp [hp, hq]
  · intro a p hp
    -- Variables evaluate to `a`, and multiplication is preserved.
    simp [fixedPresentationEvaluation, mvPolynomial_tensor_evaluation, hp]

/-- Helper for Lemma 15.111.6: after descending a fixed polynomial from `MvPolynomial A R` to
`MvPolynomial A (R^G)`, the induced fixed-points map is just evaluation in `A` followed by the
left tensor inclusion. -/
private theorem mvPolynomial_tensor_evaluation_on_fixedSubring
    (p : FixedPoints.subring PresentationPoly G) :
    mvPolynomial_tensor_evaluation (R := R) (G := G) (A := A) p.1 =
      (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange)
        ((fixedPresentationEvaluation (R := R) (G := G) (A := A)).toRingHom.comp
          (mvPolynomial_fixedSubring_equiv_fixedPresentation
            (R := R) (G := G) (A := A)).toRingHom p) := by
  let q : MvPolynomial A RFix :=
    mvPolynomial_fixedSubring_equiv_fixedPresentation
      (R := R) (G := G) (A := A) p
  have hq :
      fixedPresentationToMvPolynomialFixedSubring (R := R) (G := G) (A := A) q = p := by
    -- The equivalence was defined as the inverse of coefficient extension.
    exact
      RingEquiv.apply_symm_apply
        (RingEquiv.ofBijective
          (fixedPresentationToMvPolynomialFixedSubring (R := R) (G := G) (A := A))
          (fixedPresentationToMvPolynomialFixedSubring_bijective
            (R := R) (G := G) (A := A)))
        p
  change
    mvPolynomial_tensor_evaluation (R := R) (G := G) (A := A) p.1 =
      (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange)
        (fixedPresentationEvaluation (R := R) (G := G) (A := A) q)
  have hq_val :
      (fixedPresentationToMvPolynomialFixedSubring (R := R) (G := G) (A := A) q).1 = p.1 :=
    congrArg Subtype.val hq
  rw [← hq_val]
  exact mvPolynomial_tensor_evaluation_map_fixedPresentation
    (R := R) (G := G) (A := A) q

-- Proof sketch: choose a polynomial algebra `E` over `R^G` mapping surjectively to `A`, lift `b`
-- to an invariant element of `E ⊗[R^G] R`, apply Lemma `15.111.4` to that polynomial algebra,
-- and descend the resulting monic polynomial to `A`.
/-- Lemma 15.111.6 (1): if `b : A ⊗[R^G] R` is fixed by the induced right `G`-action, then there
exists a monic polynomial over `A` whose image in `(A ⊗[R^G] R)[T]` is `(X - C b)^|G|`. -/
@[stacks 0BRG]
theorem exists_monic_polynomial_over_baseChange_eq_X_sub_C_pow_of_fixed
    (b : BaseChangeFixed) :
    ∃ P : Polynomial A,
      P.Monic ∧
        P.map (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange) =
          (X - C (b : BaseChange)) ^ Nat.card G := by
  -- Route correction: clause (1) closes directly from the fixed-points owner theorem applied to
  -- the equivariant evaluation map `MvPolynomial A R → A ⊗[R^G] R`; the coefficient descent above
  -- then turns the resulting polynomial over the fixed subring into one over `A`.
  let φ :
      PresentationPoly →+*[G] BaseChange :=
    mvPolynomial_tensor_evaluationMulSemiringActionHom (R := R) (G := G) (A := A)
  obtain ⟨Q, hQmonic, hQmap⟩ :=
    exists_monic_polynomial_over_fixedPoints_map_eq_X_sub_C_pow
      φ
      (mvPolynomial_tensor_evaluation_surjective (R := R) (G := G) (A := A))
      b
  let ψ : FixedPoints.subring PresentationPoly G →+* A :=
    (fixedPresentationEvaluation (R := R) (G := G) (A := A)).toRingHom.comp
      (mvPolynomial_fixedSubring_equiv_fixedPresentation
        (R := R) (G := G) (A := A)).toRingHom
  refine ⟨Polynomial.map ψ Q, hQmonic.map _, ?_⟩
  let ι : BaseChangeFixed →+* BaseChange := BaseChangeFixed.val
  have hψ :
      (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange).toRingHom.comp ψ =
        ι.comp φ.fixedPoints := by
    ext p
    -- Forgetting the fixed codomain turns the owner map back into ordinary evaluation.
    simpa [ψ, φ, ι, MulSemiringActionHom.fixedPoints] using
      mvPolynomial_tensor_evaluation_on_fixedSubring
        (R := R) (G := G) (A := A) p
  -- Map the fixed-subring polynomial identity along `BaseChangeFixed ↪ BaseChange`.
  calc
    Polynomial.map (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange)
        (Polynomial.map ψ Q) =
      Polynomial.map
        ((Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange).toRingHom.comp ψ) Q := by
          rw [Polynomial.map_map]
    _ = Polynomial.map (ι.comp φ.fixedPoints) Q := by
          rw [hψ]
    _ = Polynomial.map ι (Polynomial.map φ.fixedPoints Q) := by
          rw [Polynomial.map_map]
    _ = Polynomial.map ι ((X - C b) ^ Nat.card G) := by
          rw [hQmap]
    _ = (X - C (b : BaseChange)) ^ Nat.card G := by
          simp

-- Proof sketch: apply the first clause to the image of `a` in `A ⊗[R^G] R`; because `a` lies in
-- the kernel of `A → A ⊗[R^G] R`, its image is zero, so the translated polynomial identity
-- reduces to `(X - C a)^|G| = X^|G|` in `A[T]`.
/-- Lemma 15.111.6 (2): if `a` maps to zero under the canonical base-change map
`A → A ⊗[R^G] R`, then `(X - C a)^|G| = X^|G|` in `A[T]`. -/
@[stacks 0BRG]
theorem kernelElement_X_sub_pow_eq_X_pow_of_baseChange
    (a : RingHom.ker (Algebra.TensorProduct.includeLeft : A →ₐ[RFix] BaseChange)) :
    ((X - C a.1) ^ Nat.card G : Polynomial A) = X ^ Nat.card G := by
  -- Route correction: the same presentation map above isolates the remaining work to the quotient
  -- transport comparison with `Lemma_15_111_4`. The fixed-coefficient descent step has been
  -- separated out above, and the new compatibility
  -- `mvPolynomial_tensor_evaluation_comp_tensor_mvPolynomial_algHom` fixes the tensor-side
  -- evaluation comparison. Only the quotient-equivalence and final comparison with
  -- `Algebra.TensorProduct.includeLeft` remain.
  -- TODO: transport `a` through the quotient model determined by `ker (MvPolynomial.aeval id)` and
  -- apply `kernelElement_X_sub_pow_eq_X_pow` from `Lemma_15_111_4`.
  sorry

end
