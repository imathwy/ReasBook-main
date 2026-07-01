import stacks_project.Chap10.Definition_10_60_10
import stacks_project.Chap10.Definition_10_70_1
import stacks_project.Chap10.«10_69_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

noncomputable section

variable {R : Type u} [CommRing R]

variable [IsRegularLocalRing R]

local notation "κ" => ResidueField R
local notation "Sym" => SymmetricAlgebra κ (CotangentSpace R)
local notation "grR" => idealAssociatedGradedRing (maximalIdeal R)

/-
Domain-style sampling pass.

Primary domain: local commutative algebra of associated graded rings.

Sampled owner declarations:
* `idealAssociatedGradedRing`, `idealAssociatedGradedRingGrade`, and
  `idealAssociatedGradedDegreeOne` from `10_69_0_1.lean`;
* `CotangentSpace`, `(maximalIdeal R).toCotangent`, and
  `IsLocalRing.CotangentSpace.span_image_eq_top_iff` from mathlib's cotangent-space owner API;
* `SymmetricAlgebra.ι` and `SymmetricAlgebra.equivMvPolynomial` from mathlib's symmetric-algebra
  basis API.

Owner abstraction: the core owner is the associated graded ring
`grR = idealAssociatedGradedRing (maximalIdeal R)`. The source-facing surface in this file is the
polynomial `κ`-algebra presentation attached to a chosen regular system of parameters, while the
intrinsic symmetric-algebra presentation on `CotangentSpace R = maximalIdeal R / (maximalIdeal R)^2`
is the supporting canonical layer beneath it.

Primitive data:
* the core owner `grR = idealAssociatedGradedRing (maximalIdeal R)`;
* the intrinsic degree-one generator map
  `CotangentSpace R → grR`, sending the cotangent class of `x` to
  `idealAssociatedGradedDegreeOne x`.

Derived API:
* after choosing a regular system of parameters, a basis of `CotangentSpace R`;
* the resulting source-facing polynomial presentation `MvPolynomial (Fin d) κ ≃ₐ[κ] grR`;
* the supporting intrinsic presentation of `grR` as
  `SymmetricAlgebra κ (CotangentSpace R)`.

Source/core/bridge triage:
* source-facing: for a regular system of parameters `x : Fin d → maximalIdeal R`, the associated
  graded ring is the polynomial `κ`-algebra on the degree-one classes of the `x i`;
* core/canonical: `SymmetricAlgebra κ (CotangentSpace R)` mapping canonically to `grR`;
* bridge/view: the cotangent-space basis extracted from a regular system of parameters and the
  basis rewrite `SymmetricAlgebra.equivMvPolynomial`.
-/

section

variable {d : ℕ}

local notation "P" => MvPolynomial (Fin d) κ

local instance : CommRing grR :=
  inferInstanceAs (CommRing (idealAssociatedGradedRing (maximalIdeal R)))

local instance : Algebra κ grR :=
  inferInstance

local instance : Module κ grR :=
  by
    let _ : Algebra κ grR := inferInstance
    exact Algebra.toModule

/-- The degree-one classes define the canonical `R`-linear map from the maximal ideal to the
associated graded ring. -/
noncomputable def associatedGradedDegreeOneLinear :
    maximalIdeal R →ₗ[R] grR where
  toFun := fun x ↦ idealAssociatedGradedDegreeOne x
  map_add' x y := by
    sorry
  map_smul' a x := by
    sorry

private theorem associatedGradedDegreeOneLinear_mul
    (x y : maximalIdeal R) :
    idealAssociatedGradedDegreeOne (x * y) = 0 := by
  sorry

/-- The degree-one classes define the canonical `R`-linear map from the cotangent space to the
associated graded ring. -/
noncomputable def associatedGradedDegreeOneCotangentLinearR :
    CotangentSpace R →ₗ[R] grR :=
  Ideal.Cotangent.lift associatedGradedDegreeOneLinear associatedGradedDegreeOneLinear_mul

/-- The degree-one classes in the associated graded ring define the canonical `κ`-linear map from
the cotangent space `CotangentSpace R` to `grR`. This is the primitive core datum; the symmetric-
algebra and polynomial presentations are derived from it. -/
noncomputable def associatedGradedDegreeOneCotangentLinear :
    CotangentSpace R →ₗ[κ] grR :=
  let f : CotangentSpace R →ₗ[R] grR := associatedGradedDegreeOneCotangentLinearR
  { toFun := fun x ↦ f x
    map_add' := f.map_add
    map_smul' := by
      sorry }

@[simp] theorem associatedGradedDegreeOneCotangentLinear_toCotangent
    (x : maximalIdeal R) :
    associatedGradedDegreeOneCotangentLinear ((maximalIdeal R).toCotangent x) =
      idealAssociatedGradedDegreeOne x := by
  simpa [associatedGradedDegreeOneCotangentLinear,
    associatedGradedDegreeOneCotangentLinearR, associatedGradedDegreeOneLinear] using
    Ideal.Cotangent.lift_toCotangent associatedGradedDegreeOneLinear
      associatedGradedDegreeOneLinear_mul x

/-- A regular system of parameters spans the cotangent space after passing to
`maximalIdeal R / (maximalIdeal R)^2`. This is the direct source-facing use of the cotangent-space
owner theorem `CotangentSpace.span_image_eq_top_iff`; the basis object is derived from this span
statement together with regularity's finrank equality. -/
theorem regularSystemOfParameters_span_toCotangent_eq_top
    {x : Fin d → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) :
    Submodule.span κ (Set.range fun i ↦ (maximalIdeal R).toCotangent (x i)) = ⊤ := by
  have hparam : IsLocalRing.parameterIdeal x = maximalIdeal R :=
    (IsLocalRing.isRegularSystemOfParameters_iff x).1 hx |>.2
  have hsubtype_range :
      (((↑) : maximalIdeal R → R) '' Set.range x) =
        Set.range fun i ↦ ((x i : maximalIdeal R) : R) := by
    ext r
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  have hspan : Submodule.span R (Set.range x) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_subtype_top, Submodule.map_span]
    change Ideal.span (((↑) : maximalIdeal R → R) '' Set.range x) = maximalIdeal R
    simpa [IsLocalRing.parameterIdeal_eq_span, hsubtype_range] using hparam
  have hcot_range :
      (maximalIdeal R).toCotangent '' Set.range x =
        Set.range fun i ↦ (maximalIdeal R).toCotangent (x i) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  simpa [hcot_range] using
    IsLocalRing.CotangentSpace.span_image_eq_top_iff.2 hspan

/-- The cotangent classes of a regular system of parameters form the canonical basis obtained from
their spanning property and the regular-local-ring finrank formula. -/
noncomputable def regularSystemOfParameters_cotangentBasis
    {x : Fin d → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) :
    Module.Basis (Fin d) κ (CotangentSpace R) :=
  basisOfTopLeSpanOfCardEqFinrank
    (fun i ↦ (maximalIdeal R).toCotangent (x i))
    (by simpa using (regularSystemOfParameters_span_toCotangent_eq_top hx).ge)
    (by
      have hregdim :
          IsRegularLocalRing R ↔ Module.finrank κ (CotangentSpace R) = ringKrullDim R :=
        IsRegularLocalRing.iff_finrank_cotangentSpace R
      have hcot :
          Module.finrank κ (CotangentSpace R) = ringKrullDim R :=
        hregdim.1 inferInstance
      have hdim : ringKrullDim R = d :=
        (IsLocalRing.isRegularSystemOfParameters_iff x).1 hx |>.1
      simpa using
        (show Module.finrank κ (CotangentSpace R) = d from by
          exact_mod_cast hcot.trans hdim).symm)

@[simp] theorem regularSystemOfParameters_cotangentBasis_apply
    {x : Fin d → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) (i : Fin d) :
    regularSystemOfParameters_cotangentBasis hx i =
      (maximalIdeal R).toCotangent (x i) := by
  simp [regularSystemOfParameters_cotangentBasis]

-- Proof sketch: the degree-one map `maximalIdeal R → grR` kills `(maximalIdeal R)^2`, so it
-- descends to a `κ`-linear map `CotangentSpace R → grR`. The symmetric algebra on
-- `CotangentSpace R` is the canonical owner for commutative `κ`-algebras generated by that
-- degree-one piece. Regularity identifies the Hilbert function of `grR` with that of the
-- symmetric algebra on `CotangentSpace R`, forcing the induced algebra map to be bijective.
/-- Supporting core/canonical companion: intrinsically, the associated graded ring `grR` of the
maximal ideal is the symmetric algebra on the cotangent space
`CotangentSpace R = maximalIdeal R / (maximalIdeal R)^2`. The source-facing polynomial
presentation above is obtained by rewriting this intrinsic presentation through the basis
`regularSystemOfParameters_cotangentBasis` attached to a regular system of parameters. -/
noncomputable def regularLocalRing_associatedGraded_algEquiv_symmetricAlgebraCotangentSpace :
    Sym ≃ₐ[κ] grR :=
  AlgEquiv.ofBijective (SymmetricAlgebra.lift associatedGradedDegreeOneCotangentLinear)
    (by
    sorry)

@[simp] theorem
    regularLocalRing_associatedGraded_algEquiv_symmetricAlgebraCotangentSpace_ι_toCotangent
    (x : maximalIdeal R) :
    regularLocalRing_associatedGraded_algEquiv_symmetricAlgebraCotangentSpace
        (SymmetricAlgebra.ι κ (CotangentSpace R) ((maximalIdeal R).toCotangent x)) =
      idealAssociatedGradedDegreeOne x := by
  simp [regularLocalRing_associatedGraded_algEquiv_symmetricAlgebraCotangentSpace]

/-- Lemma 10.106.1, source-facing form: if `x` is a regular system of parameters of length `d`,
then the associated graded ring `grR` is the polynomial `κ`-algebra on the degree-one classes of
the `x i`. -/
noncomputable def
    regularLocalRing_associatedGraded_algEquiv_mvPolynomial_of_regularSystemOfParameters
    {x : Fin d → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) :
    P ≃ₐ[κ] grR :=
  (SymmetricAlgebra.equivMvPolynomial (regularSystemOfParameters_cotangentBasis hx)).symm.trans
    regularLocalRing_associatedGraded_algEquiv_symmetricAlgebraCotangentSpace

@[simp] theorem
    regularLocalRing_associatedGraded_algEquiv_mvPolynomial_of_regularSystemOfParameters_X
    {x : Fin d → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) (i : Fin d) :
    regularLocalRing_associatedGraded_algEquiv_mvPolynomial_of_regularSystemOfParameters hx
        (MvPolynomial.X i) =
      idealAssociatedGradedDegreeOne (x i) := by
  simp [regularLocalRing_associatedGraded_algEquiv_mvPolynomial_of_regularSystemOfParameters,
    regularSystemOfParameters_cotangentBasis_apply]

end
