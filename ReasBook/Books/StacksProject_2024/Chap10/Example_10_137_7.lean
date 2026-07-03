import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial

attribute [local instance high] Semiring.toModule Algebra.toModule

universe u

namespace Algebra

variable (R : Type u) [CommRing R]

/-- The original variables `x₁, …, x_c, x_{c+1}, …, x_n` occurring in the equations `fᵢ`. -/
abbrev SmoothExampleBaseVars (c m : ℕ) : Type := Sum (Fin c) (Fin m)

/-- The reordered variables `x₁, …, x_c, x_{n+1}, x_{c+1}, …, x_n`. -/
abbrev SmoothExampleVars (c m : ℕ) : Type := Sum (Fin c) (Sum Unit (Fin m))

/-- The relation indices `f₁, …, f_c` together with the inverse-Jacobian relation. -/
abbrev SmoothExampleRelations (c : ℕ) : Type := Sum (Fin c) Unit

/-- The new variable `x_{n + 1}` adjoining an inverse to the Jacobian determinant. -/
abbrev smoothExampleInverseVar (c m : ℕ) : SmoothExampleVars c m := Sum.inr (Sum.inl ())

/-- The inclusion of the original variables into the reordered variable set, skipping the new
inverse-Jacobian variable. -/
def smoothExampleBaseVarInclusion (c m : ℕ) :
    SmoothExampleBaseVars c m → SmoothExampleVars c m
  | Sum.inl i => Sum.inl i
  | Sum.inr i => Sum.inr (Sum.inr i)

/-- The Jacobian determinant of `f₁, …, f_c` with respect to the first `c` variables. -/
noncomputable def smoothExampleJacobian (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    MvPolynomial (SmoothExampleBaseVars c m) R :=
  Matrix.det fun i j ↦ MvPolynomial.pderiv (Sum.inl i) (f j)

/-- The reordered defining relations `f₁, …, f_c, h`, where `h` expresses that the new variable is
an inverse to the Jacobian determinant. -/
noncomputable def smoothExampleRelation (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    SmoothExampleRelations c → MvPolynomial (SmoothExampleVars c m) R
  | Sum.inl i => rename (smoothExampleBaseVarInclusion c m) (f i)
  | Sum.inr _ =>
      rename (smoothExampleBaseVarInclusion c m) (smoothExampleJacobian R c m f) *
        X (smoothExampleInverseVar c m) - 1

/-- The explicit quotient ring from Example 10.137.7. -/
noncomputable abbrev smoothExampleQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) : Type u :=
  MvPolynomial (SmoothExampleVars c m) R ⧸
    Ideal.span (Set.range (smoothExampleRelation R c m f))

/-- The inverse permutation sending the source-facing variable order to the canonical composition
order where the localization variable comes first. -/
private def smoothExampleVarEquiv (c m : ℕ) :
    SmoothExampleVars c m ≃ Sum Unit (SmoothExampleBaseVars c m) where
  toFun
    | Sum.inl i => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inl u) => Sum.inl u
    | Sum.inr (Sum.inr i) => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl u => Sum.inr (Sum.inl u)
    | Sum.inr (Sum.inl i) => Sum.inl i
    | Sum.inr (Sum.inr i) => Sum.inr (Sum.inr i)
  left_inv := by
    intro x
    cases x with
    | inl i => rfl
    | inr x =>
        cases x with
        | inl u => rfl
        | inr i => rfl
  right_inv := by
    intro x
    cases x with
    | inl u => rfl
    | inr x =>
        cases x with
        | inl i => rfl
        | inr i => rfl

/-- The inverse permutation sending the source-facing relation order `(f₁, …, f_c, h)` to the
canonical composition order `(h, f₁, …, f_c)`. -/
private def smoothExampleRelEquiv (c : ℕ) :
    SmoothExampleRelations c ≃ Sum Unit (Fin c) :=
  Equiv.sumComm (Fin c) Unit

/-- The quotient by the equations `f₁, …, f_c` before adjoining the inverse Jacobian variable. -/
private noncomputable abbrev smoothExampleBaseQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) : Type u :=
  MvPolynomial (SmoothExampleBaseVars c m) R ⧸ Ideal.span (Set.range f)

/-- The canonical pre-submersive presentation of the quotient by `f₁, …, f_c`, using the first
`c` variables to compute the Jacobian. -/
private noncomputable abbrev smoothExampleBasePresentation (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    PreSubmersivePresentation R (smoothExampleBaseQuotient R c m f)
      (SmoothExampleBaseVars c m) (Fin c) :=
  PreSubmersivePresentation.naive Sum.inl Sum.inl_injective

/-- The canonical localized submersive presentation obtained by adjoining an inverse to the
Jacobian determinant in the quotient by `f₁, …, f_c`, then reordering variables and relations into
the source-facing order. -/
private noncomputable def smoothExampleRawPresentation (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    SubmersivePresentation R
      (Localization.Away (smoothExampleBasePresentation R c m f).jacobian)
      (SmoothExampleVars c m) (SmoothExampleRelations c) := by
  let P := smoothExampleBasePresentation R c m f
  letI : Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f) :=
    Semiring.toModule
  letI : DistribMulAction (smoothExampleBaseQuotient R c m f)
      (smoothExampleBaseQuotient R c m f) :=
    { (Semiring.toModule :
        Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f)) with }
  let Q :
      SubmersivePresentation
        (smoothExampleBaseQuotient R c m f)
        (Localization.Away P.jacobian) Unit Unit :=
    SubmersivePresentation.localizationAway (Localization.Away P.jacobian) P.jacobian
  let PQ :
      SubmersivePresentation R (Localization.Away P.jacobian)
        (Sum Unit (SmoothExampleBaseVars c m)) (Sum Unit (Fin c)) :=
    { toPreSubmersivePresentation :=
        PreSubmersivePresentation.comp Q.toPreSubmersivePresentation P
      jacobian_isUnit := by
        have hP :
            IsUnit
              (algebraMap (smoothExampleBaseQuotient R c m f) (Localization.Away P.jacobian)
                P.jacobian) :=
          IsLocalization.map_units _ (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
        have hQ :
            IsUnit
              ((algebraMap (smoothExampleBaseQuotient R c m f) (Localization.Away P.jacobian)
                  P.jacobian) * Q.jacobian) :=
          hP.mul Q.jacobian_isUnit
        change IsUnit
          (PreSubmersivePresentation.comp Q.toPreSubmersivePresentation P).jacobian
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def]
        exact hQ }
  simpa [P] using PQ.reindex (smoothExampleVarEquiv c m) (smoothExampleRelEquiv c)

/-- The polynomial map sending the original variables to their images in the explicit reordered
quotient. -/
private noncomputable def smoothExampleBaseToQuotientPolynomial (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    MvPolynomial (SmoothExampleBaseVars c m) R →ₐ[R] smoothExampleQuotient R c m f :=
  aeval fun i ↦ Ideal.Quotient.mk _ (X (smoothExampleBaseVarInclusion c m i))

private lemma smoothExampleBaseToQuotientPolynomial_mem (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    ∀ p : MvPolynomial (SmoothExampleBaseVars c m) R,
      p ∈ Ideal.span (Set.range f) →
        smoothExampleBaseToQuotientPolynomial R c m f p = 0 := by
  sorry

/-- The canonical map from the base quotient by `f₁, …, f_c` to the explicit quotient of Example
10.137.7. -/
private noncomputable def smoothExampleBaseToQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleBaseQuotient R c m f →ₐ[R] smoothExampleQuotient R c m f :=
  Ideal.Quotient.liftₐ _ (smoothExampleBaseToQuotientPolynomial R c m f)
    (smoothExampleBaseToQuotientPolynomial_mem R c m f)

private lemma smoothExampleBaseToQuotient_apply_mk (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R)
    (p : MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleBaseToQuotient R c m f (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (rename (smoothExampleBaseVarInclusion c m) p) := by
  sorry

private noncomputable abbrev smoothExampleBaseJacobianClass (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleBaseQuotient R c m f :=
  algebraMap _ _ (smoothExampleJacobian R c m f)

private noncomputable abbrev smoothExampleInverseVarClass (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleQuotient R c m f :=
  Ideal.Quotient.mk _ (X (smoothExampleInverseVar c m))

private lemma smoothExampleBaseToQuotient_jacobian_mul_inverseVar (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleBaseToQuotient R c m f (smoothExampleBaseJacobianClass R c m f) *
      smoothExampleInverseVarClass R c m f = 1 := by
  sorry

private lemma smoothExampleBaseJacobian_isUnit_in_quotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    IsUnit (smoothExampleBaseToQuotient R c m f (smoothExampleBaseJacobianClass R c m f)) := by
  sorry

/-- The canonical algebra map from the quotient by `f₁, …, f_c` to its localization away from the
Jacobian class. -/
private noncomputable def smoothExampleBaseToLocalization (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleBaseQuotient R c m f →ₐ[R]
      Localization.Away (smoothExampleBaseJacobianClass R c m f) where
  toRingHom := algebraMap _ _
  commutes' r := by
    letI : Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f) :=
      Semiring.toModule
    letI : DistribMulAction (smoothExampleBaseQuotient R c m f)
        (smoothExampleBaseQuotient R c m f) :=
      { (Semiring.toModule :
          Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f)) with }
    exact
    IsScalarTower.algebraMap_apply R
      (smoothExampleBaseQuotient R c m f)
      (Localization.Away (smoothExampleBaseJacobianClass R c m f)) r

/-- The canonical map from the localization away from the Jacobian class to the explicit quotient
of Example 10.137.7. -/
private noncomputable def smoothExampleLocalizationToQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    Localization.Away (smoothExampleBaseJacobianClass R c m f) →ₐ[R]
      smoothExampleQuotient R c m f where
  toRingHom :=
    Localization.awayLift (smoothExampleBaseToQuotient R c m f).toRingHom
      (smoothExampleBaseJacobianClass R c m f)
      (smoothExampleBaseJacobian_isUnit_in_quotient R c m f)
  commutes' r := by
    change
      Localization.awayLift (smoothExampleBaseToQuotient R c m f).toRingHom
        (smoothExampleBaseJacobianClass R c m f)
        (smoothExampleBaseJacobian_isUnit_in_quotient R c m f)
        (algebraMap _ _ (algebraMap R (smoothExampleBaseQuotient R c m f) r)) = _
    rw [← RingHom.comp_apply]
    rw [IsLocalization.Away.lift_comp]
    exact (smoothExampleBaseToQuotient R c m f).commutes r

private lemma smoothExampleLocalizationToQuotient_comp_base (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleLocalizationToQuotient R c m f).comp
      (smoothExampleBaseToLocalization R c m f) =
      smoothExampleBaseToQuotient R c m f := by
  sorry

private noncomputable def smoothExampleQuotientToLocalizationVar (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    SmoothExampleVars c m →
      Localization.Away (smoothExampleBaseJacobianClass R c m f)
  | Sum.inl i =>
      algebraMap (smoothExampleBaseQuotient R c m f)
        (Localization.Away (smoothExampleBaseJacobianClass R c m f))
        (Ideal.Quotient.mk _ (X (Sum.inl i)))
  | Sum.inr (Sum.inl _) =>
      IsLocalization.Away.invSelf (smoothExampleBaseJacobianClass R c m f)
  | Sum.inr (Sum.inr i) =>
      algebraMap (smoothExampleBaseQuotient R c m f)
        (Localization.Away (smoothExampleBaseJacobianClass R c m f))
        (Ideal.Quotient.mk _ (X (Sum.inr i)))

/-- The polynomial map defining the comparison from the explicit quotient to the localization away
from the Jacobian class. -/
private noncomputable def smoothExampleQuotientToLocalizationPolynomial (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    MvPolynomial (SmoothExampleVars c m) R →ₐ[R]
      Localization.Away (smoothExampleBaseJacobianClass R c m f) :=
  aeval (smoothExampleQuotientToLocalizationVar R c m f)

private lemma smoothExampleQuotientToLocalizationPolynomial_mem (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    ∀ p : MvPolynomial (SmoothExampleVars c m) R,
      p ∈ Ideal.span (Set.range (smoothExampleRelation R c m f)) →
        smoothExampleQuotientToLocalizationPolynomial R c m f p = 0 := by
  sorry

/-- The canonical map from the explicit quotient of Example 10.137.7 to the localization away from
the Jacobian class in the base quotient. -/
private noncomputable def smoothExampleQuotientToLocalization (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleQuotient R c m f →ₐ[R]
      Localization.Away (smoothExampleBaseJacobianClass R c m f) :=
  Ideal.Quotient.liftₐ _ (smoothExampleQuotientToLocalizationPolynomial R c m f)
    (smoothExampleQuotientToLocalizationPolynomial_mem R c m f)

private lemma smoothExampleQuotientToLocalization_apply_mk (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R)
    (p : MvPolynomial (SmoothExampleVars c m) R) :
    smoothExampleQuotientToLocalization R c m f (Ideal.Quotient.mk _ p) =
      smoothExampleQuotientToLocalizationPolynomial R c m f p := by
  sorry

private lemma smoothExampleQuotientToLocalization_comp_baseToQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleQuotientToLocalization R c m f).comp
      (smoothExampleBaseToQuotient R c m f) =
      smoothExampleBaseToLocalization R c m f := by
  sorry

private lemma smoothExampleLocalizationToQuotient_invSelf (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleLocalizationToQuotient R c m f
        (IsLocalization.Away.invSelf (smoothExampleBaseJacobianClass R c m f)) =
      smoothExampleInverseVarClass R c m f := by
  sorry

private lemma smoothExampleLocalization_quotient_roundtrip (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleQuotientToLocalization R c m f).comp
      (smoothExampleLocalizationToQuotient R c m f) =
      AlgHom.id R _ := by
  sorry

private lemma smoothExampleQuotient_localization_roundtrip (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleLocalizationToQuotient R c m f).comp
      (smoothExampleQuotientToLocalization R c m f) =
      AlgHom.id R _ := by
  sorry

private noncomputable def smoothExampleLocalizationEquiv (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    Localization.Away (smoothExampleBaseJacobianClass R c m f) ≃ₐ[R]
      smoothExampleQuotient R c m f :=
  AlgEquiv.ofAlgHom
    (smoothExampleLocalizationToQuotient R c m f)
    (smoothExampleQuotientToLocalization R c m f)
    (smoothExampleQuotient_localization_roundtrip R c m f)
    (smoothExampleLocalization_quotient_roundtrip R c m f)

private lemma smoothExampleBasePresentation_jacobian (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleBasePresentation R c m f).jacobian =
      smoothExampleBaseJacobianClass R c m f := by
  sorry

/-- The submersive presentation on the explicit quotient model of Example 10.137.7. -/
private noncomputable def smoothExamplePresentation (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    SubmersivePresentation R (smoothExampleQuotient R c m f)
      (SmoothExampleVars c m) (SmoothExampleRelations c) :=
  let P :
      SubmersivePresentation R
        (Localization.Away (smoothExampleBaseJacobianClass R c m f))
        (SmoothExampleVars c m) (SmoothExampleRelations c) := by
      exact (smoothExampleBasePresentation_jacobian R c m f) ▸
        smoothExampleRawPresentation R c m f
  P.ofAlgEquiv (smoothExampleLocalizationEquiv R c m f)

-- Proof sketch: start from the canonical pre-submersive presentation of
-- `R[x₁, …, x_n] / (f₁, …, f_c)`, localize away its Jacobian determinant, and then transport the
-- resulting submersive presentation to the explicit reordered quotient by its quotient equivalence.
/-- Example 10.137.7: after ordering the variables as `x₁, …, x_c, x_{n+1}, x_{c+1}, …, x_n`,
the quotient by `f₁, …, f_c` and the inverse-Jacobian relation is a standard smooth `R`-algebra.
-/
theorem jacobian_inverted_quotient_isStandardSmooth (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    IsStandardSmooth R
      (MvPolynomial (SmoothExampleVars c m) R ⧸
        Ideal.span (Set.range (smoothExampleRelation R c m f))) := by
  simpa [smoothExampleQuotient] using
    (smoothExamplePresentation R c m f).isStandardSmooth

end Algebra
