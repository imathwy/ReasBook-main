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
  -- It is enough to check the generators `f i`; the remaining ideal operations are
  -- preserved by the algebra map to the quotient.
  intro p hp
  induction hp using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨i, rfl⟩
      have hmem : (rename (smoothExampleBaseVarInclusion c m) (f i)) ∈
          Ideal.span (Set.range (smoothExampleRelation R c m f)) :=
        Ideal.subset_span ⟨Sum.inl i, rfl⟩
      have hzero : Ideal.Quotient.mk
          (Ideal.span (Set.range (smoothExampleRelation R c m f)))
          (rename (smoothExampleBaseVarInclusion c m) (f i)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      have heval :
          smoothExampleBaseToQuotientPolynomial R c m f (f i) =
            Ideal.Quotient.mk (Ideal.span (Set.range (smoothExampleRelation R c m f)))
              (rename (smoothExampleBaseVarInclusion c m) (f i)) := by
        let I : Ideal (MvPolynomial (SmoothExampleVars c m) R) :=
          Ideal.span (Set.range (smoothExampleRelation R c m f))
        have hmk := congrFun (congrArg DFunLike.coe
          (MvPolynomial.aeval_unique (Ideal.Quotient.mkₐ R I)))
          ((rename (smoothExampleBaseVarInclusion c m)) (f i))
        have hrename := (MvPolynomial.aeval_rename (smoothExampleBaseVarInclusion c m)
          (fun x ↦ (Ideal.Quotient.mkₐ R I) (X x)) (f i)).symm
        simpa [smoothExampleBaseToQuotientPolynomial, Function.comp, I,
          Ideal.Quotient.mkₐ_eq_mk] using hrename.trans hmk.symm
      exact heval.trans hzero
  | zero =>
      simp
  | add x y hx hy hx0 hy0 =>
      simp [hx0, hy0]
  | smul a x hx hx0 =>
      simp [hx0]

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
  -- Reduce the quotient lift to the polynomial algebra map and then identify that
  -- map with quotienting after variable renaming.
  rw [smoothExampleBaseToQuotient, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  let I : Ideal (MvPolynomial (SmoothExampleVars c m) R) :=
    Ideal.span (Set.range (smoothExampleRelation R c m f))
  have hmk := congrFun (congrArg DFunLike.coe
    (MvPolynomial.aeval_unique (Ideal.Quotient.mkₐ R I)))
    ((rename (smoothExampleBaseVarInclusion c m)) p)
  have hrename := (MvPolynomial.aeval_rename (smoothExampleBaseVarInclusion c m)
    (fun x ↦ (Ideal.Quotient.mkₐ R I) (X x)) p).symm
  simpa [smoothExampleBaseToQuotientPolynomial, Function.comp, I, Ideal.Quotient.mkₐ_eq_mk]
    using hrename.trans hmk.symm

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
  -- The extra defining relation says precisely that the Jacobian class multiplied
  -- by the new variable is one in the explicit quotient.
  have hzero : Ideal.Quotient.mk
      (Ideal.span (Set.range (smoothExampleRelation R c m f)))
      (smoothExampleRelation R c m f (Sum.inr ())) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨Sum.inr (), rfl⟩)
  have hrel : Ideal.Quotient.mk
      (Ideal.span (Set.range (smoothExampleRelation R c m f)))
      (rename (smoothExampleBaseVarInclusion c m) (smoothExampleJacobian R c m f) *
        X (smoothExampleInverseVar c m)) = 1 := by
    simpa [smoothExampleRelation] using sub_eq_zero.mp hzero
  simpa [smoothExampleBaseJacobianClass, smoothExampleBaseToQuotient_apply_mk,
    smoothExampleInverseVarClass, Ideal.Quotient.mkₐ_eq_mk] using hrel

private lemma smoothExampleBaseJacobian_isUnit_in_quotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    IsUnit (smoothExampleBaseToQuotient R c m f (smoothExampleBaseJacobianClass R c m f)) := by
  -- The inverse variable supplies both inverse identities because the quotient ring
  -- is commutative.
  exact isUnit_iff_exists.mpr
    ⟨smoothExampleInverseVarClass R c m f,
      smoothExampleBaseToQuotient_jacobian_mul_inverseVar R c m f,
      by simpa [mul_comm] using smoothExampleBaseToQuotient_jacobian_mul_inverseVar R c m f⟩

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
  -- The localization lift was defined to extend the base quotient map.
  ext x
  simp [smoothExampleLocalizationToQuotient, smoothExampleBaseToLocalization]

/-- Helper for Chap10 Example 10 137 7: the localization-to-quotient comparison map agrees with
the base quotient map on elements coming from the localized base quotient. -/
private lemma smoothExampleLocalizationToQuotient_algebraMap (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R)
    (x : smoothExampleBaseQuotient R c m f) :
    smoothExampleLocalizationToQuotient R c m f
        ((algebraMap (smoothExampleBaseQuotient R c m f)
          (Localization.Away (smoothExampleBaseJacobianClass R c m f))) x) =
      smoothExampleBaseToQuotient R c m f x := by
  -- Evaluate the composition identity pointwise and unfold only the local wrapper
  -- around the canonical algebra map.
  have happ := congrFun (congrArg DFunLike.coe
    (smoothExampleLocalizationToQuotient_comp_base R c m f)) x
  simpa [smoothExampleBaseToLocalization] using happ

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
  -- First record the representative computation for base polynomials, then check
  -- the two kinds of defining relations.
  letI : Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f) :=
    Semiring.toModule
  letI : DistribMulAction (smoothExampleBaseQuotient R c m f)
      (smoothExampleBaseQuotient R c m f) :=
    { (Semiring.toModule :
        Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f)) with }
  have hrename (p : MvPolynomial (SmoothExampleBaseVars c m) R) :
      (smoothExampleQuotientToLocalizationPolynomial R c m f)
        (rename (smoothExampleBaseVarInclusion c m) p) =
      algebraMap (smoothExampleBaseQuotient R c m f)
        (Localization.Away (smoothExampleBaseJacobianClass R c m f))
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) p) := by
    have hcomp :
        (smoothExampleQuotientToLocalizationPolynomial R c m f).comp
          (rename (smoothExampleBaseVarInclusion c m)) =
        (smoothExampleBaseToLocalization R c m f).comp
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) := by
      apply MvPolynomial.algHom_ext
      intro i
      cases i <;>
        simp [smoothExampleQuotientToLocalizationPolynomial,
          smoothExampleQuotientToLocalizationVar, smoothExampleBaseVarInclusion,
          smoothExampleBaseToLocalization, Ideal.Quotient.mkₐ_eq_mk]
    have happ := congrFun (congrArg DFunLike.coe hcomp) p
    simpa [smoothExampleBaseToLocalization, Ideal.Quotient.mkₐ_eq_mk] using happ
  intro p hp
  induction hp using Submodule.span_induction with
  | mem q hq =>
      rcases hq with ⟨j, rfl⟩
      cases j with
      | inl i =>
          have hbase : (Ideal.Quotient.mk (Ideal.span (Set.range f)) (f i) :
              smoothExampleBaseQuotient R c m f) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
          rw [smoothExampleRelation, hrename]
          simpa using congrArg (algebraMap (smoothExampleBaseQuotient R c m f)
            (Localization.Away (smoothExampleBaseJacobianClass R c m f))) hbase
      | inr u =>
          cases u
          have hunit := IsLocalization.Away.mul_invSelf
            (S := Localization.Away (smoothExampleBaseJacobianClass R c m f))
            (smoothExampleBaseJacobianClass R c m f)
          rw [smoothExampleRelation, map_sub, map_mul, hrename,
            smoothExampleQuotientToLocalizationPolynomial, MvPolynomial.aeval_X, map_one]
          simpa [smoothExampleQuotientToLocalizationPolynomial,
            smoothExampleQuotientToLocalizationVar, smoothExampleInverseVar,
            smoothExampleBaseJacobianClass, Ideal.Quotient.mkₐ_eq_mk]
            using sub_eq_zero.mpr hunit
  | zero =>
      simp
  | add x y hx hy hx0 hy0 =>
      simp [hx0, hy0]
  | smul a x hx hx0 =>
      simp [hx0]

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
  -- This is the defining computation rule for the quotient lift.
  simp [smoothExampleQuotientToLocalization, Ideal.Quotient.liftₐ_apply,
    Ideal.Quotient.lift_mk]

private lemma smoothExampleQuotientToLocalization_comp_baseToQuotient (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleQuotientToLocalization R c m f).comp
      (smoothExampleBaseToQuotient R c m f) =
      smoothExampleBaseToLocalization R c m f := by
  -- Both maps from the base quotient agree on polynomial generators.
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;>
    simp [smoothExampleBaseToQuotient_apply_mk, smoothExampleQuotientToLocalization_apply_mk,
      smoothExampleQuotientToLocalizationPolynomial, smoothExampleQuotientToLocalizationVar,
      smoothExampleBaseToLocalization, smoothExampleBaseVarInclusion, Ideal.Quotient.mkₐ_eq_mk]

private lemma smoothExampleLocalizationToQuotient_invSelf (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    smoothExampleLocalizationToQuotient R c m f
        (IsLocalization.Away.invSelf (smoothExampleBaseJacobianClass R c m f)) =
      smoothExampleInverseVarClass R c m f := by
  -- Both candidates are inverses to the image of the Jacobian in the explicit
  -- quotient, so cancel by the unit proved above.
  refine (smoothExampleBaseJacobian_isUnit_in_quotient R c m f).mul_left_cancel ?_
  have hmap :
      (smoothExampleLocalizationToQuotient R c m f)
        ((algebraMap (smoothExampleBaseQuotient R c m f)
            (Localization.Away (smoothExampleBaseJacobianClass R c m f)))
            (smoothExampleBaseJacobianClass R c m f) *
          IsLocalization.Away.invSelf (smoothExampleBaseJacobianClass R c m f)) = 1 := by
    simpa using congrArg (smoothExampleLocalizationToQuotient R c m f)
      (IsLocalization.Away.mul_invSelf (smoothExampleBaseJacobianClass R c m f))
  have hcomp :
      (smoothExampleLocalizationToQuotient R c m f)
        ((algebraMap (smoothExampleBaseQuotient R c m f)
            (Localization.Away (smoothExampleBaseJacobianClass R c m f)))
            (smoothExampleBaseJacobianClass R c m f)) =
      smoothExampleBaseToQuotient R c m f (smoothExampleBaseJacobianClass R c m f) := by
    simpa using smoothExampleLocalizationToQuotient_algebraMap R c m f
      (smoothExampleBaseJacobianClass R c m f)
  have hleft : smoothExampleBaseToQuotient R c m f (smoothExampleBaseJacobianClass R c m f) *
        smoothExampleLocalizationToQuotient R c m f
          (IsLocalization.Away.invSelf (smoothExampleBaseJacobianClass R c m f)) = 1 := by
    rw [map_mul] at hmap
    rw [hcomp] at hmap
    exact hmap
  exact hleft.trans (smoothExampleBaseToQuotient_jacobian_mul_inverseVar R c m f).symm

private lemma smoothExampleLocalization_quotient_roundtrip (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleQuotientToLocalization R c m f).comp
      (smoothExampleLocalizationToQuotient R c m f) =
      AlgHom.id R _ := by
  -- A map out of the localization is determined by its restriction to the base
  -- quotient.  The two comparison lemmas identify that restriction with the identity.
  letI : Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f) :=
    Semiring.toModule
  letI : DistribMulAction (smoothExampleBaseQuotient R c m f)
      (smoothExampleBaseQuotient R c m f) :=
    { (Semiring.toModule :
        Module (smoothExampleBaseQuotient R c m f) (smoothExampleBaseQuotient R c m f)) with }
  apply IsLocalization.algHom_ext (Submonoid.powers (smoothExampleBaseJacobianClass R c m f))
  · have hbaseAlg :
        algHom R (smoothExampleBaseQuotient R c m f)
            (Localization.Away (smoothExampleBaseJacobianClass R c m f)) =
          smoothExampleBaseToLocalization R c m f := by
        ext x
        rfl
    rw [hbaseAlg, AlgHom.comp_assoc, smoothExampleLocalizationToQuotient_comp_base,
      smoothExampleQuotientToLocalization_comp_baseToQuotient]
    rfl

private lemma smoothExampleQuotient_localization_roundtrip (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    (smoothExampleLocalizationToQuotient R c m f).comp
      (smoothExampleQuotientToLocalization R c m f) =
      AlgHom.id R _ := by
  -- A quotient map is determined by its values on polynomial generators; the base
  -- variables use the algebra-map computation and the new variable uses `invSelf`.
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with i | (_ | i)
  · simp [smoothExampleQuotientToLocalization_apply_mk,
      smoothExampleQuotientToLocalizationPolynomial, smoothExampleQuotientToLocalizationVar,
      smoothExampleLocalizationToQuotient_algebraMap,
      smoothExampleBaseToQuotient_apply_mk, smoothExampleBaseVarInclusion]
  · simp [smoothExampleQuotientToLocalization_apply_mk,
      smoothExampleQuotientToLocalizationPolynomial, smoothExampleQuotientToLocalizationVar,
      smoothExampleLocalizationToQuotient_invSelf, smoothExampleInverseVarClass,
      smoothExampleInverseVar]
  · simp [smoothExampleQuotientToLocalization_apply_mk,
      smoothExampleQuotientToLocalizationPolynomial, smoothExampleQuotientToLocalizationVar,
      smoothExampleLocalizationToQuotient_algebraMap,
      smoothExampleBaseToQuotient_apply_mk, smoothExampleBaseVarInclusion]

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
  -- The naive presentation has Jacobian matrix `(pderiv (Sum.inl i) (f j))`;
  -- its determinant is exactly the polynomial `smoothExampleJacobian`.
  classical
  have hmatrix : (smoothExampleBasePresentation R c m f).jacobiMatrix =
      (fun i j ↦ MvPolynomial.pderiv (Sum.inl i) (f j)) := by
    ext i j
    simp [smoothExampleBasePresentation]
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hmatrix]
  exact rfl

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
/-- Chap10 Example 10 137 7: after ordering the variables as `x₁, …, x_c, x_{n+1}, x_{c+1}, …, x_n`,
the quotient by `f₁, …, f_c` and the inverse-Jacobian relation is a standard smooth `R`-algebra.
-/
@[stacks 00T8]
theorem jacobian_inverted_quotient_isStandardSmooth (c m : ℕ)
    (f : Fin c → MvPolynomial (SmoothExampleBaseVars c m) R) :
    IsStandardSmooth R
      (MvPolynomial (SmoothExampleVars c m) R ⧸
        Ideal.span (Set.range (smoothExampleRelation R c m f))) := by
  simpa [smoothExampleQuotient] using
    (smoothExamplePresentation R c m f).isStandardSmooth

end Algebra
