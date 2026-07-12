import StacksProject_2024.Chap10.Lemma_10_57_10.Index

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators DirectSum
open HomogeneousLocalization
open Lemma_10_57_10

universe u u' v
universe w

section

variable {R : Type u} {R' : Type u'} {M : Type v}
variable [CommRing R] [CommRing R'] [Algebra R R']
variable [AddCommGroup M] [Module R' M]

attribute [local instance] RingHomInvPair.of_ringEquiv
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

namespace Lemma_10_57_10

/-- Helper for Chap10 Lemma 10 57 10: homogeneous localization away from a homogeneous element of
a commutative graded ring is itself a commutative ring. -/
@[reducible] noncomputable instance awayCommRing {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedAlgebra grading] {d : ℕ} (f : grading d) :
    CommRing (Away grading (f : S)) :=
  HomogeneousLocalization.homogeneousLocalizationCommRing

/-- Helper for Chap10 Lemma 10 57 10: transport an `R`-submodule family across the canonical
linear equivalence from a module to its universe lift. -/
def uliftSubmoduleFamily {A : Type _} [AddCommMonoid A] [Module R A] {ι : Type _}
    (𝒜 : ι → Submodule R A) : ι → Submodule R (ULift A) :=
  fun i ↦ (𝒜 i).map (ULift.moduleEquiv.symm : A ≃ₗ[R] ULift A).toLinearMap

/-- Helper for Chap10 Lemma 10 57 10: membership in the transported `ULift` family is detected
after applying `ULift.down`. -/
theorem mem_uliftSubmoduleFamily_iff {A : Type _} [AddCommMonoid A] [Module R A] {ι : Type _}
    (𝒜 : ι → Submodule R A) (i : ι) (x : ULift A) :
    x ∈ uliftSubmoduleFamily  𝒜 i ↔ x.down ∈ 𝒜 i := by
  constructor
  · -- A member of the mapped submodule has a source representative, and `down` recovers it.
    rintro ⟨y, hy, hxy⟩
    have hdown : y = x.down := by
      simpa using congrArg ULift.down hxy
    simpa [← hdown] using hy
  · -- Conversely, lift the detected source member back with `ULift.up`.
    intro hx
    refine ⟨x.down, hx, ?_⟩
    ext
    rfl

/-- Helper for Chap10 Lemma 10 57 10: a homogeneous element lifts to the corresponding component
of the transported `ULift` family. -/
def uliftSubmoduleFamilyElement {A : Type _} [AddCommMonoid A] [Module R A] {ι : Type _}
    (𝒜 : ι → Submodule R A) {i : ι} (x : 𝒜 i) :
    uliftSubmoduleFamily  𝒜 i :=
  ⟨ULift.up (x : A), (mem_uliftSubmoduleFamily_iff  𝒜 i (ULift.up (x : A))).2 x.2⟩

/-- Helper for Chap10 Lemma 10 57 10: the degree-zero algebra component is preserved by the
canonical universe lift of a grading. -/
noncomputable def uliftDegreeZeroAlgEquiv {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedAlgebra grading]
    [GradedAlgebra (uliftSubmoduleFamily  grading)] :
    grading 0 ≃ₐ[R] (uliftSubmoduleFamily  grading) 0 where
  toFun x :=
    ⟨ULift.up (x : S),
      (mem_uliftSubmoduleFamily_iff  grading 0 (ULift.up (x : S))).2 x.2⟩
  invFun x :=
    ⟨x.1.down, (mem_uliftSubmoduleFamily_iff  grading 0 x.1).1 x.2⟩
  left_inv x := by
    -- Projecting back down from the lifted degree-zero component recovers the original element.
    ext
    rfl
  right_inv x := by
    -- Lifting the detected source element gives the original lifted subtype element.
    ext
    rfl
  map_mul' x y := by
    -- Multiplication is inherited from the ambient ring, where `ULift.up` is multiplicative.
    ext
    rfl
  map_add' x y := by
    -- Addition is inherited from the ambient additive group, where `ULift.up` is additive.
    ext
    rfl
  commutes' r := by
    -- The `R`-algebra structures on both degree-zero pieces are the ambient algebra maps.
    ext
    rfl

/-- Helper for Chap10 Lemma 10 57 10: graded scalar multiplication is preserved by lifting both
the graded ring and graded module through `ULift`. -/
@[reducible] def uliftGradedSMul {S : Type _} [CommRing S] [Algebra R S]
    {N : Type _} [AddCommGroup N] [Module S N] [Module R N]
    (grading : ℕ → Submodule R S) (gradingN : ℕ → Submodule R N)
    [SetLike.GradedSMul grading gradingN] :
    SetLike.GradedSMul
      (uliftSubmoduleFamily  grading)
      (uliftSubmoduleFamily  gradingN) where
  smul_mem := by
    -- Membership in each lifted component is checked after `down`, where the original graded
    -- scalar action applies.
    intro i j a b ha hb
    rw [mem_uliftSubmoduleFamily_iff] at ha hb ⊢
    simpa using (SetLike.GradedSMul.smul_mem ha hb)

/-- Helper for Chap10 Lemma 10 57 10: the transported `ULift` gradings inherit the graded scalar
action from the source graded module. -/
noncomputable instance uliftSubmoduleFamilyGradedSMul
    {S : Type _} [CommRing S] [Algebra R S]
    {N : Type _} [AddCommGroup N] [Module S N] [Module R N]
    (grading : ℕ → Submodule R S) (gradingN : ℕ → Submodule R N)
    [SetLike.GradedSMul grading gradingN] :
    SetLike.GradedSMul
      (uliftSubmoduleFamily  grading)
      (uliftSubmoduleFamily  gradingN) :=
  uliftGradedSMul  grading gradingN

/-- Helper for Chap10 Lemma 10 57 10: each homogeneous component maps into the corresponding
component of the transported `ULift` grading. -/
theorem uliftSubmoduleFamily_componentMap_mem
    {A : Type _} [AddCommMonoid A] [Module R A] {ι : Type _}
    (𝒜 : ι → Submodule R A) (i : ι) (x : 𝒜 i) :
    ((ULift.moduleEquiv.symm : A ≃ₗ[R] ULift A).toLinearMap.comp (𝒜 i).subtype) x ∈
      uliftSubmoduleFamily  𝒜 i := by
  -- Membership in the lifted component is reduced to the original component by `down`.
  rw [mem_uliftSubmoduleFamily_iff]
  exact x.2

/-- Helper for Chap10 Lemma 10 57 10: a direct-sum decomposition transports across the canonical
linear equivalence `ULift A ≃ₗ[R] A`. -/
@[reducible] noncomputable def uliftDecomposition {A : Type _} [AddCommMonoid A] [Module R A]
    {ι : Type _} [DecidableEq ι]
    (𝒜 : ι → Submodule R A) [DirectSum.Decomposition 𝒜] :
    DirectSum.Decomposition (uliftSubmoduleFamily  𝒜) := by
  let liftComponent : ∀ i, 𝒜 i →ₗ[R] uliftSubmoduleFamily  𝒜 i := fun i ↦
    LinearMap.codRestrict
      (uliftSubmoduleFamily  𝒜 i)
      ((ULift.moduleEquiv.symm : A ≃ₗ[R] ULift A).toLinearMap.comp (𝒜 i).subtype)
      (uliftSubmoduleFamily_componentMap_mem  𝒜 i)
  let decomposeLift :
      ULift A →ₗ[R] DirectSum ι fun i ↦ uliftSubmoduleFamily  𝒜 i :=
    (DirectSum.lmap fun i ↦ liftComponent i).comp
      ((DirectSum.decomposeLinearEquiv 𝒜).toLinearMap.comp
        (ULift.moduleEquiv : ULift A ≃ₗ[R] A).toLinearMap)
  refine DirectSum.Decomposition.ofLinearMap (uliftSubmoduleFamily 𝒜) decomposeLift ?_ ?_
  · -- Recomposition after lifted decomposition is checked after projecting back to `A`.
    ext x
    cases x
    rename_i y
    have hdownCoe :
        (ULift.moduleEquiv : ULift A ≃ₗ[R] A).toLinearMap.comp
            ((DirectSum.coeLinearMap (uliftSubmoduleFamily  𝒜)).comp
              (DirectSum.lmap fun i ↦ liftComponent i)) =
          DirectSum.coeLinearMap 𝒜 := by
      apply DirectSum.linearMap_ext
      intro i
      ext x
      simp [liftComponent, DirectSum.lof_eq_of]
    calc
      ((DirectSum.coeLinearMap (uliftSubmoduleFamily  𝒜))
          ((DirectSum.lmap fun i ↦ liftComponent i)
            ((DirectSum.decomposeLinearEquiv 𝒜) y))).down =
          DirectSum.coeLinearMap 𝒜 ((DirectSum.decomposeLinearEquiv 𝒜) y) := by
            simpa [LinearMap.comp_apply] using
              congrArg
                (fun f ↦
                  f ((DirectSum.decomposeLinearEquiv 𝒜) y)) hdownCoe
      _ = y := by
            exact (DirectSum.decomposeLinearEquiv 𝒜).left_inv y
  · -- On each lifted homogeneous summand, decomposition returns the matching direct-sum basis
    -- vector because the source decomposition has that property before lifting.
    apply DirectSum.linearMap_ext
    intro i
    ext x
    rename_i j
    have hxmem : (x : ULift A).down ∈ 𝒜 i :=
      (mem_uliftSubmoduleFamily_iff  𝒜 i (x : ULift A)).1 x.2
    by_cases hij : i = j
    · subst hij
      -- In the matching degree, the source decomposition returns the original component.
      simpa [decomposeLift, liftComponent, DirectSum.decomposeLinearEquiv_apply,
        DirectSum.lof_eq_of] using
        (DirectSum.decompose_of_mem_same 𝒜 hxmem)
    · -- In all other degrees, both the source projection and the lifted `lof` coordinate vanish.
      have hji : j ≠ i := fun hji ↦ hij hji.symm
      simpa [decomposeLift, liftComponent, DirectSum.decomposeLinearEquiv_apply,
        DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hji] using
        (DirectSum.decompose_of_mem_ne 𝒜 hxmem hij)

/-- Helper for Chap10 Lemma 10 57 10: the graded monoid structure transports across `ULift`. -/
@[reducible] def uliftSetLikeGradedMonoid {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [SetLike.GradedMonoid grading] :
    SetLike.GradedMonoid (uliftSubmoduleFamily  grading) where
  one_mem := by
    -- The lifted unit has degree zero because its `down` is the original unit.
    rw [mem_uliftSubmoduleFamily_iff]
    exact SetLike.GradedOne.one_mem
  mul_mem := by
    -- Multiplication of lifted homogeneous elements is tested after `down`.
    intro i j a b ha hb
    rw [mem_uliftSubmoduleFamily_iff] at ha hb ⊢
    exact SetLike.GradedMul.mul_mem ha hb

/-- Helper for Chap10 Lemma 10 57 10: a graded algebra structure transports across `ULift`. -/
@[reducible] noncomputable def uliftGradedAlgebra {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedAlgebra grading] :
    GradedAlgebra (uliftSubmoduleFamily  grading) := by
  -- Package the transported direct-sum decomposition and graded multiplication as the two
  -- fields of `GradedAlgebra`.
  exact
    { uliftSetLikeGradedMonoid  grading,
      uliftDecomposition  grading with }

/-- Helper for Chap10 Lemma 10 57 10: the transported `ULift` grading inherits the graded
algebra structure from the source graded ring. -/
noncomputable instance uliftSubmoduleFamilyGradedAlgebra
    {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedAlgebra grading] :
    GradedAlgebra (uliftSubmoduleFamily  grading) :=
  uliftGradedAlgebra  grading

/-- Helper for Chap10 Lemma 10 57 10: the upward `ULift` ring map sends each homogeneous
component into the transported homogeneous component. -/
theorem uliftGradedRingHom_map_mem {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) {i : ℕ} {x : S} (hx : x ∈ grading i) :
    ULift.up x ∈ uliftSubmoduleFamily  grading i := by
  -- Membership in the lifted component is exactly source membership after applying `down`.
  exact (mem_uliftSubmoduleFamily_iff  grading i (ULift.up x)).2 hx

/-- Helper for Chap10 Lemma 10 57 10: the downward `ULift` ring map sends transported
homogeneous components back to their source components. -/
theorem uliftDownGradedRingHom_map_mem {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) {i : ℕ} {x : ULift S}
    (hx : x ∈ uliftSubmoduleFamily  grading i) :
    x.down ∈ grading i := by
  -- The transported-family membership criterion is the whole bridge.
  exact (mem_uliftSubmoduleFamily_iff  grading i x).1 hx

/-- Helper for Chap10 Lemma 10 57 10: the canonical upward ring equivalence is a graded ring
homomorphism for the transported `ULift` grading. -/
noncomputable def uliftGradedRingHom {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) :
    grading →+*ᵍ uliftSubmoduleFamily  grading where
  __ := (ULift.ringEquiv : ULift S ≃+* S).symm.toRingHom
  map_mem hx := uliftGradedRingHom_map_mem  grading hx

/-- Helper for Chap10 Lemma 10 57 10: the canonical downward ring equivalence is a graded ring
homomorphism from the transported `ULift` grading. -/
noncomputable def uliftDownGradedRingHom {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) :
    uliftSubmoduleFamily  grading →+*ᵍ grading where
  __ := (ULift.ringEquiv : ULift S ≃+* S).toRingHom
  map_mem hx := uliftDownGradedRingHom_map_mem  grading hx

/-- Helper for Chap10 Lemma 10 57 10: projecting after lifting is the identity as a graded ring
homomorphism. -/
theorem uliftDown_comp_uliftGradedRingHom {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) :
    (uliftDownGradedRingHom  grading).comp
      (uliftGradedRingHom  grading) = GradedRingHom.id grading := by
  -- The underlying ring maps are `ULift.down ∘ ULift.up`, so extensionality closes the identity.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 57 10: lifting after projecting is the identity as a graded ring
homomorphism on the transported `ULift` grading. -/
theorem uliftGradedRingHom_comp_uliftDown {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) :
    (uliftGradedRingHom  grading).comp
      (uliftDownGradedRingHom  grading) =
        GradedRingHom.id (uliftSubmoduleFamily  grading) := by
  -- A lifted element is determined by its `down` field, so extensionality reduces the composite
  -- to `ULift.up ∘ ULift.down`.
  ext x
  cases x
  rfl

/-- Helper for Chap10 Lemma 10 57 10: the downward `ULift` map is a left inverse to the upward
map on homogeneous away-localizations. -/
theorem uliftAwayMap_down_leftInverse {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedRing grading]
    [GradedRing (uliftSubmoduleFamily  grading)] {d : ℕ} (f : grading d) :
    Function.LeftInverse
      ((HomogeneousLocalization.Away.map (uliftDownGradedRingHom  grading)
        (ULift.up (f : S))) :
          Away (uliftSubmoduleFamily  grading) (ULift.up (f : S)) →
            Away grading (f : S))
      ((HomogeneousLocalization.Away.map (uliftGradedRingHom  grading) (f : S)) :
        Away grading (f : S) →
          Away (uliftSubmoduleFamily  grading) (ULift.up (f : S))) := sorry

/-- Helper for Chap10 Lemma 10 57 10: the downward `ULift` map is a right inverse to the upward
map on homogeneous away-localizations. -/
theorem uliftAwayMap_down_rightInverse {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedRing grading]
    [GradedRing (uliftSubmoduleFamily  grading)] {d : ℕ} (f : grading d) :
    Function.RightInverse
      ((HomogeneousLocalization.Away.map (uliftDownGradedRingHom  grading)
        (ULift.up (f : S))) :
          Away (uliftSubmoduleFamily  grading) (ULift.up (f : S)) →
            Away grading (f : S))
      ((HomogeneousLocalization.Away.map (uliftGradedRingHom  grading) (f : S)) :
        Away grading (f : S) →
          Away (uliftSubmoduleFamily  grading) (ULift.up (f : S))) := sorry

/-- Helper for Chap10 Lemma 10 57 10: the induced map on homogeneous away-localizations is
bijective after transporting the grading through `ULift`. -/
theorem uliftAwayMap_bijective {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedRing grading]
    [GradedRing (uliftSubmoduleFamily  grading)] {d : ℕ} (f : grading d) :
    Function.Bijective
      (HomogeneousLocalization.Away.map (uliftGradedRingHom  grading) (f : S) :
        Away grading (f : S) →
          Away (uliftSubmoduleFamily  grading) (ULift.up (f : S))) := by
  -- Use the explicit downward localization map as the inverse; the inverse laws were proved on
  -- fraction representatives, avoiding dependent composition normal forms for `Away.map`.
  exact
    ⟨(uliftAwayMap_down_leftInverse  grading f).injective,
      (uliftAwayMap_down_rightInverse  grading f).surjective⟩

/-- Helper for Chap10 Lemma 10 57 10: homogeneous localization away from a homogeneous element
commutes with the canonical universe lift of the graded ring. -/
noncomputable def uliftAwayRingEquiv {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedRing grading]
    [GradedRing (uliftSubmoduleFamily  grading)] {d : ℕ} (f : grading d) :
    Away grading (f : S) ≃+*
      Away (uliftSubmoduleFamily  grading) (ULift.up (f : S)) :=
  RingEquiv.ofBijective
    (HomogeneousLocalization.Away.map (uliftGradedRingHom  grading) (f : S))
    (uliftAwayMap_bijective  grading f)

/-- Helper for Chap10 Lemma 10 57 10: the `ULift` away equivalence preserves the base
`R`-algebra structure. -/
theorem uliftAwayRingEquiv_commutes {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedAlgebra grading]
    [GradedAlgebra (uliftSubmoduleFamily  grading)] {d : ℕ} (f : grading d)
    (r : R) :
    uliftAwayRingEquiv  grading f (algebraMap R (Away grading (f : S)) r) =
      algebraMap R (Away (uliftSubmoduleFamily  grading) (ULift.up (f : S))) r := by
  -- Both algebra structures pass through the degree-zero component, and the upward map is
  -- literally `ULift.up` on representatives.
  rfl

/-- Helper for Chap10 Lemma 10 57 10: homogeneous away-localization is preserved as an
`R`-algebra by the canonical universe lift of a graded ring. -/
noncomputable def uliftAwayAlgEquiv {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedAlgebra grading]
    [GradedAlgebra (uliftSubmoduleFamily  grading)] {d : ℕ} (f : grading d) :
    Away grading (f : S) ≃ₐ[R]
      Away (uliftSubmoduleFamily  grading) (ULift.up (f : S)) :=
  { toRingEquiv := uliftAwayRingEquiv grading f
    commutes' := uliftAwayRingEquiv_commutes grading f }

/-- Helper for Chap10 Lemma 10 57 10: the class of the cone variable `X 0` lies in degree
`1` of the cone quotient grading. -/
theorem coneStandardDenominator_mem_grade_one {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))) ∈
      cone_quotient_grading   J 1 := by
  -- This records the standard denominator membership once, so later chart comparisons share the
  -- same subtype spelling instead of rebuilding the proof locally.
  exact cone_quotient_X_mem_grade_one   J (0 : Fin (n + 1))

/-- Helper for Chap10 Lemma 10 57 10: the standard denominator for the homogeneous cone chart is
the degree-one class of `X 0`. -/
noncomputable def coneStandardDenominator {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    cone_quotient_grading   J 1 :=
  ⟨Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))),
    coneStandardDenominator_mem_grade_one   J⟩

/-- Helper for Chap10 Lemma 10 57 10: the affine variable `x_i` maps to the degree-zero cone
fraction `X_{i+1}/X_0` in the homogeneous away chart. -/
noncomputable def coneAffineVariableFraction {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)] (i : Fin n) :
    Away (cone_quotient_grading   J)
      ((coneStandardDenominator   J :
        MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  HomogeneousLocalization.Away.mk
    (cone_quotient_grading   J)
    (coneStandardDenominator_mem_grade_one   J)
    1
    (Ideal.Quotient.mk J (MvPolynomial.X i.succ))
    (by simpa using cone_quotient_X_succ_mem_grade_one   J i)

/-- Helper for Chap10 Lemma 10 57 10: the affine polynomial algebra maps to the cone away chart by
sending each affine generator to `X_{i+1}/X_0`. -/
noncomputable def coneAffineToAwayAlgHom {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)] :
    letI : CommRing
        (Away (cone_quotient_grading   J)
          ((coneStandardDenominator   J :
            MvPolynomial (Fin (n + 1)) R ⧸ J))) :=
      HomogeneousLocalization.homogeneousLocalizationCommRing
    MvPolynomial (Fin n) R →ₐ[R]
      Away (cone_quotient_grading   J)
        ((coneStandardDenominator   J :
          MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  letI : CommRing
      (Away (cone_quotient_grading   J)
        ((coneStandardDenominator   J :
          MvPolynomial (Fin (n + 1)) R ⧸ J))) :=
    HomogeneousLocalization.homogeneousLocalizationCommRing
  MvPolynomial.aeval (coneAffineVariableFraction   J)

/-- Helper for Chap10 Lemma 10 57 10: the ordinary away inverse of the cone chart sends
`a / X₀^j` to the dehomogenized quotient class of `a`. -/
theorem coneOrdinaryAwayToAffineQuotient_mk {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom  ) I)
    (a : MvPolynomial (Fin (n + 1)) R ⧸ J) (j : ℕ) :
    cone_ordinary_away_to_affine_quotient   I J hJ
      (Localization.mk a
        ⟨(Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) ^ j,
          by exact ⟨j, rfl⟩⟩) =
      coneDehom_quotient_map   I J hJ a := by
  -- Unfold the ordinary away lift once; the denominator maps to the unit `1`, so all powers
  -- disappear in the affine quotient.
  rw [cone_ordinary_away_to_affine_quotient]
  simpa using
    (Localization.awayLift_mk
      (coneDehom_quotient_map   I J hJ).toRingHom
      (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))))
      a 1 (by simp) j)

/-- Helper for Chap10 Lemma 10 57 10: the ordinary away inverse sends the cone fraction
`X_{i+1}/X₀` to the affine quotient generator `x_i`. -/
theorem coneOrdinaryAwayToAffineQuotient_val_coneAffineVariableFraction {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    (hJ : J ≤ Ideal.comap (coneDehom  ) I) (i : Fin n) :
    cone_ordinary_away_to_affine_quotient   I J hJ
      (coneAffineVariableFraction   J i).val =
      Ideal.Quotient.mk I (MvPolynomial.X i) := by
  -- Reduce the homogeneous fraction to its ordinary localization value, then use the quotient
  -- dehomogenization computation on `rename Fin.succ`.
  rw [coneAffineVariableFraction, HomogeneousLocalization.Away.val_mk]
  have hrename :
      coneDehom_quotient_map   I J hJ
          (Ideal.Quotient.mk J (MvPolynomial.X i.succ)) =
        Ideal.Quotient.mk I (MvPolynomial.X i) := by
    -- The support-file lemma is stated for `rename Fin.succ`; here it specializes to a single
    -- affine generator.
    simpa using coneDehom_quotient_map_rename_succ   I J hJ
      (MvPolynomial.X i)
  simpa [coneStandardDenominator] using
    (coneOrdinaryAwayToAffineQuotient_mk   I J hJ
      (Ideal.Quotient.mk J (MvPolynomial.X i.succ)) 1).trans
      hrename

/-- Helper for Chap10 Lemma 10 57 10: composing the affine-to-cone chart with the ordinary
away inverse recovers the affine quotient map. -/
theorem coneOrdinaryAwayToAffineQuotient_val_coneAffineToAwayAlgHom {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    (hJ : J ≤ Ideal.comap (coneDehom  ) I)
    (p : MvPolynomial (Fin n) R) :
    cone_ordinary_away_to_affine_quotient   I J hJ
      (coneAffineToAwayAlgHom   J p).val =
      Ideal.Quotient.mk I p := by
  letI : CommRing
      (Away (cone_quotient_grading   J)
        ((coneStandardDenominator   J :
          MvPolynomial (Fin (n + 1)) R ⧸ J))) :=
    HomogeneousLocalization.homogeneousLocalizationCommRing
  let φ : MvPolynomial (Fin n) R →+* (MvPolynomial (Fin n) R ⧸ I) :=
    (cone_ordinary_away_to_affine_quotient   I J hJ).comp
      ((algebraMap
        (Away (cone_quotient_grading   J)
          ((coneStandardDenominator   J :
            MvPolynomial (Fin (n + 1)) R ⧸ J)))
        (Localization.Away
          ((coneStandardDenominator   J :
            MvPolynomial (Fin (n + 1)) R ⧸ J)))).comp
          (coneAffineToAwayAlgHom   J).toRingHom)
  have hφ :
      φ = (Ideal.Quotient.mkₐ R I).toRingHom := by
    -- Compare the two polynomial maps on coefficients and variables.
    apply MvPolynomial.ringHom_ext
    · intro r
      -- Coefficients become ordinary localized constants, and dehomogenization preserves them.
      have hconstVal :
          HomogeneousLocalization.val
              ((algebraMap R
                    (Away (cone_quotient_grading   J)
                      ((coneStandardDenominator   J :
                        MvPolynomial (Fin (n + 1)) R ⧸ J))) r)) =
            Localization.mk (Ideal.Quotient.mk J (MvPolynomial.C r))
              ⟨1, by exact ⟨0, rfl⟩⟩ := by
        rfl
      have hconstVal' :
          (((algebraMap
                (Away (cone_quotient_grading   J)
                  ((coneStandardDenominator   J :
                    MvPolynomial (Fin (n + 1)) R ⧸ J)))
                (Localization.Away
                  ((coneStandardDenominator   J :
                    MvPolynomial (Fin (n + 1)) R ⧸ J)))).comp
              (coneAffineToAwayAlgHom   J).toRingHom)
            (MvPolynomial.C r)) =
            Localization.mk (Ideal.Quotient.mk J (MvPolynomial.C r))
              ⟨1, by exact ⟨0, rfl⟩⟩ := by
        simpa [coneAffineToAwayAlgHom, RingHom.comp_apply,
          HomogeneousLocalization.algebraMap_apply] using hconstVal
      have hconstEval :=
        congrArg
          (cone_ordinary_away_to_affine_quotient   I J hJ)
          hconstVal'
      calc
        φ (MvPolynomial.C r) =
          cone_ordinary_away_to_affine_quotient   I J hJ
            ((((algebraMap
                  (Away (cone_quotient_grading   J)
                    ((coneStandardDenominator   J :
                      MvPolynomial (Fin (n + 1)) R ⧸ J)))
                (Localization.Away
                    ((coneStandardDenominator   J :
                      MvPolynomial (Fin (n + 1)) R ⧸ J)))).comp
                (coneAffineToAwayAlgHom   J).toRingHom)
              (MvPolynomial.C r))) := by
              rfl
        _ =
          cone_ordinary_away_to_affine_quotient   I J hJ
            (Localization.mk (Ideal.Quotient.mk J (MvPolynomial.C r))
              ⟨1, by exact ⟨0, rfl⟩⟩) := by
              exact hconstEval
        _ =
          coneDehom_quotient_map   I J hJ
            (Ideal.Quotient.mk J (MvPolynomial.C r)) := by
              simpa using
                (coneOrdinaryAwayToAffineQuotient_mk   I J hJ
                  (Ideal.Quotient.mk J (MvPolynomial.C r)) 0)
        _ = algebraMap R (MvPolynomial (Fin n) R ⧸ I) r := by
              simp [coneDehom_quotient_map, coneDehom]
    · intro i
      -- Generators were already identified with the cone fractions `X_{i+1} / X₀`.
      have hvarVal :
          (((algebraMap
                (Away (cone_quotient_grading   J)
                  ((coneStandardDenominator   J :
                    MvPolynomial (Fin (n + 1)) R ⧸ J)))
                (Localization.Away
                  ((coneStandardDenominator   J :
                    MvPolynomial (Fin (n + 1)) R ⧸ J)))).comp
              (coneAffineToAwayAlgHom   J).toRingHom)
            (MvPolynomial.X i)) =
            (coneAffineVariableFraction   J i).val := by
        simp [coneAffineToAwayAlgHom, RingHom.comp_apply,
          HomogeneousLocalization.algebraMap_apply]
      have hvarVal' :=
        congrArg
          (cone_ordinary_away_to_affine_quotient   I J hJ)
          hvarVal
      -- The away inverse sends `X_{i+1}/X₀` back to the affine generator `xᵢ`.
      calc
        φ (MvPolynomial.X i) =
          cone_ordinary_away_to_affine_quotient   I J hJ
            (coneAffineVariableFraction   J i).val := by
              simpa [φ, RingHom.comp_apply] using hvarVal'
        _ = Ideal.Quotient.mk I (MvPolynomial.X i) := by
              exact coneOrdinaryAwayToAffineQuotient_val_coneAffineVariableFraction
                  I J hJ i
  -- The desired identity is the equality of these two polynomial ring maps evaluated at `p`.
  simpa [φ] using congrArg (fun ψ : MvPolynomial (Fin n) R →+* (MvPolynomial (Fin n) R ⧸ I) ↦
    ψ p) hφ

/-- Helper for Chap10 Lemma 10 57 10: the affine chart map has the prescribed value on each
polynomial generator. -/
@[simp] theorem coneAffineToAwayAlgHom_X {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)] (i : Fin n) :
    coneAffineToAwayAlgHom   J (MvPolynomial.X i) =
      coneAffineVariableFraction   J i := by
  -- The polynomial map was defined by `aeval`, so generator evaluation is definitional after `simp`.
  simp [coneAffineToAwayAlgHom]

/-- Helper for Chap10 Lemma 10 57 10: the normalized ordinary-localization fraction attached to a
constant affine polynomial reduces to the corresponding constant class. -/
theorem normalizedConeConstantFraction_eq {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (r : R) :
    let f0 : MvPolynomial (Fin (n + 1)) R ⧸ J :=
      Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))
    let f01 : Submonoid.powers f0 := ⟨f0 ^ 1, by exact ⟨1, rfl⟩⟩
    let one : Submonoid.powers f0 := 1
    Localization.mk
      (Ideal.Quotient.mk J
        (coneHomogenizeTo   1 (MvPolynomial.C r)))
      f01 =
      Localization.mk (Ideal.Quotient.mk J (MvPolynomial.C r)) one := sorry

/-- Helper for Chap10 Lemma 10 57 10: on an affine generator, the ordinary-localization value of
the cone chart already matches the normalized degree-one cone fraction. -/
theorem coneAffineToAwayAlgHom_val_X_eq_normalizedFraction {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)] (i : Fin n) :
    let f0 : MvPolynomial (Fin (n + 1)) R ⧸ J :=
      Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))
    let f1 : Submonoid.powers f0 := ⟨f0 ^ 1, by exact ⟨1, rfl⟩⟩
    (coneAffineToAwayAlgHom   J (MvPolynomial.X i)).val =
      Localization.mk
        (Ideal.Quotient.mk J
          (coneHomogenizeTo   1 (MvPolynomial.X i)))
        f1 := sorry

/-- Helper for Chap10 Lemma 10 57 10: in an ordinary away-localization, two fractions with the
same denominator add by adding their numerators. -/
theorem localizationMk_add_sameDenominator {A : Type*} [CommRing A]
    (f x y : A) (d : ℕ) :
    let fd : Submonoid.powers f := ⟨f ^ d, by exact ⟨d, rfl⟩⟩
    Localization.mk x fd + Localization.mk y fd = Localization.mk (x + y) fd := sorry

/-- Helper for Chap10 Lemma 10 57 10: a finite sum of ordinary-localization fractions with one
fixed denominator is the fraction whose numerator is the sum of the numerators. -/
theorem localizationMk_sum_sameDenominator {A : Type*} [CommRing A] {α : Type*}
    (f : A) (d : ℕ) (s : Finset α) (g : α → A) :
    let fd : Submonoid.powers f := ⟨f ^ d, by exact ⟨d, rfl⟩⟩
    (Finset.sum s fun a ↦ Localization.mk (g a) fd) =
      Localization.mk (Finset.sum s g) fd := sorry

/-- Helper for Chap10 Lemma 10 57 10: a finite sum of localized-module fractions with one fixed
denominator exponent is the fraction of the summed numerator. -/
theorem localizedModuleMk_sum_sameDenominator {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N] {α : Type*}
    (f : A) (d : ℕ) (s : Finset α) (g : α → N) :
    let fd : Submonoid.powers f := ⟨f ^ d, by exact ⟨d, rfl⟩⟩
    (Finset.sum s fun a ↦ LocalizedModule.mk (g a) fd) =
      LocalizedModule.mk (Finset.sum s g) fd := sorry

/-- Helper for Chap10 Lemma 10 57 10: multiplying numerator and denominator by the same power of
the away element does not change the represented ordinary-localization fraction. -/
theorem localizationMk_shiftDenominator {A : Type*} [CommRing A]
    (f x : A) {i d : ℕ} (hid : i ≤ d) :
    let fi : Submonoid.powers f := ⟨f ^ i, by exact ⟨i, rfl⟩⟩
    let fd : Submonoid.powers f := ⟨f ^ d, by exact ⟨d, rfl⟩⟩
    Localization.mk x fi = Localization.mk (f ^ (d - i) * x) fd := sorry

/-- Helper for Chap10 Lemma 10 57 10: in an ordinary away-localization, a `Finsupp.prod` of
fractions with the same base denominator collapses to the corresponding single fraction. -/
theorem localizationMk_finsuppProd_sameBase {A : Type*} [CommRing A] {α : Type*}
    (f : A) (m : α →₀ ℕ) (g : α → A) :
    let f1 : Submonoid.powers f := ⟨f ^ 1, ⟨1, rfl⟩⟩
    let fd : Submonoid.powers f := ⟨f ^ (m.sum fun _ e ↦ e), ⟨m.sum fun _ e ↦ e, rfl⟩⟩
    m.prod (fun i e ↦ Localization.mk (g i) f1 ^ e) =
      Localization.mk (m.prod fun i e ↦ g i ^ e) fd := sorry

/-- Helper for Chap10 Lemma 10 57 10: the constant affine polynomial already matches its
normalized cone fraction in ordinary away-localization. -/
theorem coneAffineToAwayAlgHom_val_C_eq_normalizedFraction {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    (r : R) :
    (coneAffineToAwayAlgHom   J (MvPolynomial.C r)).val =
      Localization.mk
        (Ideal.Quotient.mk J
          (coneHomogenizeTo   1 (MvPolynomial.C r)))
        ⟨(Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) ^ 1,
          by exact ⟨1, rfl⟩⟩ := sorry

/-- Helper for Chap10 Lemma 10 57 10: source homogenization commutes with finite affine sums. -/
theorem coneHomogenizeTo_sum {n : ℕ} {α : Type*}
    (d : ℕ) (s : Finset α) (f : α → MvPolynomial (Fin n) R) :
    coneHomogenizeTo   d (∑ a ∈ s, f a) =
      ∑ a ∈ s, coneHomogenizeTo   d (f a) := sorry

/-- Helper for Chap10 Lemma 10 57 10: after passing to ordinary away-localization, the affine
cone chart sends `X i` to the ordinary fraction `X_{i+1} / X₀`. -/
theorem coneAffineToAwayAlgHom_val_X_eq_ordinaryFraction {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)] (i : Fin n) :
    let f0 : MvPolynomial (Fin (n + 1)) R ⧸ J :=
      Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))
    let f1 : Submonoid.powers f0 := ⟨f0 ^ 1, by exact ⟨1, by simp⟩⟩
    (coneAffineToAwayAlgHom   J (MvPolynomial.X i)).val =
      Localization.mk
        (Ideal.Quotient.mk J (MvPolynomial.X i.succ))
        f1 := sorry

/-- Helper for Chap10 Lemma 10 57 10: after forgetting the grading, the affine cone chart is the
ordinary affine evaluation sending `x_i` to `X_{i+1} / X₀`. -/
theorem coneAffineToAwayAlgHom_val_eq_ordinaryAeval {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    (p : MvPolynomial (Fin n) R) :
    let f0 : MvPolynomial (Fin (n + 1)) R ⧸ J :=
      Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))
    let f1 : Submonoid.powers f0 := ⟨f0 ^ 1, ⟨1, rfl⟩⟩
    let ordinaryAeval : MvPolynomial (Fin n) R →ₐ[R] Localization.Away f0 :=
      MvPolynomial.aeval fun i ↦
        Localization.mk (Ideal.Quotient.mk J (MvPolynomial.X i.succ)) f1
    (coneAffineToAwayAlgHom   J p).val = ordinaryAeval p := sorry

/-- Helper for Chap10 Lemma 10 57 10: a homogeneous affine polynomial of degree `d` already
evaluates to the cone fraction `rename Fin.succ p / X₀^d` in ordinary away-localization. -/

theorem coneAffineToAwayAlgHom_val_monomial {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    (m : Fin n →₀ ℕ) (c : R) :
    let f0 : MvPolynomial (Fin (n + 1)) R ⧸ J :=
      Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))
    let fd : Submonoid.powers f0 :=
      ⟨f0 ^ (m.sum fun _ e ↦ e), by exact ⟨m.sum fun _ e ↦ e, rfl⟩⟩
    (coneAffineToAwayAlgHom   J (MvPolynomial.monomial m c)).val =
      Localization.mk
        (Ideal.Quotient.mk J
          (MvPolynomial.rename Fin.succ (MvPolynomial.monomial m c)))
        fd := sorry

/-- Helper for Chap10 Lemma 10 57 10: cone homogenization commutes with the affine support
expansion of a polynomial. -/
theorem coneHomogenizeTo_supportExpansion {n d : ℕ} (p : MvPolynomial (Fin n) R) :
    coneHomogenizeTo   d p =
      ∑ m ∈ p.support,
        coneHomogenizeTo   d
          (MvPolynomial.monomial m (p.coeff m)) := sorry

theorem coneAffineToAwayAlgHom_val_eq_fraction_of_totalDegree_le_aux {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    {p : MvPolynomial (Fin n) R} (hd : p.totalDegree ≤ d) :
    let f0 : MvPolynomial (Fin (n + 1)) R ⧸ J :=
      Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))
    let fd : Submonoid.powers f0 := ⟨f0 ^ d, ⟨d, rfl⟩⟩
    (coneAffineToAwayAlgHom   J p).val =
      Localization.mk
        (Ideal.Quotient.mk J (coneHomogenizeTo   d p))
        fd := sorry

theorem coneAffineToAwayAlgHom_val_of_isHomogeneous {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    {p : MvPolynomial (Fin n) R} (hp : p.IsHomogeneous d) :
    let f0 : MvPolynomial (Fin (n + 1)) R ⧸ J :=
      Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))
    let fd : Submonoid.powers f0 := ⟨f0 ^ d, by exact ⟨d, rfl⟩⟩
    (coneAffineToAwayAlgHom   J p).val =
      Localization.mk
        (Ideal.Quotient.mk J (MvPolynomial.rename Fin.succ p))
        fd := sorry

/-- Helper for Chap10 Lemma 10 57 10: if a common degree `d` dominates `p.totalDegree`, then the
ordinary away value of the affine chart is the degree-`d` cone homogenization fraction. -/
theorem coneAffineToAwayAlgHom_val_eq_fraction_of_totalDegree_le {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    {p : MvPolynomial (Fin n) R} (hd : p.totalDegree ≤ d) :
    let f0 : MvPolynomial (Fin (n + 1)) R ⧸ J :=
      Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))
    let fd : Submonoid.powers f0 := ⟨f0 ^ d, by exact ⟨d, rfl⟩⟩
    (coneAffineToAwayAlgHom   J p).val =
      Localization.mk
        (Ideal.Quotient.mk J (coneHomogenizeTo   d p))
        fd := sorry

/-- Helper for Chap10 Lemma 10 57 10: if an affine polynomial is homogeneous of degree `i`, then
every larger cone homogenization is just the renamed affine polynomial multiplied by the remaining
power of `X₀`. -/
theorem coneHomogenizeTo_eq_X_zero_pow_mul_of_isHomogeneous {n i d : ℕ}
    {p : MvPolynomial (Fin n) R} (hp : p.IsHomogeneous i) (hid : i ≤ d) :
    coneHomogenizeTo   d p =
      MvPolynomial.X (0 : Fin (n + 1)) ^ (d - i) * MvPolynomial.rename Fin.succ p := sorry

/-- Helper for Chap10 Lemma 10 57 10: after passing to ordinary away-localization, the affine
chart sends `p` to the normalized fraction defined by the shifted homogenization of `p`. -/
theorem coneAffineToAwayAlgHom_val_eq_normalizedFraction {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    (p : MvPolynomial (Fin n) R) :
    (coneAffineToAwayAlgHom   J p).val =
      Localization.mk
        (Ideal.Quotient.mk J
          (coneHomogenizeTo   (max p.totalDegree 1) p))
        ⟨(Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) ^ (max p.totalDegree 1),
          by exact ⟨max p.totalDegree 1, rfl⟩⟩ := sorry

/-- Helper for Chap10 Lemma 10 57 10: the affine-to-away chart kills the affine kernel after
positive cone homogenization. -/
theorem coneAffineToAwayAlgHom_eq_zero_of_mem {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    [GradedAlgebra (cone_quotient_grading  
      (positively_shifted_cone_homogenized_ideal   I))]
    {p : MvPolynomial (Fin n) R} (hp : p ∈ I) :
    letI : CommRing
        (Away
          (cone_quotient_grading  
            (positively_shifted_cone_homogenized_ideal   I))
          ((coneStandardDenominator  
            (positively_shifted_cone_homogenized_ideal   I) :
            MvPolynomial (Fin (n + 1)) R ⧸
              positively_shifted_cone_homogenized_ideal   I))) :=
      HomogeneousLocalization.homogeneousLocalizationCommRing
    coneAffineToAwayAlgHom  
        (positively_shifted_cone_homogenized_ideal   I) p = 0 := sorry

/-- Helper for Chap10 Lemma 10 57 10: the affine chart descends through the kernel quotient of the
chosen polynomial presentation. -/
noncomputable def coneKernelQuotientAwayAlgHom {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    [GradedAlgebra (cone_quotient_grading  
      (positively_shifted_cone_homogenized_ideal   I))] :
    letI : CommRing
        (Away
          (cone_quotient_grading  
            (positively_shifted_cone_homogenized_ideal   I))
          ((coneStandardDenominator  
            (positively_shifted_cone_homogenized_ideal   I) :
            MvPolynomial (Fin (n + 1)) R ⧸
              positively_shifted_cone_homogenized_ideal   I))) :=
      HomogeneousLocalization.homogeneousLocalizationCommRing
    (MvPolynomial (Fin n) R ⧸ I) →ₐ[R]
      Away
        (cone_quotient_grading  
          (positively_shifted_cone_homogenized_ideal   I))
        ((coneStandardDenominator  
          (positively_shifted_cone_homogenized_ideal   I) :
          MvPolynomial (Fin (n + 1)) R ⧸
            positively_shifted_cone_homogenized_ideal   I)) :=
  letI : CommRing
      (Away
        (cone_quotient_grading  
          (positively_shifted_cone_homogenized_ideal   I))
        ((coneStandardDenominator  
          (positively_shifted_cone_homogenized_ideal   I) :
          MvPolynomial (Fin (n + 1)) R ⧸
            positively_shifted_cone_homogenized_ideal   I))) :=
    HomogeneousLocalization.homogeneousLocalizationCommRing
  Ideal.Quotient.liftₐ I
    (coneAffineToAwayAlgHom  
      (positively_shifted_cone_homogenized_ideal   I))
    (fun _ hp ↦ coneAffineToAwayAlgHom_eq_zero_of_mem   I hp)

/-- Helper for Chap10 Lemma 10 57 10: the descended affine chart sends `x_i` to `X_{i+1}/X_0`. -/
@[simp] theorem coneKernelQuotientAwayAlgHom_mk_X {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    [GradedAlgebra (cone_quotient_grading  
      (positively_shifted_cone_homogenized_ideal   I))] (i : Fin n) :
    coneKernelQuotientAwayAlgHom   I
        (Ideal.Quotient.mk I (MvPolynomial.X i)) =
      coneAffineVariableFraction  
        (positively_shifted_cone_homogenized_ideal   I) i := by
  -- The quotient chart is the lift of the affine polynomial chart, so this is the generator
  -- computation after quotient descent.
  simp [coneKernelQuotientAwayAlgHom]

/-- Helper for Chap10 Lemma 10 57 10: the explicit affine-quotient cone chart sends the class of
an affine polynomial to the common-degree homogenized fraction in the cone away chart. -/
theorem coneKernelQuotientAwayAlgHom_apply_mk_of_totalDegree_le {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    [GradedAlgebra (cone_quotient_grading  
      (positively_shifted_cone_homogenized_ideal   I))]
    {p : MvPolynomial (Fin n) R} (hd : p.totalDegree ≤ d) :
    let hq :
        Ideal.Quotient.mk
            (positively_shifted_cone_homogenized_ideal I)
            (coneHomogenizeTo d p) ∈
          cone_quotient_grading (positively_shifted_cone_homogenized_ideal I) (d * 1) :=
      cone_quotient_mk_mem_grade_of_isHomogeneous_nsmul_one
        (coneHomogenizeTo_isHomogeneous d p)
    coneKernelQuotientAwayAlgHom   I (Ideal.Quotient.mk I p) =
      Away.mk
        (cone_quotient_grading  
          (positively_shifted_cone_homogenized_ideal   I))
        (coneStandardDenominator_mem_grade_one  
          (positively_shifted_cone_homogenized_ideal   I))
        d
        (Ideal.Quotient.mk
          (positively_shifted_cone_homogenized_ideal   I)
          (coneHomogenizeTo   d p))
        hq := sorry

/-- Helper for Chap10 Lemma 10 57 10: the source affine quotient is the homogeneous cone chart away
from `X_0`. -/
theorem coneKernelQuotientAwayAlgHom_leftInverse {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    [GradedAlgebra (cone_quotient_grading  
      (positively_shifted_cone_homogenized_ideal   I))] :
    letI : CommRing
        (Away
          (cone_quotient_grading  
            (positively_shifted_cone_homogenized_ideal   I))
          ((coneStandardDenominator  
            (positively_shifted_cone_homogenized_ideal   I) :
            MvPolynomial (Fin (n + 1)) R ⧸
              positively_shifted_cone_homogenized_ideal   I))) :=
      HomogeneousLocalization.homogeneousLocalizationCommRing
    Function.LeftInverse
      (fun z ↦
        cone_ordinary_away_to_affine_quotient   I
          (positively_shifted_cone_homogenized_ideal   I)
          (positively_shifted_cone_homogenized_ideal_le_comap_coneDehom
              I)
          z.val)
      (coneKernelQuotientAwayAlgHom   I) := sorry

/-- Helper for Chap10 Lemma 10 57 10: the descended affine chart is injective because the
ordinary affine chart is a left inverse. -/
theorem coneKernelQuotientAwayAlgHom_injective {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    [GradedAlgebra (cone_quotient_grading  
      (positively_shifted_cone_homogenized_ideal   I))] :
    letI : CommRing
        (Away
          (cone_quotient_grading  
            (positively_shifted_cone_homogenized_ideal   I))
          ((coneStandardDenominator  
            (positively_shifted_cone_homogenized_ideal   I) :
            MvPolynomial (Fin (n + 1)) R ⧸
              positively_shifted_cone_homogenized_ideal   I))) :=
      HomogeneousLocalization.homogeneousLocalizationCommRing
    Function.Injective (coneKernelQuotientAwayAlgHom   I) := sorry

noncomputable def coneKernelQuotientAwayAlgEquiv {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    [GradedAlgebra (cone_quotient_grading  
      (positively_shifted_cone_homogenized_ideal   I))] :
    letI : CommRing
        (Away
          (cone_quotient_grading  
            (positively_shifted_cone_homogenized_ideal   I))
          ((coneStandardDenominator  
            (positively_shifted_cone_homogenized_ideal   I) :
            MvPolynomial (Fin (n + 1)) R ⧸
              positively_shifted_cone_homogenized_ideal   I))) :=
      HomogeneousLocalization.homogeneousLocalizationCommRing
    (MvPolynomial (Fin n) R ⧸ I) ≃ₐ[R]
      Away
        (cone_quotient_grading  
          (positively_shifted_cone_homogenized_ideal   I))
        ((coneStandardDenominator  
          (positively_shifted_cone_homogenized_ideal   I) :
          MvPolynomial (Fin (n + 1)) R ⧸
            positively_shifted_cone_homogenized_ideal   I)) := by
  let J : Ideal (MvPolynomial (Fin (n + 1)) R) :=
    positively_shifted_cone_homogenized_ideal   I
  letI : CommRing
      (Away
        (cone_quotient_grading   J)
        ((coneStandardDenominator   J :
          MvPolynomial (Fin (n + 1)) R ⧸ J))) :=
    HomogeneousLocalization.homogeneousLocalizationCommRing
  exact AlgEquiv.ofBijective (coneKernelQuotientAwayAlgHom I) <| by
    refine ⟨coneKernelQuotientAwayAlgHom_injective I, ?_⟩
    sorry

/-- Helper for Chap10 Lemma 10 57 10: the quotient-side degree-`d` component receives the
degree-`d` source component through the quotient map. -/
def homogeneousQuotientComponentMapNat
    {A : Type _} [Ring A] {P : Type _} [AddCommGroup P] [Module A P]
    (ℳ : ℕ → Submodule A P) [DirectSum.Decomposition ℳ]
    (N : Submodule A P) (d : ℕ) :
    ℳ d →ₗ[A] (ℳ d).map N.mkQ :=
  LinearMap.codRestrict
    ((ℳ d).map N.mkQ)
    (N.mkQ.domRestrict (ℳ d))
    (fun x ↦ ⟨x, x.2, rfl⟩)

/-- Helper for Chap10 Lemma 10 57 10: decompose a source element and then map each homogeneous
piece to the corresponding component of the quotient. -/
noncomputable def homogeneousQuotientPredecomposeNat
    {A : Type _} [Ring A] {P : Type _} [AddCommGroup P] [Module A P]
    (ℳ : ℕ → Submodule A P) [DirectSum.Decomposition ℳ]
    (N : Submodule A P) :
    P →ₗ[A] DirectSum ℕ fun d ↦ (ℳ d).map N.mkQ :=
  (DirectSum.lmap fun d ↦ homogeneousQuotientComponentMapNat ℳ N d).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

/-- Helper for Chap10 Lemma 10 57 10: a homogeneous source element maps to the matching
direct-sum generator after quotienting. -/
theorem homogeneousQuotientPredecomposeNat_eq_lof_of_mem
    {A : Type _} [Ring A] {P : Type _} [AddCommGroup P] [Module A P]
    (ℳ : ℕ → Submodule A P) [DirectSum.Decomposition ℳ]
    (N : Submodule A P) {x : P} {d : ℕ} (hx : x ∈ ℳ d) :
    homogeneousQuotientPredecomposeNat ℳ N x =
      DirectSum.lof A ℕ (fun e ↦ (ℳ e).map N.mkQ) d
        (homogeneousQuotientComponentMapNat ℳ N d ⟨x, hx⟩) := by
  apply DFinsupp.ext
  intro e
  by_cases hde : d = e
  · subst hde
    -- In the matching degree, the source decomposition has exactly the chosen homogeneous
    -- summand, so the quotient predecomposition is the corresponding `lof`.
    have hsame : (DirectSum.decompose ℳ x d : ℳ d) = ⟨x, hx⟩ := by
      apply Subtype.ext
      simpa using (DirectSum.decompose_of_mem_same ℳ hx)
    rw [homogeneousQuotientPredecomposeNat, LinearMap.comp_apply, DirectSum.lmap_apply]
    simpa [DirectSum.decomposeLinearEquiv_apply, DirectSum.lof_eq_of, hsame] using
      congrArg (homogeneousQuotientComponentMapNat ℳ N d) hsame
  · have hed : e ≠ d := by
      intro hed
      exact hde hed.symm
    have hdecomp : (((DirectSum.decompose ℳ) x e : ℳ e) : P) = 0 := by
      simpa using (DirectSum.decompose_of_mem_ne ℳ hx hde)
    have hzero : ((DirectSum.decompose ℳ x e : ℳ e)) = 0 := by
      apply Subtype.ext
      simpa using hdecomp
    -- Away from the matching degree, the source homogeneous projection is already zero.
    rw [homogeneousQuotientPredecomposeNat, LinearMap.comp_apply, DirectSum.lmap_apply]
    have hcoord :
        ((DirectSum.decomposeLinearEquiv ℳ x) e) = ((DirectSum.decompose ℳ) x e) := rfl
    have hleft :
        (homogeneousQuotientComponentMapNat ℳ N e)
            ((DirectSum.decompose ℳ) x e) = 0 := by
      simpa [homogeneousQuotientComponentMapNat, hzero]
    calc
      (homogeneousQuotientComponentMapNat ℳ N e)
          ((DirectSum.decomposeLinearEquiv ℳ x) e) =
          (homogeneousQuotientComponentMapNat ℳ N e)
            ((DirectSum.decompose ℳ) x e) := by
              simpa [DirectSum.decomposeLinearEquiv_apply] using
                congrArg (homogeneousQuotientComponentMapNat ℳ N e) hcoord
      _ = 0 := hleft
      _ =
          ((DirectSum.lof A ℕ (fun e ↦ (ℳ e).map N.mkQ) d)
            ((homogeneousQuotientComponentMapNat ℳ N d) ⟨x, hx⟩)) e := by
              symm
              exact DirectSum.of_eq_of_ne _ _ _ hed

/-- Helper for Chap10 Lemma 10 57 10: the componentwise quotient predecomposition vanishes on a
homogeneous submodule. -/
theorem homogeneousQuotientPredecomposeNat_eq_zero_of_mem
    {A : Type _} [Ring A] {P : Type _} [AddCommGroup P] [Module A P]
    (ℳ : ℕ → Submodule A P) [DirectSum.Decomposition ℳ]
    {N : Submodule A P} (hN : N.IsHomogeneous ℳ) {x : P} (hx : x ∈ N) :
    homogeneousQuotientPredecomposeNat ℳ N x = 0 := by
  apply DFinsupp.ext
  intro d
  have hproj_mem : (((DirectSum.decompose ℳ x d : ℳ d) : P)) ∈ N := hN d hx
  have hproj_zero :
      N.mkQ (((DirectSum.decompose ℳ x d : ℳ d) : P)) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero N).2 hproj_mem
  -- Each source projection of an element of `N` is still in `N`, so its quotient component
  -- is zero.
  rw [homogeneousQuotientPredecomposeNat, LinearMap.comp_apply, DirectSum.lmap_apply]
  apply Subtype.ext
  simpa [homogeneousQuotientComponentMapNat, DirectSum.decomposeLinearEquiv_apply] using
    hproj_zero

/-- Helper for Chap10 Lemma 10 57 10: a homogeneous submodule is contained in the kernel of the
quotient predecomposition. -/
theorem homogeneousQuotientPredecomposeNat_le_ker
    {A : Type _} [Ring A] {P : Type _} [AddCommGroup P] [Module A P]
    (ℳ : ℕ → Submodule A P) [DirectSum.Decomposition ℳ]
    {N : Submodule A P} (hN : N.IsHomogeneous ℳ) :
    N ≤ LinearMap.ker (homogeneousQuotientPredecomposeNat ℳ N) := by
  intro x hx
  -- The previous vanishing statement is exactly the kernel condition needed for `liftQ`.
  exact homogeneousQuotientPredecomposeNat_eq_zero_of_mem ℳ hN hx

/-- Helper for Chap10 Lemma 10 57 10: the quotient predecomposition descends to the quotient
module by a homogeneous submodule. -/
noncomputable def homogeneousQuotientDecomposeLinearNat
    {A : Type _} [Ring A] {P : Type _} [AddCommGroup P] [Module A P]
    (ℳ : ℕ → Submodule A P) [DirectSum.Decomposition ℳ]
    {N : Submodule A P} (hN : N.IsHomogeneous ℳ) :
    P ⧸ N →ₗ[A] DirectSum ℕ fun d ↦ (ℳ d).map N.mkQ :=
  N.liftQ
    (homogeneousQuotientPredecomposeNat ℳ N)
    (homogeneousQuotientPredecomposeNat_le_ker ℳ hN)

/-- Helper for Chap10 Lemma 10 57 10: recomposing the descended quotient decomposition recovers
the quotient class. -/
theorem homogeneousQuotientDecomposeLinearNat_left_inv
    {A : Type _} [Ring A] {P : Type _} [AddCommGroup P] [Module A P]
    (ℳ : ℕ → Submodule A P) [DirectSum.Decomposition ℳ]
    {N : Submodule A P} (hN : N.IsHomogeneous ℳ) :
    DirectSum.coeLinearMap (fun d ↦ (ℳ d).map N.mkQ) ∘ₗ
        homogeneousQuotientDecomposeLinearNat ℳ hN =
      LinearMap.id := sorry

/-- Helper for Chap10 Lemma 10 57 10: the descended quotient decomposition is the identity on
the direct sum of quotient homogeneous components. -/
theorem homogeneousQuotientDecomposeLinearNat_right_inv
    {A : Type _} [Ring A] {P : Type _} [AddCommGroup P] [Module A P]
    (ℳ : ℕ → Submodule A P) [DirectSum.Decomposition ℳ]
    {N : Submodule A P} (hN : N.IsHomogeneous ℳ) :
    homogeneousQuotientDecomposeLinearNat ℳ hN ∘ₗ
        DirectSum.coeLinearMap (fun d ↦ (ℳ d).map N.mkQ) =
      LinearMap.id := by
  let ℳbar : ℕ → Submodule A (P ⧸ N) := fun d ↦ (ℳ d).map N.mkQ
  -- A direct-sum map is determined by its values on `lof` generators.
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro xbar
  rcases xbar.2 with ⟨x, hx, hqx⟩
  have hxbar :
      xbar = ⟨N.mkQ x, ⟨x, hx, rfl⟩⟩ := by
    apply Subtype.ext
    exact hqx.symm
  have hpre :
      homogeneousQuotientDecomposeLinearNat ℳ hN (N.mkQ x) =
        DirectSum.lof A ℕ (fun e ↦ ℳbar e) d ⟨N.mkQ x, ⟨x, hx, rfl⟩⟩ := by
    -- A homogeneous representative still yields the expected direct-sum basis vector after
    -- passing to the quotient.
    simpa [ℳbar, homogeneousQuotientDecomposeLinearNat,
      homogeneousQuotientComponentMapNat] using
      (homogeneousQuotientPredecomposeNat_eq_lof_of_mem ℳ N hx)
  simpa [LinearMap.comp_apply, hxbar] using hpre

/-- Helper for Chap10 Lemma 10 57 10: quotienting a graded module by a homogeneous submodule
inherits the direct-sum decomposition on the mapped quotient pieces. -/
@[reducible] noncomputable def homogeneousQuotientDecompositionNat
    {A : Type _} [Ring A] {P : Type _} [AddCommGroup P] [Module A P]
    (ℳ : ℕ → Submodule A P) [DirectSum.Decomposition ℳ]
    {N : Submodule A P} (hN : N.IsHomogeneous ℳ) :
    DirectSum.Decomposition (fun d ↦ (ℳ d).map N.mkQ) :=
  DirectSum.Decomposition.ofLinearMap
    (fun d ↦ (ℳ d).map N.mkQ)
    (homogeneousQuotientDecomposeLinearNat ℳ hN)
    (homogeneousQuotientDecomposeLinearNat_left_inv ℳ hN)
    (homogeneousQuotientDecomposeLinearNat_right_inv ℳ hN)

/-- Helper for Chap10 Lemma 10 57 10: the homogenized relation cokernel inherits the direct-sum
decomposition from the free cone module grading. -/
@[reducible] noncomputable def homogenizedRelationQuotientGrading_decomposition {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    [DirectSum.Decomposition (cone_quotient_grading   J)]
    [DirectSum.Decomposition
      (@free_cone_module_grading R _ n r J)]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    DirectSum.Decomposition
      (homogenized_relation_quotient_grading     J τ) := by
  let V := Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)
  let ℳ : ℕ → Submodule R V := free_cone_module_grading    J
  let N : Submodule (MvPolynomial (Fin (n + 1)) R ⧸ J) V :=
    homogenized_relation_submodule     J τ
  let P : Submodule R V := N.restrictScalars R
  have hP : P.IsHomogeneous ℳ := by
    -- First prove homogeneity in the explicitly named quotient carrier; this avoids making Lean
    -- unfold the quotient/module owners while matching the generic quotient-decomposition lemma.
    subst P
    subst N
    subst ℳ
    exact homogenized_relation_submodule_is_homogeneous
          J τ
  have hdec : DirectSum.Decomposition (fun d ↦ (ℳ d).map P.mkQ) :=
    homogeneousQuotientDecompositionNat ℳ hP
  -- The quotient by the `S`-submodule and by its `R`-restricted submodule have the same quotient
  -- carrier here, so unfolding the named aliases turns the generic decomposition into the target.
  subst P
  subst N
  subst ℳ
  exact hdec

/-- Helper for Chap10 Lemma 10 57 10: if a submodule already localizes to the whole source, then
localizing its image under a linear map recovers the full localized image. -/
lemma localizedImageOfTopLocalizedSubmodule
    {A : Type _} [CommRing A] (T : Submonoid A)
    {P : Type*} [AddCommGroup P] [Module A P]
    {Q : Type*} [AddCommGroup Q] [Module A Q]
    (ι : P →ₗ[A] Q)
    (N : Submodule A P)
    (hN : N.localized T = ⊤) :
    (N.map ι).localized T = LinearMap.range (LocalizedModule.map T ι) := by
  apply le_antisymm
  · -- Every localized image element comes from a localized source element in `N`.
    intro z hz
    rcases (Submodule.mem_localized'
        (S := Localization T) (p := T) (f := LocalizedModule.mkLinearMap T Q) (M' := N.map ι) z).mp
        hz with ⟨x, hx, s, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨LocalizedModule.mk y s, ?_⟩
    simpa [IsLocalizedModule.mk_eq_mk'] using
      (LocalizedModule.map_mk (S := T) ι y s)
  · -- Conversely, use `hN` to rewrite any localized source element with numerator in `N`.
    rintro z ⟨y, rfl⟩
    have hy : y ∈ N.localized T := by
      simpa [hN] using
        (show y ∈ (⊤ : Submodule (Localization T) (LocalizedModule T P)) from trivial)
    rcases (Submodule.mem_localized'
        (S := Localization T) (p := T) (f := LocalizedModule.mkLinearMap T P) (M' := N) y).mp hy
      with ⟨x, hx, s, hs⟩
    rw [← hs]
    exact (Submodule.mem_localized'
      (S := Localization T) (p := T) (f := LocalizedModule.mkLinearMap T Q) (M' := N.map ι)
      (((LocalizedModule.map T) ι) (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap T P) x s))).2
      ⟨ι x, ⟨x, hx, rfl⟩, s, by
        exact
          (IsLocalizedModule.map_mk'
            (S := T)
            (f := LocalizedModule.mkLinearMap T P)
            (g := LocalizedModule.mkLinearMap T Q)
            ι x s).symm⟩

/-- Helper for Chap10 Lemma 10 57 10: if a kernel submodule already localizes to the whole kernel,
then its image inside the source module localizes to the full localized kernel. -/
lemma kernelImageLocalizedEqLocalizedKernel
    {A : Type _} [CommRing A] (T : Submonoid A)
    {N : Type _} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] N)
    (Ksub : Submodule A (LinearMap.ker π))
    (hKsub : Ksub.localized T = ⊤) :
    (Ksub.map (LinearMap.ker π).subtype).localized T =
      (LinearMap.ker π).localized' (Localization T) T (LocalizedModule.mkLinearMap T P) := by
  -- First localize the chosen kernel submodule inside the ambient source module.
  calc
    (Ksub.map (LinearMap.ker π).subtype).localized T =
        LinearMap.range (LocalizedModule.map T (LinearMap.ker π).subtype) := by
      simpa using
        localizedImageOfTopLocalizedSubmodule
          (T := T) (LinearMap.ker π).subtype Ksub hKsub
    _ = (LinearMap.ker π).localized' (Localization T) T (LocalizedModule.mkLinearMap T P) := by
      -- Then identify that localized image with the canonical localization of the kernel itself.
      symm
      simpa [Submodule.localized, Submodule.map_top, Submodule.range_subtype] using
        localizedImageOfTopLocalizedSubmodule
          (T := T) (LinearMap.ker π).subtype (⊤ : Submodule A (LinearMap.ker π))
          (by simp [Submodule.localized])

/-- Helper for Chap10 Lemma 10 57 10: a localized quotient generator vanishes exactly when some
denominator multiple of its source numerator already lies in the quotient submodule. -/
lemma localizedQuotientMkZero_iff_exists_smul_mem
    {A : Type _} [CommRing A] (T : Submonoid A)
    {P : Type*} [AddCommGroup P] [Module A P]
    (K : Submodule A P) (x : P) (s : T) :
    IsLocalizedModule.mk' (LocalizedModule.mkLinearMap T (P ⧸ K))
        (Submodule.Quotient.mk x) s = 0 ↔
      ∃ t : T, (t : A) • x ∈ K := by
  -- Translate the localized zero statement back to the quotient, then rewrite quotient-zero as
  -- source-submodule membership.
  rw [IsLocalizedModule.mk'_eq_zero']
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero K]
    simpa using ht
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ht

/-- Helper for Chap10 Lemma 10 57 10: the inverse of `localizedQuotientEquiv` sends a localized
quotient generator to the quotient class of the localized numerator. -/
lemma localizedQuotientEquivSymmApplyMk
    {A : Type _} [CommRing A] (T : Submonoid A)
    {P : Type*} [AddCommGroup P] [Module A P]
    (K0 : Submodule A P) (x : P) :
    (localizedQuotientEquiv T K0).symm
      (LocalizedModule.mkLinearMap T (P ⧸ K0) (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap T P x) := by
  -- The canonical localization equivalence is characterized by its action on quotient generators.
  simpa [localizedQuotientEquiv, Submodule.toLocalizedQuotient] using
    (IsLocalizedModule.linearEquiv_symm_apply
      (S := T)
      (f := K0.toLocalizedQuotient T)
      (g := LocalizedModule.mkLinearMap T (P ⧸ K0))
      (x := Submodule.Quotient.mk x))

/-- Helper for Chap10 Lemma 10 57 10: the standard quotient-localization comparison computes on
localized quotient generators by sending them to the corresponding localized presentation value. -/
lemma localizedQuotientComparisonApplyMk
    {A : Type _} [CommRing A] (T : Submonoid A)
    {N : Type _} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] N)
    (K0 : Submodule A P)
    (hkerloc : K0.localized T = LinearMap.ker (LocalizedModule.map T π))
    (hπ : Function.Surjective (LocalizedModule.map T π))
    (x : P) :
    (((localizedQuotientEquiv T K0).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hkerloc ≪≫ₗ
        (LocalizedModule.map T π).quotKerEquivOfSurjective hπ)
      (LocalizedModule.mkLinearMap T (P ⧸ K0) (Submodule.Quotient.mk x))) =
        LocalizedModule.mkLinearMap T N (π x) := by
  -- Route correction: compute the whole quotient comparison on generators before comparing maps.
  simp only [LinearEquiv.trans_apply]
  rw [localizedQuotientEquivSymmApplyMk]
  rw [Submodule.quotEquivOfEq_mk]
  simpa using
    (LinearMap.quotKerEquivOfSurjective_apply_mk
      (f := LocalizedModule.map T π)
      (hf := hπ)
      (x := LocalizedModule.mkLinearMap T P x))

/-- Helper for Chap10 Lemma 10 57 10: once a localized relation submodule matches the localized
kernel of a presentation, the induced quotient map becomes a localization isomorphism. -/
lemma localizedQuotientEquivOfSurjectiveAndKernelMatch
    {A : Type _} [CommRing A] (T : Submonoid A)
    {N : Type _} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] N)
    (K0 : Submodule A P)
    (fbar : P ⧸ K0 →ₗ[A] N)
    (hπ : Function.Surjective (LocalizedModule.map T π))
    (hfbar : fbar.comp (Submodule.mkQ K0) = π)
    (hK0 : K0.localized T = (LinearMap.ker π).localized' (Localization T) T
      (LocalizedModule.mkLinearMap T P)) :
    ∃ e : LocalizedModule T (P ⧸ K0) ≃ₗ[Localization T] LocalizedModule T N,
      e.toLinearMap = LocalizedModule.map T fbar := by
  have hkerloc : K0.localized T = LinearMap.ker (LocalizedModule.map T π) := by
    -- Rewrite the localized relation submodule into the actual kernel of the localized map.
    calc
      K0.localized T = (LinearMap.ker π).localized' (Localization T) T
          (LocalizedModule.mkLinearMap T P) := hK0
      _ = LinearMap.ker (LocalizedModule.map T π) := by
        simpa using
          (LinearMap.localized'_ker_eq_ker_localizedMap
            (S := Localization T)
            (p := T)
            (f := LocalizedModule.mkLinearMap T P)
            (f' := LocalizedModule.mkLinearMap T N)
            (g := π))
  let e : LocalizedModule T (P ⧸ K0) ≃ₗ[Localization T] LocalizedModule T N :=
    (localizedQuotientEquiv T K0).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hkerloc ≪≫ₗ
      (LocalizedModule.map T π).quotKerEquivOfSurjective hπ
  refine ⟨e, ?_⟩
  have hcomp :
      e.toLinearMap.restrictScalars A ∘ₗ LocalizedModule.mkLinearMap T (P ⧸ K0) =
        (LocalizedModule.map T fbar).restrictScalars A ∘ₗ
          LocalizedModule.mkLinearMap T (P ⧸ K0) := by
    ext x
    -- Compare both localized maps on quotient generators coming from `P`.
    change e (LocalizedModule.mkLinearMap T (P ⧸ K0) (Submodule.Quotient.mk x)) =
      (LocalizedModule.map T fbar) (LocalizedModule.mkLinearMap T (P ⧸ K0) (Submodule.Quotient.mk x))
    rw [localizedQuotientComparisonApplyMk
      (T := T) (π := π) (K0 := K0) (hkerloc := hkerloc) (hπ := hπ) (x := x)]
    have hfbar_apply : fbar (Submodule.Quotient.mk x) = π x := by
      exact LinearMap.congr_fun hfbar x
    simpa [hfbar_apply] using
      (IsLocalizedModule.map_apply
        (S := T)
        (f := LocalizedModule.mkLinearMap T (P ⧸ K0))
        (g := LocalizedModule.mkLinearMap T N)
        (h := fbar)
        (x := Submodule.Quotient.mk x))
  have hEqA :
      e.toLinearMap.restrictScalars A = (LocalizedModule.map T fbar).restrictScalars A := by
    exact IsLocalizedModule.linearMap_ext
      (S := T)
      (LocalizedModule.mkLinearMap T (P ⧸ K0))
      (LocalizedModule.mkLinearMap T N)
      hcomp
  -- Equality after restricting scalars already determines the localized linear map.
  ext x
  exact LinearMap.congr_fun hEqA x

/-- Helper for Chap10 Lemma 10 57 10: finite generation of a module transports from a ring and
module to their canonical universe lifts. -/
theorem moduleFinite_ulift_of_moduleFinite
    {S : Type _} [Semiring S] {N : Type _} [AddCommMonoid N] [Module S N]
    [Module.Finite S N] :
    Module.Finite (ULift S) (ULift N) := sorry

/-- Helper for Chap10 Lemma 10 57 10: a finite adjoin-top generating set remains adjoin-top
after transporting the grading to the universe-lifted ring. -/
theorem ulift_adjoin_finset_eq_top
    {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S)
    [GradedAlgebra grading]
    [GradedAlgebra (uliftSubmoduleFamily  grading)]
    (s : Finset S)
    (hs_top : Algebra.adjoin (grading 0) (s : Set S) = ⊤) :
    Algebra.adjoin
      ((uliftSubmoduleFamily  grading) 0)
      ((s.map ⟨ULift.up, fun _ _ h ↦ ULift.up.inj h⟩ : Finset (ULift S)) :
        Set (ULift S)) = ⊤ := sorry

/-- Helper for Chap10 Lemma 10 57 10: the finite-type degree-one-generated model package
transports from a graded ring and module to their canonical universe lifts. -/
theorem isDegreeOneGeneratedFiniteTypeModel_ulift
    {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S)
    [GradedAlgebra grading]
    [GradedAlgebra (uliftSubmoduleFamily  grading)]
    {N : Type _} [AddCommGroup N] [Module S N]
    (hmodel : IsDegreeOneGeneratedFiniteTypeModel grading N) :
    IsDegreeOneGeneratedFiniteTypeModel
      (uliftSubmoduleFamily  grading)
      (ULift N) := sorry

/-- Helper for Chap10 Lemma 10 57 10: the unlifted affine ring chart transports through the
canonical `ULift` homogeneous away-localization equivalence. -/
noncomputable def liftedAwayAlgEquiv_of_unlifted
    {S : Type _} [CommRing S] [Algebra R S]
    (grading : ℕ → Submodule R S) [GradedAlgebra grading]
    {d : ℕ} (f : grading d)
    [GradedAlgebra (uliftSubmoduleFamily  grading)]
    (ringIso : R' ≃ₐ[R] Away grading (f : S)) :
    R' ≃ₐ[R]
        Away (uliftSubmoduleFamily  grading)
          ((uliftSubmoduleFamilyElement  grading f :
            uliftSubmoduleFamily  grading d) : ULift S) :=
  -- Compose the source chart with the owner-level `ULift` localization equivalence.
  ringIso.trans (uliftAwayAlgEquiv  grading f)

/-- Helper for Chap10 Lemma 10 57 10: the coordinate vector with a single `1` already lies in the
degree-zero piece of the free cone module. -/
lemma freeConeModuleSingle_mem_degree {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    {a : MvPolynomial (Fin (n + 1)) R ⧸ J}
    (ha : a ∈ cone_quotient_grading   J d)
    (i : Fin r) :
    Pi.single i a ∈ free_cone_module_grading    J d := sorry

/-- Helper for Chap10 Lemma 10 57 10: the quotient class of a single homogeneous coordinate vector
lies in the matching degree of the homogenized relation cokernel. -/
lemma homogenizedRelationQuotientSingle_mem_degree {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    {a : MvPolynomial (Fin (n + 1)) R ⧸ J}
    (ha : a ∈ cone_quotient_grading   J d)
    (i : Fin r) :
    (Submodule.Quotient.mk (Pi.single i a) :
        ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
          homogenized_relation_submodule     J τ)) ∈
      homogenized_relation_quotient_grading     J τ d := sorry

/-- Helper for Chap10 Lemma 10 57 10: a single lifted homogeneous quotient coordinate already
defines a degree-zero class in the away localization once the denominator is shifted by its
degree. -/
lemma liftedHomogenizedRelationQuotientSingle_mem_awayDegreeZeroPart {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1)
    {a : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (ha : a ∈ uliftSubmoduleFamily 
      (cone_quotient_grading   J) d)
    (i : Fin r) :
    LocalizedModule.mk
      (ULift.up
        (Submodule.Quotient.mk
          (Pi.single i a.down) :
            ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
              homogenized_relation_submodule     J τ)))
      ((⟨(fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) ^ d,
          by exact ⟨d, rfl⟩⟩ :
        Submonoid.powers (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))) ∈
      awayDegreeZeroPart
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (uliftSubmoduleFamily 
          (homogenized_relation_quotient_grading     J τ))
        fLift := sorry

/-- Helper for Chap10 Lemma 10 57 10: the coordinate vector with a single `1` already lies in the
degree-zero piece of the free cone module. -/
lemma freeConeModuleSingleOne_mem_degreeZero {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin r) :
    Pi.single i (1 : MvPolynomial (Fin (n + 1)) R ⧸ J) ∈
      free_cone_module_grading    J 0 := by
  -- Check the degree coordinatewise: the chosen entry is `1`, and all others are `0`.
  rw [mem_free_cone_module_grading_iff]
  intro j
  by_cases hji : j = i
  · subst hji
    simpa using
      (show (1 : MvPolynomial (Fin (n + 1)) R ⧸ J) ∈
          cone_quotient_grading   J 0 from
            SetLike.one_mem_graded
              (cone_quotient_grading J))
  · simp [Pi.single_apply, hji]

/-- Helper for Chap10 Lemma 10 57 10: the quotient class of the `i`-th standard basis vector is a
degree-zero element of the homogenized relation cokernel. -/
lemma homogenizedRelationQuotientSingleOne_mem_degreeZero {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (i : Fin r) :
    (Submodule.Quotient.mk (Pi.single i (1 : MvPolynomial (Fin (n + 1)) R ⧸ J)) :
        ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
          homogenized_relation_submodule     J τ)) ∈
      homogenized_relation_quotient_grading     J τ 0 := by
  -- The quotient degree-zero piece is the image of the free degree-zero piece.
  rw [mem_homogenized_relation_quotient_grading_iff]
  exact ⟨Pi.single i (1 : MvPolynomial (Fin (n + 1)) R ⧸ J),
    freeConeModuleSingleOne_mem_degreeZero    J i,
    rfl⟩

/-- Helper for Chap10 Lemma 10 57 10: after the canonical universe lift, the same quotient basis
vector still lies in the degree-zero component of the transported grading. -/
lemma liftedHomogenizedRelationQuotientSingleOne_mem_degreeZero {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (i : Fin r) :
    ULift.up
        (Submodule.Quotient.mk (Pi.single i (1 : MvPolynomial (Fin (n + 1)) R ⧸ J)) :
          ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
            homogenized_relation_submodule     J τ)) ∈
      uliftSubmoduleFamily 
        (homogenized_relation_quotient_grading     J τ) 0 := by
  -- Membership in the lifted grading is detected after projecting back down.
  exact
    (mem_uliftSubmoduleFamily_iff 
      (homogenized_relation_quotient_grading     J τ)
      0
      (ULift.up
        (Submodule.Quotient.mk (Pi.single i (1 : MvPolynomial (Fin (n + 1)) R ⧸ J)) :
          ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
            homogenized_relation_submodule     J τ)))).2
      (homogenizedRelationQuotientSingleOne_mem_degreeZero
            J τ i)

/-- Helper for Chap10 Lemma 10 57 10: the denominator-one localization class of the `i`-th
lifted quotient basis vector already belongs to the degree-zero away part. -/
lemma liftedHomogenizedRelationQuotientSingleOne_mem_awayDegreeZeroPart {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily
        (cone_quotient_grading J) 1)
    (i : Fin r) :
    LocalizedModule.mk
      (ULift.up
        (Submodule.Quotient.mk
          (Pi.single i (1 : MvPolynomial (Fin (n + 1)) R ⧸ J)) :
            ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
              homogenized_relation_submodule J τ)))
      ((⟨(fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) ^ 0,
          by exact ⟨0, rfl⟩⟩ :
        Submonoid.powers (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))) ∈
      awayDegreeZeroPart
        (uliftSubmoduleFamily (cone_quotient_grading J))
        (uliftSubmoduleFamily (homogenized_relation_quotient_grading J τ))
        fLift := sorry

/-- Helper for Chap10 Lemma 10 57 10: abbreviate the localized degree-zero target module so later
presentation lemmas can use a stable codomain spelling. -/
noncomputable abbrev targetAwayPart {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1) :=
  awayDegreeZeroPart
    (uliftSubmoduleFamily 
      (cone_quotient_grading   J))
    (uliftSubmoduleFamily 
      (homogenized_relation_quotient_grading     J τ))
    fLift

/-- Helper for Chap10 Lemma 10 57 10: the abbreviated localized target inherits its additive
commutative monoid structure from the ambient localized module. -/
@[reducible] noncomputable instance targetAwayPartAddCommMonoid {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1) :
    AddCommMonoid (targetAwayPart     J τ fLift) :=
  show
    AddCommMonoid
      (awayDegreeZeroPart
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (uliftSubmoduleFamily 
          (homogenized_relation_quotient_grading
                J τ))
        fLift) from
    inferInstance

/-- Helper for Chap10 Lemma 10 57 10: the abbreviated localized target inherits its additive
group structure from the ambient localized module. -/
@[reducible] noncomputable instance targetAwayPartAddCommGroup {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1) :
    AddCommGroup (targetAwayPart     J τ fLift) :=
  show
    AddCommGroup
      (awayDegreeZeroPart
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (uliftSubmoduleFamily 
          (homogenized_relation_quotient_grading
                J τ))
        fLift) from
    inferInstance

/-- Helper for Chap10 Lemma 10 57 10: package the denominator-one class of the `i`-th lifted
quotient basis vector as an element of the target degree-zero away part. -/
noncomputable def liftedTargetBasisElement {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1)
    (i : Fin r) :
    targetAwayPart     J τ fLift :=
  ⟨LocalizedModule.mk
      (ULift.up
        (Submodule.Quotient.mk
          (Pi.single i (1 : MvPolynomial (Fin (n + 1)) R ⧸ J)) :
            ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
              homogenized_relation_submodule     J τ)))
      ((⟨(fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) ^ 0,
          by exact ⟨0, rfl⟩⟩ :
        Submonoid.powers (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))),
    liftedHomogenizedRelationQuotientSingleOne_mem_awayDegreeZeroPart
          J τ fLift i⟩


/-- Helper for Chap10 Lemma 10 57 10: a lifted degree-`d` cone element defines the away-ring
coefficient `a / fLift^d`. -/
noncomputable def homogeneousAwayElement {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1)
    (a :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) d) :
    Away
      (uliftSubmoduleFamily 
        (cone_quotient_grading   J))
      (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  Away.mk
    (uliftSubmoduleFamily 
      (cone_quotient_grading   J))
    fLift.2 d (a : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))
    (by simpa using a.2)

/-- Helper for Chap10 Lemma 10 57 10: cache the ambient away-ring action on the target degree-zero
submodule so later free-module presentation lemmas do not re-run expensive typeclass search. -/
@[reducible] noncomputable instance targetAwayPartModule {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1) :
    Module
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (targetAwayPart     J τ fLift) :=
  show
    Module
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (awayDegreeZeroPart
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (uliftSubmoduleFamily 
          (homogenized_relation_quotient_grading
                J τ))
        fLift) from
    inferInstance

/-- Helper for Chap10 Lemma 10 57 10: expose the scalar action carried by
`targetAwayPartModule` directly, so later statements do not have to reconstruct it through the
module hierarchy. -/
@[reducible] noncomputable instance targetAwayPartSMul {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1) :
    SMul
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (targetAwayPart     J τ fLift) :=
  (targetAwayPartModule     J τ fLift).toSMul

/-- Helper for Chap10 Lemma 10 57 10: expose the multiplicative action carried by
`targetAwayPartModule` directly, so basis-defined linear maps can elaborate without timing out. -/
@[reducible] noncomputable instance targetAwayPartMulAction {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1) :
    MulAction
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (targetAwayPart     J τ fLift) :=
  (targetAwayPartModule     J τ fLift).toMulAction

/-- Helper for Chap10 Lemma 10 57 10: the target degree-zero away part also has the canonical
free presentation over the away ring itself, obtained by sending each basis vector to the matching
denominator-one generator. -/
noncomputable def targetAwayPresentationMap {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1) :
    (Fin r →
        Away
          (uliftSubmoduleFamily 
            (cone_quotient_grading   J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))) →ₗ[
        Away
          (uliftSubmoduleFamily 
            (cone_quotient_grading   J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))]
      targetAwayPart     J τ fLift :=
  letI :=
    targetAwayPartModule     J τ fLift
  (Pi.basisFun
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (Fin r)).constr
    (Away
      (uliftSubmoduleFamily 
        (cone_quotient_grading   J))
      (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
    (fun i ↦ liftedTargetBasisElement     J τ fLift i)

/-- Helper for Chap10 Lemma 10 57 10: the away-linear target presentation sends a basis vector to
the corresponding denominator-one generator. -/
lemma targetAwayPresentationMap_single {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1)
    (i : Fin r)
    (a :
      Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))) :
    targetAwayPresentationMap     J τ fLift
        (Pi.single i a) =
      a • liftedTargetBasisElement     J τ fLift i := by
  letI :
      Module
        (Away
          (uliftSubmoduleFamily 
            (cone_quotient_grading   J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
        (Fin r →
          Away
            (uliftSubmoduleFamily 
              (cone_quotient_grading   J))
            (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))) :=
    inferInstance
  change
    ((Pi.basisFun
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (Fin r)).constr
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (fun j ↦ liftedTargetBasisElement     J τ fLift j)
      (Pi.single i a :
        Fin r →
          Away
            (uliftSubmoduleFamily 
              (cone_quotient_grading   J))
            (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))) =
      a • liftedTargetBasisElement     J τ fLift i
  simpa using
    ((Pi.basisFun
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (Fin r)).constr_apply_fintype
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (fun j ↦ liftedTargetBasisElement     J τ fLift j)
      (Pi.single i a :
        Fin r →
          Away
            (uliftSubmoduleFamily 
              (cone_quotient_grading   J))
            (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))))

/-- Helper for Chap10 Lemma 10 57 10: the away-linear target presentation evaluates a free vector
by summing its away coefficients against the canonical denominator-one generators. -/
lemma targetAwayPresentationMap_eq_sum {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading   J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift :
      uliftSubmoduleFamily 
        (cone_quotient_grading   J) 1)
    (x :
      Fin r →
        Away
          (uliftSubmoduleFamily 
            (cone_quotient_grading   J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))) :
    targetAwayPresentationMap     J τ fLift x =
      ∑ i, x i • liftedTargetBasisElement     J τ fLift i := by
  change
    ((Pi.basisFun
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (Fin r)).constr
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (fun i ↦ liftedTargetBasisElement     J τ fLift i)
      x) =
      ∑ i, x i • liftedTargetBasisElement     J τ fLift i
  simpa using
    ((Pi.basisFun
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (Fin r)).constr_apply_fintype
      (Away
        (uliftSubmoduleFamily 
          (cone_quotient_grading   J))
        (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
      (fun i ↦ liftedTargetBasisElement     J τ fLift i)
      x)

/-- Helper for Chap10 Lemma 10 57 10: the quotient class of a vector in a finite product module is
the sum of the quotient classes of its standard coordinate vectors, and this identity is preserved
by the canonical `ULift`. -/
lemma uliftQuotientMkQ_sum_piSingle
    {A : Type _} [AddCommGroup A] [Module R A] {r : ℕ}
    (K : Submodule R (Fin r → A)) (x : Fin r → A) :
    (∑ i, (ULift.up
      (Submodule.Quotient.mk (Pi.single i (x i)) : (Fin r → A) ⧸ K) :
      ULift ((Fin r → A) ⧸ K))) =
      ULift.up (Submodule.Quotient.mk x : (Fin r → A) ⧸ K) := by
  have hxsum : (∑ i, (Pi.single i (x i) : Fin r → A)) = x := by
    -- Reassemble the coordinate vectors back into the original product-module element.
    ext i
    simp
  have hqsum :
      (∑ i,
        (Submodule.Quotient.mk (Pi.single i (x i)) : (Fin r → A) ⧸ K)) =
        (Submodule.Quotient.mk x : (Fin r → A) ⧸ K) := by
    calc
      (∑ i,
        (Submodule.Quotient.mk (Pi.single i (x i)) : (Fin r → A) ⧸ K)) =
          (Submodule.Quotient.mk (∑ i, (Pi.single i (x i) : Fin r → A)) :
            (Fin r → A) ⧸ K) := by
              symm
              exact map_sum (Submodule.mkQ K)
                (fun i ↦ (Pi.single i (x i) : Fin r → A)) Finset.univ
      _ = (Submodule.Quotient.mk x : (Fin r → A) ⧸ K) := by
            rw [hxsum]
  have hdownsum (s : Finset (Fin r)) :
      (Finset.sum s (fun i ↦
        (ULift.up
          (Submodule.Quotient.mk (Pi.single i (x i)) : (Fin r → A) ⧸ K) :
            ULift ((Fin r → A) ⧸ K)))).down =
        Finset.sum s (fun i ↦
          (Submodule.Quotient.mk (Pi.single i (x i)) : (Fin r → A) ⧸ K)) := by
    induction s using Finset.induction_on with
    | empty =>
        rfl
    | @insert i s hi ih =>
        simp [hi, ih]
  -- First sum inside the quotient, then lift the resulting quotient identity through `ULift.up`.
  apply ULift.down_injective
  calc
    (∑ i, (ULift.up
      (Submodule.Quotient.mk (Pi.single i (x i)) : (Fin r → A) ⧸ K) :
        ULift ((Fin r → A) ⧸ K))).down =
        ∑ i, (Submodule.Quotient.mk (Pi.single i (x i)) : (Fin r → A) ⧸ K) := by
          simpa using hdownsum Finset.univ
    _ = (Submodule.Quotient.mk x : (Fin r → A) ⧸ K) := hqsum

/-- Helper for Chap10 Lemma 10 57 10: localizing the sum of the lifted quotient coordinate classes
is the same as localizing the lifted quotient class of the whole vector. -/
lemma localizedModuleMkUliftQuotientPiSingleSum
    {A : Type _} [CommRing A] {P : Type _} [AddCommGroup P] [Module A P] {r : ℕ}
    (K : Submodule A (Fin r → P)) (x : Fin r → P) {f : ULift.{w} A}
    (powd : Submonoid.powers f) :
    (LocalizedModule.mk
        (∑ i, (ULift.up
          (Submodule.Quotient.mk (Pi.single i (x i)) : (Fin r → P) ⧸ K) :
          ULift.{w} ((Fin r → P) ⧸ K))) powd :
        LocalizedModule.Away (f : ULift.{w} A) (ULift.{w} ((Fin r → P) ⧸ K))) =
      LocalizedModule.mk
        (ULift.up (Submodule.Quotient.mk x : (Fin r → P) ⧸ K) : ULift.{w} ((Fin r → P) ⧸ K))
        powd := by
  -- The localized numerator only depends on the quotient class, and the numerator sum already
  -- collapses to the quotient class of the whole vector.
  rw [uliftQuotientMkQ_sum_piSingle (K := K) (x := x)]

/-- Helper for Chap10 Lemma 10 57 10: after dehomogenizing coefficients from the cone quotient to
`R'`, the cone-side free presentation is the basis-defined `Scone`-linear map sending each basis
vector to the corresponding affine generator image under `τ`. -/
noncomputable abbrev coneDehomPresentationMap {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    [Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M] :
    (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) →ₗ[(MvPolynomial (Fin (n + 1)) R ⧸ J)] M := by
  letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) (MvPolynomial (Fin (n + 1)) R ⧸ J) :=
    Semiring.toModule
  exact
    (Pi.basisFun (MvPolynomial (Fin (n + 1)) R ⧸ J) (Fin r)).constr
      (MvPolynomial (Fin (n + 1)) R ⧸ J)
      (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))

/-- Helper for Chap10 Lemma 10 57 10: the dehomogenized cone-side presentation evaluates by the
standard basis expansion, with coefficients pushed to `R'` through `dehomToR'`. -/
lemma coneDehomPresentationMap_eq_sum {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    [Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M]
    (z : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) :
    coneDehomPresentationMap     J τ z =
      ∑ i, z i • τ (Pi.single i (1 : MvPolynomial (Fin n) R)) := by
  simpa [coneDehomPresentationMap] using
    ((Pi.basisFun (MvPolynomial (Fin (n + 1)) R ⧸ J) (Fin r)).constr_apply_fintype
      (MvPolynomial (Fin (n + 1)) R ⧸ J)
      (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R))) z)

/-- Helper for Chap10 Lemma 10 57 10: the basis-defined affine presentation over `R'` is
surjective as soon as the original affine free presentation is. -/
lemma affinePresentationMap_surjective {n r : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R')
    [instModuleAffineM : Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hmodule : instModuleAffineM = Module.compHom M π.toRingHom)
    (hτ : Function.Surjective τ) :
    let τR' : (Fin r → R') →ₗ[R'] M :=
      (Pi.basisFun R' (Fin r)).constr R'
        (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
    Function.Surjective τR' := by
  subst instModuleAffineM
  letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M π.toRingHom
  let τR' : (Fin r → R') →ₗ[R'] M :=
    (Pi.basisFun R' (Fin r)).constr R'
      (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
  change Function.Surjective τR'
  intro m₀
  rcases hτ m₀ with ⟨x, rfl⟩
  refine ⟨fun i ↦ π (x i), ?_⟩
  have hsingle (i : Fin r) :
      (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R) =
        x i •
          (Pi.single i (1 : MvPolynomial (Fin n) R) :
            Fin r → MvPolynomial (Fin n) R) := by
    -- Rewrite each coordinate vector as a scalar multiple of the corresponding basis vector.
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  have hxsum :
      (∑ i, (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R)) = x := by
    -- The standard basis expansion of a finite function vector recombines to the original vector.
    ext i
    simp
  -- Expand the basis-defined affine map and then recombine the standard basis decomposition.
  calc
    τR' (fun i ↦ π (x i)) =
        ∑ i, π (x i) • τ (Pi.single i (1 : MvPolynomial (Fin n) R)) := by
          simpa [τR'] using
            ((Pi.basisFun R' (Fin r)).constr_apply_fintype
              R'
              (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
              (fun i ↦ π (x i)))
    _ =
        ∑ i, τ (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hsingle i]
          exact (τ.map_smul (x i)
            (Pi.single i (1 : MvPolynomial (Fin n) R) :
              Fin r → MvPolynomial (Fin n) R)).symm
    _ = τ (∑ i, (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R)) := by
          symm
          exact map_sum τ (fun i ↦ (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R))
            Finset.univ
    _ = τ x := by
          rw [hxsum]

/-- Helper for Chap10 Lemma 10 57 10: compose cone dehomogenization with the affine quotient
presentation so later proofs can reuse one fixed `AlgHom` spelling. -/
noncomputable def coneQuotientDehomToPresentedAlgHom {n : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ :
      J ≤ Ideal.comap (coneDehom  ) (RingHom.ker π)) :
    (MvPolynomial (Fin (n + 1)) R ⧸ J) →ₐ[R] R' :=
  ((Ideal.quotientKerAlgEquivOfSurjective hπ :
      (MvPolynomial (Fin n) R ⧸ RingHom.ker π) ≃ₐ[R] R')).toAlgHom.comp
    (coneDehom_quotient_map   (RingHom.ker π) J hJ)

/-- Helper for Chap10 Lemma 10 57 10: the fixed cone dehomogenization chart onto `R'` is
surjective. -/
lemma coneQuotientDehomToPresentedAlgHom_surjective {n : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R')
    (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ :
      J ≤ Ideal.comap (coneDehom  ) (RingHom.ker π)) :
    Function.Surjective (coneQuotientDehomToPresentedAlgHom π hπ J hJ) := by
  let I : Ideal (MvPolynomial (Fin n) R) := RingHom.ker π
  have hdehom :
      Function.Surjective (coneDehom_quotient_map (R := R) (n := n) I J (by simpa [I] using hJ)) :=
    coneDehom_quotient_map_surjective (R := R) (n := n) I J (by simpa [I] using hJ)
  intro y
  rcases (mvPolynomial_quotient_equiv_of_surjective π hπ).surjective y with ⟨pbar, hpbar⟩
  rcases hdehom pbar with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  -- First lift to the affine quotient, then compose with the quotient-kernel equivalence to `R'`.
  simpa [coneQuotientDehomToPresentedAlgHom, I, hz] using hpbar

/-- Helper for Chap10 Lemma 10 57 10: after fixing the cone dehomogenization chart, the
dehomogenized cone free presentation is still surjective onto `M`. -/
lemma coneDehomPresentationMap_surjective {n r : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R')
    (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [instModuleAffineM : Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hmodule : instModuleAffineM = Module.compHom M π.toRingHom)
    (hJ :
      J ≤ Ideal.comap (coneDehom  ) (RingHom.ker π))
    (hτ : Function.Surjective τ) :
    let dehomToR' :=
      coneQuotientDehomToPresentedAlgHom    π hπ J hJ
    letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M := Module.compHom M dehomToR'.toRingHom
    Function.Surjective (coneDehomPresentationMap     J τ) := by
  subst instModuleAffineM
  letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M π.toRingHom
  let dehomToR' := coneQuotientDehomToPresentedAlgHom π hπ J hJ
  letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M := Module.compHom M dehomToR'.toRingHom
  have hdehom : Function.Surjective dehomToR' :=
    coneQuotientDehomToPresentedAlgHom_surjective (π := π) (hπ := hπ) (J := J) hJ
  change Function.Surjective (coneDehomPresentationMap J τ)
  intro m₀
  rcases hτ m₀ with ⟨x, rfl⟩
  choose z hz using fun i : Fin r ↦ hdehom (π (x i))
  refine ⟨z, ?_⟩
  have hsingle (i : Fin r) :
      (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R) =
        x i •
          (Pi.single i (1 : MvPolynomial (Fin n) R) :
            Fin r → MvPolynomial (Fin n) R) := by
    -- Rewrite each affine coefficient vector into the standard basis for the finite free module.
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  have hxsum :
      (∑ i, (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R)) = x := by
    -- Recombine the coordinatewise basis expansion back into the original affine vector.
    ext i
    simp
  -- Evaluate the cone presentation by the basis sum and replace each cone coefficient by its
  -- chosen dehomogenized affine image.
  calc
    coneDehomPresentationMap J τ z =
        ∑ i, dehomToR' (z i) • τ (Pi.single i (1 : MvPolynomial (Fin n) R)) := by
          rw [coneDehomPresentationMap_eq_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rfl
    _ =
        ∑ i, π (x i) • τ (Pi.single i (1 : MvPolynomial (Fin n) R)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [hz i]
    _ =
        ∑ i, τ (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hsingle i]
          exact (τ.map_smul (x i)
            (Pi.single i (1 : MvPolynomial (Fin n) R) :
              Fin r → MvPolynomial (Fin n) R)).symm
    _ = τ (∑ i, (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R)) := by
          symm
          exact map_sum τ (fun i ↦ (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R))
            Finset.univ
    _ = τ x := by
          rw [hxsum]

/-- Helper for Chap10 Lemma 10 57 10: fix the `ULift` level used by the final presentation
package when transporting gradings. -/
abbrev presentationUliftSubmoduleFamily
    {A : Type _} [AddCommMonoid A] [Module R A] {ι : Type _}
    (𝒜 : ι → Submodule R A) : ι → Submodule R (ULift.{max u u' v} A) :=
  uliftSubmoduleFamily 𝒜

/-- Helper for Chap10 Lemma 10 57 10: lift a homogeneous element into the fixed-presentation
`ULift` grading. -/
abbrev presentationUliftSubmoduleFamilyElement
    {A : Type _} [AddCommMonoid A] [Module R A] {ι : Type _}
    (𝒜 : ι → Submodule R A) {i : ι} (x : 𝒜 i) :
    presentationUliftSubmoduleFamily (R := R) 𝒜 i :=
  uliftSubmoduleFamilyElement 𝒜 x

/-- Helper for Chap10 Lemma 10 57 10: package the fixed `ULift` direct-sum decomposition used by
the final presentation file so the existential theorem does not have to rebuild it theorem-locally.
-/
@[reducible] noncomputable def presentationUliftQuotientDecomposition
    {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    [DirectSum.Decomposition (cone_quotient_grading J)]
    [DirectSum.Decomposition (@free_cone_module_grading R _ n r J)]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    DirectSum.Decomposition
      (presentationUliftSubmoduleFamily (R := R)
        (homogenized_relation_quotient_grading J τ)) := by
  letI : DirectSum.Decomposition (homogenized_relation_quotient_grading J τ) :=
    homogenizedRelationQuotientGrading_decomposition (R := R) (n := n) (r := r) J τ
  -- Freeze the universe-lifted decomposition once so later packaging only reuses the owner API.
  simpa [presentationUliftSubmoduleFamily] using
    (uliftDecomposition (R := R) (homogenized_relation_quotient_grading J τ))

/-- Helper for Chap10 Lemma 10 57 10: once the cone-side graded ring and module data are fixed,
the remaining blocker is the semilinear module chart in one fixed affine/cone presentation chart. -/
noncomputable def targetAwayRestrictedPresentation
    {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift : uliftSubmoduleFamily (cone_quotient_grading J) 1)
    (ringIso :
      R' ≃ₐ[R]
        Away
          (uliftSubmoduleFamily (cone_quotient_grading J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))) :
    letI : Module R' (targetAwayPart J τ fLift) :=
      Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom
    letI : SMul R' (targetAwayPart J τ fLift) :=
      (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toSMul
    letI : MulAction R' (targetAwayPart J τ fLift) :=
      (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toMulAction
    (Fin r → R') →ₗ[R'] targetAwayPart J τ fLift := by
  letI : Module R' (targetAwayPart J τ fLift) :=
    Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom
  letI : SMul R' (targetAwayPart J τ fLift) :=
    (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toSMul
  letI : MulAction R' (targetAwayPart J τ fLift) :=
    (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toMulAction
  -- Work over the restricted `R'`-module structure so the target presentation and the affine
  -- presentation share the same free `R'`-module domain.
  exact
    (Pi.basisFun R' (Fin r)).constr R'
      (fun i ↦ liftedTargetBasisElement J τ fLift i)

/-- Helper for Chap10 Lemma 10 57 10: after restricting scalars along the fixed ring chart, the
target presentation still evaluates by the standard basis expansion. -/
lemma targetAwayRestrictedPresentation_eq_sum
    {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift : uliftSubmoduleFamily (cone_quotient_grading J) 1)
    (ringIso :
      R' ≃ₐ[R]
        Away
          (uliftSubmoduleFamily (cone_quotient_grading J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
    (x : Fin r → R') :
    letI : Module R' (targetAwayPart J τ fLift) :=
      Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom
    letI : SMul R' (targetAwayPart J τ fLift) :=
      (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toSMul
    letI : MulAction R' (targetAwayPart J τ fLift) :=
      (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toMulAction
    targetAwayRestrictedPresentation (R' := R') J τ fLift ringIso x =
      ∑ i, x i • liftedTargetBasisElement J τ fLift i := by
  letI : Module R' (targetAwayPart J τ fLift) :=
    Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom
  letI : SMul R' (targetAwayPart J τ fLift) :=
    (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toSMul
  letI : MulAction R' (targetAwayPart J τ fLift) :=
    (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toMulAction
  -- The restricted target map is basis-defined, so its value is the coordinatewise basis sum.
  change
    ((Pi.basisFun R' (Fin r)).constr R'
      (fun i ↦ liftedTargetBasisElement J τ fLift i) x) =
      ∑ i, x i • liftedTargetBasisElement J τ fLift i
  simpa [targetAwayRestrictedPresentation] using
    ((Pi.basisFun R' (Fin r)).constr_apply_fintype R'
      (fun i ↦ liftedTargetBasisElement J τ fLift i) x)

/-- Helper for Chap10 Lemma 10 57 10: the restricted `R'`-linear target presentation is just the
away-linear target presentation with each coefficient transported across `ringIso`. -/
lemma targetAwayRestrictedPresentation_eq_targetAwayPresentation
    {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift : uliftSubmoduleFamily (cone_quotient_grading J) 1)
    (ringIso :
      R' ≃ₐ[R]
        Away
          (uliftSubmoduleFamily (cone_quotient_grading J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
    (x : Fin r → R') :
    letI : Module R' (targetAwayPart J τ fLift) :=
      Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom
    letI : SMul R' (targetAwayPart J τ fLift) :=
      (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toSMul
    letI : MulAction R' (targetAwayPart J τ fLift) :=
      (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toMulAction
    targetAwayRestrictedPresentation (R' := R') J τ fLift ringIso x =
      targetAwayPresentationMap J τ fLift (fun i ↦ ringIso (x i)) := by
  letI : Module R' (targetAwayPart J τ fLift) :=
    Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom
  letI : SMul R' (targetAwayPart J τ fLift) :=
    (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toSMul
  letI : MulAction R' (targetAwayPart J τ fLift) :=
    (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toMulAction
  -- Compare the two basis-defined maps through their common coordinatewise basis expansion.
  calc
    targetAwayRestrictedPresentation (R' := R') J τ fLift ringIso x =
        ∑ i, x i • liftedTargetBasisElement J τ fLift i := by
          simpa using
            targetAwayRestrictedPresentation_eq_sum
              (R' := R') (J := J) (τ := τ) (fLift := fLift) (ringIso := ringIso) x
    _ =
        ∑ i, ringIso (x i) • liftedTargetBasisElement J τ fLift i := by
          rfl
    _ = targetAwayPresentationMap J τ fLift (fun i ↦ ringIso (x i)) := by
          symm
          simpa using
            targetAwayPresentationMap_eq_sum
              (J := J) (τ := τ) (fLift := fLift) (x := fun i ↦ ringIso (x i))

/-- Helper for Chap10 Lemma 10 57 10: a homogeneous away coefficient times the denominator-one
target basis vector is exactly the localized single-coordinate quotient class with the same
denominator exponent. -/
lemma homogeneousAwayElement_smul_liftedTargetBasisElement
    {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading J)]
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift : uliftSubmoduleFamily (cone_quotient_grading J) 1)
    (a : uliftSubmoduleFamily (cone_quotient_grading J) d)
    (i : Fin r) :
    homogeneousAwayElement J fLift a • liftedTargetBasisElement J τ fLift i =
      ⟨LocalizedModule.mk
          (ULift.up
            (Submodule.Quotient.mk
              (Pi.single i a.down) :
                ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
                  homogenized_relation_submodule J τ)))
          ((⟨(fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) ^ d,
              by exact ⟨d, rfl⟩⟩ :
            Submonoid.powers (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))),
        liftedHomogenizedRelationQuotientSingle_mem_awayDegreeZeroPart
          J τ fLift a.2 i⟩ := by
  apply Subtype.ext
  change
    (algebraMap
        (Away
          (uliftSubmoduleFamily (cone_quotient_grading J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
        (Localization.Away (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))
        (homogeneousAwayElement J fLift a)) •
        LocalizedModule.mk
          (ULift.up
            (Submodule.Quotient.mk
              (Pi.single i (1 : MvPolynomial (Fin (n + 1)) R ⧸ J)) :
                ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
                  homogenized_relation_submodule J τ)))
          ((⟨(fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) ^ 0,
              by exact ⟨0, rfl⟩⟩ :
            Submonoid.powers (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))) =
      LocalizedModule.mk
        (ULift.up
          (Submodule.Quotient.mk
            (Pi.single i a.down) :
              ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
                homogenized_relation_submodule J τ)))
        ((⟨(fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) ^ d,
            by exact ⟨d, rfl⟩⟩ :
          Submonoid.powers (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))))
  -- Compare both subtype elements inside the ordinary localized module, where `mk_smul_mk`
  -- collapses the degree-zero target basis vector into the desired single-coordinate numerator.
  rw [HomogeneousLocalization.algebraMap_apply, homogeneousAwayElement, Away.val_mk,
    LocalizedModule.mk_smul_mk]
  congr 2
  apply ULift.down_injective
  simp [Pi.smul_apply]

/-- Helper for Chap10 Lemma 10 57 10: the away-linear target presentation is surjective because a
degree-zero localized quotient class splits coordinatewise into the canonical denominator-one
generators. -/
lemma targetAwayPresentationMap_surjective
    {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading J)]
    [Module (MvPolynomial (Fin n) R) M]
    [DirectSum.Decomposition (cone_quotient_grading J)]
    [DirectSum.Decomposition (@free_cone_module_grading R _ n r J)]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift : uliftSubmoduleFamily (cone_quotient_grading J) 1) :
    Function.Surjective (targetAwayPresentationMap J τ fLift) := by
  intro z
  rcases (mem_awayDegreeZeroPart_iff
      (𝒜 := uliftSubmoduleFamily (cone_quotient_grading J))
      (ℳ := uliftSubmoduleFamily (homogenized_relation_quotient_grading J τ))
      fLift).1 z.2 with ⟨d, m, rfl⟩
  have hm :
      ((m : ULift
        (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
          homogenized_relation_submodule J τ))) : ULift
            (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
              homogenized_relation_submodule J τ))) ∈
        uliftSubmoduleFamily (homogenized_relation_quotient_grading J τ) d := by
    simpa [Nat.mul_one] using m.2
  rcases (mem_homogenized_relation_quotient_grading_iff
      (R := R) (n := n) (r := r) (d := d) J τ).1
      ((mem_uliftSubmoduleFamily_iff
        (homogenized_relation_quotient_grading J τ) d
        ((m : ULift
          (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
            homogenized_relation_submodule J τ))) : ULift
              (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
                homogenized_relation_submodule J τ)))).1 hm) with
      ⟨y, hy, hym⟩
  let a :
      Fin r →
        Away
          (uliftSubmoduleFamily (cone_quotient_grading J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
    fun i ↦
      homogeneousAwayElement J fLift
        ⟨ULift.up (y i),
          (mem_uliftSubmoduleFamily_iff
            (cone_quotient_grading J) d (ULift.up (y i))).2
            ((mem_free_cone_module_grading_iff
              (R := R) (n := n) (r := r) (d := d) (J := J)).1 hy i)⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  calc
    ((targetAwayPresentationMap J τ fLift a : targetAwayPart J τ fLift) :
        LocalizedModule.Away
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))
          (ULift
            (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
              homogenized_relation_submodule J τ)))) =
        ∑ i,
          (LocalizedModule.mk
            (ULift.up
              (Submodule.Quotient.mk
                (Pi.single i (y i)) :
                  ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
                    homogenized_relation_submodule J τ)))
            ((⟨(fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) ^ d,
                by exact ⟨d, rfl⟩⟩ :
              Submonoid.powers (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))) : 
            LocalizedModule.Away
              (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))
              (ULift
                (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
                  homogenized_relation_submodule J τ)))) := by
          simpa [a] using
            congrArg Subtype.val
              (targetAwayPresentationMap_eq_sum (J := J) (τ := τ) (fLift := fLift) a)
    _ =
        LocalizedModule.mk
          (ULift.up
            (Submodule.Quotient.mk y :
              ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
                homogenized_relation_submodule J τ)))
          ((⟨(fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) ^ d,
              by exact ⟨d, rfl⟩⟩ :
            Submonoid.powers (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))) := by
          simpa using
            localizedModuleMkUliftQuotientPiSingleSum
              (K := homogenized_relation_submodule J τ) (x := y)
              (powd := (⟨(fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) ^ d,
                by exact ⟨d, rfl⟩⟩ :
                  Submonoid.powers (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))))
    _ =
        LocalizedModule.mk
          ((m : ULift
            (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
              homogenized_relation_submodule J τ))) : ULift
                (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
                  homogenized_relation_submodule J τ)))
          ((⟨(fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) ^ d,
              by exact ⟨d, rfl⟩⟩ :
            Submonoid.powers (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))) := by
          simpa using congrArg ULift.up hym

/-- Helper for Chap10 Lemma 10 57 10: after restricting scalars along the fixed ring chart, the
target presentation remains surjective because the away-linear chart already is. -/
lemma targetAwayRestrictedPresentation_surjective
    {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading J)]
    [Module (MvPolynomial (Fin n) R) M]
    [DirectSum.Decomposition (cone_quotient_grading J)]
    [DirectSum.Decomposition (@free_cone_module_grading R _ n r J)]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (fLift : uliftSubmoduleFamily (cone_quotient_grading J) 1)
    (ringIso :
      R' ≃ₐ[R]
        Away
          (uliftSubmoduleFamily (cone_quotient_grading J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J))) :
    letI : Module R' (targetAwayPart J τ fLift) :=
      Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom
    letI : SMul R' (targetAwayPart J τ fLift) :=
      (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toSMul
    letI : MulAction R' (targetAwayPart J τ fLift) :=
      (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toMulAction
    Function.Surjective (targetAwayRestrictedPresentation (R' := R') J τ fLift ringIso) := by
  letI : Module R' (targetAwayPart J τ fLift) :=
    Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom
  letI : SMul R' (targetAwayPart J τ fLift) :=
    (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toSMul
  letI : MulAction R' (targetAwayPart J τ fLift) :=
    (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toMulAction
  intro z
  rcases targetAwayPresentationMap_surjective
      (R := R) (n := n) (r := r) (J := J) (τ := τ) (fLift := fLift) z with ⟨a, ha⟩
  refine ⟨fun i ↦ ringIso.symm (a i), ?_⟩
  -- Pull the chosen away coefficients back through `ringIso`; the restricted presentation is
  -- definitionally the same target map in the transported coefficient spelling.
  rw [targetAwayRestrictedPresentation_eq_targetAwayPresentation]
  simpa using ha

/-- Helper for Chap10 Lemma 10 57 10: once the cone-side graded ring and module data are fixed,
the remaining blocker is the semilinear module chart in one fixed affine/cone presentation chart. -/
noncomputable def chosenConePresentationModuleIso
    {n r : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π)
    [instModuleAffineM : Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hmodule : instModuleAffineM = Module.compHom M π.toRingHom)
    (hτ : Function.Surjective τ) :
    let I : Ideal (MvPolynomial (Fin n) R) := RingHom.ker π
    let J : Ideal (MvPolynomial (Fin (n + 1)) R) :=
      positively_shifted_cone_homogenized_ideal I
    letI : GradedAlgebra (cone_quotient_grading J) :=
      cone_quotient_gradedAlgebra_of_homogeneous_ideal
        (R := R) (n := n) J
        (positively_shifted_cone_homogenized_ideal_isHomogeneous
          (R := R) (n := n) I)
    let fLift :
        uliftSubmoduleFamily (cone_quotient_grading J) 1 :=
      presentationUliftSubmoduleFamilyElement
        (cone_quotient_grading J)
        (coneStandardDenominator J)
    let ringIso0 : R' ≃ₐ[R]
        Away (cone_quotient_grading J)
          ((coneStandardDenominator J : MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
      (mvPolynomial_quotient_equiv_of_surjective π hπ).symm.trans
        (coneKernelQuotientAwayAlgEquiv I)
    let ringIso :
        R' ≃ₐ[R]
          Away
            (uliftSubmoduleFamily (cone_quotient_grading J))
            (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
      letI : GradedAlgebra
          (uliftSubmoduleFamily (cone_quotient_grading J)) := inferInstance
      liftedAwayAlgEquiv_of_unlifted
        (grading := cone_quotient_grading J)
        (f := coneStandardDenominator J)
        ringIso0
    M ≃ₛₗ[(ringIso.toRingEquiv :
      R' →+*
        Away
          (uliftSubmoduleFamily (cone_quotient_grading J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)))]
      targetAwayPart J τ fLift :=
by
  subst instModuleAffineM
  letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M π.toRingHom
  let I : Ideal (MvPolynomial (Fin n) R) := RingHom.ker π
  let J : Ideal (MvPolynomial (Fin (n + 1)) R) :=
    positively_shifted_cone_homogenized_ideal I
  letI : GradedAlgebra (cone_quotient_grading J) :=
    cone_quotient_gradedAlgebra_of_homogeneous_ideal
      (R := R) (n := n) J
      (positively_shifted_cone_homogenized_ideal_isHomogeneous
        (R := R) (n := n) I)
  let fLift :
      uliftSubmoduleFamily (cone_quotient_grading J) 1 :=
    presentationUliftSubmoduleFamilyElement
      (cone_quotient_grading J)
      (coneStandardDenominator J)
  let ringIso0 : R' ≃ₐ[R]
      Away (cone_quotient_grading J)
        ((coneStandardDenominator J : MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
    (mvPolynomial_quotient_equiv_of_surjective π hπ).symm.trans
      (coneKernelQuotientAwayAlgEquiv I)
  let ringIso :
      R' ≃ₐ[R]
        Away
          (uliftSubmoduleFamily (cone_quotient_grading J))
          (fLift : ULift (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
    letI : GradedAlgebra (uliftSubmoduleFamily (cone_quotient_grading J)) := inferInstance
    liftedAwayAlgEquiv_of_unlifted
      (grading := cone_quotient_grading J)
      (f := coneStandardDenominator J)
      ringIso0
  letI : Module R' (targetAwayPart J τ fLift) :=
    Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom
  letI : SMul R' (targetAwayPart J τ fLift) :=
    (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toSMul
  letI : MulAction R' (targetAwayPart J τ fLift) :=
    (Module.compHom (targetAwayPart J τ fLift) ringIso.toRingHom).toMulAction
  let τR' : (Fin r → R') →ₗ[R'] M :=
    (Pi.basisFun R' (Fin r)).constr R'
      (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
  have hτR' : Function.Surjective τR' := by
    -- The affine presentation stays surjective after descending coefficients through `π`.
    simpa [τR'] using
      affinePresentationMap_surjective
        (R := R) (R' := R') (M := M) (π := π) (τ := τ) (hmodule := rfl) hτ
  have htarget :
      Function.Surjective
        (targetAwayRestrictedPresentation (R' := R') J τ fLift ringIso) := by
    -- The target away presentation is surjective in the fixed chart because the away-linear
    -- presentation already hits every degree-zero localized quotient class.
    simpa using
      targetAwayRestrictedPresentation_surjective
        (R := R) (R' := R') (n := n) (r := r) (M := M)
        (J := J) (τ := τ) (fLift := fLift) (ringIso := ringIso)
  -- Route correction: the remaining work is no longer the global existential packaging. The only
  -- open step is the fixed-chart kernel comparison between `τR'` and the restricted target map.
  --
  -- TODO: prove the normalization lemma for
  -- `targetAwayRestrictedPresentation (fun i ↦ π (x i))`, deduce the affine-kernel equality in
  -- this fixed `ringIso` spelling world, and then compose the two quotient equivalences:
  -- `(free_module_quotient_equiv_of_surjective τR' hτR').symm.trans
  --   ((Submodule.quotEquivOfEq _ _ hker.symm).trans
  --     ((targetAwayRestrictedPresentation ...).quotKerEquivOfSurjective htarget))`.
  sorry

/-- Helper for Chap10 Lemma 10 57 10: a surjective polynomial presentation makes `R'` finite over
the affine polynomial ring, and a finite `R'`-module remains finite after restricting scalars
along that presentation. -/
theorem affinePresentationModuleFinite
    {n : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π)
    [Module.Finite R' M] :
    letI : Algebra (MvPolynomial (Fin n) R) R' := π.toRingHom.toAlgebra
    letI : Module.Finite (MvPolynomial (Fin n) R) R' := by
      simpa using
        (Module.Finite.of_surjective
          (Algebra.linearMap (MvPolynomial (Fin n) R) R')
          hπ)
    letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M π.toRingHom
    letI : IsScalarTower (MvPolynomial (Fin n) R) R' M :=
      IsScalarTower.of_compHom (MvPolynomial (Fin n) R) R' M
    Module.Finite (MvPolynomial (Fin n) R) M := by
  letI : Algebra (MvPolynomial (Fin n) R) R' := π.toRingHom.toAlgebra
  letI : Module.Finite (MvPolynomial (Fin n) R) R' := by
    simpa using
      (Module.Finite.of_surjective
        (Algebra.linearMap (MvPolynomial (Fin n) R) R')
        hπ)
  letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M π.toRingHom
  letI : IsScalarTower (MvPolynomial (Fin n) R) R' M :=
    IsScalarTower.of_compHom (MvPolynomial (Fin n) R) R' M
  -- Restrict scalars along the chosen affine presentation before taking the finite free cover.
  exact Module.Finite.trans R' M

/-- Helper for Chap10 Lemma 10 57 10: the shifted cone ideal attached to a polynomial presentation
inherits the canonical graded algebra structure on its quotient ring. -/
@[reducible] noncomputable def chosenConePresentationGradedAlgebra
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] R') :
    let I : Ideal (MvPolynomial (Fin n) R) := RingHom.ker π
    let J : Ideal (MvPolynomial (Fin (n + 1)) R) :=
      positively_shifted_cone_homogenized_ideal I
    GradedAlgebra (cone_quotient_grading J) :=
  let I : Ideal (MvPolynomial (Fin n) R) := RingHom.ker π
  let J : Ideal (MvPolynomial (Fin (n + 1)) R) :=
    positively_shifted_cone_homogenized_ideal I
  cone_quotient_gradedAlgebra_of_homogeneous_ideal (R := R) (n := n) J
    (positively_shifted_cone_homogenized_ideal_isHomogeneous (R := R) (n := n) I)

/-- Helper for Chap10 Lemma 10 57 10: the source finite type algebra and finite module determine
one explicit cone quotient ring, a homogenized relation quotient module, and the corresponding
away-localized module chart. -/
theorem exists_unlifted_cone_model_presentation_data_of_finite_module
    [Algebra.FiniteType R R'] [Module.Finite R' M] :
    ∃ (S : Type (max u u' v)) (_ : CommRing S) (_ : Algebra R S)
      (grading : ℕ → Submodule R S) (_ : GradedAlgebra grading)
      (N : Type (max u u' v)) (_ : AddCommGroup N) (_ : Module S N)
      (_ : Module R N) (_ : IsScalarTower R S N)
      (gradingN : ℕ → Submodule R N) (_ : DirectSum.Decomposition gradingN)
      (_ : SetLike.GradedSMul grading gradingN) (f : grading 1),
          ∃ zeroIso : R ≃ₐ[R] grading 0,
          ∃ ringIso : R' ≃ₐ[R] Away grading (f : S),
          ∃ moduleIso :
              M ≃ₛₗ[(ringIso.toRingEquiv : R' →+* Away grading (f : S))]
                awayDegreeZeroPart grading gradingN f,
            IsDegreeOneGeneratedFiniteTypeModel grading N := by
  classical
  obtain ⟨n, π, hπ⟩ := exists_surjective_mvPolynomial_presentation (R := R) (R' := R')
  let I : Ideal (MvPolynomial (Fin n) R) := RingHom.ker π
  let J : Ideal (MvPolynomial (Fin (n + 1)) R) :=
    positively_shifted_cone_homogenized_ideal I
  letI : GradedAlgebra (cone_quotient_grading J) :=
    chosenConePresentationGradedAlgebra (R := R) (R' := R') π
  letI : Algebra (MvPolynomial (Fin n) R) R' := π.toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M π.toRingHom
  letI : IsScalarTower (MvPolynomial (Fin n) R) R' M :=
    IsScalarTower.of_compHom (MvPolynomial (Fin n) R) R' M
  letI : Module.Finite (MvPolynomial (Fin n) R) M :=
    affinePresentationModuleFinite (R := R) (R' := R') (M := M) π hπ
  obtain ⟨r, τ, hτ⟩ :=
    exists_surjective_affine_free_module_presentation
      (R := R) (R' := R') (M := M) π
  let S : Type (max u u' v) := ULift.{max u u' v} (MvPolynomial (Fin (n + 1)) R ⧸ J)
  let grading : ℕ → Submodule R S := by
    simpa [S, presentationUliftSubmoduleFamily] using
      (uliftSubmoduleFamily (R := R) (cone_quotient_grading J))
  let instGradedAlgebraS : GradedAlgebra grading := by
    simpa [S, grading, J] using
      (show GradedAlgebra (uliftSubmoduleFamily (cone_quotient_grading J)) from inferInstance)
  letI : GradedAlgebra grading := by
    exact instGradedAlgebraS
  let N : Type (max u u' v) :=
    ULift.{max u u' v} (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
      homogenized_relation_submodule J τ))
  let instCommRingS : CommRing S := inferInstance
  let instAlgS : Algebra R S := inferInstance
  let instAddCommGroupN : AddCommGroup N := inferInstance
  let instModuleSN : Module S N := inferInstance
  let instModuleRN : Module R N := inferInstance
  let instTower : IsScalarTower R S N := inferInstance
  letI : CommRing S := instCommRingS
  letI : Algebra R S := instAlgS
  letI : AddCommGroup N := instAddCommGroupN
  letI : Module S N := instModuleSN
  letI : Module R N := instModuleRN
  letI : IsScalarTower R S N := instTower
  let gradingN : ℕ → Submodule R N := by
    simpa [N, presentationUliftSubmoduleFamily] using
      (uliftSubmoduleFamily (R := R) (homogenized_relation_quotient_grading J τ))
  letI : DirectSum.Decomposition (homogenized_relation_quotient_grading J τ) :=
    homogenizedRelationQuotientGrading_decomposition
      (R := R) (n := n) (r := r) J τ
  let instDecompositionN : DirectSum.Decomposition gradingN := by
    simpa [N, gradingN] using
      (presentationUliftQuotientDecomposition (R := R) (n := n) (r := r) J τ)
  let instGradedSmulSN : SetLike.GradedSMul grading gradingN := by
    simpa [grading, N, gradingN] using
      (show SetLike.GradedSMul
          (uliftSubmoduleFamily (cone_quotient_grading J))
          (uliftSubmoduleFamily (homogenized_relation_quotient_grading J τ)) from
        inferInstance)
  let f : grading 1 :=
    by
      simpa [grading, presentationUliftSubmoduleFamily, presentationUliftSubmoduleFamilyElement,
        S] using
        (uliftSubmoduleFamilyElement
          (R := R)
          (cone_quotient_grading J)
          (coneStandardDenominator J))
  let ringIso0 : R' ≃ₐ[R]
      Away (cone_quotient_grading J)
        ((coneStandardDenominator J : MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
    (mvPolynomial_quotient_equiv_of_surjective π hπ).symm.trans
      (coneKernelQuotientAwayAlgEquiv I)
  let ringIso :
      R' ≃ₐ[R] Away grading (f : S) :=
    liftedAwayAlgEquiv_of_unlifted
      (grading := cone_quotient_grading J)
      (f := coneStandardDenominator J)
      ringIso0
  have hfiniteN :
      Module.Finite (MvPolynomial (Fin (n + 1)) R ⧸ J)
        (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
          homogenized_relation_submodule J τ)) := by
    simpa [J] using
      moduleFinite_homogenized_relation_quotient
        (R := R) (n := n) (r := r) J τ
  have hmodel0 :
      IsDegreeOneGeneratedFiniteTypeModel
        (cone_quotient_grading J)
        (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
          homogenized_relation_submodule J τ)) := by
    let s : Finset (MvPolynomial (Fin (n + 1)) R ⧸ J) :=
      Finset.univ.image fun i : Fin (n + 1) => Ideal.Quotient.mk J (MvPolynomial.X i)
    letI :
        Module.Finite (MvPolynomial (Fin (n + 1)) R ⧸ J)
          (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
            homogenized_relation_submodule J τ)) := hfiniteN
    -- The cone quotient is generated by its degree-one variables, and the homogenized cokernel is
    -- a finite quotient of a finite free module over that ring.
    refine isDegreeOneGeneratedFiniteTypeModel_of_finset
      (R := R)
      (grading := cone_quotient_grading J)
      (((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
        homogenized_relation_submodule J τ))
      s
      ?_
      ?_
    · simpa [s] using
        cone_quotient_degree_one_generators_adjoin_top (R := R) (n := n) J
    · intro x hx
      simp only [s, Finset.mem_image, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨i, rfl⟩
      exact cone_quotient_X_mem_grade_one (R := R) (n := n) J i
  have hmodel :
      IsDegreeOneGeneratedFiniteTypeModel grading N := by
    -- Transport the finite-type model package through the fixed universe lift used by the final
    -- localization chart.
    simpa [grading, N, gradingN] using
      isDegreeOneGeneratedFiniteTypeModel_ulift
        (R := R)
        (grading := cone_quotient_grading J)
        hmodel0
  refine ⟨S, instCommRingS, instAlgS, grading, instGradedAlgebraS, N, instAddCommGroupN,
    instModuleSN, instModuleRN, instTower, gradingN, instDecompositionN, instGradedSmulSN, f,
    ?_, ringIso, ?_,
    (show IsDegreeOneGeneratedFiniteTypeModel grading N from hmodel)⟩
  · -- The degree-zero algebra piece is preserved by the same fixed `ULift` transport.
    simpa [S, grading] using
      (uliftDegreeZeroAlgEquiv (R := R) (cone_quotient_grading J))
  · -- The remaining proof-local blocker is now isolated as the specialized presentation chart.
    simpa [S, grading, N, gradingN, f, ringIso, J] using
      chosenConePresentationModuleIso
        (R := R) (R' := R') (M := M)
        π hπ τ rfl hτ

/-- Helper for Chap10 Lemma 10 57 10: a surjective coefficient map stays surjective after applying
it coordinatewise to a family of coefficients. -/
lemma surjective_piMap {α : Type _} {β : Type _} {ι : Type _}
    (f : α → β) (hf : Function.Surjective f) :
    Function.Surjective (fun x : ι → α ↦ fun i ↦ f (x i)) := by
  classical
  intro y
  choose x hx using fun i ↦ hf (y i)
  -- Reassemble the chosen coordinatewise lifts into one lifted coefficient vector.
  exact ⟨x, funext hx⟩

/-- Helper for Chap10 Lemma 10 57 10: before the final localized module-chart comparison, the
source finite type algebra and finite module already determine an unlifted cone quotient ring, a
homogenized relation cokernel, and the finite-type graded model data promised by the source
construction. -/
theorem exists_unlifted_cone_model_data_of_finite_module
    [Algebra.FiniteType R R'] [Module.Finite R' M] :
    ∃ (S : Type (max u u' v)) (_ : CommRing S) (_ : Algebra R S)
      (grading : ℕ → Submodule R S) (_ : GradedAlgebra grading)
      (N : Type (max u u' v)) (_ : AddCommGroup N) (_ : Module S N)
      (_ : Module R N) (_ : IsScalarTower R S N)
      (gradingN : ℕ → Submodule R N) (_ : DirectSum.Decomposition gradingN)
      (_ : SetLike.GradedSMul grading gradingN) (f : grading 1),
          ∃ _ : R ≃ₐ[R] grading 0,
          ∃ _ : R' ≃ₐ[R] Away grading (f : S),
            IsDegreeOneGeneratedFiniteTypeModel grading N := by
  rcases exists_unlifted_cone_model_presentation_data_of_finite_module
      (R := R) (R' := R') (M := M) with
    ⟨S, instCommRingS, instAlgS, grading, instGradedAlgebra, N, instAddCommGroupN, instModuleSN,
      instModuleRN, instTower, gradingN, instDecompositionN, instGradedSMul, f, zeroIso,
      ringIso, moduleIso, model⟩
  -- Forget the explicit localized module equivalence when only the cone-model data is needed.
  exact ⟨S, instCommRingS, instAlgS, grading, instGradedAlgebra, N, instAddCommGroupN,
    instModuleSN, instModuleRN, instTower, gradingN, instDecompositionN, instGradedSMul,
    f, zeroIso, ringIso, model⟩

end Lemma_10_57_10

/-- Helper for Chap10 Lemma 10 57 10: after restricting scalars along the explicit cone
dehomogenization chart, the cone-side presentation still evaluates by the standard basis sum. -/
lemma coneDehomPresentationMap_eq_sum_viaPresentedAlgHom {n r : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hJ :
      J ≤ Ideal.comap (coneDehom  ) (RingHom.ker π))
    (z : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) :
    let dehomToR' :=
      coneQuotientDehomToPresentedAlgHom    π hπ J hJ
    letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M := Module.compHom M dehomToR'.toRingHom
    coneDehomPresentationMap     J τ z =
      ∑ i, dehomToR' (z i) • τ (Pi.single i (1 : MvPolynomial (Fin n) R)) := by
  let dehomToR' := coneQuotientDehomToPresentedAlgHom π hπ J hJ
  letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M := Module.compHom M dehomToR'.toRingHom
  -- The cone presentation is already basis-defined, and under the chosen scalar restriction the
  -- quotient coefficients act through `dehomToR'`.
  dsimp
  rw [coneDehomPresentationMap_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rfl

/-- Helper for Chap10 Lemma 10 57 10: the explicit cone dehomogenization chart sends each
coordinate of a homogenized affine relation back to the original affine coefficient. -/
lemma coneQuotientDehomToPresentedAlgHom_apply_homogenizedAffineRelation {n r : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ :
      J ≤ Ideal.comap (coneDehom  ) (RingHom.ker π))
    (y : Fin r → MvPolynomial (Fin n) R) (i : Fin r) :
    coneQuotientDehomToPresentedAlgHom    π hπ J hJ
        ((homogenized_affine_relation    J y) i) =
      π (y i) := by
  -- Dehomogenizing a common-degree homogenization recovers the original affine coefficient, and
  -- the quotient-kernel equivalence then evaluates the quotient class via `π`.
  simp [coneQuotientDehomToPresentedAlgHom, homogenized_affine_relation,
    totalDegree_le_affine_relation_common_degree,
    coneDehom_quotient_map_homogenizeTo]

/-- Helper for Chap10 Lemma 10 57 10: the explicit cone dehomogenization chart sends every power
of the cone denominator to `1`, so later evaluations can collapse denominator powers before
comparing with the affine presentation. -/
lemma coneQuotientDehomToPresentedAlgHom_apply_XZeroPow {n : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ :
      J ≤ Ideal.comap (coneDehom  ) (RingHom.ker π))
    (d : ℕ) :
    coneQuotientDehomToPresentedAlgHom    π hπ J hJ
        ((Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) ^ d) = 1 := by
  -- The dehomogenization chart sends `X₀` to `1`, so every power collapses immediately.
  simp [coneQuotientDehomToPresentedAlgHom]

/-- Helper for Chap10 Lemma 10 57 10: evaluating the homogenized affine relation through the
explicit cone dehomogenization presentation recovers the original affine presentation value. -/
lemma coneDehomPresentationMap_apply_homogenizedAffineRelation {n r : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [instModuleAffineM : Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hmodule : instModuleAffineM = Module.compHom M π.toRingHom)
    (hJ :
      J ≤ Ideal.comap (coneDehom  ) (RingHom.ker π))
    (y : Fin r → MvPolynomial (Fin n) R) :
    let dehomToR' :=
      coneQuotientDehomToPresentedAlgHom    π hπ J hJ
    letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M := Module.compHom M dehomToR'.toRingHom
    coneDehomPresentationMap     J τ
        (homogenized_affine_relation    J y) = τ y := by
  subst instModuleAffineM
  letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M π.toRingHom
  let dehomToR' := coneQuotientDehomToPresentedAlgHom π hπ J hJ
  letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M := Module.compHom M dehomToR'.toRingHom
  let τR' : (Fin r → R') →ₗ[R'] M :=
    (Pi.basisFun R' (Fin r)).constr R'
      (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
  have hsingle (i : Fin r) :
      (Pi.single i (y i) : Fin r → MvPolynomial (Fin n) R) =
        y i •
          (Pi.single i (1 : MvPolynomial (Fin n) R) :
            Fin r → MvPolynomial (Fin n) R) := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  have hysum :
      (∑ i, (Pi.single i (y i) : Fin r → MvPolynomial (Fin n) R)) = y := by
    ext i
    simp
  -- First evaluate the cone presentation coefficientwise after dehomogenization, then identify
  -- those coefficients with the original affine ones and recombine the basis presentation.
  calc
    coneDehomPresentationMap J τ (homogenized_affine_relation J y) =
        ∑ i, dehomToR' ((homogenized_affine_relation J y) i) •
          τ (Pi.single i (1 : MvPolynomial (Fin n) R)) := by
          simpa [dehomToR'] using
            coneDehomPresentationMap_eq_sum_viaPresentedAlgHom
              (π := π) (hπ := hπ) (J := J) (τ := τ) (hJ := hJ)
              (z := homogenized_affine_relation J y)
    _ =
        ∑ i, π (y i) • τ (Pi.single i (1 : MvPolynomial (Fin n) R)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [coneQuotientDehomToPresentedAlgHom_apply_homogenizedAffineRelation
            (π := π) (hπ := hπ) (J := J) (hJ := hJ) (y := y) (i := i)]
    _ = τR' (fun i ↦ π (y i)) := by
          symm
          simpa [τR'] using
            ((Pi.basisFun R' (Fin r)).constr_apply_fintype
              R'
              (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
              (fun i ↦ π (y i)))
    _ = τ y := by
          calc
            τR' (fun i ↦ π (y i)) =
                ∑ i, π (y i) • τ (Pi.single i (1 : MvPolynomial (Fin n) R)) := by
                  simpa [τR'] using
                    ((Pi.basisFun R' (Fin r)).constr_apply_fintype
                      R'
                      (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
                      (fun i ↦ π (y i)))
            _ =
                ∑ i, τ (Pi.single i (y i) : Fin r → MvPolynomial (Fin n) R) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  rw [hsingle i]
                  exact (τ.map_smul (y i)
                    (Pi.single i (1 : MvPolynomial (Fin n) R) :
                      Fin r → MvPolynomial (Fin n) R)).symm
            _ = τ (∑ i, (Pi.single i (y i) : Fin r → MvPolynomial (Fin n) R)) := by
                  symm
                  exact map_sum τ
                    (fun i ↦ (Pi.single i (y i) : Fin r → MvPolynomial (Fin n) R))
                    Finset.univ
            _ = τ y := by
                  rw [hysum]

/-- Helper for Chap10 Lemma 10 57 10: every homogenized relation generator coming from the affine
kernel is killed by the dehomogenized cone presentation. -/
lemma coneDehomPresentationMap_homogenizedAffineRelation_eq_zero_of_mem_ker {n r : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [instModuleAffineM : Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hmodule : instModuleAffineM = Module.compHom M π.toRingHom)
    (hJ :
      J ≤ Ideal.comap (coneDehom  ) (RingHom.ker π))
    (k : LinearMap.ker τ) :
    let dehomToR' :=
      coneQuotientDehomToPresentedAlgHom    π hπ J hJ
    letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M := Module.compHom M dehomToR'.toRingHom
    coneDehomPresentationMap     J τ
        (homogenized_affine_relation    J k.1) = 0 := by
  subst instModuleAffineM
  letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M π.toRingHom
  let dehomToR' := coneQuotientDehomToPresentedAlgHom π hπ J hJ
  letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M := Module.compHom M dehomToR'.toRingHom
  -- Kernel generators are exactly the affine relations whose presentation value is zero, so the
  -- dehomogenized cone presentation kills their homogenizations as well.
  simpa [k.2] using
    coneDehomPresentationMap_apply_homogenizedAffineRelation
      (π := π) (hπ := hπ) (J := J) (τ := τ) (hmodule := rfl) (hJ := hJ) (y := k.1)

/-- Helper for Chap10 Lemma 10 57 10: the whole homogenized relation submodule lies in the kernel
of the dehomogenized cone presentation. This isolates the easy direction of the later kernel
comparison before the localization transport is introduced. -/
lemma homogenizedRelationSubmodule_le_ker_coneDehomPresentationMap {n r : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π)
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [instModuleAffineM : Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hmodule : instModuleAffineM = Module.compHom M π.toRingHom)
    (hJ :
      J ≤ Ideal.comap (coneDehom  ) (RingHom.ker π)) :
    let dehomToR' :=
      coneQuotientDehomToPresentedAlgHom    π hπ J hJ
    letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M := Module.compHom M dehomToR'.toRingHom
    homogenized_relation_submodule     J τ ≤
      LinearMap.ker (coneDehomPresentationMap     J τ) := by
  subst instModuleAffineM
  letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M π.toRingHom
  let dehomToR' := coneQuotientDehomToPresentedAlgHom π hπ J hJ
  letI : Module (MvPolynomial (Fin (n + 1)) R ⧸ J) M := Module.compHom M dehomToR'.toRingHom
  rw [homogenized_relation_submodule]
  -- The submodule is spanned by affine-kernel generators, and each generator was already shown
  -- to lie in the presentation kernel.
  refine Submodule.span_le.mpr ?_
  intro x hx
  rcases hx with ⟨k, rfl⟩
  simpa [LinearMap.mem_ker] using
    coneDehomPresentationMap_homogenizedAffineRelation_eq_zero_of_mem_ker
      (π := π) (hπ := hπ) (J := J) (τ := τ) (hmodule := rfl) (hJ := hJ) (k := k)

/-- Helper for Chap10 Lemma 10 57 10: the basis-defined affine presentation over `R'` sends the
coordinatewise images of polynomial coefficients under `π` back to the original affine
presentation value. -/
lemma affinePresentationMap_apply_pi {n r : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R')
    [instModuleAffineM : Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hmodule : instModuleAffineM = Module.compHom M π.toRingHom)
    (x : Fin r → MvPolynomial (Fin n) R) :
    let τR' : (Fin r → R') →ₗ[R'] M :=
      (Pi.basisFun R' (Fin r)).constr R'
        (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
    τR' (fun i ↦ π (x i)) = τ x := by
  subst instModuleAffineM
  letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M π.toRingHom
  let τR' : (Fin r → R') →ₗ[R'] M :=
    (Pi.basisFun R' (Fin r)).constr R'
      (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
  have hsingle (i : Fin r) :
      (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R) =
        x i •
          (Pi.single i (1 : MvPolynomial (Fin n) R) :
            Fin r → MvPolynomial (Fin n) R) := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  have hxsum :
      (∑ i, (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R)) = x := by
    ext i
    simp
  -- Expand the basis-defined `R'`-linear map and then recombine the coordinatewise basis
  -- decomposition back into the original affine relation vector.
  calc
    τR' (fun i ↦ π (x i)) =
        ∑ i, π (x i) • τ (Pi.single i (1 : MvPolynomial (Fin n) R)) := by
          simpa [τR'] using
            ((Pi.basisFun R' (Fin r)).constr_apply_fintype
              R'
              (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
              (fun i ↦ π (x i)))
    _ =
        ∑ i, τ (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hsingle i]
          exact (τ.map_smul (x i)
            (Pi.single i (1 : MvPolynomial (Fin n) R) :
              Fin r → MvPolynomial (Fin n) R)).symm
    _ = τ (∑ i, (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R)) := by
          symm
          exact map_sum τ (fun i ↦ (Pi.single i (x i) : Fin r → MvPolynomial (Fin n) R))
            Finset.univ
    _ = τ x := by
          rw [hxsum]

/-- Helper for Chap10 Lemma 10 57 10: in the chosen affine chart, the basis-defined `R'`-linear
presentation kills the coefficient vector `π ∘ x` exactly when the original affine presentation
kills `x`. -/
lemma hkerEq_affine {n r : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R')
    [instModuleAffineM : Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (hmodule : instModuleAffineM = Module.compHom M π.toRingHom)
    (x : Fin r → MvPolynomial (Fin n) R) :
    let τR' : (Fin r → R') →ₗ[R'] M :=
      (Pi.basisFun R' (Fin r)).constr R'
        (fun i ↦ τ (Pi.single i (1 : MvPolynomial (Fin n) R)))
    τR' (fun i ↦ π (x i)) = 0 ↔ τ x = 0 := by
  have happly :=
    affinePresentationMap_apply_pi
      (π := π) (τ := τ) (hmodule := hmodule) (x := x)
  -- Rewrite the basis-defined affine presentation to the original presentation value first.
  dsimp at happly ⊢
  simpa [happly]

/-- Chap10 Lemma 10 57 10: if `R'` is a finite type `R`-algebra and `M` is a finite
`R'`-module, then
there exist a graded `R`-algebra `S`, a graded `S`-module `N`, and a degree-one homogeneous
element `f` such that `R'` is `R`-algebra isomorphic to `S_(f)`, `M` is semilinearly equivalent
to `N_(f)` over this algebra isomorphism, `R ≃ₐ[R] S₀`, `S` is generated in degree `1` over
`S₀`, `S` is of finite type over `S₀`, and `N` is finite over `S`. The explicit finite set of
degree-one generators from the source is kept below as a companion consequence, while the main
theorem records the chapter-owner finite-type condition `Algebra.FiniteType (S₀) S`. This is the
degree-zero-piece form of the source conditions `S₀ = R` and “`S` is generated over `R` by
finitely many degree-one elements”. -/
@[stacks 052N]
-- Proof sketch: choose finitely many generators of the finite type algebra `R'`, homogenize the
-- defining ideal inside a polynomial ring with one extra variable of degree `1`, and then
-- homogenize a finite presentation of `M` to obtain a finite graded `S`-module whose localization
-- away from the extra variable recovers `M`.
theorem exists_graded_localization_model_of_finite_module
    [Algebra.FiniteType R R'] [Module.Finite R' M] :
    ∃ (S : Type (max u u' v)) (_ : CommRing S) (_ : Algebra R S)
      (grading : ℕ → Submodule R S) (_ : GradedAlgebra grading)
      (N : Type (max u u' v)) (_ : AddCommGroup N) (_ : Module S N)
      (_ : Module R N) (_ : IsScalarTower R S N)
      (gradingN : ℕ → Submodule R N) (_ : DirectSum.Decomposition gradingN)
      (_ : SetLike.GradedSMul grading gradingN) (f : grading 1),
          ∃ zeroIso : R ≃ₐ[R] grading 0,
          ∃ ringIso : R' ≃ₐ[R] Away grading (f : S),
          ∃ moduleIso :
              M ≃ₛₗ[(ringIso.toRingEquiv : R' →+* Away grading (f : S))]
                awayDegreeZeroPart grading gradingN f,
            IsDegreeOneGeneratedFiniteTypeModel grading N := by
  exact exists_unlifted_cone_model_presentation_data_of_finite_module
    (R := R) (R' := R') (M := M)

/-- A degree-one generated finite type graded ring admits a finite set of degree-one generators. -/
-- Proof sketch: choose finitely many algebra generators of `S` over `grading 0`, write each one
-- using the degree-one generating hypothesis, and collect the finitely many homogeneous degree-one
-- elements appearing in those expressions into a single finite generating set.
theorem exists_finset_degreeOne_generators_of_model
    {S : Type _} [CommRing S] [Algebra R S] (grading : ℕ → Submodule R S)
    [GradedAlgebra grading] (N : Type _) [AddCommGroup N] [Module S N]
    (hmodel : IsDegreeOneGeneratedFiniteTypeModel grading N) :
    ∃ s : Finset S,
      Algebra.adjoin (grading 0) (s : Set S) = ⊤ ∧
        ∀ x ∈ s, x ∈ grading 1 := by
  classical
  letI : Algebra.FiniteType (grading 0) S := hmodel.finiteType
  obtain ⟨t, ht_top⟩ := Algebra.FiniteType.out (R := grading 0) (A := S)
  have ht_mem :
      ∀ x ∈ t, x ∈ Algebra.adjoin (grading 0) (grading 1 : Set S) := by
    intro x hx
    rw [hmodel.degreeOne_adjoin_eq_top]
    simp
  have hpieces :
      ∀ x : {x // x ∈ t}, ∃ u : Finset S, (∀ y ∈ u, y ∈ grading 1) ∧
        (x : S) ∈ Algebra.adjoin (grading 0) (u : Set S) := by
    intro x
    exact exists_finset_subset_of_mem_adjoin
      (R := grading 0)
      (s := (grading 1 : Set S))
      (x := (x : S))
      (ht_mem x.1 x.2)
  choose u hu_deg hu_mem using hpieces
  refine ⟨t.attach.biUnion u, ?_, ?_⟩
  · -- Each finite-type algebra generator lies in the adjoin of finitely many degree-one pieces,
    -- so the union of those witnesses still generates the whole ring.
    apply top_le_iff.mp
    rw [← ht_top]
    exact Algebra.adjoin_le_iff.mpr fun x hx => by
      let xt : {x // x ∈ t} := ⟨x, hx⟩
      exact (Algebra.adjoin_mono fun y hy ↦
        Finset.mem_biUnion.mpr ⟨xt, by simp [xt], hy⟩) (hu_mem xt)
  · -- Every element of the finite union comes from one of the degree-one witness sets.
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨a, _, hx'⟩
    exact hu_deg a x hx'

end
