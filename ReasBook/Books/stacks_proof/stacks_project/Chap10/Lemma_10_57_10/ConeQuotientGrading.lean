import stacks_proof.stacks_project.Chap10.Lemma_10_57_10.ConeHomogenization

open scoped BigOperators DirectSum
open HomogeneousLocalization

universe u u' v

section

variable {R : Type u} {R' : Type u'} {M : Type v}
variable [CommRing R] [CommRing R'] [Algebra R R']
variable [AddCommGroup M] [Module R' M]

attribute [local instance] RingHomInvPair.of_ringEquiv
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

namespace Lemma_10_57_10

/-- Helper for Lemma 10.57.10: once the homogenized cone ideal maps into the affine kernel under
dehomogenization, the source substitution `X₀ ↦ 1` descends to the quotient rings. -/
noncomputable def coneDehom_quotient_map {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I) :
    (MvPolynomial (Fin (n + 1)) R ⧸ J) →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) :=
  Ideal.Quotient.liftₐ J
    ((Ideal.Quotient.mkₐ R I).comp (coneDehom (R := R) (n := n)))
    (fun _q hq => Ideal.Quotient.eq_zero_iff_mem.mpr (hJ hq))

/-- Helper for Lemma 10.57.10: the descended quotient dehomogenization still sends the cone
variable `X 0` to `1`. This is the source computation `X₀/X₀ ↦ 1`. -/
@[simp] theorem coneDehom_quotient_map_X_zero {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I) :
    coneDehom_quotient_map (R := R) (n := n) I J hJ
        (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) = 1 := by
  -- Evaluate the descended map on `X₀` by comparing it with its pre-quotient composite.
  let F : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).comp (coneDehom (R := R) (n := n))
  have hcomp :
      (coneDehom_quotient_map (R := R) (n := n) I J hJ).comp (Ideal.Quotient.mkₐ R J) = F := by
    simpa [coneDehom_quotient_map, F] using
      (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := J) F
        (fun _q hq => Ideal.Quotient.eq_zero_iff_mem.mpr (hJ hq)))
  have hX :=
    congrArg (fun φ : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) =>
      φ (MvPolynomial.X (0 : Fin (n + 1)))) hcomp
  simpa [F, coneDehom]
    using hX

/-- Helper for Lemma 10.57.10: the descended quotient dehomogenization sends `rename Fin.succ p`
to the affine quotient class of `p`. This is the quotient-level surjectivity witness used by the
source ring chart. -/
@[simp] theorem coneDehom_quotient_map_rename_succ {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I)
    (p : MvPolynomial (Fin n) R) :
    coneDehom_quotient_map (R := R) (n := n) I J hJ
        (Ideal.Quotient.mk J (MvPolynomial.rename Fin.succ p)) =
      Ideal.Quotient.mk I p := by
  -- Evaluate the descended map on `rename Fin.succ p` and use the source dehomogenization formula.
  let F : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).comp (coneDehom (R := R) (n := n))
  have hcomp :
      (coneDehom_quotient_map (R := R) (n := n) I J hJ).comp (Ideal.Quotient.mkₐ R J) = F := by
    simpa [coneDehom_quotient_map, F] using
      (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := J) F
        (fun _q hq => Ideal.Quotient.eq_zero_iff_mem.mpr (hJ hq)))
  have hrename :=
    congrArg (fun φ : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) =>
      φ (MvPolynomial.rename Fin.succ p)) hcomp
  simpa [F, coneDehom_rename_succ]
    using hrename

/-- Helper for Lemma 10.57.10: the descended quotient dehomogenization sends a bounded
homogenization back to the original affine quotient class. This packages the source identity
`\\widetilde g(1, x_1, \\dots, x_n) = g`. -/
@[simp] theorem coneDehom_quotient_map_homogenizeTo {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I)
    (d : ℕ) (p : MvPolynomial (Fin n) R) (hp : p.totalDegree ≤ d) :
    coneDehom_quotient_map (R := R) (n := n) I J hJ
        (Ideal.Quotient.mk J (coneHomogenizeTo (R := R) d p)) =
      Ideal.Quotient.mk I p := by
  -- Evaluate the descended quotient map on the homogenized polynomial and collapse the inserted
  -- `X₀`-powers via the already-proved dehomogenization formula.
  let F : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).comp (coneDehom (R := R) (n := n))
  have hcomp :
      (coneDehom_quotient_map (R := R) (n := n) I J hJ).comp (Ideal.Quotient.mkₐ R J) = F := by
    simpa [coneDehom_quotient_map, F] using
      (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := J) F
        (fun _q hq => Ideal.Quotient.eq_zero_iff_mem.mpr (hJ hq)))
  have hhomogenize :=
    congrArg (fun φ : MvPolynomial (Fin (n + 1)) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) =>
      φ (coneHomogenizeTo (R := R) d p)) hcomp
  simpa [F, coneDehom_homogenizeTo, hp]
    using hhomogenize

/-- Helper for Lemma 10.57.10: the descended quotient dehomogenization is surjective. This is the
quotient-level source fact that every affine class lifts by ignoring the extra cone variable. -/
theorem coneDehom_quotient_map_surjective {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I) :
    Function.Surjective (coneDehom_quotient_map (R := R) (n := n) I J hJ) := by
  intro pbar
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective pbar
  refine ⟨Ideal.Quotient.mk J (MvPolynomial.rename Fin.succ p), ?_⟩
  simpa using coneDehom_quotient_map_rename_succ (R := R) (n := n) I J hJ p

/-- Helper for Lemma 10.57.10: an element of the degree-`d` mapped homogeneous piece of the cone
quotient is represented by a degree-`d` homogeneous cone polynomial upstairs. -/
theorem homogeneous_quotient_lift_of_mem_grade {n d : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    (qbar :
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d).map
        ((Ideal.Quotient.mkₐ R J).toLinearMap)) :
    ∃ q : MvPolynomial (Fin (n + 1)) R,
      q.IsHomogeneous d ∧ Ideal.Quotient.mk J q = qbar.1 := by
  -- Unpack the mapped degree piece directly: membership in the quotient grading is already given
  -- by a homogeneous source representative.
  rcases qbar.2 with ⟨q, hq, hqbar⟩
  refine ⟨q, ?_, hqbar⟩
  simpa [MvPolynomial.mem_homogeneousSubmodule] using hq

/-- Helper for Lemma 10.57.10: a degree-`d` homogeneous cone polynomial whose dehomogenization
vanishes in the affine quotient already vanishes in the cone quotient. -/
theorem cone_polynomial_quotient_eq_zero_of_dehom_zero {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d)
    (hdehom : Ideal.Quotient.mk I (coneDehom (R := R) (n := n) q) = 0) :
    Ideal.Quotient.mk
        (Ideal.span (Set.range fun p : I =>
          coneHomogenizeTo (R := R) p.1.totalDegree p.1)) q = 0 := by
  -- Apply the raw cone-kernel lemma upstairs, then translate ideal membership back to the quotient
  -- class of `q`.
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact cone_homogenized_ideal_mem_of_isHomogeneous_of_dehom_mem
    (R := R) (n := n) (I := I) hq
    ((Ideal.Quotient.eq_zero_iff_mem).mp hdehom)

/-- Helper for Lemma 10.57.10: the degree-`d` graded piece of the cone quotient is the image of
the degree-`d` homogeneous submodule under the quotient map. -/
noncomputable def cone_quotient_grading {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (d : ℕ) :
    Submodule R (MvPolynomial (Fin (n + 1)) R ⧸ J) :=
  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d).map
    ((Ideal.Quotient.mkₐ R J).toLinearMap)

/-- Helper for Lemma 10.57.10: each homogeneous cone piece maps linearly to the corresponding
graded piece of the cone quotient. -/
noncomputable def cone_quotient_component_map {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d →ₗ[R]
      cone_quotient_grading (R := R) (n := n) J d :=
  LinearMap.codRestrict
    (cone_quotient_grading (R := R) (n := n) J d)
    (((Ideal.Quotient.mkₐ R J).toLinearMap).domRestrict
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d))
    (fun x ↦ ⟨x, x.2, rfl⟩)

/-- Helper for Lemma 10.57.10: the direct sum of the source homogeneous cone pieces carries the
canonical graded semiring structure. -/
noncomputable instance cone_homogeneous_directSum_gSemiring {n : ℕ} :
    DirectSum.GSemiring
      (fun d ↦ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) :=
  inferInstance

/-- Helper for Lemma 10.57.10: the quotient images of the homogeneous cone pieces still form a
graded monoid. -/
instance cone_quotient_setLikeGradedMonoid {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    SetLike.GradedMonoid (cone_quotient_grading (R := R) (n := n) J) where
  one_mem := by
    refine ⟨1, SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R), ?_⟩
    simp
  mul_mem := by
    intro i j x y hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    refine ⟨x' * y', SetLike.mul_mem_graded hx' hy', ?_⟩
    simp

/-- Helper for Lemma 10.57.10: before descending to the cone quotient, decompose a cone
polynomial into homogeneous pieces and map each piece componentwise to the quotient. -/
noncomputable def cone_quotient_predecompose {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    MvPolynomial (Fin (n + 1)) R →ₗ[R]
      DirectSum ℕ (fun d ↦ cone_quotient_grading (R := R) (n := n) J d) :=
  (DirectSum.lmap fun d ↦ cone_quotient_component_map (R := R) (n := n) J d).comp
    (DirectSum.decomposeLinearEquiv
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toLinearMap

/-- Helper for Lemma 10.57.10: the componentwise quotient predecomposition annihilates every
element of a homogeneous cone ideal. This is the exact descent input needed before building the
quotient grading on the cone quotient ring. -/
theorem cone_quotient_predecompose_eq_zero_of_mem_J {n : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q ∈ J) :
    cone_quotient_predecompose (R := R) (n := n) J q = 0 := by
  ext d
  -- Each homogeneous projection of an element of `J` still lies in `J`, so its quotient image
  -- vanishes coordinatewise.
  have hproj_mem :
      GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d q ∈ J := by
    exact (Ideal.IsHomogeneous.mem_iff
      (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) hJ).1 hq d
  have hproj_zero :
      Ideal.Quotient.mk J
        (GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d q) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hproj_mem
  -- After rewriting the `d`-th coordinate of `DirectSum.decompose` as `GradedRing.proj`, the
  -- quotient coordinate is exactly the previously established zero class.
  rw [cone_quotient_predecompose, LinearMap.comp_apply, DirectSum.lmap_apply]
  simp [cone_quotient_component_map]
  rw [DirectSum.decomposeLinearEquiv_apply]
  rw [← GradedRing.proj_apply
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d q]
  exact hproj_zero

/-- Helper for Lemma 10.57.10: the quotient class of a degree-`d` homogeneous cone polynomial
already lies in the `d`-th graded piece of the cone quotient. -/
theorem cone_quotient_mk_mem_grade_of_isHomogeneous {n d : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    Ideal.Quotient.mk J q ∈ cone_quotient_grading (R := R) (n := n) J d := by
  -- The quotient grading is defined as the image of the homogeneous source piece, so the source
  -- representative itself gives the required witness.
  refine ⟨q, ?_, rfl⟩
  simpa [MvPolynomial.mem_homogeneousSubmodule] using hq

/-- Helper for Lemma 10.57.10: on the direct sum of source homogeneous pieces, the componentwise
quotient maps preserve the multiplicative graded generators. -/
theorem cone_quotient_directSum_component_preserves_one {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    (DirectSum.lof R ℕ
        (fun d ↦ cone_quotient_grading (R := R) (n := n) J d) 0)
      ((cone_quotient_component_map (R := R) (n := n) J 0)
        ⟨1, SetLike.one_mem_graded
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)⟩) = 1 := by
  -- The quotient component map sends the degree-zero unit to the degree-zero direct-sum unit.
  rw [DirectSum.lof_eq_of]
  rfl

/-- Helper for Lemma 10.57.10: on the direct sum of source homogeneous pieces, the componentwise
quotient maps respect graded multiplication. -/
theorem cone_quotient_directSum_component_preserves_mul {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) {i j : ℕ}
    (x : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R i)
    (y : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R j) :
      (DirectSum.lof R ℕ
          (fun d ↦ cone_quotient_grading (R := R) (n := n) J d) (i + j))
      ((cone_quotient_component_map (R := R) (n := n) J (i + j))
        ⟨x.1 * y.1, SetLike.mul_mem_graded x.2 y.2⟩) =
      (DirectSum.lof R ℕ
          (fun d ↦ cone_quotient_grading (R := R) (n := n) J d) i)
        ((cone_quotient_component_map (R := R) (n := n) J i) x) *
        (DirectSum.lof R ℕ
            (fun d ↦ cone_quotient_grading (R := R) (n := n) J d) j)
          ((cone_quotient_component_map (R := R) (n := n) J j) y) := by
  -- Multiplication of direct-sum generators matches multiplication of the quotient classes.
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_mul_of]
  rfl

/-- Helper for Lemma 10.57.10: map the direct sum of homogeneous cone pieces to the direct sum of
their quotient images degreewise. -/
noncomputable def cone_quotient_directSumAlgHom {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    (⨁ d, MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) →ₐ[R]
      (⨁ d, cone_quotient_grading (R := R) (n := n) J d) :=
  DirectSum.toAlgebra (R := R)
    (A := fun d ↦ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d)
    (B := ⨁ d, cone_quotient_grading (R := R) (n := n) J d)
    (fun d ↦
      (DirectSum.lof R ℕ
        (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d).comp
        (cone_quotient_component_map (R := R) (n := n) J d))
    (cone_quotient_directSum_component_preserves_one (R := R) (n := n) J)
    (fun {_i _j} x y ↦
      cone_quotient_directSum_component_preserves_mul (R := R) (n := n) J x y)

/-- Helper for Lemma 10.57.10: before quotienting by `J`, the algebra decomposition into source
homogeneous pieces can be followed by the componentwise quotient maps. -/
noncomputable def cone_quotient_predecomposeAlgHom {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R]
      (⨁ d, cone_quotient_grading (R := R) (n := n) J d) :=
  (cone_quotient_directSumAlgHom (R := R) (n := n) J).comp
    (DirectSum.decomposeAlgEquiv
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).toAlgHom

/-- Helper for Lemma 10.57.10: the algebraic predecomposition agrees with the previously defined
linear predecomposition on cone polynomials. -/
theorem cone_quotient_predecomposeAlgHom_apply {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (q : MvPolynomial (Fin (n + 1)) R) :
    cone_quotient_predecomposeAlgHom (R := R) (n := n) J q =
      cone_quotient_predecompose (R := R) (n := n) J q := by
  -- The algebraic map and the linear map agree because `DirectSum.toAlgebra` extends the same
  -- degreewise component maps on each direct-sum generator.
  have hlmap :
      (cone_quotient_directSumAlgHom (R := R) (n := n) J).toLinearMap =
        DirectSum.lmap (fun d ↦ cone_quotient_component_map (R := R) (n := n) J d) := by
    apply DirectSum.linearMap_ext
    intro d
    apply LinearMap.ext
    intro x
    simpa [LinearMap.comp_apply, cone_quotient_directSumAlgHom, DirectSum.lof_eq_of,
      DirectSum.lmap_lof] using
      (DirectSum.toSemiring_of
        (f := fun e ↦
          ((DirectSum.lof R ℕ
            (fun f ↦ cone_quotient_grading (R := R) (n := n) J f) e).comp
            (cone_quotient_component_map (R := R) (n := n) J e)).toAddMonoidHom)
        (hone := cone_quotient_directSum_component_preserves_one (R := R) (n := n) J)
        (hmul := fun {_i _j} x y ↦
          cone_quotient_directSum_component_preserves_mul (R := R) (n := n) J x y)
        d x)
  simpa [cone_quotient_predecomposeAlgHom, cone_quotient_predecompose, LinearMap.comp_apply,
    DirectSum.decomposeAlgEquiv_apply, DirectSum.decomposeLinearEquiv_apply] using
    congrArg
      (fun φ :
        (⨁ d, MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) →ₗ[R]
          (⨁ d, cone_quotient_grading (R := R) (n := n) J d) =>
        φ (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) q))
      hlmap

/-- Helper for Lemma 10.57.10: for a homogeneous source polynomial, the quotient predecomposition
is concentrated in the matching degree. -/
theorem cone_quotient_predecompose_eq_of_isHomogeneous {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    cone_quotient_predecompose (R := R) (n := n) J q =
      DirectSum.of
        (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d
        ⟨Ideal.Quotient.mk J q,
          cone_quotient_mk_mem_grade_of_isHomogeneous
            (R := R) (n := n) (J := J) hq⟩ := by
  -- A homogeneous polynomial has only one nonzero source component, so the quotient
  -- predecomposition is concentrated in the matching direct-sum slot.
  have hq_mem :
      q ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d := by
    simpa [MvPolynomial.mem_homogeneousSubmodule] using hq
  change (DirectSum.lmap fun e ↦ cone_quotient_component_map (R := R) (n := n) J e)
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) q) =
    DirectSum.of
      (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d
      ⟨Ideal.Quotient.mk J q,
        cone_quotient_mk_mem_grade_of_isHomogeneous
          (R := R) (n := n) (J := J) hq⟩
  rw [DirectSum.decompose_of_mem _ hq_mem]
  rw [DirectSum.lmap_of]
  rfl

/-- Helper for Lemma 10.57.10: the algebraic quotient predecomposition already annihilates the
cone ideal, so it can descend through the quotient. -/
theorem cone_quotient_predecomposeAlgHom_eq_zero_of_mem_J {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (q : MvPolynomial (Fin (n + 1)) R) (hq : q ∈ J) :
    cone_quotient_predecomposeAlgHom (R := R) (n := n) J q = 0 := by
  -- The algebraic and linear predecompositions agree pointwise, so the earlier vanishing lemma
  -- on `J` is already enough for the quotient lift.
  rw [cone_quotient_predecomposeAlgHom_apply]
  exact cone_quotient_predecompose_eq_zero_of_mem_J
    (R := R) (n := n) hJ hq

/-- Helper for Lemma 10.57.10: if `J` is homogeneous, the source algebraic predecomposition
descends through the quotient by `J`. -/
noncomputable def cone_quotient_decomposeAlgHom_of_homogeneous_ideal {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    (MvPolynomial (Fin (n + 1)) R ⧸ J) →ₐ[R]
      (⨁ d, cone_quotient_grading (R := R) (n := n) J d) :=
  Ideal.Quotient.liftₐ J
    (cone_quotient_predecomposeAlgHom (R := R) (n := n) J)
    (cone_quotient_predecomposeAlgHom_eq_zero_of_mem_J
      (R := R) (n := n) J hJ)

/-- Helper for Lemma 10.57.10: the descended quotient decomposition recovers the source-side
predecomposition after precomposing with the quotient map. -/
theorem cone_quotient_decomposeAlgHom_comp_mk {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    (cone_quotient_decomposeAlgHom_of_homogeneous_ideal
        (R := R) (n := n) J hJ).comp (Ideal.Quotient.mkₐ R J) =
      cone_quotient_predecomposeAlgHom (R := R) (n := n) J := by
  -- The descended map computes by the defining quotient-lift formula.
  simpa [cone_quotient_decomposeAlgHom_of_homogeneous_ideal] using
    (Ideal.Quotient.liftₐ_comp (R₁ := R) (I := J)
      (cone_quotient_predecomposeAlgHom (R := R) (n := n) J)
      (cone_quotient_predecomposeAlgHom_eq_zero_of_mem_J
        (R := R) (n := n) J hJ))

/-- Helper for Lemma 10.57.10: the descended quotient decomposition is a right inverse to the
canonical direct-sum algebra map back to the cone quotient ring. -/
theorem cone_quotient_decomposeAlgHom_right_inv {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    (DirectSum.coeAlgHom (cone_quotient_grading (R := R) (n := n) J)).comp
        (cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ) =
      AlgHom.id R (MvPolynomial (Fin (n + 1)) R ⧸ J) := by
  -- Check the identity after precomposing with the quotient map, then use quotient extensionality.
  refine Ideal.Quotient.algHom_ext (R₁ := R) (I := J) ?_
  rw [AlgHom.comp_assoc, cone_quotient_decomposeAlgHom_comp_mk]
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, cone_quotient_predecomposeAlgHom_apply]
  rw [cone_quotient_predecompose_eq_of_isHomogeneous (R := R) (n := n) (J := J)
    (d := 1) (q := MvPolynomial.X i) (MvPolynomial.isHomogeneous_X (R := R) i)]
  simp

/-- Helper for Lemma 10.57.10: on a homogeneous quotient class, the descended quotient
decomposition lands in the expected direct-sum slot. -/
theorem cone_quotient_decomposeAlgHom_left_inv {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (d : ℕ) (x : cone_quotient_grading (R := R) (n := n) J d) :
    cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ (x : _) =
      DirectSum.of
        (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d x := by
  -- Lift the quotient class to a homogeneous source representative, then use concentration of the
  -- source predecomposition in its degree.
  rcases homogeneous_quotient_lift_of_mem_grade (R := R) (n := n) (d := d) x with ⟨q, hq, hqx⟩
  have hx :
      (⟨Ideal.Quotient.mk J q,
        cone_quotient_mk_mem_grade_of_isHomogeneous
          (R := R) (n := n) (J := J) hq⟩
        : cone_quotient_grading (R := R) (n := n) J d) = x := by
    ext
    exact hqx
  have hcomp :=
    show
      cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ
          (Ideal.Quotient.mk J q) =
        cone_quotient_predecomposeAlgHom (R := R) (n := n) J q by
      simpa [AlgHom.comp_apply] using
        AlgHom.congr_fun
          (cone_quotient_decomposeAlgHom_comp_mk (R := R) (n := n) J hJ) q
  calc
    cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ (x : _) =
        cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ
          (Ideal.Quotient.mk J q) := by rw [hqx]
    _ = DirectSum.of
          (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d
          ⟨Ideal.Quotient.mk J q,
            cone_quotient_mk_mem_grade_of_isHomogeneous
              (R := R) (n := n) (J := J) hq⟩ := by
      rw [hcomp, cone_quotient_predecomposeAlgHom_apply]
      exact cone_quotient_predecompose_eq_of_isHomogeneous
        (R := R) (n := n) (J := J) (d := d) hq
    _ = DirectSum.of
          (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d x := by
      simpa [hx]

/-- Helper for Lemma 10.57.10: a homogeneous cone ideal induces an owner-level graded algebra
structure on the cone quotient ring. -/
noncomputable def cone_quotient_gradedAlgebra_of_homogeneous_ideal {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    GradedAlgebra (cone_quotient_grading (R := R) (n := n) J) :=
  GradedAlgebra.ofAlgHom (cone_quotient_grading (R := R) (n := n) J)
    (cone_quotient_decomposeAlgHom_of_homogeneous_ideal (R := R) (n := n) J hJ)
    (cone_quotient_decomposeAlgHom_right_inv (R := R) (n := n) J hJ)
    (cone_quotient_decomposeAlgHom_left_inv (R := R) (n := n) J hJ)

/-- Helper for Lemma 10.57.10: the quotient class of `X i.succ` lies in the degree-one cone piece,
so it defines the canonical degree-zero fraction `X(i+1) / X0` in the homogeneous localization. -/
theorem cone_quotient_X_succ_mem_grade_one {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin n) :
    Ideal.Quotient.mk J (MvPolynomial.X i.succ) ∈
      cone_quotient_grading (R := R) (n := n) J 1 := by
  -- The source variable `X i.succ` is already homogeneous of degree `1`, so its quotient class
  -- lands in the degree-one cone piece by construction.
  exact cone_quotient_mk_mem_grade_of_isHomogeneous
    (R := R) (n := n) (J := J) (MvPolynomial.isHomogeneous_X (R := R) i.succ)

/-- Helper for Lemma 10.57.10: the descended quotient dehomogenization sends the cone denominator
to a unit, so ordinary away-localization at `X 0` can be evaluated back in the affine quotient. -/
theorem coneDehom_quotient_map_X_zero_isUnit {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I) :
    IsUnit
      (coneDehom_quotient_map (R := R) (n := n) I J hJ
        (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))))) := by
  -- The quotient-level dehomogenization formula already computes the cone denominator as `1`.
  rw [coneDehom_quotient_map_X_zero (R := R) (n := n) I J hJ]
  exact isUnit_one

/-- Helper for Lemma 10.57.10: after descending dehomogenization to the cone quotient, the
ordinary away-localization at the image of `X 0` maps canonically to the affine quotient because
that denominator already goes to `1`. -/
noncomputable def cone_ordinary_away_to_affine_quotient {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (coneDehom (R := R) (n := n)) I) :
    Localization.Away (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) →+*
      (MvPolynomial (Fin n) R ⧸ I) :=
  Localization.awayLift
    (coneDehom_quotient_map (R := R) (n := n) I J hJ).toRingHom
    (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))))
    (coneDehom_quotient_map_X_zero_isUnit (R := R) (n := n) I J hJ)

/-- Helper for Lemma 10.57.10: shift the cone homogenized affine kernel to positive degree so
degree-zero scalars are not already killed in the cone quotient. -/
noncomputable def positively_shifted_cone_homogenized_ideal {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    Ideal (MvPolynomial (Fin (n + 1)) R) :=
  Ideal.span (Set.range fun p : I =>
    coneHomogenizeTo (R := R) (max p.1.totalDegree 1) p.1)

/-- Helper for Lemma 10.57.10: the positively shifted cone kernel remains homogeneous for the
standard grading on the cone polynomial ring. -/
theorem positively_shifted_cone_homogenized_ideal_isHomogeneous {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := by
  -- The one-step degree shift preserves homogeneity because each chosen generator is still
  -- homogeneous in its declared source degree.
  rw [positively_shifted_cone_homogenized_ideal]
  apply Ideal.homogeneous_span
  intro q hq
  rcases hq with ⟨p, rfl⟩
  refine ⟨max p.1.totalDegree 1, ?_⟩
  simpa [MvPolynomial.mem_homogeneousSubmodule] using
    coneHomogenizeTo_isHomogeneous (R := R) (n := n) (max p.1.totalDegree 1) p.1

/-- Helper for Lemma 10.57.10: the positively shifted cone kernel still dehomogenizes into the
affine kernel under `X₀ ↦ 1`. -/
theorem positively_shifted_cone_homogenized_ideal_le_comap_coneDehom {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    positively_shifted_cone_homogenized_ideal (R := R) (n := n) I ≤
      Ideal.comap (coneDehom (R := R) (n := n)) I := by
  -- Each shifted generator dehomogenizes back to the same affine kernel element because the shift
  -- degree still dominates the total degree.
  rw [positively_shifted_cone_homogenized_ideal, Ideal.span_le]
  intro q hq
  rcases hq with ⟨p, rfl⟩
  change
    coneDehom (R := R) (n := n)
        (coneHomogenizeTo (R := R) (max p.1.totalDegree 1) p.1) ∈ I
  rw [coneDehom_homogenizeTo (R := R) (n := n) (max p.1.totalDegree 1) p.1 (le_max_left _ _)]
  exact p.2

/-- Helper for Lemma 10.57.10: for localization away from a degree-one element, the required
target degree `d • 1` is just the original homogeneous degree `d`. -/
theorem cone_quotient_mk_mem_grade_of_isHomogeneous_nsmul_one {n d : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    Ideal.Quotient.mk J q ∈ cone_quotient_grading (R := R) (n := n) J (d • 1) := by
  simpa using
    (cone_quotient_mk_mem_grade_of_isHomogeneous
      (R := R) (n := n) (J := J) (d := d) hq)

/-- Helper for Lemma 10.57.10: if a homogeneous cone polynomial dehomogenizes into the affine
kernel, then its normalized fraction vanishes in the ordinary away-localization of the positively
shifted cone quotient. -/
theorem normalized_homogeneous_fraction_eq_zero_of_dehom_mem {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d)
    (hdehom : coneDehom (R := R) (n := n) q ∈ I) :
    (Localization.mk
      (Ideal.Quotient.mk
        (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I) q)
      ⟨(Ideal.Quotient.mk
          (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I)
          (MvPolynomial.X (0 : Fin (n + 1)))) ^ d, by exact ⟨d, rfl⟩⟩ :
      Localization.Away
        (Ideal.Quotient.mk
          (positively_shifted_cone_homogenized_ideal (R := R) (n := n) I)
          (MvPolynomial.X (0 : Fin (n + 1))))) = 0 := by
  let J : Ideal (MvPolynomial (Fin (n + 1)) R) :=
    positively_shifted_cone_homogenized_ideal (R := R) (n := n) I
  let f0 : MvPolynomial (Fin (n + 1)) R ⧸ J :=
    Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))
  have htd :
      (coneDehom (R := R) (n := n) q).totalDegree ≤ d :=
    coneDehom_totalDegree_le_of_isHomogeneous (R := R) (n := n) (d := d) hq
  -- Compare in the ordinary away-localization and then use the shifted cone generators to clear
  -- the numerator by a suitable power of `X₀`.
  by_cases hd0 : d = 0
  · have hp0 : (coneDehom (R := R) (n := n) q).totalDegree = 0 := by
      exact Nat.eq_zero_of_le_zero (hd0 ▸ htd)
    have hqeq :
        coneHomogenizeTo (R := R) (n := n) 0 (coneDehom (R := R) (n := n) q) = q := by
      simpa [hd0] using
        (coneHomogenizeTo_coneDehom_of_isHomogeneous
          (R := R) (n := n) (d := d) hq)
    have hgen_mem :
        coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) ∈ J := by
      exact Ideal.subset_span
        (⟨⟨coneDehom (R := R) (n := n) q, hdehom⟩, by
          simp [J, hp0]⟩ :
          coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) ∈
            Set.range fun p : I =>
              coneHomogenizeTo (R := R) (n := n) (max p.1.totalDegree 1) p.1)
    have hshift :
        MvPolynomial.X (0 : Fin (n + 1)) *
            coneHomogenizeTo (R := R) (n := n) 0 (coneDehom (R := R) (n := n) q) =
          coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) := by
      simpa [hp0, pow_one] using
        (coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree
          (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q)
          (by simpa [hp0])).symm
    have hmul_zero : f0 * Ideal.Quotient.mk J q = 0 := by
      change Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)) * q) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← hqeq, hshift]
      exact hgen_mem
    rw [hd0, Localization.mk_eq_mk']
    change IsLocalization.mk' (Localization.Away f0) (Ideal.Quotient.mk J q)
      (1 : Submonoid.powers f0) = 0
    refine (IsLocalization.mk'_eq_zero_iff
      (S := Localization.Away f0) (Ideal.Quotient.mk J q) (1 : Submonoid.powers f0)).2 ?_
    refine ⟨⟨f0, ⟨1, by simp⟩⟩, ?_⟩
    simpa [f0, J] using hmul_zero
  · rcases d with _ | d
    · contradiction
    have hq_mem : q ∈ J := by
      by_cases hp0 : (coneDehom (R := R) (n := n) q).totalDegree = 0
      · have hgen_mem :
          coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) ∈ J := by
          exact Ideal.subset_span
            (⟨⟨coneDehom (R := R) (n := n) q, hdehom⟩, by
              simp [J, hp0]⟩ :
              coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) ∈
                Set.range fun p : I =>
                  coneHomogenizeTo (R := R) (n := n) (max p.1.totalDegree 1) p.1)
        have hqeq :
            q = MvPolynomial.X (0 : Fin (n + 1)) ^ d *
              coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) := by
          have hqeq' :
              coneHomogenizeTo (R := R) (n := n) (d + 1) (coneDehom (R := R) (n := n) q) = q := by
            simpa using
              (coneHomogenizeTo_coneDehom_of_isHomogeneous
                (R := R) (n := n) (d := d + 1) hq)
          have hshift_d :
              coneHomogenizeTo (R := R) (n := n) (d + 1)
                  (coneDehom (R := R) (n := n) q) =
                MvPolynomial.X (0 : Fin (n + 1)) ^ (d + 1) *
                  coneHomogenizeTo (R := R) (n := n) 0
                    (coneDehom (R := R) (n := n) q) := by
            simpa [hp0] using
              (coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree
                (R := R) (n := n) (d + 1) (coneDehom (R := R) (n := n) q)
                (by simpa [hp0]))
          have hshift_one :
              coneHomogenizeTo (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q) =
                MvPolynomial.X (0 : Fin (n + 1)) *
                  coneHomogenizeTo (R := R) (n := n) 0
                    (coneDehom (R := R) (n := n) q) := by
            simpa [hp0, pow_one] using
              (coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree
                (R := R) (n := n) 1 (coneDehom (R := R) (n := n) q)
                (by simpa [hp0]))
          calc
            q =
                coneHomogenizeTo (R := R) (n := n) (d + 1)
                  (coneDehom (R := R) (n := n) q) := by
                  symm
                  exact hqeq'
            _ = MvPolynomial.X (0 : Fin (n + 1)) ^ (d + 1) *
                  coneHomogenizeTo (R := R) (n := n) 0
                    (coneDehom (R := R) (n := n) q) := hshift_d
            _ = MvPolynomial.X (0 : Fin (n + 1)) ^ d *
                  coneHomogenizeTo (R := R) (n := n) 1
                    (coneDehom (R := R) (n := n) q) := by
                  rw [pow_succ, mul_assoc, hshift_one]
        rw [hqeq]
        exact Ideal.mul_mem_left _ _ hgen_mem
      · have hp1 :
          1 ≤ (coneDehom (R := R) (n := n) q).totalDegree := by
          exact Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr hp0)
        have hgen_mem :
            coneHomogenizeTo (R := R) (n := n)
                (coneDehom (R := R) (n := n) q).totalDegree
                (coneDehom (R := R) (n := n) q) ∈ J := by
          exact Ideal.subset_span
            (⟨⟨coneDehom (R := R) (n := n) q, hdehom⟩, by
              simp [J, max_eq_left hp1]⟩ :
              coneHomogenizeTo (R := R) (n := n)
                  (coneDehom (R := R) (n := n) q).totalDegree
                  (coneDehom (R := R) (n := n) q) ∈
                Set.range fun p : I =>
                  coneHomogenizeTo (R := R) (n := n) (max p.1.totalDegree 1) p.1)
        have hqeq :
            q =
              MvPolynomial.X (0 : Fin (n + 1)) ^
                ((d + 1) - (coneDehom (R := R) (n := n) q).totalDegree) *
              coneHomogenizeTo (R := R) (n := n)
                (coneDehom (R := R) (n := n) q).totalDegree
                (coneDehom (R := R) (n := n) q) := by
          calc
            q =
                coneHomogenizeTo (R := R) (n := n) (d + 1)
                  (coneDehom (R := R) (n := n) q) := by
                  symm
                  exact coneHomogenizeTo_coneDehom_of_isHomogeneous
                    (R := R) (n := n) (d := d + 1) hq
            _ =
                MvPolynomial.X (0 : Fin (n + 1)) ^
                  ((d + 1) - (coneDehom (R := R) (n := n) q).totalDegree) *
                coneHomogenizeTo (R := R) (n := n)
                  (coneDehom (R := R) (n := n) q).totalDegree
                  (coneDehom (R := R) (n := n) q) := by
                  exact coneHomogenizeTo_eq_X_zero_pow_mul_totalDegree
                    (R := R) (n := n) (d + 1)
                    (coneDehom (R := R) (n := n) q) htd
        rw [hqeq]
        exact Ideal.mul_mem_left _ _ hgen_mem
    have hq_zero : Ideal.Quotient.mk J q = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hq_mem
    simp [J, Localization.mk_eq_mk', hq_zero]

/-- Helper for Lemma 10.57.10: every positively shifted cone generator has zero constant
coefficient because it is homogeneous of positive degree. -/
theorem constantCoeff_coneHomogenizeTo_max_totalDegree_one_eq_zero {n : ℕ}
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.constantCoeff
        (coneHomogenizeTo (R := R) (n := n) (max p.totalDegree 1) p) = 0 := by
  -- The shift to `max totalDegree 1` forces positive total degree, so the degree-zero monomial
  -- cannot appear.
  have hhom :
      (coneHomogenizeTo (R := R) (n := n) (max p.totalDegree 1) p).IsHomogeneous
        (max p.totalDegree 1) :=
    coneHomogenizeTo_isHomogeneous (R := R) (n := n) (max p.totalDegree 1) p
  have hpositive : 0 < max p.totalDegree 1 := by
    exact Nat.succ_le_iff.mp (le_max_right p.totalDegree 1)
  have hdegree_ne : (0 : Fin (n + 1) →₀ ℕ).degree ≠ max p.totalDegree 1 := by
    intro hzero
    exact Nat.ne_of_gt hpositive hzero.symm
  simpa [MvPolynomial.constantCoeff_eq] using hhom.coeff_eq_zero hdegree_ne

/-- Helper for Lemma 10.57.10: every element of the positively shifted cone kernel has zero
constant coefficient. This is the key degree-zero input for the corrected cone quotient. -/
theorem positively_shifted_cone_homogenized_ideal_constantCoeff_eq_zero {n : ℕ}
    {I : Ideal (MvPolynomial (Fin n) R)} {q : MvPolynomial (Fin (n + 1)) R}
    (hq : q ∈ positively_shifted_cone_homogenized_ideal (R := R) (n := n) I) :
    MvPolynomial.constantCoeff q = 0 := by
  -- The property is stable under addition and multiplication by arbitrary cone polynomials, so a
  -- span induction over the shifted generators suffices.
  change q ∈
      Ideal.span (Set.range fun p : I =>
        coneHomogenizeTo (R := R) (max p.1.totalDegree 1) p.1) at hq
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · intro x hx
    rcases hx with ⟨p, rfl⟩
    exact constantCoeff_coneHomogenizeTo_max_totalDegree_one_eq_zero
      (R := R) (n := n) p.1
  · simp
  · intro x y _ _ hx hy
    simp [map_add, hx, hy]
  · intro a x _ hx
    simp [smul_eq_mul, map_mul, hx]

/-- Helper for Lemma 10.57.10: a constant polynomial in the positively shifted cone kernel must be
zero, because that kernel has zero constant coefficient. -/
theorem eq_zero_of_C_mem_positively_shifted_cone_homogenized_ideal {n : ℕ}
    {I : Ideal (MvPolynomial (Fin n) R)} {r : R}
    (hr :
      MvPolynomial.C r ∈ positively_shifted_cone_homogenized_ideal (R := R) (n := n) I) :
    r = 0 := by
  -- Apply the constant-coefficient vanishing lemma to the constant polynomial representative.
  have hconst :
      MvPolynomial.constantCoeff (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) = 0 :=
    positively_shifted_cone_homogenized_ideal_constantCoeff_eq_zero
      (R := R) (n := n) hr
  simpa using hconst

/-- Helper for Lemma 10.57.10: the quotient class of `X 0` is, tautologically, a power of itself in
the ordinary away-localization denominator submonoid. -/
theorem cone_quotient_X_zero_mem_powers {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))) ∈
      Submonoid.powers (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) := by
  exact ⟨1, by simp⟩

/-- Helper for Lemma 10.57.10: every cone variable class in the quotient ring is homogeneous of
degree `1`. -/
theorem cone_quotient_X_mem_grade_one {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin (n + 1)) :
    Ideal.Quotient.mk J (MvPolynomial.X i) ∈
      cone_quotient_grading (R := R) (n := n) J 1 := by
  -- Split the cone variable into the denominator variable `X 0` and the shifted affine variables,
  -- then invoke the already established homogeneous-degree-one formulas in each case.
  refine Fin.cases ?_ ?_ i
  · exact cone_quotient_mk_mem_grade_of_isHomogeneous
      (R := R) (n := n) (J := J)
      (MvPolynomial.isHomogeneous_X (R := R) (0 : Fin (n + 1)))
  · intro j
    exact cone_quotient_X_succ_mem_grade_one (R := R) (n := n) J j

/-- Helper for Lemma 10.57.10: the finitely many quotient classes of the cone variables generate
the cone quotient ring over its degree-zero part. -/
theorem cone_quotient_degree_one_generators_adjoin_top {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading (R := R) (n := n) J)] :
    let S := MvPolynomial (Fin (n + 1)) R ⧸ J
    let grading := cone_quotient_grading (R := R) (n := n) J
    let s : Set S := Set.range fun i : Fin (n + 1) =>
      Ideal.Quotient.mk J (MvPolynomial.X i)
    Algebra.adjoin (grading 0) (s : Set S) = ⊤ := by
  classical
  let S := MvPolynomial (Fin (n + 1)) R ⧸ J
  let grading := cone_quotient_grading (R := R) (n := n) J
  let s : Set S := Set.range fun i : Fin (n + 1) =>
    Ideal.Quotient.mk J (MvPolynomial.X i)
  let B : Subalgebra (grading 0) S := Algebra.adjoin (grading 0) (s : Set S)
  -- The quotient ring is generated by constants and the cone variables, so it suffices to prove
  -- that every quotient polynomial class already lies in the adjoin generated by those variables.
  rw [show B = ⊤ ↔ ⊤ ≤ B by rw [← top_le_iff]]
  intro x _
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  let P : MvPolynomial (Fin (n + 1)) R → Prop := fun q =>
    (Ideal.Quotient.mk J q : S) ∈ B
  change P p
  refine MvPolynomial.induction_on p ?_ ?_ ?_
  · intro r
    change P (MvPolynomial.C r)
    let r₀ : grading 0 := ⟨Ideal.Quotient.mk J (MvPolynomial.C r), by
      exact cone_quotient_mk_mem_grade_of_isHomogeneous
        (R := R) (n := n) (J := J)
        (MvPolynomial.isHomogeneous_C (σ := Fin (n + 1)) r)⟩
    -- Constants land in the degree-zero piece, hence already belong to the base subalgebra.
    simpa [B, grading, S] using B.algebraMap_mem r₀
  · intro p q hp hq
    -- The adjoin is closed under addition, so the induction hypothesis is stable under sums.
    change P (p + q)
    simpa [P, map_add] using B.add_mem hp hq
  · intro p i hp
    -- Multiplying by one more cone variable stays inside the adjoin because that variable is one
    -- of the chosen generators.
    have hi : (Ideal.Quotient.mk J (MvPolynomial.X i) : S) ∈ B := by
      exact Algebra.subset_adjoin (by
        refine Set.mem_range.mpr ?_
        exact ⟨i, rfl⟩)
    change P (p * MvPolynomial.X i)
    simpa [P, map_mul] using B.mul_mem hp hi

/-- Helper for Lemma 10.57.10: under the current minimal-degree cone ideal, any scalar whose
constant affine polynomial already lies in `I` is killed in the cone quotient as well. This is the
exact obstruction to obtaining `S₀ ≃ R` from the present cone-kernel choice when the original
structure map `R → R'` has kernel. -/
theorem cone_quotient_constant_eq_zero_of_mem_affine_kernel {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) {r : R}
    (hr : MvPolynomial.C r ∈ I) :
    Ideal.Quotient.mk
        (Ideal.span (Set.range fun p : I =>
          coneHomogenizeTo (R := R) p.1.totalDegree p.1))
        (MvPolynomial.C r) = 0 := by
  -- The current cone ideal includes the minimal homogenization of every kernel element, and for a
  -- constant kernel element that minimal homogenization is still the same constant polynomial.
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span
    (⟨⟨MvPolynomial.C r, hr⟩, by
      simpa using (coneHomogenizeTo_C (R := R) (n := n) r)⟩ :
      (MvPolynomial.C r) ∈ Set.range fun p : I =>
        coneHomogenizeTo (R := R) p.1.totalDegree p.1)

/-- Helper for Lemma 10.57.10: every degree-zero class in the cone quotient is represented by a
constant polynomial. This is the normalized source-faithful form of the corrected `S₀ = R`
statement before packaging it as an algebra isomorphism. -/
theorem cone_quotient_grade_zero_normal_form {n : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    (x : cone_quotient_grading (R := R) (n := n) J 0) :
    ∃ r : R,
      (⟨Ideal.Quotient.mk J (MvPolynomial.C r),
        cone_quotient_mk_mem_grade_of_isHomogeneous
          (R := R) (n := n) (J := J)
          (MvPolynomial.isHomogeneous_C (σ := Fin (n + 1)) r)⟩ :
        cone_quotient_grading (R := R) (n := n) J 0) = x := by
  -- Lift the quotient class to a homogeneous degree-zero polynomial upstairs.
  rcases homogeneous_quotient_lift_of_mem_grade (R := R) (n := n) (d := 0) x with ⟨q, hq, hq_eq⟩
  have hdeg : q.totalDegree = 0 := by
    exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := q)).2 hq
  -- Degree-zero homogeneous cone polynomials are exactly constants.
  have hqC : q = MvPolynomial.C (q.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C (p := q)).mp hdeg
  refine ⟨q.coeff 0, ?_⟩
  ext
  rw [hqC] at hq_eq
  exact hq_eq

/-- Helper for Lemma 10.57.10: the corrected shifted cone quotient kills a constant polynomial
exactly when the scalar itself is zero. -/
theorem cone_quotient_constant_class_eq_zero_iff {n : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    (hJ_constant : ∀ r : R, MvPolynomial.C r ∈ J → r = 0) (r : R) :
    Ideal.Quotient.mk J (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) = 0 ↔ r = 0 := by
  constructor
  · -- Move quotient-zero back to ideal membership, then use the corrected constant-kernel input.
    intro hr
    exact hJ_constant r ((Ideal.Quotient.eq_zero_iff_mem).mp hr)
  · -- The zero scalar gives the zero class tautologically.
    intro hr
    simpa [hr]

/-- Helper for Lemma 10.57.10: the canonical scalar map into the degree-zero cone quotient piece
is injective once constants are not killed by the shifted cone ideal. -/
theorem cone_quotient_grade_zero_algebraMap_injective {n : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    [GradedAlgebra (cone_quotient_grading (R := R) (n := n) J)]
    (hJ_constant : ∀ r : R, MvPolynomial.C r ∈ J → r = 0) :
    Function.Injective (Algebra.ofId R (cone_quotient_grading (R := R) (n := n) J 0)) := by
  intro r s hrs
  have hconst :
      (Ideal.Quotient.mk J (MvPolynomial.C r) :
          MvPolynomial (Fin (n + 1)) R ⧸ J) =
        Ideal.Quotient.mk J (MvPolynomial.C s) := by
    have hconstQ :
        (((Algebra.ofId R (cone_quotient_grading (R := R) (n := n) J 0)) r :
            cone_quotient_grading (R := R) (n := n) J 0) :
          MvPolynomial (Fin (n + 1)) R ⧸ J) =
          ((Algebra.ofId R (cone_quotient_grading (R := R) (n := n) J 0) s :
              cone_quotient_grading (R := R) (n := n) J 0) :
            MvPolynomial (Fin (n + 1)) R ⧸ J) :=
      congrArg (fun x : cone_quotient_grading (R := R) (n := n) J 0 => x.1) hrs
    change
      (algebraMap R (MvPolynomial (Fin (n + 1)) R ⧸ J)) r =
        (algebraMap R (MvPolynomial (Fin (n + 1)) R ⧸ J)) s at hconstQ
    change
      (algebraMap R (MvPolynomial (Fin (n + 1)) R ⧸ J)) r =
        (algebraMap R (MvPolynomial (Fin (n + 1)) R ⧸ J)) s
    exact hconstQ
  have hsub :
      Ideal.Quotient.mk J (MvPolynomial.C (r - s) : MvPolynomial (Fin (n + 1)) R) = 0 := by
    simpa [MvPolynomial.C_sub] using sub_eq_zero.mpr hconst
  -- Reduce injectivity to the already normalized constant-class criterion.
  exact sub_eq_zero.mp <|
    (cone_quotient_constant_class_eq_zero_iff
      (R := R) (n := n) (J := J) hJ_constant (r - s)).mp hsub

/-- Helper for Lemma 10.57.10: every degree-zero quotient class is reached by the canonical scalar
map from `R`. -/
theorem cone_quotient_grade_zero_algebraMap_surjective {n : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    [GradedAlgebra (cone_quotient_grading (R := R) (n := n) J)]
    : Function.Surjective (Algebra.ofId R (cone_quotient_grading (R := R) (n := n) J 0)) := by
  intro x
  rcases cone_quotient_grade_zero_normal_form (R := R) (n := n) (J := J) x with ⟨r, rfl⟩
  -- The normalized constant representative is exactly the image of `r`.
  refine ⟨r, ?_⟩
  ext
  rfl

/-- Helper for Lemma 10.57.10: the degree-zero piece of the shifted cone quotient is canonically
the base ring `R`. -/
noncomputable def cone_quotient_grade_zero_algEquiv {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [GradedAlgebra (cone_quotient_grading (R := R) (n := n) J)]
    (hJ_constant : ∀ r : R, MvPolynomial.C r ∈ J → r = 0) :
    R ≃ₐ[R] cone_quotient_grading (R := R) (n := n) J 0 :=
  AlgEquiv.ofBijective (Algebra.ofId R (cone_quotient_grading (R := R) (n := n) J 0))
    ⟨cone_quotient_grade_zero_algebraMap_injective
        (R := R) (n := n) (J := J) hJ_constant,
      cone_quotient_grade_zero_algebraMap_surjective
        (R := R) (n := n) (J := J)⟩

end Lemma_10_57_10

end
