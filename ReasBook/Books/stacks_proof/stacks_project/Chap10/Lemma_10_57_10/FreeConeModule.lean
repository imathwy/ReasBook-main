import StacksProject_2024.Chap10.Lemma_10_57_10.ConeQuotientGrading

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

/-- Helper for Lemma 10.57.10: the finite free module on `Fin r` over the cone quotient inherits
the coordinatewise grading from the cone quotient ring. -/
noncomputable def free_cone_module_grading {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (d : ℕ) :
    Submodule R (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  Submodule.pi Set.univ fun _ : Fin r =>
    cone_quotient_grading (R := R) (n := n) J d

/-- Helper for Lemma 10.57.10: the cone quotient ring acts on itself by multiplication. Making
this owner instance explicit avoids repeated typeclass search through quotient-ring defaults in the
free-module grading API. -/
noncomputable instance cone_quotient_selfModule {n : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    Module (MvPolynomial (Fin (n + 1)) R ⧸ J)
      (MvPolynomial (Fin (n + 1)) R ⧸ J) :=
  Semiring.toModule

/-- Helper for Lemma 10.57.10: the free cone module on `Fin r` is the standard pointwise module
over the cone quotient ring. This is the owner-level Pi-module API used by the homogeneous-span
arguments below. -/
noncomputable instance free_cone_module_pointwiseModule {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    Module (MvPolynomial (Fin (n + 1)) R ⧸ J)
      (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  Pi.Function.module (I := Fin r)
    (α := MvPolynomial (Fin (n + 1)) R ⧸ J)
    (β := MvPolynomial (Fin (n + 1)) R ⧸ J)

/-- Helper for Lemma 10.57.10: expose the pointwise scalar action on the free cone module
directly, so later graded-module owners do not spend heartbeats rediscovering it through the full
module hierarchy. -/
@[reducible] noncomputable instance free_cone_module_pointwiseSMul {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    SMul (MvPolynomial (Fin (n + 1)) R ⧸ J)
      (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  (free_cone_module_pointwiseModule (R := R) (n := n) (r := r) J).toSMul

/-- Helper for Lemma 10.57.10: membership in the free cone-module grading is coordinatewise
membership in the corresponding cone quotient piece. -/
theorem mem_free_cone_module_grading_iff {n r d : ℕ}
    {J : Ideal (MvPolynomial (Fin (n + 1)) R)}
    {v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)} :
    v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J d ↔
      ∀ i, v i ∈ cone_quotient_grading (R := R) (n := n) J d := by
  -- The coordinatewise grading is exactly the product submodule over all coordinates.
  simp [free_cone_module_grading]

/-- Helper for Lemma 10.57.10: insert a homogeneous cone quotient class into a single coordinate
of the free cone module, keeping the same source degree. -/
noncomputable def free_cone_module_degree_single {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin r) (d : ℕ) :
    cone_quotient_grading (R := R) (n := n) J d →ₗ[R]
      free_cone_module_grading (R := R) (n := n) (r := r) J d :=
  LinearMap.codRestrict
    (free_cone_module_grading (R := R) (n := n) (r := r) J d)
    (((LinearMap.single R (fun _ : Fin r ↦ MvPolynomial (Fin (n + 1)) R ⧸ J) i).comp
      (cone_quotient_grading (R := R) (n := n) J d).subtype))
    (fun x ↦ by
      -- The inserted vector is zero off the chosen coordinate and equals the given homogeneous
      -- class at that coordinate, so it still lies in the degree-`d` piece coordinatewise.
      rw [mem_free_cone_module_grading_iff]
      intro j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [LinearMap.single_apply, hji])

/-- Helper for Lemma 10.57.10: the degreewise coordinate insertion is exactly the expected
`Pi.single` on the underlying vector. -/
@[simp] theorem free_cone_module_degree_single_coe {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (i : Fin r)
    (x : cone_quotient_grading (R := R) (n := n) J d) :
    ((free_cone_module_degree_single (R := R) (n := n) (r := r) J i d x :
        free_cone_module_grading (R := R) (n := n) (r := r) J d) :
        Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =
      Pi.single i (x : MvPolynomial (Fin (n + 1)) R ⧸ J) := by
  rfl

/-- Helper for Lemma 10.57.10: decompose each coordinate of the free cone module and reinsert the
homogeneous summands into the matching coordinate of the graded direct sum. -/
noncomputable def free_cone_module_predecomposeLinear {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)] :
    (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) →ₗ[R]
      (⨁ d : ℕ, free_cone_module_grading (R := R) (n := n) (r := r) J d) :=
  ∑ i : Fin r,
    (DirectSum.lmap
      (fun d ↦ free_cone_module_degree_single (R := R) (n := n) (r := r) J i d)).comp
      (((DirectSum.decomposeLinearEquiv
          (cone_quotient_grading (R := R) (n := n) J)).toLinearMap).comp
        (LinearMap.proj i))

/-- Helper for Lemma 10.57.10: for one fixed coordinate, decomposing and then recomposing the
inserted homogeneous summands recovers the corresponding `Pi.single` vector. -/
theorem free_cone_module_coordinate_recompose {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    (i : Fin r) :
    DirectSum.coeLinearMap
        (free_cone_module_grading (R := R) (n := n) (r := r) J) ∘ₗ
      (DirectSum.lmap
        (fun d ↦ free_cone_module_degree_single (R := R) (n := n) (r := r) J i d)) ∘ₗ
      ((DirectSum.decomposeLinearEquiv
          (cone_quotient_grading (R := R) (n := n) J)).toLinearMap) =
        LinearMap.single R
          (fun _ : Fin r ↦ MvPolynomial (Fin (n + 1)) R ⧸ J) i := by
  -- Compare both maps on each homogeneous source summand of the cone quotient grading.
  apply DirectSum.decompose_lhom_ext
    (ℳ := cone_quotient_grading (R := R) (n := n) J)
  intro d
  apply LinearMap.ext
  intro x
  -- On a homogeneous source vector, the decomposition is already the single `lof` term.
  change
    DirectSum.coeLinearMap
        (free_cone_module_grading (R := R) (n := n) (r := r) J)
        ((DirectSum.lmap
            (fun e ↦ free_cone_module_degree_single (R := R) (n := n) (r := r) J i e))
          (((DirectSum.decomposeLinearEquiv
              (cone_quotient_grading (R := R) (n := n) J)).toLinearMap) x)) =
      LinearMap.single R
        (fun _ : Fin r ↦ MvPolynomial (Fin (n + 1)) R ⧸ J) i x
  have hx :
      ((DirectSum.decomposeLinearEquiv
          (cone_quotient_grading (R := R) (n := n) J)).toLinearMap) x =
        DirectSum.lof R ℕ
          (fun e ↦ cone_quotient_grading (R := R) (n := n) J e) d x := by
    simpa using
      (DirectSum.decomposeLinearEquiv_apply_coe
        (cone_quotient_grading (R := R) (n := n) J) d x)
  rw [hx, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
  ext j
  by_cases hji : j = i
  · subst hji
    simp [LinearMap.single_apply]
  · simp [LinearMap.single_apply, hji]

/-- Helper for Lemma 10.57.10: the `e`-component of the free-cone predecomposition is obtained by
decomposing each coordinate in degree `e`. This is the coercion-stable bridge from the direct-sum
object back to the coordinatewise source data. -/
theorem free_cone_module_predecompose_component_eq_coordinate_decompose {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    (v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) (e : ℕ) :
    (((free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J v) e :
        free_cone_module_grading (R := R) (n := n) (r := r) J e) :
        Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =
      fun i ↦
        ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) (v i) e :
            cone_quotient_grading (R := R) (n := n) J e) :
            MvPolynomial (Fin (n + 1)) R ⧸ J) := by
  -- Expand the finite sum defining the predecomposition and read off one coordinate. Only the
  -- `Pi.single` inserted at that coordinate survives.
  ext i
  have hcomponent :
      (((free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J v) e :
          free_cone_module_grading (R := R) (n := n) (r := r) J e) :
          Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =
        ∑ j : Fin r,
          ((((DirectSum.lmap
                (fun d ↦ free_cone_module_degree_single (R := R) (n := n) (r := r) J j d))
              (((DirectSum.decomposeLinearEquiv
                  (cone_quotient_grading (R := R) (n := n) J)).toLinearMap) (v j))) e :
              free_cone_module_grading (R := R) (n := n) (r := r) J e) :
            Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) := by
    -- First project the finite sum to degree `e`, and then coerce that graded piece back to the
    -- underlying coordinatewise function.
    rw [free_cone_module_predecomposeLinear, LinearMap.sum_apply]
    simpa [LinearMap.comp_apply, LinearMap.proj_apply] using
      congrArg
        (fun z :
          free_cone_module_grading (R := R) (n := n) (r := r) J e ↦
            (z : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)))
        (DFinsupp.finset_sum_apply Finset.univ
          (fun j : Fin r ↦
            (DirectSum.lmap
              (fun d ↦ free_cone_module_degree_single (R := R) (n := n) (r := r) J j d))
              (((DirectSum.decomposeLinearEquiv
                  (cone_quotient_grading (R := R) (n := n) J)).toLinearMap) (v j)))
          e)
  rw [hcomponent, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp only [DirectSum.lmap_apply, free_cone_module_degree_single_coe, Pi.single_apply]
    simpa [DirectSum.decomposeLinearEquiv_apply]
  · intro j hj hji
    have hij : i ≠ j := by
      intro hij
      exact hji hij.symm
    simp [DirectSum.lmap_apply, free_cone_module_degree_single_coe, Pi.single_apply, hij]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Helper for Lemma 10.57.10: recomposing the coordinatewise free-module predecomposition
recovers the original vector. -/
theorem free_cone_module_predecomposeLinear_left_inv {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)] :
    DirectSum.coeLinearMap
        (free_cone_module_grading (R := R) (n := n) (r := r) J) ∘ₗ
      free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J =
        LinearMap.id := by
  -- Route correction: rewrite the composite at the linear-map level first, so the final
  -- coordinate comparison only sees the finite sum of `Pi.single` vectors.
  apply LinearMap.ext
  intro v
  ext j
  calc
    (DirectSum.coeLinearMap
        (free_cone_module_grading (R := R) (n := n) (r := r) J)
        (free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J v)) j =
      ∑ i : Fin r, (Pi.single i (v i)) j := by
        rw [free_cone_module_predecomposeLinear, LinearMap.sum_apply, map_sum, Finset.sum_apply]
        -- Each summand recomposes one coordinate decomposition back to the corresponding
        -- `Pi.single` vector.
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [LinearMap.comp_apply, LinearMap.proj_apply] using
          congrArg
            (fun f :
              (MvPolynomial (Fin (n + 1)) R ⧸ J) →ₗ[R]
                (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =>
              (f (v i)) j)
            (free_cone_module_coordinate_recompose (R := R) (n := n) (r := r) J i)
    _ = v j := by
      simpa using
        congrArg (fun w : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J) => w j)
          (LinearMap.sum_single_apply R (fun i : Fin r ↦ v i))

/-- Helper for Lemma 10.57.10: a degree-`d` cone quotient element has zero decomposition in every
other degree. This isolates the coordinatewise vanishing needed for the free-cone right inverse. -/
theorem cone_quotient_decompose_eq_zero_of_mem_ne {n d e : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    {x : MvPolynomial (Fin (n + 1)) R ⧸ J}
    (hx : x ∈ cone_quotient_grading (R := R) (n := n) J d) (hed : e ≠ d) :
    ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) x e :
        cone_quotient_grading (R := R) (n := n) J e) :
        MvPolynomial (Fin (n + 1)) R ⧸ J) = 0 := by
  -- Once the element is known to lie in degree `d`, every off-diagonal direct-sum component
  -- vanishes by the decomposition API.
  simpa using
    (DirectSum.decompose_of_mem_ne
      (cone_quotient_grading (R := R) (n := n) J) hx hed.symm)

/-- Helper for Lemma 10.57.10: a degree-`d` cone quotient element is recovered by its `d`-th
decomposition component. This isolates the matching-degree step for the free-cone right inverse. -/
theorem cone_quotient_decompose_eq_self_of_mem {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    {x : MvPolynomial (Fin (n + 1)) R ⧸ J}
    (hx : x ∈ cone_quotient_grading (R := R) (n := n) J d) :
    ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) x d :
        cone_quotient_grading (R := R) (n := n) J d) :
        MvPolynomial (Fin (n + 1)) R ⧸ J) = x := by
  -- The diagonal direct-sum component is exactly the original homogeneous element.
  simpa using
    (DirectSum.decompose_of_mem_same
      (cone_quotient_grading (R := R) (n := n) J) hx)

/-- Helper for Lemma 10.57.10: a homogeneous free-cone vector has each coordinate decomposition
concentrated in the same degree. -/
theorem free_cone_module_coordinate_decompose_eq_ite {n r d e : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    {v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (hv : v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J d) (i : Fin r) :
    ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) (v i) e :
        cone_quotient_grading (R := R) (n := n) J e) :
        MvPolynomial (Fin (n + 1)) R ⧸ J) =
      if e = d then v i else 0 := by
  have hvi :
      v i ∈ cone_quotient_grading (R := R) (n := n) J d :=
    (mem_free_cone_module_grading_iff (R := R) (n := n) (r := r) (d := d) (J := J)).1 hv i
  by_cases hed : e = d
  · subst e
    -- In the matching degree, the decomposition is the original homogeneous coordinate.
    simpa using
      cone_quotient_decompose_eq_self_of_mem (R := R) (n := n) (d := d) J hvi
  · -- Outside the matching degree, the coordinate decomposition vanishes.
    simpa [hed] using
      cone_quotient_decompose_eq_zero_of_mem_ne
        (R := R) (n := n) (d := d) (e := e) J hvi hed

/-- Helper for Lemma 10.57.10: on a homogeneous free-cone vector, the coordinatewise
predecomposition is concentrated in the matching degree. -/
theorem free_cone_module_predecompose_eq_lof_of_mem {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    {v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (hv : v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J d) :
    free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J v =
      DirectSum.lof R ℕ
        (fun e ↦ free_cone_module_grading (R := R) (n := n) (r := r) J e) d
        ⟨v, hv⟩ := by
  -- Compare degree components. The new component formula reduces the claim to the already-isolated
  -- statement that each coordinate decomposition is concentrated in degree `d`.
  apply DirectSum.ext
  intro e
  by_cases hed : e = d
  · subst e
    have hsame :
        ((DirectSum.lof R ℕ
            (fun a ↦ free_cone_module_grading (R := R) (n := n) (r := r) J a) d
            ⟨v, hv⟩) d :
            free_cone_module_grading (R := R) (n := n) (r := r) J d) = ⟨v, hv⟩ := by
      rw [DirectSum.lof_eq_of]
      simpa using DirectSum.of_eq_same
        (β := fun a ↦ free_cone_module_grading (R := R) (n := n) (r := r) J a) d ⟨v, hv⟩
    rw [hsame]
    apply Subtype.ext
    ext i
    have hvi :
        v i ∈ cone_quotient_grading (R := R) (n := n) J d :=
      (mem_free_cone_module_grading_iff (R := R) (n := n) (r := r) (d := d) (J := J)).1 hv i
    rw [free_cone_module_predecompose_component_eq_coordinate_decompose]
    exact cone_quotient_decompose_eq_self_of_mem (R := R) (n := n) (d := d) J hvi
  · have hzero :
        ((DirectSum.lof R ℕ
            (fun a ↦ free_cone_module_grading (R := R) (n := n) (r := r) J a) d
            ⟨v, hv⟩) e :
            free_cone_module_grading (R := R) (n := n) (r := r) J e) = 0 := by
      rw [DirectSum.lof_eq_of]
      exact DirectSum.of_eq_of_ne
        (β := fun a ↦ free_cone_module_grading (R := R) (n := n) (r := r) J a) d e ⟨v, hv⟩ hed
    rw [hzero]
    apply Subtype.ext
    ext i
    have hvi :
        v i ∈ cone_quotient_grading (R := R) (n := n) J d :=
      (mem_free_cone_module_grading_iff (R := R) (n := n) (r := r) (d := d) (J := J)).1 hv i
    rw [free_cone_module_predecompose_component_eq_coordinate_decompose]
    exact cone_quotient_decompose_eq_zero_of_mem_ne
      (R := R) (n := n) (d := d) (e := e) J hvi hed

/-- Helper for Lemma 10.57.10: the coordinatewise predecomposition sends each homogeneous
generator of the free cone module back to the matching direct-sum `lof`. -/
theorem free_cone_module_predecomposeLinear_right_inv {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)] :
    free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J ∘ₗ
      DirectSum.coeLinearMap
        (free_cone_module_grading (R := R) (n := n) (r := r) J) =
        LinearMap.id := by
  -- A direct-sum map is determined by its values on the `lof` generators.
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  -- A homogeneous generator is sent back to the matching direct-sum basis vector.
  simpa [LinearMap.comp_apply, DirectSum.coeLinearMap_lof] using
    (free_cone_module_predecompose_eq_lof_of_mem
      (R := R) (n := n) (r := r) (d := d) J x.2)

/-- Helper for Lemma 10.57.10: package the missing coordinatewise direct-sum decomposition owner
for the graded free cone module on `Fin r`. -/
@[reducible] noncomputable def free_cone_module_grading_decomposition {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)] :
    DirectSum.Decomposition
      (free_cone_module_grading (R := R) (n := n) (r := r) J) :=
  DirectSum.Decomposition.ofLinearMap
    (ℳ := free_cone_module_grading (R := R) (n := n) (r := r) J)
    (free_cone_module_predecomposeLinear (R := R) (n := n) (r := r) J)
    (free_cone_module_predecomposeLinear_left_inv
      (R := R) (n := n) (r := r) J)
    (free_cone_module_predecomposeLinear_right_inv
      (R := R) (n := n) (r := r) J)

/-- Helper for Lemma 10.57.10: coordinatewise multiplication by a homogeneous cone quotient class
preserves the free cone-module grading degree-by-degree. -/
theorem free_cone_module_grading_mul_mem {n r i j : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    {a : MvPolynomial (Fin (n + 1)) R ⧸ J}
    {v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (ha : a ∈ cone_quotient_grading (R := R) (n := n) J i)
    (hv : v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J j) :
    (fun k ↦ a * v k) ∈ free_cone_module_grading (R := R) (n := n) (r := r) J (i + j) := by
  -- Read membership coordinatewise: each entry stays homogeneous after multiplication by `a`.
  rw [mem_free_cone_module_grading_iff] at hv ⊢
  intro k
  exact SetLike.mul_mem_graded ha (hv k)

/-- Helper for Lemma 10.57.10: pointwise scalar multiplication by a homogeneous cone quotient
class raises the free cone-module degree by the same amount. -/
theorem free_cone_module_grading_pointwise_smul_mem {n r i j : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    {a : MvPolynomial (Fin (n + 1)) R ⧸ J}
    {v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (ha : a ∈ cone_quotient_grading (R := R) (n := n) J i)
    (hv : v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J j) :
    a • v ∈ free_cone_module_grading (R := R) (n := n) (r := r) J (i + j) := by
  -- Read the pointwise scalar action coordinatewise and use graded multiplication in each entry.
  rw [mem_free_cone_module_grading_iff] at hv ⊢
  intro k
  simpa [Pi.smul_apply, smul_eq_mul] using SetLike.mul_mem_graded ha (hv k)

/-- Helper for Lemma 10.57.10: the coordinatewise free cone-module grading is a graded module over
the cone quotient grading. -/
instance free_cone_module_grading_gradedSMul {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    SetLike.GradedSMul
      (cone_quotient_grading (R := R) (n := n) J)
      (free_cone_module_grading (R := R) (n := n) (r := r) J) where
  smul_mem := by
    intro i j a v ha hv
    exact free_cone_module_grading_pointwise_smul_mem
      (R := R) (n := n) (r := r) (i := i) (j := j) J ha hv

/-- Helper for Lemma 10.57.10: homogenizing an affine relation vector to one common degree yields
a homogeneous vector in the free cone module. -/
theorem homogenized_affine_relation_mem_free_cone_module_grading {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (k : Fin r → MvPolynomial (Fin n) R) :
    (fun i ↦ Ideal.Quotient.mk J (coneHomogenizeTo (R := R) (n := n) d (k i))) ∈
      free_cone_module_grading (R := R) (n := n) (r := r) J d := by
  -- Each coordinate is the quotient class of a degree-`d` homogenized polynomial, so the whole
  -- vector lands in the coordinatewise degree-`d` piece.
  rw [mem_free_cone_module_grading_iff]
  intro i
  exact cone_quotient_mk_mem_grade_of_isHomogeneous
    (R := R) (n := n) (J := J)
    (coneHomogenizeTo_isHomogeneous (R := R) (n := n) d (k i))

/-- Helper for Lemma 10.57.10: the source relation vector is homogenized in the maximum total
degree of its affine coordinates so that all entries land in one graded piece. -/
noncomputable def affine_relation_common_degree {n r : ℕ}
    (k : Fin r → MvPolynomial (Fin n) R) : ℕ :=
  Finset.sup Finset.univ fun i => (k i).totalDegree

/-- Helper for Lemma 10.57.10: every affine coordinate degree is bounded by the common
homogenization degree chosen for the whole relation vector. -/
theorem totalDegree_le_affine_relation_common_degree {n r : ℕ}
    (k : Fin r → MvPolynomial (Fin n) R) (i : Fin r) :
    (k i).totalDegree ≤ affine_relation_common_degree (R := R) (n := n) (r := r) k := by
  -- The chosen common degree is the supremum of all coordinate total degrees.
  simpa [affine_relation_common_degree] using
    (Finset.le_sup (f := fun j : Fin r => (k j).totalDegree) (Finset.mem_univ i))

/-- Helper for Lemma 10.57.10: homogenize an affine relation vector coordinatewise in the common
source degree so that it can be inserted into the free cone module. -/
noncomputable def homogenized_affine_relation {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (k : Fin r → MvPolynomial (Fin n) R) :
    Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J) :=
  fun i =>
    Ideal.Quotient.mk J
      (coneHomogenizeTo (R := R) (n := n)
        (affine_relation_common_degree (R := R) (n := n) (r := r) k) (k i))

/-- Helper for Lemma 10.57.10: the coordinatewise homogenized affine relation vector lies in the
graded free cone module piece indexed by its common source degree. -/
theorem homogenized_affine_relation_mem_common_degree {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (k : Fin r → MvPolynomial (Fin n) R) :
    homogenized_affine_relation (R := R) (n := n) (r := r) J k ∈
      free_cone_module_grading (R := R) (n := n) (r := r) J
        (affine_relation_common_degree (R := R) (n := n) (r := r) k) := by
  -- This is the previous coordinatewise homogeneous-vector lemma specialized to the common degree.
  simpa [homogenized_affine_relation] using
    (homogenized_affine_relation_mem_free_cone_module_grading
      (R := R) (n := n) (r := r)
      (d := affine_relation_common_degree (R := R) (n := n) (r := r) k) J k)

/-- Helper for Lemma 10.57.10: the source module quotient is the span of the homogenized affine
kernel relations inside the free cone module. -/
noncomputable def homogenized_relation_submodule {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    Submodule (MvPolynomial (Fin (n + 1)) R ⧸ J)
      (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) :=
  Submodule.span _ <|
    Set.range fun k : LinearMap.ker τ =>
      homogenized_affine_relation (R := R) (n := n) (r := r) J k.1

/-- Helper for Lemma 10.57.10: in a Nat-graded module, the span of homogeneous elements is a
homogeneous submodule. -/
theorem span_isHomogeneous_of_isHomogeneousElem_nat
    {A : Type*} [Semiring A]
    {M' : Type*} [AddCommMonoid M'] [Module A M']
    (ℳ : ℕ → Submodule A M')
    [DirectSum.Decomposition ℳ]
    {t : Set M'} (ht : ∀ x ∈ t, SetLike.IsHomogeneousElem ℳ x) :
    (Submodule.span A t).IsHomogeneous ℳ := by
  intro i x hx
  -- Keep the target degree fixed and run span induction on the statement that its homogeneous
  -- projection already lies back in the span.
  refine Submodule.span_induction
    (p := fun y _ ↦ ((DirectSum.decompose ℳ y i : ℳ i) : M') ∈ Submodule.span A t) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases ht y hy with ⟨j, hj⟩
    by_cases hji : j = i
    · subst hji
      simpa [DirectSum.decompose_of_mem_same ℳ hj] using
        (Submodule.subset_span hy : y ∈ Submodule.span A t)
    · simpa [DirectSum.decompose_of_mem_ne ℳ hj hji] using
        (Submodule.zero_mem (Submodule.span A t))
  · simpa using (Submodule.zero_mem (Submodule.span A t))
  · intro y z _ _ hy hz
    simpa [DirectSum.decompose_add] using
      (Submodule.add_mem (Submodule.span A t) hy hz)
  · intro a y _ hy
    simpa [map_smul] using
      (Submodule.smul_mem (Submodule.span A t) a hy)

/-- Helper for Lemma 10.57.10: if a homogeneous free-cone vector already lies in an `Scone`-span,
then every graded component of any pointwise scalar multiple still lies in that same span. -/
theorem free_cone_module_decompose_sum_component_eval {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition
      (free_cone_module_grading (R := R) (n := n) (r := r) J)]
    {α : Type*} (s : Finset α)
    (f : α → Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) (j : ℕ) :
    ((DirectSum.decompose
        (free_cone_module_grading (R := R) (n := n) (r := r) J) (Finset.sum s f) j :
        free_cone_module_grading (R := R) (n := n) (r := r) J j) :
        Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =
      Finset.sum s fun a =>
        ((DirectSum.decompose
            (free_cone_module_grading (R := R) (n := n) (r := r) J)
            (f a) j :
            free_cone_module_grading (R := R) (n := n) (r := r) J j) :
            Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) := by
  -- Rewrite `DirectSum.decompose` across the finite sum and then read off the `j`-th coordinate.
  rw [DirectSum.decompose_sum]
  simpa using
    (DFinsupp.finset_sum_apply s
      (fun a ↦ DirectSum.decompose
        (free_cone_module_grading (R := R) (n := n) (r := r) J) (f a))
      j)

/-- Helper for Lemma 10.57.10: if a homogeneous free-cone vector already lies in an `Scone`-span,
then every graded component of any pointwise scalar multiple still lies in that same span. -/
theorem free_cone_module_component_of_pointwise_smul_mem_span {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    [DirectSum.Decomposition
      (free_cone_module_grading (R := R) (n := n) (r := r) J)]
    {t : Set (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J))}
    {x : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)}
    (hx₁ : SetLike.IsHomogeneousElem
      (free_cone_module_grading (R := R) (n := n) (r := r) J) x)
    (hx₂ : x ∈ Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t)
    (a : MvPolynomial (Fin (n + 1)) R ⧸ J) (j : ℕ) :
    ((DirectSum.decompose
        (free_cone_module_grading (R := R) (n := n) (r := r) J) (a • x) j :
        free_cone_module_grading (R := R) (n := n) (r := r) J j) :
        Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ∈
      Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t := by
  classical
  rcases hx₁ with ⟨d, hx₁⟩
  let g : ℕ → Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J) := fun i =>
    (((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) a i :
        cone_quotient_grading (R := R) (n := n) J i) :
        MvPolynomial (Fin (n + 1)) R ⧸ J) • x)
  let u : Set (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) := Set.range g
  have hg_hom : ∀ i, SetLike.IsHomogeneousElem
      (free_cone_module_grading (R := R) (n := n) (r := r) J) (g i) := by
    intro i
    -- Each homogeneous scalar piece of `a` raises the degree of `x` by the same amount.
    refine ⟨i + d, ?_⟩
    exact free_cone_module_grading_pointwise_smul_mem
      (R := R) (n := n) (r := r) (i := i) (j := d) J
      ((DirectSum.decompose
          (cone_quotient_grading (R := R) (n := n) J) a i :
          cone_quotient_grading (R := R) (n := n) J i).2)
      hx₁
  have hu_hom :
      (Submodule.span R u).IsHomogeneous
        (free_cone_module_grading (R := R) (n := n) (r := r) J) := by
    -- The auxiliary span is generated by homogeneous vectors, so every graded projection stays in
    -- that span.
    refine span_isHomogeneous_of_isHomogeneousElem_nat
      (A := R)
      (ℳ := free_cone_module_grading (R := R) (n := n) (r := r) J)
      (t := u) ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact hg_hom i
  have hu_le :
      (Submodule.span R u) ≤
        (Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t).restrictScalars R := by
    -- Every generator of the auxiliary span already lies in the original `Scone`-span.
    refine Submodule.span_le.2 ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ hx₂
  have hax :
      a • x ∈ Submodule.span R u := by
    -- Decompose `a` into homogeneous scalar pieces and expand the scalar action through the finite
    -- support decomposition.
    let s : Finset ℕ :=
      (DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) a).support
    have hsum :
        ((∑ i ∈ s,
            ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) a i :
                cone_quotient_grading (R := R) (n := n) J i) :
              MvPolynomial (Fin (n + 1)) R ⧸ J)) : MvPolynomial (Fin (n + 1)) R ⧸ J) = a := by
      simpa [s] using
        (DirectSum.sum_support_decompose (cone_quotient_grading (R := R) (n := n) J) a)
    have hs :
        a • x = ∑ i ∈ s, g i := by
      calc
        a • x =
            ((∑ i ∈ s,
              ((DirectSum.decompose (cone_quotient_grading (R := R) (n := n) J) a i :
                  cone_quotient_grading (R := R) (n := n) J i) :
                  MvPolynomial (Fin (n + 1)) R ⧸ J)) : _) • x := by
          rw [hsum]
        _ = ∑ i ∈ s, g i := by
          simp [g, Finset.sum_smul]
    rw [hs]
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hgi : g i ∈ u := ⟨i, rfl⟩
    exact Submodule.subset_span hgi
  -- The target component belongs to the auxiliary homogeneous span, hence to the original span.
  exact hu_le (hu_hom j hax)

/-- Helper for Lemma 10.57.10: an `Scone`-span generated by homogeneous free-cone vectors remains
homogeneous after restricting scalars back to `R`. -/
theorem free_cone_module_span_restrictScalars_is_homogeneous {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    [DirectSum.Decomposition
      (free_cone_module_grading (R := R) (n := n) (r := r) J)]
    {t : Set (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J))}
    (ht : ∀ x ∈ t,
      SetLike.IsHomogeneousElem
        (free_cone_module_grading (R := R) (n := n) (r := r) J) x) :
    ((Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t).restrictScalars R).IsHomogeneous
      (free_cone_module_grading (R := R) (n := n) (r := r) J) := by
  classical
  let Scone := MvPolynomial (Fin (n + 1)) R ⧸ J
  letI : Module Scone Scone := cone_quotient_selfModule (R := R) (n := n) J
  letI : Module Scone (Fin r → Scone) :=
    free_cone_module_pointwiseModule (R := R) (n := n) (r := r) J
  letI : SMul Scone (Fin r → Scone) :=
    free_cone_module_pointwiseSMul (R := R) (n := n) (r := r) J
  intro i x hx
  -- Rewrite the restricted-scalars membership back to the original `Scone`-span.
  rw [Submodule.restrictScalars_mem] at hx ⊢
  -- Prove all components at once; the scalar step needs every component of the vector being
  -- multiplied, not only the currently requested degree.
  suffices hcomponents :
      ∀ y ∈ Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t,
        ∀ j,
          ((DirectSum.decompose
              (free_cone_module_grading (R := R) (n := n) (r := r) J) y j :
              free_cone_module_grading (R := R) (n := n) (r := r) J j) :
              Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ∈
            Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t by
    exact hcomponents x hx i
  intro y hy
  refine Submodule.span_induction
    (p := fun y _ ↦
      ∀ j,
        ((DirectSum.decompose
            (free_cone_module_grading (R := R) (n := n) (r := r) J) y j :
            free_cone_module_grading (R := R) (n := n) (r := r) J j) :
            Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ∈
          Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t)
    ?_ ?_ ?_ ?_ hy
  · -- A homogeneous generator contributes either itself in degree `i` or zero otherwise.
    intro y hy j
    rcases ht y hy with ⟨d, hy_d⟩
    by_cases hdi : d = j
    · subst hdi
      simpa [DirectSum.decompose_of_mem_same _ hy_d] using
        (Submodule.subset_span hy :
          y ∈ Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t)
    · simpa [DirectSum.decompose_of_mem_ne _ hy_d hdi] using
        (Submodule.zero_mem
          (Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t))
  · -- The zero vector has zero component in every degree.
    simpa using
      (Submodule.zero_mem
        (Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t))
  · -- Degreewise projections commute with addition.
    intro y z _ _ hy hz j
    simpa [DirectSum.decompose_add] using
      (Submodule.add_mem
        (Submodule.span (MvPolynomial (Fin (n + 1)) R ⧸ J) t) (hy j) (hz j))
  · -- Scalar multiples are handled by decomposing the vector into homogeneous pieces first.
    intro a y _ hy j
    let s : Finset ℕ :=
      (DirectSum.decompose
        (free_cone_module_grading (R := R) (n := n) (r := r) J) y).support
    let f : ℕ → Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J) := fun d =>
      a •
        ((DirectSum.decompose
            (free_cone_module_grading (R := R) (n := n) (r := r) J) y d :
            free_cone_module_grading (R := R) (n := n) (r := r) J d) :
            Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J))
    have hy_sum :
        (∑ d ∈ s,
          ((DirectSum.decompose
              (free_cone_module_grading (R := R) (n := n) (r := r) J) y d :
              free_cone_module_grading (R := R) (n := n) (r := r) J d) :
              Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J))) = y := by
      simpa [s] using
        (DirectSum.sum_support_decompose
          (free_cone_module_grading (R := R) (n := n) (r := r) J) y)
    have hsmul_sum : a • y = ∑ d ∈ s, f d := by
      ext k
      have hy_sum_apply :
          (∑ d ∈ s,
            ((DirectSum.decompose
                (free_cone_module_grading (R := R) (n := n) (r := r) J) y d :
                free_cone_module_grading (R := R) (n := n) (r := r) J d) :
                Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) k) = y k := by
        simpa [Finset.sum_apply] using
          congrArg (fun v : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J) => v k) hy_sum
      calc
        (a • y) k = a * y k := by
          simp [Pi.smul_apply, smul_eq_mul]
        _ =
            a * (∑ d ∈ s,
              ((DirectSum.decompose
                  (free_cone_module_grading (R := R) (n := n) (r := r) J) y d :
                  free_cone_module_grading (R := R) (n := n) (r := r) J d) :
                  Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) k) := by
          rw [hy_sum_apply]
        _ =
            ∑ d ∈ s,
              a *
                ((DirectSum.decompose
                  (free_cone_module_grading (R := R) (n := n) (r := r) J) y d :
                  free_cone_module_grading (R := R) (n := n) (r := r) J d) :
                  Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) k := by
          rw [Finset.mul_sum]
        _ = (∑ d ∈ s, f d) k := by
          simp [f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hcomponent_sum :
        ((DirectSum.decompose
            (free_cone_module_grading (R := R) (n := n) (r := r) J) (a • y) j :
            free_cone_module_grading (R := R) (n := n) (r := r) J j) :
            Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) =
          ∑ d ∈ s,
            ((DirectSum.decompose
                (free_cone_module_grading (R := R) (n := n) (r := r) J) (f d) j :
                free_cone_module_grading (R := R) (n := n) (r := r) J j) :
                Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) := by
      rw [hsmul_sum]
      exact free_cone_module_decompose_sum_component_eval
        (R := R) (n := n) (r := r) J s f j
    rw [hcomponent_sum]
    refine Submodule.sum_mem _ ?_
    intro d hd
    let xcomp : Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J) :=
      ((DirectSum.decompose
          (free_cone_module_grading (R := R) (n := n) (r := r) J) y d :
          free_cone_module_grading (R := R) (n := n) (r := r) J d) :
          Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J))
    have hxhom : SetLike.IsHomogeneousElem
        (free_cone_module_grading (R := R) (n := n) (r := r) J)
        xcomp := by
      exact ⟨d,
        (DirectSum.decompose
          (free_cone_module_grading (R := R) (n := n) (r := r) J) y d).2⟩
    exact free_cone_module_component_of_pointwise_smul_mem_span
      (R := R) (n := n) (r := r) J
      (t := t)
      (x := xcomp)
      hxhom (hy d) a j

/-- Helper for Lemma 10.57.10: once the coordinatewise free-module grading owners are fixed, the
span of the homogenized affine relation vectors is the homogeneous relation submodule from the
source proof. -/
theorem homogenized_relation_submodule_is_homogeneous {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    [DirectSum.Decomposition (cone_quotient_grading (R := R) (n := n) J)]
    [DirectSum.Decomposition
      (free_cone_module_grading (R := R) (n := n) (r := r) J)]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    ((homogenized_relation_submodule (R := R) (n := n) (r := r) J τ).restrictScalars R).IsHomogeneous
      (free_cone_module_grading (R := R) (n := n) (r := r) J) := by
  classical
  -- The relation submodule is generated by homogeneous homogenized kernel vectors.
  simpa [homogenized_relation_submodule] using
    (free_cone_module_span_restrictScalars_is_homogeneous
      (R := R) (n := n) (r := r) J
      (t := Set.range fun k : LinearMap.ker τ =>
        homogenized_affine_relation (R := R) (n := n) (r := r) J k.1)
      (fun x hx => by
        rcases hx with ⟨k, rfl⟩
        exact ⟨affine_relation_common_degree (R := R) (n := n) (r := r) k.1,
          homogenized_affine_relation_mem_common_degree
            (R := R) (n := n) (r := r) J k.1⟩))

/-- Helper for Lemma 10.57.10: restrict the quotient map to the homogenized relation cokernel
along `R`, so the quotient grading can be expressed as an `R`-graded family. -/
noncomputable def homogenized_relation_quotient_mkQ {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) →ₗ[R]
      ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
        homogenized_relation_submodule (R := R) (n := n) (r := r) J τ) :=
  (((Submodule.mkQ (homogenized_relation_submodule (R := R) (n := n) (r := r) J τ)) :
      (Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) →ₗ[(MvPolynomial (Fin (n + 1)) R ⧸ J)]
        ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
          homogenized_relation_submodule (R := R) (n := n) (r := r) J τ)).restrictScalars R)

/-- Helper for Lemma 10.57.10: the homogenized relation cokernel inherits its degree-`d` piece by
mapping the free cone-module degree-`d` part through the quotient map. -/
noncomputable def homogenized_relation_quotient_grading {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    (d : ℕ) :
    Submodule R
      ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
        homogenized_relation_submodule (R := R) (n := n) (r := r) J τ) :=
  (free_cone_module_grading (R := R) (n := n) (r := r) J d).map
    (homogenized_relation_quotient_mkQ (R := R) (n := n) (r := r) J τ)

/-- Helper for Lemma 10.57.10: membership in the quotient grading means that the class has a
homogeneous lift in the free cone module of the same degree. -/
theorem mem_homogenized_relation_quotient_grading_iff {n r d : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    {x : ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
      homogenized_relation_submodule (R := R) (n := n) (r := r) J τ)} :
    x ∈ homogenized_relation_quotient_grading (R := R) (n := n) (r := r) J τ d ↔
      ∃ y ∈ free_cone_module_grading (R := R) (n := n) (r := r) J d,
        homogenized_relation_quotient_mkQ (R := R) (n := n) (r := r) J τ y = x := by
  -- Unfold the quotient piece: it is literally the image of the homogeneous free piece.
  rfl

/-- Helper for Lemma 10.57.10: multiplying a homogeneous quotient class in the ring with a
homogeneous quotient class in the module preserves the expected total degree after passing to the
cokernel. -/
theorem homogenized_relation_quotient_grading_smul_mem {n r i j : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M)
    {a : MvPolynomial (Fin (n + 1)) R ⧸ J}
    {x : ((Fin r → (MvPolynomial (Fin (n + 1)) R ⧸ J)) ⧸
      homogenized_relation_submodule (R := R) (n := n) (r := r) J τ)}
    (ha : a ∈ cone_quotient_grading (R := R) (n := n) J i)
    (hx : x ∈ homogenized_relation_quotient_grading (R := R) (n := n) (r := r) J τ j) :
    a • x ∈ homogenized_relation_quotient_grading (R := R) (n := n) (r := r) J τ (i + j) := by
  -- Lift the quotient class to a homogeneous free-cone vector, multiply upstairs, and descend the
  -- result back through the quotient map.
  rcases (mem_homogenized_relation_quotient_grading_iff
      (R := R) (n := n) (r := r) (d := j) J τ).1 hx with ⟨y, hy, rfl⟩
  refine (mem_homogenized_relation_quotient_grading_iff
      (R := R) (n := n) (r := r) (d := i + j) J τ).2 ?_
  refine ⟨a • y, ?_, ?_⟩
  · exact free_cone_module_grading_pointwise_smul_mem
      (R := R) (n := n) (r := r) (i := i) (j := j) J ha hy
  · -- The quotient map is still `S`-linear before restricting scalars back to `R`.
    change homogenized_relation_quotient_mkQ (R := R) (n := n) (r := r) J τ (a • y) =
      a • homogenized_relation_quotient_mkQ (R := R) (n := n) (r := r) J τ y
    simp [homogenized_relation_quotient_mkQ]

/-- Helper for Lemma 10.57.10: the quotient grading on the homogenized relation cokernel is a
graded module over the shifted cone quotient ring. -/
instance homogenized_relation_quotient_grading_gradedSMul {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    SetLike.GradedSMul
      (cone_quotient_grading (R := R) (n := n) J)
      (homogenized_relation_quotient_grading (R := R) (n := n) (r := r) J τ) where
  smul_mem := by
    intro i j a x ha hx
    exact homogenized_relation_quotient_grading_smul_mem
      (R := R) (n := n) (r := r) (i := i) (j := j) J τ ha hx

/-- Helper for Lemma 10.57.10: the finite free cone module on `Fin r` is finite over the cone
quotient ring. This records the finite-basis witness explicitly, avoiding fragile instance
search in the cokernel step. -/
theorem moduleFinite_free_cone_module {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R)) :
    let Scone := MvPolynomial (Fin (n + 1)) R ⧸ J
    let _ : Module Scone Scone := Semiring.toModule
    let _ : Module Scone (Fin r → Scone) :=
      Pi.Function.module (I := Fin r) (α := Scone) (β := Scone)
    Module.Finite Scone (Fin r → Scone) := by
  -- The standard basis on `Fin r → Scone` already gives the finite free presentation needed here.
  let Scone := MvPolynomial (Fin (n + 1)) R ⧸ J
  letI : Module Scone Scone := Semiring.toModule
  letI : Module Scone (Fin r → Scone) :=
    Pi.Function.module (I := Fin r) (α := Scone) (β := Scone)
  exact (show Module.Finite Scone (Fin r → Scone) from
    Module.Finite.of_basis (Pi.basisFun Scone (Fin r)))

/-- Helper for Lemma 10.57.10: once the homogenized relation span is fixed, the source cokernel
candidate is automatically finite because it is a quotient of a finite free cone module. -/
theorem moduleFinite_homogenized_relation_quotient {n r : ℕ}
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    [Module (MvPolynomial (Fin n) R) M]
    (τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M) :
    let Scone := MvPolynomial (Fin (n + 1)) R ⧸ J
    let _ : Module Scone Scone := Semiring.toModule
    let _ : Module Scone (Fin r → Scone) :=
      Pi.Function.module (I := Fin r) (α := Scone) (β := Scone)
    Module.Finite Scone
      ((Fin r → Scone) ⧸
        homogenized_relation_submodule (R := R) (n := n) (r := r) J τ) := by
  let Scone := MvPolynomial (Fin (n + 1)) R ⧸ J
  letI : Module Scone Scone := Semiring.toModule
  letI : Module Scone (Fin r → Scone) :=
    Pi.Function.module (I := Fin r) (α := Scone) (β := Scone)
  let _ :
      Module.Finite Scone (Fin r → Scone) := by
    -- Use the explicit finite-basis witness to keep this step stable under elaboration changes.
    simpa [Scone] using moduleFinite_free_cone_module (R := R) (n := n) (r := r) J
  -- The source cokernel is a quotient of that finite free module via the canonical quotient map.
  exact (show
      Module.Finite Scone
        ((Fin r → Scone) ⧸ homogenized_relation_submodule (R := R) (n := n) (r := r) J τ) from
    Module.Finite.of_surjective
      (Submodule.mkQ (homogenized_relation_submodule (R := R) (n := n) (r := r) J τ))
      (Submodule.mkQ_surjective _))

end Lemma_10_57_10

end
