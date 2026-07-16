import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_105_3

-- Theorem-local helper module for Lemma 15.105.20.

open CategoryTheory Limits

universe u v w

section

variable {R : Type w} [CommRing R]

/-- Helper for Lemma 15.105.20: if every finitely generated ideal of `R` is flat, then every
submodule of a flat `R`-module is flat. -/
private theorem submodule_flat_of_fg_ideal_flat
    (hfg : ∀ I : Ideal R, I.FG → Module.Flat R I)
    (M : ModuleCat.{w} R) [Module.Flat R M] (N : Submodule R M) :
    Module.Flat R N := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hI
  letI : Module.Flat R I := hfg I hI
  have hmap :
      Function.Injective
        (TensorProduct.map (LinearMap.id : I →ₗ[R] I) N.subtype) := by
    simpa using
      (TensorProduct.map_injective_of_flat_flat'
        (R := R)
        (f := (LinearMap.id : I →ₗ[R] I))
        (g := N.subtype)
        (hf := fun _ _ h ↦ h)
        (hg := N.subtype_injective))
  have hflatM :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)) := by
    exact
      (Module.Flat.iff_lift_lsmul_comp_subtype_injective (R := R) (M := M)).1 inferInstance hI
  have hcomp :
      N.subtype.comp (TensorProduct.lift ((LinearMap.lsmul R N).comp I.subtype)) =
        (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)).comp
          (TensorProduct.map (LinearMap.id : I →ₗ[R] I) N.subtype) := by
    ext x y
    rfl
  let αN := TensorProduct.lift ((LinearMap.lsmul R N).comp I.subtype)
  let αM := TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  let β := TensorProduct.map (LinearMap.id : I →ₗ[R] I) N.subtype
  have hcomp_apply : ∀ z, N.subtype (αN z) = αM (β z) := by
    intro z
    simpa [αN, αM, β, LinearMap.comp_apply] using congrArg (fun f => f z) hcomp
  intro x y hxy
  have hcompxy :
      αM (β x) = αM (β y) := by
    rw [← hcomp_apply x, ← hcomp_apply y]
    exact congrArg N.subtype hxy
  exact hmap (hflatM hcompxy)

/-- Helper for Lemma 15.105.20: if every submodule of a flat `R`-module is flat, then `R` has
weak dimension at most `1`. -/
private theorem weak_dimension_le_one_of_submodule_flat
    (hsub :
      ∀ (M : ModuleCat.{w} R) [Module.Flat R M] (N : Submodule R M),
        Module.Flat R N) :
    HasWeakDimensionLE R 1 := by
  refine ⟨?_⟩
  intro M
  let q : Projective.over M ⟶ M := Projective.π M
  let F : Fin 2 → ModuleCat R := fun i ↦ Fin.cases (Projective.over M) (fun _ ↦ kernel q) i
  let δ : (i : Fin 1) → F i.succ ⟶ F i.castSucc :=
    fun i ↦ Fin.cases (kernel.ι q) (fun j ↦ Fin.elim0 j) i
  have hProjectiveFlat : Module.Flat R ↑(Projective.over M) := by
    -- The canonical projective cover is flat.
    exact Module.Flat.of_projective
  have hKernelKerFlat : Module.Flat R (LinearMap.ker q.hom) := by
    -- Apply the hypothesis to the kernel submodule inside the flat projective cover.
    letI : Module.Flat R ↑(Projective.over M) := hProjectiveFlat
    exact hsub (Projective.over M) (LinearMap.ker q.hom)
  have hKernelFlat : Module.Flat R ↑(kernel q) := by
    -- Transport flatness from the concrete kernel submodule to the categorical kernel object.
    letI : Module.Flat R (ModuleCat.of R (LinearMap.ker q.hom)) := hKernelKerFlat
    exact Module.Flat.of_linearEquiv (ModuleCat.kernelIsoKer q).toLinearEquiv
  have hq_surj : Function.Surjective q.hom := by
    -- Projective covers are epimorphisms in `ModuleCat`.
    exact (ModuleCat.epi_iff_surjective q).1 inferInstance
  have hq_exact : Function.Exact (kernel.ι q).hom q.hom := by
    -- The standard kernel row is exact.
    let S : ShortComplex (ModuleCat R) := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
    have hSExact : S.Exact := by
      simpa [S] using ShortComplex.exact_kernel q
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hSExact
  have hδ_injective : Function.Injective (kernel.ι q).hom := by
    -- Kernels are monomorphisms in `ModuleCat`.
    exact (ModuleCat.mono_iff_injective (kernel.ι q)).1 inferInstance
  have hresolution : ModuleCat.HasFiniteFlatResolutionLengthLE M 1 := by
    -- The projective cover and its flat kernel give a two-term flat resolution.
    refine ⟨F, ?_, δ, q, hq_surj, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa [F] using hProjectiveFlat
      · intro j
        simpa [F] using hKernelFlat
    · simpa [δ] using hq_exact
    · intro i
      exact Fin.elim0 i
    · simpa [δ] using hδ_injective
  exact ModuleCat.HasFiniteFlatResolutionLengthLE.hasTorDimensionLE (M := M) hresolution

end

section

variable {J : Type u}
variable {A : J → Type v}
variable [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)]

attribute [local instance] Classical.decEq

/-- Helper for Lemma 15.105.20: a finitely generated ideal in a product ring agrees with the
product of its component images under the evaluation maps. -/
private lemma fg_ideal_eq_pi_component_maps (I : Ideal ((j : J) → A j)) (hI : I.FG) :
    I = Ideal.pi (fun j ↦ Ideal.map (Pi.evalRingHom A j) I) := by
  classical
  obtain ⟨s, hs⟩ := hI
  ext x
  constructor
  · intro hx j
    -- Evaluating an element of `I` lands in the corresponding component ideal.
    rw [Ideal.mem_map_iff_of_surjective (Pi.evalRingHom A j) (Function.surjective_eval j)]
    exact ⟨x, hx, rfl⟩
  · intro hx
    -- Finite generation lets us reassemble the coordinatewise expressions into one global one.
    have hx' :
        ∀ j, x j ∈ Ideal.span ((fun y : (j : J) → A j ↦ y j) '' (↑s : Set ((j : J) → A j))) := by
      intro j
      have hxj : x j ∈ Ideal.map (Pi.evalRingHom A j) I := hx j
      rw [← hs] at hxj
      simpa [Ideal.map_span] using hxj
    have hcoeff :
        ∀ j, ∃ c : s → A j, ∑ i, c i * i.1 j = x j := by
      intro j
      simpa [smul_eq_mul] using
        (Submodule.mem_span_image_finset_iff_exists_fun (R := A j)
          (v := fun y : (j : J) → A j ↦ y j) (s := s)).mp (hx' j)
    choose c hc using hcoeff
    let coeff : s → ((j : J) → A j) := fun i j ↦ c j i
    let y : (j : J) → A j := ∑ i, coeff i * i.1
    have hy_mem_span : y ∈ Ideal.span (↑s : Set ((j : J) → A j)) := by
      -- By construction `y` is an `s`-linear combination.
      refine Ideal.sum_mem (Ideal.span (↑s : Set ((j : J) → A j))) ?_
      intro i hi
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span i.2)
    have hy : y = x := by
      -- Coordinatewise, the chosen coefficients recover the target element.
      funext j
      simp only [y, coeff, Finset.sum_apply, Pi.mul_apply]
      exact hc j
    rw [← hs]
    simpa [hy] using hy_mem_span

/-- Helper for Lemma 15.105.20: once each component ideal is principal, the whole finitely
generated ideal is principal with the assembled generator. -/
private lemma fg_ideal_eq_span_singleton_of_componentwise_principal
    (I : Ideal ((j : J) → A j)) (Icomp : ∀ j, Ideal (A j)) (f : (j : J) → A j)
    (hI : I = Ideal.pi Icomp)
    (hf : ∀ j, Icomp j = Ideal.span ({f j} : Set (A j))) :
    I = Ideal.span ({f} : Set ((j : J) → A j)) := by
  -- Product ideals of singleton spans collapse to the singleton span of the assembled family.
  calc
    I = Ideal.pi Icomp := hI
    _ = Ideal.pi (fun j ↦ Ideal.span ({f j} : Set (A j))) := by
      rw [show Icomp = fun j ↦ Ideal.span ({f j} : Set (A j)) from funext hf]
    _ = Ideal.span ({f} : Set ((j : J) → A j)) := Ideal.pi_span

/-- Helper for Lemma 15.105.20: multiplication by an idempotent sends the ambient ring into the
ideal it generates. -/
private lemma support_idempotent_mul_mem_span (e x : (j : J) → A j) :
    e * x ∈ Ideal.span ({e} : Set ((j : J) → A j)) := by
  exact Ideal.mem_span_singleton'.mpr ⟨x, by rw [mul_comm]⟩

/-- Helper for Lemma 15.105.20: the standard multiplication map onto an idempotent ideal lands in
that ideal. -/
private def support_idempotent_retraction (e : (j : J) → A j) :
    ((j : J) → A j) →ₗ[((j : J) → A j)] Ideal.span ({e} : Set ((j : J) → A j)) :=
  (LinearMap.mulLeft ((j : J) → A j) e).codRestrict (Ideal.span ({e} : Set ((j : J) → A j)))
    (support_idempotent_mul_mem_span (A := A) e)

/-- Helper for Lemma 15.105.20: on the ideal generated by an idempotent, multiplying by that
idempotent is the identity. -/
private lemma support_idempotent_mul_eq_self_of_mem_span
    {e x : (j : J) → A j} (he : e * e = e)
    (hx : x ∈ Ideal.span ({e} : Set ((j : J) → A j))) :
    e * x = x := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  calc
    e * (a * e) = a * (e * e) := by
      ext j
      simp [mul_comm, mul_left_comm]
    _ = a * e := by rw [he]

/-- Helper for Lemma 15.105.20: the retraction onto an idempotent ideal splits the inclusion of
that ideal into the ambient free module. -/
private lemma support_idempotent_retraction_comp_subtype (e : (j : J) → A j)
    (he : e * e = e) :
    (support_idempotent_retraction (A := A) e).comp
        (Submodule.subtype (Ideal.span ({e} : Set ((j : J) → A j)))) =
      LinearMap.id := by
  ext x j
  exact congrArg (fun z : (j : J) → A j ↦ z j)
    (support_idempotent_mul_eq_self_of_mem_span (A := A) he x.2)

/-- Helper for Lemma 15.105.20: an ideal generated by an idempotent element is flat because it is
a retract of the free rank-one module. -/
private lemma flat_span_singleton_of_isIdempotentElem (e : (j : J) → A j)
    (he : e * e = e) :
    Module.Flat ((j : J) → A j) (Ideal.span ({e} : Set ((j : J) → A j))) := by
  -- The inclusion splits by multiplication with `e`, so the ideal is a retract of a free module.
  let i := Submodule.subtype (Ideal.span ({e} : Set ((j : J) → A j)))
  let r := support_idempotent_retraction (A := A) e
  have hr : r.comp i = LinearMap.id := support_idempotent_retraction_comp_subtype (A := A) e he
  exact Module.Flat.of_retract i r hr

/-- Helper for Lemma 15.105.20: componentwise nonvanishing makes multiplication injective on the
product ring. -/
private lemma mulLeft_injective_of_componentwise_nonzero (g : (j : J) → A j)
    (hg : ∀ j, g j ≠ 0) :
    Function.Injective (LinearMap.mulLeft ((j : J) → A j) g) := by
  -- Evaluate each coordinate and use that the factors are domains.
  intro x y hxy
  funext j
  have hxyj :
      g j * x j = g j * y j := by
    exact congrArg (fun z : (j : J) → A j ↦ z j) hxy
  have hz : g j * (x j - y j) = 0 := by
    rw [mul_sub, hxyj, sub_self]
  have hdiff : x j - y j = 0 := by
    exact (mul_eq_zero.mp hz).resolve_left (hg j)
  exact sub_eq_zero.mp hdiff

/-- Helper for Lemma 15.105.20: if `f = g * e`, then multiplying the ideal `(e)` by `g` has range
exactly the ideal `(f)`. -/
private lemma range_mul_subtype_span_singleton_eq_span_singleton
    (e g f : (j : J) → A j) (hfg : g * e = f) :
    LinearMap.range
        ((LinearMap.mulLeft ((j : J) → A j) g).comp
          (Submodule.subtype (Ideal.span ({e} : Set ((j : J) → A j)))) ) =
      Ideal.span ({f} : Set ((j : J) → A j)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    -- Any element in the range is a multiple of `f = g * e`.
    rcases Ideal.mem_span_singleton'.mp x.2 with ⟨a, ha⟩
    refine Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩
    calc
      a * f = a * (g * e) := by rw [← hfg]
      _ = g * (a * e) := by
        ext j
        simp [mul_left_comm, mul_comm]
      _ = g * (x : (j : J) → A j) := by rw [ha]
  · intro hy
    -- Conversely, any multiple of `f` comes from the matching multiple of `e`.
    rcases Ideal.mem_span_singleton'.mp hy with ⟨a, ha⟩
    refine ⟨⟨a * e, ?_⟩, ?_⟩
    · exact Ideal.mem_span_singleton'.mpr ⟨a, by simp [mul_comm]⟩
    change g * ((a * e : (j : J) → A j)) = y
    calc
      g * (a * e) = a * (g * e) := by
        ext j
        simp [mul_left_comm, mul_comm]
      _ = a * f := by rw [hfg]
      _ = y := by rw [ha]

/-- Helper for Lemma 15.105.20: the auxiliary factor in the support-idempotent decomposition is
componentwise nonzero. -/
private lemma support_generator_factor_ne_zero (f : (j : J) → A j) :
    ∀ j, (if f j = 0 then (1 : A j) else f j) ≠ 0 := by
  intro j
  by_cases hf : f j = 0
  · simp [hf]
  · simpa [hf] using hf

/-- Helper for Lemma 15.105.20: the original generator family factors as the support idempotent
times the componentwise nonzero factor. -/
private lemma support_generator_factor_mul_support_idempotent (f : (j : J) → A j) :
    (fun j ↦ if f j = 0 then (1 : A j) else f j) *
        (fun j ↦ if f j = 0 then 0 else 1) =
      f := by
  -- Pointwise the factorization is either `1 * 0` or `f j * 1`.
  funext j
  by_cases hf : f j = 0
  · simp [hf]
  · simp [hf]

/-- Helper for Lemma 15.105.20: restricting multiplication by the support factor to the
support-idempotent ideal is injective. -/
private lemma support_generator_restricted_mul_injective (f : (j : J) → A j) :
    Function.Injective
      (((LinearMap.mulLeft ((j : J) → A j) (fun j ↦ if f j = 0 then (1 : A j) else f j)).comp
        (Submodule.subtype
          (Ideal.span ({fun j ↦ if f j = 0 then 0 else 1} : Set ((j : J) → A j)))))) := by
  -- Injectivity reduces to injectivity of the ambient multiplication map.
  intro x y hxy
  apply Subtype.ext
  exact
    mulLeft_injective_of_componentwise_nonzero (A := A)
      (fun j ↦ if f j = 0 then (1 : A j) else f j)
      (support_generator_factor_ne_zero (A := A) f) <| by
        simpa using hxy

/-- Helper for Lemma 15.105.20: the restricted multiplication map by the support factor has range
equal to the original principal ideal. -/
private lemma support_generator_restricted_mul_range (f : (j : J) → A j) :
    LinearMap.range
        (((LinearMap.mulLeft ((j : J) → A j) (fun j ↦ if f j = 0 then (1 : A j) else f j)).comp
          (Submodule.subtype
            (Ideal.span ({fun j ↦ if f j = 0 then 0 else 1} : Set ((j : J) → A j)))))) =
      Ideal.span ({f} : Set ((j : J) → A j)) := by
  exact
    range_mul_subtype_span_singleton_eq_span_singleton (A := A)
      (fun j ↦ if f j = 0 then 0 else 1)
      (fun j ↦ if f j = 0 then (1 : A j) else f j)
      f
      (support_generator_factor_mul_support_idempotent (A := A) f)

/-- Helper for Lemma 15.105.20: the support idempotent associated to a generator family is
linearly equivalent to the original principal ideal. -/
private noncomputable def support_idempotent_span_linearEquiv_generator_span
    (f : (j : J) → A j) :
    let e : (j : J) → A j := fun j ↦ if f j = 0 then 0 else 1
    let g : (j : J) → A j := fun j ↦ if f j = 0 then 1 else f j
    Ideal.span ({e} : Set ((j : J) → A j)) ≃ₗ[((j : J) → A j)]
      Ideal.span ({f} : Set ((j : J) → A j)) :=
  let e : (j : J) → A j := fun j ↦ if f j = 0 then 0 else 1
  let g : (j : J) → A j := fun j ↦ if f j = 0 then 1 else f j
  let m :
      Ideal.span ({e} : Set ((j : J) → A j)) →ₗ[((j : J) → A j)] ((j : J) → A j) :=
    (LinearMap.mulLeft ((j : J) → A j) g).comp
      (Submodule.subtype (Ideal.span ({e} : Set ((j : J) → A j))))
  (LinearEquiv.ofInjective m (support_generator_restricted_mul_injective (A := A) f)).trans
    (LinearEquiv.ofEq _ _ (support_generator_restricted_mul_range (A := A) f))

/-- Helper for Lemma 15.105.20: the support idempotent attached to a family is idempotent. -/
private lemma support_idempotent_sq (f : (j : J) → A j) :
    (let e : (j : J) → A j := fun j ↦ if f j = 0 then 0 else 1; e * e = e) := by
  -- Pointwise, the support idempotent only takes the values `0` and `1`.
  funext j
  by_cases hf : f j = 0
  · simp [hf]
  · simp [hf]

variable [∀ j, ValuationRing (A j)]

/-- Helper for Lemma 15.105.20: a product of valuation rings has weak dimension at most `1`. -/
theorem hasWeakDimensionLEOne_pi_of_valuationRing :
    HasWeakDimensionLE ((j : J) → A j) 1 := by
  have hfg :
      ∀ I : Ideal ((j : J) → A j), I.FG → Module.Flat ((j : J) → A j) I := by
    intro I hI
    -- Rewrite the ideal as the product of its component ideals.
    let Icomp : (j : J) → Ideal (A j) := fun j ↦ Ideal.map (Pi.evalRingHom A j) I
    have hpi : I = Ideal.pi Icomp := fg_ideal_eq_pi_component_maps (A := A) I hI
    -- Each component ideal is principal because each factor is a valuation ring.
    have hprincipal : ∀ j, (Icomp j).IsPrincipal := by
      intro j
      exact IsBezout.isPrincipal_of_FG (Icomp j) (Ideal.FG.map hI (Pi.evalRingHom A j))
    have hprincipal_eq : ∀ j, ∃ x : A j, Icomp j = Ideal.span ({x} : Set (A j)) := by
      intro j
      letI : (Icomp j).IsPrincipal := hprincipal j
      exact
        ⟨Submodule.IsPrincipal.generator (Icomp j),
          (Ideal.span_singleton_generator (Icomp j)).symm⟩
    choose f hf using hprincipal_eq
    have hI_span : I = Ideal.span ({f} : Set ((j : J) → A j)) :=
      fg_ideal_eq_span_singleton_of_componentwise_principal (A := A) I Icomp f hpi hf
    -- Replace the principal ideal `(f)` by the isomorphic idempotent ideal `(e)`.
    let e : (j : J) → A j := fun j ↦ if f j = 0 then 0 else 1
    have he : e * e = e := by
      simpa [e] using (support_idempotent_sq (A := A) f)
    letI : Module.Flat ((j : J) → A j) (Ideal.span ({e} : Set ((j : J) → A j))) :=
      flat_span_singleton_of_isIdempotentElem (A := A) e he
    have hflat_span_f :
        Module.Flat ((j : J) → A j) (Ideal.span ({f} : Set ((j : J) → A j))) := by
      exact Module.Flat.of_linearEquiv
        ((support_idempotent_span_linearEquiv_generator_span (A := A) f).symm)
    rw [hI_span]
    exact hflat_span_f
  have hsub :
      ∀ (M : ModuleCat.{max u v} ((j : J) → A j)) [Module.Flat ((j : J) → A j) M]
        (N : Submodule ((j : J) → A j) M),
        Module.Flat ((j : J) → A j) N := by
    intro M _ N
    exact submodule_flat_of_fg_ideal_flat (R := ((j : J) → A j)) hfg M N
  exact weak_dimension_le_one_of_submodule_flat (R := ((j : J) → A j)) hsub

end
