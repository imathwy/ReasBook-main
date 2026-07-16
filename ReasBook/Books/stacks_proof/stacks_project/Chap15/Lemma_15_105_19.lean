import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_105_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {J : Type u}

/-
Domain-style sampling:
- primary domain: commutative algebra of weak dimension, valuation rings, and localization of
  product rings;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ValuationRing`,
  `IsFractionRing`,
  `IsLocalization`;
- best owner abstraction:
  part `(1)` is genuinely source-facing, but its public owner is still the chapter class
  `HasWeakDimensionLE`, so the target surface should provide that owner directly for the product
  ring;
  part `(2)` is exact-interface reuse of the canonical product-localization `IsLocalization`
  instance, so it should be exposed by direct instance synthesis rather than restated behind a
  duplicate local theorem name.

Primitive-vs-derived split:
- primitive data: the family of valuation rings `A j`, and for part `(2)` the family of fraction
  rings `K j` together with the canonical `CommRing`, `Algebra`, and `IsFractionRing` instances;
- derived API: the product weak-dimension statement in part `(1)`, and the product localization
  statement in part `(2)`, which is already owned canonically by `IsLocalization`.

Source/core/bridge triage:
- `source-facing`: part `(1)`, the Stacks weak-dimension statement for products of valuation
  rings;
- `core/canonical`: `HasWeakDimensionLE`, `ValuationRing`, `IsFractionRing`, and
  `IsLocalization`;
- `bridge/view`: part `(2)` is only a direct specialization of the canonical localization owner,
  so it should stay as direct instance synthesis rather than a parallel wrapper theorem.
-/

variable {A : J → Type v}
variable [∀ j, CommRing (A j)]

attribute [local instance] Classical.decEq

/-- Helper for Lemma 15.105.19: a finitely generated ideal in a product ring agrees with the
product of its component images under the evaluation maps. -/
private lemma fg_ideal_eq_pi_component_maps (I : Ideal ((j : J) → A j)) (hI : I.FG) :
    I = Ideal.pi (fun j ↦ Ideal.map (Pi.evalRingHom A j) I) := by
  classical
  obtain ⟨s, hs⟩ := hI
  ext x
  constructor
  · -- Membership in `I` implies membership in every component image by evaluation.
    intro hx j
    rw [Ideal.mem_map_iff_of_surjective (Pi.evalRingHom A j) (Function.surjective_eval j)]
    exact ⟨x, hx, rfl⟩
  · -- Finite generation lets us reconstruct a global element from compatible component witnesses.
    intro hx
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
      -- The reconstructed element is an `s`-linear combination of the chosen generators.
      refine Ideal.sum_mem (Ideal.span (↑s : Set ((j : J) → A j))) ?_
      intro i hi
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span i.2)
    have hy : y = x := by
      -- Coordinatewise, the chosen coefficients recover the prescribed component values.
      funext j
      simp only [y, coeff, Finset.sum_apply, Pi.mul_apply]
      exact hc j
    rw [← hs]
    simpa [hy] using hy_mem_span

/-- Helper for Lemma 15.105.19: once each component ideal is principal, the whole finitely
generated ideal is principal with the assembled generator. -/
private lemma fg_ideal_eq_span_singleton_of_componentwise_principal
    (I : Ideal ((j : J) → A j)) (Icomp : ∀ j, Ideal (A j)) (f : (j : J) → A j)
    (hI : I = Ideal.pi Icomp)
    (hf : ∀ j, Icomp j = Ideal.span ({f j} : Set (A j))) :
    I = Ideal.span ({f} : Set ((j : J) → A j)) := by
  -- The product of the componentwise singleton spans is exactly the singleton span in the product.
  calc
    I = Ideal.pi Icomp := hI
    _ = Ideal.pi (fun j ↦ Ideal.span ({f j} : Set (A j))) := by
      rw [show Icomp = fun j ↦ Ideal.span ({f j} : Set (A j)) from funext hf]
    _ = Ideal.span ({f} : Set ((j : J) → A j)) := Ideal.pi_span

/-- Helper for Lemma 15.105.19: multiplication by an idempotent sends the ambient ring into the
ideal it generates. -/
private lemma support_idempotent_mul_mem_span (e x : (j : J) → A j) :
    e * x ∈ Ideal.span ({e} : Set ((j : J) → A j)) := by
  exact Ideal.mem_span_singleton'.mpr ⟨x, by rw [mul_comm]⟩

/-- Helper for Lemma 15.105.19: the standard multiplication map onto an idempotent ideal lands in
that ideal. -/
private def support_idempotent_retraction (e : (j : J) → A j) :
    ((j : J) → A j) →ₗ[((j : J) → A j)] Ideal.span ({e} : Set ((j : J) → A j)) :=
  (LinearMap.mulLeft ((j : J) → A j) e).codRestrict (Ideal.span ({e} : Set ((j : J) → A j)))
    (support_idempotent_mul_mem_span (A := A) e)

/-- Helper for Lemma 15.105.19: on the ideal generated by an idempotent, multiplying by that
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

/-- Helper for Lemma 15.105.19: the retraction onto an idempotent ideal splits the inclusion of
that ideal into the ambient free module. -/
private lemma support_idempotent_retraction_comp_subtype (e : (j : J) → A j)
    (he : e * e = e) :
    (support_idempotent_retraction (A := A) e).comp
        (Submodule.subtype (Ideal.span ({e} : Set ((j : J) → A j)))) =
      LinearMap.id := by
  ext x j
  exact congrArg (fun z : (j : J) → A j ↦ z j)
    (support_idempotent_mul_eq_self_of_mem_span (A := A) he x.2)

/-- Helper for Lemma 15.105.19: an ideal generated by an idempotent element is flat because it is
a retract of the free rank-one module. -/
private lemma flat_span_singleton_of_isIdempotentElem (e : (j : J) → A j)
    (he : e * e = e) :
    Module.Flat ((j : J) → A j) (Ideal.span ({e} : Set ((j : J) → A j))) := by
  -- The inclusion splits by multiplication with `e`, so the ideal is a retract of a free module.
  let i := Submodule.subtype (Ideal.span ({e} : Set ((j : J) → A j)))
  let r := support_idempotent_retraction (A := A) e
  have hr : r.comp i = LinearMap.id := support_idempotent_retraction_comp_subtype (A := A) e he
  exact Module.Flat.of_retract i r hr

/-- Helper for Lemma 15.105.19: if `f = g * e`, then multiplying the ideal `(e)` by `g` has range
exactly the ideal `(f)`. -/
private lemma range_mul_subtype_span_singleton_eq_span_singleton
    (e g f : (j : J) → A j) (hfg : g * e = f) :
    LinearMap.range
        ((LinearMap.mulLeft ((j : J) → A j) g).comp
          (Submodule.subtype (Ideal.span ({e} : Set ((j : J) → A j)))) ) =
      Ideal.span ({f} : Set ((j : J) → A j)) := by
  ext y
  constructor
  · -- Any element in the range is a multiple of the generator `f = g * e`.
    rintro ⟨x, rfl⟩
    rcases Ideal.mem_span_singleton'.mp x.2 with ⟨a, ha⟩
    refine Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩
    calc
      a * f = a * (g * e) := by rw [← hfg]
      _ = g * (a * e) := by
        ext j
        simp [mul_left_comm, mul_comm]
      _ = g * (x : (j : J) → A j) := by rw [ha]
  · -- Conversely, any multiple of `f` comes from the corresponding multiple of `e`.
    intro hy
    rcases Ideal.mem_span_singleton'.mp hy with ⟨a, ha⟩
    refine ⟨⟨a * e, ?_⟩, ?_⟩
    · exact Ideal.mem_span_singleton'.mpr ⟨a, by simp [mul_comm]⟩
    · change g * ((a * e : (j : J) → A j)) = y
      calc
        g * (a * e) = a * (g * e) := by
          ext j
          simp [mul_left_comm, mul_comm]
        _ = a * f := by rw [hfg]
        _ = y := by rw [ha]

/-- Helper for Lemma 15.105.19: the original generator family factors as the support idempotent
times the componentwise nonzero factor. -/
private lemma support_generator_factor_mul_support_idempotent (f : (j : J) → A j) :
    (fun j ↦ if f j = 0 then (1 : A j) else f j) *
        (fun j ↦ if f j = 0 then 0 else 1) =
      f := by
  -- Pointwise, the factor is either `1 * 0` or `f j * 1`.
  funext j
  by_cases hf : f j = 0
  · simp [hf]
  · simp [hf]

/-- Helper for Lemma 15.105.19: the restricted multiplication map by the support factor has range
equal to the original principal ideal. -/
private lemma support_generator_restricted_mul_range (f : (j : J) → A j) :
    LinearMap.range
        (((LinearMap.mulLeft ((j : J) → A j) (fun j ↦ if f j = 0 then (1 : A j) else f j)).comp
          (Submodule.subtype
            (Ideal.span ({fun j ↦ if f j = 0 then 0 else 1} : Set ((j : J) → A j)))))) =
      Ideal.span ({f} : Set ((j : J) → A j)) := by
  -- This is the source proof's equality `(f) = g · (e)` rewritten in ideal-language.
  exact
    range_mul_subtype_span_singleton_eq_span_singleton (A := A)
      (fun j ↦ if f j = 0 then 0 else 1)
      (fun j ↦ if f j = 0 then (1 : A j) else f j)
      f
      (support_generator_factor_mul_support_idempotent (A := A) f)

/-- Helper for Lemma 15.105.19: the support idempotent attached to a family is idempotent. -/
private lemma support_idempotent_sq (f : (j : J) → A j) :
    (let e : (j : J) → A j := fun j ↦ if f j = 0 then 0 else 1; e * e = e) := by
  -- Pointwise, the support idempotent has only the values `0` and `1`.
  funext j
  by_cases hf : f j = 0
  · simp [hf]
  · simp [hf]

section

variable [∀ j, IsDomain (A j)]

/-- Helper for Lemma 15.105.19: componentwise nonvanishing makes multiplication injective on the
product ring. -/
private lemma mulLeft_injective_of_componentwise_nonzero (g : (j : J) → A j)
    (hg : ∀ j, g j ≠ 0) :
    Function.Injective (LinearMap.mulLeft ((j : J) → A j) g) := by
  -- Evaluate the equality in each coordinate and use that each factor is a domain.
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

/-- Helper for Lemma 15.105.19: the auxiliary factor in the support-idempotent decomposition is
componentwise nonzero. -/
private lemma support_generator_factor_ne_zero (f : (j : J) → A j) :
    ∀ j, (if f j = 0 then (1 : A j) else f j) ≠ 0 := by
  intro j
  by_cases hf : f j = 0
  · simpa [hf] using (one_ne_zero : (1 : A j) ≠ 0)
  · simpa [hf] using hf

/-- Helper for Lemma 15.105.19: restricting multiplication by the support factor to the
support-idempotent ideal is injective. -/
private lemma support_generator_restricted_mul_injective (f : (j : J) → A j) :
    Function.Injective
      (((LinearMap.mulLeft ((j : J) → A j) (fun j ↦ if f j = 0 then (1 : A j) else f j)).comp
        (Submodule.subtype
          (Ideal.span ({fun j ↦ if f j = 0 then 0 else 1} : Set ((j : J) → A j)))))) := by
  -- Injectivity reduces to the ambient product-ring multiplication map.
  intro x y hxy
  apply Subtype.ext
  exact
    mulLeft_injective_of_componentwise_nonzero (A := A)
      (fun j ↦ if f j = 0 then (1 : A j) else f j)
      (support_generator_factor_ne_zero (A := A) f) <| by
        simpa using hxy

/-- Helper for Lemma 15.105.19: the support idempotent associated to a generator family is
linearly equivalent to the original principal ideal. -/
private noncomputable def support_idempotent_span_linearEquiv_generator_span
    (f : (j : J) → A j) :
    let e : (j : J) → A j := fun j ↦ if f j = 0 then 0 else 1
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

end

variable [∀ j, IsDomain (A j)]
variable [∀ j, ValuationRing (A j)]

-- Proof sketch: apply Lemma `15.105.18` to the product ring `∏ j, A j`. A finitely generated ideal
-- in a product ring is the product of its component ideals by Proposition `10.89.2`, each component
-- ideal in a valuation ring is principal by Lemma `10.50.15`, and principal idempotent ideals are
-- direct summands, hence flat. This gives weak dimension at most `1`.
/-- Lemma 15.105.19 (1): the product of a family of valuation rings has weak dimension at most
`1`. -/
@[stacks 092T]
instance : HasWeakDimensionLE ((j : J) → A j) 1 := by
  -- Reduce weak dimension `≤ 1` to flatness of finitely generated ideals.
  refine
    ((weakDimensionLEOne_idealFlat_fgIdealFlat_submoduleFlat_localizations_valuationRing_tfae
      (A := ((j : J) → A j))).out 2 0).mp ?_
  intro I hI
  -- Rewrite the ideal as the product of its component ideals.
  let Icomp : (j : J) → Ideal (A j) := fun j ↦ Ideal.map (Pi.evalRingHom A j) I
  have hpi : I = Ideal.pi Icomp := fg_ideal_eq_pi_component_maps (A := A) I hI
  -- Each component ideal is principal because each factor is a valuation ring.
  letI : ∀ j, IsBezout (A j) := fun j ↦
    (ValuationRing.iff_local_bezout_domain (R := A j)).mp inferInstance |>.2
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
  -- Route correction: transport flatness along the canonical range equivalence from `(e)` to `(f)`.
  let e : (j : J) → A j := fun j ↦ if f j = 0 then 0 else 1
  have he : e * e = e := by
    simpa [e] using (support_idempotent_sq (A := A) f)
  letI : Module.Flat ((j : J) → A j) (Ideal.span ({e} : Set ((j : J) → A j))) :=
    flat_span_singleton_of_isIdempotentElem (A := A) e he
  have hflat_span_f :
      Module.Flat ((j : J) → A j) (Ideal.span ({f} : Set ((j : J) → A j))) := by
    -- The support-idempotent ideal and the original principal ideal are linearly equivalent.
    exact Module.Flat.of_linearEquiv
      ((support_idempotent_span_linearEquiv_generator_span (A := A) f).symm)
  rw [hI_span]
  exact hflat_span_f

variable {K : J → Type w}
variable [∀ j, CommRing (K j)] [∀ j, Algebra (A j) (K j)] [∀ j, IsFractionRing (A j) (K j)]

-- Proof sketch: for each factor `j`, `K j` is the localization of `A j` at the nonzerodivisors of
-- `A j`. The canonical product-localization `IsLocalization` instance then identifies the product
-- `∀ j, K j` as the localization of `∀ j, A j` at the product submonoid of componentwise
-- nonzerodivisors. The field structure on each fraction ring is derived from `IsFractionRing`, so
-- it does not belong in the public hypotheses for this direct localization recall.
/- Lemma 15.105.19 (2): if each `K j` is a fraction ring of `A j`, then the canonical map
`((j : J) → A j) → ((j : J) → K j)` is the localization at the product submonoid of componentwise
nonzerodivisors. This is direct instance inference from the canonical product-localization owner
in mathlib. -/
#synth IsLocalization (Submonoid.pi Set.univ fun j ↦ nonZeroDivisors (A j)) ((j : J) → K j)

end
