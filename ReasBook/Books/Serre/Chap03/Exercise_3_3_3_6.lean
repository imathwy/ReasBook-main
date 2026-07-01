import Mathlib
import Serre.Chap03.Definition_3_3_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

noncomputable section

section InducedFromCoinducedModel

variable {k : Type u} {G : Type v} [Semiring k] [Group G]
variable (H : Subgroup G)
variable {W : Type w} [AddCommMonoid W] [Module k W]
variable (θ : Representation k H W)

local instance : CoeFun (θ.coindV H.subtype) (fun _ ↦ G → W) where
  coe f := f.1

/-- The right-translation action of `H` preserves the property of being supported on `H`. -/
-- Proof sketch: if `u ∉ H` and `t ∈ H`, then also `u * t ∉ H`, so the translated function still
-- vanishes at `u`.
private theorem supportedOnSubgroup_apply_mem (t : H)
    {f : θ.coindV H.subtype}
    (hf : Function.support f ⊆ (H : Set G)) :
    Function.support (((θ.coind H.subtype).comp H.subtype) t f) ⊆ (H : Set G) :=
  by
  -- Rephrase support containment as pointwise vanishing away from `H`.
  rw [Function.support_subset_iff'] at hf ⊢
  intro u hu
  have hut : u * t ∉ H := by
    intro hut
    have hu' : u ∈ H := by
      have : (u * t) * t⁻¹ ∈ H := H.mul_mem hut (H.inv_mem t.2)
      simpa [mul_assoc] using this
    exact hu hu'
  simpa using hf (u * t) hut

/-- The `H`-subrepresentation `W₀ ⊆ V` of functions supported on `H`. -/
def supportedOnSubgroupSubrepresentation :
    Subrepresentation ((θ.coind H.subtype).comp H.subtype) where
  toSubmodule := {
    carrier := {f | Function.support f ⊆ (H : Set G)}
    zero_mem' := by
      simp
    add_mem' := fun hf hg ↦
      (Function.support_add _ _).trans <| Set.union_subset hf hg
    smul_mem' := fun a f hf ↦ by
      simpa using
        (Function.support_smul_subset_right (fun _ : G ↦ a) (f : G → W)).trans hf
  }
  apply_mem_toSubmodule := supportedOnSubgroup_apply_mem H θ

local notation "W₀" => supportedOnSubgroupSubrepresentation H θ

/-- Membership in the subgroup-supported subrepresentation is support containment in `H`. -/
theorem mem_supportedOnSubgroupSubrepresentation_iff
    (f : θ.coindV H.subtype) :
    f ∈ W₀ ↔ Function.support (f : G → W) ⊆ (H : Set G) :=
  Iff.rfl

/-- Membership in the subgroup-supported subrepresentation is vanishing away from `H`. -/
theorem mem_supportedOnSubgroupSubrepresentation_iff_forall_not_mem
    (f : θ.coindV H.subtype) :
    f ∈ W₀ ↔ ∀ u : G, u ∉ H → f u = 0 := by
  rw [mem_supportedOnSubgroupSubrepresentation_iff]
  simpa using (Function.support_subset_iff' :
    Function.support (f : G → W) ⊆ (H : Set G) ↔ ∀ u, u ∉ (H : Set G) → f u = 0)

/-- The underlying function of `f_w`, equal to `θ_u w` on `H` and `0` outside `H`. -/
private def subgroupSupportedFunctionFun (w : W) : G → W :=
  let _ : DecidablePred (fun u : G ↦ u ∈ H) := Classical.decPred _
  fun u ↦ if hu : u ∈ H then θ ⟨u, hu⟩ w else 0

/-- The function `f_w` lies in the canonical coinduced-function model `θ.coindV H.subtype`. -/
-- Proof sketch: split into whether the argument lies in `H`; on `H`, the covariance identity is
-- exactly the representation law for `θ`, and off `H` both sides are zero.
private theorem subgroupSupportedFunction_mem_coindV (w : W) :
    subgroupSupportedFunctionFun H θ w ∈ θ.coindV H.subtype :=
  by
  -- Check the coinduced covariance relation pointwise.
  rw [Representation.mem_coindV]
  intro t u
  by_cases hu : u ∈ H
  · -- On `H`, the defining formula reduces to the representation law for `θ`.
    have hmul : (t : G) * u ∈ H := H.mul_mem t.2 hu
    simpa only [subgroupSupportedFunctionFun, hu, hmul, Subgroup.subtype_apply] using
      LinearMap.congr_fun (θ.map_mul t ⟨u, hu⟩) w
  · -- Outside `H`, both sides vanish because left multiplication by `t ∈ H` preserves
    -- non-membership in the subgroup.
    have hmul : (t : G) * u ∉ H := by
      intro hmul
      apply hu
      have : ((t : G)⁻¹) * ((t : G) * u) ∈ H := H.mul_mem (H.inv_mem t.2) hmul
      simpa [mul_assoc] using this
    simpa only [subgroupSupportedFunctionFun, hu, hmul, Subgroup.subtype_apply] using
      (map_zero (θ t)).symm

/-- The element `f_w` of the canonical coinduced-function representation `θ.coind H.subtype`. -/
def subgroupSupportedFunction (w : W) : θ.coindV H.subtype :=
  ⟨subgroupSupportedFunctionFun H θ w,
    subgroupSupportedFunction_mem_coindV H θ w⟩

/-- On elements of `H`, the function `f_w` is given by the `H`-action on `w`. -/
-- Proof sketch: unfold `subgroupSupportedFunction` and evaluate the defining `if`.
theorem subgroupSupportedFunction_of_mem (w : W) {u : G} (hu : u ∈ H) :
    subgroupSupportedFunction H θ w u = θ ⟨u, hu⟩ w := by
  -- On `H` the defining `if` takes the representation branch.
  simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu]

/-- Outside `H`, the function `f_w` vanishes. -/
-- Proof sketch: unfold `subgroupSupportedFunction` and evaluate the defining `if`.
theorem subgroupSupportedFunction_of_not_mem (w : W) {u : G} (hu : u ∉ H) :
    subgroupSupportedFunction H θ w u = 0 := by
  -- Away from `H` the defining `if` forces the function to vanish.
  simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu]

/-- The function `f_w` belongs to the subgroup-supported subrepresentation `W₀`. -/
-- Proof sketch: this follows immediately from the defining formula for `f_w`.
theorem subgroupSupportedFunction_mem_supportedOnSubgroupSubrepresentation (w : W) :
    subgroupSupportedFunction H θ w ∈ W₀ := by
  -- The explicit formula for `f_w` vanishes on every point outside `H`.
  rw [mem_supportedOnSubgroupSubrepresentation_iff_forall_not_mem]
  intro u hu
  simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu]

/-- The map `w ↦ f_w` is additive. -/
-- Proof sketch: both sides are functions with the same pointwise values on and off `H`.
private theorem subgroupSupportedFunction_add (w₁ w₂ : W) :
    subgroupSupportedFunction H θ (w₁ + w₂) =
      subgroupSupportedFunction H θ w₁ + subgroupSupportedFunction H θ w₂ := by
  -- Compare the two coinduced functions pointwise on and off `H`.
  ext u
  by_cases hu : u ∈ H
  · simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu, map_add]
  · simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu]

/- The map `w ↦ f_w` is `k`-linear. -/
-- Proof sketch: compare pointwise values and use linearity of the representation maps `θ_u`.
private theorem subgroupSupportedFunction_smul (a : k) (w : W) :
    subgroupSupportedFunction H θ (a • w) =
      a • subgroupSupportedFunction H θ w := by
  -- Compare the two coinduced functions pointwise on and off `H`.
  ext u
  by_cases hu : u ∈ H
  · simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu, map_smul]
  · simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu]

/-- The linear map `w ↦ f_w` into the canonical coinduced-function model `θ.coindV H.subtype`. -/
private def subgroupSupportedFunctionLinearMap :
    W →ₗ[k] θ.coindV H.subtype where
  toFun := subgroupSupportedFunction H θ
  map_add' := subgroupSupportedFunction_add H θ
  map_smul' := subgroupSupportedFunction_smul H θ

/-- The map `w ↦ f_w` intertwines `θ` with the restricted coinduced action. -/
-- Proof sketch: compare the two subgroup-supported functions pointwise; on each `u ∈ G`, both
-- sides are the value of `f_w` translated by `t`, which is exactly the `H`-equivariance built into
-- the coinduced model.
private theorem subgroupSupportedFunction_isIntertwining
    (t : H) (w : W) :
    subgroupSupportedFunction H θ (θ t w) =
      ((θ.coind H.subtype).comp H.subtype) t (subgroupSupportedFunction H θ w) := by
  -- Compare the two functions pointwise.
  ext u
  by_cases hu : u ∈ H
  · -- On `H`, right translation stays inside `H`, so the two formulas differ only by the
    -- representation law for `θ`.
    have hmul : u * t ∈ H := H.mul_mem hu t.2
    simpa only [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu, hmul,
      MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, coind_apply,
      LinearMap.restrict_coe_apply, LinearMap.funLeft_apply] using
      (LinearMap.congr_fun (θ.map_mul ⟨u, hu⟩ t) w).symm
  · -- Off `H`, both sides vanish because right translation by `t ∈ H` cannot move the argument
    -- into `H`.
    have hmul : u * t ∉ H := by
      intro hmul
      apply hu
      have : (u * (t : G)) * (t : G)⁻¹ ∈ H := H.mul_mem hmul (H.inv_mem t.2)
      simpa [mul_assoc] using this
    simp [subgroupSupportedFunction, subgroupSupportedFunctionFun, hu, hmul,
      MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, coind_apply,
      LinearMap.restrict_coe_apply, LinearMap.funLeft_apply]

/-- The canonical `H`-equivariant map `w ↦ f_w` from `θ` into the subgroup-supported
subrepresentation `W₀`. -/
def supportedOnSubgroupHom :
    θ.IntertwiningMap (W₀).toRepresentation :=
  let f : W →ₗ[k] (W₀).toSubmodule :=
    (subgroupSupportedFunctionLinearMap H θ).codRestrict
      (W₀).toSubmodule
      (subgroupSupportedFunction_mem_supportedOnSubgroupSubrepresentation H θ)
  f.intertwiningMap_of_isIntertwiningMap θ (W₀).toRepresentation fun t w ↦
    Subtype.ext <| subgroupSupportedFunction_isIntertwining H θ t w

/-- The canonical intertwining map `w ↦ f_w` into `W₀` is the subgroup-supported function `f_w`.
-/
theorem supportedOnSubgroupHom_apply (w : W) :
    (supportedOnSubgroupHom H θ w : θ.coindV H.subtype) =
      subgroupSupportedFunction H θ w := by
  simp [supportedOnSubgroupHom, subgroupSupportedFunctionLinearMap]

/-- The map `w ↦ f_w` is a bijection from `W` onto `W₀`. -/
-- Proof sketch: injectivity is read off by evaluating at `1 ∈ H`; surjectivity reconstructs an
-- arbitrary function in `W₀` from its value at `1`, using covariance on `H` and vanishing away
-- from `H`.
private theorem supportedOnSubgroupHom_bijective :
    Function.Bijective (supportedOnSubgroupHom H θ) := by
  constructor
  · intro w₁ w₂ h
    -- Evaluate at `1` to recover the original vector in `W`.
    have hEval :
        subgroupSupportedFunction H θ w₁ 1 = subgroupSupportedFunction H θ w₂ 1 := by
      simpa [supportedOnSubgroupHom_apply] using
        congrArg (fun f : W₀ ↦ ((f : θ.coindV H.subtype) 1)) h
    have hEval' : θ ⟨1, H.one_mem⟩ w₁ = θ ⟨1, H.one_mem⟩ w₂ := by
      simpa [subgroupSupportedFunction, subgroupSupportedFunctionFun, H.one_mem] using hEval
    calc
      w₁ = θ ⟨1, H.one_mem⟩ w₁ := by
        symm
        exact LinearMap.congr_fun (θ.map_one) w₁
      _ = θ ⟨1, H.one_mem⟩ w₂ := hEval'
      _ = w₂ := by
        exact LinearMap.congr_fun (θ.map_one) w₂
  · intro f
    -- Reconstruct `f` from its value at `1`, using covariance on `H` and vanishing off `H`.
    refine ⟨(f : θ.coindV H.subtype) 1, ?_⟩
    apply Subtype.ext
    ext u
    by_cases hu : u ∈ H
    · have hcoind :
          (f : θ.coindV H.subtype) u =
            θ ⟨u, hu⟩ ((f : θ.coindV H.subtype) 1) := by
        simpa using (f : θ.coindV H.subtype).2 ⟨u, hu⟩ (1 : G)
      simpa [supportedOnSubgroupHom_apply, subgroupSupportedFunction_of_mem, hu] using
        hcoind.symm
    · have hf_zero :
          (f : θ.coindV H.subtype) u = 0 :=
        (mem_supportedOnSubgroupSubrepresentation_iff_forall_not_mem H θ
          (f : θ.coindV H.subtype)).mp f.2 u hu
      simpa [supportedOnSubgroupHom_apply, subgroupSupportedFunction_of_not_mem, hu] using
        hf_zero.symm

/-- Helper for Exercise 3-3.3-6: the quotient coordinate `QuotientGroup.mk u⁻¹` records exactly
when the right translate of `u` by `q.out` lands in `H`. -/
private theorem quotient_inv_eq_iff_mul_mem (q : G ⧸ H) (u : G) :
    ((QuotientGroup.mk u⁻¹ : G ⧸ H) = q) ↔ u * q.out ∈ H := by
  -- Rewrite equality in the quotient against the chosen representative `q.out`.
  rw [← Quotient.out_eq q, QuotientGroup.eq]
  simp

local instance quotientDecidableEq : DecidableEq (G ⧸ H) := Classical.decEq _

-- Route correction: use the inverse-quotient coordinate directly, since it is stable under the
-- left `H`-action appearing in `Representation.mem_coindV`.
/-- Helper for Exercise 3-3.3-6: the raw `q`-coset cutoff of a coinduced function still satisfies
the coinduced covariance relation. -/
private theorem cosetComponentFun_mem_coindV
    (q : G ⧸ H) (f : θ.coindV H.subtype) :
    (fun u : G ↦ if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q then f u else 0) ∈
      θ.coindV H.subtype := by
  -- The quotient coordinate `QuotientGroup.mk u⁻¹` is unchanged by left multiplication by `H`.
  rw [Representation.mem_coindV]
  intro t u
  have hleft :
      (QuotientGroup.mk (((t : G) * u)⁻¹) : G ⧸ H) = QuotientGroup.mk u⁻¹ := by
    rw [QuotientGroup.eq]
    simp
  by_cases huq : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q
  · have hmulq : (QuotientGroup.mk (((t : G) * u)⁻¹) : G ⧸ H) = q := hleft.trans huq
    simpa only [huq, hmulq, Subgroup.subtype_apply] using f.2 t u
  · have hmulq :
        (QuotientGroup.mk (((t : G) * u)⁻¹) : G ⧸ H) ≠ q := by
      intro hmulq
      exact huq (hleft.symm.trans hmulq)
    simpa only [huq, hmulq, Subgroup.subtype_apply] using (map_zero (θ t)).symm

/-- Helper for Exercise 3-3.3-6: the `q`-indexed coset component of a coinduced function, obtained
by keeping only the values whose inverse lies in the quotient class `q`. -/
private def cosetComponent (q : G ⧸ H) (f : θ.coindV H.subtype) : θ.coindV H.subtype :=
  ⟨fun u ↦ if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q then f u else 0,
    cosetComponentFun_mem_coindV H θ q f⟩

/-- Helper for Exercise 3-3.3-6: each quotient-indexed component already lies in the corresponding
translate of the subgroup-supported subrepresentation. -/
private theorem cosetComponent_mem_leftQuotientSubmodule
    (q : G ⧸ H) (f : θ.coindV H.subtype) :
    cosetComponent H θ q f ∈ (θ.coind H.subtype).leftQuotientSubmodule H W₀ q := by
  -- Translate the `q`-component back to the trivial coset, where it becomes subgroup-supported.
  rw [← Quotient.out_eq q, Representation.leftQuotientSubmodule_mk, Submodule.mem_map]
  let g : θ.coindV H.subtype := ((θ.coind H.subtype) q.out⁻¹) (cosetComponent H θ q f)
  have hg : g ∈ W₀ := by
    -- After translating by `q.out⁻¹`, a value can survive only on `H`.
    rw [mem_supportedOnSubgroupSubrepresentation_iff_forall_not_mem]
    intro u hu
    have huq :
        (QuotientGroup.mk ((u * q.out⁻¹)⁻¹) : G ⧸ H) ≠ q := by
      intro huq
      have : (u * q.out⁻¹) * q.out ∈ H :=
        (quotient_inv_eq_iff_mul_mem H q (u * q.out⁻¹)).mp huq
      exact hu (by simpa [mul_assoc] using this)
    dsimp [g]
    have hcut : (QuotientGroup.mk (q.out * u⁻¹) : G ⧸ H) ≠ q := by
      simpa using huq
    simp [coind_apply, cosetComponent, hcut]
  refine ⟨g, hg, ?_⟩
  -- Translating forward by `q.out` recovers the original `q`-component.
  subst g
  simpa using
    (LinearMap.congr_fun ((θ.coind H.subtype).map_mul q.out q.out⁻¹)
      (cosetComponent H θ q f)).symm

/-- Helper for Exercise 3-3.3-6: an element of the `q`-translate of `W₀` vanishes away from the
coset indexed by `q`. -/
private theorem leftQuotientSubmodule_apply_eq_zero_of_ne
    {q : G ⧸ H} {f : θ.coindV H.subtype}
    (hf : f ∈ (θ.coind H.subtype).leftQuotientSubmodule H W₀ q)
    {u : G} (hu : (QuotientGroup.mk u⁻¹ : G ⧸ H) ≠ q) : f u = 0 := by
  -- Unpack membership in the `q`-summand as a translate of a subgroup-supported function.
  rw [← Quotient.out_eq q, Representation.leftQuotientSubmodule_mk, Submodule.mem_map] at hf
  rcases hf with ⟨g, hg, rfl⟩
  have hug : u * q.out ∉ H := by
    intro hug
    exact hu ((quotient_inv_eq_iff_mul_mem H q u).2 hug)
  have hg_zero :
      g (u * q.out) = 0 :=
    (mem_supportedOnSubgroupSubrepresentation_iff_forall_not_mem H θ g).mp hg
      (u * q.out) hug
  simpa [coind_apply] using hg_zero

/-- Helper for Exercise 3-3.3-6: if a function is already supported on the `q`-coset, then its
`q`-component is the whole function. -/
private theorem cosetComponent_eq_of_mem
    {q : G ⧸ H} {f : θ.coindV H.subtype}
    (hf : f ∈ (θ.coind H.subtype).leftQuotientSubmodule H W₀ q) :
    cosetComponent H θ q f = f := by
  -- Evaluate pointwise: on the `q`-coset nothing changes, and away from it the function already
  -- vanishes.
  ext u
  by_cases huq : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q
  · show (if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q then f u else 0) = f u
    simp [huq]
  · have hf_zero : f u = 0 := leftQuotientSubmodule_apply_eq_zero_of_ne H θ hf huq
    show (if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q then f u else 0) = f u
    simp [huq, hf_zero]

/-- Helper for Exercise 3-3.3-6: if a function is supported on the `q`-coset, then every other
quotient component vanishes. -/
private theorem cosetComponent_eq_zero_of_mem_ne
    {q q' : G ⧸ H} (hqq' : q' ≠ q) {f : θ.coindV H.subtype}
    (hf : f ∈ (θ.coind H.subtype).leftQuotientSubmodule H W₀ q) :
    cosetComponent H θ q' f = 0 := by
  -- The `q'`-cutoff sees only points where the `q`-summand must already vanish.
  ext u
  by_cases huq' : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q'
  · have huq : (QuotientGroup.mk u⁻¹ : G ⧸ H) ≠ q := by
      intro huq
      exact hqq' (huq'.symm.trans huq)
    have hf_zero : f u = 0 := leftQuotientSubmodule_apply_eq_zero_of_ne H θ hf huq
    show (if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q' then f u else 0) = 0
    simp [huq', hf_zero]
  · show (if (QuotientGroup.mk u⁻¹ : G ⧸ H) = q' then f u else 0) = 0
    simp [huq']

/-- The canonical equivalence of `H`-representations identifying `θ` with the subgroup-supported
subrepresentation `W₀` via `w ↦ f_w`. -/
def supportedOnSubgroupEquiv :
    θ.Equiv (W₀).toRepresentation :=
  let f : θ.IntertwiningMap (W₀).toRepresentation :=
    supportedOnSubgroupHom H θ
  Representation.Equiv.mk
    (LinearEquiv.ofBijective f.toLinearMap (supportedOnSubgroupHom_bijective H θ))
    f.isIntertwining'

/-- The equivalence `θ ≃ W₀` sends `w` to the supported function `f_w`. -/
-- Proof sketch: unfold `supportedOnSubgroupEquiv`; it is the codomain-restricted map
-- `w ↦ f_w` viewed as an `H`-equivariant equivalence.
theorem supportedOnSubgroupEquiv_apply (w : W) :
    (supportedOnSubgroupEquiv H θ w : θ.coindV H.subtype) =
      subgroupSupportedFunction H θ w := by
  simpa [supportedOnSubgroupEquiv] using
    (supportedOnSubgroupHom_apply H θ w)

/-- Helper for Exercise 3-3.3-6: with finitely many cosets, a coinduced function is the sum of
its quotient-indexed cutoff pieces. -/
private theorem sum_cosetComponent_eq [Fintype (G ⧸ H)]
    (f : θ.coindV H.subtype) :
    (∑ q : G ⧸ H, cosetComponent H θ q f) = f := by
  -- At each point `u`, only the cutoff indexed by `QuotientGroup.mk u⁻¹` survives.
  ext u
  simp [cosetComponent]

/-- Helper for Exercise 3-3.3-6: the quotient-indexed translates of `W₀` span the coinduced
representation once the quotient `G ⧸ H` is finite. -/
private theorem leftQuotientSubmodule_iSup_eq_top_supportedOnSubgroup
    [Finite (G ⧸ H)] :
    iSup (fun q : G ⧸ H =>
      (θ.coind H.subtype).leftQuotientSubmodule H W₀ q) = ⊤ := by
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  -- Reconstruct an arbitrary coinduced function as the sum of its coset components.
  apply top_unique
  intro f _
  rw [← sum_cosetComponent_eq H θ f]
  exact Submodule.sum_mem _ fun q _ ↦
    Submodule.mem_iSup_of_mem q (cosetComponent_mem_leftQuotientSubmodule H θ q f)

/-- Helper for Exercise 3-3.3-6: any element of the supremum of the wrong quotient summands
vanishes on the chosen quotient block. -/
private theorem leftQuotientSubmodule_apply_eq_zero_of_mem_iSup_ne
    (q : G ⧸ H) {f : θ.coindV H.subtype}
    (hf : f ∈ ⨆ q' : G ⧸ H,
      ⨆ (_ : q' ≠ q), (θ.coind H.subtype).leftQuotientSubmodule H W₀ q')
    {u : G} (hu : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q) :
    f u = 0 := by
  -- Induct through the outer and inner suprema using the pointwise vanishing predicate.
  refine Submodule.iSup_induction
      (p := fun q' : G ⧸ H ↦
        ⨆ (_ : q' ≠ q), (θ.coind H.subtype).leftQuotientSubmodule H W₀ q')
      (motive := fun g : θ.coindV H.subtype ↦ g u = 0) hf ?_ ?_ ?_
  · intro q' g hg
    refine Submodule.iSup_induction
        (p := fun _ : q' ≠ q ↦ (θ.coind H.subtype).leftQuotientSubmodule H W₀ q')
        (motive := fun g : θ.coindV H.subtype ↦ g u = 0) hg ?_ ?_ ?_
    · intro hq' g hg'
      -- Each wrong summand already vanishes on the `q`-coset by the single-summand lemma.
      have huq' : (QuotientGroup.mk u⁻¹ : G ⧸ H) ≠ q' := by
        intro huq'
        exact hq' (huq'.symm.trans hu)
      exact leftQuotientSubmodule_apply_eq_zero_of_ne H θ hg' huq'
    · simp
    · intro g₁ g₂ hg₁ hg₂
      simp [hg₁, hg₂]
  · simp
  · intro g₁ g₂ hg₁ hg₂
    simp [hg₁, hg₂]

/-- Helper for Exercise 3-3.3-6: the `q`-component of an element supported on all other summands
is zero. -/
private theorem cosetComponent_eq_zero_of_mem_iSup_ne
    (q : G ⧸ H) {f : θ.coindV H.subtype}
    (hf : f ∈ ⨆ q' : G ⧸ H,
      ⨆ (_ : q' ≠ q), (θ.coind H.subtype).leftQuotientSubmodule H W₀ q') :
    cosetComponent H θ q f = 0 := by
  -- Evaluate pointwise: on the chosen coset use the vanishing lemma above, elsewhere the cutoff
  -- defining `cosetComponent` is already zero.
  ext u
  by_cases hu : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q
  · have hfu : f u = 0 :=
      leftQuotientSubmodule_apply_eq_zero_of_mem_iSup_ne H θ q hf hu
    simp [cosetComponent, hu, hfu]
  · simp [cosetComponent, hu]

/-- Helper for Exercise 3-3.3-6: the quotient-indexed translates of `W₀` are independent. -/
private theorem leftQuotientSubmodule_iSupIndep_supportedOnSubgroup :
    iSupIndep (fun q : G ⧸ H =>
      (θ.coind H.subtype).leftQuotientSubmodule H W₀ q) := by
  -- The cutoff `cosetComponent q` acts as the identity on the `q`-summand and kills the
  -- supremum of all other summands, so the intersection is trivial.
  rw [iSupIndep_def]
  intro q
  rw [Submodule.disjoint_def]
  intro x hxq hxrest
  have hself : cosetComponent H θ q x = x :=
    cosetComponent_eq_of_mem H θ hxq
  have hzero : cosetComponent H θ q x = 0 :=
    cosetComponent_eq_zero_of_mem_iSup_ne H θ q hxrest
  simpa [hself] using hzero

/-- Helper for Exercise 3-3.3-6: the quotient-indexed family of left translates of the
subgroup-supported subrepresentation. -/
private abbrev leftQuotientSubmoduleFamily :
    G ⧸ H → Submodule k (θ.coindV H.subtype) :=
  fun q => (θ.coind H.subtype).leftQuotientSubmodule H W₀ q

/-- Helper for Exercise 3-3.3-6: the direct-sum decomposition sends a coinduced function to its
family of quotient-indexed coset components. -/
private def leftQuotientSubmoduleDecompositionFun [Fintype (G ⧸ H)]
    (f : θ.coindV H.subtype) :
    DirectSum (G ⧸ H) fun q ↦ ↥(leftQuotientSubmoduleFamily H θ q) :=
  DirectSum.mk
    (fun q : G ⧸ H ↦ ↥(leftQuotientSubmoduleFamily H θ q))
    Finset.univ
    (fun q ↦ ⟨cosetComponent H θ q.1 f,
      cosetComponent_mem_leftQuotientSubmodule H θ q.1 f⟩)

/-- Helper for Exercise 3-3.3-6: each coordinate of the decomposition map is the corresponding
coset component. -/
private theorem leftQuotientSubmoduleDecompositionFun_apply [Fintype (G ⧸ H)]
    (f : θ.coindV H.subtype) (q : G ⧸ H) :
    leftQuotientSubmoduleDecompositionFun H θ f q =
      ⟨cosetComponent H θ q f,
        cosetComponent_mem_leftQuotientSubmodule H θ q f⟩ := by
  -- The direct-sum element is built from all coordinates on `Finset.univ`, so evaluation at `q`
  -- returns exactly the `q`-component.
  exact DirectSum.mk_apply_of_mem (β := fun q : G ⧸ H ↦ ↥(leftQuotientSubmoduleFamily H θ q))
    (s := Finset.univ)
    (f := fun q ↦ ⟨cosetComponent H θ q.1 f,
      cosetComponent_mem_leftQuotientSubmodule H θ q.1 f⟩)
    (hn := Finset.mem_univ q)

/-- Helper for Exercise 3-3.3-6: the decomposition map preserves zero. -/
private theorem leftQuotientSubmoduleDecompositionFun_zero [Fintype (G ⧸ H)] :
    leftQuotientSubmoduleDecompositionFun H θ (0 : θ.coindV H.subtype) = 0 := by
  -- Each quotient coordinate is the zero coset component.
  ext q u
  simp [leftQuotientSubmoduleDecompositionFun_apply, cosetComponent]

/-- Helper for Exercise 3-3.3-6: the decomposition map preserves addition. -/
private theorem leftQuotientSubmoduleDecompositionFun_add [Fintype (G ⧸ H)]
    (f g : θ.coindV H.subtype) :
    leftQuotientSubmoduleDecompositionFun H θ (f + g) =
      leftQuotientSubmoduleDecompositionFun H θ f +
        leftQuotientSubmoduleDecompositionFun H θ g := by
  -- Each quotient coordinate is cut out pointwise, so addition is coordinatewise.
  ext q u
  by_cases huq : (QuotientGroup.mk u⁻¹ : G ⧸ H) = q
  · simp [leftQuotientSubmoduleDecompositionFun_apply, cosetComponent, huq]
  · simp [leftQuotientSubmoduleDecompositionFun_apply, cosetComponent, huq]

/-- Helper for Exercise 3-3.3-6: the additive decomposition map into the quotient-indexed direct
sum of left translates of `W₀`. -/
private def leftQuotientSubmoduleDecomposition [Fintype (G ⧸ H)] :
    θ.coindV H.subtype →+
      DirectSum (G ⧸ H) fun q ↦ ↥(leftQuotientSubmoduleFamily H θ q) where
  toFun := leftQuotientSubmoduleDecompositionFun H θ
  map_zero' := leftQuotientSubmoduleDecompositionFun_zero H θ
  map_add' := leftQuotientSubmoduleDecompositionFun_add H θ

/-- Helper for Exercise 3-3.3-6: recomposing the quotient-indexed coset components recovers the
original coinduced function. -/
private theorem coeAddMonoidHom_comp_leftQuotientSubmoduleDecomposition
    [Fintype (G ⧸ H)] :
    (DirectSum.coeAddMonoidHom (leftQuotientSubmoduleFamily H θ)).comp
      (leftQuotientSubmoduleDecomposition H θ) =
      AddMonoidHom.id (θ.coindV H.subtype) := by
  classical
  -- Recomposition is the finite sum of the quotient-indexed cutoff pieces.
  apply DFunLike.ext
  intro f
  ext u
  change ((DirectSum.coeAddMonoidHom (leftQuotientSubmoduleFamily H θ))
      (leftQuotientSubmoduleDecomposition H θ f)) u = f u
  rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
  simpa [leftQuotientSubmoduleDecomposition, leftQuotientSubmoduleDecompositionFun,
    DirectSum.mk, cosetComponent] using
    congrArg (fun g : θ.coindV H.subtype => g u) (sum_cosetComponent_eq H θ f)

/-- Helper for Exercise 3-3.3-6: decomposing a pure direct-sum summand and then recomposing keeps
that summand unchanged, hence the decomposition map is also a left inverse. -/
private theorem leftQuotientSubmoduleDecomposition_comp_coeAddMonoidHom
    [Fintype (G ⧸ H)] :
    (leftQuotientSubmoduleDecomposition H θ).comp
      (DirectSum.coeAddMonoidHom (leftQuotientSubmoduleFamily H θ)) =
      AddMonoidHom.id
        (DirectSum (G ⧸ H) fun q ↦ ↥(leftQuotientSubmoduleFamily H θ q)) := by
  -- It suffices to check the identity on `0`, on pure generators, and then extend by additivity.
  apply DFunLike.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero =>
      simpa [AddMonoidHom.comp_apply, leftQuotientSubmoduleDecomposition]
        using leftQuotientSubmoduleDecompositionFun_zero H θ
  | of q x =>
      ext r u
      by_cases hr : r = q
      · subst hr
        have hself :
            cosetComponent H θ r (x : θ.coindV H.subtype) = (x : θ.coindV H.subtype) :=
          cosetComponent_eq_of_mem H θ x.property
        simp [AddMonoidHom.comp_apply, leftQuotientSubmoduleDecomposition,
          DirectSum.coeAddMonoidHom_of, leftQuotientSubmoduleDecompositionFun_apply, hself]
      · have hzero :
            cosetComponent H θ r (x : θ.coindV H.subtype) = 0 :=
          cosetComponent_eq_zero_of_mem_ne H θ hr x.property
        simp [AddMonoidHom.comp_apply, leftQuotientSubmoduleDecomposition,
          DirectSum.coeAddMonoidHom_of, DirectSum.of_eq_of_ne,
          leftQuotientSubmoduleDecompositionFun_apply, hr, hzero]
  | add x y hx hy =>
      rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, map_add, map_add]
      simpa using congrArg₂ HAdd.hAdd hx hy

/-- Exercise 3-3.3-6: the comparison between the given `H`-representation `θ` and the
subgroup-supported subrepresentation `W₀` is the canonical `H`-equivariant equivalence
`supportedOnSubgroupEquiv H θ : θ.Equiv W₀.toRepresentation`, whose underlying linear
equivalence is `(supportedOnSubgroupEquiv H θ).toLinearEquiv`. If `H` has finite index, then the
canonical coinduced-function representation `θ.coind H.subtype` is induced from the
subgroup-supported subrepresentation `W₀`. -/
-- Proof sketch: use the canonical finite-index comparison `Rep.indCoindIso` between
-- `Ind_H^G(W)` and `Coind_H^G(W)`, together with the trivial-coset generator
-- `IndV.mk H.subtype θ 1 : W →ₗ[k] Ind_H^G(W)`, then identify its image in the coinduced model
-- with `W₀`; the left-coset translates of `W₀` give the internal direct-sum decomposition of
-- `θ.coind H.subtype`.
theorem isInducedFrom_supportedOnSubgroupSubrepresentation [H.FiniteIndex] :
    (θ.coind H.subtype).IsInducedFromSubrepresentation H
      W₀ := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have hleft :
      (DirectSum.coeAddMonoidHom (leftQuotientSubmoduleFamily H θ)).comp
        (leftQuotientSubmoduleDecomposition H θ) =
        AddMonoidHom.id (θ.coindV H.subtype) := by
    exact coeAddMonoidHom_comp_leftQuotientSubmoduleDecomposition H θ
  have hright :
      (leftQuotientSubmoduleDecomposition H θ).comp
        (DirectSum.coeAddMonoidHom (leftQuotientSubmoduleFamily H θ)) =
        AddMonoidHom.id (DirectSum (G ⧸ H) fun q ↦ ↥(leftQuotientSubmoduleFamily H θ q)) := by
    exact leftQuotientSubmoduleDecomposition_comp_coeAddMonoidHom H θ
  let decomp : DirectSum.Decomposition (leftQuotientSubmoduleFamily H θ) :=
    DirectSum.Decomposition.ofAddHom (ℳ := leftQuotientSubmoduleFamily H θ)
      (leftQuotientSubmoduleDecomposition H θ)
      hleft
      hright
  letI : DirectSum.Decomposition (leftQuotientSubmoduleFamily H θ) := decomp
  -- Route correction: in the semiring setting, prove internality by exhibiting the explicit
  -- quotient-indexed decomposition map and its two-sided inverse property.
  change DirectSum.IsInternal (leftQuotientSubmoduleFamily H θ)
  exact DirectSum.Decomposition.isInternal (ℳ := leftQuotientSubmoduleFamily H θ)

end InducedFromCoinducedModel

end

end Representation
