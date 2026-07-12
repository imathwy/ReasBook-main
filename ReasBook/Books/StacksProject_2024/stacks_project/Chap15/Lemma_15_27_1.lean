import StacksProject_2024.Chap10.Lemma_10_82_13
import StacksProject_2024.Chap10.Lemma_10_82_10
import StacksProject_2024.Chap10.Lemma_10_51_3
import StacksProject_2024.Chap10.Lemma_10_91_3
import StacksProject_2024.Chap10.Lemma_10_96_4
import StacksProject_2024.Chap10.Lemma_10_96_11
import StacksProject_2024.Chap10.Lemma_10_97_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum
open AdicCompletion
open LinearMap

universe u v

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (A : Type v)

/- Domain triage:
- primary domain: adic completion functoriality and universal injectivity of linear maps;
- sampled owner declarations of the same kind:
  `mapToComplete` and `mapToComplete_comp_of` from the completion bridge API,
  `AdicCompletion.Families.pi` and `LinearEquiv.piCongrRight` for the canonical product
  comparison,
  the owner criterion `LinearMap.universallyInjective_iff_injective_mod_finite_ideal`,
  and the owner flatness theorem `Module.noetherian_pi_flat_and_mittagLeffler`;
- primitive data: the ideal `I`, the index type `A`, and the direct-sum inclusion
  `DirectSum.coeFnLinearMap R`;
- source/core/bridge triage:
  `source-facing`: the universally injective comparison map from the completed direct sum to the
  product `A → R`;
  `core/canonical`: the owner predicate `LinearMap.UniversallyInjective`;
  `bridge/view`: the canonical comparison is the composite of
  `AdicCompletion.map I (DirectSum.coeFnLinearMap R)`,
  `AdicCompletion.Families.pi I (fun _ : A ↦ R)`,
  and the pointwise completion equivalence
  `LinearEquiv.piCongrRight (fun _ : A ↦ (AdicCompletion.ofLinearEquiv I R).symm)`.
-/
variable [IsAdicComplete I R]

/-- The canonical map from the completed direct sum `AdicCompletion I (⨁ a, R)` to the product
`A → R`, obtained by functoriality of completion followed by the coordinatewise identification of
the completion of a product with the product of the completed coordinates. -/
noncomputable abbrev adicCompletionDirectSumToPi :
    AdicCompletion I (⨁ _ : A, R) →ₗ[R] A → R :=
  ((LinearEquiv.piCongrRight fun _ : A ↦ (ofLinearEquiv I R).symm).toLinearMap).comp
    (((AdicCompletion.pi I (fun _ : A ↦ R)).restrictScalars R).comp
      ((map I (DirectSum.coeFnLinearMap R)).restrictScalars R))

@[simp]
theorem adicCompletionDirectSumToPi_of (x : ⨁ _ : A, R) :
    adicCompletionDirectSumToPi I A (of I (⨁ _ : A, R) x) = DirectSum.coeFnLinearMap R x := by
  ext a
  change (ofLinearEquiv I R).symm
      (map I (LinearMap.proj a) ((map I (DirectSum.coeFnLinearMap R)) (of I (⨁ _ : A, R) x))) =
    x a
  rw [map_of, map_of, ofLinearEquiv_symm_of]
  rfl

@[simp]
theorem adicCompletionDirectSumToPi_comp_of :
    (adicCompletionDirectSumToPi I A).comp (of I (⨁ _ : A, R)) = DirectSum.coeFnLinearMap R := by
  ext x a
  rw [LinearMap.comp_apply, adicCompletionDirectSumToPi_of]

/-- Helper for Lemma 15.27.1: applying `AdicCompletion.of` to one coordinate of the product-side
comparison recovers the same coordinate viewed via completion functoriality. -/
private theorem of_coordinate_adicCompletionDirectSumToPi
    (xhat : AdicCompletion I (⨁ _ : A, R)) (a : A) :
    of I R ((adicCompletionDirectSumToPi I A xhat) a) =
      map I ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R)) xhat := by
  -- Compare the two maps as linear maps into the one-coordinate completion `AdicCompletion I R`.
  have hmap :
      (of I R).comp ((LinearMap.proj a).comp (adicCompletionDirectSumToPi I A)) =
        (map I ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))).restrictScalars R := by
    -- On each Cauchy representative and each stage, both maps reduce to the same quotient
    -- coordinate.
    apply AdicCompletion.map_ext''
    ext x n
    simp [adicCompletionDirectSumToPi, LinearMap.comp_apply, AdicCompletion.pi, LinearMap.pi_apply]
  exact LinearMap.congr_fun hmap xhat

/-- Helper for Lemma 15.27.1: the product-side completion comparison sends the canonical dense
image of a family back to that family. -/
@[simp]
private theorem pi_completionComparison_of (x : A → R) :
    (((LinearEquiv.piCongrRight fun _ : A ↦ (ofLinearEquiv I R).symm).toLinearMap).comp
      ((AdicCompletion.pi I (fun _ : A ↦ R)).restrictScalars R))
        (of I (A → R) x) = x := by
  -- Evaluate the completion comparison coordinatewise and use the defining property of `of`.
  ext a
  change (ofLinearEquiv I R).symm
      (map I (LinearMap.proj a) (of I (A → R) x)) = x a
  rw [map_of, ofLinearEquiv_symm_of]
  rfl

/-- Helper for Lemma 15.27.1: for a finite index type, the ordinary direct-sum inclusion into the
product is bijective. This is the finite-support endpoint needed by the planned reduction. -/
private theorem directSum_coeFn_bijective_of_fintype [Fintype A] :
    Function.Bijective (DirectSum.coeFnLinearMap R : (⨁ _ : A, R) →ₗ[R] (A → R)) := by
  -- On a finite index type, the canonical direct-sum/product comparison is a linear equivalence.
  simpa using
    (DirectSum.linearEquivFunOnFintype R A (fun _ : A ↦ R)).bijective

/-- Helper for Lemma 15.27.1: on a finite index type, the canonical direct-sum inclusion agrees
with the linear equivalence from the direct sum to the full product. -/
private theorem directSum_coeFn_eq_linearEquivFunOnFintype_toLinearMap [Fintype A] :
    (DirectSum.coeFnLinearMap R : (⨁ _ : A, R) →ₗ[R] (A → R)) =
      (DirectSum.linearEquivFunOnFintype R A (fun _ : A ↦ R)).toLinearMap := by
  -- Both maps simply read the coordinates of the finitely supported family.
  ext x a
  rfl

/-- Helper for Lemma 15.27.1: for a finite index type, the completed comparison is the canonical
composite of the completion of the finite direct-sum/product equivalence with the finite-product
completion equivalence. -/
private noncomputable def adicCompletionDirectSumToPi_linearEquiv_of_fintype
    [Fintype A] [DecidableEq A] :
    AdicCompletion I (⨁ _ : A, R) ≃ₗ[R] A → R :=
  LinearEquiv.trans
    (LinearEquiv.trans
      (LinearEquiv.restrictScalars R
        (AdicCompletion.congr I (DirectSum.linearEquivFunOnFintype R A (fun _ : A ↦ R))))
      (LinearEquiv.restrictScalars R
        (AdicCompletion.piEquivOfFintype I (fun _ : A ↦ R))))
    (LinearEquiv.piCongrRight fun _ : A ↦ (ofLinearEquiv I R).symm)

/-- Helper for Lemma 15.27.1: the finite completed comparison is injective because it is the
underlying map of a linear equivalence. -/
private theorem adicCompletionDirectSumToPi_linearEquiv_of_fintype_injective
    [Fintype A] [DecidableEq A] :
    Function.Injective
      (adicCompletionDirectSumToPi_linearEquiv_of_fintype
        (R := R) (I := I) (A := A)).toLinearMap :=
  -- The finite endpoint is now frozen as a genuine linear equivalence, so injectivity is formal.
  (adicCompletionDirectSumToPi_linearEquiv_of_fintype
    (R := R) (I := I) (A := A)).injective

/-- Helper for Lemma 15.27.1: after postcomposing with the coordinatewise identification
`AdicCompletion I R ≃ₗ[R] R`, the finite-product completion comparison is literally the same as the
raw coordinate map `AdicCompletion.pi`. -/
private theorem pi_completionComparison_eq_of_fintype
    [Fintype A] [DecidableEq A] :
    (((LinearEquiv.piCongrRight fun _ : A ↦ (ofLinearEquiv I R).symm).toLinearMap).comp
      ((AdicCompletion.pi I (fun _ : A ↦ R)).restrictScalars R)) =
      (((LinearEquiv.piCongrRight fun _ : A ↦ (ofLinearEquiv I R).symm).toLinearMap).comp
        ((LinearEquiv.restrictScalars R
          (AdicCompletion.piEquivOfFintype I (fun _ : A ↦ R))).toLinearMap)) := by
  -- The finite-product equivalence already agrees with `AdicCompletion.pi`, so after applying the
  -- coordinatewise completion equivalence there is no remaining transport to normalize.
  ext x a
  simp [LinearMap.comp_apply, AdicCompletion.piEquivOfFintype_apply]

/-- Helper for Lemma 15.27.1: on a finite index type, the canonical completed comparison is
literally the map underlying the finite-support linear equivalence. -/
private theorem adicCompletionDirectSumToPi_eq_linearEquiv_of_fintype
    [Fintype A] [DecidableEq A] :
    adicCompletionDirectSumToPi I A =
      (adicCompletionDirectSumToPi_linearEquiv_of_fintype
        (R := R) (I := I) (A := A)).toLinearMap := by
  -- Normalize the finite product leg first, then rewrite the direct-sum leg by the finite owner
  -- equivalence `DirectSum.linearEquivFunOnFintype`.
  ext x a
  rw [adicCompletionDirectSumToPi, adicCompletionDirectSumToPi_linearEquiv_of_fintype]
  simp only [LinearEquiv.trans_apply, LinearMap.comp_apply, AdicCompletion.congr_apply]
  rw [directSum_coeFn_eq_linearEquivFunOnFintype_toLinearMap (R := R) (A := A)]
  simpa using
    LinearMap.congr_fun
      (pi_completionComparison_eq_of_fintype (R := R) (I := I) (A := A))
      (((AdicCompletion.map I
        (DirectSum.linearEquivFunOnFintype R A (fun _ : A ↦ R)).toLinearMap).restrictScalars R) x) a

/-- Helper for Lemma 15.27.1: after reducing modulo an ideal `J`, the canonical map from the
completed direct sum agrees on `AdicCompletion.of` with the ordinary finitely supported inclusion
into the product quotient. -/
theorem adicCompletionDirectSumToPi_quotientMapByIdeal_apply_of (J : Ideal R) (x : ⨁ _ : A, R) :
    (adicCompletionDirectSumToPi I A).quotientMapByIdeal J
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ (of I (⨁ _ : A, R) x)) =
        ((J • (⊤ : Submodule R (A → R))).mkQ (DirectSum.coeFnLinearMap R x)) := by
  -- Reduce the completed comparison to the explicit computation on the dense image of `of`.
  simp [LinearMap.quotientMapByIdeal, adicCompletionDirectSumToPi_of]

/-- Helper for Lemma 15.27.1: a linear equivalence remains inverse to its inverse after reducing
modulo an ideal. -/
private theorem quotientMapByIdeal_comp_eq_id_of_linearEquiv
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (J : Ideal R) (e : M ≃ₗ[R] N) :
    ((e.symm.toLinearMap).quotientMapByIdeal J).comp ((e.toLinearMap).quotientMapByIdeal J) =
        LinearMap.id ∧
      ((e.toLinearMap).quotientMapByIdeal J).comp ((e.symm.toLinearMap).quotientMapByIdeal J) =
        LinearMap.id := by
  constructor
  · -- Check the left inverse identity on quotient representatives.
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R M)) x
    simp [LinearMap.quotientMapByIdeal]
  · -- The same computation gives the right inverse identity on the target quotient.
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R N)) x
    simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 15.27.1: quotient reduction commutes with composition. -/
private theorem quotientMapByIdeal_comp
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    (J : Ideal R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    (g.comp f).quotientMapByIdeal J =
      (g.quotientMapByIdeal J).comp (f.quotientMapByIdeal J) := by
  -- Compare both quotient maps on quotient representatives of the source.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R M)) x
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 15.27.1: for a finite index type, reducing the completed comparison modulo an
ideal stays injective because the comparison itself is a linear equivalence. -/
private theorem adicCompletionDirectSumToPi_quotient_injective_of_fintype
    [Fintype A] [DecidableEq A] (J : Ideal R) :
    Function.Injective ((adicCompletionDirectSumToPi I A).quotientMapByIdeal J) := by
  let e := adicCompletionDirectSumToPi_linearEquiv_of_fintype
    (R := R) (I := I) (A := A)
  have hquot :
      (adicCompletionDirectSumToPi I A).quotientMapByIdeal J =
        e.toLinearMap.quotientMapByIdeal J := by
    -- Rewrite the quotient map through the finite-type normalization.
    rw [adicCompletionDirectSumToPi_eq_linearEquiv_of_fintype (R := R) (I := I) (A := A)]
  have hleft :
      (e.symm.toLinearMap.quotientMapByIdeal J).comp (e.toLinearMap.quotientMapByIdeal J) =
        LinearMap.id := by
    -- The quotient of the inverse still acts as a left inverse because both quotient maps are
    -- computed on representatives.
    exact (quotientMapByIdeal_comp_eq_id_of_linearEquiv (R := R) J e).1
  rw [hquot]
  intro x y hxy
  have hxy' := congrArg (fun z ↦ (e.symm.toLinearMap.quotientMapByIdeal J) z) hxy
  calc
    x = (e.symm.toLinearMap.quotientMapByIdeal J) ((e.toLinearMap.quotientMapByIdeal J) x) := by
          simpa using (LinearMap.congr_fun hleft x).symm
    _ = (e.symm.toLinearMap.quotientMapByIdeal J) ((e.toLinearMap.quotientMapByIdeal J) y) := hxy'
    _ = y := by
          simpa using LinearMap.congr_fun hleft y

/-- Helper for Lemma 15.27.1: if a completion class maps to zero modulo `J`, then each product
coordinate of the comparison map already lies in `J`. This is the coordinatewise input needed for
the later Artin-Rees support-freezing step. -/
private theorem coordinate_mem_ideal_of_kernel
    (J : Ideal R) {xhat : AdicCompletion I (⨁ _ : A, R)}
    (hker : (adicCompletionDirectSumToPi I A).quotientMapByIdeal J
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) = 0)
    (a : A) :
    (adicCompletionDirectSumToPi I A xhat) a ∈ J := by
  -- Rewrite the kernel condition as membership of the ambient product family in `J • ⊤`.
  have hclass :
      (J • (⊤ : Submodule R (A → R))).mkQ (adicCompletionDirectSumToPi I A xhat) =
        (J • (⊤ : Submodule R (A → R))).mkQ 0 := by
    simpa [LinearMap.quotientMapByIdeal] using hker
  have hmem :
      adicCompletionDirectSumToPi I A xhat ∈ J • (⊤ : Submodule R (A → R)) := by
    simpa using (Submodule.Quotient.eq (J • (⊤ : Submodule R (A → R)))).1 hclass
  -- Project to the chosen coordinate and identify `J • ⊤ ⊆ R` with the ideal `J`.
  have hcoord :
      (adicCompletionDirectSumToPi I A xhat) a ∈ (J • (⊤ : Submodule R R) : Submodule R R) := by
    have hcomap :
        adicCompletionDirectSumToPi I A xhat ∈
          Submodule.comap (LinearMap.proj a) (J • (⊤ : Submodule R R)) :=
      (Submodule.smul_top_le_comap_smul_top J (LinearMap.proj a)) hmem
    simpa [Submodule.mem_comap] using hcomap
  -- Unpack the scalar submodule `J • ⊤` directly on `R`.
  refine Submodule.smul_induction_on hcoord ?_ ?_
  · intro r hr y hy
    simpa using Ideal.mul_mem_right y J hr
  · intro y z hy hz
    exact J.add_mem hy hz

section FinsetSupport

variable [DecidableEq A]

/-- Helper for Lemma 15.27.1: the finite-support direct sum on `↥S` includes into the ambient
direct sum on `A` by sending each basis vector to the corresponding ambient basis vector. -/
private noncomputable def finsetSupportInclusion (S : Finset A) :
    (⨁ _ : ↥S, R) →ₗ[R] (⨁ _ : A, R) :=
  DirectSum.toModule R (↥S) (⨁ _ : A, R) fun s ↦
    DirectSum.lof R A (fun _ : A ↦ R) s.1

/-- Helper for Lemma 15.27.1: restricting product coordinates from `A` to a finite carrier `S`.
This is the product-side map in the finite-support factorization square. -/
private noncomputable def restrictCoordinates (S : Finset A) :
    (A → R) →ₗ[R] (↥S → R) :=
  LinearMap.pi fun s : ↥S ↦ LinearMap.proj s.1

/-- Helper for Lemma 15.27.1: the support inclusion sends a basis vector on `↥S` to the matching
ambient basis vector on `A`. -/
@[simp] private theorem finsetSupportInclusion_lof (S : Finset A) (s : ↥S) (r : R) :
    finsetSupportInclusion (R := R) (A := A) S
        (DirectSum.lof R (↥S) (fun _ : ↥S ↦ R) s r) =
      DirectSum.lof R A (fun _ : A ↦ R) s.1 r := by
  -- Expand the direct-sum map on a basis vector through `DirectSum.toModule`.
  simp [finsetSupportInclusion]

/-- Helper for Lemma 15.27.1: the coordinate restriction map simply evaluates the ambient family
at the underlying index of a point of `↥S`. -/
@[simp] private theorem restrictCoordinates_apply (S : Finset A) (f : A → R) (s : ↥S) :
    restrictCoordinates (R := R) (A := A) S f s = f s.1 := by
  -- The `LinearMap.pi` description makes the restriction formula immediate.
  simp [restrictCoordinates, LinearMap.pi_apply]

/-- Helper for Lemma 15.27.1: before completing, finite-support inclusion on the direct-sum side
and coordinate restriction on the product side commute with the canonical direct-sum comparison. -/
private theorem restrictCoordinates_comp_directSum_coeFn_finset_support (S : Finset A) :
    (((restrictCoordinates (R := R) (A := A) S).comp
        (DirectSum.coeFnLinearMap R : (⨁ _ : A, R) →ₗ[R] (A → R))).comp
      (finsetSupportInclusion (R := R) (A := A) S)) =
        (DirectSum.coeFnLinearMap R : (⨁ _ : ↥S, R) →ₗ[R] (↥S → R)) := by
  -- Check the square on basis vectors of the finite direct sum and then evaluate coordinates.
  ext s r
  have hs :
      finsetSupportInclusion (R := R) (A := A) S
          ((DirectSum.of (fun _ : ↥S ↦ R) s) (1 : R)) =
        (DirectSum.of (fun _ : A ↦ R) s.1) (1 : R) := by
    -- The support inclusion preserves the chosen basis vector.
    simpa [DirectSum.lof_eq_of] using
      finsetSupportInclusion_lof (R := R) (A := A) S s (1 : R)
  by_cases h : r = s
  · -- On the distinguished coordinate, both sides return the chosen coefficient.
    subst h
    simp [LinearMap.comp_apply, hs, DirectSum.lof_eq_of, DirectSum.of_eq_same]
  · -- Off the distinguished coordinate, both sides vanish by the direct-sum basis rules.
    have h' : (r : A) ≠ s := fun hrs ↦ h (Subtype.ext hrs)
    simp [LinearMap.comp_apply, hs, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, h, h']

/-- Helper for Lemma 15.27.1: on indices inside `S`, the finite-support inclusion reads back the
original coordinate. -/
@[simp] private theorem finsetSupportInclusion_apply_of_mem
    (S : Finset A) (x : ⨁ _ : ↥S, R) {a : A} (ha : a ∈ S) :
    finsetSupportInclusion (R := R) (A := A) S x a = x ⟨a, ha⟩ := by
  -- Restrict the ambient coordinate map back to `↥S` and use the commuting square.
  let s : ↥S := ⟨a, ha⟩
  have hsquare :=
    congrFun
      (LinearMap.congr_fun
        (restrictCoordinates_comp_directSum_coeFn_finset_support (R := R) (A := A) S)
        x)
      s
  simpa [restrictCoordinates_apply, LinearMap.comp_apply, s] using hsquare

/-- Helper for Lemma 15.27.1: on indices outside `S`, the finite-support inclusion vanishes. -/
@[simp] private theorem finsetSupportInclusion_apply_of_not_mem
    (S : Finset A) (x : ⨁ _ : ↥S, R) {a : A} (ha : a ∉ S) :
    finsetSupportInclusion (R := R) (A := A) S x a = 0 := by
  -- Follow the direct-sum induction: the ambient coordinate vanishes on zero, on one basis vector,
  -- and is preserved by addition.
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp
  · intro s r
    -- A basis vector supported at `s : ↥S` has zero `a`-coordinate because `a ∉ S`.
    have hne : a ≠ s.1 := fun hmem ↦ ha (hmem ▸ s.2)
    rw [finsetSupportInclusion_lof]
    simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hne]
  · intro y z hy hz
    -- Additivity of the inclusion reduces the coordinate computation to the induction hypotheses.
    simp [map_add, hy, hz]

/-- Helper for Lemma 15.27.1: after completing the finite-support inclusion, restricting ambient
coordinates agrees with the canonical completed comparison on the finite carrier `↥S`. -/
private theorem restrictCoordinates_comp_adicCompletionDirectSumToPi_finset_support
    (S : Finset A) :
    (((restrictCoordinates (R := R) (A := A) S).comp (adicCompletionDirectSumToPi I A)).comp
      ((AdicCompletion.map I (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R)) =
        adicCompletionDirectSumToPi I (↥S) := by
  -- Compare the two completed maps on arbitrary Cauchy-sequence representatives.
  apply AdicCompletion.map_ext''
  ext x s
  -- Compare the chosen coordinate in the completed product stage by stage.
  apply (ofLinearEquiv I R).injective
  apply AdicCompletion.ext_evalₐ
  intro n
  -- Each stage is the quotient of the corresponding coordinate of the finite-support square.
  have hstage :
      ((DirectSum.coeFnLinearMap R : (⨁ _ : A, R) →ₗ[R] A → R)
          (finsetSupportInclusion (R := R) (A := A) S (x n))) s.1 =
        ((DirectSum.coeFnLinearMap R : (⨁ _ : ↥S, R) →ₗ[R] ↥S → R) (x n)) s := by
    have hsquare :=
      congrFun
        (LinearMap.congr_fun
          (restrictCoordinates_comp_directSum_coeFn_finset_support (R := R) (A := A) S)
          (x n))
        s
    simpa [restrictCoordinates_apply, LinearMap.comp_apply] using hsquare
  simpa [adicCompletionDirectSumToPi, AdicCompletion.pi, LinearMap.comp_apply,
    AdicCompletion.map_mk, AdicCompletion.evalₐ_mk] using
    congrArg (Ideal.Quotient.mk (I ^ n)) hstage

end FinsetSupport

variable [IsNoetherianRing R]

/-- Helper for Lemma 15.27.1: Artin-Rees for the inclusion `J ↪ R`, rewritten as a stabilized
intersection formula inside the scalar module `R`. -/
private theorem ideal_intersection_pow_smul_eventually_eq (J : Ideal R) :
    ∃ c : ℕ, ∀ n ≥ c,
      ((J : Submodule R R) ⊓ (I ^ n : Ideal R)) =
        I ^ (n - c) • (((J : Submodule R R) ⊓ (I ^ c : Ideal R))) := by
  obtain ⟨c, hc⟩ := Ideal.exists_exact_preimage_pow_smul_eq (R := R) (I := I)
    ((J : Submodule R R).subtype)
  refine ⟨c, ?_⟩
  intro n hn
  have hker : LinearMap.ker ((J : Submodule R R).subtype : J →ₗ[R] R) = ⊥ := by
    ext x
    simp
  have hmap_comap_n :
      Submodule.map ((J : Submodule R R).subtype : J →ₗ[R] R)
          (Submodule.comap ((J : Submodule R R).subtype : J →ₗ[R] R) (I ^ n : Ideal R)) =
        ((J : Submodule R R) ⊓ (I ^ n : Ideal R)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hmap_comap_c :
      Submodule.map ((J : Submodule R R).subtype : J →ₗ[R] R)
          (Submodule.comap ((J : Submodule R R).subtype : J →ₗ[R] R) (I ^ c : Ideal R)) =
        ((J : Submodule R R) ⊓ (I ^ c : Ideal R)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hcore :
      Submodule.map ((J : Submodule R R).subtype : J →ₗ[R] R)
          (Submodule.comap ((J : Submodule R R).subtype : J →ₗ[R] R) (I ^ n : Ideal R)) =
        Submodule.map ((J : Submodule R R).subtype : J →ₗ[R] R)
          (I ^ (n - c) •
            Submodule.comap ((J : Submodule R R).subtype : J →ₗ[R] R) (I ^ c : Ideal R)) := by
    -- Collapse the zero-kernel Artin-Rees equality before pushing it into `R`.
    exact congrArg (Submodule.map ((J : Submodule R R).subtype : J →ₗ[R] R)) <|
      by simpa [hker] using hc n hn
  -- After mapping back into `R`, the preimage equality becomes the desired equality of
  -- intersections inside `R`.
  simpa [hmap_comap_n, hmap_comap_c, Submodule.map_smul''] using hcore

/-- Helper for Lemma 15.27.1: the same Artin-Rees equality evaluated on the shifted stages
`c + n`, which is the form needed to choose the finite support carrier at one fixed stage. -/
private theorem ideal_intersection_pow_smul_shift_eq (J : Ideal R) :
    ∃ c : ℕ, ∀ n : ℕ,
      ((J : Submodule R R) ⊓ (I ^ (c + n) : Ideal R)) =
        I ^ n • (((J : Submodule R R) ⊓ (I ^ c : Ideal R))) := by
  obtain ⟨c, hc⟩ := ideal_intersection_pow_smul_eventually_eq (R := R) (I := I) J
  refine ⟨c, ?_⟩
  intro n
  -- This is the source-faithful Artin-Rees equality specialized to the shifted stage `c + n`.
  simpa [Nat.add_sub_cancel_left] using hc (c + n) (Nat.le_add_right c n)

/-- Helper for Lemma 15.27.1: in the scalar module `R`, belonging to `J • ⊤` is equivalent to
belonging to the ideal `J` itself. -/
private theorem mem_smul_top_iff_mem_ideal (J : Ideal R) (x : R) :
    x ∈ (J • (⊤ : Submodule R R) : Submodule R R) ↔ x ∈ J := by
  constructor
  · intro hx
    -- Unpack the submodule smul as a finite sum of scalar multiples coming from `J`.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      simpa using Ideal.mul_mem_right y J hr
    · intro y z hy hz
      exact J.add_mem hy hz
  · intro hx
    -- The reverse direction is the single-generator witness `x • 1`.
    simpa using
      (Submodule.smul_mem_smul (I := J) (N := (⊤ : Submodule R R)) hx (by simp) :
        x • (1 : R) ∈ J • (⊤ : Submodule R R))

/-- Helper for Lemma 15.27.1: a finitely supported family lies in `J • ⊤` once every coordinate
lies in the ideal `J`. -/
private theorem directSum_mem_smul_top_of_coordinate_mem (J : Ideal R) (x : ⨁ _ : A, R)
    (hx : ∀ a, x a ∈ J) :
    x ∈ J • (⊤ : Submodule R (⨁ _ : A, R)) := by
  classical
  have hdecomp :
      x = x.sum fun a r ↦ (DirectSum.of (fun _ => R) a) r := by
    -- Expand the finitely supported family as the sum of its coordinate basis vectors.
    exact (DFinsupp.sum_single (f := x)).symm
  rw [hdecomp]
  change x.support.sum (fun a ↦ (DirectSum.of (fun _ => R) a) (x a)) ∈
    J • (⊤ : Submodule R (⨁ _ : A, R))
  -- Each summand is the coordinate value times the corresponding basis vector.
  refine Submodule.sum_mem _ ?_
  intro a ha
  have hlof :
      DirectSum.lof R A (fun _ => R) a (x a) =
        x a • DirectSum.lof R A (fun _ => R) a (1 : R) := by
    calc
      DirectSum.lof R A (fun _ => R) a (x a) =
          DirectSum.lof R A (fun _ => R) a (x a • (1 : R)) := by
            simp
      _ = x a • DirectSum.lof R A (fun _ => R) a (1 : R) := by
            rw [LinearMap.map_smul]
  have hsmul :
      x a • DirectSum.lof R A (fun _ => R) a (1 : R) ∈
        J • (⊤ : Submodule R (⨁ _ : A, R)) :=
    Submodule.smul_mem_smul (I := J) (N := (⊤ : Submodule R (⨁ _ : A, R))) (hx a) (by simp)
  have hsingle :
      (DirectSum.of (fun _ => R) a) (x a) =
        x a • DirectSum.lof R A (fun _ => R) a (1 : R) := by
    simpa [DirectSum.lof_eq_of] using hlof
  rw [hsingle]
  exact hsmul

/-- Helper for Lemma 15.27.1: once a finitely generated ideal `J` is presented by generators
`j : Fin m → R`, every element of `J • ⊤` can be written as a finite sum `∑ i, j i • u i`. -/
private theorem generator_sum_representation_of_mem_smul_top
    {M : Type*} [AddCommGroup M] [Module R M]
    (J : Ideal R) {m : ℕ} (j : Fin m → R)
    (hspan : Ideal.span (Set.range j) = J)
    {x : M} (hx : x ∈ J • (⊤ : Submodule R M)) :
    ∃ u : Fin m → M, x = ∑ i, j i • u i := by
  -- Decompose `x ∈ J • ⊤` by submodule-smul induction, lifting each scalar generator of `J`
  -- through the chosen finite family `j`.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    have hrange : r ∈ Ideal.span (Set.range j) := by
      simpa [hspan] using hr
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hrange
    refine ⟨fun i ↦ c i • y, ?_⟩
    calc
      r • y = (∑ i, j i * c i) • y := by rw [hc]
      _ = ∑ i, (j i * c i) • y := by rw [Finset.sum_smul]
      _ = ∑ i, j i • (c i • y) := by
            congr with i
            rw [smul_smul, mul_comm]
  · intro y z hy hz
    rcases hy with ⟨uy, rfl⟩
    rcases hz with ⟨uz, rfl⟩
    refine ⟨fun i ↦ uy i + uz i, ?_⟩
    simp [smul_add, Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc]

/-- Helper for Lemma 15.27.1: an explicit sum of the chosen generators of `J` already lies in
`J • ⊤`. This is the easy source-side half of the later reconstruction argument. -/
private theorem generator_sum_mem_smul_top
    {M : Type*} [AddCommGroup M] [Module R M]
    (J : Ideal R) {m : ℕ} (j : Fin m → R)
    (hj : ∀ i, j i ∈ J) (u : Fin m → M) :
    (∑ i, j i • u i) ∈ J • (⊤ : Submodule R M) := by
  -- Each generator term is visibly in `J • ⊤`, so the whole finite sum stays there.
  refine Submodule.sum_mem _ ?_
  intro i hi
  exact Submodule.smul_mem_smul (I := J) (N := (⊤ : Submodule R M)) (hj i) (by simp)

/-- Helper for Lemma 15.27.1: the scalar generator map attached to a finite family
`j : Fin m → R`. -/
private noncomputable abbrev generatorLinearMap {m : ℕ} (j : Fin m → R) :
    (Fin m → R) →ₗ[R] R :=
  ∑ i, (j i) • LinearMap.proj i

/-- Helper for Lemma 15.27.1: the scalar generator map evaluates as the expected finite linear
combination of the chosen generators. -/
@[simp] private theorem generatorLinearMap_apply {m : ℕ} (j : Fin m → R) (v : Fin m → R) :
    generatorLinearMap (R := R) j v = ∑ i, j i * v i := by
  -- Expand the finite sum of coordinate projections and simplify each summand.
  simp [generatorLinearMap, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 15.27.1: if a finitely supported family lies in `J • ⊤`, then each
coordinate lies in `J`. -/
private theorem coordinate_mem_ideal_of_mem_smul_top
    (J : Ideal R) {x : ⨁ _ : A, R}
    (hx : x ∈ J • (⊤ : Submodule R (⨁ _ : A, R))) (a : A) :
    x a ∈ J := by
  -- Project the ambient `J • ⊤` membership to the chosen coordinate and rewrite it inside `R`.
  have hproj :
      x ∈ Submodule.comap ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))
        (J • (⊤ : Submodule R R)) :=
    (Submodule.smul_top_le_comap_smul_top J
      ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))) hx
  have hxcoord : x a ∈ (J • (⊤ : Submodule R R) : Submodule R R) := by
    simpa [Submodule.mem_comap, LinearMap.comp_apply] using hproj
  exact (mem_smul_top_iff_mem_ideal (R := R) J (x a)).1 hxcoord

/-- Helper for Lemma 15.27.1: projecting a function-valued `I^n • ⊤` witness to one coordinate
keeps that coordinate inside `I ^ n`. -/
private theorem coordinate_mem_pow_of_function_mem_smul_top
    {m : ℕ} {n : ℕ} {v : Fin m → R}
    (hv : v ∈ I ^ n • (⊤ : Submodule R (Fin m → R))) (i : Fin m) :
    v i ∈ I ^ n := by
  -- Coordinate projection of the function module preserves the standard power submodules.
  have hproj :
      v ∈ Submodule.comap (LinearMap.proj i) (I ^ n • (⊤ : Submodule R R)) :=
    (Submodule.smul_top_le_comap_smul_top (I ^ n) (LinearMap.proj i)) hv
  have hcoord : v i ∈ (I ^ n • (⊤ : Submodule R R) : Submodule R R) := by
    simpa [Submodule.mem_comap] using hproj
  exact (mem_smul_top_iff_mem_ideal (R := R) (I ^ n) (v i)).1 hcoord

/-- Helper for Lemma 15.27.1: a deep difference lying in `J • ⊤` can be lifted through a finite
set of generators of `J` with coefficients already inside the prescribed power `I ^ n`. -/
private theorem deep_generator_difference_lift
    (J : Ideal R) {m : ℕ} (j : Fin m → R)
    (hspan : Ideal.span (Set.range j) = J)
    (b n : ℕ)
    (hσ : (generatorLinearMap (R := R) j).IsArtinReesBound I b)
    {d : ⨁ _ : A, R}
    (hdJ : d ∈ J • (⊤ : Submodule R (⨁ _ : A, R)))
    (hdI : d ∈ I ^ (b + n) • (⊤ : Submodule R (⨁ _ : A, R))) :
    ∃ Δ : Fin m → (⨁ _ : A, R),
      d = ∑ i, j i • Δ i ∧
      ∀ i, Δ i ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
  classical
  let σ : (Fin m → R) →ₗ[R] R := generatorLinearMap (R := R) j
  have hcoeff :
      ∀ a : A, ∃ v : Fin m → R, σ v = d a ∧ v ∈ I ^ n • (⊤ : Submodule R (Fin m → R)) := by
    intro a
    -- Use the coordinatewise Artin-Rees bound for the scalar generator map `σ`.
    have haJ : d a ∈ J :=
      coordinate_mem_ideal_of_mem_smul_top (R := R) (A := A) J hdJ a
    have haRange : d a ∈ LinearMap.range σ := by
      have haSpan : d a ∈ Ideal.span (Set.range j) := by
        simpa [hspan] using haJ
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp haSpan
      refine ⟨c, ?_⟩
      simpa [σ] using hc.symm
    have haPow : d a ∈ I ^ (b + n) := by
      have hproj :
          d ∈ Submodule.comap ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))
            (I ^ (b + n) • (⊤ : Submodule R R)) :=
        (Submodule.smul_top_le_comap_smul_top (I ^ (b + n))
          ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))) hdI
      have hcoord : d a ∈ (I ^ (b + n) • (⊤ : Submodule R R) : Submodule R R) := by
        simpa [Submodule.mem_comap, LinearMap.comp_apply] using hproj
      exact (mem_smul_top_iff_mem_ideal (R := R) (I ^ (b + n)) (d a)).1 hcoord
    have haInf :
        d a ∈ LinearMap.range σ ⊓ I ^ (b + n) • (⊤ : Submodule R R) := by
      rw [Submodule.mem_inf]
      refine ⟨haRange, ?_⟩
      exact (mem_smul_top_iff_mem_ideal (R := R) (I ^ (b + n)) (d a)).2 haPow
    have haMap :
        d a ∈ Submodule.map σ (I ^ n • (⊤ : Submodule R (Fin m → R))) := by
      simpa [show b + n - b = n by omega] using hσ (b + n) (by omega) haInf
    rcases Submodule.mem_map.mp haMap with ⟨v, hv, hv_eq⟩
    exact ⟨v, hv_eq, hv⟩
  choose coeff hcoeff_eq hcoeff_mem using hcoeff
  let Δ : Fin m → (⨁ _ : A, R) := fun i ↦
    d.support.sum fun a ↦ DirectSum.lof R A (fun _ : A ↦ R) a (coeff a i)
  have hΔ_apply :
      ∀ i : Fin m, ∀ a : A, (Δ i) a = if a ∈ d.support then coeff a i else 0 := by
    intro i a
    by_cases ha : a ∈ d.support
    · -- On the support, only the `a`-summand survives in the coordinate expansion.
      rw [show Δ i =
        d.support.sum fun x ↦ DirectSum.lof R A (fun _ : A ↦ R) x (coeff x i) by rfl]
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single a]
      · simp [DirectSum.lof_eq_of, ha]
      · intro x hx hxa
        simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hxa]
      · exact False.elim (ha ‹a ∉ d.support›)
    · -- Off the support, every basis summand has the wrong coordinate.
      rw [show Δ i =
        d.support.sum fun x ↦ DirectSum.lof R A (fun _ : A ↦ R) x (coeff x i) by rfl]
      rw [Finset.sum_apply]
      simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, ha]
  have hΔmem :
      ∀ i : Fin m, Δ i ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
    intro i
    -- The coordinatewise Artin-Rees lifts already land in `I ^ n`, so the bundled direct-sum
    -- element does too.
    apply directSum_mem_smul_top_of_coordinate_mem (R := R) (A := A) (J := I ^ n)
    intro a
    by_cases ha : a ∈ d.support
    · have hcoord :
          coeff a i ∈ I ^ n :=
        coordinate_mem_pow_of_function_mem_smul_top
          (R := R) (I := I) (hcoeff_mem a) i
      simpa [hΔ_apply i a, ha] using hcoord
    · simpa [hΔ_apply i a, ha]
  refine ⟨Δ, ?_, hΔmem⟩
  -- Compare both sides coordinatewise; on each coordinate, the chosen Artin-Rees lift recovers
  -- `d a` exactly.
  ext a
  by_cases ha : a ∈ d.support
  · calc
      (∑ i, j i • Δ i) a = ∑ i, j i * (Δ i a) := by
            simp [smul_eq_mul]
      _ = ∑ i, j i * coeff a i := by
            simp [hΔ_apply, ha]
      _ = d a := by
            simpa [σ] using hcoeff_eq a
  · calc
      (∑ i, j i • Δ i) a = ∑ i, j i * (Δ i a) := by
            simp [smul_eq_mul]
      _ = 0 := by
            simp [hΔ_apply, ha]
      _ = d a := by
            simpa [DFinsupp.mem_support_toFun] using ha.symm

/-- Helper for Lemma 15.27.1: shifting an adic Cauchy sequence by finitely many stages does not
change its class in the completion. -/
private theorem adicCompletion_mk_shift_eq
    (c : ℕ) (δ : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R)) :
    AdicCompletion.mk I (⨁ _ : A, R)
      (AdicCompletion.AdicCauchySequence.mk (I := I) (M := (⨁ _ : A, R))
        (fun n ↦ δ (c + n))
        (fun n ↦ shifted_sequence_step (R := R) (I := I) (A := A) c δ n)) =
      AdicCompletion.mk I (⨁ _ : A, R) δ := by
  -- Evaluate both completion classes at stage `n`; the Cauchy relation for `δ` identifies the
  -- shifted stage `c + n` with the original stage `n`.
  apply AdicCompletion.ext_evalₐ (I := I)
  intro n
  apply (Submodule.Quotient.eq (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))).2
  exact (SModEq.sub_mem).mp ((δ.property (Nat.le_add_left n c)).symm)

/-- Helper for Lemma 15.27.1: the ordinary finitely supported inclusion into the product remains
injective after quotienting by any ideal. -/
private theorem directSum_coeFn_quotientMapByIdeal_injective (J : Ideal R) :
    Function.Injective
      ((DirectSum.coeFnLinearMap R : (⨁ _ : A, R) →ₗ[R] (A → R)).quotientMapByIdeal J) := by
  intro x y hxy
  refine Quotient.inductionOn₂' x y ?_ hxy
  intro x y hxy
  have hxy' :
      (Submodule.Quotient.mk (DirectSum.coeFnLinearMap R x) :
        (A → R) ⧸ (J • (⊤ : Submodule R (A → R)))) =
        Submodule.Quotient.mk (DirectSum.coeFnLinearMap R y) := by
    -- Rewrite the quotient-map equality on representatives as equality of quotient classes.
    simpa [LinearMap.quotientMapByIdeal] using hxy
  have hxy'' :
      DirectSum.coeFnLinearMap R x - DirectSum.coeFnLinearMap R y ∈
        J • (⊤ : Submodule R (A → R)) :=
    (Submodule.Quotient.eq _).1 hxy'
  apply (Submodule.Quotient.eq _).2
  -- Project to each coordinate to read the quotient equality as coordinatewise ideal membership.
  have hcoord : ∀ a, (x - y) a ∈ J := by
    intro a
    have hproj :
        DirectSum.coeFnLinearMap R x - DirectSum.coeFnLinearMap R y ∈
          Submodule.comap (LinearMap.proj a) (J • (⊤ : Submodule R R)) :=
      (Submodule.smul_top_le_comap_smul_top J (LinearMap.proj a)) hxy''
    have hmem : (x - y) a ∈ (J • (⊤ : Submodule R R) : Submodule R R) := by
      simpa [Submodule.mem_comap] using hproj
    exact (mem_smul_top_iff_mem_ideal (R := R) J ((x - y) a)).1 hmem
  -- Reassemble the finitely supported family from its coordinatewise ideal membership.
  simpa using
    directSum_mem_smul_top_of_coordinate_mem (R := R) (A := A) J (x - y) hcoord

/-- Helper for Lemma 15.27.1: the ordinary finitely supported inclusion `⨁ a, R → ∏ a, R` is
universally injective. -/
private theorem directSum_coeFn_universallyInjective :
    (DirectSum.coeFnLinearMap R : (⨁ _ : A, R) →ₗ[R] (A → R)).UniversallyInjective := by
  letI : Module.Flat R (A → R) :=
    (Module.noetherian_pi_flat_and_mittagLeffler : _
      ∧ Module.MittagLeffler R (A → R)).1
  -- Reduce universal injectivity of the dense inclusion to the quotient injectivity proved above.
  refine (universallyInjective_iff_injective_mod_finite_ideal
    (DirectSum.coeFnLinearMap R : (⨁ _ : A, R) →ₗ[R] (A → R))).2 ?_
  intro J hJ
  exact directSum_coeFn_quotientMapByIdeal_injective (R := R) (A := A) J

/-- Helper for Lemma 15.27.1: once a kernel representative `f` is frozen at one stage `c` with
all outside-support coordinates lie in `J + I^n` at shifted stage `c + n`. -/
private theorem outside_support_mem_ideal_add_pow
    (J : Ideal R) {xhat : AdicCompletion I (⨁ _ : A, R)}
    (hker : (adicCompletionDirectSumToPi I A).quotientMapByIdeal J
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) = 0)
    (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R))
    (hf : AdicCompletion.mk I (⨁ _ : A, R) f = xhat)
    (c n : ℕ) (a : A) :
    f (c + n) a ∈ J + (I ^ n : Ideal R) := by
  let r : R := (adicCompletionDirectSumToPi I A xhat) a
  have hrJ : r ∈ J := coordinate_mem_ideal_of_kernel (R := R) (I := I) (A := A) J hker a
  let fa : AdicCompletion.AdicCauchySequence I R :=
    AdicCompletion.AdicCauchySequence.map I
      ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R)) f
  have hstage_n :
      Ideal.Quotient.mk (I ^ n) (f n a) = Ideal.Quotient.mk (I ^ n) r := by
    -- Compare the chosen coordinate in the completion with the ambient product-side coordinate.
    have hcoord :
        AdicCompletion.mk I R fa = of I R r := by
      calc
        AdicCompletion.mk I R fa =
            map I ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))
              (AdicCompletion.mk I (⨁ _ : A, R) f) := by
              rw [AdicCompletion.map_mk]
        _ =
            map I ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R)) xhat := by
              rw [hf]
        _ = of I R r := by
              simpa [r] using
                (of_coordinate_adicCompletionDirectSumToPi
                  (R := R) (I := I) (A := A) xhat a).symm
    have hcoord_eval := congrArg (AdicCompletion.evalₐ I n) hcoord
    calc
      Ideal.Quotient.mk (I ^ n) (f n a) =
          AdicCompletion.evalₐ I n (AdicCompletion.mk I R fa) := by
            simp [fa, AdicCompletion.evalₐ_mk]
      _ = AdicCompletion.evalₐ I n (of I R r) := hcoord_eval
      _ = Ideal.Quotient.mk (I ^ n) r := by
            simpa using (AdicCompletion.evalₐ_of (I := I) n r)
  have hshift :
      Ideal.Quotient.mk (I ^ n) (f (c + n) a) = Ideal.Quotient.mk (I ^ n) (f n a) := by
    -- The coordinate sequence is Cauchy, so stage `c + n` agrees with stage `n` modulo `I^n`.
    have hmk :
        (Ideal.Quotient.mk (I ^ n)) (fa (c + n)) = (Ideal.Quotient.mk (I ^ n)) (fa n) := by
      simpa [fa] using
        (AdicCompletion.Ideal.mk_eq_mk (I := I) (m := n) (n := c + n)
          (Nat.le_add_left n c) fa)
    simpa [fa] using hmk
  have hdiff : f (c + n) a - r ∈ I ^ n := by
    have hzero : Ideal.Quotient.mk (I ^ n) (f (c + n) a - r) = 0 := by
      rw [map_sub, hshift, hstage_n, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  -- Decompose the element as a `J`-part plus an `I^n`-part.
  change f (c + n) a ∈ (J : Submodule R R) ⊔ (I ^ n : Ideal R)
  refine Submodule.mem_sup.2 ?_
  refine ⟨r, hrJ, f (c + n) a - r, hdiff, ?_⟩
  ring

/-- Helper for Lemma 15.27.1: the `n`th shifted stage restricted to the finite carrier `S`. -/
private noncomputable def restricted_shifted_stage
    (c : ℕ) (S : Finset A)
    (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R)) (n : ℕ) :
    (⨁ _ : ↥S, R) :=
  (DirectSum.linearEquivFunOnFintype R (↥S) (fun _ : ↥S ↦ R)).symm
    (fun s ↦ f (c + n) s.1)

/-- Helper for Lemma 15.27.1: the restricted shifted stage reads back the ambient coordinates on
the finite carrier `S`. -/
@[simp] private theorem restricted_shifted_stage_apply
    (c : ℕ) (S : Finset A)
    (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R)) (n : ℕ) (s : ↥S) :
    restricted_shifted_stage (R := R) (I := I) (A := A) c S f n s = f (c + n) s.1 := by
  simpa [restricted_shifted_stage] using
    congrFun
      (LinearEquiv.apply_symm_apply
        (DirectSum.linearEquivFunOnFintype R (↥S) (fun _ : ↥S ↦ R))
        (fun t ↦ f (c + n) t.1))
      s

/-- Helper for Lemma 15.27.1: the shifted restriction to `↥S` is still an adic Cauchy sequence. -/
private theorem restricted_shifted_sequence_step
    (c : ℕ) (S : Finset A)
    (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R)) (n : ℕ) :
    restricted_shifted_stage (R := R) (I := I) (A := A) c S f n ≡
      restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1)
        [SMOD I ^ n • (⊤ : Submodule R (⨁ _ : ↥S, R))] := by
  rw [SModEq.sub_mem]
  -- Reduce the finite-support congruence to coordinatewise ideal-power membership.
  refine directSum_mem_smul_top_of_coordinate_mem (R := R) (A := ↥S) (J := I ^ n)
    (x := restricted_shifted_stage (R := R) (I := I) (A := A) c S f n -
      restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1)) ?_
  intro s
  have hstep :
      f (c + n) - f (c + (n + 1)) ∈
        (I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R))) := by
    exact (SModEq.sub_mem).mp (f.property (Nat.le_succ (c + n)))
  have hproj :
      f (c + n) - f (c + (n + 1)) ∈
        Submodule.comap ((LinearMap.proj s.1).comp (DirectSum.coeFnLinearMap R))
          (I ^ (c + n) • (⊤ : Submodule R R)) :=
    (Submodule.smul_top_le_comap_smul_top (I ^ (c + n))
      ((LinearMap.proj s.1).comp (DirectSum.coeFnLinearMap R))) hstep
  have hcoord_big : f (c + n) s.1 - f (c + (n + 1)) s.1 ∈ I ^ (c + n) := by
    simpa [Submodule.mem_comap, LinearMap.comp_apply] using hproj
  have hcoord : f (c + n) s.1 - f (c + (n + 1)) s.1 ∈ I ^ n := by
    exact (Ideal.pow_le_pow_right (Nat.le_add_left n c)) hcoord_big
  change
    restricted_shifted_stage (R := R) (I := I) (A := A) c S f n s -
        restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1) s ∈
      I ^ n
  simpa using hcoord

/-- Helper for Lemma 15.27.1: the shifted restriction to `↥S` also preserves the deeper
`I ^ (c + n)`-adic control coming directly from the original representative sequence. -/
private theorem restricted_shifted_sequence_step_deep
    (c : ℕ) (S : Finset A)
    (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R)) (n : ℕ) :
    restricted_shifted_stage (R := R) (I := I) (A := A) c S f n -
        restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1) ∈
      I ^ (c + n) • (⊤ : Submodule R (⨁ _ : ↥S, R)) := by
  -- Reduce the deep congruence on the restricted direct sum to coordinatewise `I ^ (c + n)`
  -- membership of the underlying ambient sequence.
  refine directSum_mem_smul_top_of_coordinate_mem (R := R) (A := ↥S) (J := I ^ (c + n))
    (x := restricted_shifted_stage (R := R) (I := I) (A := A) c S f n -
      restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1)) ?_
  intro s
  have hstep :
      f (c + n) - f (c + (n + 1)) ∈
        I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
    exact (SModEq.sub_mem).mp (f.property (Nat.le_succ (c + n)))
  have hproj :
      f (c + n) - f (c + (n + 1)) ∈
        Submodule.comap ((LinearMap.proj s.1).comp (DirectSum.coeFnLinearMap R))
          (I ^ (c + n) • (⊤ : Submodule R R)) :=
    (Submodule.smul_top_le_comap_smul_top (I ^ (c + n))
      ((LinearMap.proj s.1).comp (DirectSum.coeFnLinearMap R))) hstep
  change
    restricted_shifted_stage (R := R) (I := I) (A := A) c S f n s -
        restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1) s ∈
      I ^ (c + n)
  simpa [Submodule.mem_comap, LinearMap.comp_apply] using hproj

/-- Helper for Lemma 15.27.1: the shifted restriction of an ambient representative to a fixed
finite support defines a completion point on that finite carrier. -/
private noncomputable def restricted_shifted_sequence
    (c : ℕ) (S : Finset A)
    (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R)) :
    AdicCompletion.AdicCauchySequence I (⨁ _ : ↥S, R) :=
  AdicCompletion.AdicCauchySequence.mk (I := I) (M := (⨁ _ : ↥S, R))
    (restricted_shifted_stage (R := R) (I := I) (A := A) c S f)
    (restricted_shifted_sequence_step (R := R) (I := I) (A := A) c S f)

/-- Helper for Lemma 15.27.1: shifting an adic Cauchy sequence by `c` stages preserves the
completion class while exposing the Artin-Rees stage `c` on every later term. -/
private theorem shifted_sequence_step
    (c : ℕ) (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R)) (n : ℕ) :
    f (c + n) ≡ f (c + (n + 1)) [SMOD I ^ n • (⊤ : Submodule R (⨁ _ : A, R))] := by
  -- The original Cauchy sequence already controls the shifted stages modulo `I^(c+n)`, and
  -- monotonicity of ideal powers lets us descend that control to `I^n`.
  have hstep :
      f (c + n) - f (c + (n + 1)) ∈
        I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
    exact (SModEq.sub_mem).mp (f.property (Nat.le_succ (c + n)))
  have hstep' :
      f (c + n) - f (c + (n + 1)) ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
    exact (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_add_left n c)) le_rfl) hstep
  exact (SModEq.sub_mem).2 hstep'

/-- Helper for Lemma 15.27.1: the shifted representative `n ↦ f (c + n)` is again an adic Cauchy
sequence. -/
private noncomputable def shifted_sequence
    (c : ℕ) (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R)) :
    AdicCompletion.AdicCauchySequence I (⨁ _ : A, R) :=
  AdicCompletion.AdicCauchySequence.mk (I := I) (M := (⨁ _ : A, R))
    (fun n ↦ f (c + n))
    (shifted_sequence_step (R := R) (I := I) (A := A) c f)

/-- Helper for Lemma 15.27.1: shifting a representative does not change the corresponding
completion point. -/
private theorem mk_shifted_sequence_eq
    (c : ℕ) (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R)) :
    AdicCompletion.mk I (⨁ _ : A, R) (shifted_sequence (R := R) (I := I) (A := A) c f) =
      AdicCompletion.mk I (⨁ _ : A, R) f := by
  -- Compare both completion points on every quotient stage `M / I^n M`.
  apply AdicCompletion.ext_evalₐ (I := I)
  intro n
  apply (Submodule.Quotient.eq (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))).2
  -- The Cauchy condition identifies stage `n` with the shifted stage `c + n` modulo `I^n`.
  exact (SModEq.sub_mem).mp ((f.property (Nat.le_add_left n c)).symm)

/-- Helper for Lemma 15.27.1: stagewise membership in `J M + I^n M` should force the
image of the represented completion class in the completion of `M / J M` to vanish. -/
private theorem completion_quotient_eval_zero_of_stagewise_mem_sup_pow
    (J : Ideal R)
    (δ : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R))
    (hδ :
      ∀ n : ℕ,
        δ n ∈ (J • (⊤ : Submodule R (⨁ _ : A, R))) ⊔
          (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))) :
    AdicCompletion.map I ((J • (⊤ : Submodule R (⨁ _ : A, R))).mkQ)
        (AdicCompletion.mk I (⨁ _ : A, R) δ) = 0 := by
  apply AdicCompletion.ext_evalₐ (I := I)
  intro n
  let K : Submodule R (⨁ _ : A, R) := J • (⊤ : Submodule R (⨁ _ : A, R))
  have hcomap_pow :
      Submodule.comap (K.mkQ)
          (I ^ n • (⊤ : Submodule R ((⨁ _ : A, R) ⧸ K))) =
        K ⊔ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
    -- Rewrite the `I^n`-power submodule in the quotient via the standard `mkQ` map/comap square.
    have hmap :
        Submodule.map K.mkQ (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) =
          I ^ n • (⊤ : Submodule R ((⨁ _ : A, R) ⧸ K)) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [← hmap, Submodule.comap_map_mkQ]
  have hpow :
      K.mkQ (δ n) ∈ I ^ n • (⊤ : Submodule R ((⨁ _ : A, R) ⧸ K)) := by
    -- The hypothesis `δ n ∈ J M + I^n M` is exactly the quotient-side `I^n`-membership after
    -- pulling back along `mkQ`.
    rw [← hcomap_pow, Submodule.mem_comap]
    exact hδ n
  -- Evaluating the descended completion class at stage `n` is the quotient class of `δ n`.
  change
    Submodule.Quotient.mk (I ^ n • (⊤ : Submodule R ((⨁ _ : A, R) ⧸ K))) (K.mkQ (δ n)) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 hpow

/-- Helper for Lemma 15.27.1: the completion of the quotient module `M / J M` is still
annihilated by `J`. -/
private theorem completion_quotient_target_smul_top_eq_bot
    (J : Ideal R) :
    J • (⊤ : Submodule R (AdicCompletion I ((⨁ _ : A, R) ⧸
      (J • (⊤ : Submodule R (⨁ _ : A, R)))))) = ⊥ := by
  apply le_antisymm
  · intro x hx
    -- Every generator coming from `J` already acts trivially on the quotient module itself, so
    -- it also acts trivially on its completion.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      obtain ⟨δ, rfl⟩ := AdicCompletion.mk_surjective I
        ((⨁ _ : A, R) ⧸ (J • (⊤ : Submodule R (⨁ _ : A, R)))) y
      apply AdicCompletion.ext_evalₐ (I := I)
      intro n
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
        (J • (⊤ : Submodule R (⨁ _ : A, R))) (δ n)
      change
        Submodule.Quotient.mk
            (I ^ n •
              (⊤ : Submodule R ((⨁ _ : A, R) ⧸ (J • (⊤ : Submodule R (⨁ _ : A, R))))))
            (r • (Submodule.mkQ (J • (⊤ : Submodule R (⨁ _ : A, R))) z)) = 0
      have hzero :
          r • (Submodule.mkQ (J • (⊤ : Submodule R (⨁ _ : A, R))) z) = 0 := by
        rw [← map_smul]
        refine (Submodule.Quotient.mk_eq_zero _).2 ?_
        exact Submodule.smul_mem_smul hr (by simp)
      simp [hzero]
    · intro y z hy hz
      simpa [hy, hz]
  · exact bot_le

/-- Helper for Lemma 15.27.1: the canonical comparison from the quotient of the completion to the
completion of the quotient is well defined because the target is annihilated by `J`. -/
private theorem completion_quotient_comparison_kills_source
    (J : Ideal R) :
    J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))) ≤
      LinearMap.ker
        (AdicCompletion.map I ((J • (⊤ : Submodule R (⨁ _ : A, R))).mkQ)) := by
  -- The quotient map kills `J M`, and the completed target is itself annihilated by `J`.
  have hcomap :
      J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))) ≤
        Submodule.comap
          (AdicCompletion.map I ((J • (⊤ : Submodule R (⨁ _ : A, R))).mkQ))
          (J •
            (⊤ : Submodule R
            (AdicCompletion I ((⨁ _ : A, R) ⧸
                (J • (⊤ : Submodule R (⨁ _ : A, R))))))) :=
    Submodule.smul_top_le_comap_smul_top J
      (AdicCompletion.map I ((J • (⊤ : Submodule R (⨁ _ : A, R))).mkQ))
  intro x hx
  have hx' := hcomap hx
  have hx'' :
      AdicCompletion.map I ((J • (⊤ : Submodule R (⨁ _ : A, R))).mkQ) x ∈
        (⊥ : Submodule R
          (AdicCompletion I ((⨁ _ : A, R) ⧸ (J • (⊤ : Submodule R (⨁ _ : A, R)))))) := by
    simpa [Submodule.mem_comap,
      completion_quotient_target_smul_top_eq_bot (R := R) (I := I) (A := A) J] using hx'
  simpa [LinearMap.mem_ker] using hx''

/-- Helper for Lemma 15.27.1: the canonical comparison from the quotient of the completion to the
completion of the quotient module. -/
private noncomputable def completion_quotient_comparison (J : Ideal R) :
    (AdicCompletion I (⨁ _ : A, R)) ⧸
        (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))) →ₗ[R]
      AdicCompletion I ((⨁ _ : A, R) ⧸ (J • (⊤ : Submodule R (⨁ _ : A, R)))) :=
  Submodule.liftQ
    (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))
    (AdicCompletion.map I ((J • (⊤ : Submodule R (⨁ _ : A, R))).mkQ))
    (completion_quotient_comparison_kills_source (R := R) (I := I) (A := A) J)

/-- Helper for Lemma 15.27.1: on quotient representatives, the comparison map is just the
completed quotient map. -/
@[simp] private theorem completion_quotient_comparison_apply_mkQ
    (J : Ideal R) (xhat : AdicCompletion I (⨁ _ : A, R)) :
    completion_quotient_comparison (R := R) (I := I) (A := A) J
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) =
      AdicCompletion.map I ((J • (⊤ : Submodule R (⨁ _ : A, R))).mkQ) xhat := by
  -- The descended map was defined by `Submodule.liftQ`, so it computes directly on classes.
  simp [completion_quotient_comparison]

/-- Helper for Lemma 15.27.1: if a kernel class of the quotient-completion comparison is zero,
then every stage of a chosen representative sequence already lies in `J M + I^n M`. This is the
stagewise bridge from the abstract kernel equation to the source proof's concrete Artin-Rees
invariant. -/
private theorem comparison_zero_stagewise_mem_sup_pow
    (J : Ideal R) {xhat : AdicCompletion I (⨁ _ : A, R)}
    (hker : completion_quotient_comparison (R := R) (I := I) (A := A) J
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) = 0)
    (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R))
    (hf : AdicCompletion.mk I (⨁ _ : A, R) f = xhat) :
    ∀ n : ℕ,
      f n ∈ (J • (⊤ : Submodule R (⨁ _ : A, R))) ⊔
        (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) := by
  let K : Submodule R (⨁ _ : A, R) := J • (⊤ : Submodule R (⨁ _ : A, R))
  have hdesc_zero :
      AdicCompletion.map I K.mkQ (AdicCompletion.mk I (⨁ _ : A, R) f) = 0 := by
    -- Rewrite the abstract kernel equation as vanishing of the completed quotient map on the
    -- chosen Cauchy representative.
    simpa [K, hf] using
      (completion_quotient_comparison_apply_mkQ (R := R) (I := I) (A := A) J xhat).trans hker
  intro n
  have hstage_zero :
      AdicCompletion.evalₐ I n
          (AdicCompletion.map I K.mkQ (AdicCompletion.mk I (⨁ _ : A, R) f)) = 0 := by
    -- Evaluate the vanished descended completion class at stage `n`.
    simpa using congrArg (AdicCompletion.evalₐ I n) hdesc_zero
  have hpow :
      K.mkQ (f n) ∈ I ^ n • (⊤ : Submodule R ((⨁ _ : A, R) ⧸ K)) := by
    -- The stage `n` quotient class vanishes exactly when the descended stage lies in `I^n`.
    change
      Submodule.Quotient.mk
          (I ^ n • (⊤ : Submodule R ((⨁ _ : A, R) ⧸ K)))
          (K.mkQ (f n)) = 0 at hstage_zero
    exact (Submodule.Quotient.mk_eq_zero _).1 hstage_zero
  have hcomap_pow :
      Submodule.comap K.mkQ
          (I ^ n • (⊤ : Submodule R ((⨁ _ : A, R) ⧸ K))) =
        K ⊔ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
    -- Pulling back the `I^n`-submodule along `mkQ` turns quotient-side `I^n`-membership into the
    -- source-side `J M + I^n M` condition.
    have hmap :
        Submodule.map K.mkQ (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) =
          I ^ n • (⊤ : Submodule R ((⨁ _ : A, R) ⧸ K)) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [← hmap, Submodule.comap_map_mkQ]
  rw [← hcomap_pow, Submodule.mem_comap] at hpow
  exact hpow

/-- Helper for Lemma 15.27.1: after freezing the support `S = (f c).support` of one stage of a
kernel representative for `completion_quotient_comparison`, the difference between the shifted
ambient stage and the included restricted stage has coordinates in `(J ∩ I^c) + I^(c + n)`. -/
private theorem frozen_support_difference_mem_intersection_add_pow
    [DecidableEq A]
    (J : Ideal R) {xhat : AdicCompletion I (⨁ _ : A, R)}
    (hker : completion_quotient_comparison (R := R) (I := I) (A := A) J
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) = 0)
    (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R))
    (hf : AdicCompletion.mk I (⨁ _ : A, R) f = xhat)
    (c n : ℕ) (S : Finset A)
    (hzero : ∀ a, a ∉ S → f c a = 0) :
    f (c + n) -
        finsetSupportInclusion (R := R) (A := A) S
          (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n) ∈
      (((J ⊓ I ^ c : Ideal R) • (⊤ : Submodule R (⨁ _ : A, R))) : Submodule R (⨁ _ : A, R)) ⊔
        (I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R))) := by
  let δ : ⨁ _ : A, R :=
    f (c + n) -
      finsetSupportInclusion (R := R) (A := A) S
        (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n)
  have hstage :
      f (c + n) ∈ (J • (⊤ : Submodule R (⨁ _ : A, R))) ⊔
        (I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R))) :=
    comparison_zero_stagewise_mem_sup_pow
      (R := R) (I := I) (A := A) J hker f hf (c + n)
  have hcoord :
      ∀ a, δ a ∈ (J ⊓ I ^ c : Ideal R) + I ^ (c + n) := by
    intro a
    by_cases ha : a ∈ S
    · -- On the frozen carrier the restricted stage reproduces the ambient coordinate exactly.
      have hδ : δ a = 0 := by
        simp [δ, ha, restricted_shifted_stage_apply]
      simpa [hδ]
    · -- Outside the frozen carrier, the restricted stage vanishes, and the ambient coordinate lies
      -- both in `I^c` and in `J + I^(c + n)`.
      have hδ :
          δ a = f (c + n) a := by
        simp [δ, ha]
      have hpow_stage :
          f c - f (c + n) ∈ I ^ c • (⊤ : Submodule R (⨁ _ : A, R)) := by
        exact (SModEq.sub_mem).mp (f.property (Nat.le_add_right c n))
      have hpow_coord0 :
          f c a - f (c + n) a ∈ I ^ c := by
        have hproj :
            f c - f (c + n) ∈
              Submodule.comap ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))
                (I ^ c • (⊤ : Submodule R R)) :=
          (Submodule.smul_top_le_comap_smul_top (I ^ c)
            ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))) hpow_stage
        simpa [Submodule.mem_comap, LinearMap.comp_apply] using hproj
      have hpow_coord :
          f (c + n) a ∈ I ^ c := by
        have hneg : -(f (c + n) a) ∈ I ^ c := by
          simpa [hzero a ha] using hpow_coord0
        simpa using Ideal.neg_mem (I ^ c) hneg
      have hcoord_sup :
          f (c + n) a ∈ J + I ^ (c + n) := by
        rcases Submodule.mem_sup.1 hstage with ⟨y, hyJ, z, hzI, hyz⟩
        have hycoord :
            y a ∈ J := by
          have hproj :
              y ∈ Submodule.comap ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))
                (J • (⊤ : Submodule R R)) :=
            (Submodule.smul_top_le_comap_smul_top J
              ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))) hyJ
          have hycoord' : y a ∈ (J • (⊤ : Submodule R R) : Submodule R R) := by
            simpa [Submodule.mem_comap, LinearMap.comp_apply] using hproj
          exact (mem_smul_top_iff_mem_ideal (R := R) J (y a)).1 hycoord'
        have hzcoord :
            z a ∈ I ^ (c + n) := by
          have hproj :
              z ∈ Submodule.comap ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))
                (I ^ (c + n) • (⊤ : Submodule R R)) :=
            (Submodule.smul_top_le_comap_smul_top (I ^ (c + n))
              ((LinearMap.proj a).comp (DirectSum.coeFnLinearMap R))) hzI
          simpa [Submodule.mem_comap, LinearMap.comp_apply] using hproj
        change f (c + n) a ∈ ((J : Submodule R R) ⊔ (I ^ (c + n) : Ideal R))
        refine Submodule.mem_sup.2 ?_
        refine ⟨y a, hycoord, z a, hzcoord, ?_⟩
        have hyz_coord := congrArg (fun m : ⨁ _ : A, R ↦ m a) hyz
        simpa using hyz_coord
      have hcoord_sup' :
          f (c + n) a ∈ ((J : Submodule R R) ⊔ (I ^ (c + n) : Ideal R)) := by
        simpa [Ideal.add_eq_sup] using hcoord_sup
      rcases Submodule.mem_sup.1 hcoord_sup' with ⟨j, hjJ, t, htPow, hsum⟩
      have htIc : t ∈ I ^ c := by
        exact (Ideal.pow_le_pow_right (Nat.le_add_right c n)) htPow
      have hjIc : j ∈ I ^ c := by
        have hsub : f (c + n) a - t ∈ I ^ c := by
          exact Ideal.sub_mem (I ^ c) hpow_coord htIc
        simpa [hsum] using hsub
      have hcoord_final :
          f (c + n) a ∈ ((J ⊓ I ^ c : Ideal R) : Submodule R R) ⊔ (I ^ (c + n) : Ideal R) := by
        refine Submodule.mem_sup.2 ?_
        exact ⟨j, ⟨hjJ, hjIc⟩, t, htPow, hsum⟩
      simpa [hδ, Ideal.add_eq_sup] using hcoord_final
  have hmem :
      δ ∈ ((J ⊓ I ^ c : Ideal R) + I ^ (c + n)) • (⊤ : Submodule R (⨁ _ : A, R)) := by
    exact directSum_mem_smul_top_of_coordinate_mem
      (R := R) (A := A) (J := (J ⊓ I ^ c : Ideal R) + I ^ (c + n)) δ hcoord
  have hsup :
      ((J ⊓ I ^ c : Ideal R) + I ^ (c + n)) • (⊤ : Submodule R (⨁ _ : A, R)) =
        (((J ⊓ I ^ c : Ideal R) • (⊤ : Submodule R (⨁ _ : A, R))) :
            Submodule R (⨁ _ : A, R)) ⊔
          (I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R))) := by
    simpa [Ideal.add_eq_sup] using
      (Submodule.sup_smul
        (R := R) (A := R) (M := (⨁ _ : A, R))
        (I := ((J ⊓ I ^ c : Ideal R) : Submodule R R)) (J := (I ^ (c + n) : Ideal R))
        (N := (⊤ : Submodule R (⨁ _ : A, R))))
  have hmem' :
      δ ∈ (((J ⊓ I ^ c : Ideal R) • (⊤ : Submodule R (⨁ _ : A, R))) :
          Submodule R (⨁ _ : A, R)) ⊔
        (I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R))) := by
    rwa [hsup] at hmem
  simpa [δ] using hmem'

/-- Helper for Lemma 15.27.1: from the frozen-support Artin-Rees decomposition, choose at each
stage an explicit summand in the core submodule `((J ∩ I^c) • ⊤)`. -/
private theorem frozen_support_difference_has_intersection_lift
    (J : Ideal R) (c : ℕ) (δ : ℕ → (⨁ _ : A, R))
    (hδstage :
      ∀ n : ℕ,
        δ n ∈ (((J ⊓ I ^ c : Ideal R) • (⊤ : Submodule R (⨁ _ : A, R))) :
            Submodule R (⨁ _ : A, R)) ⊔
          (I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)))) :
    ∃ g : ℕ → (⨁ _ : A, R),
      (∀ n : ℕ,
        g n ∈ (((J ⊓ I ^ c : Ideal R) • (⊤ : Submodule R (⨁ _ : A, R))) :
            Submodule R (⨁ _ : A, R))) ∧
      ∀ n : ℕ,
        δ n - g n ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
  classical
  -- Choose one witness of the `core + deep error` decomposition at each stage.
  choose g hgK e hePow hsum using fun n ↦ Submodule.mem_sup.1 (hδstage n)
  refine ⟨g, hgK, ?_⟩
  intro n
  have hrewrite : δ n - g n = e n := by
    calc
      δ n - g n = (g n + e n) - g n := by rw [(hsum n).symm]
      _ = e n := by abel
  simpa [hrewrite] using hePow n

/-- Helper for Lemma 15.27.1: a stagewise lift that approximates an adic Cauchy sequence modulo
`I^(c + n)` is itself adically Cauchy modulo `I^n`. -/
private theorem frozen_support_difference_lift_step
    (c : ℕ)
    (δ : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R))
    (g : ℕ → (⨁ _ : A, R))
    (happrox :
      ∀ n : ℕ,
        δ n - g n ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R))) :
    ∀ n : ℕ,
      g n ≡ g (n + 1) [SMOD I ^ n • (⊤ : Submodule R (⨁ _ : A, R))] := by
  intro n
  rw [SModEq.sub_mem]
  -- Split `g n - g (n + 1)` into the two approximation errors and the ambient Cauchy step of `δ`.
  have hleft_big :
      δ n - g n ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) :=
    happrox n
  have hleft :
      δ n - g n ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
    exact (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_add_left n c)) le_rfl) hleft_big
  have hright_big :
      δ (n + 1) - g (n + 1) ∈ I ^ (c + (n + 1)) • (⊤ : Submodule R (⨁ _ : A, R)) :=
    happrox (n + 1)
  have hright :
      δ (n + 1) - g (n + 1) ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
    exact
      (Submodule.smul_mono
        (Ideal.pow_le_pow_right (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.le_add_left n (c + 1))) le_rfl)
        hright_big
  have hdelta :
      δ n - δ (n + 1) ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
    exact (SModEq.sub_mem).mp (δ.property (Nat.le_succ n))
  have hsum :
      g n - g (n + 1) =
        - (δ n - g n) + (δ n - δ (n + 1)) + (δ (n + 1) - g (n + 1)) := by
    abel
  rw [hsum]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.neg_mem _ hleft) hdelta) hright

/-- Helper for Lemma 15.27.1: if the ambient frozen-support difference sequence already has deep
`I ^ (c + n)`-steps, then any stagewise lift approximating it modulo `I ^ (c + n)` inherits the
same deep-step control. -/
private theorem frozen_support_difference_lift_step_deep
    (c : ℕ)
    (δ : ℕ → (⨁ _ : A, R))
    (g : ℕ → (⨁ _ : A, R))
    (hδdeep :
      ∀ n : ℕ,
        δ n - δ (n + 1) ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)))
    (happrox :
      ∀ n : ℕ,
        δ n - g n ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R))) :
    ∀ n : ℕ,
      g n - g (n + 1) ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
  intro n
  -- Expand `g n - g (n + 1)` into the two approximation errors and the deep ambient step of `δ`.
  have hleft :
      δ n - g n ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) :=
    happrox n
  have hright :
      δ (n + 1) - g (n + 1) ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
    have hright_big :
        δ (n + 1) - g (n + 1) ∈ I ^ (c + (n + 1)) • (⊤ : Submodule R (⨁ _ : A, R)) :=
      happrox (n + 1)
    exact
      (Submodule.smul_mono
        (Ideal.pow_le_pow_right (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.le_add_left (c + n) 1)) le_rfl)
        hright_big
  have hsum :
      g n - g (n + 1) =
        - (δ n - g n) + (δ n - δ (n + 1)) + (δ (n + 1) - g (n + 1)) := by
    abel
  rw [hsum]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.neg_mem _ hleft) (hδdeep n)) hright

/-- Helper for Lemma 15.27.1: for a finite index type, the direct sum itself is already
`I`-adically complete. -/
private theorem directSum_isAdicComplete_of_fintype
    [Fintype A] [DecidableEq A] :
    IsAdicComplete I (⨁ _ : A, R) := by
  have hof_injective : Function.Injective (of I (⨁ _ : A, R)) := by
    intro x y hxy
    have hcmp := congrArg (adicCompletionDirectSumToPi I A) hxy
    exact (directSum_coeFn_bijective_of_fintype (R := R) (A := A)).1 <|
      by simpa [adicCompletionDirectSumToPi_of] using hcmp
  have hof_surjective : Function.Surjective (of I (⨁ _ : A, R)) := by
    intro xhat
    let y : A → R := adicCompletionDirectSumToPi I A xhat
    obtain ⟨x, hx⟩ := (directSum_coeFn_bijective_of_fintype (R := R) (A := A)).2 y
    refine ⟨x, ?_⟩
    apply (adicCompletionDirectSumToPi_linearEquiv_of_fintype_injective
      (R := R) (I := I) (A := A))
    rw [← adicCompletionDirectSumToPi_eq_linearEquiv_of_fintype (R := R) (I := I) (A := A)]
    simp [y, hx, adicCompletionDirectSumToPi_of]
  exact (AdicCompletion.of_bijective_iff).mp ⟨hof_injective, hof_surjective⟩

/-- Helper for Lemma 15.27.1: for a finite index type, the ideal-multiple submodule `J • ⊤` of
the direct sum is `I`-adically complete. -/
private theorem ideal_smul_top_isAdicComplete_of_fintype
    [Fintype A] [DecidableEq A] (J : Ideal R) :
    IsAdicComplete I (J • (⊤ : Submodule R (⨁ _ : A, R))) := by
  let M : Type v := (⨁ _ : A, R)
  let K : Submodule R M := J • (⊤ : Submodule R M)
  have hcompleteM : IsAdicComplete I M :=
    directSum_isAdicComplete_of_fintype (R := R) (I := I) (A := A)
  have hhausM : IsHausdorff I M := hcompleteM.toIsHausdorff
  have hbotM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥ :=
    IsHausdorff.iInf_pow_smul hhausM
  have hbotK : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R K) : Submodule R K) = ⊥ := by
    apply Submodule.eq_bot_iff.2
    intro x hx
    have hxM : (x : M) ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) := by
      rw [Submodule.mem_iInf]
      intro n
      have hxn : x ∈ I ^ n • (⊤ : Submodule R K) := by
        exact (Submodule.mem_iInf.mp hx) n
      have hcomap :
          x ∈ Submodule.comap (K.subtype : K →ₗ[R] M)
            (I ^ n • (⊤ : Submodule R M)) :=
        (Submodule.smul_top_le_comap_smul_top (I ^ n) (K.subtype : K →ₗ[R] M)) hxn
      simpa [Submodule.mem_comap] using hcomap
    have hx0 : (x : M) = 0 := by
      simpa [hbotM] using hxM
    ext
    exact hx0
  letI : Module.Finite R K := inferInstance
  exact isAdicComplete_of_finite_of_iInf_pow_smul_eq_bot (I := I) (M := K) hbotK

/-- Helper for Lemma 15.27.1: for a finite index type, the completed inclusion of the submodule
`J • ⊤` into the direct sum has range exactly `J • ⊤` inside the ambient completion. -/
private theorem completion_subtype_range_eq_smul_top_of_fintype
    [Fintype A] [DecidableEq A] (J : Ideal R) :
    LinearMap.range
        (((AdicCompletion.map I
            ((J • (⊤ : Submodule R (⨁ _ : A, R)))).subtype).restrictScalars R)) =
      J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))) := by
  let M : Type v := (⨁ _ : A, R)
  let K : Submodule R M := J • (⊤ : Submodule R M)
  let f : AdicCompletion I K →ₗ[R] AdicCompletion I M :=
    (AdicCompletion.map I K.subtype).restrictScalars R
  let eK : K ≃ₗ[R] AdicCompletion I K := ofLinearEquiv I K
  let eM : M ≃ₗ[R] AdicCompletion I M := ofLinearEquiv I M
  have hcompleteM : IsAdicComplete I M :=
    directSum_isAdicComplete_of_fintype (R := R) (I := I) (A := A)
  have hcompleteK : IsAdicComplete I K :=
    ideal_smul_top_isAdicComplete_of_fintype (R := R) (I := I) (A := A) J
  letI : IsAdicComplete I M := hcompleteM
  letI : IsAdicComplete I K := hcompleteK
  have hrange :
      LinearMap.range f = Submodule.map eM.toLinearMap K := by
    ext y
    constructor
    · rintro ⟨xhat, rfl⟩
      obtain ⟨x, rfl⟩ := eK.surjective xhat
      refine ⟨x, ?_⟩
      simp [f, eK, eM]
    · rintro ⟨x, rfl⟩
      refine ⟨eK x, ?_⟩
      simp [f, eK, eM]
  have htop : Submodule.map eM.toLinearMap (⊤ : Submodule R M) = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.2 eM.surjective
  calc
    LinearMap.range (((AdicCompletion.map I K.subtype).restrictScalars R)) =
        Submodule.map eM.toLinearMap K := hrange
    _ = J • (⊤ : Submodule R (AdicCompletion I M)) := by
      rw [K, Submodule.map_smul'', htop]

/-- Helper for Lemma 15.27.1: for a finite index type, the quotient-completion comparison is
injective because completed exactness identifies its kernel with the completed ideal-multiple
submodule. -/
private theorem completion_quotient_comparison_injective_of_fintype
    [Fintype A] [DecidableEq A] (J : Ideal R) :
    Function.Injective (completion_quotient_comparison (R := R) (I := I) (A := A) J) := by
  let M : Type v := (⨁ _ : A, R)
  let K : Submodule R M := J • (⊤ : Submodule R M)
  let f : AdicCompletion I K →ₗ[R] AdicCompletion I M :=
    (AdicCompletion.map I K.subtype).restrictScalars R
  let g : AdicCompletion I M →ₗ[R] AdicCompletion I (M ⧸ K) :=
    (AdicCompletion.map I K.mkQ).restrictScalars R
  have hsub_injective : Function.Injective (K.subtype : K →ₗ[R] M) := by
    intro x y hxy
    exact Subtype.ext hxy
  have hsub_exact : Function.Exact (K.subtype : K →ₗ[R] M) K.mkQ := by
    rw [LinearMap.exact_iff]
    ext x
    simp [K]
  have hcomp_exact : Function.Exact f g := by
    exact AdicCompletion.map_exact (I := I) hsub_injective hsub_exact K.mkQ_surjective
  have hker_eq :
      LinearMap.ker g =
        J • (⊤ : Submodule R (AdicCompletion I M)) := by
    calc
      LinearMap.ker g = LinearMap.range f := by
        symm
        exact (LinearMap.exact_iff.mp hcomp_exact)
      _ = J • (⊤ : Submodule R (AdicCompletion I M)) := by
        simpa [f, K, M] using
          completion_subtype_range_eq_smul_top_of_fintype
            (R := R) (I := I) (A := A) J
  intro q₁ q₂ hq
  refine Quotient.inductionOn₂' q₁ q₂ ?_ hq
  intro x y hxy
  apply (Submodule.Quotient.eq
    (J • (⊤ : Submodule R (AdicCompletion I M)))).2
  have hgxy : g x = g y := by
    simpa [completion_quotient_comparison_apply_mkQ, g, K, M] using hxy
  have hmemker : x - y ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker, map_sub, hgxy, sub_self]
  simpa [hker_eq, M]
    using hmemker

/-- Helper for Lemma 15.27.1: quotienting the frozen-support inclusion commutes with the
comparison maps from completion-quotients to completed quotients. -/
private theorem completion_quotient_comparison_finset_support_naturality
    [DecidableEq A] (J : Ideal R) (S : Finset A) :
    (completion_quotient_comparison (R := R) (I := I) (A := A) J).comp
        ((((AdicCompletion.map I
            (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R).quotientMapByIdeal J)) =
      (((AdicCompletion.map I
          ((finsetSupportInclusion (R := R) (A := A) S).quotientMapByIdeal J)).restrictScalars R).comp
        (completion_quotient_comparison (R := R) (I := I) (A := ↥S) J)) := by
  -- Compare the two sides on quotient representatives before the completion functor introduces
  -- any extra transport.
  ext x
  obtain ⟨xhat, rfl⟩ := Submodule.mkQ_surjective
    (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))) x
  simp [completion_quotient_comparison_apply_mkQ, quotientMapByIdeal_comp, AdicCompletion.map_comp]

/-- Helper for Lemma 15.27.1: a frozen-support core lift in `((J ∩ I^c) • ⊤)` with deep
`I ^ (c + n)`-control should already define a zero class modulo `J • ⊤` in the source
completion. -/
private theorem completed_intersection_core_lift_class_zero
    (J : Ideal R) (hJ : J.FG) (c : ℕ)
    (δ : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R))
    (g : ℕ → (⨁ _ : A, R))
    (hgK :
      ∀ n : ℕ,
        g n ∈ (((J ⊓ I ^ c : Ideal R) • (⊤ : Submodule R (⨁ _ : A, R))) :
          Submodule R (⨁ _ : A, R)))
    (happrox :
      ∀ n : ℕ,
        δ n - g n ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)))
    (hdeep :
      ∀ n : ℕ,
        g n - g (n + 1) ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R))) :
    ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).mkQ
      (AdicCompletion.mk I (⨁ _ : A, R) δ) = 0 := by
  classical
  -- Route correction: instead of asking the final quotient argument to reconstruct a source-side
  -- witness at once, shift by one Artin-Rees bound for a finite generating map of `J` and then
  -- telescope the deep differences into finitely many coefficient Cauchy sequences.
  obtain ⟨s, hs⟩ := hJ
  let j : Fin s.card → R := fun i ↦ (s.equivFin.symm i : R)
  have hspan : Ideal.span (Set.range j) = J := by
    -- Rewrite the chosen finite generating set as a `Fin`-indexed family.
    rw [← hs]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [j]⟩
  have hj : ∀ i : Fin s.card, j i ∈ J := by
    intro i
    have hmem : j i ∈ Ideal.span (Set.range j) := by
      exact Ideal.subset_span ⟨i, rfl⟩
    simpa [hspan] using hmem
  let σ : (Fin s.card → R) →ₗ[R] R := generatorLinearMap (R := R) j
  obtain ⟨b, hpreimage⟩ := Ideal.exists_exact_preimage_pow_smul_eq (R := R) (I := I) σ
  have hσ : σ.IsArtinReesBound I b :=
    LinearMap.isArtinReesBound_of_preimage_pow_smul_eq (I := I) hpreimage
  let δShift : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R) :=
    AdicCompletion.AdicCauchySequence.mk (I := I) (M := (⨁ _ : A, R))
      (fun n ↦ δ (b + n))
      (fun n ↦ shifted_sequence_step (R := R) (I := I) (A := A) b δ n)
  let gShift : ℕ → (⨁ _ : A, R) := fun n ↦ g (b + n)
  have hgShift_mem :
      ∀ n : ℕ, gShift n ∈ J • (⊤ : Submodule R (⨁ _ : A, R)) := by
    intro n
    -- Each `g (b + n)` lies in the smaller core submodule `((J ∩ I^c) • ⊤)`.
    exact (Submodule.smul_mono
      (show ((J ⊓ I ^ c : Ideal R) : Submodule R R) ≤ J by
        exact inf_le_left) le_rfl) (hgK (b + n))
  have happroxShift :
      ∀ n : ℕ,
        δShift n - gShift n ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
    intro n
    -- After shifting by `b`, the original deep approximation is automatically strong enough for
    -- the ambient `I ^ n`-adic filtration.
    exact (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_add_left n (c + b))) le_rfl) <|
      by simpa [δShift, gShift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using happrox (b + n)
  have hdeepShift :
      ∀ n : ℕ,
        gShift n - gShift (n + 1) ∈ I ^ (b + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
    intro n
    -- The shifted difference still lies in a deeper power, hence certainly in `I ^ (b + n)`.
    exact (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_add_left (b + n) c)) le_rfl) <|
      by simpa [gShift, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdeep (b + n)
  have hgShift_cauchy :
      ∀ n : ℕ,
        gShift n ≡ gShift (n + 1) [SMOD I ^ n • (⊤ : Submodule R (⨁ _ : A, R))] := by
    intro n
    rw [SModEq.sub_mem]
    exact (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_add_left n b)) le_rfl) (hdeepShift n)
  let gSeq : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R) :=
    AdicCompletion.AdicCauchySequence.mk (I := I) (M := (⨁ _ : A, R)) gShift hgShift_cauchy
  obtain ⟨u0, hu0⟩ :=
    generator_sum_representation_of_mem_smul_top
      (R := R) (J := J) (j := j) hspan (hgShift_mem 0)
  have hΔ :
      ∀ n : ℕ, ∃ Δ : Fin s.card → (⨁ _ : A, R),
        gShift n - gShift (n + 1) = ∑ i, j i • Δ i ∧
          ∀ i, Δ i ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
    intro n
    -- Lift each deep difference through the fixed finite generating map with `I ^ n`-small
    -- coefficients.
    apply deep_generator_difference_lift
      (R := R) (I := I) (A := A) J j hspan b n hσ
    · exact (J • (⊤ : Submodule R (⨁ _ : A, R))).sub_mem (hgShift_mem n) (hgShift_mem (n + 1))
    · exact hdeepShift n
  choose Δ hΔeq hΔmem using hΔ
  let uStage : Fin s.card → ℕ → (⨁ _ : A, R) :=
    fun i ↦ Nat.rec (u0 i) (fun n u ↦ u - Δ n i)
  have huStage_succ :
      ∀ i : Fin s.card, ∀ n : ℕ, uStage i (n + 1) = uStage i n - Δ n i := by
    intro i n
    simp [uStage]
  have huStage_step :
      ∀ i : Fin s.card, ∀ n : ℕ,
        uStage i n - uStage i (n + 1) ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
    intro i n
    rw [huStage_succ]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hΔmem n i
  have hgStage :
      ∀ n : ℕ, gShift n = ∑ i, j i • uStage i n := by
    intro n
    induction n with
    | zero =>
        -- The initial stage uses the one-time decomposition of `g b`.
        simpa [gShift, uStage] using hu0
    | succ n ihn =>
        -- Each successor stage is obtained by subtracting the Artin-Rees-controlled difference.
        calc
          gShift (n + 1) = gShift n - (gShift n - gShift (n + 1)) := by abel
          _ = ∑ i, j i • uStage i n - ∑ i, j i • Δ n i := by rw [ihn, hΔeq n]
          _ = ∑ i, j i • uStage i (n + 1) := by
                simp [huStage_succ, smul_sub, Finset.sum_sub_distrib]
  have hu_cauchy :
      ∀ i : Fin s.card,
        ∀ n : ℕ, uStage i n ≡ uStage i (n + 1) [SMOD I ^ n • (⊤ : Submodule R (⨁ _ : A, R))] := by
    intro i n
    rw [SModEq.sub_mem]
    exact huStage_step i n
  let u : Fin s.card → AdicCompletion.AdicCauchySequence I (⨁ _ : A, R) :=
    fun i ↦ AdicCompletion.AdicCauchySequence.mk (I := I) (M := (⨁ _ : A, R))
      (uStage i) (hu_cauchy i)
  have hgSeq_eq :
      AdicCompletion.mk I (⨁ _ : A, R) gSeq =
        ∑ i, j i • AdicCompletion.mk I (⨁ _ : A, R) (u i) := by
    -- Compare the reconstructed completion class stagewise using the explicit equality
    -- `gShift n = ∑ i, j i • uStage i n`.
    apply AdicCompletion.ext_evalₐ (I := I)
    intro n
    simp [gSeq, u, hgStage n, AdicCompletion.evalₐ_mk]
  have hδShift_eq_gSeq :
      AdicCompletion.mk I (⨁ _ : A, R) δShift =
        AdicCompletion.mk I (⨁ _ : A, R) gSeq := by
    -- The shifted approximation errors already vanish in the `n`th quotient.
    apply AdicCompletion.ext_evalₐ (I := I)
    intro n
    apply (Submodule.Quotient.eq (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))).2
    simpa [δShift, gSeq, gShift] using happroxShift n
  have hShift_mem :
      AdicCompletion.mk I (⨁ _ : A, R) δShift ∈
        J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))) := by
    -- The completion class of the shifted sequence is the visible weighted sum of the chosen
    -- generators of `J`.
    rw [hδShift_eq_gSeq, hgSeq_eq]
    exact generator_sum_mem_smul_top
      (R := R) (J := J) (j := j) hj (fun i ↦ AdicCompletion.mk I (⨁ _ : A, R) (u i))
  have hShift_zero :
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).mkQ
        (AdicCompletion.mk I (⨁ _ : A, R) δShift) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero
      (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).2 hShift_mem
  -- The completion class is unchanged by the finite shift, so the original class is already zero.
  simpa [adicCompletion_mk_shift_eq (R := R) (I := I) (A := A) b δ] using hShift_zero

/-- Helper for Lemma 15.27.1: injectivity of the quotient-completion comparison is the remaining
finite-presentation/Artin-Rees input. -/
private theorem completion_quotient_comparison_injective_of_fg
    (J : Ideal R) (hJ : J.FG) :
    Function.Injective (completion_quotient_comparison (R := R) (I := I) (A := A) J) := by
  intro q₁ q₂ hq
  -- Route correction: follow the source proof on one kernel class `q₁ - q₂`, rather than trying
  -- to prove injectivity of the comparison map by an abstract quotient-completeness argument.
  suffices hsub : q₁ - q₂ = 0 by
    exact sub_eq_zero.mp hsub
  have hzero :
      completion_quotient_comparison (R := R) (I := I) (A := A) J (q₁ - q₂) = 0 := by
    -- The linearity of the comparison map turns equality of images into a kernel equation.
    simpa [map_sub, hq]
  obtain ⟨xhat, rfl⟩ := Submodule.mkQ_surjective
    (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))) (q₁ - q₂)
  obtain ⟨f, hf⟩ := AdicCompletion.mk_surjective I (⨁ _ : A, R) xhat
  have hstage :
      ∀ n : ℕ,
        f n ∈ (J • (⊤ : Submodule R (⨁ _ : A, R))) ⊔
          (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) :=
    comparison_zero_stagewise_mem_sup_pow
      (R := R) (I := I) (A := A) J hzero f hf
  obtain ⟨c, hcJ⟩ := ideal_intersection_pow_smul_shift_eq (R := R) (I := I) J
  let S : Finset A := (f c).support
  have hsupport_zero : ∀ a, a ∉ S → f c a = 0 := by
    intro a ha
    simpa [S] using ha
  have hδstage :
      ∀ n : ℕ,
        f (c + n) -
            finsetSupportInclusion (R := R) (A := A) S
              (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n) ∈
          (((J ⊓ I ^ c : Ideal R) • (⊤ : Submodule R (⨁ _ : A, R))) :
              Submodule R (⨁ _ : A, R)) ⊔
            (I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R))) := by
    intro n
    -- This is the stabilized source-proof invariant: outside the frozen support, the shifted stage
    -- lies in the Artin-Rees core `J ∩ I^c` up to `I^(c + n)`.
    exact frozen_support_difference_mem_intersection_add_pow
      (R := R) (I := I) (A := A) J hzero f hf c n S hsupport_zero
  let ηhat : AdicCompletion I (⨁ _ : ↥S, R) :=
    AdicCompletion.mk I (⨁ _ : ↥S, R)
      (restricted_shifted_sequence (R := R) (I := I) (A := A) c S f)
  have hfactor :
      ((((AdicCompletion.map I (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R).quotientMapByIdeal J))
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) =
          ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat)) := by
    let inc : AdicCompletion I (⨁ _ : ↥S, R) →ₗ[R] AdicCompletion I (⨁ _ : A, R) :=
      (AdicCompletion.map I (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R
    let δStage : ℕ → (⨁ _ : A, R) := fun n ↦
      f (c + n) -
        finsetSupportInclusion (R := R) (A := A) S
          (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n)
    have hδcauchy :
        ∀ n : ℕ,
          δStage n ≡ δStage (n + 1) [SMOD I ^ n • (⊤ : Submodule R (⨁ _ : A, R))] := by
      intro n
      rw [SModEq.sub_mem]
      -- The ambient shifted sequence and the restricted shifted sequence are both Cauchy modulo
      -- `I ^ n`, so their difference is again Cauchy at that level.
      have hfstep :
          f (c + n) - f (c + (n + 1)) ∈
            I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
        exact (SModEq.sub_mem).mp
          (shifted_sequence_step (R := R) (I := I) (A := A) c f n)
      have hreststep0 :
          restricted_shifted_stage (R := R) (I := I) (A := A) c S f n -
              restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1) ∈
            I ^ n • (⊤ : Submodule R (⨁ _ : ↥S, R)) := by
        exact (SModEq.sub_mem).mp
          (restricted_shifted_sequence_step (R := R) (I := I) (A := A) c S f n)
      have hreststep :
          finsetSupportInclusion (R := R) (A := A) S
              (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n) -
                finsetSupportInclusion (R := R) (A := A) S
                  (restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1)) ∈
            I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
        have hcomap :
            restricted_shifted_stage (R := R) (I := I) (A := A) c S f n -
                restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1) ∈
              Submodule.comap
                (finsetSupportInclusion (R := R) (A := A) S)
                (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) :=
          (Submodule.smul_top_le_comap_smul_top (I ^ n)
            (finsetSupportInclusion (R := R) (A := A) S)) hreststep0
        simpa [Submodule.mem_comap, map_sub] using hcomap
      have hsub :
          (f (c + n) - f (c + (n + 1))) -
              (finsetSupportInclusion (R := R) (A := A) S
                  (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n) -
                finsetSupportInclusion (R := R) (A := A) S
                  (restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1))) ∈
            I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
        exact Submodule.sub_mem _ hfstep hreststep
      simpa [δStage, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have hδdeep :
        ∀ n : ℕ, δStage n - δStage (n + 1) ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
      intro n
      -- The original representative already has deep `I ^ (c + n)`-control, and the restricted
      -- stage inherits the same depth coordinatewise on the frozen carrier.
      have hfstep :
          f (c + n) - f (c + (n + 1)) ∈
            I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
        exact (SModEq.sub_mem).mp (f.property (Nat.le_succ (c + n)))
      have hreststep0 :
          restricted_shifted_stage (R := R) (I := I) (A := A) c S f n -
              restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1) ∈
            I ^ (c + n) • (⊤ : Submodule R (⨁ _ : ↥S, R)) := by
        exact restricted_shifted_sequence_step_deep
          (R := R) (I := I) (A := A) c S f n
      have hreststep :
          finsetSupportInclusion (R := R) (A := A) S
              (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n) -
                finsetSupportInclusion (R := R) (A := A) S
                  (restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1)) ∈
            I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
        have hcomap :
            restricted_shifted_stage (R := R) (I := I) (A := A) c S f n -
                restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1) ∈
              Submodule.comap
                (finsetSupportInclusion (R := R) (A := A) S)
                (I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R))) :=
          (Submodule.smul_top_le_comap_smul_top (I ^ (c + n))
            (finsetSupportInclusion (R := R) (A := A) S)) hreststep0
        simpa [Submodule.mem_comap, map_sub] using hcomap
      have hsub :
          (f (c + n) - f (c + (n + 1))) -
              (finsetSupportInclusion (R := R) (A := A) S
                  (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n) -
                finsetSupportInclusion (R := R) (A := A) S
                  (restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1))) ∈
            I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
        exact Submodule.sub_mem _ hfstep hreststep
      simpa [δStage, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    let δ : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R) :=
      AdicCompletion.AdicCauchySequence.mk (I := I) (M := (⨁ _ : A, R))
        δStage hδcauchy
    obtain ⟨g, hgK, hδapprox⟩ :=
      frozen_support_difference_has_intersection_lift
        (R := R) (I := I) (A := A) J c δStage (by
          intro n
          simpa [δStage] using hδstage n)
    have hgdeep :
        ∀ n : ℕ, g n - g (n + 1) ∈ I ^ (c + n) • (⊤ : Submodule R (⨁ _ : A, R)) := by
      exact frozen_support_difference_lift_step_deep
        (R := R) (I := I) (A := A) c δStage g hδdeep hδapprox
    have hδzero :
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).mkQ
          (AdicCompletion.mk I (⨁ _ : A, R) δ) = 0 := by
      exact completed_intersection_core_lift_class_zero
        (R := R) (I := I) (A := A) J hJ c δ g hgK hδapprox hgdeep
    have hδeq :
        AdicCompletion.mk I (⨁ _ : A, R) δ = xhat - inc ηhat := by
      -- Compare the frozen-support difference representative with the ambient completion
      -- difference stagewise.
      apply AdicCompletion.ext_evalₐ (I := I)
      intro n
      let stage :=
        finsetSupportInclusion (R := R) (A := A) S
          (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n)
      have hshift :
          Submodule.Quotient.mk (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))
              (f (c + n) - stage) =
            Submodule.Quotient.mk (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))
              (f n - stage) := by
        apply (Submodule.Quotient.eq (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))).2
        have hmem : f (c + n) - f n ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
          exact (SModEq.sub_mem).mp ((f.property (Nat.le_add_left n c)).symm)
        simpa [stage, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmem
      calc
        AdicCompletion.evalₐ I n (AdicCompletion.mk I (⨁ _ : A, R) δ) =
            Submodule.Quotient.mk (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))
              (f (c + n) - stage) := by
                simp [δ, δStage, stage, AdicCompletion.evalₐ_mk]
        _ =
            Submodule.Quotient.mk (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))
              (f n - stage) := hshift
        _ = AdicCompletion.evalₐ I n (xhat - inc ηhat) := by
              simp [hf, inc, ηhat, stage, AdicCompletion.evalₐ_mk, AdicCompletion.map_mk]
    have hmem :
        xhat - inc ηhat ∈ J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))) := by
      have hclass :
          ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).mkQ
            (xhat - inc ηhat) = 0 := by
        simpa [hδeq] using hδzero
      exact (Submodule.Quotient.mk_eq_zero
        (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).1 hclass
    -- The reconstructed source-side class differs from `xhat` by the finite-support image only by
    -- an element of `J • ⊤`, which is exactly the required quotient equality.
    symm
    apply (Submodule.Quotient.eq
      (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).2
    simpa [inc] using hmem
  have hkerS :
      completion_quotient_comparison (R := R) (I := I) (A := ↥S) J
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) = 0 := by
    have htransport := congrArg
      (((AdicCompletion.map I
          ((finsetSupportInclusion (R := R) (A := A) S).quotientMapByIdeal J)).restrictScalars R))
      (completion_quotient_comparison_finset_support_naturality
        (R := R) (I := I) (A := A) J S ▸ rfl)
    have hcomm :
        (((AdicCompletion.map I
            ((finsetSupportInclusion (R := R) (A := A) S).quotientMapByIdeal J)).restrictScalars R)
          (completion_quotient_comparison (R := R) (I := I) (A := ↥S) J
            ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat))) =
        (((AdicCompletion.map I
            ((finsetSupportInclusion (R := R) (A := A) S).quotientMapByIdeal J)).restrictScalars R)
          0) := by
      calc
        (((AdicCompletion.map I
            ((finsetSupportInclusion (R := R) (A := A) S).quotientMapByIdeal J)).restrictScalars R)
          (completion_quotient_comparison (R := R) (I := I) (A := ↥S) J
            ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat))) =
            completion_quotient_comparison (R := R) (I := I) (A := A) J
              ((((AdicCompletion.map I
                  (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R).quotientMapByIdeal J)
                ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat)) := by
                  simpa [LinearMap.comp_apply] using
                    congrArg (fun φ ↦ φ
                      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat))
                      (completion_quotient_comparison_finset_support_naturality
                        (R := R) (I := I) (A := A) J S).symm
        _ =
            completion_quotient_comparison (R := R) (I := I) (A := A) J
              ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) := by
                simpa [LinearMap.quotientMapByIdeal] using congrArg
                  (completion_quotient_comparison (R := R) (I := I) (A := A) J) hfactor
        _ = (((AdicCompletion.map I
            ((finsetSupportInclusion (R := R) (A := A) S).quotientMapByIdeal J)).restrictScalars R) 0) := by
              simp [hzero]
    have hmap_injective :
        Function.Injective
          (((AdicCompletion.map I
              ((finsetSupportInclusion (R := R) (A := A) S).quotientMapByIdeal J)).restrictScalars R)) := by
      exact AdicCompletion.map_injective (I := I) <|
        directSum_coeFn_quotientMapByIdeal_injective (R := R) (A := ↥S) J
    exact hmap_injective <| by simpa using hcomm
  have hηzero :
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) = 0 := by
    exact completion_quotient_comparison_injective_of_fintype
      (R := R) (I := I) (A := ↥S) J hkerS
  apply (Submodule.Quotient.eq
    (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).2
  have hmapzero :
      ((((AdicCompletion.map I (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R).quotientMapByIdeal J))
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) = 0 := by
    rw [hηzero]
    simp
  simpa [LinearMap.quotientMapByIdeal] using hfactor.trans hmapzero

/-- Helper for Lemma 15.27.1: stagewise membership in `J M + I^n M` should force the
corresponding completion class to vanish modulo `J`. -/
private theorem completion_quotient_class_zero_of_stagewise_mem_sup_pow
    (J : Ideal R)
    (hJ : J.FG)
    (δ : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R))
    (hδ :
      ∀ n : ℕ,
        δ n ∈ (J • (⊤ : Submodule R (⨁ _ : A, R))) ⊔
          (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))) :
    ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).mkQ
      (AdicCompletion.mk I (⨁ _ : A, R) δ) = 0 := by
  have hdesc_zero :
      AdicCompletion.map I ((J • (⊤ : Submodule R (⨁ _ : A, R))).mkQ)
        (AdicCompletion.mk I (⨁ _ : A, R) δ) = 0 := by
    -- First close the easy source-faithful part: modulo `J`, every stage already vanishes in the
    -- quotient completion because `δ n ∈ J M + I^n M`.
    exact completion_quotient_eval_zero_of_stagewise_mem_sup_pow
      (R := R) (I := I) (A := A) J δ hδ
  -- The only remaining step is the injectivity of the descended comparison map from the quotient
  -- of the completion to the completion of the quotient.
  apply completion_quotient_comparison_injective_of_fg
    (R := R) (I := I) (A := A) J hJ
  rw [completion_quotient_comparison_apply_mkQ]
  simpa using hdesc_zero

/-- Helper for Lemma 15.27.1: after freezing the support carrier `S`, the difference between the
ambient shifted stage and the included restricted stage already lies in `J M + I^n M`. -/
private theorem support_restricted_stage_difference_mem_ideal_sup_pow
    [DecidableEq A]
    (J : Ideal R) {xhat : AdicCompletion I (⨁ _ : A, R)}
    (hker : (adicCompletionDirectSumToPi I A).quotientMapByIdeal J
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) = 0)
    (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R))
    (hf : AdicCompletion.mk I (⨁ _ : A, R) f = xhat)
    (c n : ℕ) (S : Finset A) :
    f (c + n) -
        finsetSupportInclusion (R := R) (A := A) S
          (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n) ∈
      (J • (⊤ : Submodule R (⨁ _ : A, R))) ⊔
        (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) := by
  let δ : ⨁ _ : A, R :=
    f (c + n) -
      finsetSupportInclusion (R := R) (A := A) S
        (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n)
  have hcoord : ∀ a, δ a ∈ J + (I ^ n : Ideal R) := by
    intro a
    by_cases ha : a ∈ S
    · -- On the frozen support, the restricted stage agrees with the ambient stage exactly.
      have hδ : δ a = 0 := by
        simp [δ, ha, restricted_shifted_stage_apply]
      simpa [hδ]
    · -- Outside the frozen support, the included restricted stage vanishes and the kernel control
      -- gives `J + I^n` membership for the ambient stage.
      have hδ :
          δ a = f (c + n) a := by
        simp [δ, ha]
      simpa [hδ] using
        outside_support_mem_ideal_add_pow
          (R := R) (I := I) (A := A) J hker f hf c n a
  have hmem :
      δ ∈ (J + (I ^ n : Ideal R)) • (⊤ : Submodule R (⨁ _ : A, R)) := by
    exact directSum_mem_smul_top_of_coordinate_mem
      (R := R) (A := A) (J := J + (I ^ n : Ideal R)) δ hcoord
  have hsup :
      (J + (I ^ n : Ideal R)) • (⊤ : Submodule R (⨁ _ : A, R)) =
        (J • (⊤ : Submodule R (⨁ _ : A, R))) ⊔
          (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) := by
    simpa [Ideal.add_eq_sup] using
      (Submodule.sup_smul
        (R := R) (A := R) (M := (⨁ _ : A, R))
        (I := (J : Submodule R R)) (J := (I ^ n : Ideal R))
        (N := (⊤ : Submodule R (⨁ _ : A, R))))
  have hmem' :
      δ ∈ (J • (⊤ : Submodule R (⨁ _ : A, R))) ⊔
        (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) := by
    rwa [hsup] at hmem
  simpa [δ] using hmem'

/-- Helper for Lemma 15.27.1: after freezing one finite support `S`, the shifted restricted
sequence should only be compared with the ambient completion modulo `J`, not by exact equality in
the ambient completion. -/
private theorem fixed_support_quotient_factorization_of_kernel
    [DecidableEq A]
    (J : Ideal R) {xhat : AdicCompletion I (⨁ _ : A, R)}
    (hJ : J.FG)
    (hker : (adicCompletionDirectSumToPi I A).quotientMapByIdeal J
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) = 0)
    (f : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R))
    (hf : AdicCompletion.mk I (⨁ _ : A, R) f = xhat)
    (c : ℕ)
    (S : Finset A)
    (hzero : ∀ a, a ∉ S → f c a = 0) :
    ∃ ηhat : AdicCompletion I (⨁ _ : ↥S, R),
      (((AdicCompletion.map I (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R).quotientMapByIdeal J)
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) =
          ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) := by
  classical
  let ηhat : AdicCompletion I (⨁ _ : ↥S, R) :=
    AdicCompletion.mk I (⨁ _ : ↥S, R)
      (restricted_shifted_sequence (R := R) (I := I) (A := A) c S f)
  refine ⟨ηhat, ?_⟩
  -- Route correction: the exact ambient factorization is false in general, so the remaining
  -- source-faithful work is to prove only quotient-level equality after killing `J`.
  let inc : AdicCompletion I (⨁ _ : ↥S, R) →ₗ[R] AdicCompletion I (⨁ _ : A, R) :=
    (AdicCompletion.map I (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R
  let δ : AdicCompletion.AdicCauchySequence I (⨁ _ : A, R) :=
    AdicCompletion.AdicCauchySequence.mk (I := I) (M := (⨁ _ : A, R))
      (fun n ↦
        f (c + n) -
          finsetSupportInclusion (R := R) (A := A) S
            (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n))
      (fun n ↦ by
        rw [SModEq.sub_mem]
        -- Both summands are shifted Cauchy sequences, so their difference is still Cauchy.
        have hfstep :
            f (c + n) - f (c + (n + 1)) ∈
              I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
          exact (SModEq.sub_mem).mp
            (shifted_sequence_step (R := R) (I := I) (A := A) c f n)
        have hreststep0 :
            restricted_shifted_stage (R := R) (I := I) (A := A) c S f n -
                restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1) ∈
              I ^ n • (⊤ : Submodule R (⨁ _ : ↥S, R)) := by
          exact (SModEq.sub_mem).mp
            (restricted_shifted_sequence_step (R := R) (I := I) (A := A) c S f n)
        have hreststep :
            finsetSupportInclusion (R := R) (A := A) S
                (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n) -
                  finsetSupportInclusion (R := R) (A := A) S
                    (restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1)) ∈
              I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
          have hcomap :
              restricted_shifted_stage (R := R) (I := I) (A := A) c S f n -
                  restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1) ∈
                Submodule.comap
                  (finsetSupportInclusion (R := R) (A := A) S)
                  (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) :=
            (Submodule.smul_top_le_comap_smul_top (I ^ n)
              (finsetSupportInclusion (R := R) (A := A) S)) hreststep0
          simpa [Submodule.mem_comap, map_sub] using hcomap
        have hsub :
            (f (c + n) - f (c + (n + 1))) -
                (finsetSupportInclusion (R := R) (A := A) S
                    (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n) -
                  finsetSupportInclusion (R := R) (A := A) S
                    (restricted_shifted_stage (R := R) (I := I) (A := A) c S f (n + 1))) ∈
              I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
          exact Submodule.sub_mem _ hfstep hreststep
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub)
  have hδstage :
      ∀ n : ℕ,
        δ n ∈ (J • (⊤ : Submodule R (⨁ _ : A, R))) ⊔
          (I ^ n • (⊤ : Submodule R (⨁ _ : A, R))) := by
    intro n
    simpa [δ] using
      support_restricted_stage_difference_mem_ideal_sup_pow
        (R := R) (I := I) (A := A) J hker f hf c n S
  have hδzero :
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).mkQ
        (AdicCompletion.mk I (⨁ _ : A, R) δ) = 0 := by
    exact completion_quotient_class_zero_of_stagewise_mem_sup_pow
      (R := R) (I := I) (A := A) J hJ δ hδstage
  have hδeq :
      AdicCompletion.mk I (⨁ _ : A, R) δ = xhat - inc ηhat := by
    -- Compare the difference representative with the ambient completion difference stagewise.
    apply AdicCompletion.ext_evalₐ (I := I)
    intro n
    let stage :=
      finsetSupportInclusion (R := R) (A := A) S
        (restricted_shifted_stage (R := R) (I := I) (A := A) c S f n)
    have hshift :
        Submodule.Quotient.mk (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))
            (f (c + n) - stage) =
          Submodule.Quotient.mk (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))
            (f n - stage) := by
      apply (Submodule.Quotient.eq (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))).2
      have hmem : f (c + n) - f n ∈ I ^ n • (⊤ : Submodule R (⨁ _ : A, R)) := by
        exact (SModEq.sub_mem).mp ((f.property (Nat.le_add_left n c)).symm)
      simpa [stage, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmem
    calc
      AdicCompletion.evalₐ I n (AdicCompletion.mk I (⨁ _ : A, R) δ) =
          Submodule.Quotient.mk (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))
            (f (c + n) - stage) := by
              simp [δ, stage, AdicCompletion.evalₐ_mk]
      _ =
          Submodule.Quotient.mk (I ^ n • (⊤ : Submodule R (⨁ _ : A, R)))
            (f n - stage) := hshift
      _ = AdicCompletion.evalₐ I n (xhat - inc ηhat) := by
            simp [hf, inc, ηhat, stage, AdicCompletion.evalₐ_mk, AdicCompletion.map_mk]
  have hmem :
      xhat - inc ηhat ∈ J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))) := by
    have hclass :
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).mkQ
          (xhat - inc ηhat) = 0 := by
      simpa [hδeq] using hδzero
    exact (Submodule.Quotient.mk_eq_zero
      (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).1 hclass
  -- The bridge lemma supplies precisely the required quotient equality of the two completion
  -- classes after killing `J`.
  symm
  apply (Submodule.Quotient.eq
    (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).2
  simpa [inc] using hmem

/-- Helper for Lemma 15.27.1: a quotient-level factorization through one finite support carrier
transports an ambient quotient-kernel class to the corresponding finite-support quotient-kernel
class. -/
private theorem restricted_kernel_of_fixed_support_factorization
    [DecidableEq A]
    (J : Ideal R) (S : Finset A)
    {xhat : AdicCompletion I (⨁ _ : A, R)}
    {ηhat : AdicCompletion I (⨁ _ : ↥S, R)}
    (hηq :
      ((((AdicCompletion.map I (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R).quotientMapByIdeal J))
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) =
          ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat))
    (hker : (adicCompletionDirectSumToPi I A).quotientMapByIdeal J
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) = 0) :
    (adicCompletionDirectSumToPi I (↥S)).quotientMapByIdeal J
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) = 0 := by
  let inc : AdicCompletion I (⨁ _ : ↥S, R) →ₗ[R] AdicCompletion I (⨁ _ : A, R) :=
    (AdicCompletion.map I (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R
  -- Quotient the factorization equality first, then rewrite the finite-support square on the
  -- quotient level before using the ambient kernel hypothesis.
  have hrhs :
      (((restrictCoordinates (R := R) (A := A) S).comp
          (adicCompletionDirectSumToPi I A)).quotientMapByIdeal J)
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) = 0 := by
    -- Postcompose the ambient kernel equality with the quotient of the coordinate restriction map.
    simpa [quotientMapByIdeal_comp] using congrArg
      (((restrictCoordinates (R := R) (A := A) S).quotientMapByIdeal J)) hker
  have htransport :
      ((((restrictCoordinates (R := R) (A := A) S).comp
          (adicCompletionDirectSumToPi I A)).comp
          inc).quotientMapByIdeal J)
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) =
      (((restrictCoordinates (R := R) (A := A) S).comp
          (adicCompletionDirectSumToPi I A)).quotientMapByIdeal J)
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) := by
    -- Apply the ambient restricted quotient map to the quotient-level factorization.
    simpa [quotientMapByIdeal_comp] using congrArg
      ((((restrictCoordinates (R := R) (A := A) S).comp
          (adicCompletionDirectSumToPi I A)).quotientMapByIdeal J))
      hηq
  calc
    (adicCompletionDirectSumToPi I (↥S)).quotientMapByIdeal J
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) =
      (((restrictCoordinates (R := R) (A := A) S).comp
          (adicCompletionDirectSumToPi I A)).quotientMapByIdeal J)
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) := by
          simpa [inc, quotientMapByIdeal_comp,
            restrictCoordinates_comp_adicCompletionDirectSumToPi_finset_support
              (R := R) (I := I) (A := A) S] using htransport
    _ = 0 := hrhs

/-- Helper for Lemma 15.27.1: once the fixed-support factorization lands in the finite-support
kernel, finite-type injectivity forces the original quotient kernel class to vanish. -/
private theorem kernel_class_zero_of_fixed_support_factorization
    [DecidableEq A]
    (J : Ideal R) (S : Finset A)
    {xhat : AdicCompletion I (⨁ _ : A, R)}
    {ηhat : AdicCompletion I (⨁ _ : ↥S, R)}
    (hηq :
      ((((AdicCompletion.map I (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R).quotientMapByIdeal J))
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) =
          ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat))
    (hkerS : (adicCompletionDirectSumToPi I (↥S)).quotientMapByIdeal J
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) = 0) :
    ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) = 0 := by
  let inc : AdicCompletion I (⨁ _ : ↥S, R) →ₗ[R] AdicCompletion I (⨁ _ : A, R) :=
    (AdicCompletion.map I (finsetSupportInclusion (R := R) (A := A) S)).restrictScalars R
  -- The finite-support endpoint is injective modulo `J`, so the restricted quotient class is
  -- already zero. Push that zero forward along the inclusion factorization.
  have hηclass :
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) = 0 := by
    have hkerS' :
        (adicCompletionDirectSumToPi I (↥S)).quotientMapByIdeal J
          ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) =
        (adicCompletionDirectSumToPi I (↥S)).quotientMapByIdeal J 0 := by
      simpa using hkerS
    exact
      (adicCompletionDirectSumToPi_quotient_injective_of_fintype
        (R := R) (I := I) (A := ↥S) J) hkerS'
  have hmapzero :
      (inc.quotientMapByIdeal J)
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) = 0 := by
    rw [hηclass]
    exact map_zero (inc.quotientMapByIdeal J)
  calc
    ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ xhat) =
        (inc.quotientMapByIdeal J)
          ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) := by
            simpa [inc, LinearMap.quotientMapByIdeal] using hηq.symm
    _ = 0 := hmapzero

-- Proof sketch: the product module `A → R` is flat by `Module.noetherian_pi_flat_and_mittagLeffler`,
-- so the owner criterion `LinearMap.universallyInjective_iff_injective_mod_finite_ideal` reduces
-- the goal to injectivity modulo finitely generated ideals. For such an ideal, test after
-- tensoring with the finite quotient module, use completion exactness together with Artin-Rees to
-- control lifts through the completed direct sum, and identify the resulting comparison map with
-- the coordinatewise inclusion via the canonical computation
-- `adicCompletionDirectSumToPi_comp_of I A`.
/-- Lemma 15.27.1: if `R` is Noetherian and `I`-adically complete, then the canonical map from the
`I`-adic completion of `⨁ a, R` to the product `∀ a, R` is universally injective. -/
theorem adicCompletionDirectSumToPi_universallyInjective :
    (adicCompletionDirectSumToPi I A).UniversallyInjective := by
  letI : Module.Flat R (A → R) :=
    (Module.noetherian_pi_flat_and_mittagLeffler : _
      ∧ Module.MittagLeffler R (A → R)).1
  -- Route correction: the finite endpoint is now frozen by
  -- `adicCompletionDirectSumToPi_linearEquiv_of_fintype`, so the only remaining source-faithful
  -- work is to factor a kernel class modulo `J` through one fixed finite support carrier.
  -- The owner criterion reduces universal injectivity to injectivity modulo finitely generated
  -- ideals, so the remaining work is the fixed-`J` Artin-Rees analysis of the kernel.
  refine (universallyInjective_iff_injective_mod_finite_ideal
    (adicCompletionDirectSumToPi I A)).2 ?_
  intro J hJ
  obtain ⟨c, hcJ⟩ := ideal_intersection_pow_smul_shift_eq (R := R) (I := I) J
  intro x y hxy
  refine Quotient.inductionOn₂' x y ?_ hxy
  intro xhat yhat hxy
  classical
  -- Reduce equality of quotient classes to the vanishing of the difference class.
  have hker :
      (adicCompletionDirectSumToPi I A).quotientMapByIdeal J
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ (xhat - yhat)) = 0 := by
    have hxy' :
        (J • (⊤ : Submodule R (A → R))).mkQ (adicCompletionDirectSumToPi I A xhat) =
          (J • (⊤ : Submodule R (A → R))).mkQ (adicCompletionDirectSumToPi I A yhat) := by
      simpa [LinearMap.quotientMapByIdeal] using hxy
    change
      (J • (⊤ : Submodule R (A → R))).mkQ
          (adicCompletionDirectSumToPi I A (xhat - yhat)) = 0
    rw [map_sub]
    simpa using sub_eq_zero.mpr hxy'
  -- Freeze one representative sequence at the Artin-Rees stage `c` and its finite support.
  obtain ⟨f, hf⟩ := AdicCompletion.mk_surjective I (⨁ _ : A, R) (xhat - yhat)
  let S : Finset A := (f c).support
  have hzero : ∀ a, a ∉ S → f c a = 0 := by
    intro a ha
    simpa [S] using ha
  obtain ⟨ηhat, hηq⟩ :=
    fixed_support_quotient_factorization_of_kernel
      (R := R) (I := I) (A := A) J hJ hker f hf c S hzero
  -- Transport the ambient kernel class to the finite-support completion and kill it there.
  have hkerS :
      (adicCompletionDirectSumToPi I (↥S)).quotientMapByIdeal J
        ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : ↥S, R)))).mkQ ηhat) = 0 :=
    restricted_kernel_of_fixed_support_factorization
      (R := R) (I := I) (A := A) J S hηq hker
  have hzeroDiff :
      ((J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R)))).mkQ (xhat - yhat)) = 0 := by
    exact kernel_class_zero_of_fixed_support_factorization
      (R := R) (I := I) (A := A) J S hηq hkerS
  apply (Submodule.Quotient.eq
    (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).2
  exact (Submodule.Quotient.mk_eq_zero
    (J • (⊤ : Submodule R (AdicCompletion I (⨁ _ : A, R))))).1 hzeroDiff

end
