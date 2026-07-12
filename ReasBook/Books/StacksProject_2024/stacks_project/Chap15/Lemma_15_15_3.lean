import Mathlib
import StacksProject_2024.Chap10.Definition_10_82_1
import StacksProject_2024.Chap10.Lemma_10_82_9
import StacksProject_2024.Chap10.Lemma_10_82_10
import StacksProject_2024.Chap10.Lemma_10_82_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {N : Type v} [AddCommGroup N] [Module R N] [Module.Projective R N]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]

/- Domain triage:
- primary domain: universal injectivity of linear maps between projective modules over a
  commutative ring;
- sampled owner declarations:
  `LinearMap.UniversallyInjective`,
  `LinearMap.universallyInjective_iff_injective_mod_finite_ideal`,
  `proper_fg_ideal_annihilator_ne_bot_tfae`;
- best owner abstraction: `LinearMap.UniversallyInjective`;
- primitive data: the ring `R`, the projective modules `N` and `M`, and a linear map `u : N →ₗ[R] M`;
- derived API: the source-facing criterion below, with the `injective → universallyInjective`
  direction obtained canonically from clause `(1) ↔ (2)` of
  `proper_fg_ideal_annihilator_ne_bot_tfae`.

Layering:
- `source-facing`: the theorem below;
- `core/canonical`: `LinearMap.UniversallyInjective`;
- `bridge/view`: `proper_fg_ideal_annihilator_ne_bot_tfae`.
-/

-- Proof sketch: the forward implication holds for any ring by taking the tensor factor `Q = R`.
-- For the converse, use projectivity to split both source and target off free modules, reduce to
-- finite free source by expressing a projective module as a filtered colimit of finite free
-- modules, and then prove the finite free case by induction on the rank using property `(P)` to
-- split off the first basis vector.
/-- Helper for Lemma 15.15.3: an injective map from a free rank-one module into a finite free
module splits. -/
lemma split_of_injective_rank_one_to_fin
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R))
    {n : ℕ} (v : R →ₗ[R] (Fin n → R)) (hv : Function.Injective v) :
    ∃ r : (Fin n → R) →ₗ[R] R, r.comp v = LinearMap.id := by
  let f : Fin n → R := fun i ↦ v 1 i
  let I : Ideal R := Ideal.span (Set.range f)
  have hv_smul : ∀ a : R, v a = a • v 1 := by
    intro a
    calc
      v a = v (a • (1 : R)) := by simp
      _ = a • v 1 := by rw [LinearMap.map_smul]
  -- Property `(P)` forces the coordinate ideal of `v 1` to be the unit ideal.
  have hI_top : I = ⊤ := by
    by_contra hI_proper
    have hIfg : I.FG := by
      simpa [I] using (Submodule.fg_span (Set.finite_range f) : (Ideal.span (Set.range f)).FG)
    have hAnn_nonbot : I.annihilator ≠ (⊥ : Ideal R) := hP hIfg hI_proper
    have hAnn_witness : ∃ a : R, a ∈ I.annihilator ∧ a ≠ 0 := by
      by_contra hnone
      have hAnn_bot : I.annihilator = (⊥ : Ideal R) := by
        ext a
        constructor
        · intro ha
          by_cases ha_zero : a = 0
          · simpa [ha_zero]
          · exact False.elim <| hnone ⟨a, ha, ha_zero⟩
        · intro ha
          rw [Ideal.mem_bot] at ha
          simpa [ha] using (show (0 : R) ∈ I.annihilator from zero_mem _)
      exact hAnn_nonbot hAnn_bot
    rcases hAnn_witness with ⟨a, ha, ha_ne_zero⟩
    rw [Submodule.mem_annihilator] at ha
    have hva_zero : v a = 0 := by
      ext i
      have hmem : f i ∈ I := by
        simpa [I] using (Ideal.subset_span (Set.mem_range_self i) : f i ∈ Ideal.span (Set.range f))
      have hcoord : a * f i = 0 := by
        simpa using ha (f i) hmem
      calc
        (v a) i = (a • v 1) i := by rw [hv_smul]
        _ = a * f i := by simp [f]
        _ = 0 := hcoord
    exact ha_ne_zero <| hv <| by simpa using hva_zero
  have hsurj : Function.Surjective (Fintype.linearCombination R f) := by
    simpa [I] using (span_range_eq_top_iff_surjective_fintypeLinearCombination R f).1 hI_top
  rcases hsurj 1 with ⟨coeff, hcoeff⟩
  let r : (Fin n → R) →ₗ[R] R := Fintype.linearCombination R coeff
  have hr : r (v 1) = 1 := by
    calc
      r (v 1) = ∑ i, (v 1) i * coeff i := by
        simp [r, Fintype.linearCombination_apply]
      _ = ∑ i, coeff i * (v 1) i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [mul_comm]
      _ = 1 := by
        simpa [f, Fintype.linearCombination_apply] using hcoeff
  refine ⟨r, ?_⟩
  -- A retraction is determined by sending `v 1` back to `1`.
  apply LinearMap.ext
  intro a
  calc
    (r.comp v) a = r (a • v 1) := by rw [LinearMap.comp_apply, hv_smul]
    _ = a • r (v 1) := by rw [LinearMap.map_smul]
    _ = a := by simpa [hr]

/-- Helper for Lemma 15.15.3: an injective map from a free rank-one module into a projective
module splits after passing to a free ambient retract and restricting to the finite support of the
image of `1`. -/
lemma split_of_injective_rank_one_to_projective
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R))
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Projective R P]
    (v : R →ₗ[R] P) (hv : Function.Injective v) :
    ∃ r : P →ₗ[R] R, r.comp v = LinearMap.id := by
  classical
  obtain ⟨F, _, _, _, i, s, hs⟩ :=
    Module.Projective.iff_split.mp (inferInstance : Module.Projective R P)
  letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R
  let b := Module.Free.chooseBasis R F
  let x : F := i (v 1)
  let t : Finset (Module.Free.ChooseBasisIndex R F) := (b.repr x).support
  let π : F →ₗ[R] (↑t → R) := LinearMap.pi fun j ↦ b.coord j
  have hi : Function.Injective i := by
    intro p q hpq
    have hsq : s (i p) = s (i q) := congrArg s hpq
    have hcomp : (s.comp i) p = (s.comp i) q := by
      simpa [LinearMap.comp_apply] using hsq
    simpa [hs] using hcomp
  have hiv_smul : ∀ a : R, (i.comp v) a = a • x := by
    intro a
    calc
      (i.comp v) a = (i.comp v) (a • (1 : R)) := by simp
      _ = a • (i.comp v) 1 := by rw [LinearMap.map_smul]
      _ = a • x := by rfl
  have hcoord_zero_outside :
      ∀ {a : R} {j : Module.Free.ChooseBasisIndex R F}, j ∉ t →
        b.coord j ((i.comp v) a) = 0 := by
    intro a j hj
    have hxj : b.coord j x = 0 := by
      exact Finsupp.notMem_support_iff.mp hj
    calc
      b.coord j ((i.comp v) a) = b.coord j (a • x) := by rw [hiv_smul]
      _ = a * b.coord j x := by simp
      _ = 0 := by simp [hxj]
  have hπ_injective : Function.Injective (π.comp (i.comp v)) := by
    intro a a' hEq
    have hzero : (i.comp v) (a - a') = 0 := by
      apply (b.forall_coord_eq_zero_iff).1
      intro j
      by_cases hj : j ∈ t
      · have hcoord_eq :
            b.coord j ((i.comp v) a) = b.coord j ((i.comp v) a') := by
          exact congrArg (fun z : (↑t → R) => z ⟨j, hj⟩) hEq
        calc
          b.coord j ((i.comp v) (a - a')) =
              b.coord j ((i.comp v) a - (i.comp v) a') := by simp
          _ = b.coord j ((i.comp v) a) - b.coord j ((i.comp v) a') := by simp
          _ = 0 := by exact sub_eq_zero.mpr hcoord_eq
      · exact hcoord_zero_outside (a := a - a') hj
    have hiv : Function.Injective (i.comp v) := hi.comp hv
    have hzero' : (i.comp v) (a - a') = (i.comp v) 0 := by
      simpa using hzero
    exact sub_eq_zero.mp (hiv hzero')
  let e : (↑t → R) ≃ₗ[R] (Fin (Fintype.card ↑t) → R) :=
    LinearEquiv.funCongrLeft R R (Fintype.equivFin ↑t).symm
  have he_injective : Function.Injective (e.toLinearMap.comp (π.comp (i.comp v))) :=
    e.injective.comp hπ_injective
  rcases split_of_injective_rank_one_to_fin hP
      (e.toLinearMap.comp (π.comp (i.comp v))) he_injective with
    ⟨rfin, hrfin⟩
  let r : P →ₗ[R] R := rfin.comp (e.toLinearMap.comp (π.comp i))
  refine ⟨r, ?_⟩
  -- Compose the finite-support retraction back through the ambient retract.
  apply LinearMap.ext
  intro a
  simpa [r, LinearMap.comp_assoc] using LinearMap.congr_fun hrfin a

/-- Helper for Lemma 15.15.3: an injective map from a finite free module with basis indexed by
`Fin n` into a projective module admits a retraction. -/
lemma split_of_injective_fin_to_projective
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)) :
    ∀ {P : Type*} [AddCommGroup P] [Module R P] [Module.Projective R P] {n : ℕ},
      (v : (Fin n → R) →ₗ[R] P) → Function.Injective v →
        ∃ r : P →ₗ[R] (Fin n → R), r.comp v = LinearMap.id := sorry

/-- Helper for Lemma 15.15.3: reindexing a finite free source does not affect the existence of a
retraction for an injective map into a projective module. -/
lemma split_of_injective_finite_free_to_projective
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R))
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Projective R P]
    {α : Type*} [Fintype α] (v : (α → R) →ₗ[R] P) (hv : Function.Injective v) :
    ∃ r : P →ₗ[R] (α → R), r.comp v = LinearMap.id := by
  let e : (Fin (Fintype.card α) → R) ≃ₗ[R] (α → R) :=
    LinearEquiv.funCongrLeft (R := R) (M := R) (Fintype.equivFin α)
  have he_injective : Function.Injective (v.comp e.toLinearMap) := hv.comp e.injective
  rcases split_of_injective_fin_to_projective hP (v := v.comp e.toLinearMap) he_injective with
    ⟨rfin, hrfin⟩
  let r : P →ₗ[R] (α → R) := e.toLinearMap.comp rfin
  refine ⟨r, ?_⟩
  -- Evaluate the transported retraction pointwise on the `Fin`-coordinates of an arbitrary source
  -- vector.
  ext x i
  have hx := LinearMap.congr_fun hrfin (e.symm x)
  simpa [r, LinearMap.comp_apply] using congrArg (fun y ↦ e y i) hx

/-- Helper for Lemma 15.15.3: the linear map assembling basis vectors from a finite subset of a
chosen basis. -/
noncomputable def basis_subset_inclusion
    {F : Type*} [AddCommGroup F] [Module R F] {ι : Type*} (b : Module.Basis ι R F)
    (t : Finset ι) :
    (↑t → R) →ₗ[R] F :=
  (Pi.basisFun R ↑t).constr R fun j ↦ b j.1

/-- Helper for Lemma 15.15.3: the coordinate projection onto a finite subset of a chosen basis. -/
noncomputable def basis_subset_projection
    {F : Type*} [AddCommGroup F] [Module R F] {ι : Type*} (b : Module.Basis ι R F)
    (t : Finset ι) :
    F →ₗ[R] (↑t → R) :=
  LinearMap.pi fun j ↦ b.coord j.1

/-- Helper for Lemma 15.15.3: the coordinates of `basis_subset_inclusion` are the given
coordinates on the chosen finite subset and vanish outside it. -/
lemma basis_subset_inclusion_repr
    {F : Type*} [AddCommGroup F] [Module R F] {ι : Type*} [DecidableEq ι]
    (b : Module.Basis ι R F)
    (t : Finset ι) (f : ↑t → R) (i : ι) :
    (b.repr (basis_subset_inclusion (R := R) b t f)) i =
      if hi : i ∈ t then f ⟨i, hi⟩ else 0 := sorry

/-- Helper for Lemma 15.15.3: the finite-support projection is a left inverse to the finite-support
inclusion. -/
lemma basis_subset_projection_comp_inclusion
    {F : Type*} [AddCommGroup F] [Module R F] {ι : Type*} (b : Module.Basis ι R F)
    (t : Finset ι) :
    (basis_subset_projection (R := R) b t).comp (basis_subset_inclusion (R := R) b t) =
      LinearMap.id := sorry

/-- Helper for Lemma 15.15.3: an element is recovered from the coordinates on any finite subset of
the chosen basis containing its support. -/
lemma basis_subset_inclusion_projection_eq
    {F : Type*} [AddCommGroup F] [Module R F] {ι : Type*} (b : Module.Basis ι R F) (t : Finset ι)
    (x : F) (hx : (b.repr x).support ⊆ t) :
    basis_subset_inclusion (R := R) b t (basis_subset_projection (R := R) b t x) = x := sorry

/-- Helper for Lemma 15.15.3: the stabilization map attached to split source data is injective. -/
lemma stabilization_injective_of_split_source
    {L : Type*} [AddCommGroup L] [Module R L]
    (i : N →ₗ[R] L) (s : L →ₗ[R] N) (hs : s.comp i = LinearMap.id)
    (u : N →ₗ[R] M) (hu : Function.Injective u) :
    Function.Injective ((u.comp s).prod (LinearMap.id - i.comp s)) := by
  intro x y hxy
  have hfst : u (s x) = u (s y) := by
    exact congrArg Prod.fst hxy
  have hsnd : x - i (s x) = y - i (s y) := by
    exact congrArg Prod.snd hxy
  have hsxy : s x = s y := hu hfst
  have hixy : i (s x) = i (s y) := congrArg i hsxy
  calc
    x = (x - i (s x)) + i (s x) := by abel
    _ = (y - i (s y)) + i (s y) := by rw [hsnd, hixy]
    _ = y := by abel

/-- Helper for Lemma 15.15.3: a split inclusion is universally injective because its composite
with the retraction is the identity. -/
lemma universallyInjective_of_split_source
    {L : Type*} [AddCommGroup L] [Module R L]
    (i : N →ₗ[R] L) (s : L →ₗ[R] N) (hs : s.comp i = LinearMap.id) :
    UniversallyInjective i := by
  -- Tensoring preserves the split identity, so injectivity descends from the identity map.
  intro Q _ _
  have hcomp : Function.Injective ((s.comp i).rTensor Q) := by
    simpa [LinearMap.rTensor_comp, hs] using
      (universallyInjective_id (R := R) (M := N)) Q inferInstance inferInstance
  intro x y hxy
  have hxy' : ((s.comp i).rTensor Q) x = ((s.comp i).rTensor Q) y := by
    simpa [LinearMap.rTensor_comp] using congrArg (s.rTensor Q) hxy
  exact hcomp hxy'

/-- Helper for Lemma 15.15.3: an injective map from a free module into a projective module is
universally injective. -/
lemma universallyInjective_of_injective_free_source
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R))
    {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    (v : F →ₗ[R] M) (hv : Function.Injective v) :
    UniversallyInjective v := sorry

/-- Helper for Lemma 15.15.3: universal injectivity descends from the stabilized left inclusion to
the original map. -/
lemma universallyInjective_of_inl_comp
    {L : Type z} [AddCommGroup L] [Module R L] (u : N →ₗ[R] M) :
    UniversallyInjective.{u, v, max w z, u} ((LinearMap.inl R M L).comp u) →
      UniversallyInjective.{u, v, w, u} u := by
  unfold UniversallyInjective
  intro hu
  -- Tensoring the stabilized inclusion is still a composition, so injectivity of the composite
  -- forces injectivity of the original tensor map.
  intro Q _ _
  have hcomp : Function.Injective ((((LinearMap.inl R M L).comp u).rTensor Q)) :=
    hu Q inferInstance inferInstance
  intro x y hxy
  apply hcomp
  simpa [LinearMap.rTensor_comp] using congrArg ((LinearMap.inl R M L).rTensor Q) hxy

/-- Helper for Lemma 15.15.3: once the source splits off a free module, the stabilization map
into `M × L` reduces universal injectivity of `u` to the free-source case. -/
lemma universallyInjective_of_injective_of_split_source
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R))
    {L : Type z} [AddCommGroup L] [Module R L] [Module.Free R L]
    (i : N →ₗ[R] L) (s : L →ₗ[R] N) (hs : s.comp i = LinearMap.id)
    (u : N →ₗ[R] M) (hu : Function.Injective u) :
    UniversallyInjective.{u, v, w, u} u := by
  let w : L →ₗ[R] M × L := (u.comp s).prod (LinearMap.id - i.comp s)
  have hw : Function.Injective w :=
    stabilization_injective_of_split_source i s hs u hu
  have hw_univ : UniversallyInjective w :=
    universallyInjective_of_injective_free_source hP w hw
  have hi_univ : UniversallyInjective i :=
    universallyInjective_of_split_source i s hs
  have hcomp : (LinearMap.inl R M L).comp u = w.comp i := by
    -- Evaluate both composites on the split source and use `s ∘ i = id`.
    ext x
    · have hs_apply : s (i x) = x := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hs x
      simp [w, LinearMap.comp_apply, hs_apply]
    · have hs_apply : s (i x) = x := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hs x
      simp [w, LinearMap.comp_apply, hs_apply]
  -- First transport universal injectivity to the stabilized composite, then descend along the
  -- left inclusion.
  have hwi : UniversallyInjective.{u, v, max w z, u} ((LinearMap.inl R M L).comp u) := by
    intro Q _ _
    have hwq : Function.Injective (w.rTensor Q) :=
      hw_univ Q inferInstance inferInstance
    have hiq : Function.Injective (i.rTensor Q) :=
      hi_univ Q inferInstance inferInstance
    simpa [hcomp, LinearMap.rTensor_comp] using hwq.comp hiq
  exact universallyInjective_of_inl_comp (u := u) hwi

/-- Lemma 15.15.3: if `R` has property `(P)` of Lemma 15.15.2, meaning every proper finitely
generated ideal of `R` has nonzero annihilator, then a homomorphism `u : N →ₗ[R] M` of
projective `R`-modules is universally injective if and only if it is injective. -/
theorem universallyInjective_iff_injective_of_projective_of_proper_fg_ideal_annihilator_ne_bot
    (hP : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)) (u : N →ₗ[R] M) :
    UniversallyInjective.{u, v, w, u} u ↔ Function.Injective u := by
  constructor
  · intro hu x y hxy
    -- Specialize universal injectivity to the base ring and identify `M ⊗[R] R` with `M`.
    have hu' : UniversallyInjective.{u, v, w, u} u := hu
    have hrtensor : Function.Injective (u.rTensor R) :=
      hu' R inferInstance inferInstance
    have hxy' :
        u.rTensor R ((TensorProduct.rid R N).symm x) =
          u.rTensor R ((TensorProduct.rid R N).symm y) := by
      apply (TensorProduct.rid R M).injective
      simp [TensorProduct.rid_symm_apply, LinearMap.rTensor_tmul, hxy]
    exact (TensorProduct.rid R N).symm.injective <| hrtensor hxy'
  · intro hu
    -- Route correction: remove the later-item shortcut through `Lemma_15_15_4`.
    -- Split the projective source off a free module and apply the stabilization helper.
    obtain ⟨L, _, _, _, i, s, hs⟩ :=
      Module.Projective.iff_split.mp (inferInstance : Module.Projective R N)
    letI : AddCommGroup L := Module.addCommMonoidToAddCommGroup R
    exact universallyInjective_of_injective_of_split_source hP (i := i) (s := s) hs u hu

end

end LinearMap
