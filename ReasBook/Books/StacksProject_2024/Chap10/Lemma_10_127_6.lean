import StacksProject_2024.Chap10.Lemma_10_127_5

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x y

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (R : I → Type v) [∀ i, CommRing (R i)]
variable (f : ∀ i j, i ≤ j → R i →+* R j)
variable [DirectedSystem R (fun i j hij ↦ (f i j hij : R i →+* R j))]

local notation "ρ" => (fun i j hij ↦ (f i j hij : R i →+* R j))
local notation "R∞" => Ring.DirectLimit R ρ

/-!
Domain sampling:
* Primary domain: module descent along directed colimits of commutative rings.
* Sampled owner declarations:
  - `baseChangeLinearMap_descends_of_finitePresentation`
  - `baseChange_eventually_eq_of_finite`
  - the mathlib instance `[Module.FinitePresentation R M] : Module.Finite R M`
* Best owner abstraction: the module-colimit descent API from `Lemma_10_127_5`.
* Layer triage:
  - `source-facing`: the three numbered statements below
  - `core/canonical`: the owner descent theorems from `Lemma_10_127_5`
  - `bridge/view`: the internal tail restriction `j ≥ i`, together with the canonical stage maps
    into `R∞`
* Primitive vs. derived:
  - primitive data here are only the original directed system and its modules over a chosen stage
  - the stage-to-`R∞` scalar-tower compatibility and any tail-system comparison are derived bridge
    data, so they stay local
-/

private noncomputable instance stageDirectLimitAlgebra (i : I) : Algebra (R i) R∞ :=
  (Ring.DirectLimit.of R ρ i).toAlgebra

private theorem directLimitStage_isScalarTower {i j : I} (hij : i ≤ j) :
    let _ : Algebra (R i) (R j) := (f i j hij).toAlgebra
    let _ : Algebra (R j) R∞ := stageDirectLimitAlgebra R f j
    IsScalarTower (R i) (R j) R∞ := by
  let _ : Algebra (R i) (R j) := (f i j hij).toAlgebra
  let _ : Algebra (R j) R∞ := stageDirectLimitAlgebra R f j
  -- Proof comment: both scalar-tower composites are the canonical maps from stage `i` into the
  -- direct limit, so `Ring.DirectLimit.of_f` identifies them.
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext x
  change Ring.DirectLimit.of R ρ i x = Ring.DirectLimit.of R ρ j ((f i j hij) x)
  simpa using (Ring.DirectLimit.of_f hij x).symm

/-- Helper for Lemma 10.127.6: finitely many direct-limit elements already come from one stage. -/
private theorem finite_family_descends_to_stage {α : Type*} [Finite α] (z : α → R∞) :
    ∃ (i : I) (z_i : α → R i), ∀ a, Ring.DirectLimit.of R ρ i (z_i a) = z a := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  let s : Finset α := Finset.univ
  have hs :
      ∀ t : Finset α,
        ∃ (i : I) (z_i : α → R i), ∀ a ∈ t, Ring.DirectLimit.of R ρ i (z_i a) = z a := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        refine ⟨Classical.arbitrary I, fun _ ↦ 0, ?_⟩
        intro a ha
        simp at ha
    | @insert a t ha ht =>
        obtain ⟨i, a_i, ha_i⟩ := Ring.DirectLimit.exists_of (G := R) (f := ρ) (z a)
        rcases ht with ⟨j, z_j, hz_j⟩
        rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
        let z_k : α → R k :=
          Function.update (fun b ↦ (f j k hjk) (z_j b)) a ((f i k hik) a_i)
        refine ⟨k, z_k, ?_⟩
        intro b hb
        by_cases hba : b = a
        · subst b
          simp [z_k]
          exact ha_i
        · simp [z_k, hba]
          exact hz_j b (by simpa [hba] using hb)
  rcases hs s with ⟨i, z_i, hz_i⟩
  refine ⟨i, z_i, ?_⟩
  intro a
  simpa [s] using hz_i a (Finset.mem_univ a)

/-- Helper for Lemma 10.127.6: a linear map between finite free modules over the direct limit
already comes from one stage. -/
private theorem finite_free_linearMap_descends_to_stage {m n : ℕ}
    (r : (Fin m → R∞) →ₗ[R∞] (Fin n → R∞)) :
    ∃ (i : I) (r_i : (Fin m → R i) →ₗ[R i] (Fin n → R i)),
      ∀ a b,
        Ring.DirectLimit.of R ρ i (r_i (Pi.basisFun (R i) (Fin m) a) b) =
          r (Pi.basisFun R∞ (Fin m) a) b := by
  classical
  let coeffs : Fin m × Fin n → R∞ := fun p ↦ r (Pi.basisFun R∞ (Fin m) p.1) p.2
  obtain ⟨i, coeffs_i, hcoeffs_i⟩ :=
    finite_family_descends_to_stage (R := R) (f := f) coeffs
  let vectors_i : Fin m → Fin n → R i := fun a b ↦ coeffs_i (a, b)
  let r_i : (Fin m → R i) →ₗ[R i] (Fin n → R i) :=
    (Pi.basisFun (R i) (Fin m)).constr (R i) vectors_i
  refine ⟨i, r_i, ?_⟩
  intro a b
  have hbasis : r_i (Pi.basisFun (R i) (Fin m) a) b = vectors_i a b := by
    simpa [r_i, vectors_i] using
      congrArg (fun g : Fin n → R i ↦ g b)
        ((Pi.basisFun (R i) (Fin m)).constr_basis (R i) vectors_i a)
  have hbasis' :
      Ring.DirectLimit.of R ρ i (r_i (Pi.basisFun (R i) (Fin m) a) b) =
        Ring.DirectLimit.of R ρ i (vectors_i a b) := by
    exact congrArg (Ring.DirectLimit.of R ρ i) hbasis
  exact hbasis'.trans (hcoeffs_i (a, b))

/-- Helper for Lemma 10.127.6: base changing a finite free module from a stage to the direct
limit recovers the corresponding finite free module over the direct limit. -/
private theorem descended_free_module_equiv
    (i : I) (n : ℕ) :
    ∃ e : R∞ ⊗[R i] (Fin n → R i) ≃ₗ[R∞] (Fin n → R∞),
      (∀ v b,
        e ((1 : R∞) ⊗ₜ[R i] v) b = Ring.DirectLimit.of R ρ i (v b)) ∧
      (∀ a,
        e.symm (Pi.basisFun R∞ (Fin n) a) =
          (1 : R∞) ⊗ₜ[R i] Pi.basisFun (R i) (Fin n) a) := by
  classical
  let e : R∞ ⊗[R i] (Fin n → R i) ≃ₗ[R∞] (Fin n → R∞) :=
    Algebra.TensorProduct.equivPiOfFiniteBasis (A := R∞) (R := R i)
      (V := Fin n → R i) (Pi.basisFun (R i) (Fin n))
  refine ⟨e, ?_⟩
  refine ⟨?_, ?_⟩
  · intro v b
    -- Proof comment: on a pure tensor `1 ⊗ v`, the finite-free tensor equivalence is just the
    -- stage map applied coordinatewise.
    rw [show Ring.DirectLimit.of R ρ i (v b) = algebraMap (R i) R∞ (v b) by rfl]
    rw [Algebra.TensorProduct.equivPiOfFiniteBasis_apply]
    calc
      v b • (1 : R∞) = algebraMap (R i) R∞ (v b) * 1 := by rw [Algebra.smul_def]
      _ = algebraMap (R i) R∞ (v b) := by simp
  · intro a
    -- Proof comment: to recover the inverse formula, apply the equivalence and compare on each
    -- standard basis vector of the target free module.
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    ext b
    rw [Algebra.TensorProduct.equivPiOfFiniteBasis_apply]
    rw [Pi.basisFun_apply]
    by_cases h : a = b
    · subst h
      simp [Algebra.smul_def]
    · simp [h, Algebra.smul_def]

/-- Helper for Lemma 10.127.6: after identifying the base-changed finite free modules with the
direct-limit finite free modules, the descended relation map becomes the original one. -/
private theorem descended_presentation_relation_map_rebase_eq
    {m n : ℕ} {i : I}
    (r : (Fin m → R∞) →ₗ[R∞] (Fin n → R∞))
    (r_i : (Fin m → R i) →ₗ[R i] (Fin n → R i))
    (hr_i :
      ∀ a b,
        Ring.DirectLimit.of R ρ i (r_i (Pi.basisFun (R i) (Fin m) a) b) =
          r (Pi.basisFun R∞ (Fin m) a) b) :
    ∃ e_m : R∞ ⊗[R i] (Fin m → R i) ≃ₗ[R∞] (Fin m → R∞),
      ∃ e_n : R∞ ⊗[R i] (Fin n → R i) ≃ₗ[R∞] (Fin n → R∞),
        e_n.toLinearMap ∘ₗ r_i.baseChange R∞ = r ∘ₗ e_m.toLinearMap := by
  classical
  obtain ⟨e_m, he_m, he_m_symm⟩ :=
    descended_free_module_equiv (R := R) (f := f) i m
  obtain ⟨e_n, he_n, he_n_symm⟩ :=
    descended_free_module_equiv (R := R) (f := f) i n
  refine ⟨e_m, e_n, ?_⟩
  -- Proof comment: after identifying both tensorized free modules with the direct-limit free
  -- modules, it is enough to compare the two maps on the basis tensors `1 ⊗ e_a`.
  apply linearMap_eq_of_tensor_pi_basis (A := R i) (S := R∞) (P := Fin n → R∞)
  intro a
  ext b
  have he_m_basis :
      e_m ((1 : R∞) ⊗ₜ[R i] Pi.basisFun (R i) (Fin m) a) =
        Pi.basisFun R∞ (Fin m) a := by
    -- Proof comment: this is the inverse formula from `descended_free_module_equiv`, pushed
    -- forward through `e_m`.
    exact ((congrArg e_m (he_m_symm a)).symm.trans
      (LinearEquiv.apply_symm_apply e_m (Pi.basisFun R∞ (Fin m) a)))
  calc
    (e_n.toLinearMap ∘ₗ r_i.baseChange R∞)
        ((1 : R∞) ⊗ₜ[R i] Pi.basisFun (R i) (Fin m) a) b
      = e_n ((r_i.baseChange R∞)
          ((1 : R∞) ⊗ₜ[R i] Pi.basisFun (R i) (Fin m) a)) b := by
            rfl
    _ = e_n ((1 : R∞) ⊗ₜ[R i] r_i (Pi.basisFun (R i) (Fin m) a)) b := by
          rw [LinearMap.baseChange_tmul]
    _ = Ring.DirectLimit.of R ρ i (r_i (Pi.basisFun (R i) (Fin m) a) b) := by
          simpa using he_n (r_i (Pi.basisFun (R i) (Fin m) a)) b
    _ = r (Pi.basisFun R∞ (Fin m) a) b := hr_i a b
    _ = (r ∘ₗ e_m.toLinearMap)
          ((1 : R∞) ⊗ₜ[R i] Pi.basisFun (R i) (Fin m) a) b := by
          simpa [LinearMap.comp_apply] using congrArg (fun x ↦ r x b) he_m_basis.symm

/-- Helper for Lemma 10.127.6: tensoring the descended presentation quotient to the direct limit
recovers the quotient presentation over the direct-limit ring. -/
private theorem tensor_quotient_range_eq_baseChange_range
    {m n : ℕ} {i : I}
    (r_i : (Fin m → R i) →ₗ[R i] (Fin n → R i)) :
    LinearMap.range
      (((TensorProduct.AlgebraTensorModule.lTensor R∞ R∞)
        (((LinearMap.range r_i).subtype).restrictScalars (R i)))) =
      LinearMap.range (r_i.baseChange R∞) := by
  -- Proof comment: the quotient from `tensorQuotientEquiv` uses the literal `lTensor` range,
  -- while the presentation descent uses `baseChange`; `baseChange_eq_ltensor` identifies them.
  ext x
  change x ∈
      (LinearMap.range
        ((((TensorProduct.AlgebraTensorModule.lTensor R∞ R∞)
          (((LinearMap.range r_i).subtype).restrictScalars (R i))).restrictScalars (R i))) :
          Submodule (R i) _) ↔
    x ∈ (LinearMap.range ((r_i.baseChange R∞).restrictScalars (R i)) : Submodule (R i) _)
  have hRange :
      (LinearMap.range (LinearMap.lTensor R∞ ((LinearMap.range r_i).subtype)) :
          Submodule (R i) (R∞ ⊗[R i] (Fin n → R i))) =
        LinearMap.range (LinearMap.lTensor R∞ r_i) := by
    exact (LinearMap.lTensor_range (Q := R∞) (g := r_i)).symm
  simpa [TensorProduct.AlgebraTensorModule.coe_lTensor, LinearMap.baseChange_eq_ltensor] using
    (congrArg
      (fun S : Submodule (R i) (R∞ ⊗[R i] (Fin n → R i)) ↦ x ∈ S)
      hRange)

/-- Helper for Lemma 10.127.6: a conjugating linear equivalence carries the range of the
source map onto the range of the target map. -/
private theorem range_map_eq_of_conjugation
    {m n : ℕ} {i : I}
    (r : (Fin m → R∞) →ₗ[R∞] (Fin n → R∞))
    (r_i : R∞ ⊗[R i] (Fin m → R i) →ₗ[R∞] R∞ ⊗[R i] (Fin n → R i))
    (e_m : R∞ ⊗[R i] (Fin m → R i) ≃ₗ[R∞] (Fin m → R∞))
    (e_n : R∞ ⊗[R i] (Fin n → R i) ≃ₗ[R∞] (Fin n → R∞))
    (hcomp : e_n.toLinearMap ∘ₗ r_i = r ∘ₗ e_m.toLinearMap) :
    Submodule.map e_n.toLinearMap (LinearMap.range r_i) = LinearMap.range r := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨e_m z, ?_⟩
    -- Proof comment: apply the conjugation identity to the chosen preimage `z`.
    have hz := congrArg (fun F : _ →ₗ[R∞] _ ↦ F z) hcomp
    simpa [LinearMap.comp_apply] using hz.symm
  · rintro ⟨z, rfl⟩
    refine ⟨r_i (e_m.symm z), ⟨e_m.symm z, rfl⟩, ?_⟩
    -- Proof comment: surjectivity of `e_m` lets us pull the target range witness back.
    have hz := congrArg (fun F : _ →ₗ[R∞] _ ↦ F (e_m.symm z)) hcomp
    simpa [LinearMap.comp_apply] using hz

/-- Helper for Lemma 10.127.6: tensoring the descended presentation quotient to the direct limit
recovers the quotient presentation over the direct-limit ring. -/
private theorem descended_presentation_tensor_quotient_equiv
    {m n : ℕ} {i : I}
    (r : (Fin m → R∞) →ₗ[R∞] (Fin n → R∞))
    (r_i : (Fin m → R i) →ₗ[R i] (Fin n → R i))
    (hr_i :
      ∀ a b,
        Ring.DirectLimit.of R ρ i (r_i (Pi.basisFun (R i) (Fin m) a) b) =
          r (Pi.basisFun R∞ (Fin m) a) b) :
    Nonempty
      (R∞ ⊗[R i] ((Fin n → R i) ⧸ LinearMap.range r_i) ≃ₗ[R∞]
        (Fin n → R∞) ⧸ LinearMap.range r) := by
  obtain ⟨e_m, e_n, hcomp⟩ :=
    descended_presentation_relation_map_rebase_eq (R := R) (f := f) r r_i hr_i
  let e₀ :
      R∞ ⊗[R i] ((Fin n → R i) ⧸ LinearMap.range r_i) ≃ₗ[R∞]
        (R∞ ⊗[R i] (Fin n → R i)) ⧸
          LinearMap.range
            (((TensorProduct.AlgebraTensorModule.lTensor R∞ R∞)
              (((LinearMap.range r_i).subtype).restrictScalars (R i)))) :=
    TensorProduct.AlgebraTensorModule.tensorQuotientEquiv
      (R := R i) (A := R∞) (B := R i) (M := R∞)
      (n := LinearMap.range r_i)
  let e₁ :
      ((R∞ ⊗[R i] (Fin n → R i)) ⧸
          LinearMap.range
            (((TensorProduct.AlgebraTensorModule.lTensor R∞ R∞)
              (((LinearMap.range r_i).subtype).restrictScalars (R i))))) ≃ₗ[R∞]
        (R∞ ⊗[R i] (Fin n → R i)) ⧸ LinearMap.range (r_i.baseChange R∞) :=
    Submodule.quotEquivOfEq _ _ <|
      tensor_quotient_range_eq_baseChange_range (R := R) (f := f) r_i
  let e₂ :
      ((R∞ ⊗[R i] (Fin n → R i)) ⧸ LinearMap.range (r_i.baseChange R∞)) ≃ₗ[R∞]
        (Fin n → R∞) ⧸ LinearMap.range r :=
    Submodule.Quotient.equiv
      (LinearMap.range (r_i.baseChange R∞))
      (LinearMap.range r)
      e_n
      (range_map_eq_of_conjugation (R := R) (f := f) r (r_i.baseChange R∞) e_m e_n hcomp)
  -- Proof comment: the quotient comparison factors through the literal tensor quotient, then the
  -- `lTensor`-to-`baseChange` range rewrite, and finally the quotient transport along `e_n`.
  exact ⟨e₀.trans (e₁.trans e₂)⟩

/-- Lemma 10.127.6 (1): every finitely presented module over the directed colimit ring descends to
some stage. -/
-- Proof sketch: choose a finite presentation of `M` over the colimit ring; only finitely many
-- coefficients appear in the presentation matrix, so they all come from one stage `R i`, and the
-- corresponding presentation over `R i` yields a finitely presented module whose base change to
-- the colimit ring is linearly equivalent to `M`.
theorem finitelyPresented_module_descends_to_stage
    {M : Type x} [AddCommGroup M] [Module R∞ M] [Module.FinitePresentation R∞ M] :
    ∃ (i : I) (M_i : Type v) (_ : AddCommGroup M_i) (_ : Module (R i) M_i)
      (_ : Module.FinitePresentation (R i) M_i),
      Nonempty (R∞ ⊗[R i] M_i ≃ₗ[R∞] M) := by
  obtain ⟨n, K, eK, hKfg⟩ := Module.FinitePresentation.exists_fin R∞ M
  obtain ⟨m, r, hrange⟩ :=
    (Submodule.fg_iff_exists_fin_linearMap R∞ (Fin n → R∞)).mp hKfg
  let eM : M ≃ₗ[R∞] (Fin n → R∞) ⧸ LinearMap.range r :=
    eK.trans (Submodule.quotEquivOfEq _ _ hrange.symm)
  obtain ⟨i, r_i, hr_i⟩ := finite_free_linearMap_descends_to_stage (R := R) (f := f) r
  let M_i : Type v := (Fin n → R i) ⧸ LinearMap.range r_i
  have hM_i_fp : Module.FinitePresentation (R i) M_i := by
    -- Proof comment: the quotient map from the finite free module is surjective, and its kernel
    -- is the finitely generated range of the relation map `r_i`.
    have hker_fg : (LinearMap.ker (Submodule.mkQ (LinearMap.range r_i))).FG := by
      rw [Submodule.ker_mkQ]
      exact Submodule.fg_range r_i
    exact Module.finitePresentation_of_surjective
      (Submodule.mkQ (LinearMap.range r_i))
      (Submodule.mkQ_surjective _)
      hker_fg
  letI : Module.FinitePresentation (R i) M_i := hM_i_fp
  obtain ⟨eDesc⟩ :=
    descended_presentation_tensor_quotient_equiv (R := R) (f := f) r r_i hr_i
  -- Proof comment: the descended stage quotient has the chosen presentation, and the tensor
  -- quotient equivalence identifies its base change with the original quotient presentation of `M`.
  exact ⟨i, M_i, inferInstance, inferInstance, inferInstance, ⟨eDesc.trans eM.symm⟩⟩

/-- Helper for Lemma 10.127.6: the tail index set above a fixed stage remains directed. -/
private theorem tail_index_isDirected (i : I) :
    IsDirectedOrder (Set.Ici i) := by
  constructor
  intro j k
  -- Proof comment: directedness of the ambient preorder gives a common upper bound which
  -- automatically stays in the tail above `i`.
  obtain ⟨ℓ, hjℓ, hkℓ⟩ := exists_ge_ge j.1 k.1
  exact ⟨⟨ℓ, le_trans j.2 hjℓ⟩, hjℓ, hkℓ⟩

/-- Helper for Lemma 10.127.6: the tail family above `i`. -/
private abbrev tail_ring_family (i : I) : Set.Ici i → Type v := fun j ↦ R j.1

/-- Helper for Lemma 10.127.6: the direct limit of the tail family above `i`. -/
private abbrev tail_directLimit (i : I) :=
  Ring.DirectLimit (tail_ring_family (R := R) i)
    (fun j k hij ↦ (f j.1 k.1 hij : R j.1 →+* R k.1))

/-- Helper for Lemma 10.127.6: the restricted transition maps still form a directed system. -/
private instance tail_directedSystem (i : I) :
    DirectedSystem (tail_ring_family (R := R) i)
      (fun j k hij ↦ (f j.1 k.1 hij : R j.1 →+* R k.1)) where
  map_self := by
    intro j x
    exact DirectedSystem.map_self (f := fun a b hab ↦ (f a b hab : R a →+* R b)) x
  map_map := by
    intro j k ℓ hjk hkℓ x
    exact DirectedSystem.map_map (f := fun a b hab ↦ (f a b hab : R a →+* R b)) hjk hkℓ x

/-- Helper for Lemma 10.127.6: choose a common upper bound of the base stage `i` and another
stage `j`. -/
private noncomputable def tail_upper_bound (i j : I) : I :=
  (exists_ge_ge j i).choose

/-- Helper for Lemma 10.127.6: the chosen upper bound lies above the original stage `j`. -/
private theorem le_tail_upper_bound_left (i j : I) :
    j ≤ tail_upper_bound i j :=
  (exists_ge_ge j i).choose_spec.1

/-- Helper for Lemma 10.127.6: the chosen upper bound lies in the tail above the base stage `i`.
-/
private theorem le_tail_upper_bound_right (i j : I) :
    i ≤ tail_upper_bound i j :=
  (exists_ge_ge j i).choose_spec.2

/-- Helper for Lemma 10.127.6: every ambient stage maps canonically into the direct limit of the
tail above `i`. -/
private noncomputable def tail_stage_to_directLimit (i j : I) :
    R j →+* tail_directLimit (R := R) (f := f) i :=
  let k : Set.Ici i :=
    ⟨tail_upper_bound i j, le_tail_upper_bound_right i j⟩
  (Ring.DirectLimit.of (tail_ring_family (R := R) i)
      (fun a b hab ↦ (f a.1 b.1 hab : R a.1 →+* R b.1)) k).comp
    (f j k.1 (le_tail_upper_bound_left i j))

/-- Helper for Lemma 10.127.6: the ambient stage maps into the tail direct limit are compatible
with the original transition morphisms. -/
private theorem tail_stage_to_directLimit_compatible
    (i : I) {j k : I} (hjk : j ≤ k) (x : R j) :
    tail_stage_to_directLimit (R := R) (f := f) i k ((f j k hjk) x) =
      tail_stage_to_directLimit (R := R) (f := f) i j x := by
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected i
  let jj : Set.Ici i :=
    ⟨tail_upper_bound i j, le_tail_upper_bound_right i j⟩
  let kk : Set.Ici i :=
    ⟨tail_upper_bound i k, le_tail_upper_bound_right i k⟩
  obtain ⟨ℓ, hjℓ, hkℓ⟩ := exists_ge_ge jj kk
  -- Proof comment: move both representatives to a common tail stage and use the original
  -- directed-system relation there.
  calc
    tail_stage_to_directLimit (R := R) (f := f) i k ((f j k hjk) x) =
        Ring.DirectLimit.of (tail_ring_family (R := R) i)
          (fun a b hab ↦ (f a.1 b.1 hab : R a.1 →+* R b.1)) ℓ
          (f kk.1 ℓ.1 hkℓ
            (f k kk.1 (le_tail_upper_bound_left i k) ((f j k hjk) x))) := by
          simp only [tail_stage_to_directLimit, kk, RingHom.comp_apply]
          symm
          exact Ring.DirectLimit.of_f hkℓ _
    _ =
        Ring.DirectLimit.of (tail_ring_family (R := R) i)
          (fun a b hab ↦ (f a.1 b.1 hab : R a.1 →+* R b.1)) ℓ
          (f jj.1 ℓ.1 hjℓ
            (f j jj.1 (le_tail_upper_bound_left i j) x)) := by
          congr 1
          calc
            f kk.1 ℓ.1 hkℓ
                (f k kk.1 (le_tail_upper_bound_left i k) ((f j k hjk) x)) =
              f k ℓ.1 (le_trans (le_tail_upper_bound_left i k) hkℓ)
                ((f j k hjk) x) := by
                  exact DirectedSystem.map_map'
                    (f := fun a b hab ↦ (f a b hab : R a →+* R b))
                    (le_tail_upper_bound_left i k) hkℓ ((f j k hjk) x)
            _ =
              f j ℓ.1 (le_trans hjk
                (le_trans (le_tail_upper_bound_left i k) hkℓ)) x := by
                  exact DirectedSystem.map_map'
                    (f := fun a b hab ↦ (f a b hab : R a →+* R b))
                    hjk (le_trans (le_tail_upper_bound_left i k) hkℓ) x
            _ =
              f jj.1 ℓ.1 hjℓ
                (f j jj.1 (le_tail_upper_bound_left i j) x) := by
                  symm
                  exact DirectedSystem.map_map'
                    (f := fun a b hab ↦ (f a b hab : R a →+* R b))
                    (le_tail_upper_bound_left i j) hjℓ x
    _ = tail_stage_to_directLimit (R := R) (f := f) i j x := by
          simp only [tail_stage_to_directLimit, jj, RingHom.comp_apply]
          exact Ring.DirectLimit.of_f hjℓ _

/-- Helper for Lemma 10.127.6: the ambient direct limit maps canonically into the tail direct
limit above `i`. -/
private noncomputable def full_directLimit_to_tail (i : I) :
    R∞ →+* tail_directLimit (R := R) (f := f) i :=
  Ring.DirectLimit.lift R ρ (tail_directLimit (R := R) (f := f) i)
    (fun j ↦ tail_stage_to_directLimit (R := R) (f := f) i j)
    (fun _ _ hij x ↦ tail_stage_to_directLimit_compatible (R := R) (f := f) i hij x)

/-- Helper for Lemma 10.127.6: the tail direct limit maps back to the ambient direct limit by
forgetting that the index lies in the tail. -/
private noncomputable def tail_directLimit_to_full (i : I) :
    tail_directLimit (R := R) (f := f) i →+* R∞ :=
  Ring.DirectLimit.lift
    (tail_ring_family (R := R) i)
    (fun j k hij ↦ (f j.1 k.1 hij : R j.1 →+* R k.1))
    R∞
    (fun j ↦ Ring.DirectLimit.of R ρ j.1)
    (fun j k hjk x ↦ by
      -- Proof comment: tail transitions are the ambient transitions on the underlying stages.
      simpa using
        (Ring.DirectLimit.of_f
          (G := tail_ring_family (R := R) i)
          (f := fun a b hab ↦ (f a.1 b.1 hab : R a.1 →+* R b.1))
          hjk x))

/-- Helper for Lemma 10.127.6: going from the ambient direct limit to the tail and back is the
identity. -/
private theorem tail_directLimit_to_full_comp_full_directLimit_to_tail (i : I) :
    (tail_directLimit_to_full (R := R) (f := f) i).comp
        (full_directLimit_to_tail (R := R) (f := f) i) =
      RingHom.id _ := by
  apply Ring.DirectLimit.hom_ext
  intro j
  ext x
  -- Proof comment: the composite lands in the chosen upper tail stage and then uses the
  -- direct-limit relation to return to the original stage.
  simpa [full_directLimit_to_tail, tail_stage_to_directLimit, tail_directLimit_to_full,
    RingHom.comp_apply] using
    (Ring.DirectLimit.of_f
      (G := R)
      (f := ρ)
      (le_tail_upper_bound_left i j) x)

/-- Helper for Lemma 10.127.6: going from the tail direct limit to the ambient direct limit and
back is the identity. -/
private theorem full_directLimit_to_tail_comp_tail_directLimit_to_full (i : I) :
    (full_directLimit_to_tail (R := R) (f := f) i).comp
        (tail_directLimit_to_full (R := R) (f := f) i) =
      RingHom.id _ := by
  apply Ring.DirectLimit.hom_ext
  intro j
  ext x
  -- Proof comment: a tail stage already lies above `i`, so reindexing it through the chosen
  -- upper bound leaves the same direct-limit class.
  simpa [full_directLimit_to_tail, tail_stage_to_directLimit, tail_directLimit_to_full,
    RingHom.comp_apply] using
    (Ring.DirectLimit.of_f
      (G := tail_ring_family (R := R) i)
      (f := fun a b hab ↦ (f a.1 b.1 hab : R a.1 →+* R b.1))
      (le_tail_upper_bound_left i j.1) x)

/-- Helper for Lemma 10.127.6: the direct limit of the tail above `i` identifies with the ambient
direct limit as an `R i`-algebra. -/
private noncomputable instance tail_directLimit_algebra (i : I) :
    Algebra (R i) (tail_directLimit (R := R) (f := f) i) :=
  (Ring.DirectLimit.of (tail_ring_family (R := R) i)
    (fun j k hij ↦ (f j.1 k.1 hij : R j.1 →+* R k.1)) ⟨i, le_rfl⟩).toAlgebra

/-- Helper for Lemma 10.127.6: the tail direct limit is canonically `R i`-algebra equivalent to
the ambient direct limit. -/
private noncomputable def tail_directLimit_algEquiv_over_stage (i : I) :
    tail_directLimit (R := R) (f := f) i ≃ₐ[R i] R∞ where
  -- Route correction: parts (2) and (3) need an `R i`-algebra equivalence, not just a bare ring
  -- equivalence, so the tail/full comparison is packaged at the algebra level.
  __ := RingEquiv.ofRingHom
    (tail_directLimit_to_full (R := R) (f := f) i)
    (full_directLimit_to_tail (R := R) (f := f) i)
    (tail_directLimit_to_full_comp_full_directLimit_to_tail (R := R) (f := f) i)
    (full_directLimit_to_tail_comp_tail_directLimit_to_full (R := R) (f := f) i)
  commutes' a := by
    -- Proof comment: both algebra maps are represented by the distinguished tail stage `⟨i, le_rfl⟩`.
    change
      Ring.DirectLimit.of R ρ i a =
        Ring.DirectLimit.of R ρ i a
    rfl

/-- Helper for Lemma 10.127.6: the tail/full algebra equivalence sends each tail generator to the
corresponding ambient direct-limit class. -/
private theorem tail_directLimit_algEquiv_over_stage_of
    (i : I) (j : Set.Ici i) (x : R j.1) :
    tail_directLimit_algEquiv_over_stage (R := R) (f := f) i
        (Ring.DirectLimit.of (tail_ring_family (R := R) i)
          (fun a b hab ↦ (f a.1 b.1 hab : R a.1 →+* R b.1)) j x) =
      Ring.DirectLimit.of R ρ j.1 x := by
  -- Proof comment: on generators the equivalence is exactly the forgetful map from the tail
  -- system to the ambient system.
  simp [tail_directLimit_algEquiv_over_stage, tail_directLimit_to_full]

/-- Helper for Lemma 10.127.6: each tail stage inherits its `R i`-algebra structure from the
original transition map `R i → R j`. -/
private noncomputable instance tail_ring_family_algebra
    (i : I) (j : Set.Ici i) : Algebra (R i) (tail_ring_family (R := R) i j) :=
  (f i j.1 j.2).toAlgebra

/-- Helper for Lemma 10.127.6: the reindexed tail system carries the induced family of
`R i`-algebra structures. -/
private noncomputable instance tail_ring_family_algebra_family
    (i : I) :
    ∀ j : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j) :=
  fun j ↦ tail_ring_family_algebra (R := R) (f := f) i j

/-- Helper for Lemma 10.127.6: the transition map between two tail stages is an algebra map over
the base stage `R i`. -/
private theorem tail_stage_transition_commutes
    (i : I) {j k : Set.Ici i} (hjk : j ≤ k) (x : R i) :
    letI : Algebra (R i) (R j.1) := tail_ring_family_algebra (R := R) (f := f) i j
    letI : Algebra (R i) (R k.1) := tail_ring_family_algebra (R := R) (f := f) i k
    f j.1 k.1 hjk (algebraMap (R i) (R j.1) x) = algebraMap (R i) (R k.1) x := by
  letI : Algebra (R i) (R j.1) := tail_ring_family_algebra (R := R) (f := f) i j
  letI : Algebra (R i) (R k.1) := tail_ring_family_algebra (R := R) (f := f) i k
  -- Proof comment: both sides are the two composites from stage `i` to stage `k.1`.
  change f j.1 k.1 hjk ((f i j.1 j.2) x) = (f i k.1 k.2) x
  exact DirectedSystem.map_map'
    (f := fun a b hab ↦ (f a b hab : R a →+* R b)) j.2 hjk x

/-- Helper for Lemma 10.127.6: the tail transition maps are `R i`-algebra morphisms. -/
private noncomputable abbrev tail_transition_algHom
    (i : I) {j k : Set.Ici i} (hjk : j ≤ k) :
    letI : Algebra (R i) (R j.1) := tail_ring_family_algebra (R := R) (f := f) i j
    letI : Algebra (R i) (R k.1) := tail_ring_family_algebra (R := R) (f := f) i k
    R j.1 →ₐ[R i] R k.1 :=
  letI : Algebra (R i) (R j.1) := tail_ring_family_algebra (R := R) (f := f) i j
  letI : Algebra (R i) (R k.1) := tail_ring_family_algebra (R := R) (f := f) i k
  { toRingHom := f j.1 k.1 hjk
    commutes' := by
      intro x
      exact tail_stage_transition_commutes (R := R) (f := f) i hjk x }

/-- Helper for Lemma 10.127.6: the underlying ring hom of the tail transition algebra map. -/
private noncomputable abbrev tail_transition_ringHom
    (i : I) {j k : Set.Ici i} (hjk : j ≤ k) :
    R j.1 →+* R k.1 :=
  letI : Algebra (R i) (R j.1) := tail_ring_family_algebra (R := R) (f := f) i j
  letI : Algebra (R i) (R k.1) := tail_ring_family_algebra (R := R) (f := f) i k
  (tail_transition_algHom (R := R) (f := f) i hjk).toRingHom

/-- Helper for Lemma 10.127.6: the tail transition ring hom is just the underlying transition map
on the ambient directed system. -/
private theorem tail_transition_ringHom_apply
    (i : I) {j k : Set.Ici i} (hjk : j ≤ k) (x : R j.1) :
    tail_transition_ringHom (R := R) (f := f) i hjk x = f j.1 k.1 hjk x := rfl

/-- Helper for Lemma 10.127.6: the tail transition algebra maps still form a directed system on
their underlying ring homomorphisms. -/
private instance tail_directedSystem_algHom (i : I) :
    DirectedSystem (tail_ring_family (R := R) i)
      (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk) where
  map_self := by
    intro j x
    exact DirectedSystem.map_self (f := fun a b hab ↦ (f a.1 b.1 hab : R a.1 →+* R b.1)) x
  map_map := by
    intro j k ℓ hjk hkℓ x
    exact DirectedSystem.map_map
      (f := fun a b hab ↦ (f a.1 b.1 hab : R a.1 →+* R b.1)) hjk hkℓ x

/-- Helper for Lemma 10.127.6: the owner theorem's tail specialization uses the standard
arbitrary-stage `R i`-algebra structure on the tail direct limit. -/
@[reducible] private noncomputable def owner_tail_directLimitAlgebra (i : I) :
    Algebra (R i)
      (Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)) :=
  let j : Set.Ici i := Classical.arbitrary (Set.Ici i)
  letI : Algebra (R i) (R j.1) := tail_ring_family_algebra (R := R) (f := f) i j
  ((Ring.DirectLimit.of
      (tail_ring_family (R := R) i)
      (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
      j).comp
    (algebraMap (R i) (R j.1))).toAlgebra

/-- Helper for Lemma 10.127.6: the owner theorem's arbitrary-stage algebra map to the tail direct
limit agrees with the canonical algebra map from the base tail stage `⟨i, le_rfl⟩`. -/
private theorem owner_tail_directLimit_algebraMap_eq
    (i : I) (a : R i) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    algebraMap (R i) tailLimit a =
      Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        ⟨i, le_rfl⟩ a := by
  classical
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  let j : Set.Ici i := Classical.arbitrary (Set.Ici i)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
  obtain ⟨k, hjk, hik⟩ := exists_ge_ge j ⟨i, le_rfl⟩
  -- Proof comment: move both representatives to a common upper tail stage and compare the two
  -- coefficient maps there.
  change
    Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        j ((f i j.1 j.2) a) =
      Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        ⟨i, le_rfl⟩ a
  calc
    Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        j ((f i j.1 j.2) a) =
      Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        k (f j.1 k.1 hjk ((f i j.1 j.2) a)) := by
          symm
          exact Ring.DirectLimit.of_f
            (G := tail_ring_family (R := R) i)
            (f := fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
            (i := j) (j := k) (hij := hjk) (x := (f i j.1 j.2) a)
    _ =
      Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        k (f i k.1 (le_trans j.2 hjk) a) := by
          exact congrArg
            (Ring.DirectLimit.of
              (tail_ring_family (R := R) i)
              (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
              k)
            (by
              simpa using tail_stage_transition_commutes (R := R) (f := f) i hjk a)
    _ =
      Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        k (f i k.1 hik a) := by
          have hproof : le_trans j.2 hjk = hik := Subsingleton.elim _ _
          cases hproof
          rfl
    _ =
      Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        ⟨i, le_rfl⟩ a := by
          exact Ring.DirectLimit.of_f
            (G := tail_ring_family (R := R) i)
            (f := fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
            (i := ⟨i, le_rfl⟩) (j := k) (hij := hik) (x := a)

/-- Helper for Lemma 10.127.6: the owner theorem's tail direct-limit algebra structure agrees
with the canonical one used elsewhere in this file. -/
private theorem owner_tail_directLimit_algebra_eq
    (i : I) :
    owner_tail_directLimitAlgebra (R := R) (f := f) i =
      (tail_directLimit_algebra (R := R) (f := f) i :
        Algebra (R i)
          (Ring.DirectLimit
            (tail_ring_family (R := R) i)
            (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk))) := by
  -- Proof comment: both algebra structures have the same map out of `R i`, namely the canonical
  -- class of the base tail stage `⟨i, le_rfl⟩`.
  exact Algebra.algebra_ext _ _
    (owner_tail_directLimit_algebraMap_eq (R := R) (f := f) i)

/-- Helper for Lemma 10.127.6: transporting the owner theorem's tail direct-limit algebra
structure to the ambient direct limit gives the canonical tail/full algebra equivalence. -/
private noncomputable def owner_tail_directLimit_algEquiv_over_stage
    (i : I) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    tailLimit ≃ₐ[R i] R∞ :=
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  { __ := RingEquiv.ofRingHom
      (tail_directLimit_to_full (R := R) (f := f) i)
      (full_directLimit_to_tail (R := R) (f := f) i)
      (tail_directLimit_to_full_comp_full_directLimit_to_tail (R := R) (f := f) i)
      (full_directLimit_to_tail_comp_tail_directLimit_to_full (R := R) (f := f) i)
    commutes' := fun a ↦ by
      rw [owner_tail_directLimit_algebraMap_eq (R := R) (f := f) i]
      rfl }

/-- Helper for Lemma 10.127.6: each tail stage acts on the owner tail direct limit through the
canonical stage map, compatibly with the base stage `R_i`. -/
private theorem owner_tail_directLimit_isScalarTower
    (i : I) (j : Set.Ici i) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    let _ : Algebra (R j.1) tailLimit :=
      (Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        j).toAlgebra
    IsScalarTower (R i) (R j.1) tailLimit := by
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  let _ : Algebra (R j.1) tailLimit :=
    (Ring.DirectLimit.of
      (tail_ring_family (R := R) i)
      (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
      j).toAlgebra
  -- Proof comment: the owner-tail algebra map from the base stage agrees with the distinguished
  -- tail stage `⟨i, le_rfl⟩`, while the stage-`j` route is the direct-limit transition from that
  -- base stage to `j`.
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext a
  rw [owner_tail_directLimit_algebraMap_eq (R := R) (f := f) i]
  change
    Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        ⟨i, le_rfl⟩ a =
      Ring.DirectLimit.of
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
        j ((f i j.1 j.2) a)
  symm
  exact Ring.DirectLimit.of_f
    (G := tail_ring_family (R := R) i)
    (f := fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    (i := ⟨i, le_rfl⟩) (j := j) (hij := j.2) (x := a)

/-- Helper for Lemma 10.127.6: the transported owner-style tail/full equivalence still sends a
tail stage class to the corresponding ambient direct-limit class. -/
private theorem owner_tail_directLimit_algEquiv_over_stage_of
    (i : I) (j : Set.Ici i) (x : R j.1) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i
        (Ring.DirectLimit.of
          (tail_ring_family (R := R) i)
          (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
          j x) =
      Ring.DirectLimit.of R ρ j.1 x := by
  rfl

/-- Helper for Lemma 10.127.6: base change of a stage map commutes with the tail/full
identification of the coefficient direct limits. -/
private theorem tail_algEquiv_baseChange_transport
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (u : M_i →ₗ[R i] N_i) :
    let e := (tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
    let eM : tail_directLimit (R := R) (f := f) i ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
      TensorProduct.congr e (LinearEquiv.refl (R i) M_i)
    let eN : tail_directLimit (R := R) (f := f) i ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
      TensorProduct.congr e (LinearEquiv.refl (R i) N_i)
    eN.toLinearMap ∘ₗ (u.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i) =
      ((u.baseChange R∞).restrictScalars (R i)) ∘ₗ eM.toLinearMap := by
  let e := (tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
  let eM : tail_directLimit (R := R) (f := f) i ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
    TensorProduct.congr e (LinearEquiv.refl (R i) M_i)
  let eN : tail_directLimit (R := R) (f := f) i ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
    TensorProduct.congr e (LinearEquiv.refl (R i) N_i)
  -- Proof comment: both rebased maps are `R i`-linear, so it is enough to compare them on pure
  -- tensors `r ⊗ x`.
  ext r x
  simp [eM, eN]

private theorem canonical_tail_baseChange_eq_owner_tail_baseChange
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (u : M_i →ₗ[R i] N_i) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    ((u.baseChange tailLimit).restrictScalars (R i)) =
      ((u.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i)) := by
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  -- Proof comment: the two `baseChange` maps only differ by the chosen `Algebra (R i)` instance on
  -- the same tail direct-limit ring.
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | add z₁ z₂ hz₁ hz₂ =>
      simp [hz₁, hz₂]
  | tmul r x =>
      change (u.baseChange tailLimit) (r ⊗ₜ[R i] x) =
        (u.baseChange (tail_directLimit (R := R) (f := f) i)) (r ⊗ₜ[R i] x)
      rfl

/-- Helper for Lemma 10.127.6: the eventual-equality theorem from `Lemma_10_127_5` specializes to
the tail system above a fixed stage `i`. -/
private theorem canonical_tail_baseChange_eq_restrictScalars
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (φ_i ψ_i : M_i →ₗ[R i] N_i)
    (h_tail :
      φ_i.baseChange (tail_directLimit (R := R) (f := f) i) =
        ψ_i.baseChange (tail_directLimit (R := R) (f := f) i)) :
    ((φ_i.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i)) =
      ((ψ_i.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i)) := by
  -- Proof comment: equality of canonical-tail `baseChange` maps remains true after forgetting the
  -- tail direct-limit scalar action down to the base stage `R i`.
  simpa using
    congrArg
      (fun u :
        tail_directLimit (R := R) (f := f) i ⊗[R i] M_i →ₗ[
          tail_directLimit (R := R) (f := f) i]
          tail_directLimit (R := R) (f := f) i ⊗[R i] N_i ↦
        u.restrictScalars (R i))
      h_tail

/-- Helper for Lemma 10.127.6: after forgetting to the base stage `R_i`, the owner-tail
base-change map agrees with the canonical-tail base-change map. -/
private theorem owner_tail_baseChange_restrictScalars_bridge
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (u : M_i →ₗ[R i] N_i) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    ((u.baseChange tailLimit).restrictScalars (R i)) =
      ((u.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i)) := by
  exact canonical_tail_baseChange_eq_owner_tail_baseChange (R := R) (f := f) i u

/-- Helper for Lemma 10.127.6: on the exact owner-tail surface, rewriting the owner-tail
`Algebra (R i)` instance to the canonical one identifies the underlying `R i`-linear
base-change maps. -/
private theorem owner_tail_exact_baseChange_bridge
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (u : M_i →ₗ[R i] N_i) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    ((u.baseChange tailLimit).restrictScalars (R i)) =
      ((u.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i)) := by
  -- Proof comment: this is exactly the previously established restrict-scalars bridge, now kept
  -- under the dedicated owner-tail normalization name needed by the current proof route.
  exact owner_tail_baseChange_restrictScalars_bridge
    (R := R) (f := f) i u

/-- Helper for Lemma 10.127.6: equality of base-changed maps transports across equal algebra
structures on the same coefficient ring. -/
private theorem baseChange_eq_of_algebra_eq
    {A : Type*} [CommRing A]
    {S : Type*} [CommRing S]
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (alg₁ alg₂ : Algebra A S)
    (u v : M →ₗ[A] N)
    (hAlg : alg₁ = alg₂)
    (h :
      @LinearMap.baseChange A S M N _ _ alg₂ _ _ _ _ u =
        @LinearMap.baseChange A S M N _ _ alg₂ _ _ _ _ v) :
    @LinearMap.baseChange A S M N _ _ alg₁ _ _ _ _ u =
      @LinearMap.baseChange A S M N _ _ alg₁ _ _ _ _ v := by
  -- Proof comment: after rewriting the chosen `Algebra A S` structure, the two base-change
  -- equalities become definitionally identical.
  cases hAlg
  exact h

/-- Helper for Lemma 10.127.6: equality of canonical-tail base changes upgrades to the exact
owner-tail equality expected by `Lemma_10_127_5`. -/
private theorem owner_tail_baseChange_eq_of_canonical_tail_eq
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (φ_i ψ_i : M_i →ₗ[R i] N_i)
    (h_tail :
      φ_i.baseChange (tail_directLimit (R := R) (f := f) i) =
        ψ_i.baseChange (tail_directLimit (R := R) (f := f) i)) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    φ_i.baseChange tailLimit = ψ_i.baseChange tailLimit := by
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  let algCanonical : Algebra (R i) tailLimit := tail_directLimit_algebra (R := R) (f := f) i
  have h_canonical :
      @LinearMap.baseChange (R i) tailLimit M_i N_i _ _ algCanonical _ _ _ _ φ_i =
        @LinearMap.baseChange (R i) tailLimit M_i N_i _ _ algCanonical _ _ _ _ ψ_i := by
    -- Proof comment: with the canonical tail algebra structure in force, the target is exactly
    -- the canonical-tail equality `h_tail`.
    simpa [tailLimit] using h_tail
  let algOwner : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  letI : Algebra (R i) tailLimit := algOwner
  -- Proof comment: transport the finished canonical-tail equality to the owner-tail instance.
  exact baseChange_eq_of_algebra_eq
    algOwner algCanonical φ_i ψ_i
    (owner_tail_directLimit_algebra_eq (R := R) (f := f) i)
    h_canonical

/-- Helper for Lemma 10.127.6: the eventual-equality theorem from `Lemma_10_127_5` specializes to
the tail system above a fixed stage `i`. -/
theorem tail_baseChange_eventually_eq_wrapper
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
      [Module.FinitePresentation (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (φ_i ψ_i : M_i →ₗ[R i] N_i)
    (h_tail :
      φ_i.baseChange (tail_directLimit (R := R) (f := f) i) =
        ψ_i.baseChange (tail_directLimit (R := R) (f := f) i)) :
    ∃ j : Set.Ici i,
      let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
      φ_i.baseChange (R j.1) = ψ_i.baseChange (R j.1) := by
  letI : ∀ j : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j) :=
    tail_ring_family_algebra_family (R := R) (f := f) i
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
  letI :
      DirectedSystem (tail_ring_family (R := R) i)
        (fun j k hjk ↦
          ((tail_transition_algHom (R := R) (f := f) i hjk :
            R j.1 →ₐ[R i] R k.1) : R j.1 →+* R k.1)) :=
    tail_directedSystem_algHom (R := R) (f := f) i
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j k hjk ↦
        ((tail_transition_algHom (R := R) (f := f) i hjk :
          R j.1 →ₐ[R i] R k.1) : R j.1 →+* R k.1))
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  have h_owner :
      φ_i.baseChange tailLimit = ψ_i.baseChange tailLimit :=
    owner_tail_baseChange_eq_of_canonical_tail_eq
      (R := R) (f := f) i φ_i ψ_i h_tail
  obtain ⟨j, hj⟩ :=
    baseChange_eventually_eq_of_finite
      (A := R i)
      (I := Set.Ici i)
      (R := tail_ring_family (R := R) i)
      (f := fun j k hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
      (M := M_i) (N := N_i) φ_i ψ_i h_owner
  -- Proof comment: unpack the stabilized tail index to its ambient stage `j.1`.
  exact ⟨j, by simpa [tailLimit] using hj⟩

/-- Helper for Lemma 10.127.6: on a pure tensor, transporting the owner-tail stage tensor map to
the ambient direct limit gives the literal stage tensor map into `R∞`. -/
private theorem owner_stageTensorMap_to_full_tmul
    (i : I)
    {X : Type y} [AddCommGroup X] [Module (R i) X]
    (j : Set.Ici i) (r : R j.1) (x : X) :
    letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
      tail_ring_family_algebra_family (R := R) (f := f) i
    letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
    letI :
        DirectedSystem (tail_ring_family (R := R) i)
          (fun j' k' hjk ↦
            ((tail_transition_algHom (R := R) (f := f) i hjk :
              R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
      tail_directedSystem_algHom (R := R) (f := f) i
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    (TensorProduct.congr
      (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
      (LinearEquiv.refl (R i) X))
      (_root_.stageTensorMap
        (A := R i)
        (R := tail_ring_family (R := R) i)
        (f := fun j' k' hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
        (X := X) j (r ⊗ₜ[R i] x)) =
      let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
      let _ : Algebra (R j.1) R∞ := stageDirectLimitAlgebra R f j.1
      let _ : IsScalarTower (R i) (R j.1) R∞ := directLimitStage_isScalarTower R f j.2
      (LinearMap.rTensor X ((Algebra.linearMap (R j.1) R∞).restrictScalars (R i)))
        (r ⊗ₜ[R i] x) := by
  letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
    tail_ring_family_algebra_family (R := R) (f := f) i
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
  letI :
      DirectedSystem (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦
          ((tail_transition_algHom (R := R) (f := f) i hjk :
            R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
    tail_directedSystem_algHom (R := R) (f := f) i
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  let e :=
    TensorProduct.congr
      (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
      (LinearEquiv.refl (R i) X)
  -- Proof comment: the owner-tail stage tensor map sends `r ⊗ x` to the tail direct-limit class
  -- of `r`, and the owner tail/full equivalence identifies that class with the ambient one.
  simpa [e, _root_.stageTensorMap] using
    congrArg (fun s : R∞ ↦ s ⊗ₜ[R i] x)
      (owner_tail_directLimit_algEquiv_over_stage_of
        (R := R) (f := f) i j r)

/-- Helper for Lemma 10.127.6: transporting the owner-tail stage tensor map along the tail/full
comparison identifies it with the ambient stage tensor map into `R∞`. -/
private theorem owner_stageTensorMap_to_full
    (i : I)
    {X : Type y} [AddCommGroup X] [Module (R i) X]
    (j : Set.Ici i)
    (z :
      let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
      R j.1 ⊗[R i] X) :
    letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
      tail_ring_family_algebra_family (R := R) (f := f) i
    letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
    letI :
        DirectedSystem (tail_ring_family (R := R) i)
          (fun j' k' hjk ↦
            ((tail_transition_algHom (R := R) (f := f) i hjk :
              R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
      tail_directedSystem_algHom (R := R) (f := f) i
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    (TensorProduct.congr
      (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
      (LinearEquiv.refl (R i) X))
      (_root_.stageTensorMap
        (A := R i)
        (R := tail_ring_family (R := R) i)
        (f := fun j' k' hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
        (X := X) j z) =
      let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
      let _ : Algebra (R j.1) R∞ := stageDirectLimitAlgebra R f j.1
      let _ : IsScalarTower (R i) (R j.1) R∞ := directLimitStage_isScalarTower R f j.2
      (LinearMap.rTensor X ((Algebra.linearMap (R j.1) R∞).restrictScalars (R i))) z := by
  letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
    tail_ring_family_algebra_family (R := R) (f := f) i
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
  letI :
      DirectedSystem (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦
          ((tail_transition_algHom (R := R) (f := f) i hjk :
            R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
    tail_directedSystem_algHom (R := R) (f := f) i
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  let e :=
    TensorProduct.congr
      (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
      (LinearEquiv.refl (R i) X)
  let tailMap :
      R j.1 ⊗[R i] X →ₗ[R i] tailLimit ⊗[R i] X :=
    _root_.stageTensorMap
      (A := R i)
      (R := tail_ring_family (R := R) i)
      (f := fun j' k' hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
      (X := X) j
  let fullMap :
      R j.1 ⊗[R i] X →ₗ[R i] R∞ ⊗[R i] X :=
    let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
    let _ : Algebra (R j.1) R∞ := stageDirectLimitAlgebra R f j.1
    let _ : IsScalarTower (R i) (R j.1) R∞ := directLimitStage_isScalarTower R f j.2
    LinearMap.rTensor X ((Algebra.linearMap (R j.1) R∞).restrictScalars (R i))
  -- Proof comment: prove the transport formula first on pure tensors, then extend by tensor
  -- induction so the elaborator never unfolds the full owner `stageTensorMap` term globally.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · calc
      e (tailMap 0) = e 0 := by rw [tailMap.map_zero]
      _ = 0 := by simpa using e.map_zero
      _ = fullMap 0 := by symm; exact fullMap.map_zero
  · intro r x
    simpa [e, tailMap, fullMap] using
      owner_stageTensorMap_to_full_tmul
        (R := R) (f := f) i j r x
  · intro z₁ z₂ hz₁ hz₂
    have hz₁' : e (tailMap z₁) = fullMap z₁ := by
      simpa [tailMap, fullMap] using hz₁
    have hz₂' : e (tailMap z₂) = fullMap z₂ := by
      simpa [tailMap, fullMap] using hz₂
    calc
      e (tailMap (z₁ + z₂)) = e (tailMap z₁ + tailMap z₂) := by
        rw [tailMap.map_add]
      _ = e (tailMap z₁) + e (tailMap z₂) := by
        simpa using e.map_add (tailMap z₁) (tailMap z₂)
      _ = fullMap z₁ + fullMap z₂ := by rw [hz₁', hz₂']
      _ = fullMap (z₁ + z₂) := by rw [fullMap.map_add]

/-- Helper for Lemma 10.127.6: canceling `1 ⊗ z` in an iterated base change gives the canonical
tensor map induced by the ambient algebra map on coefficients. -/
private theorem cancelBaseChange_one_tmul_eq_rTensor_restrictScalars
    {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B]
    {S : Type*} [CommRing S] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    {N : Type*} [AddCommGroup N] [Module A N]
    (z : B ⊗[A] N) :
    (cancelBaseChange A B S S N) ((1 : S) ⊗ₜ[B] z) =
      (LinearMap.rTensor N ((Algebra.linearMap B S).restrictScalars A)) z := by
  -- Proof comment: verify the formula on pure tensors and extend it by tensor induction.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro b n
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simp [Algebra.smul_def]
  · intro z₁ z₂ hz₁ hz₂
    rw [TensorProduct.tmul_add, map_add, LinearMap.map_add, hz₁, hz₂]

/-- Helper for Lemma 10.127.6: the owner tail/full tensor comparison is semilinear for scalar
multiplication by tail-limit coefficients. -/
private theorem owner_tail_tensor_equiv_smul
    (i : I)
    {X : Type y} [AddCommGroup X] [Module (R i) X]
    (r :
      let tailLimit :=
        Ring.DirectLimit
          (tail_ring_family (R := R) i)
          (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
      tailLimit)
    (z :
      let tailLimit :=
        Ring.DirectLimit
          (tail_ring_family (R := R) i)
          (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
      letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
      tailLimit ⊗[R i] X) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    let eX : tailLimit ⊗[R i] X ≃ₗ[R i] R∞ ⊗[R i] X :=
      TensorProduct.congr
        (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
        (LinearEquiv.refl (R i) X)
    eX (r • z) =
      (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i r) • eX z := by
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  let eAlg := owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i
  let eX : tailLimit ⊗[R i] X ≃ₗ[R i] R∞ ⊗[R i] X :=
    TensorProduct.congr eAlg.toLinearEquiv (LinearEquiv.refl (R i) X)
  -- Route correction: prove semilinearity on pure tensors first, then extend additively so the
  -- tensor transport stays explicit and does not rely on elaborator search across coercions.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · calc
      eX (r • (0 : tailLimit ⊗[R i] X)) = eX 0 := by rw [smul_zero]
      _ = 0 := by simpa using eX.map_zero
      _ = eAlg r • 0 := by simp
      _ = eAlg r • eX (0 : tailLimit ⊗[R i] X) := by simp
  · intro a x
    calc
      eX (r • a ⊗ₜ[R i] x) = eX ((r * a) ⊗ₜ[R i] x) := by
        change eX (((r • a : tailLimit) ⊗ₜ[R i] x)) = eX ((r * a) ⊗ₜ[R i] x)
        simp [Algebra.smul_def]
      _ = eAlg (r * a) ⊗ₜ[R i] x := by
        simp [eX]
      _ = (eAlg r * eAlg a) ⊗ₜ[R i] x := by
        rw [map_mul]
      _ = eAlg r • (eAlg a ⊗ₜ[R i] x) := by
        change ((eAlg r * eAlg a) ⊗ₜ[R i] x) = ((eAlg r • eAlg a : R∞) ⊗ₜ[R i] x)
        simp [Algebra.smul_def]
      _ = eAlg r • eX (a ⊗ₜ[R i] x) := by
        simp [eX]
  · intro z₁ z₂ hz₁ hz₂
    calc
      eX (r • (z₁ + z₂)) = eX (r • z₁ + r • z₂) := by rw [smul_add]
      _ = eX (r • z₁) + eX (r • z₂) := by
            simpa using eX.map_add (r • z₁) (r • z₂)
      _ = eAlg r • eX z₁ + eAlg r • eX z₂ := by rw [hz₁, hz₂]
      _ = eAlg r • (eX z₁ + eX z₂) := by rw [smul_add]
      _ = eAlg r • eX (z₁ + z₂) := by rw [eX.map_add]

/-- Helper for Lemma 10.127.6: transporting `liftBaseChange` across the owner tail/full tensor
comparison applies the same transport to the underlying stage factor. -/
private theorem owner_tail_liftBaseChange_to_full
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (g :
      let tailLimit :=
        Ring.DirectLimit
          (tail_ring_family (R := R) i)
          (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
      letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
      M_i →ₗ[R i] tailLimit ⊗[R i] N_i) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
      TensorProduct.congr
        (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
        (LinearEquiv.refl (R i) M_i)
    let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
      TensorProduct.congr
        (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
        (LinearEquiv.refl (R i) N_i)
    eN.toLinearMap ∘ₗ (g.liftBaseChange tailLimit).restrictScalars (R i) =
      ((liftBaseChange R∞ (eN.toLinearMap.comp g)).restrictScalars (R i)) ∘ₗ eM.toLinearMap := by
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  let eAlg := owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i
  let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
    TensorProduct.congr eAlg.toLinearEquiv (LinearEquiv.refl (R i) M_i)
  let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
    TensorProduct.congr eAlg.toLinearEquiv (LinearEquiv.refl (R i) N_i)
  -- Proof comment: both maps are `R i`-linear on the tensor source, so it is enough to compare
  -- them on pure tensors and use the semilinearity of the transported tensor equivalence.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro r m
    calc
      (eN.toLinearMap ∘ₗ (g.liftBaseChange tailLimit).restrictScalars (R i))
          (r ⊗ₜ[R i] m) =
        eN.toLinearMap ((g.liftBaseChange tailLimit) (r ⊗ₜ[R i] m)) := by
          rfl
      _ = eN.toLinearMap (r • g m) := by
          rw [LinearMap.liftBaseChange_tmul]
      _ = eAlg r • eN.toLinearMap (g m) := by
          simpa [eAlg] using
            owner_tail_tensor_equiv_smul
              (R := R) (f := f) (i := i) (X := N_i) r (g m)
      _ = (liftBaseChange R∞ (eN.toLinearMap.comp g)) (eAlg r ⊗ₜ[R i] m) := by
          rw [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply]
      _ =
        (((liftBaseChange R∞ (eN.toLinearMap.comp g)).restrictScalars (R i)) ∘ₗ eM.toLinearMap)
          (r ⊗ₜ[R i] m) := by
          simp [eAlg, eM, LinearMap.comp_apply]
  · intro z₁ z₂ hz₁ hz₂
    calc
      (eN.toLinearMap ∘ₗ (g.liftBaseChange tailLimit).restrictScalars (R i)) (z₁ + z₂) =
        (eN.toLinearMap ∘ₗ (g.liftBaseChange tailLimit).restrictScalars (R i)) z₁ +
          (eN.toLinearMap ∘ₗ (g.liftBaseChange tailLimit).restrictScalars (R i)) z₂ := by
            simp
      _ =
        (((liftBaseChange R∞ (eN.toLinearMap.comp g)).restrictScalars (R i)) ∘ₗ eM.toLinearMap)
            z₁ +
          (((liftBaseChange R∞ (eN.toLinearMap.comp g)).restrictScalars (R i)) ∘ₗ eM.toLinearMap)
            z₂ := by
              rw [hz₁, hz₂]
      _ =
        (((liftBaseChange R∞ (eN.toLinearMap.comp g)).restrictScalars (R i)) ∘ₗ eM.toLinearMap)
          (z₁ + z₂) := by
            simp

/-- Helper for Lemma 10.127.6: conjugating the owner-tail input map back to the ambient direct
limit recovers the original morphism `φ`. -/
private theorem owner_tail_input_transport_eq
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (φ : R∞ ⊗[R i] M_i →ₗ[R∞] R∞ ⊗[R i] N_i) :
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
      TensorProduct.congr
        (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
        (LinearEquiv.refl (R i) M_i)
    let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
      TensorProduct.congr
        (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
        (LinearEquiv.refl (R i) N_i)
    let gInf : M_i →ₗ[R i] R∞ ⊗[R i] N_i := (LinearMap.liftBaseChangeEquiv R∞).symm φ
    let gTail : M_i →ₗ[R i] tailLimit ⊗[R i] N_i := eN.symm.toLinearMap.comp gInf
    eN.toLinearMap ∘ₗ (gTail.liftBaseChange tailLimit).restrictScalars (R i) =
      φ.restrictScalars (R i) ∘ₗ eM.toLinearMap := by
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  let eAlg := owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i
  let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
    TensorProduct.congr eAlg.toLinearEquiv (LinearEquiv.refl (R i) M_i)
  let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
    TensorProduct.congr eAlg.toLinearEquiv (LinearEquiv.refl (R i) N_i)
  let gInf : M_i →ₗ[R i] R∞ ⊗[R i] N_i := (LinearMap.liftBaseChangeEquiv R∞).symm φ
  let gTail : M_i →ₗ[R i] tailLimit ⊗[R i] N_i := eN.symm.toLinearMap.comp gInf
  have hcomp : eN.toLinearMap.comp gTail = gInf := by
    -- Proof comment: `gTail` was defined by conjugating `gInf` with the tail/full tensor
    -- equivalence on the target.
    ext m
    simp [gTail, gInf, LinearMap.comp_apply]
  have hphi :
      (liftBaseChange R∞ gInf).restrictScalars (R i) = φ.restrictScalars (R i) := by
    -- Proof comment: `gInf` is by definition the inverse image of `φ` under
    -- `LinearMap.liftBaseChangeEquiv`.
    simpa [gInf] using
      congrArg
        (fun u : R∞ ⊗[R i] M_i →ₗ[R∞] R∞ ⊗[R i] N_i ↦ u.restrictScalars (R i))
        ((LinearMap.liftBaseChangeEquiv (R∞)).apply_symm_apply φ)
  calc
    eN.toLinearMap ∘ₗ (gTail.liftBaseChange tailLimit).restrictScalars (R i) =
      ((liftBaseChange R∞ (eN.toLinearMap.comp gTail)).restrictScalars (R i)) ∘ₗ
        eM.toLinearMap := by
          simpa [eM, eN, gTail] using
            owner_tail_liftBaseChange_to_full
              (R := R) (f := f) (i := i) (M_i := M_i) (N_i := N_i) gTail
    _ = ((liftBaseChange R∞ gInf).restrictScalars (R i)) ∘ₗ eM.toLinearMap := by
          rw [hcomp]
    _ = φ.restrictScalars (R i) ∘ₗ eM.toLinearMap := by
          rw [hphi]

/-- Helper for Lemma 10.127.6: transporting the owner-tail descended stage factor to `R∞`
matches the ambient stage factor obtained from the same stage map. -/
private theorem owner_tail_stage_factor_liftBaseChange_to_full
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (j : Set.Ici i)
    (g :
      let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
      M_i →ₗ[R i] R j.1 ⊗[R i] N_i) :
    letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
      tail_ring_family_algebra_family (R := R) (f := f) i
    letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
    letI :
        DirectedSystem (tail_ring_family (R := R) i)
          (fun j' k' hjk ↦
            ((tail_transition_algHom (R := R) (f := f) i hjk :
              R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
      tail_directedSystem_algHom (R := R) (f := f) i
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
      TensorProduct.congr
        (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
        (LinearEquiv.refl (R i) M_i)
    let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
      TensorProduct.congr
        (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
        (LinearEquiv.refl (R i) N_i)
    let tailStage : M_i →ₗ[R i] tailLimit ⊗[R i] N_i :=
      (_root_.stageTensorMap
        (A := R i)
        (R := tail_ring_family (R := R) i)
        (f := fun j' k' hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
        (X := N_i) j).comp g
    let fullStage : M_i →ₗ[R i] R∞ ⊗[R i] N_i :=
      let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
      let _ : Algebra (R j.1) R∞ := stageDirectLimitAlgebra R f j.1
      let _ : IsScalarTower (R i) (R j.1) R∞ := directLimitStage_isScalarTower R f j.2
      (LinearMap.rTensor N_i ((Algebra.linearMap (R j.1) R∞).restrictScalars (R i))).comp g
    eN.toLinearMap ∘ₗ (liftBaseChange tailLimit tailStage).restrictScalars (R i) =
      ((liftBaseChange R∞ fullStage).restrictScalars (R i)) ∘ₗ eM.toLinearMap := by
  letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
    tail_ring_family_algebra_family (R := R) (f := f) i
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
  letI :
      DirectedSystem (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦
          ((tail_transition_algHom (R := R) (f := f) i hjk :
            R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
    tail_directedSystem_algHom (R := R) (f := f) i
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  let eAlg := owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i
  let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
    TensorProduct.congr eAlg.toLinearEquiv (LinearEquiv.refl (R i) M_i)
  let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
    TensorProduct.congr eAlg.toLinearEquiv (LinearEquiv.refl (R i) N_i)
  let tailStage : M_i →ₗ[R i] tailLimit ⊗[R i] N_i :=
    (_root_.stageTensorMap
      (A := R i)
      (R := tail_ring_family (R := R) i)
      (f := fun j' k' hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
      (X := N_i) j).comp g
  let fullStage : M_i →ₗ[R i] R∞ ⊗[R i] N_i :=
    let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
    let _ : Algebra (R j.1) R∞ := stageDirectLimitAlgebra R f j.1
    let _ : IsScalarTower (R i) (R j.1) R∞ := directLimitStage_isScalarTower R f j.2
    (LinearMap.rTensor N_i ((Algebra.linearMap (R j.1) R∞).restrictScalars (R i))).comp g
  have hstage : eN.toLinearMap.comp tailStage = fullStage := by
    -- Proof comment: `owner_stageTensorMap_to_full` identifies the transported tail stage factor
    -- with the ambient one pointwise on the chosen stage map `g`.
    ext m
    simpa [tailStage, fullStage, eN, LinearMap.comp_apply] using
      owner_stageTensorMap_to_full
        (R := R) (f := f) (i := i) (X := N_i) j (g m)
  calc
    eN.toLinearMap ∘ₗ (liftBaseChange tailLimit tailStage).restrictScalars (R i) =
      ((liftBaseChange R∞ (eN.toLinearMap.comp tailStage)).restrictScalars (R i)) ∘ₗ
        eM.toLinearMap := by
          simpa [eM, eN, tailStage] using
            owner_tail_liftBaseChange_to_full
              (R := R) (f := f) (i := i) (M_i := M_i) (N_i := N_i) tailStage
    _ = ((liftBaseChange R∞ fullStage).restrictScalars (R i)) ∘ₗ eM.toLinearMap := by
          rw [hstage]

/-- Helper for Lemma 10.127.6: the owner-tail descended output rewrites to an equality of
rebased stage factors after forgetting to the base stage `R i`. -/
private theorem owner_tail_descended_output_restrict
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
      [Module.FinitePresentation (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (φ : R∞ ⊗[R i] M_i →ₗ[R∞] R∞ ⊗[R i] N_i)
    (j : Set.Ici i)
    (φ_j :
      let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
      R j.1 ⊗[R i] M_i →ₗ[R j.1] R j.1 ⊗[R i] N_i)
    (hdesc :
      letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
        tail_ring_family_algebra_family (R := R) (f := f) i
      letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
      letI :
          DirectedSystem (tail_ring_family (R := R) i)
            (fun j' k' hjk ↦
              ((tail_transition_algHom (R := R) (f := f) i hjk :
                R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
        tail_directedSystem_algHom (R := R) (f := f) i
      let tailLimit :=
        Ring.DirectLimit
          (tail_ring_family (R := R) i)
          (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
      letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
      let _ : Algebra (R j.1) tailLimit :=
        (Ring.DirectLimit.of
          (tail_ring_family (R := R) i)
          (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
          j).toAlgebra
      let _ : IsScalarTower (R i) (R j.1) tailLimit :=
        owner_tail_directLimit_isScalarTower (R := R) (f := f) i j
      let e := (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
      let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
        TensorProduct.congr e (LinearEquiv.refl (R i) M_i)
      let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
        TensorProduct.congr e (LinearEquiv.refl (R i) N_i)
      let gInf : M_i →ₗ[R i] R∞ ⊗[R i] N_i := (LinearMap.liftBaseChangeEquiv R∞).symm φ
      let gTail : M_i →ₗ[R i] tailLimit ⊗[R i] N_i := eN.symm.toLinearMap.comp gInf
      (cancelBaseChange (R i) (R j.1) tailLimit tailLimit N_i).toLinearMap ∘ₗ
          φ_j.baseChange tailLimit ∘ₗ
            (cancelBaseChange (R i) (R j.1) tailLimit tailLimit M_i).symm.toLinearMap =
        gTail.liftBaseChange tailLimit) :
    letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
      tail_ring_family_algebra_family (R := R) (f := f) i
    letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
    letI :
        DirectedSystem (tail_ring_family (R := R) i)
          (fun j' k' hjk ↦
            ((tail_transition_algHom (R := R) (f := f) i hjk :
              R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
      tail_directedSystem_algHom (R := R) (f := f) i
    let tailLimit :=
      Ring.DirectLimit
        (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
    letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
    let e := (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
    let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
      TensorProduct.congr e (LinearEquiv.refl (R i) M_i)
    let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
      TensorProduct.congr e (LinearEquiv.refl (R i) N_i)
    let gInf : M_i →ₗ[R i] R∞ ⊗[R i] N_i := (LinearMap.liftBaseChangeEquiv R∞).symm φ
    let gTail : M_i →ₗ[R i] tailLimit ⊗[R i] N_i := eN.symm.toLinearMap.comp gInf
    let gStage :
        let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
        M_i →ₗ[R i] R j.1 ⊗[R i] N_i :=
      (LinearMap.liftBaseChangeEquiv (R j.1)).symm φ_j
    let tailStage : M_i →ₗ[R i] tailLimit ⊗[R i] N_i :=
      (_root_.stageTensorMap
        (A := R i)
        (R := tail_ring_family (R := R) i)
        (f := fun j' k' hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
        (X := N_i) j).comp gStage
    ((liftBaseChange tailLimit tailStage).restrictScalars (R i)) =
      (gTail.liftBaseChange tailLimit).restrictScalars (R i) := by
  letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
    tail_ring_family_algebra_family (R := R) (f := f) i
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
  letI :
      DirectedSystem (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦
          ((tail_transition_algHom (R := R) (f := f) i hjk :
            R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
    tail_directedSystem_algHom (R := R) (f := f) i
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  let e := (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
  let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
    TensorProduct.congr e (LinearEquiv.refl (R i) M_i)
  let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
    TensorProduct.congr e (LinearEquiv.refl (R i) N_i)
  let gInf : M_i →ₗ[R i] R∞ ⊗[R i] N_i := (LinearMap.liftBaseChangeEquiv R∞).symm φ
  let gTail : M_i →ₗ[R i] tailLimit ⊗[R i] N_i := eN.symm.toLinearMap.comp gInf
  let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
  let _ : Algebra (R j.1) tailLimit :=
    (Ring.DirectLimit.of
      (tail_ring_family (R := R) i)
      (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
      j).toAlgebra
  let _ : IsScalarTower (R i) (R j.1) tailLimit :=
    owner_tail_directLimit_isScalarTower (R := R) (f := f) i j
  let gStage : M_i →ₗ[R i] R j.1 ⊗[R i] N_i :=
    (LinearMap.liftBaseChangeEquiv (R j.1)).symm φ_j
  let tailStage : M_i →ₗ[R i] tailLimit ⊗[R i] N_i :=
    (_root_.stageTensorMap
      (A := R i)
      (R := tail_ring_family (R := R) i)
      (f := fun j' k' hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
      (X := N_i) j).comp gStage
  have hstage :
      (cancelBaseChange (R i) (R j.1) tailLimit tailLimit N_i).toLinearMap ∘ₗ
          φ_j.baseChange tailLimit ∘ₗ
            (cancelBaseChange (R i) (R j.1) tailLimit tailLimit M_i).symm.toLinearMap =
        liftBaseChange tailLimit tailStage := by
    -- Proof comment: this is the owner theorem's standard rebase identity, rewritten using the
    -- explicit stage factor `gStage` over the tail system.
    simpa [gStage, tailStage, _root_.stageTensorMap] using
      (stage_factor_rebase_eq_liftBaseChange
        (A := R i)
        (I := Set.Ici i)
        (R := tail_ring_family (R := R) i)
        (M := N_i) (N := M_i) (i := j) (S := tailLimit) gStage)
  have hlift :
      liftBaseChange tailLimit tailStage = gTail.liftBaseChange tailLimit := by
    calc
      liftBaseChange tailLimit tailStage =
          (cancelBaseChange (R i) (R j.1) tailLimit tailLimit N_i).toLinearMap ∘ₗ
            φ_j.baseChange tailLimit ∘ₗ
              (cancelBaseChange (R i) (R j.1) tailLimit tailLimit M_i).symm.toLinearMap := by
            symm
            exact hstage
      _ = gTail.liftBaseChange tailLimit := hdesc
  have hstage_eq : tailStage = gTail := by
    -- Proof comment: `liftBaseChange` is an equivalence on stage factors, so equality of the
    -- rebased maps already identifies the underlying `R i`-linear stage maps.
    exact (LinearMap.liftBaseChangeEquiv tailLimit).injective hlift
  -- Proof comment: the target is just the restricted form of the equality of the two stage maps.
  exact congrArg
    (fun u : M_i →ₗ[R i] tailLimit ⊗[R i] N_i ↦
      (liftBaseChange tailLimit u).restrictScalars (R i))
    hstage_eq

/-- Helper for Lemma 10.127.6: the restricted owner-tail descended equality transports back to the
ambient `R∞`-linear descent identity. -/
private theorem owner_tail_descended_output_to_full
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
      [Module.FinitePresentation (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (φ : R∞ ⊗[R i] M_i →ₗ[R∞] R∞ ⊗[R i] N_i)
    (j : Set.Ici i)
    (φ_j :
      let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
      R j.1 ⊗[R i] M_i →ₗ[R j.1] R j.1 ⊗[R i] N_i)
    (hrestrict :
      letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
        tail_ring_family_algebra_family (R := R) (f := f) i
      letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
      letI :
          DirectedSystem (tail_ring_family (R := R) i)
            (fun j' k' hjk ↦
              ((tail_transition_algHom (R := R) (f := f) i hjk :
                R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
        tail_directedSystem_algHom (R := R) (f := f) i
      let tailLimit :=
        Ring.DirectLimit
          (tail_ring_family (R := R) i)
          (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
      letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
      let e := (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
      let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
        TensorProduct.congr e (LinearEquiv.refl (R i) M_i)
      let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
        TensorProduct.congr e (LinearEquiv.refl (R i) N_i)
      let gInf : M_i →ₗ[R i] R∞ ⊗[R i] N_i := (LinearMap.liftBaseChangeEquiv R∞).symm φ
      let gTail : M_i →ₗ[R i] tailLimit ⊗[R i] N_i := eN.symm.toLinearMap.comp gInf
      let gStage :
          let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
          M_i →ₗ[R i] R j.1 ⊗[R i] N_i :=
        (LinearMap.liftBaseChangeEquiv (R j.1)).symm φ_j
      let tailStage : M_i →ₗ[R i] tailLimit ⊗[R i] N_i :=
        (_root_.stageTensorMap
          (A := R i)
          (R := tail_ring_family (R := R) i)
          (f := fun j' k' hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
          (X := N_i) j).comp gStage
      ((liftBaseChange tailLimit tailStage).restrictScalars (R i)) =
        (gTail.liftBaseChange tailLimit).restrictScalars (R i)) :
    let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
    let _ : Algebra (R j.1) R∞ := stageDirectLimitAlgebra R f j.1
    let _ : IsScalarTower (R i) (R j.1) R∞ := directLimitStage_isScalarTower R f j.2
    (cancelBaseChange (R i) (R j.1) R∞ R∞ N_i).toLinearMap ∘ₗ
        φ_j.baseChange R∞ ∘ₗ
          (cancelBaseChange (R i) (R j.1) R∞ R∞ M_i).symm.toLinearMap =
      φ := by
  letI : ∀ j' : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j') :=
    tail_ring_family_algebra_family (R := R) (f := f) i
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
  letI :
      DirectedSystem (tail_ring_family (R := R) i)
        (fun j' k' hjk ↦
          ((tail_transition_algHom (R := R) (f := f) i hjk :
            R j'.1 →ₐ[R i] R k'.1) : R j'.1 →+* R k'.1)) :=
    tail_directedSystem_algHom (R := R) (f := f) i
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j' k' hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  let e := (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
  let eM : tailLimit ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
    TensorProduct.congr e (LinearEquiv.refl (R i) M_i)
  let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
    TensorProduct.congr e (LinearEquiv.refl (R i) N_i)
  let gInf : M_i →ₗ[R i] R∞ ⊗[R i] N_i := (LinearMap.liftBaseChangeEquiv R∞).symm φ
  let gTail : M_i →ₗ[R i] tailLimit ⊗[R i] N_i := eN.symm.toLinearMap.comp gInf
  let _ : Algebra (R i) (R j.1) := (f i j.1 j.2).toAlgebra
  let _ : Algebra (R j.1) R∞ := stageDirectLimitAlgebra R f j.1
  let _ : IsScalarTower (R i) (R j.1) R∞ := directLimitStage_isScalarTower R f j.2
  let gStage : M_i →ₗ[R i] R j.1 ⊗[R i] N_i :=
    (LinearMap.liftBaseChangeEquiv (R j.1)).symm φ_j
  let tailStage : M_i →ₗ[R i] tailLimit ⊗[R i] N_i :=
    (_root_.stageTensorMap
      (A := R i)
      (R := tail_ring_family (R := R) i)
      (f := fun j' k' hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
      (X := N_i) j).comp gStage
  let fullStage : M_i →ₗ[R i] R∞ ⊗[R i] N_i :=
    (LinearMap.rTensor N_i ((Algebra.linearMap (R j.1) R∞).restrictScalars (R i))).comp gStage
  have htransport :
      eN.toLinearMap ∘ₗ ((liftBaseChange tailLimit tailStage).restrictScalars (R i)) =
        eN.toLinearMap ∘ₗ (gTail.liftBaseChange tailLimit).restrictScalars (R i) := by
    -- Proof comment: compose the restricted equality with the tail/full tensor comparison.
    exact congrArg
      (fun u :
        tailLimit ⊗[R i] M_i →ₗ[R i] tailLimit ⊗[R i] N_i ↦
          eN.toLinearMap ∘ₗ u)
      hrestrict
  have hcomp :
      ((liftBaseChange R∞ fullStage).restrictScalars (R i)) ∘ₗ eM.toLinearMap =
        φ.restrictScalars (R i) ∘ₗ eM.toLinearMap := by
    calc
      ((liftBaseChange R∞ fullStage).restrictScalars (R i)) ∘ₗ eM.toLinearMap =
          eN.toLinearMap ∘ₗ ((liftBaseChange tailLimit tailStage).restrictScalars (R i)) := by
            symm
            simpa [eM, eN, tailStage, fullStage, gStage] using
              owner_tail_stage_factor_liftBaseChange_to_full
                (R := R) (f := f) (i := i) (M_i := M_i) (N_i := N_i) j gStage
      _ = eN.toLinearMap ∘ₗ (gTail.liftBaseChange tailLimit).restrictScalars (R i) := htransport
      _ = φ.restrictScalars (R i) ∘ₗ eM.toLinearMap := by
            simpa [eM, eN, gInf, gTail] using
              owner_tail_input_transport_eq
                (R := R) (f := f) (i := i) (M_i := M_i) (N_i := N_i) φ
  have hfull_restrict :
      (liftBaseChange R∞ fullStage).restrictScalars (R i) = φ.restrictScalars (R i) := by
    -- Proof comment: `eM` is an equivalence, so equality after postcomposition with `eM`
    -- determines equality of the underlying `R i`-linear maps.
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := eM.surjective z
    exact congrArg
      (fun u :
        tailLimit ⊗[R i] M_i →ₗ[R i] R∞ ⊗[R i] N_i ↦ u w)
      hcomp
  have hfull : liftBaseChange R∞ fullStage = φ := by
    -- Proof comment: the restricted equality already identifies the underlying functions of the
    -- two `R∞`-linear maps.
    apply LinearMap.ext
    intro z
    exact congrArg
      (fun u :
        R∞ ⊗[R i] M_i →ₗ[R i] R∞ ⊗[R i] N_i ↦ u z)
      hfull_restrict
  have hstage :
      (cancelBaseChange (R i) (R j.1) R∞ R∞ N_i).toLinearMap ∘ₗ
          φ_j.baseChange R∞ ∘ₗ
            (cancelBaseChange (R i) (R j.1) R∞ R∞ M_i).symm.toLinearMap =
        liftBaseChange R∞ fullStage := by
    -- Proof comment: this is the two-stage base-change identity for the descended stage map
    -- `gStage`, checked directly on pure tensors and extended by tensor induction.
    apply DFunLike.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        change (0 : R∞ ⊗[R i] N_i) = 0
        simp
    | add z₁ z₂ hz₁ hz₂ =>
        rw [LinearMap.map_add, LinearMap.map_add, hz₁, hz₂]
    | tmul r m =>
        have hgStage :
            φ_j ((1 : R j.1) ⊗ₜ[R i] m) = gStage m := by
          simpa [gStage] using
            congrArg
              (fun u : M_i →ₗ[R i] R j.1 ⊗[R i] N_i ↦ u m)
              ((LinearMap.liftBaseChangeEquiv (R j.1)).apply_symm_apply φ_j)
        change
          (cancelBaseChange (R i) (R j.1) R∞ R∞ N_i)
            ((φ_j.baseChange R∞)
              ((cancelBaseChange (R i) (R j.1) R∞ R∞ M_i).symm (r ⊗ₜ[R i] m))) =
            (liftBaseChange R∞ fullStage) (r ⊗ₜ[R i] m)
        rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
        rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul]
        rw [hgStage]
        calc
          (cancelBaseChange (R i) (R j.1) R∞ R∞ N_i) (r ⊗ₜ[R j.1] gStage m) =
              (cancelBaseChange (R i) (R j.1) R∞ R∞ N_i)
                (r • ((1 : R∞) ⊗ₜ[R j.1] gStage m)) := by
                  congr 1
                  rw [TensorProduct.smul_tmul']
                  simpa [smul_eq_mul] using
                    congrArg (fun s : R∞ ↦ s ⊗ₜ[R j.1] gStage m) (mul_one r).symm
          _ = r •
              (cancelBaseChange (R i) (R j.1) R∞ R∞ N_i)
                ((1 : R∞) ⊗ₜ[R j.1] gStage m) := by
                  rw [map_smul]
          _ = r •
              (LinearMap.rTensor N_i
                ((Algebra.linearMap (R j.1) R∞).restrictScalars (R i)))
                (gStage m) := by
                  rw [cancelBaseChange_one_tmul_eq_rTensor_restrictScalars]
          _ = (liftBaseChange R∞ fullStage) (r ⊗ₜ[R i] m) := by
                  rw [LinearMap.liftBaseChange_tmul]
                  simp [fullStage, LinearMap.comp_apply]
  calc
    (cancelBaseChange (R i) (R j.1) R∞ R∞ N_i).toLinearMap ∘ₗ
        φ_j.baseChange R∞ ∘ₗ
          (cancelBaseChange (R i) (R j.1) R∞ R∞ M_i).symm.toLinearMap =
      liftBaseChange R∞ fullStage := hstage
    _ = φ := hfull

/-- Lemma 10.127.6 (2): for a fixed stage `i`, a morphism between the base changes of finitely
presented `R_i`-modules to the colimit ring `R∞` descends after base change from some later stage
`R_j`. -/
-- Proof sketch: specialize `baseChangeLinearMap_descends_of_finitePresentation` from
-- `Lemma_10_127_5` to the restricted tail system `j ≥ i`, then transport the result across the
-- canonical identification of that tail colimit with `R∞`. The owner theorem already packages the
-- descended map using the canonical `cancelBaseChange` comparison. It only needs finite
-- presentation of the source module `M_i`.
theorem finitelyPresented_baseChange_map_descends
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
      [Module.FinitePresentation (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (φ : R∞ ⊗[R i] M_i →ₗ[R∞] R∞ ⊗[R i] N_i) :
    ∃ (j : I) (hij : i ≤ j)
      (φ_j : let _ : Algebra (R i) (R j) := (f i j hij).toAlgebra
        R j ⊗[R i] M_i →ₗ[R j] R j ⊗[R i] N_i),
      let _ : Algebra (R i) (R j) := (f i j hij).toAlgebra
      let _ : Algebra (R j) R∞ := stageDirectLimitAlgebra R f j
      let _ : IsScalarTower (R i) (R j) R∞ := directLimitStage_isScalarTower R f hij
      (cancelBaseChange (R i) (R j) R∞ R∞ N_i).toLinearMap ∘ₗ
          φ_j.baseChange R∞ ∘ₗ
            (cancelBaseChange (R i) (R j) R∞ R∞ M_i).symm.toLinearMap =
        φ := by
  letI : ∀ j : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j) :=
    tail_ring_family_algebra_family (R := R) (f := f) i
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
  letI :
      DirectedSystem (tail_ring_family (R := R) i)
        (fun j k hjk ↦
          ((tail_transition_algHom (R := R) (f := f) i hjk :
            R j.1 →ₐ[R i] R k.1) : R j.1 →+* R k.1)) :=
    tail_directedSystem_algHom (R := R) (f := f) i
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j k hjk ↦ tail_transition_ringHom (R := R) (f := f) i hjk)
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  let e := (owner_tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
  let eN : tailLimit ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
    TensorProduct.congr e (LinearEquiv.refl (R i) N_i)
  let gInf : M_i →ₗ[R i] R∞ ⊗[R i] N_i := (LinearMap.liftBaseChangeEquiv R∞).symm φ
  let gTail : M_i →ₗ[R i] tailLimit ⊗[R i] N_i := eN.symm.toLinearMap.comp gInf
  obtain ⟨j, φ_j, hdesc⟩ :=
    baseChangeLinearMap_descends_of_finitePresentation
      (A := R i)
      (I := Set.Ici i)
      (R := tail_ring_family (R := R) i)
      (f := fun j k hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
      (M := N_i) (N := M_i)
      (v := gTail.liftBaseChange tailLimit)
  have hrestrict :=
    owner_tail_descended_output_restrict
      (R := R) (f := f) (i := i) (M_i := M_i) (N_i := N_i) φ j φ_j hdesc
  have hfull :=
    owner_tail_descended_output_to_full
      (R := R) (f := f) (i := i) (M_i := M_i) (N_i := N_i) φ j φ_j hrestrict
  -- Proof comment: the descended tail-stage map `φ_j` becomes the required ambient witness once
  -- we unpack the tail index `j : Set.Ici i`.
  exact ⟨j.1, j.2, φ_j, hfull⟩

/-- Lemma 10.127.6 (3): for a fixed stage `i`, if two maps between finitely presented
`R_i`-modules become equal after base change to the colimit ring `R∞`, then they already become
equal after base change to some later stage. -/
-- Proof sketch: `Module.FinitePresentation` on `M_i` gives `Module.Finite`, so apply
-- `baseChange_eventually_eq_of_finite` from `Lemma_10_127_5` to the restricted tail system
-- `j ≥ i` and transport the resulting stage equality back along the canonical comparison with
-- `R∞`. No finite-presentation hypothesis on the target `N_i` is needed.
theorem finitelyPresented_baseChange_map_eventually_eq
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
      [Module.FinitePresentation (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (φ_i ψ_i : M_i →ₗ[R i] N_i)
    (h : φ_i.baseChange R∞ = ψ_i.baseChange R∞) :
    ∃ (j : I) (hij : i ≤ j),
      let _ : Algebra (R i) (R j) := (f i j hij).toAlgebra
      φ_i.baseChange (R j) = ψ_i.baseChange (R j) := by
  let e := (tail_directLimit_algEquiv_over_stage (R := R) (f := f) i).toLinearEquiv
  let eM : tail_directLimit (R := R) (f := f) i ⊗[R i] M_i ≃ₗ[R i] R∞ ⊗[R i] M_i :=
    TensorProduct.congr e (LinearEquiv.refl (R i) M_i)
  let eN : tail_directLimit (R := R) (f := f) i ⊗[R i] N_i ≃ₗ[R i] R∞ ⊗[R i] N_i :=
    TensorProduct.congr e (LinearEquiv.refl (R i) N_i)
  have hφ :
      eN.toLinearMap ∘ₗ
          (φ_i.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i) =
        ((φ_i.baseChange R∞).restrictScalars (R i)) ∘ₗ eM.toLinearMap := by
    -- Proof comment: transport the base-changed map from the tail colimit to the ambient colimit.
    simpa [e, eM, eN] using
      (tail_algEquiv_baseChange_transport (R := R) (f := f) i φ_i)
  have hψ :
      eN.toLinearMap ∘ₗ
          (ψ_i.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i) =
        ((ψ_i.baseChange R∞).restrictScalars (R i)) ∘ₗ eM.toLinearMap := by
    -- Proof comment: the same transport identity holds for `ψ_i`.
    simpa [e, eM, eN] using
      (tail_algEquiv_baseChange_transport (R := R) (f := f) i ψ_i)
  have hRinf :
      ((φ_i.baseChange R∞).restrictScalars (R i)) =
        ((ψ_i.baseChange R∞).restrictScalars (R i)) := by
    -- Proof comment: restrict the ambient equality of `R∞`-linear maps to the base stage `R i`.
    simpa using
      congrArg
        (fun u : R∞ ⊗[R i] M_i →ₗ[R∞] R∞ ⊗[R i] N_i ↦ u.restrictScalars (R i))
        h
  have h_tail_comp :
      eN.toLinearMap ∘ₗ
          (φ_i.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i) =
        eN.toLinearMap ∘ₗ
          (ψ_i.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i) := by
    -- Proof comment: after transporting both sides to `R∞`, the hypothesis `h` identifies them.
    calc
      eN.toLinearMap ∘ₗ
          (φ_i.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i) =
          ((φ_i.baseChange R∞).restrictScalars (R i)) ∘ₗ eM.toLinearMap := hφ
      _ = ((ψ_i.baseChange R∞).restrictScalars (R i)) ∘ₗ eM.toLinearMap := by
            rw [hRinf]
      _ = eN.toLinearMap ∘ₗ
          (ψ_i.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i) := hψ.symm
  have h_tail_restrict :
      (φ_i.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i) =
        (ψ_i.baseChange (tail_directLimit (R := R) (f := f) i)).restrictScalars (R i) := by
    apply LinearMap.ext
    intro z
    -- Proof comment: evaluate the transported equality and use injectivity of the tail/full
    -- coefficient equivalence on the target tensor product.
    apply eN.injective
    exact congrArg
      (fun u :
        tail_directLimit (R := R) (f := f) i ⊗[R i] M_i →ₗ[R i]
          R∞ ⊗[R i] N_i ↦ u z)
      h_tail_comp
  have h_tail :
      φ_i.baseChange (tail_directLimit (R := R) (f := f) i) =
        ψ_i.baseChange (tail_directLimit (R := R) (f := f) i) := by
    apply LinearMap.ext
    intro z
    -- Proof comment: equality of the restricted `R i`-linear maps is equality of the original
    -- tail-colimit-linear maps because they have the same underlying function.
    exact congrArg
      (fun u :
        tail_directLimit (R := R) (f := f) i ⊗[R i] M_i →ₗ[R i]
          tail_directLimit (R := R) (f := f) i ⊗[R i] N_i ↦ u z)
      h_tail_restrict
  letI : ∀ j : Set.Ici i, Algebra (R i) (tail_ring_family (R := R) i j) :=
    tail_ring_family_algebra_family (R := R) (f := f) i
  letI : IsDirectedOrder (Set.Ici i) := tail_index_isDirected (i := i)
  letI :
      DirectedSystem (tail_ring_family (R := R) i)
        (fun j k hjk ↦
          ((tail_transition_algHom (R := R) (f := f) i hjk :
            R j.1 →ₐ[R i] R k.1) : R j.1 →+* R k.1)) :=
    tail_directedSystem_algHom (R := R) (f := f) i
  let tailLimit :=
    Ring.DirectLimit
      (tail_ring_family (R := R) i)
      (fun j k hjk ↦
        ((tail_transition_algHom (R := R) (f := f) i hjk :
          R j.1 →ₐ[R i] R k.1) : R j.1 →+* R k.1))
  letI : Algebra (R i) tailLimit := owner_tail_directLimitAlgebra (R := R) (f := f) i
  have h_owner :
      φ_i.baseChange tailLimit = ψ_i.baseChange tailLimit :=
    owner_tail_baseChange_eq_of_canonical_tail_eq
      (R := R) (f := f) i φ_i ψ_i h_tail
  obtain ⟨j, hj⟩ :=
    baseChange_eventually_eq_of_finite
      (A := R i)
      (I := Set.Ici i)
      (R := tail_ring_family (R := R) i)
      (f := fun j k hjk ↦ tail_transition_algHom (R := R) (f := f) i hjk)
      (M := M_i) (N := N_i) φ_i ψ_i h_owner
  -- Proof comment: unpack the tail index `j : Set.Ici i` to the ambient stage `j.1`.
  exact ⟨j.1, j.2, by simpa [tailLimit] using hj⟩

end
