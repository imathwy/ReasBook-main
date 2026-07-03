import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_101_1 (from Chap10) -/
open IsLocalRing
open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]
variable {A : Type w}

local notation "𝔪" => maximalIdeal R
local notation "k" => IsLocalRing.ResidueField R
local notation "M̄" => M ⧸ (𝔪 • (⊤ : Submodule R M))
local notation "mkQ𝔪" => Submodule.mkQ (𝔪 • (⊤ : Submodule R M))

local instance : Module k M̄ := inferInstanceAs (Module (R ⧸ 𝔪) M̄)
local instance : SMulCommClass R k M̄ := inferInstanceAs (SMulCommClass R (R ⧸ 𝔪) M̄)
local instance : IsScalarTower R k M̄ := inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) M̄)
local instance : Module k (M →ₗ[R] M̄) := inferInstanceAs (Module (R ⧸ 𝔪) (M →ₗ[R] M̄))
local instance : SMulCommClass R k (M →ₗ[R] M̄) :=
  inferInstanceAs (SMulCommClass R (R ⧸ 𝔪) (M →ₗ[R] M̄))
local instance : IsScalarTower R k (M →ₗ[R] M̄) :=
  inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) (M →ₗ[R] M̄))

-- Proof sketch: the forward implication is immediate by mapping a basis along the quotient map.
-- For the converse, Nakayama's lemma shows that lifts of a residue-field basis generate `M`.
-- Presenting `M` as a quotient of the free module on `A`, flatness keeps the kernel exact after
-- reduction modulo `maximalIdeal R`, and the quotient basis forces that kernel to vanish modulo the
-- maximal ideal. A second application of Nakayama to the kernel, using nilpotence of
-- `maximalIdeal R`, shows the generators are linearly independent.
/-
Layering for this item:
- `source-facing`: the family `x : A → M` and its reduction modulo `𝔪`;
- `core/canonical`: `Module.Basis`, `Algebra.TensorProduct.basis`,
  `IsLocalRing.linearIndependent_of_flat`, and the nilpotent Nakayama span criterion;
- `bridge/view`: the canonical comparison `((R ⧸ 𝔪) ⊗[R] M) ≃ₗ[R ⧸ 𝔪] M̄`.
-/
/-- Lemma 10.101.1: for a flat module over a local ring with nilpotent maximal ideal, a family
`x : A → M` is an `R`-basis exactly when its images in `M / maximalIdeal R • M` form a basis over
`R / maximalIdeal R`. -/
theorem basis_iff_basis_mod_maximalIdeal_of_flat_of_nilpotent_maximalIdeal
    (h_nil : IsNilpotent 𝔪)
    (x : A → M) :
    (∃ bbar : Module.Basis A k M̄, ∀ a, bbar a = mkQ𝔪 (x a)) ↔
      ∃ b : Module.Basis A R M, ∀ a, b a = x a := by
  classical
  let f : k →ₗ[k] M →ₗ[R] M̄ :=
    (LinearMap.ringLmapEquivSelf k k (M →ₗ[R] M̄)).symm mkQ𝔪
  let e₀ : (k ⊗[R] M) →ₗ[k] M̄ :=
    TensorProduct.AlgebraTensorModule.lift f
  have e₀_apply (y : M) : e₀ ((1 : k) ⊗ₜ[R] y) = mkQ𝔪 y := by
    simp [e₀, f]
  have e₀_restrictScalars :
      e₀.restrictScalars R = (TensorProduct.quotTensorEquivQuotSMul M 𝔪).toLinearMap := by
    apply TensorProduct.ext'
    intro r y
    refine Quotient.inductionOn r ?_
    intro a
    change e₀ (Ideal.Quotient.mk 𝔪 a ⊗ₜ[R] y) =
      TensorProduct.quotTensorEquivQuotSMul M 𝔪 (Ideal.Quotient.mk 𝔪 a ⊗ₜ[R] y)
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    simp [e₀, f]
    simpa using (algebraMap_smul k a (Submodule.Quotient.mk y))
  let e : (k ⊗[R] M) ≃ₗ[k] M̄ :=
    LinearEquiv.ofBijective e₀
      ⟨by
        intro u v huv
        have huv' : e₀.restrictScalars R u = e₀.restrictScalars R v := huv
        rw [e₀_restrictScalars] at huv'
        exact (TensorProduct.quotTensorEquivQuotSMul M 𝔪).injective huv'
      , by
        intro z
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (𝔪 • (⊤ : Submodule R M)) z
        exact ⟨(1 : k) ⊗ₜ[R] y, e₀_apply y⟩⟩
  have e_apply (y : M) : e ((1 : k) ⊗ₜ[R] y) = mkQ𝔪 y := e₀_apply y
  constructor
  · rintro ⟨bbar, hbbar⟩
    have hmkQx : mkQ𝔪 ∘ x = bbar := by
      funext a
      exact (hbbar a).symm
    have hx_tensor_li :
        LinearIndependent k (TensorProduct.mk R k M 1 ∘ x) := by
      refine ((e.toLinearMap).linearIndependent_iff (by simp)).mp ?_
      have hcomp : e ∘ TensorProduct.mk R k M 1 ∘ x = bbar := by
        funext a
        simpa [hbbar a] using e_apply (x a)
      simpa [hcomp] using bbar.linearIndependent
    have hx_li : LinearIndependent R x :=
      Module.IsLocalRing.linearIndependent_of_flat _ hx_tensor_li
    have hgen : Submodule.span R (mkQ𝔪 '' Set.range x) = ⊤ := by
      rw [← Set.range_comp, hmkQx, ← Submodule.restrictScalars_span R (R ⧸ 𝔪)
        Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff]
      exact bbar.span_eq
    have hx_span_eq :
        Submodule.span R (Set.range x) = ⊤ :=
      span_eq_top_of_quotient_span_eq_top_of_isNilpotent 𝔪 (Set.range x) hgen h_nil
    have hbij : Function.Bijective (Finsupp.linearCombination R x) := by
      refine ⟨hx_li, ?_⟩
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      exact hx_span_eq
    refine ⟨Module.Basis.ofRepr (LinearEquiv.ofBijective (Finsupp.linearCombination R x) hbij).symm,
      ?_⟩
    intro a
    simp
  · rintro ⟨b, hb⟩
    let btensor : Module.Basis A (R ⧸ 𝔪) ((R ⧸ 𝔪) ⊗[R] M) :=
      Algebra.TensorProduct.basis (R ⧸ 𝔪) b
    refine ⟨btensor.map e, ?_⟩
    intro a
    change e (btensor a) = mkQ𝔪 (x a)
    simpa [btensor, hb a] using e_apply (x a)

end

/-! ### Lemma_10_101_2 (from Chap10) -/
open IsLocalRing

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

local notation "𝔪" => maximalIdeal R
local notation "M̄" => M ⧸ (𝔪 • (⊤ : Submodule R M))
local notation "mkQ𝔪" => Submodule.mkQ (𝔪 • (⊤ : Submodule R M))

/- Domain triage:
- primary domain: modules over a local ring with nilpotent maximal ideal;
- sampled owner declarations:
  `basis_iff_basis_mod_maximalIdeal_of_flat_of_nilpotent_maximalIdeal`,
  `projective_module_free_of_isLocalRing`,
  `Module.Projective.of_free`,
  `Module.Flat.of_free`;
- owner abstraction: the canonical owner notions are the standard predicates
  `Module.Flat R M`, `Module.Free R M`, and `Module.Projective R M`;
- layer: `bridge/view`, since this file only packages existing owner-form implications into a
  `List.TFAE`;
- primitive data vs derived API: there is no extra primitive data here beyond the ambient module;
  the residue-field basis choice is an internal proof device for deriving freeness from flatness.
-/

-- Proof sketch: choose a basis of the residue-field vector space `M / maximalIdeal R • M`, lift
-- it across the quotient map, and apply Lemma `10.101.1` to obtain a basis of `M`. The remaining
-- equivalence between freeness and projectivity uses the canonical owner declarations
-- `Module.Projective.of_free` and Theorem `10.85.4`.
/-- Lemma 10.101.2: for a module over a local ring with nilpotent maximal ideal, flatness, freeness,
and projectivity are equivalent. -/
theorem flat_free_projective_tfae_of_nilpotent_maximalIdeal
    (h_nil : IsNilpotent 𝔪) :
    List.TFAE [Module.Flat R M, Module.Free R M, Module.Projective R M] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h_flat
      letI := h_flat
      classical
      letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
      let bbar := Module.Free.chooseBasis (R ⧸ 𝔪) M̄
      let x := fun a ↦ Classical.choose (Submodule.mkQ_surjective (𝔪 • (⊤ : Submodule R M)) (bbar a))
      obtain ⟨b, _⟩ :=
        (basis_iff_basis_mod_maximalIdeal_of_flat_of_nilpotent_maximalIdeal h_nil x).mp
          ⟨bbar, fun a ↦ (Classical.choose_spec
            (Submodule.mkQ_surjective (𝔪 • (⊤ : Submodule R M)) (bbar a))).symm⟩
      exact Module.Free.of_basis b
    · intro h_free
      letI := h_free
      infer_instance
  tfae_have 2 ↔ 3 := by
    constructor
    · intro h_free
      letI := h_free
      infer_instance
    · intro h_projective
      letI := h_projective
      exact projective_module_free_of_isLocalRing
  tfae_finish

end

/-! ### Lemma_10_101_3 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators TensorProduct

universe u v

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {A : Type v}
variable {M : Type u} [AddCommGroup M] [Module R M]

local notation "IM" => I • (⊤ : Submodule R M)
local notation "mkQIM" => Submodule.mkQ IM
set_option quotPrecheck false in
local notation "Tor₁[" R "](" N ", " M ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M))

/-- Helper for Lemma 10.101.3: a lifted basis of `M / IM` forces the family `x` to span `M`
once `I` is nilpotent. -/
lemma span_eq_top_of_family_of_quotient_basis
    (x : A → M)
    (hI : IsNilpotent I)
    (hbasis : ∃ bbar : Module.Basis A (R ⧸ I) (M ⧸ IM), ∀ a, bbar a = mkQIM (x a)) :
    Submodule.span R (Set.range x) = ⊤ := by
  rcases hbasis with ⟨bbar, hbbar⟩
  have hmkQx : mkQIM ∘ x = bbar := by
    funext a
    exact (hbbar a).symm
  -- Rewrite the quotient basis span in the `R`-linear form required by Nakayama.
  have hgen : Submodule.span R (mkQIM '' Set.range x) = ⊤ := by
    rw [← Set.range_comp, hmkQx, ← Submodule.restrictScalars_span R (R ⧸ I)
      Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff]
    exact bbar.span_eq
  -- Nilpotent Nakayama upgrades generation modulo `I` to generation upstairs.
  exact span_eq_top_of_quotient_span_eq_top_of_isNilpotent (R := R) (M := M) (I := I)
    (Set.range x) hgen hI

/-- Helper for Lemma 10.101.3: tensoring an exact pair with `R / I` is exact after passing to
quotients by `I`. -/
lemma quotientMapByIdeal_exact
    {N P Q : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : N →ₗ[R] P) (g : P →ₗ[R] Q)
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.quotientMapByIdeal I) (g.quotientMapByIdeal I) := by
  intro y
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) y
    change ((I • (⊤ : Submodule R Q)).mkQ (g x)) = 0 at hx
    have hx' : g x ∈ I • (⊤ : Submodule R Q) := by
      simpa using (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).mp hx
    have hxLift :
        ∃ y : P, y ∈ I • (⊤ : Submodule R P) ∧ g y = g x :=
      Submodule.smul_induction_on hx'
        (fun r hr z _ ↦ by
          obtain ⟨y, rfl⟩ := hg z
          refine ⟨r • y, ?_, by simp⟩
          exact Submodule.smul_mem_smul hr (by simp))
        (fun y z hy hz ↦ by
          rcases hy with ⟨y', hy', rfl⟩
          rcases hz with ⟨z', hz', rfl⟩
          exact ⟨y' + z', Submodule.add_mem _ hy' hz', by simp⟩)
    rcases hxLift with ⟨y, hyI, hy⟩
    have hxy : g (x - y) = 0 := by
      simp [hy]
    rcases (hExact (x - y)).mp hxy with ⟨n, hn⟩
    refine ⟨(I • (⊤ : Submodule R N)).mkQ n, ?_⟩
    change ((I • (⊤ : Submodule R P)).mkQ (f n)) = (I • (⊤ : Submodule R P)).mkQ x
    rw [hn]
    simpa using hyI
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) x
    change ((I • (⊤ : Submodule R Q)).mkQ (g (f x))) = 0
    exact
      (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).2 <| by
        have hfx : g (f x) = 0 := by
          simpa [Function.comp] using congr_fun hExact.comp_eq_zero x
        rw [hfx]
        exact Submodule.zero_mem _

/-- Helper for Lemma 10.101.3: the quotient-by-`I` map is the tensor map with `R ⧸ I` under the
standard quotient-tensor comparison. -/
lemma quotientMapByIdeal_lTensor_naturality
    {N P : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) :
    f.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul N I =
      TensorProduct.quotTensorEquivQuotSMul P I ∘ₗ f.lTensor (R ⧸ I) := by
  -- Check the commuting square on pure tensors coming from quotient scalars.
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 10.101.3: injectivity transfers across a commuting square of linear
equivalences. -/
lemma injective_of_ladder_linearEquiv_local
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {e₁ : A ≃ₗ[R] A'} {e₂ : B ≃ₗ[R] B'}
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply e₁.symm.injective
  apply hf
  apply e₂.injective
  calc
    e₂ (f (e₁.symm x)) = g x := by
      simpa using (LinearMap.congr_fun h (e₁.symm x)).symm
    _ = g y := hxy
    _ = e₂ (f (e₁.symm y)) := by
      simpa using LinearMap.congr_fun h (e₁.symm y)

/-- Helper for Lemma 10.101.3: the basis of `M / IM` makes the reduced free cover injective. -/
lemma reduced_free_cover_lTensor_comparison
    [DecidableEq A]
    (x : A → M) :
    (Finsupp.linearCombination R x).lTensor (R ⧸ I) ∘ₗ
        (LinearEquiv.restrictScalars R
          (TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) A)).symm.toLinearMap =
      (TensorProduct.quotTensorEquivQuotSMul M I).symm.toLinearMap ∘ₗ
        (Finsupp.linearCombination (R ⧸ I) (mkQIM ∘ x)).restrictScalars R := by
  -- Check the comparison on the `Finsupp.single` generators of the free module over `R ⧸ I`.
  apply Finsupp.lhom_ext
  intro a q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  calc
    (Finsupp.linearCombination R x).lTensor (R ⧸ I)
        ((LinearEquiv.restrictScalars R
          (TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) A)).symm
          (Finsupp.single a (Ideal.Quotient.mk I r)))
      = (Ideal.Quotient.mk I r) ⊗ₜ[R] x a := by
          simp [Finsupp.linearCombination_single]
    _ = (r • (1 : R ⧸ I)) ⊗ₜ[R] x a := by
          congr 1
          change Ideal.Quotient.mk I r = (Ideal.Quotient.mk I r) * 1
          simp
    _ = r • ((1 : R ⧸ I) ⊗ₜ[R] x a) := by
          rw [TensorProduct.smul_tmul']
    _ = (TensorProduct.quotTensorEquivQuotSMul M I).symm
          ((Ideal.Quotient.mk I r) • mkQIM (x a)) := by
          apply (TensorProduct.quotTensorEquivQuotSMul M I).injective
          simp [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
          change (Ideal.Quotient.mk I r) • mkQIM (x a) =
            (Ideal.Quotient.mk I r) • mkQIM (x a)
          rfl
    _ = (TensorProduct.quotTensorEquivQuotSMul M I).symm
          ((Finsupp.linearCombination (R ⧸ I) (mkQIM ∘ x)).restrictScalars R
            (Finsupp.single a (Ideal.Quotient.mk I r))) := by
          simp [Finsupp.linearCombination_single]

/-- Helper for Lemma 10.101.3: the basis of `M / IM` makes the reduced free cover injective. -/
lemma free_cover_mod_ideal_injective_of_quotient_basis
    (x : A → M)
    (hbasis : ∃ bbar : Module.Basis A (R ⧸ I) (M ⧸ IM), ∀ a, bbar a = mkQIM (x a)) :
    Function.Injective ((Finsupp.linearCombination R x).quotientMapByIdeal I) := by
  classical
  rcases hbasis with ⟨bbar, hbbar⟩
  have hmkQx : mkQIM ∘ x = bbar := by
    funext a
    exact (hbbar a).symm
  let e₁ : (A →₀ (R ⧸ I)) ≃ₗ[R] (R ⧸ I) ⊗[R] (A →₀ R) :=
    LinearEquiv.restrictScalars R
      (TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) A).symm
  let e₂ : (M ⧸ IM) ≃ₗ[R] (R ⧸ I) ⊗[R] M :=
    (TensorProduct.quotTensorEquivQuotSMul M I).symm
  have hCompare :
      (Finsupp.linearCombination R x).lTensor (R ⧸ I) ∘ₗ e₁.toLinearMap =
        e₂.toLinearMap ∘ₗ (Finsupp.linearCombination (R ⧸ I) bbar).restrictScalars R := by
    -- Rewrite the quotient family `mkQIM ∘ x` as the given basis `bbar`.
    simpa [e₁, e₂, hmkQx] using
      reduced_free_cover_lTensor_comparison (R := R) (I := I) (A := A) (M := M) x
  have hBasisInj :
      Function.Injective ((Finsupp.linearCombination (R ⧸ I) bbar).restrictScalars R) := by
    -- A basis identifies the reduced free cover with its coordinate isomorphism.
    intro c d hcd
    have hrepr := congrArg bbar.repr hcd
    simpa using hrepr
  have hTensorInj : Function.Injective ((Finsupp.linearCombination R x).lTensor (R ⧸ I)) :=
    injective_of_ladder_linearEquiv_local (R := R) hCompare hBasisInj
  -- Transfer the tensor-side injectivity back through the quotient-tensor comparison.
  exact injective_of_ladder_linearEquiv_local (R := R)
    (quotientMapByIdeal_lTensor_naturality (R := R) (I := I) (N := A →₀ R) (P := M)
      (Finsupp.linearCombination R x))
    hTensorInj

/-- Helper for Lemma 10.101.3: if `0 → N → P → M → 0` is exact and `Tor₁^R(R / I, M)` vanishes,
then reduction modulo `I` keeps the left map injective. -/
lemma lTensor_injective_of_exact_of_tor_one_vanishes_local
    {N P : Type (max u v)}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (g : P →ₗ[R] M)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hExact : Function.Exact f g)
    (htor :
      IsZero
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)))) :
    Function.Injective (f.lTensor (R ⧸ I)) := by
  -- Route correction: the intended proof is the six-term Tor/tensor exact sequence for
  -- `0 → N --f→ P --g→ M → 0` with left factor `R ⧸ I`.
  -- TODO: instantiate `ModuleCat.torTensorSixTermSequence_exact` from `Lemma_10_75_2`,
  -- identify the connecting map out of `Tor₁[R](R ⧸ I, M)` as zero via `htor`, and read off the
  -- injectivity of `f.lTensor (R ⧸ I)` from exactness. At the moment the earlier dependency file
  -- `StacksProject_2024/Chap10/Lemma_10_75_2.lean` itself fails to compile when imported, so the
  -- canonical owner theorem is unavailable in this item file.
  sorry

/-- Helper for Lemma 10.101.3: if `0 → N → P → M → 0` is exact and `Tor₁^R(R / I, M)` vanishes,
then reduction modulo `I` keeps the left map injective. -/
lemma quotientMapByIdeal_injective_of_exact_of_tor_one_vanishes_local
    {N P : Type (max u v)}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (g : P →ₗ[R] M)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hExact : Function.Exact f g)
    (htor :
      IsZero
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)))) :
    Function.Injective (f.quotientMapByIdeal I) := by
  have hTensorInj : Function.Injective (f.lTensor (R ⧸ I)) :=
    lTensor_injective_of_exact_of_tor_one_vanishes_local
      (R := R) (I := I) (M := M) f g hf hg hExact htor
  -- The quotient-tensor equivalence transports tensor injectivity to reduction modulo `I`.
  exact injective_of_ladder_linearEquiv_local (R := R)
    (quotientMapByIdeal_lTensor_naturality (R := R) (I := I) f) hTensorInj

-- Proof sketch: use Nakayama's lemma to show that the family `x` generates `M`. A relation
-- `∑ a, f a • x a = 0` reduces modulo `I` to show each coefficient lies in `I`, while the
-- vanishing of `Tor₁^R(R / I, M)` identifies the first obstruction group controlling relations.
-- Iterating the same argument modulo `I ^ n` forces the coefficients into every power of `I`; the
-- nilpotence of `I` then implies all coefficients vanish, so the family is a basis.
/-- Lemma 10.101.3: if `I` is a nilpotent ideal of `R`, the images of a family `x : A → M` form an
`R ⧸ I`-basis of `M / IM`, and `Tor₁^R(R / I, M)` vanishes, then `x` is an `R`-basis of `M`. -/
theorem exists_basis_of_quotient_basis_of_nilpotent_ideal_of_tor_one_vanishes
    (x : A → M)
    (hI : IsNilpotent I)
    (hbasis : ∃ bbar : Module.Basis A (R ⧸ I) (M ⧸ IM), ∀ a, bbar a = mkQIM (x a))
    (htor :
      IsZero
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)))) :
    ∃ b : Module.Basis A R M, ∀ a, b a = x a := by
  classical
  let π : (A →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
  let K : Submodule R (A →₀ R) := LinearMap.ker π
  have hspan : Submodule.span R (Set.range x) = ⊤ :=
    span_eq_top_of_family_of_quotient_basis (R := R) (I := I) (A := A) (M := M) x hI hbasis
  have hπ_surj : Function.Surjective π := by
    -- Surjectivity is the generation statement coming from Nakayama.
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hspan
  have hExact : Function.Exact K.subtype π := by
    -- The kernel inclusion and the free cover form the presentation exact sequence of `M`.
    exact LinearMap.exact_subtype_ker_map π
  have hπ_inj : Function.Injective π := by
    have hQuotExact :
        Function.Exact (K.subtype.quotientMapByIdeal I) (π.quotientMapByIdeal I) :=
      quotientMapByIdeal_exact (R := R) (I := I) K.subtype π hExact hπ_surj
    have hQuotSubtypeInj : Function.Injective (K.subtype.quotientMapByIdeal I) :=
      quotientMapByIdeal_injective_of_exact_of_tor_one_vanishes_local
        (R := R) (I := I) (M := M) K.subtype π K.injective_subtype hπ_surj hExact htor
    have hQuotInj : Function.Injective (π.quotientMapByIdeal I) :=
      free_cover_mod_ideal_injective_of_quotient_basis (R := R) (I := I) (A := A) (M := M) x hbasis
    have hRangeBot : LinearMap.range (K.subtype.quotientMapByIdeal I) = ⊥ := by
      -- Exactness modulo `I` and injectivity of the reduced free cover force the reduced kernel to
      -- vanish.
      rw [← LinearMap.exact_iff.mp hQuotExact, LinearMap.ker_eq_bot]
      exact hQuotInj
    have hQuotSubtypeZero : K.subtype.quotientMapByIdeal I = 0 :=
      LinearMap.range_eq_bot.mp hRangeBot
    have hKerQuotSubsingleton :
        Subsingleton (K ⧸ (I • (⊤ : Submodule R K))) := by
      refine ⟨fun x y ↦ hQuotSubtypeInj ?_⟩
      simp [hQuotSubtypeZero]
    have hIKer : I • (⊤ : Submodule R K) = ⊤ := by
      -- A quotient with only one point says exactly that `K = IK`.
      rwa [Submodule.Quotient.subsingleton_iff] at hKerQuotSubsingleton
    have hKSubsingleton : Subsingleton K :=
      subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent I hIKer hI
    -- Nilpotence now kills the whole kernel, so the free cover is injective.
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.subsingleton_iff_eq_bot.mp hKSubsingleton
  -- Route correction: the final basis is the one induced by the now-bijective free cover.
  refine ⟨Module.Basis.ofRepr (LinearEquiv.ofBijective π ⟨hπ_inj, hπ_surj⟩).symm, ?_⟩
  intro a
  simp [π]

end

/-! ### Lemma_10_101_4 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {I : Ideal R}

section

variable [Algebra R R']

local notation "I₂" => Ideal.comap (algebraMap R R') (Ideal.map (algebraMap R R') (I ^ 2))

/- Domain triage:
- primary domain: commutative algebra of flatness under base change and quotienting by ideals;
- sampled owner declarations of the same kind:
  `Module.Flat.iff_flat_tensorProduct`,
  `flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes`,
  `torOne_baseChangeMap_surjective_of_flat_baseChange`,
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`;
- best owner abstraction: the canonical owner predicates `Module.Flat` and the Chapter 10
  `Tor₁` base-change / quotient-flatness API;
- primitive data: the `R`-algebra `R'`, the ideal `I`, and the `R`-module `M`;
- derived API: the specific contracted-square ideal `I₂` and the resulting quotient-flatness
  statement.

Layering:
- this item stays `source-facing`: it is the textbook special-case quotient statement for the
  contracted extended square ideal;
- the proof should use the `core/canonical` owners above rather than introducing a parallel local
  flatness/Tor wrapper;
- no extra `bridge/view` owner is needed beyond the local notation for the contracted ideal.
-/

-- Proof sketch: replace `R`, `M`, and `R'` by the corresponding quotients so that `I₂ = 0` and
-- `I ^ 2 = 0`; then apply Lemma `10.99.8`, reducing flatness over `R / I₂` to vanishing of
-- `Tor₁^R(R / I, M)`, and prove that vanishing by comparing the kernel of `I ⊗[R] M → M` with its
-- image after base change to `R'`.
/-- Helper for Lemma 10.101.4: the contracted square ideal contains `I ^ 2`. -/
lemma contracted_square_le :
    I ^ 2 ≤ I₂ := by
  -- Every element of `I ^ 2` maps into the extended ideal generated by the image of `I ^ 2`.
  intro x hx
  change algebraMap R R' x ∈ Ideal.map (algebraMap R R') (I ^ 2)
  exact Ideal.mem_map_of_mem _ hx

/-- Helper for Lemma 10.101.4: the source-faithful square-zero reduction ideal is
`I ⊓ I₂`, which is contained in `I` and still contains `I ^ 2`. -/
lemma source_reduction_sq_le :
    I ^ 2 ≤ I ⊓ I₂ := by
  -- The source proof kills `I ^ 2` while keeping the reduced ideal inside `I`.
  exact le_inf (Ideal.pow_le_self two_ne_zero) (contracted_square_le (R := R) (R' := R') (I := I))

/-- Helper for Lemma 10.101.4: after reducing by `I ⊓ I₂`, quotienting the source ring by the
image of `I` recovers the original quotient `R ⧸ I`. -/
noncomputable def source_reduction_mod_ideal_ring_equiv :
    let J₀ : Ideal R := I ⊓ I₂
    (R ⧸ J₀) ⧸ Ideal.map (Ideal.Quotient.mk J₀) I ≃+* R ⧸ I := by
  -- The source reduction is a third-isomorphism step with `J₀ ≤ I`.
  exact DoubleQuot.quotQuotEquivQuotOfLE (inf_le_left : I ⊓ I₂ ≤ I)

/-- Helper for Lemma 10.101.4: after reducing by `I ⊓ I₂`, quotienting the source module by the
image of `IM` recovers the original quotient `M / IM`. -/
noncomputable def source_reduction_mod_ideal_module_equiv :
    let J₀ : Ideal R := I ⊓ I₂
    let J₀M : Submodule R M := J₀ • (⊤ : Submodule R M)
    let IM : Submodule R M := I • (⊤ : Submodule R M)
    ((M ⧸ J₀M) ⧸ IM.map (Submodule.mkQ J₀M)) ≃ₗ[R] M ⧸ IM := by
  let J₀ : Ideal R := I ⊓ I₂
  let J₀M : Submodule R M := J₀ • (⊤ : Submodule R M)
  let IM : Submodule R M := I • (⊤ : Submodule R M)
  have hJ₀M_le_IM : J₀M ≤ IM := by
    -- The reduced denominator stays inside `IM` because `J₀ ≤ I`.
    dsimp [J₀M, IM, J₀]
    simpa using
      (Submodule.smul_mono (inf_le_left : I ⊓ I₂ ≤ I)
        (show (⊤ : Submodule R M) ≤ ⊤ from le_rfl))
  -- The module version of the third-isomorphism theorem gives the iterated quotient comparison.
  exact Submodule.quotientQuotientEquivQuotient J₀M IM hJ₀M_le_IM

/-- Helper for Lemma 10.101.4: after reducing by `I ⊓ I₂`, the image of `IM` in
`M / (I ⊓ I₂)M` is exactly the submodule generated by the image ideal `K`. -/
lemma source_reduction_mod_ideal_smul_top_map_eq :
    let J₀ : Ideal R := I ⊓ I₂
    let J₀M : Submodule R M := J₀ • (⊤ : Submodule R M)
    let K : Ideal (R ⧸ J₀) := Ideal.map (Ideal.Quotient.mk J₀) I
    (I • (⊤ : Submodule R M)).map (Submodule.mkQ J₀M) =
      ((K • (⊤ : Submodule (R ⧸ J₀) (M ⧸ J₀M))).restrictScalars R) := by
  let J₀ : Ideal R := I ⊓ I₂
  let J₀M : Submodule R M := J₀ • (⊤ : Submodule R M)
  let K : Ideal (R ⧸ J₀) := Ideal.map (Ideal.Quotient.mk J₀) I
  -- First rewrite the image of `IM` through the quotient map, then convert it to the quotient
  -- ring action using `Ideal.smul_restrictScalars`.
  calc
    (I • (⊤ : Submodule R M)).map (Submodule.mkQ J₀M)
        = I • (⊤ : Submodule R (M ⧸ J₀M)) := by
            simp [J₀M, Submodule.map_smul'', Submodule.range_mkQ]
    _ = ((Ideal.map (algebraMap R (R ⧸ J₀)) I) •
          (⊤ : Submodule (R ⧸ J₀) (M ⧸ J₀M))).restrictScalars R := by
            symm
            simpa using
              (Ideal.smul_restrictScalars
                (R := R) (S := R ⧸ J₀) (M := M ⧸ J₀M) I
                (⊤ : Submodule (R ⧸ J₀) (M ⧸ J₀M)))
    _ = ((K • (⊤ : Submodule (R ⧸ J₀) (M ⧸ J₀M))).restrictScalars R) := by
          rw [Ideal.Quotient.algebraMap_eq]

/-- Helper for Lemma 10.101.4: the iterated quotient comparison can be stated using the canonical
submodule `K • ⊤` on the reduced module. -/
noncomputable def source_reduction_mod_ideal_module_equiv_canonical :
    let J₀ : Ideal R := I ⊓ I₂
    let J₀M : Submodule R M := J₀ • (⊤ : Submodule R M)
    let K : Ideal (R ⧸ J₀) := Ideal.map (Ideal.Quotient.mk J₀) I
    ((M ⧸ J₀M) ⧸ ((K • (⊤ : Submodule (R ⧸ J₀) (M ⧸ J₀M))).restrictScalars R)) ≃ₗ[R]
      M ⧸ (I • (⊤ : Submodule R M)) := by
  let J₀ : Ideal R := I ⊓ I₂
  let J₀M : Submodule R M := J₀ • (⊤ : Submodule R M)
  let IM : Submodule R M := I • (⊤ : Submodule R M)
  let K : Ideal (R ⧸ J₀) := Ideal.map (Ideal.Quotient.mk J₀) I
  let eDenom :
      ((M ⧸ J₀M) ⧸ IM.map (Submodule.mkQ J₀M)) ≃ₗ[R]
        ((M ⧸ J₀M) ⧸ ((K • (⊤ : Submodule (R ⧸ J₀) (M ⧸ J₀M))).restrictScalars R)) :=
    -- Replace the ad hoc denominator `IM.map` by the source-faithful quotient-side ideal action.
    Submodule.quotEquivOfEq
      (IM.map (Submodule.mkQ J₀M))
      ((K • (⊤ : Submodule (R ⧸ J₀) (M ⧸ J₀M))).restrictScalars R)
      (source_reduction_mod_ideal_smul_top_map_eq (R := R) (R' := R') (M := M) (I := I))
  -- The third-isomorphism equivalence now has the canonical quotient-side denominator.
  exact eDenom.symm.trans (source_reduction_mod_ideal_module_equiv (R := R) (R' := R') (M := M)
    (I := I))

/-- Helper for Lemma 10.101.4: after reducing by `I ⊓ I₂`, quotienting the source ring by the
image of `I₂` recovers the target quotient `R ⧸ I₂`. -/
noncomputable def source_reduction_target_ring_equiv :
    let J₀ : Ideal R := I ⊓ I₂
    (R ⧸ J₀) ⧸ Ideal.map (Ideal.Quotient.mk J₀) I₂ ≃+* R ⧸ I₂ := by
  -- The target quotient is the same third-isomorphism step, now with `J₀ ≤ I₂`.
  exact DoubleQuot.quotQuotEquivQuotOfLE (inf_le_right : I ⊓ I₂ ≤ I₂)

/-- Helper for Lemma 10.101.4: after reducing by `I ⊓ I₂`, quotienting the source module by the
image of `I₂M` recovers the target quotient `M / I₂M`. -/
noncomputable def source_reduction_target_module_equiv :
    let J₀ : Ideal R := I ⊓ I₂
    let J₀M : Submodule R M := J₀ • (⊤ : Submodule R M)
    let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
    ((M ⧸ J₀M) ⧸ I₂M.map (Submodule.mkQ J₀M)) ≃ₗ[R] M ⧸ I₂M := by
  let J₀ : Ideal R := I ⊓ I₂
  let J₀M : Submodule R M := J₀ • (⊤ : Submodule R M)
  let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
  have hJ₀M_le_I₂M : J₀M ≤ I₂M := by
    -- The same monotonicity identifies the reduced target quotient.
    dsimp [J₀M, I₂M, J₀]
    simpa using
      (Submodule.smul_mono (inf_le_right : I ⊓ I₂ ≤ I₂)
        (show (⊤ : Submodule R M) ≤ ⊤ from le_rfl))
  -- This is again the module third-isomorphism theorem, now for the target quotient.
  exact Submodule.quotientQuotientEquivQuotient J₀M I₂M hJ₀M_le_I₂M

/-- Helper for Lemma 10.101.4: once flatness is known modulo `I ^ 2`, base change along
`R ⧸ I ^ 2 → R ⧸ I₂` gives flatness modulo the contracted square ideal. -/
lemma flat_quotient_contracted_square_of_flat_quotient_sq
    (hflat_sq : Module.Flat (R ⧸ I ^ 2) (M ⧸ (I ^ 2 • ⊤ : Submodule R M))) :
    Module.Flat (R ⧸ I₂) (M ⧸ (I₂ • ⊤ : Submodule R M)) := by
  let A : Type u := R ⧸ I ^ 2
  let S : Type u := R ⧸ I₂
  letI : CommRing A := inferInstance
  letI : CommRing S := inferInstance
  letI : Algebra R A := Ideal.Quotient.algebra _
  letI : Algebra R S := Ideal.Quotient.algebra _
  letI : Algebra A S :=
    (Ideal.Quotient.factorₐ (R₁ := R)
      (contracted_square_le (R := R) (R' := R') (I := I))).toAlgebra
  letI : IsScalarTower R A S := by infer_instance
  -- Base change the flat quotient module from `R / I²` to `R / I₂`.
  have hflat_base :
      Module.Flat S (S ⊗[A] (M ⧸ (I ^ 2 • ⊤ : Submodule R M))) :=
    Module.Flat.baseChange (R := A) (S := S)
      (M := M ⧸ (I ^ 2 • ⊤ : Submodule R M))
  -- Rewrite the quotient model through the standard tensor and cancel-base-change equivalences.
  let e₁ : (M ⧸ (I ^ 2 • ⊤ : Submodule R M)) ≃ₗ[A] A ⊗[R] M :=
    ((TensorProduct.quotTensorEquivQuotSMul M (I ^ 2)).symm).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let e₂ : S ⊗[A] (M ⧸ (I ^ 2 • ⊤ : Submodule R M)) ≃ₗ[S] S ⊗[A] (A ⊗[R] M) :=
    LinearEquiv.baseChange A S
      (M ⧸ (I ^ 2 • ⊤ : Submodule R M)) (A ⊗[R] M) e₁
  let e₃ : S ⊗[A] (A ⊗[R] M) ≃ₗ[S] S ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A S S M
  let e₄ : S ⊗[R] M ≃ₗ[S] M ⧸ (I₂ • ⊤ : Submodule R M) :=
    (TensorProduct.quotTensorEquivQuotSMul M I₂).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  letI : Module.Flat S (S ⊗[A] (M ⧸ (I ^ 2 • ⊤ : Submodule R M))) := hflat_base
  exact Module.Flat.of_linearEquiv (e₂.trans (e₃.trans e₄)).symm

/-- Helper for Lemma 10.101.4: quotienting the base-changed module by the image of `I ^ 2`
preserves flatness over the corresponding quotient ring. -/
lemma flat_quotient_image_sq_of_flat_baseChange
    (hflat_baseChange : Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat (R' ⧸ Ideal.map (algebraMap R R') (I ^ 2))
      ((R' ⊗[R] M) ⧸
        ((Ideal.map (algebraMap R R') (I ^ 2)) •
          (⊤ : Submodule R' (R' ⊗[R] M)))) := by
  let A' : Type v := R' ⧸ Ideal.map (algebraMap R R') (I ^ 2)
  letI : CommRing A' := inferInstance
  letI : Algebra R' A' := Ideal.Quotient.algebra _
  -- First rewrite the quotient module into the canonical tensor model over `A'`.
  let e :
      ((R' ⊗[R] M) ⧸
        ((Ideal.map (algebraMap R R') (I ^ 2)) •
          (⊤ : Submodule R' (R' ⊗[R] M)))) ≃ₗ[A']
        (A' ⊗[R'] (R' ⊗[R] M)) :=
    (TensorProduct.quotTensorEquivQuotSMul (R' ⊗[R] M)
      (Ideal.map (algebraMap R R') (I ^ 2))).symm.extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective
  -- Then base change the given flat module along `R' → A'`.
  letI : Module.Flat R' (R' ⊗[R] M) := hflat_baseChange
  have hbase :
      Module.Flat A' (A' ⊗[R'] (R' ⊗[R] M)) :=
    Module.Flat.baseChange (R := R') (S := A') (M := R' ⊗[R] M)
  letI : Module.Flat A' (A' ⊗[R'] (R' ⊗[R] M)) := hbase
  exact Module.Flat.of_linearEquiv e

/-- Helper for Lemma 10.101.4: base changing `M / IM` along `R ⧸ I → R ⧸ (I ⊔ I₂)` gives the
quotient by `(I ⊔ I₂)M`. -/
lemma flat_mod_sup_contracted_square_of_flat_mod_ideal
    (hflat_mod_ideal : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Flat (R ⧸ (I ⊔ I₂)) (M ⧸ ((I ⊔ I₂) • ⊤ : Submodule R M)) := by
  let A : Type u := R ⧸ I
  let B : Type u := R ⧸ (I ⊔ I₂)
  letI : CommRing A := inferInstance
  letI : CommRing B := inferInstance
  letI : Algebra R A := Ideal.Quotient.algebra _
  letI : Algebra R B := Ideal.Quotient.algebra _
  letI : Algebra A B :=
    (Ideal.Quotient.factorₐ (R₁ := R) (show I ≤ I ⊔ I₂ from le_sup_left)).toAlgebra
  letI : IsScalarTower R A B := by infer_instance
  -- The first source hypothesis is transported by the canonical quotient map.
  have hflat_base :
      Module.Flat B (B ⊗[A] (M ⧸ (I • ⊤ : Submodule R M))) :=
    Module.Flat.baseChange (R := A) (S := B) (M := M ⧸ (I • ⊤ : Submodule R M))
  let e₁ : (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[A] A ⊗[R] M :=
    ((TensorProduct.quotTensorEquivQuotSMul M I).symm).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let e₂ : B ⊗[A] (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[B] B ⊗[A] (A ⊗[R] M) :=
    LinearEquiv.baseChange A B
      (M ⧸ (I • ⊤ : Submodule R M)) (A ⊗[R] M) e₁
  let e₃ : B ⊗[A] (A ⊗[R] M) ≃ₗ[B] B ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M
  let e₄ : B ⊗[R] M ≃ₗ[B] M ⧸ ((I ⊔ I₂) • ⊤ : Submodule R M) :=
    (TensorProduct.quotTensorEquivQuotSMul M (I ⊔ I₂)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  letI : Module.Flat B (B ⊗[A] (M ⧸ (I • ⊤ : Submodule R M))) := hflat_base
  exact Module.Flat.of_linearEquiv (e₂.trans (e₃.trans e₄)).symm

/-- Helper for Lemma 10.101.4: quotienting `R ⧸ I₂` by the image of `I` is the same as quotienting
`R` by `I ⊔ I₂`. -/
noncomputable def contracted_square_mod_ideal_ring_equiv :
    let S : Type u := R ⧸ I₂
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk I₂) I
    (S ⧸ J) ≃+* R ⧸ (I ⊔ I₂) :=
  (DoubleQuot.quotQuotEquivQuotSup I₂ I).trans
    (Ideal.quotientEquivAlgOfEq R (sup_comm I₂ I)).toRingEquiv

/-- Helper for Lemma 10.101.4: in `M / I₂M`, the image of `IM` is the submodule generated by the
image ideal `J`. -/
lemma contracted_square_mod_ideal_smul_top_map_eq :
    let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
    let J : Ideal (R ⧸ I₂) := Ideal.map (Ideal.Quotient.mk I₂) I
    (I • (⊤ : Submodule R M)).map (Submodule.mkQ I₂M) =
      ((J • (⊤ : Submodule (R ⧸ I₂) (M ⧸ I₂M))).restrictScalars R) := by
  let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
  let J : Ideal (R ⧸ I₂) := Ideal.map (Ideal.Quotient.mk I₂) I
  -- Rewrite the image denominator through the quotient map, then replace the source ideal by its
  -- image in the quotient ring.
  calc
    (I • (⊤ : Submodule R M)).map (Submodule.mkQ I₂M)
        = I • (⊤ : Submodule R (M ⧸ I₂M)) := by
            simp [I₂M, Submodule.map_smul'', Submodule.range_mkQ]
    _ = ((Ideal.map (algebraMap R (R ⧸ I₂)) I) •
          (⊤ : Submodule (R ⧸ I₂) (M ⧸ I₂M))).restrictScalars R := by
            symm
            simpa using
              (Ideal.smul_restrictScalars
                (R := R) (S := R ⧸ I₂) (M := M ⧸ I₂M) I
                (⊤ : Submodule (R ⧸ I₂) (M ⧸ I₂M)))
    _ = ((J • (⊤ : Submodule (R ⧸ I₂) (M ⧸ I₂M))).restrictScalars R) := by
          rw [Ideal.Quotient.algebraMap_eq]

/-- Helper for Lemma 10.101.4: the iterated quotient denominator over `I₂M` is the submodule
generated by `I ⊔ I₂`. -/
lemma contracted_square_mod_ideal_sup_smul_eq :
    let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
    let IM : Submodule R M := I • (⊤ : Submodule R M)
    I₂M ⊔ IM = (I ⊔ I₂) • (⊤ : Submodule R M) := by
  -- The third-isomorphism target is the quotient by the sum of the two source denominators.
  let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
  let IM : Submodule R M := I • (⊤ : Submodule R M)
  simpa [I₂M, IM, sup_comm] using (Submodule.sup_smul I₂ I (⊤ : Submodule R M)).symm

/-- Helper for Lemma 10.101.4: after quotienting by `I₂M`, quotienting once more by the image of
`IM` identifies with quotienting `M` by `(I ⊔ I₂)M`. -/
noncomputable def contracted_square_mod_ideal_module_equiv :
    let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
    let J : Ideal (R ⧸ I₂) := Ideal.map (Ideal.Quotient.mk I₂) I
    ((M ⧸ I₂M) ⧸ ((J • (⊤ : Submodule (R ⧸ I₂) (M ⧸ I₂M))).restrictScalars R)) ≃ₗ[R]
      M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M)) :=
  let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
  let IM : Submodule R M := I • (⊤ : Submodule R M)
  let J : Ideal (R ⧸ I₂) := Ideal.map (Ideal.Quotient.mk I₂) I
  let eDenom :
      ((M ⧸ I₂M) ⧸ IM.map (Submodule.mkQ I₂M)) ≃ₗ[R]
        ((M ⧸ I₂M) ⧸ ((J • (⊤ : Submodule (R ⧸ I₂) (M ⧸ I₂M))).restrictScalars R)) :=
    Submodule.quotEquivOfEq
      (IM.map (Submodule.mkQ I₂M))
      ((J • (⊤ : Submodule (R ⧸ I₂) (M ⧸ I₂M))).restrictScalars R)
      (contracted_square_mod_ideal_smul_top_map_eq (R := R) (R' := R') (M := M) (I := I))
  let eSup :
      ((M ⧸ I₂M) ⧸ IM.map (Submodule.mkQ I₂M)) ≃ₗ[R] M ⧸ (I₂M ⊔ IM) :=
    Submodule.quotientQuotientEquivQuotientSup I₂M IM
  let eTarget :
      (M ⧸ (I₂M ⊔ IM)) ≃ₗ[R] (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M))) :=
    Submodule.quotEquivOfEq _ _
      (contracted_square_mod_ideal_sup_smul_eq (R := R) (R' := R') (M := M) (I := I))
  eDenom.symm.trans (eSup.trans eTarget)

/-- Helper for Lemma 10.101.4: the iterated quotient comparison is linear over the reduced owner
ring `(R ⧸ I₂) ⧸ J`, not just over `R`. -/
noncomputable def contracted_square_mod_ideal_module_equiv_over_owner :
    let S : Type u := R ⧸ I₂
    let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
    let N : Type w := M ⧸ I₂M
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk I₂) I
    let T : Type u := S ⧸ J
    letI : Algebra T (R ⧸ (I ⊔ I₂)) :=
      (contracted_square_mod_ideal_ring_equiv (R := R) (R' := R') (I := I)).toRingHom.toAlgebra
    letI : Module T (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M))) :=
      Module.compHom (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M)))
        (algebraMap T (R ⧸ (I ⊔ I₂)))
    (N ⧸ (J • (⊤ : Submodule S N))) ≃ₗ[T]
      M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M)) := by
  let S : Type u := R ⧸ I₂
  let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
  let N : Type w := M ⧸ I₂M
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk I₂) I
  let T : Type u := S ⧸ J
  letI : Algebra R S := Ideal.Quotient.algebra _
  letI : Algebra S T := Ideal.Quotient.algebra _
  letI : Algebra R T := by infer_instance
  letI : Algebra T (R ⧸ (I ⊔ I₂)) :=
    (contracted_square_mod_ideal_ring_equiv (R := R) (R' := R') (I := I)).toRingHom.toAlgebra
  letI : Module T (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M))) :=
    Module.compHom (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M)))
      (algebraMap T (R ⧸ (I ⊔ I₂)))
  letI : IsScalarTower R T (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M))) :=
    IsScalarTower.of_compHom R T (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M)))
  let eRestrict :
      (N ⧸ ((J • (⊤ : Submodule S N)).restrictScalars R)) ≃ₗ[R] N ⧸ (J • (⊤ : Submodule S N)) :=
    -- First identify the quotient by the `S`-submodule with the same quotient viewed over `R`.
    Submodule.Quotient.restrictScalarsEquiv R (J • (⊤ : Submodule S N))
  let eR :
      (N ⧸ (J • (⊤ : Submodule S N))) ≃ₗ[R]
        M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M)) :=
    -- Then reuse the existing third-isomorphism comparison over the ground ring `R`.
    eRestrict.symm.trans
      (contracted_square_mod_ideal_module_equiv (R := R) (R' := R') (M := M) (I := I))
  have hsurj : Function.Surjective (algebraMap R T) := by
    -- The reduced owner ring is still a quotient of `R`, so scalar extension from `R` is
    -- surjective and upgrades the comparison to `T`-linearity.
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, rfl⟩
  exact eR.extendScalarsOfSurjective hsurj

/-- Helper for Lemma 10.101.4: the quotient-flatness over `R ⧸ (I ⊔ I₂)` transports to the exact
reduced owner `(R ⧸ I₂) ⧸ J`. -/
lemma flat_contracted_square_owner_of_flat_sup_owner
    (hflat_sup : Module.Flat (R ⧸ (I ⊔ I₂))
      (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M)))) :
    let S : Type u := R ⧸ I₂
    let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
    let N : Type w := M ⧸ I₂M
    let J : Ideal S := Ideal.map (Ideal.Quotient.mk I₂) I
    Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))) := by
  let S : Type u := R ⧸ I₂
  let I₂M : Submodule R M := I₂ • (⊤ : Submodule R M)
  let N : Type w := M ⧸ I₂M
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk I₂) I
  let T : Type u := S ⧸ J
  let B : Type u := R ⧸ (I ⊔ I₂)
  letI : CommRing S := inferInstance
  letI : CommRing T := inferInstance
  letI : CommRing B := inferInstance
  letI : Algebra T B :=
    (contracted_square_mod_ideal_ring_equiv (R := R) (R' := R') (I := I)).toRingHom.toAlgebra
  letI : Module T (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M))) :=
    Module.compHom (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M))) (algebraMap T B)
  letI : IsScalarTower T B (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M))) :=
    IsScalarTower.of_compHom T B (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M)))
  have hflatTB : Module.Flat T B := by
    -- The owner-ring comparison is a bijective ring map, hence flat.
    rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.of_bijective (f := algebraMap T B) <| by
      simpa [RingHom.algebraMap_toAlgebra] using
        (contracted_square_mod_ideal_ring_equiv (R := R) (R' := R') (I := I)).bijective
  have hflatTarget : Module.Flat T (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M))) := by
    -- Compose flatness along the ring equivalence with the given owner flatness.
    letI : Module.Flat T B := hflatTB
    letI : Module.Flat B (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M))) := hflat_sup
    exact Module.Flat.trans T B (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M)))
  letI : Module.Flat T (M ⧸ ((I ⊔ I₂) • (⊤ : Submodule R M))) := hflatTarget
  -- Finally rewrite the quotient module to the contracted-square owner.
  exact Module.Flat.of_linearEquiv
    (contracted_square_mod_ideal_module_equiv_over_owner
      (R := R) (R' := R') (M := M) (I := I))

/-- Helper for Lemma 10.101.4: quotienting by the contracted square ideal induces the comparison
map to the base-changed square quotient. -/
noncomputable def contracted_square_comparison :
    R ⧸ I₂ →+* R' ⧸ Ideal.map (algebraMap R R') (I ^ 2) :=
  Ideal.quotientMap (Ideal.map (algebraMap R R') (I ^ 2)) (algebraMap R R')
    (by
      -- The contracted-square ideal is exactly the comap of the target quotient ideal.
      change I₂ ≤ Ideal.comap (algebraMap R R') (Ideal.map (algebraMap R R') (I ^ 2))
      exact le_rfl)

/-- Helper for Lemma 10.101.4: the comparison map from the contracted-square quotient is
injective. -/
lemma contracted_square_comparison_injective :
    Function.Injective (contracted_square_comparison (R := R) (R' := R') (I := I)) := by
  -- Compute the kernel directly: an element maps to zero exactly when its representative lies in
  -- the contracted square ideal.
  rw [RingHom.injective_iff_ker_eq_bot]
  ext x
  constructor
  · intro hx
    rcases Ideal.Quotient.mk_surjective x with ⟨a, rfl⟩
    change contracted_square_comparison (Ideal.Quotient.mk I₂ a) = 0 at hx
    change Ideal.Quotient.mk (Ideal.map (algebraMap R R') (I ^ 2)) (algebraMap R R' a) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 <| by
      change a ∈ I₂
      exact hx
  · intro hx
    have hx0 : x = 0 := by
      simpa using hx
    simp [hx0]

/-- Helper for Lemma 10.101.4: after passing to `R ⧸ I₂`, the base change to
`R' ⧸ \varphi(I^2)R'` is the quotient of `R' ⊗[R] M` by the image of `I^2`. -/
noncomputable def contracted_square_baseChange_linear_equiv :
    let S : Type u := R ⧸ I₂
    let N : Type w := M ⧸ (I₂ • ⊤ : Submodule R M)
    let S' : Type v := R' ⧸ Ideal.map (algebraMap R R') (I ^ 2)
    letI : Algebra S S' :=
      (contracted_square_comparison (R := R) (R' := R') (I := I)).toAlgebra
    S' ⊗[S] N ≃ₗ[S']
      ((R' ⊗[R] M) ⧸
        ((Ideal.map (algebraMap R R') (I ^ 2)) •
          (⊤ : Submodule R' (R' ⊗[R] M)))) :=
  let S : Type u := R ⧸ I₂
  let N : Type w := M ⧸ (I₂ • ⊤ : Submodule R M)
  let S' : Type v := R' ⧸ Ideal.map (algebraMap R R') (I ^ 2)
  letI : Algebra R S := Ideal.Quotient.algebra _
  letI : Algebra R S' := Ideal.Quotient.algebra _
  letI : Algebra R' S' := Ideal.Quotient.algebra _
  letI : Algebra S S' :=
    (contracted_square_comparison (R := R) (R' := R') (I := I)).toAlgebra
  letI : IsScalarTower R R' S' := by infer_instance
  letI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' <| by
    ext x
    change contracted_square_comparison (R := R) (R' := R') (I := I)
        (Ideal.Quotient.mk I₂ x) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R R') (I ^ 2)) (algebraMap R R' x)
    rfl
  let e₁ : N ≃ₗ[S] S ⊗[R] M :=
    ((TensorProduct.quotTensorEquivQuotSMul M I₂).symm).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let e₂ : S' ⊗[S] N ≃ₗ[S'] S' ⊗[S] (S ⊗[R] M) :=
    LinearEquiv.baseChange S S' N (S ⊗[R] M) e₁
  let e₃ : S' ⊗[S] (S ⊗[R] M) ≃ₗ[S'] S' ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M
  let e₄ : S' ⊗[R] M ≃ₗ[S'] S' ⊗[R'] (R' ⊗[R] M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' S' S' M).symm
  let e₅ :
      S' ⊗[R'] (R' ⊗[R] M) ≃ₗ[S']
        ((R' ⊗[R] M) ⧸
          ((Ideal.map (algebraMap R R') (I ^ 2)) •
            (⊤ : Submodule R' (R' ⊗[R] M)))) :=
    (TensorProduct.quotTensorEquivQuotSMul (R' ⊗[R] M)
      (Ideal.map (algebraMap R R') (I ^ 2))).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective
  e₂.trans (e₃.trans (e₄.trans e₅))

/-- Helper for Lemma 10.101.4: after passing to `R ⧸ I₂`, the image of `I` is square-zero. -/
lemma image_ideal_square_zero_in_contracted_square_quotient :
    (Ideal.map (Ideal.Quotient.mk I₂) I) ^ 2 = ⊥ := by
  -- Map the square `I ^ 2` into the quotient and use `I ^ 2 ≤ I₂`.
  apply le_antisymm
  · calc
      (Ideal.map (Ideal.Quotient.mk I₂) I) ^ 2 =
          Ideal.map (Ideal.Quotient.mk I₂) (I ^ 2) := by
            rw [← Ideal.map_pow]
      _ ≤ Ideal.map (Ideal.Quotient.mk I₂) I₂ :=
        Ideal.map_mono (contracted_square_le (R := R) (R' := R') (I := I))
      _ = ⊥ := Ideal.map_quotient_self I₂
  · exact bot_le

/-- Helper for Lemma 10.101.4: a square-zero ideal is naturally a module over the quotient by
itself because it is annihilated by its own elements. -/
lemma square_zero_ideal_is_torsion
    {S : Type u} [CommRing S] {J : Ideal S} (hJ_sq : J ^ 2 = ⊥) :
    Module.IsTorsionBySet S J (↑J : Set S) := by
  -- The square-zero relation says exactly that every element of `J` annihilates the ideal `J`.
  rw [Module.isTorsionBySet_iff_subset_annihilator]
  intro x hx
  change x ∈ Module.annihilator S J
  rw [Module.mem_annihilator]
  intro y
  apply Subtype.ext
  change x * (y : S) = 0
  have hxy : x * (y : S) ∈ J ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx y.property
  simpa using
    (show x * (y : S) ∈ (⊥ : Ideal S) by simpa [hJ_sq] using hxy)

/-- Helper for Lemma 10.101.4: once the module universe matches the ring universe, kernel
vanishing for `I ⊗[R] N → N` gives the `Tor₁^R(N, R / I)` vanishing supplied by Remark `10.75.9`.
-/
lemma tor_one_module_quotient_vanishes_of_ker_eq_bot
    {N : Type u} [AddCommGroup N] [Module R N]
    (hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul R N).comp I.subtype)) = ⊥) :
    IsZero ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R (R ⧸ I)))) := by
  let μ : I ⊗[R] N →ₗ[R] N :=
    TensorProduct.lift ((LinearMap.lsmul R N).comp I.subtype)
  have hker_subsingleton : Subsingleton (LinearMap.ker μ) := by
    -- The assumed kernel equality identifies the kernel module with the zero submodule.
    exact (Submodule.subsingleton_iff_eq_bot).2 (by simpa [μ] using hker)
  let e :
      (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R (R ⧸ I))) ≃ₗ[R]
        LinearMap.ker μ :=
    tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := R) (M := N) I
  have hsub :
      Subsingleton (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj
        (ModuleCat.of R (R ⧸ I))) :=
    by
      refine ⟨fun x y ↦ ?_⟩
      apply e.injective
      exact Subsingleton.elim _ _
  -- Remark `10.75.9` identifies this owner with the zero kernel, so the owner itself is zero.
  exact (ModuleCat.isZero_iff_subsingleton).2 hsub

/-- Helper for Lemma 10.101.4: `tor_flip_iso` identifies the public quotient-first owner
`Tor₁^S(S / J, N)` with the fixed-coefficient source owner obtained by resolving `N` and tensoring
on the right with `S / J`. -/
noncomputable def tor_one_quotient_source_owner_iso
    {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N]
    (J : Ideal S) :
    (((Tor (ModuleCat S) 1).obj (ModuleCat.of S (S ⧸ J))).obj (ModuleCat.of S N)) ≅
      (((Functor.flip (Tor' (ModuleCat S) 1)).obj (ModuleCat.of S (S ⧸ J))).obj
        (ModuleCat.of S N)) :=
  (((tor_flip_iso (ModuleCat S) 1).app (ModuleCat.of S (S ⧸ J))).app (ModuleCat.of S N))

/-- Helper for Lemma 10.101.4: the fixed-left-factor public owner `Tor₁^S(N, -)` is naturally
isomorphic to the fixed-left-factor source owner `Tor'₁^S(N, -)`. -/
noncomputable def tor_one_module_source_owner_iso
    {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N] :
    ((Tor (ModuleCat S) 1).obj (ModuleCat.of S N)) ≅
      ((Tor' (ModuleCat S) 1).obj (ModuleCat.of S N)) := sorry

/-- Helper for Lemma 10.101.4: `tor_flip_iso` identifies the module-first public owner
`Tor₁^S(N, S / J)` with the flipped source owner `Tor'₁^S(S / J, N)`. -/
noncomputable def tor_one_module_quotient_flip_owner_iso
    {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N]
    (J : Ideal S) :
    (((Tor (ModuleCat S) 1).obj (ModuleCat.of S N)).obj (ModuleCat.of S (S ⧸ J))) ≅
      (((Functor.flip (Tor' (ModuleCat S) 1)).obj (ModuleCat.of S N)).obj
        (ModuleCat.of S (S ⧸ J))) :=
  (((tor_flip_iso (ModuleCat S) 1).app (ModuleCat.of S N)).app (ModuleCat.of S (S ⧸ J)))

/-- Helper for Lemma 10.101.4: quotienting by the image ideal in a `ULift` ring recovers the
original quotient ring. -/
lemma ulift_quotient_ring_equiv_aux
    {A : Type u} [CommRing A] (K : Ideal A) :
    K =
      (K.map (algebraMap A (ULift.{w} A))).map
        ((ULift.algEquiv (R := A) (A := A) : ULift.{w} A ≃ₐ[A] A) : ULift.{w} A →+* A) := by
  let eu : ULift.{w} A ≃ₐ[A] A := ULift.algEquiv (R := A) (A := A)
  -- The `ULift` algebra equivalence is inverse to the canonical lift `A → ULift A`.
  calc
    K = K.map (RingHom.id A) := by simp
    _ = K.map ((eu : ULift.{w} A →+* A).comp (algebraMap A (ULift.{w} A))) := by
          ext a
          rfl
    _ = (K.map (algebraMap A (ULift.{w} A))).map (eu : ULift.{w} A →+* A) := by
          rw [Ideal.map_map]

/-- Helper for Lemma 10.101.4: quotienting by the image ideal in a `ULift` ring recovers the
original quotient ring. -/
noncomputable def ulift_quotient_ring_equiv
    {A : Type u} [CommRing A] (K : Ideal A) :
    ((ULift.{w} A) ⧸ K.map (algebraMap A (ULift.{w} A))) ≃+* (A ⧸ K) :=
  (Ideal.quotientEquivAlg _ _ (ULift.algEquiv (R := A) (A := A))
    (ulift_quotient_ring_equiv_aux K)).toRingEquiv

/-- Helper for Lemma 10.101.4: quotienting by `J • ⊤` commutes with lifting only the module
universe. -/
lemma ulift_module_quotient_equiv_exists
    {A : Type u} [CommRing A] {P : Type w} [AddCommGroup P] [Module A P] (J : Ideal A) :
    Nonempty ((((ULift.{u} P) ⧸ (J • (⊤ : Submodule A (ULift.{u} P)))) ≃ₗ[A ⧸ J]
      (P ⧸ (J • (⊤ : Submodule A P))))) := by
  let eA :
      ((ULift.{u} P) ⧸ (J • (⊤ : Submodule A (ULift.{u} P)))) ≃ₗ[A]
        (P ⧸ (J • (⊤ : Submodule A P))) :=
    Submodule.Quotient.equiv
      (J • (⊤ : Submodule A (ULift.{u} P)))
      (J • (⊤ : Submodule A P))
      (ULift.moduleEquiv : ULift.{u} P ≃ₗ[A] P)
      (by
        -- `ULift.moduleEquiv` preserves the ideal-generated top submodule exactly.
        simpa [Submodule.map_smul''])
  -- The quotient modules carry their canonical `A ⧸ J`-actions, so the same equivalence upgrades
  -- to the quotient owner.
  exact ⟨eA.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- Helper for Lemma 10.101.4: choose the quotient-module equivalence produced by the lifted
module comparison. -/
noncomputable def ulift_module_quotient_equiv
    {A : Type u} [CommRing A] {P : Type w} [AddCommGroup P] [Module A P] (J : Ideal A) :
    ((ULift.{u} P) ⧸ (J • (⊤ : Submodule A (ULift.{u} P)))) ≃ₗ[A ⧸ J]
      (P ⧸ (J • (⊤ : Submodule A P))) :=
  Classical.choice (ulift_module_quotient_equiv_exists (A := A) (P := P) J)

/-- Helper for Lemma 10.101.4: mapping a square-zero ideal into a `ULift` target keeps it
square-zero. -/
lemma ulift_map_square_zero
    {A : Type u} [CommRing A] (K : Ideal A) (hK : K ^ 2 = ⊥) :
    (K.map (algebraMap A (ULift.{w} A))) ^ 2 = ⊥ := by
  -- The ring lift preserves multiplication of ideals, so the square-zero relation maps across.
  calc
    (K.map (algebraMap A (ULift.{w} A))) ^ 2 =
        Ideal.map (algebraMap A (ULift.{w} A)) (K ^ 2) := by
          rw [← Ideal.map_pow]
    _ = Ideal.map (algebraMap A (ULift.{w} A)) ⊥ := by rw [hK]
    _ = ⊥ := by simpa

/-- Helper for Lemma 10.101.4: in the reduced square-zero setting, the source-proof kernel
comparison should force the multiplication map `J ⊗[S] N → N` to be injective. -/
lemma kernel_eq_bot_of_contracted_square_baseChange
    {S : Type u} [CommRing S] {N : Type w} [AddCommGroup N] [Module S N]
    {J : Ideal S} {S' : Type v} [CommRing S'] [Algebra S S']
    (φ : S →+* S') (hφ_inj : Function.Injective φ) (hJ_sq : J ^ 2 = ⊥)
    (hflatOwner : Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))))
    (hflatBase : Module.Flat S' (S' ⊗[S] N)) :
    LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)) = ⊥ := by
  let _ := φ
  let _ := hφ_inj
  let _ := hJ_sq
  let _ := hflatOwner
  let _ := hflatBase
  -- The remaining blocker is the explicit source-proof tensor ladder comparing
  -- `J ⊗[S] N → N` with the injective multiplication map on the base-changed image ideal.
  sorry

/-- Helper for Lemma 10.101.4: in the contracted-square reduction, the source-proof kernel
comparison should give the `Tor₁` vanishing required by Lemma `10.99.8`. -/
lemma tor_vanishes_of_contracted_square_baseChange
    {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N]
    {J : Ideal S} {S' : Type v} [CommRing S'] [Algebra S S']
    (φ : S →+* S') (hφ_inj : Function.Injective φ) (hJ_sq : J ^ 2 = ⊥)
    (hflatOwner : Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))))
    (hflatBase : Module.Flat S' (S' ⊗[S] N)) :
    IsZero ((((Tor (ModuleCat S) 1).obj (ModuleCat.of S (S ⧸ J))).obj (ModuleCat.of S N))) := by
  -- First reduce the source proof to the kernel criterion for `J ⊗[S] N → N`.
  have hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)) = ⊥ :=
    kernel_eq_bot_of_contracted_square_baseChange
      (S := S) (N := N) (J := J) (S' := S') φ hφ_inj hJ_sq hflatOwner hflatBase
  have hmoduleFirst :
      IsZero ((((Tor (ModuleCat S) 1).obj (ModuleCat.of S N)).obj
        (ModuleCat.of S (S ⧸ J)))) := by
    -- Remark `10.75.9` turns the kernel vanishing into vanishing of the module-first public owner.
    exact tor_one_module_quotient_vanishes_of_ker_eq_bot (R := S) (I := J) (N := N) hker
  let eSource :
      (((Tor (ModuleCat S) 1).obj (ModuleCat.of S N)).obj (ModuleCat.of S (S ⧸ J))) ≅
        (((Tor' (ModuleCat S) 1).obj (ModuleCat.of S N)).obj (ModuleCat.of S (S ⧸ J))) :=
    (tor_one_module_source_owner_iso (S := S) (N := N)).app (ModuleCat.of S (S ⧸ J))
  have hSource :
      IsZero ((((Tor' (ModuleCat S) 1).obj (ModuleCat.of S N)).obj
        (ModuleCat.of S (S ⧸ J)))) := by
    -- This is the corrected owner bridge: keep the module `N` fixed and move only the quotient.
    exact IsZero.of_iso hmoduleFirst eSource.symm
  let ePublic :
      (((Tor (ModuleCat S) 1).obj (ModuleCat.of S (S ⧸ J))).obj (ModuleCat.of S N)) ≅
        (((Tor' (ModuleCat S) 1).obj (ModuleCat.of S N)).obj (ModuleCat.of S (S ⧸ J))) :=
    tor_one_quotient_source_owner_iso (S := S) (N := N) J
  -- Finally return from the fixed-left-factor source owner to the quotient-first public owner.
  exact IsZero.of_iso hSource ePublic

/-- Helper for Lemma 10.101.4: lifting the reduced square-zero owner data to a common universe is
the only remaining interface step before applying Lemma `10.99.8`. -/
lemma flat_of_square_zero_ideal_of_flat_mod_ideal_and_kernel_eq_bot_ulift
    {S : Type u} [CommRing S] {N : Type w} [AddCommGroup N] [Module S N]
    {J : Ideal S}
    (hJ_sq : J ^ 2 = ⊥)
    (hflat : Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))))
    (hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)) = ⊥) :
    Module.Flat S N := by
  let Su : Type max u w := ULift.{w} S
  let Nu : Type max u w := ULift.{u} N
  let eu : Su ≃+* S := ULift.ringEquiv
  letI : CommRing Su := inferInstance
  letI : Module Su Nu := Module.compHom Nu eu.toRingHom
  let Ju : Ideal Su := J.map (algebraMap S Su)
  have hJu_sq : Ju ^ 2 = ⊥ := by
    -- The square-zero ideal survives the universe lift unchanged.
    simpa [Ju] using ulift_map_square_zero J hJ_sq
  let eQuotRing : (Su ⧸ Ju) ≃+* S ⧸ J :=
    ulift_quotient_ring_equiv J
  let _ := eQuotRing
  let _ := hJu_sq
  let _ := hflat
  let _ := hker
  -- TODO: transport `hflat` to flatness of `Nu ⧸ JuNu` over `Su ⧸ Ju`, map `hker` to the lifted
  -- kernel statement and convert it to the lifted quotient-first `Tor₁` vanishing via
  -- `tor_one_module_quotient_vanishes_of_ker_eq_bot`, apply
  -- `flatness_and_tor_vanishing_along_ideal_powers` to `(Su, Ju, Nu)`, and descend the resulting
  -- flatness along `eu`.
  sorry

/-- Lemma 10.101.4: if `M / IM` is flat over `R / I` and the base change `R' ⊗[R] M` is flat over
`R'`, then `M / I₂M` is flat over `R / I₂`, where
`I₂ = Ideal.comap (algebraMap R R') (Ideal.map (algebraMap R R') (I ^ 2))`. -/
theorem flat_quotient_comap_map_sq_of_flat_mod_ideal_and_flat_baseChange
    (hflat_mod_ideal : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hflat_baseChange : Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat (R ⧸ I₂) (M ⧸ (I₂ • ⊤ : Submodule R M)) := by
  -- Route correction: the `I ⊓ I₂` detour was the wrong owner system.
  -- The source proof reduces directly to the contracted-square quotient `S = R ⧸ I₂`, where the
  -- relevant first flatness owner is `R ⧸ (I ⊔ I₂)` and the base-change owner is `S' ⊗[S] N`.
  let S : Type u := R ⧸ I₂
  let N : Type w := M ⧸ (I₂ • ⊤ : Submodule R M)
  let J : Ideal S := Ideal.map (Ideal.Quotient.mk I₂) I
  let S' : Type v := R' ⧸ Ideal.map (algebraMap R R') (I ^ 2)
  let φ : S →+* S' := contracted_square_comparison (R := R) (R' := R') (I := I)
  have hφ_inj : Function.Injective φ :=
    contracted_square_comparison_injective (R := R) (R' := R') (I := I)
  have hJ_sq : J ^ 2 = ⊥ := by
    -- The contracted-square quotient is exactly the source square-zero reduction.
    simpa [S, J] using
      image_ideal_square_zero_in_contracted_square_quotient (R := R) (R' := R') (I := I)
  have hflat_sq_image :
      Module.Flat S'
        ((R' ⊗[R] M) ⧸
          ((Ideal.map (algebraMap R R') (I ^ 2)) •
            (⊤ : Submodule R' (R' ⊗[R] M)))) := by
    -- This isolates the standard quotient-flatness part of the reduced base-change hypothesis.
    simpa [S'] using
      flat_quotient_image_sq_of_flat_baseChange
        (R := R) (R' := R') (M := M) (I := I) hflat_baseChange
  have hflat_sup :
      Module.Flat (R ⧸ (I ⊔ I₂)) (M ⧸ ((I ⊔ I₂) • ⊤ : Submodule R M)) := by
    -- This is the source-faithful transport of the first hypothesis after quotienting by `I₂`.
    exact flat_mod_sup_contracted_square_of_flat_mod_ideal
      (R := R) (R' := R') (M := M) (I := I) hflat_mod_ideal
  letI : Algebra S S' := φ.toAlgebra
  have hflat_contracted_baseChange :
      Module.Flat S' (S' ⊗[S] N) := by
    -- The second source hypothesis only needs the one canonical tensor-quotient identification.
    let e :
        S' ⊗[S] N ≃ₗ[S']
          ((R' ⊗[R] M) ⧸
            ((Ideal.map (algebraMap R R') (I ^ 2)) •
              (⊤ : Submodule R' (R' ⊗[R] M)))) :=
      contracted_square_baseChange_linear_equiv (R := R) (R' := R') (M := M) (I := I)
    letI :
        Module.Flat S'
          ((R' ⊗[R] M) ⧸
            ((Ideal.map (algebraMap R R') (I ^ 2)) •
              (⊤ : Submodule R' (R' ⊗[R] M)))) := hflat_sq_image
    exact Module.Flat.of_linearEquiv e
  have hflat_owner :
      Module.Flat (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))) := by
  -- The first source hypothesis now sits on the exact owner required by Lemma `10.99.8`.
    simpa [S, N, J] using
      flat_contracted_square_owner_of_flat_sup_owner
        (R := R) (R' := R') (M := M) (I := I) hflat_sup
  have hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype)) = ⊥ :=
    -- The remaining mathematical input is exactly the source-proof kernel comparison in the
    -- contracted-square reduction.
    kernel_eq_bot_of_contracted_square_baseChange
      (S := S) (N := N) (J := J) (S' := S') φ hφ_inj hJ_sq hflat_owner
      hflat_contracted_baseChange
  -- Once the reduced square-zero data are in place, only the common-universe adapter from
  -- Lemma `10.99.8` remains.
  simpa [S, N, J] using
    flat_of_square_zero_ideal_of_flat_mod_ideal_and_kernel_eq_bot_ulift
      (S := S) (N := N) (J := J) hJ_sq hflat_owner hker

end

end

/-! ### Lemma_10_101_5 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] [Algebra R R']
variable {I : Ideal R}
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: commutative algebra of flatness over nilpotent thickenings and injective base
  change;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `flat_quotient_comap_map_sq_of_flat_mod_ideal_and_flat_baseChange`,
  `flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes`,
  `Module.Flat.baseChange`;
- best owner abstraction: the canonical flatness predicate `Module.Flat`, with Chapter 10's
  quotient-flatness and nilpotent-ideal owners supplying the source-facing criterion;
- primitive data: the rings `R`, `R'`, the `R`-algebra structure on `R'`, the ideal `I`, and the
  `R`-module `M`;
- derived API: the flatness hypotheses on `M / IM` and `R' ⊗[R] M`, and the resulting flatness
  of `M`.

Layering:
- this item is `source-facing`: it is the textbook nilpotent-ideal criterion under an injective
  base change;
- its proof should reuse the `core/canonical` owners above rather than introduce any parallel
  flatness wrapper or alternate owner object;
- no additional `bridge/view` declaration is needed in this file.
-/

-- Proof sketch: define recursively the ideals `I₁ = I` and
-- `I_{n + 1} = comap φ ((map φ I_n)^2)` for `φ = algebraMap R R'`. Lemma `10.101.4` shows by
-- induction that each quotient `M / I_n M` is flat over `R / I_n`. Since `I` is nilpotent, the
-- images `φ(I_n)` eventually vanish; injectivity of `φ` then gives `I_n = 0` for some `n`, so the
-- flat quotient criterion yields flatness of `M` over `R`.
/-- Helper for Lemma 10.101.5: the source-proof iteration of contracted squares. -/
def iterated_contracted_square (I : Ideal R) : ℕ → Ideal R
  | 0 => I
  | n + 1 =>
      Ideal.comap (algebraMap R R')
        (Ideal.map (algebraMap R R') ((iterated_contracted_square I n) ^ 2))

/-- Helper for Lemma 10.101.5: each stage of the contracted-square iteration has flat quotient. -/
lemma flat_quotient_iterated_contracted_square
    (hflat_mod_ideal : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hflat_baseChange : Module.Flat R' (R' ⊗[R] M)) :
    ∀ n : ℕ,
      Module.Flat (R ⧸ iterated_contracted_square (R := R) (R' := R') I n)
        (M ⧸ ((iterated_contracted_square (R := R) (R' := R') I n) •
          (⊤ : Submodule R M))) := by
  intro n
  induction n with
  | zero =>
      -- The initial stage is exactly the given flat quotient modulo `I`.
      simpa [iterated_contracted_square] using hflat_mod_ideal
  | succ n ih =>
      -- The induction step is Lemma `10.101.4` applied to the current stage ideal.
      simpa [iterated_contracted_square] using
        flat_quotient_comap_map_sq_of_flat_mod_ideal_and_flat_baseChange
          (R := R) (R' := R') (M := M)
          (I := iterated_contracted_square (R := R) (R' := R') I n)
          ih hflat_baseChange

/-- Helper for Lemma 10.101.5: every stage image is bounded by the corresponding doubled power
of the initial image ideal. -/
lemma map_iterated_contracted_square_le_image_pow_two_pow :
    ∀ n : ℕ,
      Ideal.map (algebraMap R R')
          (iterated_contracted_square (R := R) (R' := R') I n) ≤
        (Ideal.map (algebraMap R R') I) ^ (2 ^ n) := by
  intro n
  induction n with
  | zero =>
      -- At the initial stage, the estimate is the identity `φ(I) ≤ φ(I)`.
      simpa [iterated_contracted_square]
  | succ n ih =>
      -- One step of the recursion maps into the square of the previous image, so the exponent
      -- doubles.
      calc
        Ideal.map (algebraMap R R')
            (iterated_contracted_square (R := R) (R' := R') I (n + 1))
            ≤ Ideal.map (algebraMap R R')
                ((iterated_contracted_square (R := R) (R' := R') I n) ^ 2) := by
                  simpa [iterated_contracted_square] using
                    (Ideal.map_comap_le
                      (f := algebraMap R R')
                      (K := Ideal.map (algebraMap R R')
                        ((iterated_contracted_square (R := R) (R' := R') I n) ^ 2)))
        _ = (Ideal.map (algebraMap R R')
              (iterated_contracted_square (R := R) (R' := R') I n)) ^ 2 := by
              rw [Ideal.map_pow]
        _ ≤ ((Ideal.map (algebraMap R R') I) ^ (2 ^ n)) ^ 2 := by
              simpa [pow_two] using mul_le_mul ih ih
        _ = (Ideal.map (algebraMap R R') I) ^ (2 ^ (n + 1)) := by
              rw [pow_two, ← pow_add]
              congr 1
              rw [Nat.pow_succ]
              omega

/-- Helper for Lemma 10.101.5: the elementary exponent bound needed to compare nilpotence with the
doubling sequence from the source proof. -/
lemma nat_le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- The induction adds one on the left while doubling the right-hand side.
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left Nat.one_le_two_pow _
        _ = 2 ^ n * 2 := by rw [← two_mul, Nat.mul_comm]
        _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]

/-- Helper for Lemma 10.101.5: the contracted-square iteration reaches the zero ideal once the
initial ideal is nilpotent and the algebra map is injective. -/
lemma exists_iterated_contracted_square_eq_bot
    (hI : IsNilpotent I) (hinj : Function.Injective (algebraMap R R')) :
    ∃ n : ℕ, iterated_contracted_square (R := R) (R' := R') I n = ⊥ := by
  obtain ⟨k, hk⟩ := hI
  have hk_bot : I ^ k = ⊥ := by
    simpa using hk
  have hmap_pow_bot : (Ideal.map (algebraMap R R') I) ^ k = ⊥ := by
    -- Mapping preserves powers, so nilpotence of `I` descends to the image ideal.
    simpa [Ideal.map_pow] using
      congrArg (Ideal.map (algebraMap R R')) hk_bot
  have hlarge_pow_bot : (Ideal.map (algebraMap R R') I) ^ (2 ^ k) = ⊥ := by
    -- Any later power is contained in the vanishing power.
    refine le_antisymm ?_ bot_le
    exact (Ideal.pow_le_pow_right (nat_le_two_pow_self k)).trans (le_of_eq hmap_pow_bot)
  have hstage_map_bot :
      Ideal.map (algebraMap R R')
        (iterated_contracted_square (R := R) (R' := R') I k) = ⊥ := by
    -- The image estimate now lands inside the zero power found above.
    refine le_antisymm ?_ bot_le
    exact
      (map_iterated_contracted_square_le_image_pow_two_pow
        (R := R) (R' := R') (I := I) k).trans (le_of_eq hlarge_pow_bot)
  have hstage_le_bot :
      iterated_contracted_square (R := R) (R' := R') I k ≤ ⊥ := by
    -- Injectivity identifies the kernel of `R → R'` with `⊥`, so vanishing of the mapped ideal
    -- forces vanishing of the source ideal.
    have hstage_le_ker :
        iterated_contracted_square (R := R) (R' := R') I k ≤
          RingHom.ker (algebraMap R R') :=
      (Ideal.map_eq_bot_iff_le_ker (algebraMap R R')).mp hstage_map_bot
    have hker_bot : RingHom.ker (algebraMap R R') = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot (algebraMap R R')).mp hinj
    simpa [hker_bot] using hstage_le_ker
  exact ⟨k, le_antisymm hstage_le_bot bot_le⟩

/-- Helper for Lemma 10.101.5: flatness of the quotient by the zero ideal is flatness of the
original module. -/
lemma flat_of_flat_quotient_bot
    (hflat :
      Module.Flat (R ⧸ (⊥ : Ideal R))
        (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M)))) :
    Module.Flat R M := by
  have hflat_ring_quot : Module.Flat R (R ⧸ (⊥ : Ideal R)) := by
    -- The quotient ring by `⊥` is canonically the original ring.
    exact Module.Flat.of_linearEquiv (AlgEquiv.quotientBot R R).toLinearEquiv
  have hflat_quot_as_R :
      Module.Flat R (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M))) := by
    -- Transitivity converts flatness over `R / 0` to flatness over `R`.
    letI : Module.Flat R (R ⧸ (⊥ : Ideal R)) := hflat_ring_quot
    letI :
        Module.Flat (R ⧸ (⊥ : Ideal R))
          (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M))) := hflat
    exact Module.Flat.trans R (R ⧸ (⊥ : Ideal R))
      (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M)))
  have hsmul_bot : ((⊥ : Ideal R) • (⊤ : Submodule R M)) = ⊥ := by
    simp
  -- The module quotient by `0` is canonically `M`.
  letI : Module.Flat R (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M))) := hflat_quot_as_R
  exact Module.Flat.of_linearEquiv
    ((((⊥ : Ideal R) • (⊤ : Submodule R M)).quotEquivOfEqBot hsmul_bot).symm)

/-- Lemma 10.101.5: if `I` is nilpotent, `R → R'` is injective, `M / IM` is flat over `R / I`,
and the base change `R' ⊗[R] M` is flat over `R'`, then `M` is flat over `R`. -/
theorem flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange
    (hI : IsNilpotent I) (hinj : Function.Injective (algebraMap R R'))
    (hflat_mod_ideal : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hflat_baseChange : Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat R M := by
  obtain ⟨n, hn⟩ :=
    exists_iterated_contracted_square_eq_bot
      (R := R) (R' := R') (I := I) hI hinj
  have hflat_stage :
      Module.Flat (R ⧸ iterated_contracted_square (R := R) (R' := R') I n)
        (M ⧸ ((iterated_contracted_square (R := R) (R' := R') I n) •
          (⊤ : Submodule R M))) :=
    flat_quotient_iterated_contracted_square
      (R := R) (R' := R') (M := M) (I := I)
      hflat_mod_ideal hflat_baseChange n
  have hflat_bot_quot :
      Module.Flat (R ⧸ (⊥ : Ideal R))
        (M ⧸ (((⊥ : Ideal R)) • (⊤ : Submodule R M))) := by
    -- At the vanishing stage, the inductive flat quotient is exactly the quotient by zero.
    exact hn ▸ hflat_stage
  -- Transport the final zero-stage quotient flatness back to the original module.
  exact flat_of_flat_quotient_bot (R := R) (M := M) hflat_bot_quot

end
