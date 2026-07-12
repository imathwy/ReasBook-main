import Mathlib
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_82_13
import StacksProject_2024.Chap15.Lemma_15_3_2
import StacksProject_2024.Chap15.Definition_15_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [Ring R]
variable {I : Ideal R} [I.IsTwoSided]
variable {E : Type v} [AddCommGroup E] [Module (R ⧸ I) E]
variable {S : Type*} [Ring S]

open CategoryTheory

/-- Helper for Lemma 15.3.3: after subtracting the chosen section part, a point lies in the
kernel of the split surjection. -/
theorem sub_section_mem_ker_of_rightInverse
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (q : P →ₗ[R] Q) (s : Q →ₗ[R] P) (hs : q.comp s = LinearMap.id) (z : P) :
    z - s (q z) ∈ LinearMap.ker q := by
  -- Applying `q` removes the corrected section term because `q ∘ s = id`.
  change q (z - s (q z)) = 0
  have hs_apply : q (s (q z)) = q z := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : Q →ₗ[R] Q => f (q z)) hs
  simpa [hs_apply]

/-- Helper for Lemma 15.3.3: containment in `Ring.jacobson R` is the same as containment in the
Jacobson radical of the zero ideal. -/
theorem le_jacobson_bot_of_le_ring_jacobson
    {J : Ideal R} (hJ : J ≤ Ring.jacobson R) :
    J ≤ Ideal.jacobson (⊥ : Ideal R) := by
  -- Rewrite the ring-level Jacobson radical as the ideal-level radical of `⊥`.
  simpa [Ideal.jacobson_bot] using hJ

/-- Helper for Lemma 15.3.3: a quotient linear map from a projective source lifts through the
canonical quotient projection. -/
theorem exists_lift_with_prescribed_quotientMapByIdeal
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    {M : Type*} [AddCommGroup M] [Module R M]
    (gbar : Q ⧸ (I • (⊤ : Submodule R Q)) →ₗ[R] M ⧸ (I • (⊤ : Submodule R M))) :
    ∃ g : Q →ₗ[R] M, g.quotientMapByIdeal I = gbar := by
  let gbarLift : Q →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
    gbar.comp (I • (⊤ : Submodule R Q)).mkQ
  -- Lift the quotient map through the canonical quotient projection.
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property (I • (⊤ : Submodule R M)).mkQ gbarLift
      (Submodule.mkQ_surjective _)
  have hgsmul : I • (⊤ : Submodule R Q) ≤ Submodule.comap g (I • (⊤ : Submodule R M)) := by
    exact Submodule.smul_top_le_comap_smul_top I g
  have hcomp :
      ((I • (⊤ : Submodule R Q)).mapQ (I • (⊤ : Submodule R M)) g hgsmul).comp
          (I • (⊤ : Submodule R Q)).mkQ =
        (I • (⊤ : Submodule R M)).mkQ.comp g :=
    Submodule.mapQ_mkQ (I • (⊤ : Submodule R Q)) (I • (⊤ : Submodule R M)) g
  refine ⟨g, ?_⟩
  -- Evaluate on quotient representatives to identify the induced quotient map.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R Q)) x
  simpa [LinearMap.quotientMapByIdeal, gbarLift] using
    (DFunLike.congr_fun hcomp x).trans (DFunLike.congr_fun hg x)

/-- Helper for Lemma 15.3.3: evaluating a quotient map on a quotient class matches quotienting
after applying the underlying linear map. -/
theorem quotientMapByIdeal_apply_mkQ
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (x : M) :
    f.quotientMapByIdeal I ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (f x) := by
  -- Expand the induced quotient map through the defining `mapQ_mkQ` square.
  simpa [LinearMap.quotientMapByIdeal] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ (I • (⊤ : Submodule R M)) (I • (⊤ : Submodule R N)) f) x

/-- Helper for Lemma 15.3.3: quotient reduction commutes with composition. -/
theorem quotientMapByIdeal_comp
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    (g.comp f).quotientMapByIdeal I =
      (g.quotientMapByIdeal I).comp (f.quotientMapByIdeal I) := by
  -- Check the two quotient maps on quotient representatives.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) x
  simp [quotientMapByIdeal_apply_mkQ]

/-- Helper for Lemma 15.3.3: quotient inverses force the lifted composites to become the identity
after reduction modulo `I`. -/
theorem quotientMapByIdeal_comp_eq_id_of_inverse
    {P : Type*} [AddCommGroup P] [Module R P]
    {P' : Type*} [AddCommGroup P'] [Module R P']
    (e : (P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R] (P' ⧸ (I • (⊤ : Submodule R P'))))
    (f : P →ₗ[R] P') (g : P' →ₗ[R] P)
    (hf : f.quotientMapByIdeal I = e.toLinearMap)
    (hg : g.quotientMapByIdeal I = e.symm.toLinearMap) :
    (g.comp f).quotientMapByIdeal I = LinearMap.id ∧
      (f.comp g).quotientMapByIdeal I = LinearMap.id := by
  constructor
  · -- Evaluate on quotient representatives and rewrite by the inverse identities.
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) x
    calc
      (g.comp f).quotientMapByIdeal I ((I • (⊤ : Submodule R P)).mkQ x)
          = (I • (⊤ : Submodule R P)).mkQ (g (f x)) := by
              simp [quotientMapByIdeal_apply_mkQ]
      _ = g.quotientMapByIdeal I
            (f.quotientMapByIdeal I ((I • (⊤ : Submodule R P)).mkQ x)) := by
            simp [quotientMapByIdeal_apply_mkQ]
      _ = e.symm.toLinearMap (e.toLinearMap ((I • (⊤ : Submodule R P)).mkQ x)) := by
            rw [hf, hg]
      _ = (I • (⊤ : Submodule R P)).mkQ x := by simp
  · -- The same computation gives the identity on the target quotient.
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P')) x
    calc
      (f.comp g).quotientMapByIdeal I ((I • (⊤ : Submodule R P')).mkQ x)
          = (I • (⊤ : Submodule R P')).mkQ (f (g x)) := by
              simp [quotientMapByIdeal_apply_mkQ]
      _ = f.quotientMapByIdeal I
            (g.quotientMapByIdeal I ((I • (⊤ : Submodule R P')).mkQ x)) := by
            simp [quotientMapByIdeal_apply_mkQ]
      _ = e.toLinearMap (e.symm.toLinearMap ((I • (⊤ : Submodule R P')).mkQ x)) := by
            rw [hf, hg]
      _ = (I • (⊤ : Submodule R P')).mkQ x := by simp

/-- Helper for Lemma 15.3.3: surjectivity modulo `I` says the image plus `I M` already fills the
target module. -/
theorem range_sup_smul_top_eq_top_of_quotientMap_surjective
    {N : Type*} [AddCommGroup N] [Module R N]
    {M : Type*} [AddCommGroup M] [Module R M]
    (g : N →ₗ[R] M)
    (hquot : Function.Surjective (g.quotientMapByIdeal I)) :
    LinearMap.range g ⊔ I • (⊤ : Submodule R M) = ⊤ := by
  -- Lift each quotient class of `M / I M` back through the surjective reduced map.
  apply top_unique
  intro x _
  obtain ⟨ybar, hybar⟩ := hquot ((I • (⊤ : Submodule R M)).mkQ x)
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) ybar
  have hdiff :
      x - g y ∈ I • (⊤ : Submodule R M) := by
    -- Equal quotient classes differ by an element of `I M`.
    have hquot_eq :
        (I • (⊤ : Submodule R M)).mkQ x =
          (I • (⊤ : Submodule R M)).mkQ (g y) := by
      simpa [quotientMapByIdeal_apply_mkQ] using hybar.symm
    exact (Submodule.Quotient.eq _).1 hquot_eq
  have hrange : g y ∈ LinearMap.range g := ⟨y, rfl⟩
  have hsum :
      g y + (x - g y) ∈ LinearMap.range g ⊔ I • (⊤ : Submodule R M) :=
    Submodule.add_mem_sup hrange hdiff
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Lemma 15.3.3: surjectivity after quotienting by `I` upgrades to surjectivity over
`R` when `I` lies in the Jacobson radical. -/
theorem surjective_of_quotientMap_surjective_of_le_ring_jacobson_noncomm
    {N : Type*} [AddCommGroup N] [Module R N]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (g : N →ₗ[R] M)
    (hquot : Function.Surjective (g.quotientMapByIdeal I))
    (hI : I ≤ Ring.jacobson R) :
    Function.Surjective g := by
  let Q := M ⧸ LinearMap.range g
  letI : Module.Finite R Q :=
    Module.Finite.of_surjective (LinearMap.range g).mkQ (Submodule.mkQ_surjective _)
  have hsup :
      LinearMap.range g ⊔ I • (⊤ : Submodule R M) = ⊤ :=
    range_sup_smul_top_eq_top_of_quotientMap_surjective (I := I) g hquot
  have hmap_top :
      Submodule.map (LinearMap.range g).mkQ (I • (⊤ : Submodule R M)) =
        (⊤ : Submodule R Q) := by
    -- Passing to the cokernel of the range turns `range g ⊔ I M = M` into `I Q = Q`.
    rw [Submodule.map_mkQ_eq_top]
    exact hsup
  have hIQ :
      I • (⊤ : Submodule R Q) = ⊤ := by
    simpa [Q, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] using hmap_top
  have htop :
      (⊤ : Submodule R Q) ≤ Ring.jacobson R • (⊤ : Submodule R Q) := by
    -- Because `Q = I Q` and `I ≤ Jac(R)`, Nakayama kills the cokernel.
    have htop_I : (⊤ : Submodule R Q) ≤ I • (⊤ : Submodule R Q) := by
      simpa [hIQ]
    exact le_trans htop_I (Submodule.smul_mono hI le_rfl)
  have hQbot : (⊤ : Submodule R Q) = ⊥ :=
    Submodule.FG.eq_bot_of_le_jacobson_smul Module.Finite.fg_top htop
  intro x
  have hxzero : (LinearMap.range g).mkQ x = 0 := by
    -- In the zero cokernel every quotient class vanishes.
    have hxmem : (LinearMap.range g).mkQ x ∈ (⊤ : Submodule R Q) := by
      simp
    have hxbot : (LinearMap.range g).mkQ x ∈ (⊥ : Submodule R Q) := by
      simpa [hQbot] using hxmem
    simpa using hxbot
  exact (Submodule.Quotient.mk_eq_zero _).1 hxzero

/-- Helper for Lemma 15.3.3: the coordinatewise quotient map sends a finite free module over `R`
to the corresponding finite free module over `R ⧸ I`. -/
noncomputable def free_pi_quotient_map (n : ℕ) :
    (Fin n → R) →ₗ[R] (Fin n → R ⧸ I) where
  toFun := fun x i ↦ Ideal.Quotient.mk I (x i)
  map_add' := by
    intro x y
    ext i
    rfl
  map_smul' := by
    intro a x
    ext i
    rfl

/-- Helper for Lemma 15.3.3: a vector in `Fin n → R` lies in `I • ⊤` exactly when each of its
coordinates lies in `I`. -/
theorem mem_smul_top_fin_fun_iff
    (n : ℕ) (x : Fin n → R) :
    x ∈ I • (⊤ : Submodule R (Fin n → R)) ↔ ∀ i, x i ∈ I := by
  constructor
  · intro hx
    -- The coordinatewise ideal-membership statement is stable under the generators of `I • ⊤`.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y hy i
      simpa [smul_eq_mul] using I.mul_mem_right (y i) ha
    · intro y z hy hz i
      exact I.add_mem (hy i) (hz i)
  · intro hx
    -- Rebuild the vector from the standard basis and place each basis term in `I • ⊤`.
    have hx_repr :
        x = ∑ i, x i • Pi.basisFun R (Fin n) i := by
      simpa [Pi.basisFun_repr] using ((Pi.basisFun R (Fin n)).sum_repr x).symm
    rw [hx_repr]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    exact
      Submodule.smul_mem_smul (I := I) (N := (⊤ : Submodule R (Fin n → R))) (hx i)
        (by simp)

/-- Helper for Lemma 15.3.3: the kernel of the coordinatewise quotient map is exactly `I • ⊤`. -/
theorem ker_free_pi_quotient_map
    (n : ℕ) :
    LinearMap.ker (free_pi_quotient_map (R := R) (I := I) n) =
      I • (⊤ : Submodule R (Fin n → R)) := by
  ext x
  constructor
  · intro hx
    change free_pi_quotient_map (R := R) (I := I) n x = 0 at hx
    rw [mem_smul_top_fin_fun_iff (I := I) n x]
    intro i
    have hxi : (free_pi_quotient_map (R := R) (I := I) n x) i = 0 := by
      exact congrFun hx i
    exact (Ideal.Quotient.eq_zero_iff_mem (I := I)).mp <| by
      simpa [free_pi_quotient_map] using hxi
  · intro hx
    change free_pi_quotient_map (R := R) (I := I) n x = 0
    ext i
    exact (Ideal.Quotient.eq_zero_iff_mem (I := I)).mpr <|
      (mem_smul_top_fin_fun_iff (I := I) n x).mp hx i

/-- Helper for Lemma 15.3.3: the coordinatewise quotient map onto `Fin n → R ⧸ I` is surjective.
-/
theorem free_pi_quotient_map_surjective
    (n : ℕ) :
    Function.Surjective (free_pi_quotient_map (R := R) (I := I) n) := by
  intro y
  choose x hx using fun i : Fin n ↦ Ideal.Quotient.mk_surjective (I := I) (y i)
  refine ⟨x, ?_⟩
  ext i
  exact hx i

/-- Helper for Lemma 15.3.3: quotienting `Fin n → R` by `I • ⊤` identifies it with
`Fin n → R ⧸ I`. -/
noncomputable def free_pi_quotient_equiv
    (n : ℕ) :
    ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) ≃ₗ[R] (Fin n → R ⧸ I) := by
  let π := free_pi_quotient_map (R := R) (I := I) n
  let hker :
      I • (⊤ : Submodule R (Fin n → R)) = LinearMap.ker π :=
    (ker_free_pi_quotient_map (R := R) (I := I) n).symm
  let hrange : LinearMap.range π = ⊤ :=
    LinearMap.range_eq_top.2 (free_pi_quotient_map_surjective (R := R) (I := I) n)
  -- Rewrite to the actual kernel of the quotient map, then collapse its full range back to the
  -- codomain.
  exact
    (Submodule.quotEquivOfEq _ _ hker).trans
      (π.quotKerEquivRange.trans ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))

/-- Helper for Lemma 15.3.3: the forward split map adds a kernel vector to the chosen section
component. -/
noncomputable def kernel_prod_forward
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (q : P →ₗ[R] Q) (s : Q →ₗ[R] P) :
    ((LinearMap.ker q) × Q) →ₗ[R] P :=
  LinearMap.coprod (LinearMap.ker q).subtype s

/-- Helper for Lemma 15.3.3: the backward split map removes the section component and records the
quotient coordinate. -/
noncomputable def kernel_prod_backward
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (q : P →ₗ[R] Q) (s : Q →ₗ[R] P) (hs : q.comp s = LinearMap.id) :
    P →ₗ[R] ((LinearMap.ker q) × Q) :=
  LinearMap.prod
    (LinearMap.codRestrict (LinearMap.ker q) (LinearMap.id - s.comp q)
      (fun z ↦ sub_section_mem_ker_of_rightInverse q s hs z))
    q

/-- Helper for Lemma 15.3.3: correcting a point and then adding back its section part recovers
the original point. -/
theorem kernel_prod_forward_comp_backward
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (q : P →ₗ[R] Q) (s : Q →ₗ[R] P) (hs : q.comp s = LinearMap.id) :
    (kernel_prod_forward q s).comp (kernel_prod_backward q s hs) = LinearMap.id := by
  apply DFunLike.ext
  intro z
  -- The corrected kernel part and the chosen section term recombine to `z`.
  simp [kernel_prod_forward, kernel_prod_backward, hs, sub_eq_add_neg, add_assoc]

/-- Helper for Lemma 15.3.3: decomposing a split pair and then correcting it returns the original
kernel/target coordinates. -/
theorem kernel_prod_backward_comp_forward
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (q : P →ₗ[R] Q) (s : Q →ₗ[R] P) (hs : q.comp s = LinearMap.id) :
    (kernel_prod_backward q s hs).comp (kernel_prod_forward q s) = LinearMap.id := by
  apply DFunLike.ext
  intro x
  -- Compare the kernel and target coordinates separately.
  apply Prod.ext
  · apply Subtype.ext
    change ((kernel_prod_backward q s hs) ((kernel_prod_forward q s) x)).1.1 = x.1.1
    have hxker : q x.1.1 = 0 := x.1.2
    have hs_apply : q (s x.2) = x.2 := by
      simpa [LinearMap.comp_apply] using congrArg (fun f : Q →ₗ[R] Q => f x.2) hs
    simp [kernel_prod_forward, kernel_prod_backward, hxker, hs_apply, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  · have hxker : q x.1.1 = 0 := x.1.2
    have hs_apply : q (s x.2) = x.2 := by
      simpa [LinearMap.comp_apply] using congrArg (fun f : Q →ₗ[R] Q => f x.2) hs
    change q ((kernel_prod_forward q s) x) = x.2
    simp [kernel_prod_forward, hxker, hs_apply]

/-- Helper for Lemma 15.3.3: the split surjection identifies the ambient module with the product
of its kernel and the target. -/
noncomputable def kernel_prod_equiv_of_rightInverse
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (q : P →ₗ[R] Q) (s : Q →ₗ[R] P) (hs : q.comp s = LinearMap.id) :
    ((LinearMap.ker q) × Q) ≃ₗ[R] P :=
  LinearEquiv.ofLinear
    (kernel_prod_forward q s)
    (kernel_prod_backward q s hs)
    (kernel_prod_forward_comp_backward q s hs)
    (kernel_prod_backward_comp_forward q s hs)

/-- Helper for Lemma 15.3.3: if an element of `I • P` is corrected by subtracting its section
part, the result comes from `I • ker q`. -/
theorem sub_section_mem_map_smul_top_ker_of_rightInverse
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (q : P →ₗ[R] Q) (s : Q →ₗ[R] P) (hs : q.comp s = LinearMap.id)
    {z : P} (hz : z ∈ I • (⊤ : Submodule R P)) :
    z - s (q z) ∈
      Submodule.map (LinearMap.ker q).subtype (I • (⊤ : Submodule R (LinearMap.ker q))) := by
  -- Keep the corrected term `z - s (q z)` as the induction invariant on `I • ⊤`.
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro a ha x hx
    refine ⟨a • ⟨x - s (q x), sub_section_mem_ker_of_rightInverse q s hs x⟩, ?_, ?_⟩
    · simpa using
        (Submodule.smul_mem_smul
          (I := I)
          (N := (⊤ : Submodule R (LinearMap.ker q)))
          ha
          (by simp) :
          a • ⟨x - s (q x), sub_section_mem_ker_of_rightInverse q s hs x⟩ ∈
            I • (⊤ : Submodule R (LinearMap.ker q)))
    · simp [smul_sub, LinearMap.map_smul]
  · intro x y hx hy
    -- The induction invariant is additive because both `q` and `s` are linear.
    simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      Submodule.add_mem _ hx hy

/-- Helper for Lemma 15.3.3: quotienting a kernel element lands in the kernel of the reduced map.
-/
theorem quotient_mk_mem_ker_of_mem_ker
    {n m : ℕ}
    (q : (Fin n → R) →ₗ[R] (Fin m → R))
    (qbar :
      ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
        ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))))
    (hqbar : q.quotientMapByIdeal I = qbar)
    (x : LinearMap.ker q) :
    (I • (⊤ : Submodule R (Fin n → R))).mkQ x.1 ∈ LinearMap.ker qbar := by
  -- Evaluate `qbar` on the quotient representative and use that `x` already lies in `ker q`.
  change qbar ((I • (⊤ : Submodule R (Fin n → R))).mkQ x.1) = 0
  rw [← hqbar, quotientMapByIdeal_apply_mkQ]
  simpa [x.2]

/-- Helper for Lemma 15.3.3: the split kernel quotient descends to the reduced kernel by taking
the quotient class of the ambient representative. -/
noncomputable def split_reduction_kernel_map
    {n m : ℕ}
    (q : (Fin n → R) →ₗ[R] (Fin m → R))
    (s : (Fin m → R) →ₗ[R] (Fin n → R))
    (qbar :
      ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
        ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))))
    (hs : q.comp s = LinearMap.id)
    (hqbar : q.quotientMapByIdeal I = qbar) :
    ((LinearMap.ker q) ⧸ (I • (⊤ : Submodule R (LinearMap.ker q)))) →ₗ[R]
      LinearMap.ker qbar := by
  let toReducedKernel : LinearMap.ker q →ₗ[R] LinearMap.ker qbar :=
    LinearMap.codRestrict (LinearMap.ker qbar)
      (((I • (⊤ : Submodule R (Fin n → R))).mkQ).comp (LinearMap.ker q).subtype)
      (quotient_mk_mem_ker_of_mem_ker (I := I) q qbar hqbar)
  have hkill :
      I • (⊤ : Submodule R (LinearMap.ker q)) ≤ LinearMap.ker toReducedKernel := by
    intro x hx
    -- Elements coming from `I • ker q` become zero after quotienting the ambient representative.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y hy
      apply Subtype.ext
      change (I • (⊤ : Submodule R (Fin n → R))).mkQ (a • y.1) = 0
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      simpa using
        (Submodule.smul_mem_smul
          (I := I)
          (N := (⊤ : Submodule R (Fin n → R)))
          ha
          (by simp) :
          a • y.1 ∈ I • (⊤ : Submodule R (Fin n → R)))
    · intro x y hx hy
      apply Subtype.ext
      have hx0 : (toReducedKernel x).1 = 0 := by
        simpa using congrArg Subtype.val hx
      have hy0 : (toReducedKernel y).1 = 0 := by
        simpa using congrArg Subtype.val hy
      simp [hx0, hy0]
  -- Descend the ambient quotient-class map across the quotient of `ker q`.
  exact Submodule.liftQ (I • (⊤ : Submodule R (LinearMap.ker q))) toReducedKernel hkill

/-- Helper for Lemma 15.3.3: the descended kernel map evaluates on a representative by quotienting
its ambient component. -/
theorem split_reduction_kernel_map_mkQ
    {n m : ℕ}
    (q : (Fin n → R) →ₗ[R] (Fin m → R))
    (s : (Fin m → R) →ₗ[R] (Fin n → R))
    (qbar :
      ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
        ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))))
    (hs : q.comp s = LinearMap.id)
    (hqbar : q.quotientMapByIdeal I = qbar)
    (z : LinearMap.ker q) :
    split_reduction_kernel_map (I := I) q s qbar hs hqbar
        ((I • (⊤ : Submodule R (LinearMap.ker q))).mkQ z) =
      ⟨(I • (⊤ : Submodule R (Fin n → R))).mkQ z.1,
        quotient_mk_mem_ker_of_mem_ker (I := I) q qbar hqbar z⟩ := by
  -- Unfold once and evaluate the descended quotient map on the chosen representative.
  rw [split_reduction_kernel_map]
  rfl

/-- Helper for Lemma 15.3.3: every reduced-kernel class has a corrected representative in the
lifted kernel. -/
theorem split_reduction_kernel_map_surjective
    {n m : ℕ}
    (q : (Fin n → R) →ₗ[R] (Fin m → R))
    (s : (Fin m → R) →ₗ[R] (Fin n → R))
    (qbar :
      ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
        ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))))
    (hs : q.comp s = LinearMap.id)
    (hqbar : q.quotientMapByIdeal I = qbar) :
    Function.Surjective (split_reduction_kernel_map (I := I) q s qbar hs hqbar) := by
  intro y
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R (Fin n → R))) y.1
  have hqx_zero : (I • (⊤ : Submodule R (Fin m → R))).mkQ (q x) = 0 := by
    -- The quotient-side kernel condition says that the quotient class of `q x` vanishes.
    have hy_zero : qbar ((I • (⊤ : Submodule R (Fin n → R))).mkQ x) = 0 := by
      simpa [hx] using y.2
    simpa [← hqbar, quotientMapByIdeal_apply_mkQ] using hy_zero
  have hqx_mem : q x ∈ I • (⊤ : Submodule R (Fin m → R)) :=
    (Submodule.Quotient.mk_eq_zero _).1 hqx_zero
  have hsqx_mem : s (q x) ∈ I • (⊤ : Submodule R (Fin n → R)) := by
    exact (Submodule.smul_top_le_comap_smul_top I s) hqx_mem
  let z : LinearMap.ker q :=
    ⟨x - s (q x), sub_section_mem_ker_of_rightInverse q s hs x⟩
  refine ⟨(I • (⊤ : Submodule R (LinearMap.ker q))).mkQ z, ?_⟩
  rw [split_reduction_kernel_map_mkQ (I := I) q s qbar hs hqbar z]
  apply Subtype.ext
  have hsqx_zero : (I • (⊤ : Submodule R (Fin n → R))).mkQ (s (q x)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hsqx_mem
  calc
    (I • (⊤ : Submodule R (Fin n → R))).mkQ z.1
        = (I • (⊤ : Submodule R (Fin n → R))).mkQ x
            - (I • (⊤ : Submodule R (Fin n → R))).mkQ (s (q x)) := by
              simp [z]
    _ = y.1 - 0 := by rw [hx, hsqx_zero]
    _ = y.1 := by simp

/-- Helper for Lemma 15.3.3: if the descended kernel class is trivial, the original class already
lies in `I • ker q`. -/
theorem split_reduction_kernel_map_injective
    {n m : ℕ}
    (q : (Fin n → R) →ₗ[R] (Fin m → R))
    (s : (Fin m → R) →ₗ[R] (Fin n → R))
    (qbar :
      ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
        ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))))
    (hs : q.comp s = LinearMap.id)
    (hqbar : q.quotientMapByIdeal I = qbar) :
    Function.Injective (split_reduction_kernel_map (I := I) q s qbar hs hqbar) := by
  intro x y hxy
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R (LinearMap.ker q))) x
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R (LinearMap.ker q))) y
  rw [split_reduction_kernel_map_mkQ (I := I) q s qbar hs hqbar z,
    split_reduction_kernel_map_mkQ (I := I) q s qbar hs hqbar w] at hxy
  apply (Submodule.Quotient.eq _).2
  have hambient :
      (I • (⊤ : Submodule R (Fin n → R))).mkQ z.1 =
        (I • (⊤ : Submodule R (Fin n → R))).mkQ w.1 := by
    exact congrArg Subtype.val hxy
  have hdiff_mem :
      z.1 - w.1 ∈ I • (⊤ : Submodule R (Fin n → R)) :=
    (Submodule.Quotient.eq _).1 hambient
  have hmap_mem :
      z.1 - w.1 ∈
        Submodule.map (LinearMap.ker q).subtype
          (I • (⊤ : Submodule R (LinearMap.ker q))) := by
    -- Because `z - w` already lies in the kernel, the split correction does not change it.
    simpa [map_sub, z.2, w.2] using
      sub_section_mem_map_smul_top_ker_of_rightInverse
        (I := I) q s hs (z := z.1 - w.1) hdiff_mem
  rcases hmap_mem with ⟨u, huI, huval⟩
  have huzw : u = z - w := by
    apply Subtype.ext
    simpa using huval
  simpa [huzw] using huI

/-- Helper for Lemma 15.3.3: the quotient of the lifted kernel identifies with the reduced kernel
of the quotient map. -/
noncomputable def kernel_quotient_equiv_of_split_reduction
    {n m : ℕ}
    (q : (Fin n → R) →ₗ[R] (Fin m → R))
    (s : (Fin m → R) →ₗ[R] (Fin n → R))
    (qbar :
      ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
        ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))))
    (hs : q.comp s = LinearMap.id)
    (hqbar : q.quotientMapByIdeal I = qbar) :
    ((LinearMap.ker q) ⧸ (I • (⊤ : Submodule R (LinearMap.ker q)))) ≃ₗ[R]
      LinearMap.ker qbar := by
  -- Package the descended map once surjectivity and injectivity have been established.
  exact LinearEquiv.ofBijective
    (split_reduction_kernel_map (I := I) q s qbar hs hqbar)
    ⟨split_reduction_kernel_map_injective (I := I) q s qbar hs hqbar,
      split_reduction_kernel_map_surjective (I := I) q s qbar hs hqbar⟩

/-- Helper for Lemma 15.3.3: restricting scalars from `R ⧸ I` to `R` does not change the kernel
of the quotient-side projection map. -/
theorem kernel_restrictScalars_eq_of_quotient_projection
    {n m : ℕ}
    (qbar : (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I)) :
    LinearMap.ker (LinearMap.restrictScalars R qbar) =
      Submodule.restrictScalars R (LinearMap.ker qbar) := by
  -- This is the standard kernel comparison for a map viewed over fewer scalars.
  simpa using (LinearMap.ker_restrictScalars R qbar)

/-- Helper for Lemma 15.3.3: after choosing a stabilized trivialization, the kernel of the
quotient-side projection is canonically the left summand `E`. -/
theorem ker_stabilized_projection_equiv_left
    {m n : ℕ}
    (e0 : (E × (Fin m → R ⧸ I)) ≃ₗ[R ⧸ I] (Fin n → R ⧸ I)) :
    Nonempty
      (LinearMap.ker
          ((LinearMap.snd (R := R ⧸ I) E (Fin m → R ⧸ I)).comp e0.symm.toLinearMap) ≃ₗ[R ⧸ I]
        E) := by
  let q0 :
      (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I) :=
    ((LinearMap.snd (R := R ⧸ I) E (Fin m → R ⧸ I)).comp e0.symm.toLinearMap)
  let forward : LinearMap.ker q0 →ₗ[R ⧸ I] E :=
    (((LinearMap.fst (R := R ⧸ I) E (Fin m → R ⧸ I)).comp e0.symm.toLinearMap).comp
      (LinearMap.ker q0).subtype)
  let backward : E →ₗ[R ⧸ I] LinearMap.ker q0 :=
    LinearMap.codRestrict (LinearMap.ker q0)
      (e0.toLinearMap.comp (LinearMap.inl (R := R ⧸ I) E (Fin m → R ⧸ I)))
      (by
        intro e
        -- The image of `(e, 0)` is in the kernel because the quotient-side projection is `snd`.
        simp [q0, LinearMap.comp_assoc, LinearMap.comp_apply])
  refine ⟨LinearEquiv.ofLinear forward backward ?_ ?_⟩
  · apply DFunLike.ext
    intro x
    -- Applying `e0.symm` to `e0 (x, 0)` recovers `(x, 0)`, so the first coordinate is `x`.
    simp [forward, backward, q0, LinearMap.comp_assoc]
  · apply DFunLike.ext
    intro x
    -- The kernel condition forces the second coordinate of `e0.symm x` to vanish.
    apply Subtype.ext
    have hxzero : (e0.symm x.1).2 = 0 := by
      have hxker : q0 x.1 = 0 := x.2
      ext i
      change q0 x.1 i = 0
      exact congrFun hxker i
    have hxpair : e0.symm x.1 = ((e0.symm x.1).1, 0) := by
      exact Prod.ext rfl hxzero
    change e0 ((e0.symm x.1).1, 0) = x.1
    rw [← hxpair]
    simp

/-- Helper for Lemma 15.3.3: the quotient-side stabilized projection splits by the obvious
inclusion of the free summand. -/
theorem stabilized_projection_section_rightInverse
    {m n : ℕ}
    (e0 : (E × (Fin m → R ⧸ I)) ≃ₗ[R ⧸ I] (Fin n → R ⧸ I)) :
    (((LinearMap.snd (R := R ⧸ I) E (Fin m → R ⧸ I)).comp e0.symm.toLinearMap).comp
        (e0.toLinearMap.comp (LinearMap.inr (R := R ⧸ I) E (Fin m → R ⧸ I)))) =
      LinearMap.id := by
  -- Reassociate the composite and cancel `e0.symm` against `e0`, leaving `snd ∘ inr = id`.
  apply DFunLike.ext
  intro x
  simp [LinearMap.comp_assoc]

/-- Helper for Lemma 15.3.3: any quotient-linear equivalence is available as a nonempty witness. -/
theorem nonempty_linearEquiv_over_quotient_of_restrictScalars
    {M : Type*} [AddCommGroup M] [Module (R ⧸ I) M]
    {N : Type*} [AddCommGroup N] [Module (R ⧸ I) N]
    (e : M ≃ₗ[R ⧸ I] N) :
    Nonempty (M ≃ₗ[R ⧸ I] N) := by
  exact ⟨e⟩

/-- Helper for Lemma 15.3.3: if `u` is the identity modulo `I`, then any right inverse to `u`
is also the identity modulo `I`. -/
theorem quotientMapByIdeal_eq_id_of_comp_eq_id
    {m : ℕ}
    (u v : (Fin m → R) →ₗ[R] (Fin m → R))
    (hu : u.quotientMapByIdeal I = LinearMap.id)
    (huv : u.comp v = LinearMap.id) :
    v.quotientMapByIdeal I = LinearMap.id := by
  -- Reduce the identity `u ∘ v = id` modulo `I` and cancel the already-corrected `u`.
  calc
    v.quotientMapByIdeal I = (LinearMap.id).comp (v.quotientMapByIdeal I) := by simp
    _ = (u.comp v).quotientMapByIdeal I := by
      rw [quotientMapByIdeal_comp, hu]
    _ = LinearMap.id := by simpa [huv]

/-- Helper for Lemma 15.3.3: after correcting the lifted projection by the Jacobson inverse on the
free summand, the corrected map still reduces to the original quotient projection and now splits
against the chosen section. -/
theorem corrected_projection_data
    {n m : ℕ}
    (q : (Fin n → R) →ₗ[R] (Fin m → R))
    (s : (Fin m → R) →ₗ[R] (Fin n → R))
    (qbar :
      ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
        ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))))
    (v : (Fin m → R) →ₗ[R] (Fin m → R))
    (hq : q.quotientMapByIdeal I = qbar)
    (hu : (q.comp s).quotientMapByIdeal I = LinearMap.id)
    (huv : (q.comp s).comp v = LinearMap.id)
    (hvu : v.comp (q.comp s) = LinearMap.id) :
    ((v.comp q).comp s = LinearMap.id) ∧
      (v.comp q).quotientMapByIdeal I = qbar := by
  constructor
  · -- Regroup the corrected projection with the section and use the chosen inverse identity.
    simpa [LinearMap.comp_assoc] using hvu
  · -- Reducing modulo `I` shows that the correction factor `v` becomes the identity.
    have hv :
        v.quotientMapByIdeal I = LinearMap.id :=
      quotientMapByIdeal_eq_id_of_comp_eq_id (I := I) (u := q.comp s) v hu huv
    calc
      (v.comp q).quotientMapByIdeal I =
          (v.quotientMapByIdeal I).comp (q.quotientMapByIdeal I) := by
            rw [quotientMapByIdeal_comp]
      _ = LinearMap.id.comp qbar := by rw [hv, hq]
      _ = qbar := by simp

/-- Helper for Lemma 15.3.3: an endomorphism of a finite free module reducing to the identity
modulo `I` is invertible. -/
theorem exists_linear_inverse_of_reduction_eq_id_pi_of_le_jacobson
    (m : ℕ) (u : (Fin m → R) →ₗ[R] (Fin m → R))
    (hu : u.quotientMapByIdeal I = LinearMap.id)
    (hI : I ≤ Ring.jacobson R) :
    ∃ v : (Fin m → R) →ₗ[R] (Fin m → R),
      u.comp v = LinearMap.id ∧ v.comp u = LinearMap.id := by
  -- Route correction: split the surjection and kill the kernel using the already-built kernel API.
  have hquot : Function.Surjective (u.quotientMapByIdeal I) := by
    simpa [hu] using
      (show Function.Surjective
          (LinearMap.id :
            ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))) →ₗ[R]
              ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R))))) from
        fun y ↦ ⟨y, rfl⟩)
  have hsurj : Function.Surjective u :=
    surjective_of_quotientMap_surjective_of_le_ring_jacobson_noncomm
      (I := I) u hquot hI
  obtain ⟨v, huv⟩ := Module.projective_lifting_property
    u (LinearMap.id : (Fin m → R) →ₗ[R] (Fin m → R)) hsurj
  have htop_I :
      (⊤ : Submodule R (LinearMap.ker u)) ≤ I • (⊤ : Submodule R (LinearMap.ker u)) := by
    intro x _
    have hx_zero : (I • (⊤ : Submodule R (Fin m → R))).mkQ x.1 = 0 := by
      -- A kernel vector reduces to zero because `u` is the identity on the quotient.
      calc
        (I • (⊤ : Submodule R (Fin m → R))).mkQ x.1 =
            u.quotientMapByIdeal I ((I • (⊤ : Submodule R (Fin m → R))).mkQ x.1) := by
              simpa [hu]
        _ = (I • (⊤ : Submodule R (Fin m → R))).mkQ (u x.1) := by
              rw [quotientMapByIdeal_apply_mkQ]
        _ = 0 := by simpa [x.2]
    have hx_mem : x.1 ∈ I • (⊤ : Submodule R (Fin m → R)) :=
      (Submodule.Quotient.mk_eq_zero _).1 hx_zero
    have hx_map :
        x.1 ∈
          Submodule.map (LinearMap.ker u).subtype
            (I • (⊤ : Submodule R (LinearMap.ker u))) := by
      -- The splitting corrects an ambient `I`-multiple back into `I • ker u`.
      simpa [x.2] using
        sub_section_mem_map_smul_top_ker_of_rightInverse
          (I := I) u v huv (z := x.1) hx_mem
    rcases hx_map with ⟨y, hyI, hyval⟩
    have hyx : y = x := by
      apply Subtype.ext
      simpa using hyval
    simpa [hyx] using hyI
  let eProd : ((LinearMap.ker u) × (Fin m → R)) ≃ₗ[R] (Fin m → R) :=
    kernel_prod_equiv_of_rightInverse u v huv
  letI : Module.Finite R ((LinearMap.ker u) × (Fin m → R)) := Module.Finite.equiv eProd.symm
  letI : Module.Finite R (LinearMap.ker u) :=
    Module.Finite.of_surjective (LinearMap.fst R (LinearMap.ker u) (Fin m → R))
      (fun x ↦ ⟨(x, 0), rfl⟩)
  have htop_bot :
      (⊤ : Submodule R (LinearMap.ker u)) = ⊥ := by
    have htop :
        (⊤ : Submodule R (LinearMap.ker u)) ≤ Ring.jacobson R •
          (⊤ : Submodule R (LinearMap.ker u)) :=
      le_trans htop_I (Submodule.smul_mono hI le_rfl)
    exact Submodule.FG.eq_bot_of_le_jacobson_smul Module.Finite.fg_top htop
  have hker_subsingleton : Subsingleton (LinearMap.ker u) := by
    refine ⟨fun a b ↦ ?_⟩
    have ha0 : a = 0 := by
      have ha_bot : a ∈ (⊥ : Submodule R (LinearMap.ker u)) := by
        simpa [htop_bot] using (show a ∈ (⊤ : Submodule R (LinearMap.ker u)) from by simp)
      simpa using ha_bot
    have hb0 : b = 0 := by
      have hb_bot : b ∈ (⊥ : Submodule R (LinearMap.ker u)) := by
        simpa [htop_bot] using (show b ∈ (⊤ : Submodule R (LinearMap.ker u)) from by simp)
      simpa using hb_bot
    simpa [ha0, hb0]
  have hker_bot : LinearMap.ker u = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx' : x ∈ LinearMap.ker u := by
      simpa using hx
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx'⟩ : LinearMap.ker u) 0)
  have hinj : Function.Injective u := (LinearMap.ker_eq_bot).1 hker_bot
  have hvu : v.comp u = LinearMap.id := by
    -- Injectivity of `u` upgrades the chosen right inverse to a two-sided inverse.
    apply DFunLike.ext
    intro x
    apply hinj
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : (Fin m → R) →ₗ[R] (Fin m → R) => f (u x)) huv
  exact ⟨v, huv, hvu⟩

namespace Module

/-- Helper for Lemma 15.3.3: stable freeness transports across linear equivalences. -/
theorem StablyFree.of_linearEquiv
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [Module.StablyFree R N] :
    Module.StablyFree R M := by
  rcases Module.StablyFree.exists_free (R := R) (M := N) with
    ⟨F, _instAddCommGroupF, _instModuleF, _instFreeF, hstab⟩
  rcases hstab with ⟨m, n, ⟨w⟩⟩
  -- Precompose the chosen stabilization witness with `e` on the left factor.
  refine ⟨F, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨m, n, ?_⟩
  exact ⟨(LinearEquiv.prodCongr e (LinearEquiv.refl R (Fin m → R))).trans w⟩

end Module

/-- Helper for Lemma 15.3.3: an `R`-linear equivalence between genuine quotient modules respects
the quotient scalar action. -/
theorem linearEquivOverQuotientOfRestrictScalars_map_smul
    {M N : Type*}
    [AddCommGroup M] [Module (R ⧸ I) M] [Module R M] [IsScalarTower R (R ⧸ I) M]
    [AddCommGroup N] [Module (R ⧸ I) N] [Module R N] [IsScalarTower R (R ⧸ I) N]
    (e : M ≃ₗ[R] N) (a : R ⧸ I) (x : M) :
    e (a • x) = a • e x := by
  -- Reduce the quotient scalar to a representative in `R`, then reuse `R`-linearity of `e`.
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) a
  have hr : ((Ideal.Quotient.mk I) r : R ⧸ I) = r • (1 : R ⧸ I) := by
    change ((Ideal.Quotient.mk I) r : R ⧸ I) = ((Ideal.Quotient.mk I) r : R ⧸ I) * 1
    simpa using (mul_one ((Ideal.Quotient.mk I) r)).symm
  have hx : ((Ideal.Quotient.mk I) r : R ⧸ I) • x = r • x := by
    rw [hr]
    simpa [smul_assoc]
  have hy : ((Ideal.Quotient.mk I) r : R ⧸ I) • e x = r • e x := by
    rw [hr]
    simpa [smul_assoc]
  rw [hx, hy]
  simpa using e.map_smul r x

noncomputable def linearEquivOverQuotientOfRestrictScalars
    {M N : Type*}
    [AddCommGroup M] [Module (R ⧸ I) M] [Module R M] [IsScalarTower R (R ⧸ I) M]
    [AddCommGroup N] [Module (R ⧸ I) N] [Module R N] [IsScalarTower R (R ⧸ I) N]
    (e : M ≃ₗ[R] N) :
    M ≃ₗ[R ⧸ I] N :=
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := linearEquivOverQuotientOfRestrictScalars_map_smul (I := I) e }

/-- Helper for Lemma 15.3.3: an ambient linear equivalence induces an equivalence on the quotients
by `IM` and `IN`. -/
noncomputable def quotientByIdealTopLinearEquiv
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (N ⧸ I • (⊤ : Submodule R N)) :=
  let hForward :
      I • (⊤ : Submodule R M) ≤
        Submodule.comap e.toLinearMap (I • (⊤ : Submodule R N)) := by
    -- Transport each `I`-multiple across `e` by linearity.
    rw [Submodule.smul_le]
    intro r hr y hy
    simpa using
      (Submodule.smul_mem_smul hr (show e y ∈ (⊤ : Submodule R N) by simp))
  let hBackward :
      I • (⊤ : Submodule R N) ≤
        Submodule.comap e.symm.toLinearMap (I • (⊤ : Submodule R M)) := by
    -- The inverse equivalence transports the quotient denominator back in the same way.
    rw [Submodule.smul_le]
    intro r hr y hy
    simpa using
      (Submodule.smul_mem_smul hr (show e.symm y ∈ (⊤ : Submodule R M) by simp))
  let f :
      (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] (N ⧸ I • (⊤ : Submodule R N)) :=
    Submodule.mapQ
      (I • (⊤ : Submodule R M))
      (I • (⊤ : Submodule R N))
      e.toLinearMap
      hForward
  let g :
      (N ⧸ I • (⊤ : Submodule R N)) →ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) :=
    Submodule.mapQ
      (I • (⊤ : Submodule R N))
      (I • (⊤ : Submodule R M))
      e.symm.toLinearMap
      hBackward
  -- Check the two composites on quotient generators and cancel the ambient equivalence.
  LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change f (g (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
      have hgx :
          g (Submodule.Quotient.mk x) =
            (Submodule.Quotient.mk (e.symm x) : M ⧸ I • (⊤ : Submodule R M)) := by
        simpa [g] using
          DFunLike.congr_fun
            (Submodule.mapQ_mkQ
              (I • (⊤ : Submodule R N))
              (I • (⊤ : Submodule R M))
              e.symm.toLinearMap)
            x
      have hfg :
          f (Submodule.Quotient.mk (e.symm x) : M ⧸ I • (⊤ : Submodule R M)) =
            (Submodule.Quotient.mk (e (e.symm x)) : N ⧸ I • (⊤ : Submodule R N)) := by
        simpa [f] using
          DFunLike.congr_fun
            (Submodule.mapQ_mkQ
              (I • (⊤ : Submodule R M))
              (I • (⊤ : Submodule R N))
              e.toLinearMap)
            (e.symm x)
      rw [hgx, hfg]
      simp)
    (by
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change g (f (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
      have hfx :
          f (Submodule.Quotient.mk x) =
            (Submodule.Quotient.mk (e x) : N ⧸ I • (⊤ : Submodule R N)) := by
        simpa [f] using
          DFunLike.congr_fun
            (Submodule.mapQ_mkQ
              (I • (⊤ : Submodule R M))
              (I • (⊤ : Submodule R N))
              e.toLinearMap)
            x
      have hgf :
          g (Submodule.Quotient.mk (e x) : N ⧸ I • (⊤ : Submodule R N)) =
            (Submodule.Quotient.mk (e.symm (e x)) : M ⧸ I • (⊤ : Submodule R M)) := by
        simpa [g] using
          DFunLike.congr_fun
            (Submodule.mapQ_mkQ
              (I • (⊤ : Submodule R N))
              (I • (⊤ : Submodule R M))
              e.symm.toLinearMap)
            (e x)
      rw [hfx, hgf]
      simp)

/-- Helper for Lemma 15.3.3: quotient transport along an ambient linear equivalence is also
`R ⧸ I`-linear on the quotient modules. -/
noncomputable def quotientByIdealTopLinearEquiv_over_quotient
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R ⧸ I] (N ⧸ I • (⊤ : Submodule R N)) :=
  linearEquivOverQuotientOfRestrictScalars (I := I) (quotientByIdealTopLinearEquiv (I := I) e)

/-- Helper for Lemma 15.3.3: a vector in the conjugated kernel maps to the kernel of the original
quotient-side projection. -/
theorem mem_restrictScalars_ker_of_mem_free_pi_conjugated_kernel
    {m n : ℕ}
    (q0 : (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I))
    (x : LinearMap.ker
      (((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap).comp
        ((LinearMap.restrictScalars R q0).comp
          (free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap))) :
    (free_pi_quotient_equiv (R := R) (I := I) n x.1) ∈
      Submodule.restrictScalars R (LinearMap.ker q0) := by
  -- Apply injectivity of the target equivalence to strip off the outer conjugation.
  change (LinearMap.restrictScalars R q0)
      ((free_pi_quotient_equiv (R := R) (I := I) n) x.1) = 0
  have hx :
      ((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap)
        ((LinearMap.restrictScalars R q0)
          ((free_pi_quotient_equiv (R := R) (I := I) n) x.1)) = 0 := by
    simpa [LinearMap.comp_apply] using x.2
  have hx' :
      ((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap)
        ((LinearMap.restrictScalars R q0)
          ((free_pi_quotient_equiv (R := R) (I := I) n) x.1)) =
        (free_pi_quotient_equiv (R := R) (I := I) m).symm 0 := by
    simpa using hx
  exact (free_pi_quotient_equiv (R := R) (I := I) m).symm.injective hx'

/-- Helper for Lemma 15.3.3: a vector in the original quotient-side kernel maps back to the
conjugated kernel. -/
theorem mem_free_pi_conjugated_kernel_of_mem_restrictScalars_ker
    {m n : ℕ}
    (q0 : (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I))
    (y : Submodule.restrictScalars R (LinearMap.ker q0)) :
    (free_pi_quotient_equiv (R := R) (I := I) n).symm y.1 ∈
      LinearMap.ker
        (((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap).comp
          ((LinearMap.restrictScalars R q0).comp
            (free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap)) := by
  -- Rewrite through the inverse equivalence on the domain and use the kernel condition on `y`.
  change
    ((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap)
      ((LinearMap.restrictScalars R q0)
        ((free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap
          ((free_pi_quotient_equiv (R := R) (I := I) n).symm y.1))) = 0
  have hy : (LinearMap.restrictScalars R q0) y.1 = 0 := y.2
  simpa [LinearMap.comp_apply, hy]

/-- Helper for Lemma 15.3.3: the forward map for the conjugated-kernel equivalence applies the
free quotient equivalence on the domain side. -/
noncomputable def kernel_free_pi_conjugated_projection_forward
    {m n : ℕ}
    (q0 : (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I)) :
    LinearMap.ker
        (((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap).comp
          ((LinearMap.restrictScalars R q0).comp
            (free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap)) →ₗ[R]
      Submodule.restrictScalars R (LinearMap.ker q0) :=
  LinearMap.codRestrict
    (Submodule.restrictScalars R (LinearMap.ker q0))
    ((free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap.comp
      (LinearMap.ker
        (((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap).comp
          ((LinearMap.restrictScalars R q0).comp
            (free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap))).subtype)
    (mem_restrictScalars_ker_of_mem_free_pi_conjugated_kernel (R := R) (I := I) q0)

/-- Helper for Lemma 15.3.3: the backward map for the conjugated-kernel equivalence applies the
inverse free quotient equivalence on the domain side. -/
noncomputable def kernel_free_pi_conjugated_projection_backward
    {m n : ℕ}
    (q0 : (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I)) :
    Submodule.restrictScalars R (LinearMap.ker q0) →ₗ[R]
      LinearMap.ker
        (((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap).comp
          ((LinearMap.restrictScalars R q0).comp
            (free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap)) :=
  LinearMap.codRestrict
    (LinearMap.ker
      (((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap).comp
        ((LinearMap.restrictScalars R q0).comp
          (free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap)))
    ((free_pi_quotient_equiv (R := R) (I := I) n).symm.toLinearMap.comp
      (Submodule.restrictScalars R (LinearMap.ker q0)).subtype)
    (mem_free_pi_conjugated_kernel_of_mem_restrictScalars_ker (R := R) (I := I) q0)

/-- Helper for Lemma 15.3.3: the forward and backward conjugated-kernel maps are inverse on the
quotient-side kernel. -/
theorem kernel_free_pi_conjugated_projection_forward_comp_backward
    {m n : ℕ}
    (q0 : (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I)) :
    (kernel_free_pi_conjugated_projection_forward (R := R) (I := I) q0).comp
        (kernel_free_pi_conjugated_projection_backward (R := R) (I := I) q0) =
      LinearMap.id := by
  -- The domain-side quotient equivalence cancels with its inverse.
  apply DFunLike.ext
  intro y
  apply Subtype.ext
  simp [kernel_free_pi_conjugated_projection_forward,
    kernel_free_pi_conjugated_projection_backward, LinearMap.comp_apply]

/-- Helper for Lemma 15.3.3: the forward and backward conjugated-kernel maps are inverse on the
conjugated kernel. -/
theorem kernel_free_pi_conjugated_projection_backward_comp_forward
    {m n : ℕ}
    (q0 : (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I)) :
    (kernel_free_pi_conjugated_projection_backward (R := R) (I := I) q0).comp
        (kernel_free_pi_conjugated_projection_forward (R := R) (I := I) q0) =
      LinearMap.id := by
  -- The same cancellation proves the other composite is the identity on the conjugated kernel.
  apply DFunLike.ext
  intro x
  apply Subtype.ext
  simp [kernel_free_pi_conjugated_projection_forward,
    kernel_free_pi_conjugated_projection_backward, LinearMap.comp_apply]

/-- Helper for Lemma 15.3.3: conjugating a quotient-side projection through
`free_pi_quotient_equiv` identifies its kernel with the kernel of the original projection after
restricting scalars. -/
noncomputable def kernel_free_pi_conjugated_projection_equiv
    {m n : ℕ}
    (q0 : (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I)) :
    LinearMap.ker
        (((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap).comp
          ((LinearMap.restrictScalars R q0).comp
            (free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap)) ≃ₗ[R]
      Submodule.restrictScalars R (LinearMap.ker q0) :=
  LinearEquiv.ofLinear
    (kernel_free_pi_conjugated_projection_forward (R := R) (I := I) q0)
    (kernel_free_pi_conjugated_projection_backward (R := R) (I := I) q0)
    (kernel_free_pi_conjugated_projection_forward_comp_backward (R := R) (I := I) q0)
    (kernel_free_pi_conjugated_projection_backward_comp_forward (R := R) (I := I) q0)

/-- Helper for Lemma 15.3.3: the corrected lifted kernel quotient identifies with the original
quotient-side kernel, and hence with the left summand `E` of the chosen stabilization. -/
theorem quotient_kernel_equiv_left_of_stabilization
    {m n : ℕ}
    (e0 : (E × (Fin m → R ⧸ I)) ≃ₗ[R ⧸ I] (Fin n → R ⧸ I))
    (q : (Fin n → R) →ₗ[R] (Fin m → R))
    (s : (Fin m → R) →ₗ[R] (Fin n → R))
    (qbar0 :
      ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
        ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))))
    (hs : q.comp s = LinearMap.id)
    (hq : q.quotientMapByIdeal I = qbar0)
    (hqbar0 :
      qbar0 =
        (((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap).comp
          ((LinearMap.restrictScalars R
              ((LinearMap.snd (R := R ⧸ I) E (Fin m → R ⧸ I)).comp e0.symm.toLinearMap)).comp
            (free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap))) :
    Nonempty
      (((LinearMap.ker q) ⧸ (I • (⊤ : Submodule R (LinearMap.ker q)))) ≃ₗ[R ⧸ I] E) := by
  let q0 :
      (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I) :=
    (LinearMap.snd (R := R ⧸ I) E (Fin m → R ⧸ I)).comp e0.symm.toLinearMap
  let eKernelQuot :
      ((LinearMap.ker q) ⧸ (I • (⊤ : Submodule R (LinearMap.ker q)))) ≃ₗ[R]
        LinearMap.ker qbar0 :=
    kernel_quotient_equiv_of_split_reduction (I := I) q s qbar0 hs hq
  have hkerq :
      LinearMap.ker qbar0 =
        LinearMap.ker
          (((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap).comp
            ((LinearMap.restrictScalars R q0).comp
              (free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap)) := by
    rw [hqbar0]
  have eConj :
      LinearMap.ker qbar0 ≃ₗ[R] Submodule.restrictScalars R (LinearMap.ker q0) := by
    -- Rewrite the reduced projection to the conjugated free one, then invoke the explicit kernel
    -- transport equivalence.
    exact (LinearEquiv.ofEq _ _ hkerq).trans
      (kernel_free_pi_conjugated_projection_equiv (R := R) (I := I) q0)
  have eRestricted :
      ((LinearMap.ker q) ⧸ (I • (⊤ : Submodule R (LinearMap.ker q)))) ≃ₗ[R]
        LinearMap.ker q0 := by
    -- The restricted-scalar kernel and the quotient-side kernel have the same underlying carrier.
    simpa [q0] using eKernelQuot.trans eConj
  have eOverQuotient :
      ((LinearMap.ker q) ⧸ (I • (⊤ : Submodule R (LinearMap.ker q)))) ≃ₗ[R ⧸ I]
        LinearMap.ker q0 :=
    linearEquivOverQuotientOfRestrictScalars (I := I) eRestricted
  rcases ker_stabilized_projection_equiv_left (I := I) (E := E) e0 with ⟨eLeft⟩
  exact ⟨eOverQuotient.trans eLeft⟩

/-- Helper for Lemma 15.3.3: the kernel of a split surjection between finite free modules is
finite stably free. -/
theorem finiteStablyFree_ker_of_split_surjection_fin
    {m n : ℕ}
    (q : (Fin n → R) →ₗ[R] (Fin m → R))
    (s : (Fin m → R) →ₗ[R] (Fin n → R))
    (hs : q.comp s = LinearMap.id) :
    Module.Finite R (LinearMap.ker q) ∧ Module.StablyFree R (LinearMap.ker q) := by
  let K : Submodule R (Fin n → R) := LinearMap.ker q
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk K.subtype q (by
      apply DFunLike.ext
      intro x
      simpa [K] using x.2)
  letI : Module.Finite R S.X₂ := by
    change Module.Finite R (Fin n → R)
    infer_instance
  letI : Module.StablyFree R S.X₂ := by
    change Module.StablyFree R (Fin n → R)
    infer_instance
  letI : Module.Finite R S.X₃ := by
    change Module.Finite R (Fin m → R)
    infer_instance
  letI : Module.StablyFree R S.X₃ := by
    change Module.StablyFree R (Fin m → R)
    infer_instance
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · -- The left map is the kernel inclusion, so exactness is the standard kernel exactness fact.
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [S, K] using (LinearMap.exact_subtype_ker_map q)
    · exact (ModuleCat.mono_iff_injective _).2 K.injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).2 (by
        intro y
        refine ⟨s y, ?_⟩
        simpa [LinearMap.comp_apply] using congrArg (fun f : (Fin m → R) →ₗ[R] (Fin m → R) => f y) hs)
  simpa [S] using CategoryTheory.ShortComplex.finiteStablyFree_X₁_of_shortExact
    (R := R) (S := S) hS

/- Domain-style sampling:
- primary domain: Jacobson-radical lifting of finite stably free modules across a quotient ring;
- sampled owner declarations of the same kind:
  `Module.StablyFree`,
  `Module.Finite`,
  `Ring.jacobson`,
  `ModuleCat.finiteStablyFree_X₂_of_shortExact`;
- best owner abstraction: this item is source-facing existence data built from the canonical owners
  `Module.StablyFree` and `Module.Finite`, together with the standard quotient module
  `M ⧸ (I • (⊤ : Submodule R M))`;
- primitive vs. derived: the primitive witness is the lifted `R`-module together with the quotient
  equivalence to `E`, while finiteness and stable freeness are derived owner properties of that
  witness and should not be existentially packaged as separate primitive fields.

Layer classification:
- `source-facing`: the lifting statement below;
- `core/canonical`: `Module.StablyFree`, `Module.Finite`, and the Jacobson-radical containment
  `I ≤ Ring.jacobson R`;
- `bridge/view`: the quotient module `M ⧸ (I • (⊤ : Submodule R M))` over `R ⧸ I`.
-/

-- Proof sketch: choose a stable trivialization
-- `E × (Fin n → R ⧸ I) ≃ₗ[R ⧸ I] (Fin m → R ⧸ I)`. Lift the associated projection and section to
-- `R`-linear maps between `Fin m → R` and `Fin n → R`, use the Jacobson-radical hypothesis to make
-- the lifted endomorphism of `Fin n → R` invertible, and identify the kernel of the lifted
-- projection as a finite stably free `R`-module whose quotient modulo `I` recovers `E`.
/-- Lemma 15.3.3: if `I` is contained in the Jacobson radical of `R`, then every finite stably
free `R ⧸ I`-module lifts to a finite stably free `R`-module. -/
@[stacks 0BC5]
theorem exists_finiteStablyFree_lift_of_le_ring_jacobson
    [Module.Finite (R ⧸ I) E] [Module.StablyFree (R ⧸ I) E] (hI : I ≤ Ring.jacobson R) :
    ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module R M)
      (e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] E),
      Module.Finite R M ∧ Module.StablyFree R M := by
  -- Route correction: keep the stabilized-kernel/Jacobson argument and only replace the final
  -- universe packaging by the canonical `Module.Finite.small` plus `Shrink.linearEquiv` transport.
  rcases CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization
      (R := R ⧸ I) (M := E) with ⟨m, n, ⟨e0⟩⟩
  let q0 : (Fin n → R ⧸ I) →ₗ[R ⧸ I] (Fin m → R ⧸ I) :=
    (LinearMap.snd (R := R ⧸ I) E (Fin m → R ⧸ I)).comp e0.symm.toLinearMap
  let qbar0 :
      ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
        ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))) :=
    (((free_pi_quotient_equiv (R := R) (I := I) m).symm.toLinearMap).comp
      ((LinearMap.restrictScalars R q0).comp
        (free_pi_quotient_equiv (R := R) (I := I) n).toLinearMap))
  -- Lift the stabilized quotient-side projection to an `R`-linear map on the finite free modules.
  obtain ⟨q, hq⟩ :=
    exists_lift_with_prescribed_quotientMapByIdeal
      (R := R) (I := I) (Q := Fin n → R) (M := Fin m → R) qbar0
  let s0 : (Fin m → R ⧸ I) →ₗ[R ⧸ I] (Fin n → R ⧸ I) :=
    e0.toLinearMap.comp (LinearMap.inr (R := R ⧸ I) E (Fin m → R ⧸ I))
  let sbar0 :
      ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))) →ₗ[R]
        ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) :=
    (((free_pi_quotient_equiv (R := R) (I := I) n).symm.toLinearMap).comp
      ((LinearMap.restrictScalars R s0).comp
        (free_pi_quotient_equiv (R := R) (I := I) m).toLinearMap))
  -- Lift the quotient-side section as well so the reduction of `q.comp s` is still the identity.
  obtain ⟨s, hs⟩ :=
    exists_lift_with_prescribed_quotientMapByIdeal
      (R := R) (I := I) (Q := Fin m → R) (M := Fin n → R) sbar0
  have hq0s0 : q0.comp s0 = LinearMap.id := by
    -- The original stabilization identifies `q0` as the second projection with section `s0`.
    simpa [q0, s0] using stabilized_projection_section_rightInverse (R := R) (I := I) (E := E) e0
  let en : ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) ≃ₗ[R] (Fin n → R ⧸ I) :=
    free_pi_quotient_equiv (R := R) (I := I) n
  let em : ((Fin m → R) ⧸ (I • (⊤ : Submodule R (Fin m → R)))) ≃ₗ[R] (Fin m → R ⧸ I) :=
    free_pi_quotient_equiv (R := R) (I := I) m
  have hen : en.toLinearMap.comp en.symm.toLinearMap = LinearMap.id := by
    -- The quotient equivalence cancels with its inverse on the source free block.
    ext x
    simp [en]
  have hem : em.symm.toLinearMap.comp em.toLinearMap = LinearMap.id := by
    -- The same cancellation holds on the target free block.
    ext x
    simp [em]
  have hrestrict : (LinearMap.restrictScalars R q0).comp (LinearMap.restrictScalars R s0) =
      LinearMap.id := by
    -- Restricting scalars preserves the stabilized section identity.
    apply LinearMap.ext
    intro x
    simpa [LinearMap.comp_apply] using congrArg (fun f : (Fin m → R ⧸ I) →ₗ[R ⧸ I]
      (Fin m → R ⧸ I) => f x) hq0s0
  have hqbar0sbar0 : qbar0.comp sbar0 = LinearMap.id := by
    -- Conjugating the stabilized section identity through the free quotient equivalences keeps
    -- the composite equal to the identity.
    calc
      qbar0.comp sbar0 =
          em.symm.toLinearMap.comp
            (((LinearMap.restrictScalars R q0).comp (LinearMap.restrictScalars R s0)).comp
              em.toLinearMap) := by
            simp [qbar0, sbar0, en, em, LinearMap.comp_assoc, hen]
      _ = em.symm.toLinearMap.comp (LinearMap.id.comp em.toLinearMap) := by
            rw [hrestrict]
      _ = LinearMap.id := by
            simp [em, hem, LinearMap.comp_assoc]
  have hu : (q.comp s).quotientMapByIdeal I = LinearMap.id := by
    -- Reduce the lifted composite modulo `I` and rewrite it by the conjugated quotient identity.
    calc
      (q.comp s).quotientMapByIdeal I = qbar0.comp sbar0 := by
        rw [quotientMapByIdeal_comp, hq, hs]
      _ = LinearMap.id := hqbar0sbar0
  obtain ⟨v, huv, hvu⟩ :=
    exists_linear_inverse_of_reduction_eq_id_pi_of_le_jacobson
      (R := R) (I := I) m (q.comp s) hu hI
  have hcorrected :
      ((v.comp q).comp s = LinearMap.id) ∧
        (v.comp q).quotientMapByIdeal I = qbar0 := by
    -- Correct the lifted projection by the inverse on the free summand without changing reduction.
    exact corrected_projection_data (R := R) (I := I) q s qbar0 v hq hu huv hvu
  let q' : (Fin n → R) →ₗ[R] (Fin m → R) := v.comp q
  have hq's : q'.comp s = LinearMap.id := by
    -- The corrected projection now splits against the chosen lift of the section.
    simpa [q'] using hcorrected.1
  have hq' : q'.quotientMapByIdeal I = qbar0 := by
    -- The Jacobson correction is invisible modulo `I`.
    simpa [q'] using hcorrected.2
  let K := LinearMap.ker q'
  have hK :
      Module.Finite R K ∧ Module.StablyFree R K := by
    -- A kernel of a split surjection between finite free modules is finite stably free.
    simpa [K] using finiteStablyFree_ker_of_split_surjection_fin (R := R) q' s hq's
  letI : Module.Finite R K := hK.1
  letI : Module.StablyFree R K := hK.2
  obtain ⟨eK⟩ :=
    quotient_kernel_equiv_left_of_stabilization
      (R := R) (I := I) (E := E) e0 q' s qbar0 hq's hq' rfl
  have hsmallR : Small.{max u v} R := by
    let _ : Small.{u} R := small_self R
    exact small_lift.{u, v, u} R
  letI : Small.{max u v} R := hsmallR
  have hsmallK : Small.{max u v} K := by
    exact Module.Finite.small.{max u v, u, u} (R := R) (M := K)
  letI : Small.{max u v} K := hsmallK
  let eShrink : Shrink.{max u v} K ≃ₗ[R] K := Shrink.linearEquiv R K
  letI : Module.Finite R (Shrink.{max u v} K) := Module.Finite.equiv eShrink.symm
  have hShrinkStabilization :
      ∃ m n : ℕ, Nonempty (((Shrink.{max u v} K) × (Fin m → R)) ≃ₗ[R] (Fin n → R)) := by
    -- Move the finite-rank stabilization witness for `K` across the shrink equivalence.
    have hKStabilization :
        ∃ m n : ℕ, Nonempty ((K × (Fin m → R)) ≃ₗ[R] (Fin n → R)) :=
      CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := R) (M := K)
    exact CategoryTheory.ShortComplex.fin_stabilization_of_equiv
      (R := R) (M := Shrink.{max u v} K) (N := K) eShrink hKStabilization
  letI : Module.StablyFree R (Shrink.{max u v} K) :=
    CategoryTheory.ShortComplex.stablyFree_of_fin_stabilization
      (R := R) (M := Shrink.{max u v} K) hShrinkStabilization
  let eShrinkQuot :
      (Shrink.{max u v} K ⧸ (I • (⊤ : Submodule R (Shrink.{max u v} K)))) ≃ₗ[R ⧸ I]
        (K ⧸ (I • (⊤ : Submodule R K))) :=
    quotientByIdealTopLinearEquiv_over_quotient (R := R) (I := I) eShrink
  -- Package the corrected kernel in the target universe and transport the quotient identification.
  refine ⟨Shrink.{max u v} K, inferInstance, inferInstance, eShrinkQuot.trans eK, ?_⟩
  exact ⟨inferInstance, inferInstance⟩

end
