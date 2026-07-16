import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_157_1
import stacks_proof.stacks_project.Chap10.Definition_10_72_1
import stacks_proof.stacks_project.Chap10.Lemma_10_39_12
import stacks_proof.stacks_project.Chap10.Lemma_10_72_5
import stacks_proof.stacks_project.Chap10.Lemma_10_72_7
import stacks_proof.stacks_project.Chap10.Lemma_10_99_1
import stacks_proof.stacks_project.Chap10.Lemma_10_99_4
import stacks_proof.stacks_project.Chap10.Lemma_10_63_18

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open RingTheory Sequence Ideal IsLocalRing
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct Pointwise

universe u v w x uA uP

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] N

/- Domain-style sampling pass:
* primary domain: local commutative algebra of depth for finite modules under flat local base
  change, with the closed fiber carried by the canonical fiber-ring owner;
* sampled owner declarations:
  `moduleDepth`,
  `Ideal.Fiber`,
  `Module.Finite.base_change`,
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`;
* best owner abstraction: the right-hand side belongs on the canonical local depth
  `moduleDepth ClosedFiber ClosedFiberModule`, where
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and
  `ClosedFiberModule = ClosedFiber ⊗[S] N`; the quotient module
  `N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))` is only a bridge.

Primitive data vs. derived API:
* primitive data: the local flat map `R → S`, the finite `R`-module `M`, and the finite
  `S`-module `N` that is flat over `R`;
* derived API: the quotient presentation of the closed fiber and of the closed-fiber module.

Source/core/bridge triage:
* `source-facing`: the Stacks additivity formula for depth under flat local base change;
* `core/canonical`: `moduleDepth` on the owner ring/module pair `ClosedFiber` and
  `ClosedFiberModule`;
* `bridge/view`: the quotient presentation `S ⧸ 𝔪S` and
  `N ⧸ (𝔪S • (⊤ : Submodule S N))`.
-/

/-- Helper for Lemma 10.163.1: the canonical closed fiber is the quotient `S / 𝔪_R S`. -/
noncomputable def closedFiberQuotEquiv : ClosedFiber ≃ₐ[R] S ⧸ 𝔪S :=
  (Algebra.TensorProduct.congr (.symm <| .ofBijective _
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)

/-- Helper for Lemma 10.163.1: the canonical quotient comparison from `Lemma 10.99.4` sends
`1 ⊗ n` to the quotient class of `n`. -/
@[simp] lemma closed_fiber_module_quotient_equiv_apply_one_tmul (n : N) :
    letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
      (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
    letI : Module ClosedFiber (N ⧸ (𝔪S • (⊤ : Submodule S N))) :=
      Module.compHom (N ⧸ (𝔪S • (⊤ : Submodule S N))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
    closed_fiber_module_quotient_equiv (R := R) (S := S) (M := N)
      ((1 : ClosedFiber) ⊗ₜ[S] n) =
        (Submodule.Quotient.mk n : N ⧸ (𝔪S • (⊤ : Submodule S N))) := by
  -- Route correction: the earlier file-local owner-change package duplicated `Lemma 10.99.4`.
  -- The stable route is to unfold the canonical imported bridge once and simplify its action on
  -- the pure tensor `1 ⊗ n`.
  -- Proof comment: the imported equivalence is a composition of the left-factor quotient rewrite
  -- with the standard tensor/quotient equivalence, so `simp` reduces the pure tensor directly.
  dsimp [closed_fiber_module_quotient_equiv]
  simp [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]

/-- Helper for Lemma 10.163.1: the inverse quotient comparison from `Lemma 10.99.4` also fixes
quotient representatives. -/
@[simp] lemma map_maximalIdeal_quotient_equiv_symm_apply_mk (n : N) :
    (map_maximalIdeal_quotient_equiv (R := R) (S := S) N).symm (Submodule.Quotient.mk n) =
      (Submodule.Quotient.mk n : N ⧸ (𝔪S • (⊤ : Submodule S N))) := by
  -- Proof comment: the forward quotient comparison already fixes representatives, so injectivity
  -- of the equivalence forces the inverse to do the same.
  apply (map_maximalIdeal_quotient_equiv (R := R) (S := S) N).injective
  simp

/-- The canonical closed fiber `ClosedFiber = (maximalIdeal R).Fiber S` is a local ring. -/
instance closedFiber_isLocalRing : IsLocalRing ClosedFiber := by
  -- Proof comment: transfer the local-ring structure across the quotient presentation
  -- `ClosedFiber ≃ S ⧸ 𝔪_R S`.
  letI : IsLocalRing (S ⧸ 𝔪S) := by
    have h𝔪S : 𝔪S < (⊤ : Ideal S) :=
      IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)
    have : Nontrivial (S ⧸ 𝔪S) :=
      Quotient.nontrivial_iff.mpr h𝔪S.ne
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔪S) Ideal.Quotient.mk_surjective
  exact (closedFiberQuotEquiv (R := R) (S := S)).toRingEquiv.symm.isLocalRing

/-- The canonical closed fiber inherits Noetherianity from its quotient presentation
`S ⧸ 𝔪_R S`. -/
instance closedFiber_isNoetherianRing : IsNoetherianRing ClosedFiber :=
  isNoetherianRing_of_ringEquiv (S ⧸ 𝔪S)
    (closedFiberQuotEquiv (R := R) (S := S)).toRingEquiv.symm

/-- The tensor product `N ⊗[R] M`, which represents `M ⊗[R] N` in a form carrying its natural
`S`-module structure, is finite over `S` under the flat local algebra hypotheses. -/
instance : Module.Finite S (N ⊗[R] M) := by
  -- Proof comment: first base change the finite `R`-module `M` to `S`, then tensor over `S`
  -- with the finite `S`-module `N`, and finally transport finiteness back through the standard
  -- base-change comparison.
  let _ : Module.Finite S (S ⊗[R] M) := by infer_instance
  let _ : Module.Finite S ((S ⊗[R] M) ⊗[S] N) := by infer_instance
  let e :
      ((S ⊗[R] M) ⊗[S] N) ≃ₗ[S] (N ⊗[R] M) :=
    (TensorProduct.comm S (S ⊗[R] M) N).trans <|
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N M
  simpa using (Module.Finite.equiv e : Module.Finite S (N ⊗[R] M))

/-- Helper for Lemma 10.163.1: a finite subsingleton module over a Noetherian local ring has
infinite depth. -/
theorem moduleDepth_eq_top_of_subsingleton_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Subsingleton P] :
    moduleDepth A P = ⊤ := by
  -- Proof comment: for a subsingleton module the top submodule is already `⊥`, so `𝔪 P = P`.
  have htop_eq_bot : (⊤ : Submodule A P) = ⊥ := by
    ext p
    simp [Subsingleton.elim p 0]
  have hsmul_bot : maximalIdeal A • (⊥ : Submodule A P) = ⊥ := by
    ext p
    simp
  have hsmul_top : maximalIdeal A • (⊤ : Submodule A P) = ⊤ := by
    rw [htop_eq_bot, hsmul_bot, ← htop_eq_bot]
  change Ideal.depth (maximalIdeal A) P = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (maximalIdeal A) P hsmul_top

/-- Helper for Lemma 10.163.1: depth zero forces a finite module over a Noetherian local ring to
be nontrivial. -/
theorem nontrivial_of_moduleDepth_eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    (hdepth : moduleDepth A P = 0) :
    Nontrivial P := by
  -- Proof comment: a subsingleton module would have infinite depth, contradicting the zero-depth
  -- hypothesis.
  by_contra hP
  letI : Subsingleton P := not_nontrivial_iff_subsingleton.mp hP
  have htop : moduleDepth A P = ⊤ :=
    moduleDepth_eq_top_of_subsingleton_for_entry (A := A) (P := P)
  exact ENat.top_ne_zero <| by simpa [hdepth] using htop

/-- Helper for Lemma 10.163.1: an element killed by the maximal ideal defines the canonical
residue-field line inside the module. -/
noncomputable def residueField_to_module_map_of_annihilated
    {A : Type*} [CommRing A] [IsLocalRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    (p : P) (hpann : ∀ a ∈ maximalIdeal A, a • p = 0) :
    ResidueField A →ₗ[A] P := by
  let z : A →ₗ[A] P :=
    { toFun := fun a => a • p
      map_add' := by
        intro a b
        simp [add_smul]
      map_smul' := by
        intro a b
        simp [smul_smul, mul_comm] }
  have hker : maximalIdeal A ≤ LinearMap.ker z := by
    intro a ha
    exact hpann a ha
  -- Proof comment: the scalar line `A → P`, `a ↦ a • p`, factors through the residue field
  -- because every element of the maximal ideal kills `p`.
  exact (maximalIdeal A).liftQ z hker

/-- Helper for Lemma 10.163.1: the quotient-descended residue-field line sends `1` to the chosen
annihilated element. -/
@[simp] lemma residueField_to_module_map_of_annihilated_apply_one
    {A : Type*} [CommRing A] [IsLocalRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    (p : P) (hpann : ∀ a ∈ maximalIdeal A, a • p = 0) :
    residueField_to_module_map_of_annihilated (A := A) (P := P) p hpann 1 = p := by
  -- Proof comment: `ResidueField A` is definitionally the quotient `A ⧸ maximalIdeal A`, so the
  -- descended map evaluates on `1` by the quotient computation rule for `Submodule.liftQ`.
  let z : A →ₗ[A] P :=
    { toFun := fun a => a • p
      map_add' := by
        intro a b
        simp [add_smul]
      map_smul' := by
        intro a b
        simp [smul_smul] }
  have hker : maximalIdeal A ≤ LinearMap.ker z := by
    intro a ha
    exact hpann a ha
  change (maximalIdeal A).liftQ z hker (Ideal.Quotient.mk (maximalIdeal A) 1) = p
  simpa [z] using (Submodule.liftQ_apply (p := maximalIdeal A) z (x := (1 : A)))

/-- Helper for Lemma 10.163.1: if the chosen element is nonzero, the induced residue-field line is
injective. -/
lemma residueField_to_module_map_of_annihilated_injective
    {A : Type*} [CommRing A] [IsLocalRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    {p : P} (hp : p ≠ 0) (hpann : ∀ a ∈ maximalIdeal A, a • p = 0) :
    Function.Injective (residueField_to_module_map_of_annihilated (A := A) (P := P) p hpann) := by
  -- Proof comment: represent a residue-field class by `a : A`; if its image is zero and `a`
  -- avoids the maximal ideal, then `a` is a unit, so `a • p = 0` forces `p = 0`, contradicting
  -- the chosen nonzero witness.
  intro x y hxy
  have hsub :
      residueField_to_module_map_of_annihilated (A := A) (P := P) p hpann (x - y) = 0 := by
    simpa [map_sub, hxy]
  have hxy_zero : x - y = 0 := by
    obtain ⟨a, haeq⟩ := IsLocalRing.residue_surjective (R := A) (x - y)
    have hsmul : a • p = 0 := by
      have hsub' :
          residueField_to_module_map_of_annihilated (A := A) (P := P) p hpann
            (IsLocalRing.residue A a) = 0 := by
        simpa [haeq] using hsub
      simpa [IsLocalRing.residue, residueField_to_module_map_of_annihilated] using hsub'
    have hres0 : IsLocalRing.residue A a = 0 := by
      by_cases ha : a ∈ maximalIdeal A
      · exact (IsLocalRing.residue_eq_zero_iff (R := A) a).2 ha
      · have hunit : IsUnit a := (IsLocalRing.notMem_maximalIdeal (R := A)).1 ha
        exact False.elim <| hp <| (hunit.smul_eq_zero).1 hsmul
    simpa [haeq] using hres0
  exact sub_eq_zero.mp hxy_zero

/-- Helper for Lemma 10.163.1: depth zero forces the maximal ideal to be associated. -/
lemma maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    (hdepth0 : moduleDepth A P = 0) :
    maximalIdeal A ∈ associatedPrimes A P := by
  have htop :
      maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ := by
    intro htop
    rw [show moduleDepth A P = ⊤ from
          Ideal.depth_eq_top_of_smul_top (maximalIdeal A) P htop] at hdepth0
    simp at hdepth0
  have hnontrivial : Nontrivial P := by
    by_contra hP
    letI : Subsingleton P := not_nontrivial_iff_subsingleton.mp hP
    exact htop <| by
      ext p
      simp [Subsingleton.elim p 0]
  have hno_regular : ¬ ∃ x ∈ maximalIdeal A, IsSMulRegular P x := by
    intro hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    have hdepth_pos : (1 : ℕ∞) ≤ moduleDepth A P := by
      rw [show moduleDepth A P = sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) from
        Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) P htop]
      refine le_sSup ?_
      refine ⟨[x], ?_, ?_, by simp⟩
      · exact RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal P
          (by
            intro r hr
            simpa [List.mem_singleton.mp hr] using hx)
          ((RingTheory.Sequence.isWeaklyRegular_singleton_iff P x).2 hxreg)
      · simpa using hx
    exact (ENat.one_le_iff_ne_zero.1 hdepth_pos) hdepth0
  by_contra hmax
  have hforall :
      ∀ q ∈ associatedPrimes A P, ¬ maximalIdeal A ≤ q := by
    intro q hq hmq
    have hq_le : q ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hq.1.ne_top
    have hq_eq : q = maximalIdeal A := le_antisymm hq_le hmq
    exact hmax (hq_eq ▸ hq)
  exact hno_regular <|
    (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
      (R := A) (M := P) (I := maximalIdeal A)).2 hforall

/-- Helper for Lemma 10.163.1: depth zero yields a nonzero element annihilated by the maximal
ideal. -/
lemma exists_nonzero_annihilated_by_maximalIdeal_of_moduleDepth_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    (hdepth0 : moduleDepth A P = 0) :
    ∃ p : P, p ≠ 0 ∧ ∀ a ∈ maximalIdeal A, a • p = 0 := by
  -- Proof comment: depth zero makes the maximal ideal associated; the associated-prime owner
  -- theorem gives an injective line from the residue field, and evaluating it at `1` produces the
  -- required annihilated nonzero element.
  have hmax : maximalIdeal A ∈ associatedPrimes A P :=
    maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero_for_entry (A := A) hdepth0
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff_exists_injective_linearMap] at hmax
  rcases hmax with ⟨_, f, hf⟩
  refine ⟨f 1, ?_, ?_⟩
  · intro hf1
    have h10 : f (1 : ResidueField A) = f 0 := by simpa [hf1]
    have : (1 : ResidueField A) = 0 := hf h10
    exact one_ne_zero this
  · intro a ha
    -- Proof comment: elements of the maximal ideal act trivially on the residue field, hence on
    -- its image under the injective linear map.
    have hsmul : a • (1 : ResidueField A) = 0 := by
      change IsLocalRing.residue A a * 1 = 0
      rw [(IsLocalRing.residue_eq_zero_iff (R := A) a).2 ha]
      simp
    calc
      a • f 1 = f (a • (1 : ResidueField A)) := by
        exact (f.map_smul a (1 : ResidueField A)).symm
      _ = f 0 := by exact congrArg f hsmul
      _ = 0 := by exact map_zero f

/-- Helper for Lemma 10.163.1: a nonzero element annihilated by the maximal ideal forces depth
zero. -/
lemma moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    (hmax : maximalIdeal A ∈ associatedPrimes A P) :
    moduleDepth A P = 0 := by
  by_cases hsub : Subsingleton P
  · letI : Subsingleton P := hsub
    rw [AssociatedPrimes.mem_iff] at hmax
    exact False.elim (not_isAssociatedPrime_of_subsingleton hmax)
  · letI : Nontrivial P := not_subsingleton_iff_nontrivial.mp hsub
    have hsmul :
        maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ := by
      simpa [ne_comm] using
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A P)))
    rw [show moduleDepth A P = sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) P hsmul]
    apply le_antisymm
    · refine sSup_le ?_
      intro d hd
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      cases rs with
      | nil =>
          simp
      | cons x xs =>
          exfalso
          have hx : x ∈ maximalIdeal A := hmem (Ideal.subset_span (by simp))
          have hxreg : IsSMulRegular P x :=
            ((RingTheory.Sequence.isRegular_cons_iff P x xs).1 hreg).1
          have hx_not_union :
              x ∉ ⋃ p ∈ associatedPrimes A P, (p : Set A) := by
            simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular A P] using hxreg
          exact hx_not_union <|
            Set.mem_iUnion.2 ⟨maximalIdeal A, Set.mem_iUnion.2 ⟨hmax, hx⟩⟩
    · exact bot_le

/-- Helper for Lemma 10.163.1: a nonzero element annihilated by the maximal ideal forces depth
zero. -/
lemma moduleDepth_eq_zero_of_exists_annihilated_by_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    (hann : ∃ p : P, p ≠ 0 ∧ ∀ a ∈ maximalIdeal A, a • p = 0) :
    moduleDepth A P = 0 := by
  -- Proof comment: the annihilated nonzero element defines an injective residue-field line, so
  -- the maximal ideal is associated; the previous helper then converts that associated closed
  -- point into depth zero.
  rcases hann with ⟨p, hp, hpann⟩
  have hmax : maximalIdeal A ∈ associatedPrimes A P := by
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff_exists_injective_linearMap]
    refine ⟨Ideal.IsMaximal.isPrime (IsLocalRing.maximalIdeal.isMaximal A), ?_⟩
    exact ⟨residueField_to_module_map_of_annihilated (A := A) (P := P) p hpann,
      residueField_to_module_map_of_annihilated_injective (A := A) (P := P) hp hpann⟩
  exact
    moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes_for_entry
      (A := A) (P := P) hmax

/-- Helper for Lemma 10.163.1: linear equivalences preserve local module depth. -/
theorem moduleDepth_eq_of_linearEquiv
    {A : Type*} [CommRing A] [IsLocalRing A]
    {P Q : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    (e : P ≃ₗ[A] Q) :
    moduleDepth A P = moduleDepth A Q := by
  -- Proof comment: transport the regular-sequence presentation of depth across the linear
  -- equivalence and compare the `𝔪`-multiple/top branch on both sides.
  have htop :
      maximalIdeal A • (⊤ : Submodule A P) = ⊤ ↔
        maximalIdeal A • (⊤ : Submodule A Q) = ⊤ := by
    constructor
    · intro h
      have hmap := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    · intro h
      have hmap := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap
  by_cases hP : maximalIdeal A • (⊤ : Submodule A P) = ⊤
  · rw [show moduleDepth A P = ⊤ from
          Ideal.depth_eq_top_of_smul_top (maximalIdeal A) P hP,
      show moduleDepth A Q = ⊤ from
          Ideal.depth_eq_top_of_smul_top (maximalIdeal A) Q (htop.mp hP)]
  · rw [show moduleDepth A P =
        sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) P hP,
      show moduleDepth A Q =
        sSup (Ideal.regularSequenceLengths (maximalIdeal A) Q) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) Q (mt htop.mpr hP)]
    apply le_antisymm
    · refine sSup_le ?_
      intro d hd
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      refine le_sSup ?_
      exact ⟨rs, (e.isRegular_congr rs).1 hreg, hmem, rfl⟩
    · refine sSup_le ?_
      intro d hd
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      refine le_sSup ?_
      exact ⟨rs, (e.isRegular_congr rs).2 hreg, hmem, rfl⟩

/-- Helper for Lemma 10.163.1: on the quotient model of the closed-fiber module, the transported
`ClosedFiber`-scalar coming from `s : S` agrees with the original `S`-scalar action. -/
lemma closed_fiber_quotient_smul_eq_source_smul (s : S)
    (q : N ⧸ (𝔪S • (⊤ : Submodule S N))) :
    letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
      (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
    letI : Module ClosedFiber (N ⧸ (𝔪S • (⊤ : Submodule S N))) :=
      Module.compHom (N ⧸ (𝔪S • (⊤ : Submodule S N))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
    ((algebraMap S ClosedFiber s) • q : N ⧸ (𝔪S • (⊤ : Submodule S N))) = s • q := by
  letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
    (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
  letI : Module ClosedFiber (N ⧸ (𝔪S • (⊤ : Submodule S N))) :=
    Module.compHom (N ⧸ (𝔪S • (⊤ : Submodule S N))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
  -- Proof comment: unfold the transported `ClosedFiber`-action to the quotient-ring owner
  -- `S ⧸ 𝔪S`, identify the image of `s`, and then rewrite back to the original quotient action.
  change
    ((algebraMap ClosedFiber (S ⧸ 𝔪S) (algebraMap S ClosedFiber s)) • q :
      N ⧸ (𝔪S • (⊤ : Submodule S N))) = s • q
  rw [show algebraMap ClosedFiber (S ⧸ 𝔪S) (algebraMap S ClosedFiber s) =
      Ideal.Quotient.mk 𝔪S s by
        change
          (closedFiber_quotient_equiv (R := R) (S := S)).symm (algebraMap S ClosedFiber s) =
            Ideal.Quotient.mk 𝔪S s
        simpa using closedFiber_quotient_equiv_symm_algebraMap (R := R) (S := S) s]
  simpa using
    (ideal_scalar_action_eq_quotient_scalar_action
      (R := S) (I := 𝔪S) (N := N ⧸ (𝔪S • (⊤ : Submodule S N))) s q).symm

/-- Helper for Lemma 10.163.1: depth zero on the closed-fiber module yields a nonzero quotient
class killed by every element of `maximalIdeal S`. -/
lemma closed_fiber_quotient_has_maximalIdeal_annihilated_element_of_depth_zero
    (hdepth0 : moduleDepth ClosedFiber ClosedFiberModule = 0) :
    letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
      (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
    letI : Module ClosedFiber (N ⧸ (𝔪S • (⊤ : Submodule S N))) :=
      Module.compHom (N ⧸ (𝔪S • (⊤ : Submodule S N))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
    ∃ q : N ⧸ (𝔪S • (⊤ : Submodule S N)),
      q ≠ 0 ∧ ∀ s ∈ maximalIdeal S, s • q = 0 := by
  letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
    (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
  letI : Module ClosedFiber (N ⧸ (𝔪S • (⊤ : Submodule S N))) :=
    Module.compHom (N ⧸ (𝔪S • (⊤ : Submodule S N))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
  let e := closed_fiber_module_quotient_equiv (R := R) (S := S) (M := N)
  letI : Module.Finite ClosedFiber ClosedFiberModule := by infer_instance
  letI : Module.Finite ClosedFiber (N ⧸ (𝔪S • (⊤ : Submodule S N))) :=
    Module.Finite.equiv e
  have hdepthQ :
      moduleDepth ClosedFiber (N ⧸ (𝔪S • (⊤ : Submodule S N))) = 0 := by
    -- Proof comment: move the depth-zero hypothesis from the canonical owner
    -- `ClosedFiber ⊗[S] N` to the quotient model via the imported linear equivalence.
    simpa [moduleDepth_eq_of_linearEquiv (A := ClosedFiber) (e := e)] using hdepth0
  rcases
      exists_nonzero_annihilated_by_maximalIdeal_of_moduleDepth_zero
        (A := ClosedFiber) (P := N ⧸ (𝔪S • (⊤ : Submodule S N))) hdepthQ with
    ⟨q, hq0, hqann⟩
  refine ⟨q, hq0, ?_⟩
  intro s hs
  -- Proof comment: the algebra map `S → ClosedFiber` is local, so elements of `maximalIdeal S`
  -- land in `maximalIdeal ClosedFiber`; the previous scalar-compatibility lemma then rewrites the
  -- transported annihilation statement back to the original quotient action.
  letI : IsLocalHom (algebraMap S ClosedFiber) :=
    IsLocalHom.of_surjective (algebraMap S ClosedFiber)
      (closedFiber_algebraMap_surjective (R := R) (S := S))
  have hs_closed : algebraMap S ClosedFiber s ∈ maximalIdeal ClosedFiber := by
    refine (IsLocalRing.mem_maximalIdeal _).2 <| mem_nonunits_iff.mpr ?_
    have hs_nonunit : ¬ IsUnit s :=
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal s).1 hs)
    intro hs_unit
    exact hs_nonunit <| IsLocalHom.map_nonunit (f := algebraMap S ClosedFiber) s hs_unit
  have hs_zero : (algebraMap S ClosedFiber s) • q = 0 :=
    hqann (algebraMap S ClosedFiber s) hs_closed
  rw [closed_fiber_quotient_smul_eq_source_smul (R := R) (S := S) (N := N) s q] at hs_zero
  exact hs_zero

/-- Helper for Lemma 10.163.1: the nonzero element `m : M` defines the comparison
`N / 𝔪_R N → N ⊗[R] M` by tensoring with `m`. -/
noncomputable def source_quotient_to_tensor_map (z : ResidueField R →ₗ[R] M) :
    N ⧸ (maximalIdeal R • (⊤ : Submodule R N)) →ₗ[R] N ⊗[R] M :=
  -- Proof comment: rewrite `N / 𝔪_R N` as `κ(R) ⊗[R] N`, tensor the residue-field line
  -- `z : κ(R) → M` on the left factor, and finally commute the tensor factors.
  (TensorProduct.comm R M N).toLinearMap.comp <|
    (z.rTensor N).comp <|
      (TensorProduct.quotTensorEquivQuotSMul N (maximalIdeal R)).symm.toLinearMap

/-- Helper for Lemma 10.163.1: on quotient representatives, the source quotient-to-tensor map
sends `n` to the pure tensor `n ⊗ z(1)`. -/
@[simp] lemma source_quotient_to_tensor_map_apply_mk
    (z : ResidueField R →ₗ[R] M) (n : N) :
    source_quotient_to_tensor_map (R := R) (N := N) (M := M) z (Submodule.Quotient.mk n) =
      n ⊗ₜ[R] z 1 := by
  -- Proof comment: the quotient class of `n` corresponds to `1 ⊗ n` under
  -- `quotTensorEquivQuotSMul`; tensoring with `z` gives `z 1 ⊗ n`, and the commutor swaps the
  -- two tensor factors.
  change
    (TensorProduct.comm R M N)
        ((z.rTensor N)
          ((TensorProduct.quotTensorEquivQuotSMul N (maximalIdeal R)).symm
            (Submodule.Quotient.mk n))) =
      n ⊗ₜ[R] z 1
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk]
  rfl

/-- Helper for Lemma 10.163.1: tensoring the quotient comparison with an injective residue-field
line remains injective because `N` is flat over `R`. -/
lemma source_quotient_to_tensor_map_injective {z : ResidueField R →ₗ[R] M}
    (hz_inj : Function.Injective z) :
    Function.Injective (source_quotient_to_tensor_map (R := R) (N := N) (M := M) z) := by
  -- Proof comment: the quotient/tensor comparison is a linear equivalence, and flatness of `N`
  -- preserves injectivity of the residue-field line after right tensoring.
  exact (TensorProduct.comm R M N).injective.comp <|
    (Module.Flat.rTensor_preserves_injective_linearMap (M := N) z hz_inj).comp <|
      (TensorProduct.quotTensorEquivQuotSMul N (maximalIdeal R)).symm.injective

/-- Helper for Lemma 10.163.1: when both `M` and the closed fiber have depth zero, the tensor
product contains a nonzero element annihilated by `maximalIdeal S`. -/
lemma tensor_has_maximalIdeal_annihilated_element_of_depth_zero
    (hM0 : moduleDepth R M = 0) (hCF0 : moduleDepth ClosedFiber ClosedFiberModule = 0) :
    ∃ t : N ⊗[R] M, t ≠ 0 ∧ ∀ s ∈ maximalIdeal S, s • t = 0 := by
  rcases
      exists_nonzero_annihilated_by_maximalIdeal_of_moduleDepth_zero
        (A := R) (P := M) hM0 with
    ⟨m, hm0, hm_ann⟩
  rcases
      closed_fiber_quotient_has_maximalIdeal_annihilated_element_of_depth_zero
        (R := R) (S := S) (N := N) hCF0 with
    ⟨q, hq0, hq_ann⟩
  rcases Submodule.mkQ_surjective (𝔪S • (⊤ : Submodule S N)) q with ⟨y, rfl⟩
  let z : ResidueField R →ₗ[R] M :=
    residueField_to_module_map_of_annihilated (A := R) (P := M) m hm_ann
  let t : N ⊗[R] M :=
    source_quotient_to_tensor_map (R := R) (N := N) (M := M) z
      (Submodule.Quotient.mk y)
  refine ⟨t, ?_, ?_⟩
  · -- Proof comment: injectivity of the residue-field line and flatness of `N` make the source
    -- quotient-to-tensor map injective, so the nonzero quotient class of `y` stays nonzero.
    have hz_inj :
        Function.Injective (residueField_to_module_map_of_annihilated
          (A := R) (P := M) m hm_ann) :=
      residueField_to_module_map_of_annihilated_injective
        (A := R) (P := M) hm0 hm_ann
    have hmap_inj :
        Function.Injective (source_quotient_to_tensor_map (R := R) (N := N) (M := M) z) :=
      source_quotient_to_tensor_map_injective (R := R) (N := N) (M := M) hz_inj
    intro ht0
    apply hq0
    apply (map_maximalIdeal_quotient_equiv (R := R) (S := S) N).injective
    apply hmap_inj
    simpa [t, z] using ht0
  · intro s hs
    -- Proof comment: the quotient witness says `s • [y] = 0` in `N / 𝔪S N`, hence the class of
    -- `s • y` also vanishes in `N / 𝔪_R N`; mapping that zero class into the tensor product gives
    -- the desired annihilation of the pure tensor image.
    have hs_closed :
        (Submodule.Quotient.mk (s • y) : N ⧸ (𝔪S • (⊤ : Submodule S N))) = 0 := by
      simpa [Module.Quotient.mk_smul_mk] using hq_ann s hs
    have hs_source :
        (Submodule.Quotient.mk (s • y) : N ⧸ (maximalIdeal R • (⊤ : Submodule R N))) = 0 := by
      have hs_mem_closed : s • y - 0 ∈ 𝔪S • (⊤ : Submodule S N) :=
        (Submodule.Quotient.eq _).1 hs_closed
      have hs_mem_source : s • y - 0 ∈ maximalIdeal R • (⊤ : Submodule R N) := by
        simpa [smul_top_eq_map_restrictScalars (R := R) (S := S) (P := N) (maximalIdeal R)] using
          hs_mem_closed
      exact (Submodule.Quotient.eq _).2 hs_mem_source
    calc
      s • t = s • (y ⊗ₜ[R] z 1) := by
        simp [t, z, source_quotient_to_tensor_map_apply_mk]
      _ = (s • y) ⊗ₜ[R] z 1 := by rw [TensorProduct.smul_tmul']
      _ = source_quotient_to_tensor_map (R := R) (N := N) (M := M) z
            (Submodule.Quotient.mk (s • y)) := by
          symm
          simpa [z] using
            (source_quotient_to_tensor_map_apply_mk (R := R) (N := N) (M := M) z (s • y))
      _ = 0 := by
          simpa [hs_source]

/-- Helper for Lemma 10.163.1: the base case of the source-faithful induction. -/
lemma depth_zero_tensor_of_depth_zero_closed_fiber
    (hM0 : moduleDepth R M = 0) (hCF0 : moduleDepth ClosedFiber ClosedFiberModule = 0) :
    moduleDepth S (N ⊗[R] M) = 0 := by
  rcases
      tensor_has_maximalIdeal_annihilated_element_of_depth_zero
        (R := R) (S := S) (M := M) (N := N) hM0 hCF0 with
    ⟨t, ht0, ht_ann⟩
  -- Proof comment: the explicit tensor witness killed by `maximalIdeal S` triggers the local
  -- depth-zero criterion on the finite `S`-module `N ⊗[R] M`.
  exact
    moduleDepth_eq_zero_of_exists_annihilated_by_maximalIdeal
      (A := S) (P := N ⊗[R] M) ⟨t, ht0, ht_ann⟩

/-- Helper for Lemma 10.163.1: the depth-zero tensor base case already works for arbitrary finite
flat recursive pairs `(M', N')`. -/
lemma depth_zero_tensor_of_depth_zero_closed_fiber_generic
    {M' : Type w} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    {N' : Type x} [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] [Module.Flat R N']
    (hM0 : moduleDepth R M' = 0)
    (hCF0 : moduleDepth ClosedFiber (ClosedFiber ⊗[S] N') = 0) :
    moduleDepth S (N' ⊗[R] M') = 0 := by
  -- Proof comment: the ambient base-case witness construction was already parameterized by the
  -- source and target modules, so the recursive induction can reuse it verbatim on quotient pairs.
  exact
    depth_zero_tensor_of_depth_zero_closed_fiber
      (R := R) (S := S) (M := M') (N := N') hM0 hCF0


end
