import stacks_proof.stacks_project.Chap10.Lemma_10_163_1.ClosedFiberDepthZero

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

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite R M] [Module.Finite S N] in
/-- Helper for Lemma 10.163.1: a source nonzerodivisor stays regular after tensoring with the flat
target module `N`, viewed as an `S`-linear endomorphism of `N ⊗[R] M`. -/
lemma source_regular_on_tensor {x : R} (hreg : IsSMulRegular M x) :
    IsSMulRegular (N ⊗[R] M) (algebraMap R S x) := by
  have hTensor : IsSMulRegular (N ⊗[R] M) x :=
    IsSMulRegular.lTensor (R := R) (M := N) hreg
  -- Proof comment: the `S`-action by `algebraMap R S x` agrees with the restricted `R`-action by
  -- `x`, so the flat-tensor regularity statement applies verbatim.
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro z hz
  exact hTensor.right_eq_zero_of_smul <| by
    simpa [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using hz

/-- Helper for Lemma 10.163.1: quotienting `N ⊗[R] M` by the source element `x` acting through
`R → S` agrees with tensoring `N` against the quotient `M / xM`. -/
noncomputable def tensor_quotient_by_source_element (x : R) :
    QuotSMulTop (algebraMap R S x) (N ⊗[R] M) ≃ₗ[S] N ⊗[R] QuotSMulTop x M := by
  let e₀ :
      ((S ⊗[R] M) ⊗[S] N) ≃ₗ[S] (N ⊗[R] M) :=
    (TensorProduct.comm S (S ⊗[R] M) N).trans <|
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N M
  let e₁ :
      QuotSMulTop (algebraMap R S x) (N ⊗[R] M) ≃ₗ[S]
        QuotSMulTop (algebraMap R S x) ((S ⊗[R] M) ⊗[S] N) :=
    QuotSMulTop.congr (algebraMap R S x) e₀.symm
  let e₂ :
      QuotSMulTop (algebraMap R S x) ((S ⊗[R] M) ⊗[S] N) ≃ₗ[S]
        QuotSMulTop (algebraMap R S x) (S ⊗[R] M) ⊗[S] N :=
    (QuotSMulTop.quotSMulTopTensorEquivQuotSMulTop
      (r := algebraMap R S x) (M' := S ⊗[R] M) (M := N)).symm
  let e₃ :
      QuotSMulTop (algebraMap R S x) (S ⊗[R] M) ⊗[S] N ≃ₗ[S]
        (S ⊗[R] QuotSMulTop x M) ⊗[S] N :=
    (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop
      (R := R) (r := x) (M := M) S).rTensor N
  let e₄ :
      (S ⊗[R] QuotSMulTop x M) ⊗[S] N ≃ₗ[S] N ⊗[R] QuotSMulTop x M :=
    (TensorProduct.comm S (S ⊗[R] QuotSMulTop x M) N).trans <|
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N (QuotSMulTop x M)
  -- Proof comment: rewrite the tensor product through `S ⊗[R] M`, commute quotienting past the
  -- outer `S`-tensor factor, then use the standard base-change cancellation again on `M / xM`.
  exact e₁.trans (e₂.trans (e₃.trans e₄))

/-- Helper for Lemma 10.163.1: regularity of the lifted element on the canonical closed-fiber
module makes multiplication by its quotient class injective on the quotient model
`N ⧸ (𝔪S • ⊤)`. -/
lemma closed_fiber_module_quotient_equiv_smul {f : S}
    (x : ClosedFiberModule) :
    letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
      (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
    letI : Module ClosedFiber (N ⧸ (𝔪S • (⊤ : Submodule S N))) :=
      Module.compHom (N ⧸ (𝔪S • (⊤ : Submodule S N))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
    closed_fiber_module_quotient_equiv (R := R) (S := S) (M := N)
      ((algebraMap S ClosedFiber f) • x) =
        (Ideal.Quotient.mk 𝔪S f) •
          closed_fiber_module_quotient_equiv (R := R) (S := S) (M := N) x := by
  letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
    (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
  letI : Module ClosedFiber (N ⧸ (𝔪S • (⊤ : Submodule S N))) :=
    Module.compHom (N ⧸ (𝔪S • (⊤ : Submodule S N))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
  let e := closed_fiber_module_quotient_equiv (R := R) (S := S) (M := N)
  -- Proof comment: first move the scalar through the imported `ClosedFiber`-linear equivalence,
  -- then rewrite the transported `ClosedFiber`-scalar as the quotient-ring scalar induced by `f`.
  calc
    e ((algebraMap S ClosedFiber f) • x) =
        (algebraMap S ClosedFiber f) • e x := by
          simpa using e.map_smul (algebraMap S ClosedFiber f) x
    _ = f • e x := by
          rw [← closed_fiber_quotient_smul_eq_source_smul (R := R) (S := S) (N := N) f (e x)]
    _ = (Ideal.Quotient.mk 𝔪S f) • e x := by
          simpa using
            ideal_scalar_action_eq_quotient_scalar_action
              (R := S) (I := 𝔪S)
              (N := N ⧸ (𝔪S • (⊤ : Submodule S N))) f (e x)

/-- Helper for Lemma 10.163.1: the quotient comparison `N / 𝔪S N ≃ N / maximalIdeal R • N`
intertwines multiplication by `f` with multiplication by its closed-fiber class on quotient
representatives. -/
lemma map_maximalIdeal_quotient_equiv_lsmul_naturality {f : S} (n : N) :
    (((LinearMap.lsmul S N f).restrictScalars R).quotientMapByIdeal (maximalIdeal R))
      (map_maximalIdeal_quotient_equiv (R := R) (S := S) N (Submodule.Quotient.mk n)) =
        map_maximalIdeal_quotient_equiv (R := R) (S := S) N
          ((Ideal.Quotient.mk 𝔪S f) •
            (Submodule.Quotient.mk n : N ⧸ (𝔪S • (⊤ : Submodule S N)))) := by
  -- Proof comment: both sides are the quotient class of `f • n`; expand only on the chosen
  -- representative `n` and avoid a global map extensionality argument.
  calc
    (((LinearMap.lsmul S N f).restrictScalars R).quotientMapByIdeal (maximalIdeal R))
        (map_maximalIdeal_quotient_equiv (R := R) (S := S) N (Submodule.Quotient.mk n)) =
          (Submodule.Quotient.mk (f • n) :
            N ⧸ (maximalIdeal R • (⊤ : Submodule R N))) := by
            simp [LinearMap.quotientMapByIdeal, map_maximalIdeal_quotient_equiv_apply_mk]
    _ =
        map_maximalIdeal_quotient_equiv (R := R) (S := S) N
          (Submodule.Quotient.mk (f • n) : N ⧸ (𝔪S • (⊤ : Submodule S N))) := by
            rw [map_maximalIdeal_quotient_equiv_apply_mk]
    _ =
        map_maximalIdeal_quotient_equiv (R := R) (S := S) N
          ((Ideal.Quotient.mk 𝔪S f) •
            (Submodule.Quotient.mk n : N ⧸ (𝔪S • (⊤ : Submodule S N)))) := by
            simpa using
              congrArg
                (map_maximalIdeal_quotient_equiv (R := R) (S := S) N)
                (ideal_scalar_action_eq_quotient_scalar_action
              (R := S) (I := 𝔪S) (N := N ⧸ (𝔪S • (⊤ : Submodule S N)))
              f (Submodule.Quotient.mk n))

/-- Helper for Lemma 10.163.1: regularity of the lifted element on the canonical closed-fiber
module makes multiplication by its quotient class injective on the quotient model
`N ⧸ (𝔪S • ⊤)`. -/
lemma quotient_smul_injective_of_closed_fiber_regular {f : S}
    (hreg : IsSMulRegular ClosedFiberModule (algebraMap S ClosedFiber f)) :
    Function.Injective
      (LinearMap.lsmul (S ⧸ 𝔪S) (N ⧸ (𝔪S • (⊤ : Submodule S N))) (Ideal.Quotient.mk 𝔪S f)) := by
  letI : Algebra ClosedFiber (S ⧸ 𝔪S) :=
    (closedFiber_quotient_equiv (R := R) (S := S)).symm.toAlgHom.toAlgebra
  letI : Module ClosedFiber (N ⧸ (𝔪S • (⊤ : Submodule S N))) :=
    Module.compHom (N ⧸ (𝔪S • (⊤ : Submodule S N))) (algebraMap ClosedFiber (S ⧸ 𝔪S))
  let e := closed_fiber_module_quotient_equiv (R := R) (S := S) (M := N)
  intro x y hxy
  -- Proof comment: conjugate quotient multiplication through the closed-fiber owner equivalence,
  -- use regularity on `ClosedFiberModule`, and then pull equality back through the equivalence.
  apply e.symm.injective
  apply hreg
  apply e.injective
  calc
    e ((algebraMap S ClosedFiber f) • e.symm x) =
        (Ideal.Quotient.mk 𝔪S f) • e (e.symm x) := by
          simpa [e] using
            closed_fiber_module_quotient_equiv_smul
              (R := R) (S := S) (N := N) (f := f) (e.symm x)
    _ = (LinearMap.lsmul (S ⧸ 𝔪S)
          (N ⧸ (𝔪S • (⊤ : Submodule S N))) (Ideal.Quotient.mk 𝔪S f)) x := by
          simp
    _ = (LinearMap.lsmul (S ⧸ 𝔪S)
          (N ⧸ (𝔪S • (⊤ : Submodule S N))) (Ideal.Quotient.mk 𝔪S f)) y := hxy
    _ = (Ideal.Quotient.mk 𝔪S f) • e (e.symm y) := by
          simp
    _ = e ((algebraMap S ClosedFiber f) • e.symm y) := by
          symm
          simpa [e] using
            closed_fiber_module_quotient_equiv_smul
              (R := R) (S := S) (N := N) (f := f) (e.symm y)

/-- Helper for Lemma 10.163.1: closed-fiber regularity gives the exact injectivity hypothesis on
`N / maximalIdeal R • N` needed by Lemma `10.99.1` for multiplication by a lift `f : S`. -/
lemma quotient_multiplication_injective_of_closed_fiber_regular {f : S}
    (hreg : IsSMulRegular ClosedFiberModule (algebraMap S ClosedFiber f)) :
    Function.Injective
      (((LinearMap.lsmul S N f).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := by
  let e := map_maximalIdeal_quotient_equiv (R := R) (S := S) N
  let v :
      (N ⧸ (𝔪S • (⊤ : Submodule S N))) →ₗ[R]
        N ⧸ (𝔪S • (⊤ : Submodule S N)) :=
    (LinearMap.lsmul (S ⧸ 𝔪S)
      (N ⧸ (𝔪S • (⊤ : Submodule S N))) (Ideal.Quotient.mk 𝔪S f)).restrictScalars R
  have hcompare :
      (((LinearMap.lsmul S N f).restrictScalars R).quotientMapByIdeal (maximalIdeal R)).comp
          e.toLinearMap =
        e.toLinearMap.comp v := by
    -- Proof comment: compare the two quotient maps on representatives and use the dedicated
    -- naturality lemma instead of unfolding the entire quotient-owner square globally.
    apply LinearMap.ext
    intro q
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (𝔪S • (⊤ : Submodule S N)) q
    simpa [v, LinearMap.comp_apply] using
      map_maximalIdeal_quotient_equiv_lsmul_naturality
        (R := R) (S := S) (N := N) (f := f) n
  exact
    injective_of_ladder_linearEquiv (R := R) hcompare
      (quotient_smul_injective_of_closed_fiber_regular
        (R := R) (S := S) (N := N) hreg)

/-- Helper for Lemma 10.163.1: a lift of a closed-fiber regular element is regular on `N`, and
the quotient `N / fN` remains flat over `R`. -/
lemma lift_closed_fiber_regular_element {f : S}
    (hreg : IsSMulRegular ClosedFiberModule (algebraMap S ClosedFiber f)) :
    IsSMulRegular N f ∧ Module.Flat R (QuotSMulTop f N) := by
  let u : N →ₗ[S] N := LinearMap.lsmul S N f
  have hmod :
      Function.Injective
        (((LinearMap.lsmul S N f).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) :=
    quotient_multiplication_injective_of_closed_fiber_regular
      (R := R) (S := S) (N := N) hreg
  have hu :
      Function.Injective (u.restrictScalars R) :=
    injective_of_mod_maximalIdeal_injective
      (R := R) (S := S) (M := N) (N := N) (u.restrictScalars R) hmod
  have hflat_range :
      Module.Flat R (N ⧸ LinearMap.range (u.restrictScalars R)) :=
    flat_quotient_of_mod_maximalIdeal_injective
      (R := R) (S := S) (M := N) (N := N) (u.restrictScalars R) hmod
  have hrange :
      LinearMap.range u = f • (⊤ : Submodule S N) := by
    ext n
    constructor
    · rintro ⟨m, rfl⟩
      exact Submodule.smul_mem_pointwise_smul m f (⊤ : Submodule S N) trivial
    · intro hn
      rcases (Submodule.mem_smul_pointwise_iff_exists n f (⊤ : Submodule S N)).1 hn with
        ⟨m, -, hm⟩
      exact ⟨m, by simpa [u] using hm⟩
  refine ⟨?_, ?_⟩
  · -- Proof comment: injectivity of the multiplication map is exactly scalar-regularity of `f`.
    refine IsSMulRegular.of_right_eq_zero_of_smul ?_
    intro n hn
    exact hu <| by simpa [u] using hn
  · -- Proof comment: the quotient by the range of multiplication by `f` is definitionally the
    -- quotient `QuotSMulTop f N`.
    have hflat_smul :
        Module.Flat R (N ⧸ (f • (⊤ : Submodule S N)).restrictScalars R) := by
      have hflat_range' := hflat_range
      rw [LinearMap.range_restrictScalars, hrange] at hflat_range'
      exact hflat_range'
    simpa [QuotSMulTop] using hflat_smul

/-- Helper for Lemma 10.163.1: a nonzero finite module over a Noetherian local ring has finite
depth, so the remaining proof may induct on an ordinary natural number. -/
theorem exists_nat_moduleDepth_of_nontrivial_finite_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P] :
    ∃ n : ℕ, moduleDepth A P = n := by
  -- Proof comment: over a local ring, Nakayama rules out `𝔪 P = P` for a nonzero finite module,
  -- so the depth cannot be `⊤`.
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ :=
    by
      simpa [ne_comm] using
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A P)))
  have hfiniteDepth : moduleDepth A P < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top
        (R := A) (I := maximalIdeal A) (M := P) hsmul
  rcases ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth) with ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

/-- Helper for Lemma 10.163.1: if the depth is represented by a natural number, then the module is
nontrivial. -/
theorem nontrivial_of_moduleDepth_eq_nat_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    {n : ℕ} (hdepth : moduleDepth A P = n) :
    Nontrivial P := by
  -- Proof comment: a subsingleton module has infinite depth, so a finite natural depth excludes
  -- the zero-module branch.
  by_contra hP
  letI : Subsingleton P := not_nontrivial_iff_subsingleton.mp hP
  have htop : moduleDepth A P = ⊤ :=
    moduleDepth_eq_top_of_subsingleton_for_entry (A := A) (P := P)
  have hnat_top : (n : ℕ∞) = ⊤ := by
    simpa [hdepth] using htop
  have hne_top : (n : ℕ∞) ≠ ⊤ := ENat.coe_ne_top (a := n)
  exact hne_top hnat_top

/-- Helper for Lemma 10.163.1: a maximal-ideal nonzerodivisor gives positive depth. -/
lemma one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P]
    {x : A} (hx : x ∈ maximalIdeal A) (hreg : IsSMulRegular P x) :
    (1 : ℕ∞) ≤ moduleDepth A P := by
  letI : Nontrivial (QuotSMulTop x P) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (R := A) (L := P) hx
  have hnil : IsRegular (R := A) (M := QuotSMulTop x P) [] := by
    simpa using (IsRegular.nil A (QuotSMulTop x P))
  have hsingleton_reg : IsRegular P [x] :=
    IsRegular.cons hreg hnil
  have hsingleton_mem : Ideal.ofList [x] ≤ maximalIdeal A := by
    simpa using (Ideal.span_singleton_le_iff_mem (I := maximalIdeal A) (x := x)).2 hx
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ :=
    by
      simpa [ne_comm] using
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A P)))
  -- Proof comment: the singleton regular sequence `[x]` contributes length `1` to the depth
  -- supremum.
  rw [show moduleDepth A P = sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) P hsmul]
  refine le_sSup ?_
  exact ⟨[x], hsingleton_reg, hsingleton_mem, by simp⟩

/-- Helper for Lemma 10.163.1: the maximal ideal of a Noetherian local ring cannot generate a
nonzero finite module, even in split universes. -/
lemma maximalIdeal_smul_top_ne_top_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P] :
    maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ := by
  -- Proof comment: this is Nakayama's lemma in the Jacobson-ideal form for the maximal ideal.
  simpa [ne_comm] using
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A P)))

/-- Helper for Lemma 10.163.1: for split universes, depth zero is equivalent to the absence of a
maximal-ideal regular element. -/
lemma moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P] :
    moduleDepth A P = 0 ↔ ¬ ∃ x ∈ maximalIdeal A, IsSMulRegular P x := by
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_entry (A := A) (P := P)
  rw [show moduleDepth A P = sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) P hsmul]
  constructor
  · intro hdepth hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    -- Proof comment: a regular element in the maximal ideal contributes a regular sequence of
    -- length one, contradicting depth zero.
    have hge : (1 : ℕ∞) ≤ sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) := by
      refine le_sSup ?_
      refine ⟨[x], ?_, ?_, by simp⟩
      · exact RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal P
          (by
            intro r hr
            simpa [List.mem_singleton.mp hr] using hx)
          ((RingTheory.Sequence.isWeaklyRegular_singleton_iff P x).2 hxreg)
      · simpa using hx
    exact (ENat.one_le_iff_ne_zero.1 hge) hdepth
  · intro hno
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
          exact hno ⟨x, hx, hxreg⟩
    · exact bot_le

/-- Helper for Lemma 10.163.1: positive finite depth produces a maximal-ideal nonzerodivisor in
split universes. -/
lemma exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P]
    (hdepth : moduleDepth A P ≠ 0) :
    ∃ x ∈ maximalIdeal A, IsSMulRegular P x := by
  -- Proof comment: contrapose the split-universe zero-depth criterion from the previous helper.
  by_contra hno
  exact hdepth
    ((moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_entry (A := A) (P := P)).2 hno)

/-- Helper for Lemma 10.163.1: mapping a regular sequence along a surjective algebra map does not
change its regularity on the same module. -/
theorem isRegular_map_algebraMap_iff_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {P : Type*} [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    (rs : List A) :
    RingTheory.Sequence.IsRegular P (rs.map (algebraMap A B)) ↔ RingTheory.Sequence.IsRegular P rs := by
  -- Proof comment: the identity map on the underlying additive group intertwines the two scalar
  -- actions through `algebraMap A B`.
  exact
    (AddEquiv.refl P).isRegular_congr <|
      List.forall₂_map_left_iff.mpr <|
        List.forall₂_same.mpr fun r _ => algebraMap_smul B r

/-- Helper for Lemma 10.163.1: a list of maximal-ideal elements in the target local ring lifts to
one in the source local ring under a surjective local algebra map. -/
theorem exists_preimage_list_in_maximalIdeal_of_surjective_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    (hsurj : Function.Surjective (algebraMap A B)) (rs : List B)
    (hI : Ideal.ofList rs ≤ maximalIdeal B) :
    ∃ rs' : List A,
      rs'.map (algebraMap A B) = rs ∧ Ideal.ofList rs' ≤ maximalIdeal A := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  induction rs with
  | nil =>
      have hnil : Ideal.ofList ([] : List A) ≤ maximalIdeal A := by
        simpa using (bot_le : (⊥ : Ideal A) ≤ maximalIdeal A)
      exact ⟨[], rfl, hnil⟩
  | cons b rs ih =>
      have hb_mem : b ∈ maximalIdeal B := by
        apply hI
        exact Ideal.subset_span (by simp)
      have hb_map : b ∈ Ideal.map (algebraMap A B) (maximalIdeal A) := by
        simpa [hmap] using hb_mem
      rcases (Ideal.mem_map_iff_of_surjective (f := algebraMap A B) hsurj).1 hb_map with
        ⟨a, ha, hab⟩
      have htail_aux : Ideal.ofList rs ≤ Ideal.ofList (b :: rs) := by
        rw [Ideal.ofList_cons]
        exact le_sup_of_le_right le_rfl
      have htail : Ideal.ofList rs ≤ maximalIdeal B := htail_aux.trans hI
      rcases ih htail with ⟨rs', hrs', hI'⟩
      have ha_le : Ideal.span ({a} : Set A) ≤ maximalIdeal A := by
        refine Ideal.span_le.mpr ?_
        intro x hx
        simp at hx
        simpa [hx] using ha
      have hcons : Ideal.ofList (a :: rs') ≤ maximalIdeal A := by
        rw [Ideal.ofList_cons]
        exact sup_le ha_le hI'
      exact ⟨a :: rs', by simp [hab, hrs'], hcons⟩

/-- Helper for Lemma 10.163.1: the maximal-ideal regular-sequence lengths on a module coincide
along a surjective local algebra map. -/
theorem regularSequenceLengths_maximalIdeal_eq_of_surjective_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    {P : Type*} [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Ideal.regularSequenceLengths (maximalIdeal A) P =
      Ideal.regularSequenceLengths (maximalIdeal B) P := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    -- Proof comment: push the source regular sequence forward into the target maximal ideal.
    have hreg' : RingTheory.Sequence.IsRegular P (rs.map (algebraMap A B)) :=
      (isRegular_map_algebraMap_iff_for_entry (A := A) (B := B) (P := P) rs).2 hreg
    have hI' : Ideal.ofList (rs.map (algebraMap A B)) ≤ maximalIdeal B := by
      simpa [Ideal.map_ofList, hmap] using Ideal.map_mono (f := algebraMap A B) hI
    exact ⟨rs.map (algebraMap A B), hreg', hI', by simp⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    -- Proof comment: lift the target regular sequence entrywise through surjectivity and pull
    -- regularity back along the same scalar comparison.
    rcases exists_preimage_list_in_maximalIdeal_of_surjective_for_entry
        (A := A) (B := B) hsurj rs hI with
      ⟨rs', hrs', hI'⟩
    have hreg_map : RingTheory.Sequence.IsRegular P (rs'.map (algebraMap A B)) := by
      simpa [hrs'] using hreg
    have hreg' : RingTheory.Sequence.IsRegular P rs' :=
      (isRegular_map_algebraMap_iff_for_entry (A := A) (B := B) (P := P) rs').1 hreg_map
    have hlen_nat : rs'.length = rs.length := by
      simpa using congrArg List.length hrs'
    exact ⟨rs', hreg', hI', by exact_mod_cast hlen_nat.symm⟩

/-- Helper for Lemma 10.163.1: restricting scalars along a surjective local algebra map preserves
module depth. -/
theorem moduleDepth_eq_of_surjective_local_algebra_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {P : Type*} [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    [Module.Finite A P] [Module.Finite B P]
    (hsurj : Function.Surjective (algebraMap A B)) :
    moduleDepth A P = moduleDepth B P := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  have hsmul :
      (maximalIdeal B • (⊤ : Submodule B P)).restrictScalars A =
        maximalIdeal A • (⊤ : Submodule A P) := by
    -- Proof comment: the target maximal ideal is exactly the image of the source maximal ideal.
    simpa [hmap] using
      (Ideal.smul_restrictScalars (R := A) (S := B) (M := P) (maximalIdeal A)
        (⊤ : Submodule B P))
  have htop :
      maximalIdeal A • (⊤ : Submodule A P) = ⊤ ↔
        maximalIdeal B • (⊤ : Submodule B P) = ⊤ := by
    constructor
    · intro hA
      have hA' : (maximalIdeal B • (⊤ : Submodule B P)).restrictScalars A = ⊤ := by
        rw [hsmul, hA]
      exact
        (Submodule.restrictScalars_eq_top_iff (S := A)
          (p := maximalIdeal B • (⊤ : Submodule B P))).mp hA'
    · intro hB
      have hB' : (maximalIdeal B • (⊤ : Submodule B P)).restrictScalars A = ⊤ := by
        rw [hB, Submodule.restrictScalars_top]
      simpa [hsmul] using hB'
  by_cases hA : maximalIdeal A • (⊤ : Submodule A P) = ⊤
  · -- Proof comment: if `𝔪_A P = P`, then both depths are infinite.
    rw [show moduleDepth A P = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal A) P hA,
      show moduleDepth B P = ⊤ from
        Ideal.depth_eq_top_of_smul_top (maximalIdeal B) P (htop.mp hA)]
  · -- Proof comment: otherwise both depths are suprema of the same regular-sequence lengths.
    have hB : maximalIdeal B • (⊤ : Submodule B P) ≠ ⊤ := mt htop.mpr hA
    rw [show moduleDepth A P =
          sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) P hA,
      show moduleDepth B P =
          sSup (Ideal.regularSequenceLengths (maximalIdeal B) P) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal B) P hB,
      regularSequenceLengths_maximalIdeal_eq_of_surjective_for_entry
        (A := A) (B := B) (P := P) hsurj]

/-- Helper for Lemma 10.163.1: in split universes, quotienting by a maximal-ideal nonzerodivisor
lowers local depth by at most one. -/
lemma moduleDepth_quotSMulTop_le_sub_one_of_mem_maximalIdeal_univ
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P] {x : A}
    (hx : x ∈ maximalIdeal A) (hreg : IsSMulRegular P x) :
    moduleDepth A (QuotSMulTop x P) ≤ moduleDepth A P - 1 := by
  letI : Nontrivial (QuotSMulTop x P) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (R := A) (L := P) hx
  -- Proof comment: rewrite both depths as suprema of maximal-ideal regular-sequence lengths and
  -- prepend the regular element `x` to any regular sequence on the quotient.
  have hquot_smul :
      maximalIdeal A • (⊤ : Submodule A (QuotSMulTop x P)) ≠ ⊤ := by
    simpa using maximalIdeal_smul_top_ne_top_for_entry (A := A) (P := QuotSMulTop x P)
  have hmodule_smul :
      maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_entry (A := A) (P := P)
  have hfiniteDepth : moduleDepth A P < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top
        (R := A) (I := maximalIdeal A) (M := P) hmodule_smul
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  have hdepth : moduleDepth A P = n := by
    simpa using hn.symm
  rw [show moduleDepth A (QuotSMulTop x P) =
      sSup (Ideal.regularSequenceLengths (maximalIdeal A) (QuotSMulTop x P)) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) (QuotSMulTop x P)
        hquot_smul]
  refine sSup_le ?_
  intro d hd
  rcases hd with ⟨ys, hysreg, hysmem, rfl⟩
  have hcons_reg : IsRegular P ([x] ++ ys) := by
    have hfull : IsRegular P (x :: ys) := by
      exact IsRegular.cons hreg hysreg
    simpa using hfull
  have hcons_mem : Ideal.ofList ([x] ++ ys) ≤ maximalIdeal A := by
    refine Ideal.span_le.mpr ?_
    intro r hr
    rcases (by simpa [List.mem_append] using hr : r = x ∨ r ∈ ys) with rfl | hyr
    · exact hx
    · exact hysmem (Ideal.subset_span hyr)
  have hcons_le : ((([x] ++ ys).length : ℕ∞) ≤ moduleDepth A P) := by
    rw [show moduleDepth A P = sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) P hmodule_smul]
    refine le_sSup ?_
    exact ⟨[x] ++ ys, hcons_reg, hcons_mem, rfl⟩
  have hcons_le_nat : ([x] ++ ys).length ≤ n := by
    rw [hdepth] at hcons_le
    exact_mod_cast hcons_le
  have hys_le_nat : ys.length ≤ n - 1 := by
    have hsucc_le : ys.length + 1 ≤ n := by
      simpa using hcons_le_nat
    omega
  rw [hdepth]
  exact_mod_cast hys_le_nat

/-- Helper for Lemma 10.163.1: in split universes, quotienting by a maximal-ideal nonzerodivisor
lowers local depth by exactly one. -/
theorem moduleDepth_quotSMulTop_eq_sub_one_univ
    {A : Type uA} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type uP} [AddCommGroup P] [Module A P] [Module.Finite A P] {x : A}
    (hreg : IsSMulRegular P x) (hx : x ∈ maximalIdeal A) :
    moduleDepth A (QuotSMulTop x P) = moduleDepth A P - 1 := by
  by_cases hP : Subsingleton P
  · letI : Subsingleton P := hP
    letI : Subsingleton (QuotSMulTop x P) := by infer_instance
    -- Proof comment: in the zero-module branch, both depths are `⊤`.
    have hdepth_P : moduleDepth A P = ⊤ :=
      moduleDepth_eq_top_of_subsingleton_for_entry (A := A) (P := P)
    have hdepth_quot : moduleDepth A (QuotSMulTop x P) = ⊤ :=
      moduleDepth_eq_top_of_subsingleton_for_entry (A := A) (P := QuotSMulTop x P)
    simpa [hdepth_P, hdepth_quot]
  · letI : Nontrivial P := not_subsingleton_iff_nontrivial.mp hP
    -- Route correction: instead of rebuilding the short-exact lower bound in split universes,
    -- move to the common-universe `ULift` model, apply Lemma `10.72.7` there, and then descend
    -- the resulting depth identity through the surjective local algebra `ULift A → A`.
    let eR : ULift.{uP} A ≃+* A := ULift.ringEquiv
    letI : IsLocalRing (ULift.{uP} A) := RingEquiv.isLocalRing eR.symm
    letI : IsNoetherianRing (ULift.{uP} A) :=
      isNoetherianRing_of_ringEquiv A eR.symm
    letI : Algebra (ULift.{uP} A) A := eR.toRingHom.toAlgebra
    letI : Module (ULift.{uP} A) P :=
      Module.compHom P (algebraMap (ULift.{uP} A) A)
    have hTowerP :
        IsScalarTower (ULift.{uP} A) A P :=
      IsScalarTower.of_compHom (ULift.{uP} A) A P
    let φA : ULift.{uP} A →ₗ[ULift.{uP} A] A :=
      { toFun := algebraMap (ULift.{uP} A) A
        map_add' := map_add _
        map_smul' := by
          intro a b
          change
            algebraMap (ULift.{uP} A) A (a * b) =
              algebraMap (ULift.{uP} A) A a * algebraMap (ULift.{uP} A) A b
          simp }
    letI : RingHomSurjective (algebraMap (ULift.{uP} A) A) :=
      ⟨eR.surjective⟩
    letI : Module.Finite (ULift.{uP} A) A :=
      Module.Finite.of_surjective φA eR.surjective
    letI : Module.Finite (ULift.{uP} A) P :=
      @Module.Finite.trans
        (ULift.{uP} A) A P _ _ _ _ _ _
        hTowerP inferInstance inferInstance
    letI : Module (ULift.{uP} A) (QuotSMulTop x P) :=
      Module.compHom (QuotSMulTop x P) (algebraMap (ULift.{uP} A) A)
    have hTowerQ :
        IsScalarTower (ULift.{uP} A) A (QuotSMulTop x P) :=
      IsScalarTower.of_compHom (ULift.{uP} A) A (QuotSMulTop x P)
    letI : Module.Finite (ULift.{uP} A) (QuotSMulTop x P) :=
      @Module.Finite.trans
        (ULift.{uP} A) A (QuotSMulTop x P) _ _ _ _ _ _
        hTowerQ inferInstance inferInstance
    letI : Module.Finite (ULift.{uP} A) (ULift.{uA} P) :=
      Module.Finite.equiv
        (ULift.moduleEquiv (R := ULift.{uP} A) (M := P)).symm
    have hxw :
        algebraMap A (ULift.{uP} A) x ∈ maximalIdeal (ULift.{uP} A) := by
      have hsurj :
          Function.Surjective (algebraMap A (ULift.{uP} A)) :=
        fun y ↦ ⟨y.down, by cases y; rfl⟩
      have hmap :
          Ideal.map (algebraMap A (ULift.{uP} A)) (maximalIdeal A) =
            maximalIdeal (ULift.{uP} A) :=
        IsLocalRing.map_maximalIdeal_of_surjective
          (algebraMap A (ULift.{uP} A)) hsurj
      have hxmap :
          algebraMap A (ULift.{uP} A) x ∈
            Ideal.map (algebraMap A (ULift.{uP} A)) (maximalIdeal A) :=
        Ideal.mem_map_of_mem (algebraMap A (ULift.{uP} A)) hx
      simpa [hmap] using hxmap
    have hregw :
        IsSMulRegular (ULift.{uA} P) (algebraMap A (ULift.{uP} A) x) := by
      -- Proof comment: `ULift.down` identifies scalar multiplication on the lifted module with
      -- the original scalar multiplication on `P`.
      intro a b hab
      apply ULift.ext
      apply hreg
      exact congrArg ULift.down hab
    let eQ :
        QuotSMulTop (algebraMap A (ULift.{uP} A) x)
            (ULift.{uA} P) ≃ₗ[ULift.{uP} A]
          QuotSMulTop x P :=
      QuotSMulTop.congr (algebraMap A (ULift.{uP} A) x)
        (ULift.moduleEquiv : ULift.{uA} P ≃ₗ[ULift.{uP} A] P)
    have hdepthP :
        moduleDepth (ULift.{uP} A) (ULift.{uA} P) =
          moduleDepth A P := by
      -- Proof comment: first remove the module lift by the canonical linear equivalence, then
      -- descend depth across the surjective local algebra `ULift A → A`.
      calc
        moduleDepth (ULift.{uP} A) (ULift.{uA} P) =
            moduleDepth (ULift.{uP} A) P := by
              simpa using
                moduleDepth_eq_of_equiv
                  (R := ULift.{uP} A)
                  (e := (ULift.moduleEquiv : ULift.{uA} P ≃ₗ[ULift.{uP} A] P))
        _ = moduleDepth A P := by
              exact
                @moduleDepth_eq_of_surjective_local_algebra_for_entry
                  (ULift.{uP} A) A _ _ _ inferInstance inferInstance
                  inferInstance inferInstance P _ _ _ hTowerP inferInstance inferInstance
                  eR.surjective
    have hdepthQ :
        moduleDepth (ULift.{uP} A) (QuotSMulTop x P) =
          moduleDepth A (QuotSMulTop x P) := by
      -- Proof comment: the quotient module is also obtained from an `A`-module by restricting
      -- scalars along the same surjective local algebra.
      exact
        @moduleDepth_eq_of_surjective_local_algebra_for_entry
          (ULift.{uP} A) A _ _ _ inferInstance inferInstance
          inferInstance inferInstance (QuotSMulTop x P) _ _ _ hTowerQ inferInstance
          inferInstance eR.surjective
    have hlift :
        moduleDepth (ULift.{uP} A)
            (QuotSMulTop (algebraMap A (ULift.{uP} A) x) (ULift.{uA} P)) =
          moduleDepth (ULift.{uP} A) (ULift.{uA} P) - 1 := by
      -- Proof comment: now the ring and module live in a common universe, so the original
      -- same-universe depth-drop theorem applies directly.
      exact
        IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one
          (R := ULift.{uP} A) (M := ULift.{uA} P)
          hregw hxw
    calc
      moduleDepth A (QuotSMulTop x P) =
          moduleDepth (ULift.{uP} A) (QuotSMulTop x P) := by
            rw [hdepthQ.symm]
      _ =
          moduleDepth (ULift.{uP} A)
            (QuotSMulTop (algebraMap A (ULift.{uP} A) x) (ULift.{uA} P)) := by
            -- Proof comment: transport the quotient module across the lifted module equivalence.
            symm
            simpa using
              moduleDepth_eq_of_equiv (R := ULift.{uP} A) (e := eQ)
      _ = moduleDepth (ULift.{uP} A) (ULift.{uA} P) - 1 := hlift
      _ = moduleDepth A P - 1 := by rw [hdepthP]


end
