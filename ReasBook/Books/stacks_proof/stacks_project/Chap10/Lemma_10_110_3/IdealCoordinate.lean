import StacksProject_2024.Chap10.Lemma_10_110_3.LocalKoszul
import StacksProject_2024.Chap10.Lemma_10_96_1

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: a vector in a finite product whose coordinates all lie in
an ideal belongs to the ideal multiple of the whole product module. -/
private lemma finFun_mem_ideal_smul_top_of_forall_mem
    {n : ℕ} (I : Ideal R) (v : Fin n → R) (hv : ∀ i, v i ∈ I) :
    v ∈ I • (⊤ : Submodule R (Fin n → R)) := by
  classical
  -- Expand the vector in the standard coordinate basis and put each basis summand in `I • ⊤`.
  have hsum : (∑ i : Fin n, v i • (Pi.single i (1 : R) : Fin n → R)) = v := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij), smul_zero]
    · intro hnot
      simp at hnot
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hv i) trivial

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: membership in `I • ⊤` for a finite product forces each
coordinate to lie in `I`. -/
private lemma forall_mem_of_finFun_mem_ideal_smul_top
    {n : ℕ} (I : Ideal R) {v : Fin n → R}
    (hv : v ∈ I • (⊤ : Submodule R (Fin n → R))) :
    ∀ i, v i ∈ I := by
  -- Induct over the `I`-linear-combination presentation of the vector.
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro r hr y _hy i
    simpa [Pi.smul_apply] using I.mul_mem_right (y i) hr
  · intro y z hy hz i
    simpa [Pi.add_apply] using I.add_mem (hy i) (hz i)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: a coordinate linear map whose matrix entries lie in an
ideal sends every vector into the ideal multiple of the target. -/
private lemma linearMap_pi_mem_ideal_smul_top_of_basis_mem
    {m n : ℕ} (I : Ideal R) (f : (Fin m → R) →ₗ[R] (Fin n → R))
    (hf : ∀ a b, f (Pi.single a (1 : R) : Fin m → R) b ∈ I) (v : Fin m → R) :
    f v ∈ I • (⊤ : Submodule R (Fin n → R)) := by
  classical
  -- It is enough to prove ideal membership coordinatewise in the target product.
  apply finFun_mem_ideal_smul_top_of_forall_mem I
  intro b
  have hsum : (∑ a : Fin m, v a • (Pi.single a (1 : R) : Fin m → R)) = v := by
    ext c
    rw [Finset.sum_apply, Finset.sum_eq_single c]
    · simp
    · intro a _ hac
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hac), smul_zero]
    · intro hnot
      simp at hnot
  -- Write the `b`th coordinate as a finite sum of scalar multiples of matrix entries in `I`.
  rw [← hsum]
  rw [map_sum]
  simp only [LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply]
  exact Ideal.sum_mem I (fun a _ ↦ I.mul_mem_left (v a) (hf a b))

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: if the input vector is already in `I • ⊤`, then a coordinate
map with entries in `I` lands in `I ^ 2 • ⊤`. -/
private lemma linearMap_pi_mem_ideal_sq_smul_top_of_basis_mem
    {m n : ℕ} (I : Ideal R) (f : (Fin m → R) →ₗ[R] (Fin n → R))
    (hf : ∀ a b, f (Pi.single a (1 : R) : Fin m → R) b ∈ I)
    {v : Fin m → R} (hv : v ∈ I • (⊤ : Submodule R (Fin m → R))) :
    f v ∈ I ^ 2 • (⊤ : Submodule R (Fin n → R)) := by
  classical
  -- Work coordinatewise: source coordinates lie in `I`, while matrix entries lie in `I`.
  apply finFun_mem_ideal_smul_top_of_forall_mem (I ^ 2)
  intro b
  have hv_coord : ∀ a, v a ∈ I :=
    forall_mem_of_finFun_mem_ideal_smul_top I hv
  have hsum : (∑ a : Fin m, v a • (Pi.single a (1 : R) : Fin m → R)) = v := by
    ext c
    rw [Finset.sum_apply, Finset.sum_eq_single c]
    · simp
    · intro a _ hac
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hac), smul_zero]
    · intro hnot
      simp at hnot
  rw [← hsum]
  rw [map_sum]
  simp only [LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply]
  exact Ideal.sum_mem (I ^ 2) fun a _ ↦ by
    rw [pow_two]
    exact Ideal.mul_mem_mul (hv_coord a) (hf a b)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: in a minimal displayed finite free complex, the differential
sends `maximalIdeal R • Cᵢ₊₁` into `(maximalIdeal R) ^ 2 • Cᵢ`. -/
lemma diffAt_mem_maximalSquare_of_entries_mem_maximal
    {e : ℕ} (C : FiniteFreeComplex R e) (i : Fin e)
    (hentry : ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
      FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R)
    {y : C.term i.succ}
    (hy : y ∈ maximalIdeal R • (⊤ : Submodule R (C.term i.succ))) :
    C.diffAt i y ∈ (maximalIdeal R) ^ 2 • (⊤ : Submodule R (C.term i.castSucc)) := by
  -- Apply the coordinate matrix lemma to the displayed differential `C.diffAt i`.
  exact linearMap_pi_mem_ideal_sq_smul_top_of_basis_mem
    (I := maximalIdeal R) (f := C.diffAt i) hentry hy

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: in a minimal displayed finite free complex, the differential
has image in the maximal-ideal multiple of the target term. -/
private lemma diffAt_mem_maximal_smul_top_of_entries_mem_maximal
    {e : ℕ} (C : FiniteFreeComplex R e) (i : Fin e)
    (hentry : ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
      FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R)
    (y : C.term i.succ) :
    C.diffAt i y ∈ maximalIdeal R • (⊤ : Submodule R (C.term i.castSucc)) := by
  -- The displayed matrix has all entries in `𝔪`, so every coordinate of the image is an
  -- `R`-linear combination of elements of `𝔪`.
  exact linearMap_pi_mem_ideal_smul_top_of_basis_mem
    (I := maximalIdeal R) (f := C.diffAt i) hentry y

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: reducing a minimal displayed differential modulo the
maximal ideal gives the zero map. -/
private lemma diffAt_quotientMap_maximal_eq_zero_of_entries_mem_maximal
    {e : ℕ} (C : FiniteFreeComplex R e) (i : Fin e)
    (hentry : ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
      FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R) :
    (C.diffAt i).quotientMapByIdeal (maximalIdeal R) = 0 := by
  -- It suffices to check representatives; the preceding image-containment lemma says every
  -- representative maps to zero in the quotient by `𝔪`.
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨y, rfl⟩ :=
    Submodule.mkQ_surjective
      (maximalIdeal R • (⊤ : Submodule R (C.term i.succ))) z
  change
    Submodule.Quotient.mk (C.diffAt i y) =
      (0 :
        C.term i.castSucc ⧸
          maximalIdeal R • (⊤ : Submodule R (C.term i.castSucc)))
  exact (Submodule.Quotient.mk_eq_zero _).2
    (diffAt_mem_maximal_smul_top_of_entries_mem_maximal (R := R) C i hentry y)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the top term of the residue-field tensor of the
finite-family local Koszul complex is nontrivial. -/
lemma residueTensor_localKoszul_topTerm_nontrivial
    {n : ℕ} (x : Fin n → maximalIdeal R) :
    Nontrivial
      (TensorProduct R (ResidueField R)
        ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X n)) := by
  -- The degree-`n` term is `κ ⊗_R ⋀^n_R R^n`.
  change Nontrivial (TensorProduct R (ResidueField R) (⋀[R]^n (Fin n → R)))
  let eBase : TensorProduct R (ResidueField R) (⋀[R]^n (Fin n → R)) ≃ₗ[ResidueField R]
      ⋀[ResidueField R]^n (TensorProduct R (ResidueField R) (Fin n → R)) :=
    baseChangeExteriorPowerLinearEquiv
      (R := R) (A := ResidueField R) (M := Fin n → R) n
  let eStd :
      ⋀[ResidueField R]^n (TensorProduct R (ResidueField R) (Fin n → R)) →ₗ[ResidueField R]
        ⋀[ResidueField R]^n (Fin n → ResidueField R) :=
    exteriorPower.map n
      (TensorProduct.piScalarRight R (ResidueField R) (ResidueField R) (Fin n)).toLinearMap
  have hsurjStd : Function.Surjective eStd := by
    -- The standard finite-free base-change equivalence induces a surjection on exterior powers.
    exact
      exteriorPower.map_surjective (n := n)
        (f := (TensorProduct.piScalarRight R (ResidueField R) (ResidueField R)
          (Fin n)).toLinearMap)
        (TensorProduct.piScalarRight R (ResidueField R) (ResidueField R) (Fin n)).surjective
  have hsurj : Function.Surjective fun y ↦ eStd (eBase y) :=
    hsurjStd.comp eBase.surjective
  let _ : Nontrivial (⋀[ResidueField R]^n (Fin n → ResidueField R)) :=
    topExteriorFinFun_nontrivial (ResidueField R) n
  -- Pull nontriviality back along the composite surjection to the tensorized Koszul term.
  exact hsurj.nontrivial

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the local Koszul augmentation admits a comparison map to
any finite free resolution of the residue field. -/
lemma localKoszulComparisonMap_exists
    {n : ℕ} (x : Fin n → maximalIdeal R)
    {F : ChainComplex (ModuleCat R) ℕ}
    (ρ : F ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ) :
    ∃ α : localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ F,
      α ≫ ρ = localKoszulAugmentation (R := R) x := by
  -- Lift the identity map on the residue field through the chosen finite free resolution.
  letI : QuasiIso ρ := hρ.toIsFreeResolution.toQuasiIso
  simpa using
    free_complex_lift_to_resolution_exists
      (R := R) (M := ResidueField R) (N := ResidueField R)
      (F := localKoszulComplexOn (R := R) (fun i ↦ (x i : R))) (G := F)
      (f := 𝟙 (ModuleCat.of R (ResidueField R)))
      (πF := localKoszulAugmentation (R := R) x) (πG := ρ)
      (localKoszulComplexOn_termwiseFree (R := R) (x := fun i ↦ (x i : R)))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: a finite free resolution of length `d + 1` makes
`Tor_{d+2}^R(κ, κ)` vanish. -/
lemma shortMinimalResolution_selfTor_vanishes_top
    {d : ℕ} (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ) :
    Limits.IsZero
      ((((CategoryTheory.Tor (ModuleCat R) (d + 2)).obj
          (ModuleCat.of R (ResidueField R))).obj
        (ModuleCat.of R (ResidueField R)))) := by
  -- Package the displayed finite free complex as a bounded resolution and use the existing
  -- Tor-vanishing theorem above the bound.
  have hres :
      HasFiniteFreeResolutionLengthLE R (ResidueField R) (d + 1) :=
    ⟨C.toChainComplex, ρ, hρ, C.isZero_toChainComplex_X⟩
  exact
    tor_residueField_isZero_of_finiteFreeResolutionLengthLE_lt
      (R := R) hres (Nat.lt_succ_self (d + 1))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: tensoring with a module over the residue field depends only
on the closed-fiber quotient of the source module. -/
private noncomputable def closedFiberTensorLinearEquiv
    {P : Type u} [AddCommGroup P] [Module R P]
    (Q : Type u) [AddCommGroup Q] [Module R Q]
    [Module (R ⧸ maximalIdeal R) Q] [IsScalarTower R (R ⧸ maximalIdeal R) Q] :
    TensorProduct R Q P ≃ₗ[R]
      TensorProduct (R ⧸ maximalIdeal R) Q
        (P ⧸ ((maximalIdeal R) • (⊤ : Submodule R P))) :=
  let eQuot :
      TensorProduct R (R ⧸ maximalIdeal R) P ≃ₗ[R ⧸ maximalIdeal R]
        (P ⧸ ((maximalIdeal R) • (⊤ : Submodule R P))) :=
    (TensorProduct.quotTensorEquivQuotSMul P (maximalIdeal R)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let eTensor :
      TensorProduct (R ⧸ maximalIdeal R) Q
          (TensorProduct R (R ⧸ maximalIdeal R) P) ≃ₗ[R ⧸ maximalIdeal R]
        TensorProduct (R ⧸ maximalIdeal R) Q
          (P ⧸ ((maximalIdeal R) • (⊤ : Submodule R P))) :=
    eQuot.lTensor Q
  (((TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ maximalIdeal R)
      (R ⧸ maximalIdeal R) Q P).symm.trans eTensor)).restrictScalars R

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: after the closed-fiber tensor comparison, tensoring `f`
with a residue-field module is exactly tensoring the reduced map `f mod maximalIdeal R`. -/
private lemma closedFiberTensorLinearEquiv_symm_naturality
    {P P' : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P']
    (f : P →ₗ[R] P')
    (Q : Type u) [AddCommGroup Q] [Module R Q]
    [Module (R ⧸ maximalIdeal R) Q] [IsScalarTower R (R ⧸ maximalIdeal R) Q] :
    (f.lTensor Q).comp
        (closedFiberTensorLinearEquiv (R := R) (P := P) Q).symm.toLinearMap =
      (closedFiberTensorLinearEquiv (R := R) (P := P') Q).symm.toLinearMap.comp
        ((((f.reduceModIdeal (maximalIdeal R)).lTensor Q)).restrictScalars R) := by
  -- Check the ladder on pure tensors `q ⊗ [x]`, which generate the source tensor product.
  apply DFunLike.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro q xbar
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((maximalIdeal R) • (⊤ : Submodule R P)) xbar
    simp [closedFiberTensorLinearEquiv]
  · intro x y hx hy
    simp [map_add, hx, hy]

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: injectivity modulo the maximal ideal gives injectivity
after tensoring on the left with the residue field. -/
lemma tensorResidue_injective_of_quotientMap_maximal_injective
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hf : Function.Injective (f.quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective
      (TensorProduct.map
        (LinearMap.id : ResidueField R →ₗ[R] ResidueField R) f :
        TensorProduct R (ResidueField R) M →ₗ[R] TensorProduct R (ResidueField R) N) := by
  -- Route correction: rebuild the closed-fiber tensor comparison locally instead of importing
  -- the full `Lemma_10_99_1` API chain.
  change Function.Injective (LinearMap.lTensor (R ⧸ maximalIdeal R) f)
  have hReduce :
      Function.Injective (((f.reduceModIdeal (maximalIdeal R))).restrictScalars R) := by
    simpa [quotientMapByIdeal_eq_reduceModIdeal_restrictScalars
      (R := R) (J := maximalIdeal R) f] using hf
  have hTensorReduce :
      Function.Injective
        ((((f.reduceModIdeal (maximalIdeal R)).lTensor (R ⧸ maximalIdeal R)).restrictScalars R)) :=
    by
      -- Over the residue field, tensoring preserves injectivity because every module is flat.
      letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
      letI : Module.Free (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R) :=
        Module.Free.of_divisionRing (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R)
      letI : Module.Flat (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R) := Module.Flat.of_free
      exact Module.Flat.lTensor_preserves_injective_linearMap
        ((f.reduceModIdeal (maximalIdeal R))) hReduce
  have hTensor : Function.Injective (f.lTensor (R ⧸ maximalIdeal R)) :=
    injective_of_ladder_linearEquiv (R := R)
      (closedFiberTensorLinearEquiv_symm_naturality
        (R := R) (P := M) (P' := N) f (R ⧸ maximalIdeal R))
      hTensorReduce
  exact hTensor

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: injectivity of an ideal-quotient map is equivalent to
the expected kernel membership criterion. -/
lemma quotientMapByIdeal_injective_iff_mem_smul
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    Function.Injective (f.quotientMapByIdeal I) ↔
      ∀ z, f z ∈ I • (⊤ : Submodule R N) → z ∈ I • (⊤ : Submodule R M) := by
  constructor
  · intro hf z hz
    -- A representative whose image is in `I N` maps to zero in the target quotient, hence was
    -- already zero in the source quotient by injectivity.
    have hzQ :
        (f.quotientMapByIdeal I) (Submodule.Quotient.mk z) = 0 := by
      change Submodule.Quotient.mk (f z) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 hz
    have hq : (Submodule.Quotient.mk z : M ⧸ I • (⊤ : Submodule R M)) = 0 := by
      exact hf (by simpa using hzQ)
    exact (Submodule.Quotient.mk_eq_zero _).1 hq
  · intro h x y hxy
    -- Reduce equality of quotient classes to representatives and apply the kernel criterion to
    -- the difference of the two representatives.
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) x
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) y
    apply (Submodule.Quotient.eq _).2
    apply h
    have htarget :
        (Submodule.Quotient.mk (f x') : N ⧸ I • (⊤ : Submodule R N)) =
          Submodule.Quotient.mk (f y') := by
      simpa [LinearMap.quotientMapByIdeal] using hxy
    have hdiff : f x' - f y' ∈ I • (⊤ : Submodule R N) :=
      (Submodule.Quotient.eq _).1 htarget
    simpa using hdiff

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: membership in an ideal multiple of a finite free module
can be checked on the coordinates of any finite basis. -/
private lemma basis_mem_ideal_smul_top_iff_coords
    {ι : Type*} [Finite ι]
    {M : Type u} [AddCommGroup M] [Module R M]
    (I : Ideal R) (b : Module.Basis ι R M) (z : M) :
    z ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr z i ∈ I := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro hz
    -- Push an `I`-linear-combination presentation through each basis coordinate.
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro r hr y _hy i
      simpa [map_smul] using I.mul_mem_right (b.repr y i) hr
    · intro y w hy hw i
      simpa [map_add] using I.add_mem (hy i) (hw i)
  · intro hcoord
    -- Expand in the basis and put every coordinate summand into `I • ⊤`.
    rw [← b.sum_repr z]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    exact Submodule.smul_mem_smul (hcoord i) trivial

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: membership in an ideal multiple of a standard exterior
power is equivalent to ideal membership of all standard exterior coordinates. -/
lemma standardExteriorPower_mem_ideal_smul_top_iff_coords
    (I : Ideal R) (n q : ℕ) (z : ⋀[R]^q (Fin n → R)) :
    z ∈ I • (⊤ : Submodule R (⋀[R]^q (Fin n → R))) ↔
      ∀ S : Set.powersetCard (Fin n) q,
        ((Pi.basisFun R (Fin n)).exteriorPower q).repr z S ∈ I := by
  -- Apply the finite-basis coordinate criterion to the exterior-power basis.
  exact
    basis_mem_ideal_smul_top_iff_coords I
      ((Pi.basisFun R (Fin n)).exteriorPower q) z


end
