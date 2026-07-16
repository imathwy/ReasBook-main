import stacks_proof.stacks_project.Chap10.Lemma_10_99_1
import stacks_proof.stacks_project.Chap10.Lemma_10_110_3.KoszulFirstOrder

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: an `R`-linear map to the residue field kills the
maximal-ideal multiple of any source module. -/
lemma linearMap_to_residueField_eq_zero_of_mem_maximal_smul_top
    {M : Type u} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] ResidueField R) {y : M}
    (hy : y ∈ maximalIdeal R • (⊤ : Submodule R M)) :
    f y = 0 := by
  -- Induct over the `𝔪`-linear-combination presentation and use that the residue action of
  -- every element of `𝔪` is zero.
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr y _hy
    have hr0 : algebraMap R (ResidueField R) r = 0 := by
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using
        (IsLocalRing.residue_eq_zero_iff (R := R) r).mpr hr
    calc
      f (r • y) = r • f y := map_smul f r y
      _ = (algebraMap R (ResidueField R) r) * f y := Algebra.smul_def r (f y)
      _ = 0 := by rw [hr0, zero_mul]
  · intro y z hy hz
    simp [hy, hz]

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: in degree zero, vanishing in the residue field puts an
exterior-power element in the maximal-ideal multiple. -/
lemma exteriorPower_zero_mem_maximal_smul_top_of_quotient_eq_zero
    {E : Type u} [AddCommGroup E] [Module R E]
    {z : ⋀[R]^0 E}
    (hz : ((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap)
      ((exteriorPower.zeroEquiv R E) z) = 0) :
    z ∈ maximalIdeal R • (⊤ : Submodule R (⋀[R]^0 E)) := by
  let r : R := (exteriorPower.zeroEquiv R E) z
  -- The degree-zero exterior-power equivalence identifies the kernel with `𝔪 ⊂ R`, then the
  -- element is written as an `𝔪`-multiple of the unit basis vector.
  have hr : r ∈ maximalIdeal R := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hz
  have hz_eq : z = r • (exteriorPower.zeroEquiv R E).symm (1 : R) := by
    rw [← LinearEquiv.map_smul]
    simp [r]
  rw [hz_eq]
  exact Submodule.smul_mem_smul hr trivial

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the degree-zero component of a Koszul comparison is
injective after reducing modulo the maximal ideal. -/
lemma minimalComparison_reducedComponent_zero_injective
    {n : ℕ} (x : Fin n → maximalIdeal R)
    {F : ChainComplex (ModuleCat R) ℕ}
    (ρ : F ⟶ moduleSingle[R] (ResidueField R))
    (α : localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ F)
    (hα : α ≫ ρ = localKoszulAugmentation (R := R) x) :
    Function.Injective (((α.f 0).hom).quotientMapByIdeal (maximalIdeal R)) := by
  rw [quotientMapByIdeal_injective_iff_mem_smul]
  intro z hz
  -- Push a putative kernel element through the augmentation square; the target augmentation
  -- kills the image because it is an `𝔪`-multiple in the resolution term.
  have hρ_zero : (ρ.f 0).hom ((α.f 0).hom z) = 0 :=
    linearMap_to_residueField_eq_zero_of_mem_maximal_smul_top (R := R) (ρ.f 0).hom hz
  have hcomp0 : α.f 0 ≫ ρ.f 0 = (localKoszulAugmentation (R := R) x).f 0 := by
    simpa using congrArg (fun β :
      localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶
        moduleSingle[R] (ResidueField R) => β.f 0) hα
  have haug_zero : ((localKoszulAugmentation (R := R) x).f 0).hom z = 0 := by
    have hpoint := congrArg
      (fun f : (localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X 0 ⟶
          (moduleSingle[R] (ResidueField R)).X 0 => f.hom z)
      hcomp0
    exact hpoint.symm.trans hρ_zero
  -- The explicit degree-zero augmentation is the quotient map `R → κ` after `⋀⁰ ≃ R`.
  apply exteriorPower_zero_mem_maximal_smul_top_of_quotient_eq_zero (R := R)
  rw [localKoszulAugmentation_f_zero] at haug_zero
  simpa using haug_zero

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: a minimal displayed target differential sends the first
maximal-ideal layer into the square layer in owner chain-complex coordinates. -/
lemma minimalTarget_ownerDifferential_mem_maximalSquare
    {d : ℕ} (C : FiniteFreeComplex R (d + 1))
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R)
    {i : ℕ} (hi : i < d + 2) {y : C.toChainComplex.X (i + 1)}
    (hy : y ∈ maximalIdeal R • (⊤ : Submodule R (C.toChainComplex.X (i + 1)))) :
    ((C.toChainComplex.d (i + 1) i).hom y) ∈
      (maximalIdeal R) ^ 2 • (⊤ : Submodule R (C.toChainComplex.X i)) := by
  by_cases hi' : i < d + 1
  · let k : Fin (d + 1) := ⟨i, hi'⟩
    let ycoord : C.term k.succ := (C.termIso k.succ).hom.hom y
    -- Move the input to displayed coordinates, where minimality was stated entrywise.
    have hycoord : ycoord ∈ maximalIdeal R • (⊤ : Submodule R (C.term k.succ)) := by
      exact (Submodule.smul_top_le_comap_smul_top (maximalIdeal R)
        (C.termIso k.succ).hom.hom) hy
    have hdiffcoord :
        C.diffAt k ycoord ∈
          (maximalIdeal R) ^ 2 • (⊤ : Submodule R (C.term k.castSucc)) :=
      diffAt_mem_maximalSquare_of_entries_mem_maximal (R := R) C k (hminimal k) hycoord
    -- Transport the square-layer membership back through the target coordinate isomorphism.
    have howner_mem :
        (C.termIso k.castSucc).inv.hom (C.diffAt k ycoord) ∈
          (maximalIdeal R) ^ 2 • (⊤ : Submodule R (C.toChainComplex.X i)) := by
      exact (Submodule.smul_top_le_comap_smul_top ((maximalIdeal R) ^ 2)
        (C.termIso k.castSucc).inv.hom) hdiffcoord
    have hy_back : (C.termIso k.succ).inv.hom ycoord = y := by
      simpa [ycoord] using (C.termIso k.succ).toLinearEquiv.symm_apply_apply y
    have hdiff_eq :
        (C.termIso k.castSucc).inv.hom (C.diffAt k ycoord) =
          (C.toChainComplex.d (i + 1) i).hom y := by
      calc
        (C.termIso k.castSucc).inv.hom (C.diffAt k ycoord) =
            (C.toChainComplex.d (k.1 + 1) k.1).hom ((C.termIso k.succ).inv.hom ycoord) := by
              exact diffAt_termIso_inv_apply (R := R) C k ycoord
        _ = (C.toChainComplex.d (k.1 + 1) k.1).hom y := by
              rw [hy_back]
        _ = (C.toChainComplex.d (i + 1) i).hom y := by
              rfl
    rw [← hdiff_eq]
    exact howner_mem
  · -- In the top boundary case the source term is beyond the displayed length, so the input is
    -- zero and the conclusion is immediate.
    have hsrczero : Limits.IsZero (C.toChainComplex.X (i + 1)) := by
      exact C.isZero_toChainComplex_X (i + 1) (by omega)
    let _ : Subsingleton (C.toChainComplex.X (i + 1)) :=
      ModuleCat.subsingleton_of_isZero hsrczero
    have hy0 : y = 0 := Subsingleton.elim y 0
    rw [hy0, map_zero]
    exact Submodule.zero_mem _

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the top component of a minimal Koszul comparison is
injective after reducing modulo the maximal ideal. -/
lemma minimalComparison_topQuotientMap_injective
    {d : ℕ}
    (b : Module.Basis (Fin (d + 2)) (ResidueField R) (CotangentSpace R))
    (x : Fin (d + 2) → maximalIdeal R)
    (hx : ∀ i, (maximalIdeal R).toCotangent (x i) = b i)
    (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (α : localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ C.toChainComplex)
    (hα : α ≫ ρ = localKoszulAugmentation (R := R) x)
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R) :
    Function.Injective
      (((α.f (d + 2)).hom).quotientMapByIdeal (maximalIdeal R)) := by
  -- Route correction: the tensor statement should be obtained from a reduced comparison theorem,
  -- not by repeating tensor/coercion transport in the top theorem. The remaining source-facing
  -- task is the degree-by-degree first-order Koszul comparison induction for this minimal
  -- finite-free resolution.
  -- TODO: prove the reduced-component induction. The successor step should combine the chain-map
  -- square, the target square-filtration from `hminimal`, the imported maximal-power injectivity
  -- upgrade, and the first-order Koszul kernel statement from the cotangent-basis lift `hx`.
  have _hρ_used : ChainComplex.IsFiniteFreeResolution ρ := hρ
  have hbase :
      Function.Injective (((α.f 0).hom).quotientMapByIdeal (maximalIdeal R)) :=
    minimalComparison_reducedComponent_zero_injective (R := R) x ρ α hα
  have hstep :
      ∀ i, i < d + 2 →
        Function.Injective (((α.f i).hom).quotientMapByIdeal (maximalIdeal R)) →
        Function.Injective (((α.f (i + 1)).hom).quotientMapByIdeal (maximalIdeal R)) := by
    intro i hi hprev
    rw [quotientMapByIdeal_injective_iff_mem_smul]
    intro z hz
    -- Use the source first-order kernel after proving that the source differential is in `𝔪²`.
    refine localKoszulDifferential_firstOrder_kernel_of_cotangentBasis (R := R) b x hx hi ?_
    have hprevSquare :
        Function.Injective (((α.f i).hom).quotientMapByIdeal ((maximalIdeal R) ^ 2)) :=
      maximalIdeal_pow_stage_injective (R := R) (u := (α.f i).hom) hprev 2 (by norm_num)
    have htargetSquare :
        ((C.toChainComplex.d (i + 1) i).hom ((α.f (i + 1)).hom z)) ∈
          (maximalIdeal R) ^ 2 • (⊤ : Submodule R (C.toChainComplex.X i)) :=
      minimalTarget_ownerDifferential_mem_maximalSquare (R := R) C hminimal hi hz
    have hcomm :
        (α.f i).hom
            (((localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).d (i + 1) i).hom z) =
          (C.toChainComplex.d (i + 1) i).hom ((α.f (i + 1)).hom z) := by
      -- Evaluate the chain-map square for `α` on the representative `z`.
      have hmap := congrArg
        (fun f :
            (localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).X (i + 1) ⟶
              C.toChainComplex.X i ↦ f.hom z)
        ((α.comm (i + 1) i).symm)
      simpa using hmap
    have hsourceImageSquare :
        (α.f i).hom
            (((localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).d (i + 1) i).hom z) ∈
          (maximalIdeal R) ^ 2 • (⊤ : Submodule R (C.toChainComplex.X i)) := by
      rwa [hcomm]
    exact
      ((quotientMapByIdeal_injective_iff_mem_smul
        (R := R) ((maximalIdeal R) ^ 2) (α.f i).hom).1 hprevSquare)
        (((localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).d (i + 1) i).hom z)
        hsourceImageSquare
  have hind :
      ∀ i, i ≤ d + 2 →
        Function.Injective (((α.f i).hom).quotientMapByIdeal (maximalIdeal R)) := by
    intro i
    induction i with
    | zero =>
        intro _hi
        exact hbase
    | succ i ih =>
        intro hi
        -- Advance the reduced comparison one degree using the successor step.
        have hi_lt : i < d + 2 := Nat.lt_of_succ_le hi
        have hi_le : i ≤ d + 2 := Nat.le_trans (Nat.le_succ i) hi
        exact hstep i hi_lt (ih hi_le)
  exact hind (d + 2) (Nat.le_refl _)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the residue-field base change of the top Koszul
comparison component is injective for cotangent-basis lifts and a minimal target resolution. -/
lemma minimalComparison_topBaseChange_injective
    {d : ℕ}
    (b : Module.Basis (Fin (d + 2)) (ResidueField R) (CotangentSpace R))
    (x : Fin (d + 2) → maximalIdeal R)
    (hx : ∀ i, (maximalIdeal R).toCotangent (x i) = b i)
    (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (α : localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ C.toChainComplex)
    (hα : α ≫ ρ = localKoszulAugmentation (R := R) x)
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R) :
    Function.Injective
      (TensorProduct.map
        (LinearMap.id : ResidueField R →ₗ[R] ResidueField R)
        (α.f (d + 2)).hom :
        TensorProduct R (ResidueField R)
            ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X (d + 2)) →ₗ[R]
      TensorProduct R (ResidueField R) (C.toChainComplex.X (d + 2))) := by
  -- Route correction: the previous top-only contradiction was too weak for arbitrary `x`; the
  -- remaining invariant is the source proof's reduced-component induction with the cotangent-basis
  -- lift and entrywise minimality hypotheses made explicit.
  -- The tensor transport is now isolated in the closed-fiber adapter; the source-facing quotient
  -- injectivity remains the only mathematical input needed at this top degree.
  exact
    tensorResidue_injective_of_quotientMap_maximal_injective
      (R := R) (f := (α.f (d + 2)).hom)
      (minimalComparison_topQuotientMap_injective (R := R) b x hx C ρ hρ α hα hminimal)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the top first-order Koszul comparison contradicts a
minimal finite free resolution whose top residue-field term is zero. -/
lemma minimalComparison_topFirstOrder_contradiction
    {d : ℕ}
    (b : Module.Basis (Fin (d + 2)) (ResidueField R) (CotangentSpace R))
    (x : Fin (d + 2) → maximalIdeal R)
    (hx : ∀ i, (maximalIdeal R).toCotangent (x i) = b i)
    (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (α : localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ C.toChainComplex)
    (hα : α ≫ ρ = localKoszulAugmentation (R := R) x)
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R)
    (htopTerm :
      Nontrivial
        (TensorProduct R (ResidueField R)
          ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X (d + 2))))
    (htarget :
      Subsingleton (TensorProduct R (ResidueField R) (C.toChainComplex.X (d + 2)))) :
    False := by
  -- The only remaining source-facing invariant is injectivity of the top reduced comparison map.
  -- Once that is available, nontriviality of the source transfers a subsingleton contradiction
  -- back from the top target term.
  have hinj :
      Function.Injective
        (TensorProduct.map
          (LinearMap.id : ResidueField R →ₗ[R] ResidueField R)
          (α.f (d + 2)).hom :
          TensorProduct R (ResidueField R)
              ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X (d + 2)) →ₗ[R]
            TensorProduct R (ResidueField R) (C.toChainComplex.X (d + 2))) :=
    minimalComparison_topBaseChange_injective (R := R) b x hx C ρ hρ α hα hminimal
  have hsource_subsingleton :
      Subsingleton
        (TensorProduct R (ResidueField R)
          ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X (d + 2))) := by
    constructor
    intro y z
    exact hinj (htarget.elim _ _)
  exact (not_subsingleton_iff_nontrivial.mpr htopTerm) hsource_subsingleton

end
