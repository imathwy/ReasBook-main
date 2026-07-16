import Mathlib
import StacksProject_2024.stacks_project.Chap15.«15_90_8_1»
import StacksProject_2024.stacks_project.Chap15.Lemma_15_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ}
variable (M : ModuleCat R)

/-- Helper for Lemma 15.90.9: the `ℤ`-indexed extended alternating Čech complex of `M`,
obtained by extending the nonnegative complex along `embeddingUpNat`. -/
noncomputable abbrev moduleCechComplexZ
    (f : Fin t → R) (M : ModuleCat R) :
    CochainComplex (ModuleCat R) ℤ :=
  (extendedAlternatingCechComplex f M).extend ComplexShape.embeddingUpNat

/-- Helper for Lemma 15.90.9: the scalar-changed `ℤ`-indexed extended alternating Čech complex,
viewed back in `ModuleCat R` via restriction of scalars. -/
noncomputable abbrev moduleBaseChangedCechComplexZ
    (S : Type u) [CommRing S] [Algebra R S]
    (f : Fin t → R) (M : ModuleCat R) :
    CochainComplex (ModuleCat R) ℤ :=
  (((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
    ((extendedAlternatingCechComplex (fun i ↦ algebraMap R S (f i)) (S ⊗[R] M)).extend
      ComplexShape.embeddingUpNat))

/-- Helper for Lemma 15.90.9: extending a nonnegative cochain complex to `ℤ` creates zero terms
in every negative degree. -/
private theorem extend_embeddingUpNat_isZero_of_neg
    (K : CochainComplex (ModuleCat R) ℕ) {i : ℤ} (hi : i < 0) :
    IsZero ((K.extend ComplexShape.embeddingUpNat).X i) := by
  -- Negative degrees lie outside the image of `embeddingUpNat`, so the extended term is zero.
  exact K.isZero_extend_X ComplexShape.embeddingUpNat i <| by
    intro n hni
    have hni' : ((n : ℕ) : ℤ) = i := by
      simpa using hni
    have hge : 0 ≤ i := by
      simpa [← hni'] using (Int.natCast_nonneg n)
    exact (not_lt_of_ge hge) hi

/-- Helper for Lemma 15.90.9: the `ℤ`-extended module Čech complex has zero terms in negative
degrees. -/
private theorem moduleCechComplexZ_isZero_of_neg
    (f : Fin t → R) (M : ModuleCat R) {i : ℤ} (hi : i < 0) :
    IsZero ((moduleCechComplexZ (R := R) f M).X i) := by
  -- This is just the generic negative-degree vanishing for `embeddingUpNat`.
  exact extend_embeddingUpNat_isZero_of_neg (R := R)
    (extendedAlternatingCechComplex f M) hi

/-- Helper for Lemma 15.90.9: the restricted scalar-changed Čech complex also vanishes in
negative degrees. -/
private theorem moduleBaseChangedCechComplexZ_isZero_of_neg
    (S : Type u) [CommRing S] [Algebra R S]
    (f : Fin t → R) (M : ModuleCat R) {i : ℤ} (hi : i < 0) :
    IsZero ((moduleBaseChangedCechComplexZ (R := R) (S := S) f M).X i) := by
  -- Restriction of scalars preserves zero objects, so the vanishing reduces to the extended
  -- nonnegative complex over `S`.
  simpa [moduleBaseChangedCechComplexZ] using
    (ModuleCat.restrictScalars (algebraMap R S)).map_isZero
      (extend_embeddingUpNat_isZero_of_neg (R := S)
        (extendedAlternatingCechComplex (fun j ↦ algebraMap R S (f j)) (S ⊗[R] M)) hi)

/-- Helper for Lemma 15.90.9: the degree `-2` term of the cone of the module Čech comparison is
zero because both input complexes come from `ℕ`-indexed complexes by extension. -/
private theorem module_cech_mappingCone_negTwo_isZero
    (S : Type u) [CommRing S] [Algebra R S]
    (f : Fin t → R) (M : ModuleCat R)
    (φ : moduleCechComplexZ (R := R) f M ⟶
      moduleBaseChangedCechComplexZ (R := R) (S := S) f M) :
    IsZero ((CochainComplex.mappingCone φ).X (-2)) := by
  -- The cone term is the biproduct of the source degree `-1` term and the target degree `-2`
  -- term, and each of those vanishes separately.
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨moduleCechComplexZ_isZero_of_neg (R := R) f M (by omega),
    moduleBaseChangedCechComplexZ_isZero_of_neg (R := R) (S := S) f M (by omega)⟩

/-- Helper for Lemma 15.90.9: an acyclic mapping cone is available for every quasi-isomorphism of
`ℤ`-indexed cochain complexes of modules. -/
private theorem mappingCone_acyclic_of_quasiIso
    {K L : CochainComplex (ModuleCat R) ℤ} (φ : K ⟶ L) (hφ : QuasiIso φ) :
    (CochainComplex.mappingCone φ).Acyclic := by
  have hq :
      HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ)
        ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map φ) := by
    exact
      (HomotopyCategory.quotient_map_mem_quasiIso_iff
        (C := ModuleCat R) (c := ComplexShape.up ℤ) φ).2 hφ
  have hq' :
      (HomotopyCategory.subcategoryAcyclic (ModuleCat R)).trW
        ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map φ) := by
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := ModuleCat R)] using hq
  have hmem :
      HomotopyCategory.subcategoryAcyclic (ModuleCat R)
        ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone φ)) := by
    -- The standard mapping-cone triangle identifies the cone with the `trW` witness.
    simpa using
      ((HomotopyCategory.subcategoryAcyclic (ModuleCat R)).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh φ)
        (HomotopyCategory.mappingCone_triangleh_distinguished φ)).1 hq'
  exact
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (C := ModuleCat R) (CochainComplex.mappingCone φ)).1 hmem

/-- Helper for Lemma 15.90.9: if the degree `-2` term of a cochain complex vanishes, then
`H^{-1}` is canonically the kernel of the degree `-1` differential. -/
private noncomputable def homology_negOne_iso_kernel_of_isZero_X_negTwo
    (P : CochainComplex (ModuleCat R) ℤ) (hzero : IsZero (P.X (-2))) :
    P.homology (-1) ≅ ModuleCat.of R (LinearMap.ker ((P.d (-1) 0).hom)) := by
  let hprev : (ComplexShape.up ℤ).prev (-1 : ℤ) = (-2 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (-1 : ℤ))
  let hnext : (ComplexShape.up ℤ).next (-1 : ℤ) = (0 : ℤ) := by
    simpa using (CochainComplex.next ℤ (-1 : ℤ))
  let T : ShortComplex (ModuleCat R) := P.sc' (-2) (-1) 0
  let eCycles :
      P.homology (-1) ≅ P.cycles (-1) :=
    (P.isoHomologyπ (-2) (-1) (by simp) (hzero.eq_of_src (P.d (-2) (-1)) 0)).symm
  let eKernel :
      T.cycles ≅ ModuleCat.of R (LinearMap.ker ((P.d (-1) 0).hom)) := by
    -- On the owner short complex `T`, cycles are just the kernel of the outgoing differential.
    simpa [T, hnext] using
      (T.cyclesIsoKernel ≪≫ ModuleCat.kernelIsoKer T.g)
  -- First identify homology with cycles, then rewrite cycles through the owner short complex.
  exact eCycles ≪≫
    (P.cyclesIsoSc' (-2) (-1) 0 hprev hnext) ≪≫
      eKernel

/-- Helper for Lemma 15.90.9: vanishing of `H^0` forces exactness of the three-term slice
`P^{-1} ⟶ P^0 ⟶ P^1`. -/
private theorem sc'_exact_of_isZero_homology_zero
    (P : CochainComplex (ModuleCat R) ℤ) (hzero : IsZero (P.homology 0)) :
    (P.sc' (-1) 0 1).Exact := by
  let hprev : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (0 : ℤ))
  let hnext : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
    simpa using (CochainComplex.next ℤ (0 : ℤ))
  -- Transport the vanishing of ambient homology to the owner short complex at degree `0`.
  rw [ShortComplex.exact_iff_isZero_homology]
  exact IsZero.of_iso hzero (P.homologyIsoSc' (-1) 0 1 hprev hnext).symm

/-- Helper for Lemma 15.90.9: if the degree `-2` term is zero and `H^{-1}` vanishes, then the
left map of the slice `P^{-1} ⟶ P^0 ⟶ P^1` is injective. -/
private theorem sc'_mono_f_of_isZero_homology_negOne_of_isZero_X_negTwo
    (P : CochainComplex (ModuleCat R) ℤ)
    (hhomology : IsZero (P.homology (-1))) (hzero : IsZero (P.X (-2))) :
    Mono (P.sc' (-1) 0 1).f := by
  let hprev : (ComplexShape.up ℤ).prev (-1 : ℤ) = (-2 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (-1 : ℤ))
  let hnext : (ComplexShape.up ℤ).next (-1 : ℤ) = (0 : ℤ) := by
    simpa using (CochainComplex.next ℤ (-1 : ℤ))
  have hexactPrev : (P.sc' (-2) (-1) 0).Exact := by
    -- First turn the vanishing of `H^{-1}` into exactness of the preceding three-term slice.
    rw [ShortComplex.exact_iff_isZero_homology]
    exact IsZero.of_iso hhomology (P.homologyIsoSc' (-2) (-1) 0 hprev hnext).symm
  have hmonoPrev : Mono (P.sc' (-2) (-1) 0).g := by
    -- With zero source term, exactness of the previous slice is equivalent to monicity of its
    -- right map.
    exact ((P.sc' (-2) (-1) 0).exact_iff_mono (hzero.eq_of_src _ _)).1 hexactPrev
  simpa using hmonoPrev

/-- Helper for Lemma 15.90.9: if a `ℤ`-indexed cochain complex is acyclic and has zero term in
degree `-2`, then its slice `P^{-1} ⟶ P^0 ⟶ P^1` is exact with injective left map. -/
private theorem sc'_exact_mono_of_acyclic_of_isZero_X_negTwo
    (P : CochainComplex (ModuleCat R) ℤ)
    (hacyclic : P.Acyclic) (hzero : IsZero (P.X (-2))) :
    (P.sc' (-1) 0 1).Exact ∧ Mono (P.sc' (-1) 0 1).f := by
  have hzero0 : IsZero (P.homology 0) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hacyclic 0
  have hzeroNegOne : IsZero (P.homology (-1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hacyclic (-1)
  -- Read exactness from degree `0` homology and injectivity from degree `-1` homology.
  exact ⟨sc'_exact_of_isZero_homology_zero (R := R) P hzero0,
    sc'_mono_f_of_isZero_homology_negOne_of_isZero_X_negTwo
      (R := R) P hzeroNegOne hzero⟩

/-- Helper for Lemma 15.90.9: the missing source-faithful package is a quasi-isomorphic Čech
comparison whose cone slice is exactly the formal glueing short complex. -/
private theorem formal_glueing_cone_model
    (f : Fin t → R) (hflat : (algebraMap R S).Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    ∃ φ : moduleCechComplexZ (R := R) f M ⟶ moduleBaseChangedCechComplexZ (R := R) (S := S) f M,
      QuasiIso φ ∧
        ∃ e : formalGlueingModuleComplex S f M ≅ (CochainComplex.mappingCone φ).sc' (-1) 0 1,
          True := by
  -- Route correction: the direct module-homology comparison route would use the support/torsion
  -- API around `Lemma_15_29_5`, but importing that owner directly currently forces a broken
  -- dependency build in `Chap14/Lemma_14_28_6`. The remaining work is therefore still precisely
  -- the same source-faithful cone model: build the module-level Čech comparison and identify its
  -- `(-1,0,1)` cone slice with `formalGlueingModuleComplex`.
  -- TODO: construct the module-level Čech comparison by tensoring the ring comparison from
  -- `Lemma_15_90_4`, transport it through the tensor/base-change Čech isomorphisms, and then
  -- identify the degree `(-1,0,1)` cone slice with `formalGlueingModuleComplex`.
  sorry

-- Proof sketch: identify the displayed sequence with the truncation of the cone of the morphism
-- between the extended alternating Cech complexes for `R` and `S`. Lemma `15.90.4` gives that
-- morphism as a quasi-isomorphism, and flatness lets one tensor it with `M`. Equivalently, the
-- computational proof shows `Mono α` using the `I^∞`-torsion comparison map and proves
-- `ker β = range α` by reducing a compatible family to degree-one Koszul homology, then applying
-- Lemmas `15.90.2`, `15.90.3`, and `15.90.7`, yielding the canonical short-complex owner surface
-- `S.Exact ∧ Mono S.f`.
/-- Lemma 15.90.9: let `f : Fin t → R` generate the ideal `I = (f₁, …, fₜ)`. If `R → S` is flat
and the induced quotient map `R ⧸ I → S ⧸ IS` is bijective, then the formal glueing complex
`0 → M → (S ⊗[R] M) × ∏ i, M_{f_i} → ∏ i, (S ⊗[R] M)_{f_i} × ∏ i j, M_{f_i f_j}` is exact. In
this library-facing formulation, the overlap term `M_{f_i f_j}` is represented by iterated away
localizations, and the exactness statement is expressed by the owner pair
`(formalGlueingModuleComplex S f M).Exact ∧ Mono (formalGlueingModuleComplex S f M).f`. -/
theorem formalGlueingModuleComplex_exact_of_flat_of_quotientMap_bijective
    (f : Fin t → R) (hflat : (algebraMap R S).Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    (formalGlueingModuleComplex S f M).Exact ∧
      Mono (formalGlueingModuleComplex S f M).f :=
  by
  obtain ⟨φ, hφ, eφ, _⟩ :=
    formal_glueing_cone_model (R := R) (S := S) (M := M) f hflat hquot
  have hcone_acyclic :
      (CochainComplex.mappingCone φ).Acyclic :=
    mappingCone_acyclic_of_quasiIso (R := R) φ hφ
  have hcone_negTwo :
      IsZero ((CochainComplex.mappingCone φ).X (-2)) := by
    -- Both complexes in the cone model come from `ℕ`-indexed Čech complexes by extension.
    exact module_cech_mappingCone_negTwo_isZero (R := R) (S := S) f M φ
  have hcone :
      ((CochainComplex.mappingCone φ).sc' (-1) 0 1).Exact ∧
        Mono ((CochainComplex.mappingCone φ).sc' (-1) 0 1).f :=
    sc'_exact_mono_of_acyclic_of_isZero_X_negTwo
      (R := R) (CochainComplex.mappingCone φ) hcone_acyclic hcone_negTwo
  constructor
  · -- Transport exactness back across the cone-slice identification.
    exact (ShortComplex.exact_iff_of_iso eφ).2 hcone.1
  · -- Monicity is stable under the isomorphism of short complexes.
    refine (ModuleCat.mono_iff_injective _).2 ?_
    let hconeMono :
        Function.Injective
          ⇑(ModuleCat.Hom.hom ((CochainComplex.mappingCone φ).sc' (-1) 0 1).f) :=
      (ModuleCat.mono_iff_injective _).1 hcone.2
    let hτ₁Mono :
        Function.Injective ⇑(ModuleCat.Hom.hom eφ.hom.τ₁) :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    intro x y hxy
    have hx :
        ModuleCat.Hom.hom ((CochainComplex.mappingCone φ).sc' (-1) 0 1).f
            (ModuleCat.Hom.hom eφ.hom.τ₁ x) =
          ModuleCat.Hom.hom eφ.hom.τ₂
            (ModuleCat.Hom.hom (formalGlueingModuleComplex S f M).f x) := by
      simpa using
        LinearMap.congr_fun (congrArg ModuleCat.Hom.hom eφ.hom.comm₁₂) x
    have hy :
        ModuleCat.Hom.hom ((CochainComplex.mappingCone φ).sc' (-1) 0 1).f
            (ModuleCat.Hom.hom eφ.hom.τ₁ y) =
          ModuleCat.Hom.hom eφ.hom.τ₂
            (ModuleCat.Hom.hom (formalGlueingModuleComplex S f M).f y) := by
      simpa using
        LinearMap.congr_fun (congrArg ModuleCat.Hom.hom eφ.hom.comm₁₂) y
    have hconeEq :
        ModuleCat.Hom.hom ((CochainComplex.mappingCone φ).sc' (-1) 0 1).f
            (ModuleCat.Hom.hom eφ.hom.τ₁ x) =
          ModuleCat.Hom.hom ((CochainComplex.mappingCone φ).sc' (-1) 0 1).f
            (ModuleCat.Hom.hom eφ.hom.τ₁ y) := by
      calc
        ModuleCat.Hom.hom ((CochainComplex.mappingCone φ).sc' (-1) 0 1).f
            (ModuleCat.Hom.hom eφ.hom.τ₁ x) =
          ModuleCat.Hom.hom eφ.hom.τ₂
            (ModuleCat.Hom.hom (formalGlueingModuleComplex S f M).f x) := hx
        _ =
          ModuleCat.Hom.hom eφ.hom.τ₂
            (ModuleCat.Hom.hom (formalGlueingModuleComplex S f M).f y) := by
              simpa [hxy]
        _ =
          ModuleCat.Hom.hom ((CochainComplex.mappingCone φ).sc' (-1) 0 1).f
            (ModuleCat.Hom.hom eφ.hom.τ₁ y) := hy.symm
    exact hτ₁Mono <| hconeMono hconeEq

end
