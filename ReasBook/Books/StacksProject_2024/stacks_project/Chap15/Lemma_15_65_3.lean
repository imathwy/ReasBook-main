import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_5_3
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q

/- Helper layer for Lemma 15.65.3:
- the source-proof first identifies the top cycles of a bounded-above finite free complex with the
  top term itself, because the outgoing differential vanishes there;
- after that identification, the top homology is a quotient of those finite cycles via
  `homologyπ`.
-/

/-- Helper for Lemma 15.65.3: in the top degree of a bounded-above termwise finite free complex,
the cycles object is finite projective because the outgoing differential vanishes and
`HomologicalComplex.iCyclesIso` identifies cycles with the top term. -/
lemma finite_projective_cycles_top_of_isStrictlyLE
    {E : Cpx} [E.IsTermwiseFiniteFree] {b : ℤ} (hE : E.IsStrictlyLE b) :
    Module.Projective R (E.cycles b) ∧ Module.Finite R (E.cycles b) := by
  letI : E.IsStrictlyLE b := hE
  -- Above the top bound, the next term is zero, so the top differential is the zero map.
  have hzero : IsZero (E.X (b + 1)) := E.isZero_of_isStrictlyLE b (b + 1) (by omega)
  have hd : E.d b (b + 1) = 0 := hzero.eq_of_tgt _ _
  -- Identify top cycles with the top term and transport the finite/projective structure across
  -- that linear equivalence.
  let e : E.cycles b ≅ E.X b := HomologicalComplex.iCyclesIso E b (b + 1) (by simp) hd
  constructor
  · exact Module.Projective.of_equiv (R := R) (S := R) e.symm.toLinearEquiv
  · exact
      Module.Finite.of_surjective
        e.symm.toLinearEquiv.toLinearMap
        e.symm.toLinearEquiv.surjective

/-- Helper for Lemma 15.65.3: once a termwise finite free complex is supported in degrees `≤ m`,
its degree-`m` homology is finite because `homologyπ` is a quotient of the finite top cycles. -/
lemma homology_finite_of_termwiseFiniteFree_of_isStrictlyLE
    {E : Cpx} [E.IsTermwiseFiniteFree] {m : ℤ} (hE : E.IsStrictlyLE m) :
    Module.Finite R (E.homology m) := by
  -- First make the source-proof top-cycle identification explicit.
  have hcycles : Module.Finite R (E.cycles m) :=
    (finite_projective_cycles_top_of_isStrictlyLE (R := R) (E := E) hE).2
  -- Then pass to homology through the canonical quotient map from cycles.
  exact
    Module.Finite.of_surjective
      (E.homologyπ m).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- Helper for Lemma 15.65.3: the boundary submodule inside the cycle object of `E.sc i` is
finitely generated because it is the range of a map from the finite predecessor term. -/
lemma fg_range_moduleCatToCycles
    {E : Cpx} [E.IsTermwiseFiniteFree] (i : ℤ) :
    (LinearMap.range (E.sc i).moduleCatToCycles).FG := by
  let S : ShortComplex (ModuleCat R) := E.sc i
  letI : Module.Finite R S.X₁ := by
    -- The left term of `E.sc i` is the predecessor term of `E`, which is finite free.
    change Module.Finite R (E.X ((ComplexShape.up ℤ).prev i))
    infer_instance
  -- A range in a finite module is finitely generated.
  simpa [S] using Submodule.fg_range S.moduleCatToCycles

/-- Helper for Lemma 15.65.3: the cycle object of `E` in degree `i` is the concrete kernel module
used by the outgoing differential in degree `i`. -/
noncomputable abbrev cycles_iso_sc_kernel
    {E : Cpx} (i : ℤ) :
    E.cycles i ≅ ModuleCat.of R (LinearMap.ker (E.d i (i + 1)).hom) := by
  -- Route correction: first move from the chosen cycle object to the concrete kernel of `d^i`;
  -- the remaining `sc`-transport is then isolated to the quotient step.
  let hprev : (ComplexShape.up ℤ).prev i = i - 1 := by
    simpa using (CochainComplex.prev ℤ i)
  let hnext : (ComplexShape.up ℤ).next i = i + 1 := by
    simpa [add_assoc] using (CochainComplex.next ℤ i)
  let S : ShortComplex (ModuleCat R) := E.sc' (i - 1) i (i + 1)
  let eKernel :
      S.cycles ≅ ModuleCat.of R (LinearMap.ker (E.d i (i + 1)).hom) := by
    simpa [S, hnext] using
      (S.cyclesIsoKernel ≪≫ ModuleCat.kernelIsoKer S.g)
  exact (E.cyclesIsoSc' (i - 1) i (i + 1) hprev hnext) ≪≫ eKernel

/-- Helper for Lemma 15.65.3: before replacing `next i` by `i + 1`, the owner short complex
already has the concrete outgoing kernel expected from the differential in degree `i`. -/
lemma sc_g_kernel_eq_d_next_kernel
    {E : Cpx} (i : ℤ) :
    LinearMap.ker (E.sc i).g.hom = LinearMap.ker (E.d i ((ComplexShape.up ℤ).next i)).hom := by
  -- `HomologicalComplex.sc` defines the right map to be the outgoing differential itself.
  rfl

/-- Helper for Lemma 15.65.3: the owner short complex `E.sc i` uses the same concrete outgoing
kernel as the differential `d^i`. -/
noncomputable abbrev sc_kernel_iso_d_kernel
    {E : Cpx} (i : ℤ) :
    ModuleCat.of R (LinearMap.ker (E.d i (i + 1)).hom) ≅
      ModuleCat.of R (LinearMap.ker (E.sc i).g.hom) :=
by
  -- Normalize the owner `g`-kernel by replacing `next i` with the concrete index `i + 1`.
  have hnext : (ComplexShape.up ℤ).next i = i + 1 := by
    simpa [add_assoc] using (CochainComplex.next ℤ i)
  have hker :
      LinearMap.ker (E.sc i).g.hom = LinearMap.ker (E.d i (i + 1)).hom := by
    rw [sc_g_kernel_eq_d_next_kernel (E := E) i, hnext]
  -- Package the resulting equality of kernel submodules as the required module isomorphism.
  exact (LinearEquiv.ofEq _ _ hker.symm).toModuleIso

/-- Helper for Lemma 15.65.3: the codomain restriction defining `moduleCatToCycles` does not
change the concrete kernel, so its kernel agrees with the kernel of the owner left map. -/
noncomputable abbrev sc_moduleCatToCycles_kernel_iso_f_kernel
    {E : Cpx} (j : ℤ) :
    ModuleCat.of R (LinearMap.ker (E.sc j).moduleCatToCycles) ≅
      ModuleCat.of R (LinearMap.ker (E.sc j).f.hom) :=
by
  -- The codomain restriction keeps the same underlying linear map on elements, so kernel
  -- membership is unchanged.
  have hker :
      LinearMap.ker (E.sc j).moduleCatToCycles = LinearMap.ker (E.sc j).f.hom := by
    ext x
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      ext
      exact hx
  -- Turn the kernel equality into the corresponding module isomorphism.
  exact (LinearEquiv.ofEq _ _ hker).toModuleIso

/-- Helper for Lemma 15.65.3: changing the source index of a differential along an equality
transports its concrete kernel module without changing the underlying vectors. -/
noncomputable abbrev d_kernel_iso_of_source_eq
    {E : Cpx} {i i' j : ℤ} (h : i = i') :
    ModuleCat.of R (LinearMap.ker (E.d i j).hom) ≅
      ModuleCat.of R (LinearMap.ker (E.d i' j).hom) :=
by
  -- Route correction: isolate the source-index cast on kernels before re-entering the owner
  -- short-complex proof, so later compositions never rewrite dependent subtype kernels in place.
  subst h
  exact (LinearEquiv.refl R _).toModuleIso

/-- Helper for Lemma 15.65.3: changing the target index of a differential along an equality
transports its concrete kernel module without changing the underlying vectors. -/
noncomputable abbrev d_kernel_iso_of_target_eq
    {E : Cpx} {i j j' : ℤ} (h : j = j') :
    ModuleCat.of R (LinearMap.ker (E.d i j).hom) ≅
      ModuleCat.of R (LinearMap.ker (E.d i j').hom) :=
by
  -- This isolates the target-index cast needed to normalize `((j - 1) + 1) = j` on cycles.
  subst h
  exact (LinearEquiv.refl R _).toModuleIso

/-- Helper for Lemma 15.65.3: the owner left map of `E.sc j` is exactly the predecessor
differential after normalizing `prev j = j - 1`. -/
noncomputable abbrev sc_f_kernel_iso_prev_d_kernel
    {E : Cpx} (j : ℤ) :
    ModuleCat.of R (LinearMap.ker (E.sc j).f.hom) ≅
      ModuleCat.of R (LinearMap.ker (E.d (j - 1) j).hom) :=
by
  -- The owner short complex stores the incoming differential from the predecessor degree.
  have hprev : (ComplexShape.up ℤ).prev j = j - 1 := by
    simpa using (CochainComplex.prev ℤ j)
  -- First expose the definitional predecessor differential in `(E.sc j).f`.
  change ModuleCat.of R (LinearMap.ker (E.d ((ComplexShape.up ℤ).prev j) j).hom) ≅
      ModuleCat.of R (LinearMap.ker (E.d (j - 1) j).hom)
  -- Then transport the kernel along the normalized predecessor-index equality.
  exact d_kernel_iso_of_source_eq (R := R) (E := E) (j := j) hprev

/-- Helper for Lemma 15.65.3: the short-complex homology object of `E.sc i` is the cochain
homology object of `E` in degree `i`. -/
noncomputable abbrev sc_homology_iso_homology
    {E : Cpx} (i : ℤ) :
    (E.sc i).homology ≅ E.homology i :=
  -- This comparison is definitional: `E.homology i` is the homology of the owner short complex.
  Iso.refl _

/-- Helper for Lemma 15.65.3: the owner quotient object `leftHomology` of `E.sc i` agrees with
the cochain homology of `E` in degree `i`. -/
noncomputable abbrev sc_leftHomology_iso_homology
    {E : Cpx} (i : ℤ) :
    (E.sc i).leftHomology ≅ E.homology i :=
  -- First identify `leftHomology` with the explicit quotient by boundaries, then compare that
  -- quotient with the abstract short-complex homology and hence with `E.homology i`.
  (E.sc i).moduleCatLeftHomologyData.leftHomologyIso ≪≫ ((E.sc i).moduleCatHomologyIso).symm

/-- Helper for Lemma 15.65.3: the derived homology of a cochain complex is computed by its
ordinary cochain homology on the chosen representative. -/
noncomputable abbrev derived_homology_iso
    (K : Cpx) (i : ℤ) :
    (H i).obj (Q.obj K) ≅ K.homology i :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K

/-- Helper for Lemma 15.65.3: a morphism in the derived category induces the expected map on the
ordinary homology of chosen cochain representatives. -/
noncomputable abbrev homology_map_of_derived_map
    {E K : Cpx} (α : Q.obj E ⟶ Q.obj K) (i : ℤ) :
    E.homology i ⟶ K.homology i :=
  (derived_homology_iso (R := R) E i).inv ≫ (H i).map α ≫ (derived_homology_iso (R := R) K i).hom

/-- Helper for Lemma 15.65.3: if a derived morphism is an isomorphism on degree-`i` homology,
then the same is true on the ordinary homology of the chosen representatives. -/
noncomputable abbrev homology_iso_of_derived_map
    {E K : Cpx} (α : Q.obj E ⟶ Q.obj K) (i : ℤ) [IsIso ((H i).map α)] :
    E.homology i ≅ K.homology i :=
  (derived_homology_iso (R := R) E i).symm ≪≫ asIso ((H i).map α) ≪≫
    derived_homology_iso (R := R) K i

/-- Helper for Lemma 15.65.3: the concrete quotient by the owner boundary range is always
surjective. -/
lemma mkQ_surjective_range_moduleCatToCycles
    (S : ShortComplex (ModuleCat R)) :
    Function.Surjective (Submodule.mkQ (LinearMap.range S.moduleCatToCycles)) :=
  Submodule.mkQ_surjective _

/-- Helper for Lemma 15.65.3: the kernel of the owner map `moduleCatToCycles` is the concrete
kernel of the predecessor differential after rewriting `prev j = j - 1`. -/
noncomputable abbrev sc_moduleCatToCycles_kernel_iso_prev_d_kernel
    {E : Cpx} (j : ℤ) :
    ModuleCat.of R (LinearMap.ker (E.sc j).moduleCatToCycles) ≅
      ModuleCat.of R (LinearMap.ker (E.d (j - 1) j).hom) :=
by
  -- Route correction: split the transport into the codRestrict-kernel comparison and the
  -- predecessor-index normalization, so no single helper mixes both coercions.
  exact
    sc_moduleCatToCycles_kernel_iso_f_kernel (R := R) (E := E) j ≪≫
      sc_f_kernel_iso_prev_d_kernel (R := R) (E := E) j

/-- Helper for Lemma 15.65.3: the previous cycles object is the kernel of the owner boundary map
`(E.sc j).moduleCatToCycles`, so the descent step can stay on the owner short complex. -/
noncomputable abbrev cycles_prev_iso_kernel_moduleCatToCycles
    {E : Cpx} (j : ℤ) :
    E.cycles (j - 1) ≅ ModuleCat.of R (LinearMap.ker (E.sc j).moduleCatToCycles) :=
by
  -- Route correction: separate the predecessor-differential kernel from the owner codRestrict
  -- kernel, then compose the two canonical identifications.
  have htarget : (j - 1) + 1 = j := by omega
  -- First identify the previous cycles with the predecessor differential kernel.
  refine
    cycles_iso_sc_kernel (R := R) (E := E) (j - 1) ≪≫
      d_kernel_iso_of_target_eq (R := R) (E := E) (i := j - 1) htarget ≪≫ ?_
  -- Then move from the differential kernel to the owner kernel in the reverse direction.
  exact (sc_moduleCatToCycles_kernel_iso_prev_d_kernel (R := R) (E := E) j).symm

/-- Helper for Lemma 15.65.3: vanishing of `H^j(E)` forces the owner boundary map
`(E.sc j).moduleCatToCycles` to be surjective onto the degree-`j` cycles. -/
lemma sc_moduleCatToCycles_surjective_of_isZero_homology
    {E : Cpx} {j : ℤ} (hj : IsZero (E.homology j)) :
    Function.Surjective (E.sc j).moduleCatToCycles := by
  -- The vanishing hypothesis is exactly the exactness of the owner short complex at degree `j`.
  have hexact : (E.sc j).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    simpa using hj
  exact (ShortComplex.exact_iff_surjective_moduleCatToCycles (S := E.sc j)).1 hexact

/-- Helper for Lemma 15.65.3: a section `σ` of `s` produces elements of `ker s` by subtracting
the split image `σ (s x)`. -/
lemma sub_section_apply_mem_ker
    {M P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (s : M →ₗ[R] P) (σ : P →ₗ[R] M) (hσ : s.comp σ = LinearMap.id) (x : M) :
    x - σ (s x) ∈ LinearMap.ker s := by
  -- Applying `s` cancels the correction term because `σ` is a right inverse.
  rw [LinearMap.mem_ker]
  rw [map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]

/-- Helper for Lemma 15.65.3: a section of `s` induces a retraction from the source onto
`ker s`. -/
def kernel_retraction_of_section
    {M P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (s : M →ₗ[R] P) (σ : P →ₗ[R] M) (hσ : s.comp σ = LinearMap.id) :
    M →ₗ[R] LinearMap.ker s :=
  (LinearMap.id - σ.comp s).codRestrict (LinearMap.ker s)
    (sub_section_apply_mem_ker (R := R) s σ hσ)

/-- Helper for Lemma 15.65.3: the kernel retraction associated to a section is the identity on
the kernel subtype. -/
lemma kernel_retraction_of_section_comp_subtype
    {M P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (s : M →ₗ[R] P) (σ : P →ₗ[R] M) (hσ : s.comp σ = LinearMap.id) :
    (kernel_retraction_of_section (R := R) s σ hσ).comp (LinearMap.ker s).subtype = LinearMap.id :=
by
  -- On a kernel element the correction term vanishes, so the retraction returns the same element.
  ext x
  simp [kernel_retraction_of_section, sub_eq_add_neg, LinearMap.comp_apply]

/-- Helper for Lemma 15.65.3: if the degree-`j` cycles are finite projective and `H^j(E)` is
zero, then the previous cycles object is the kernel of a split surjection from a finite free term,
hence is again finite projective. -/
lemma finite_projective_cycles_prev_of_isZero_homology
    {E : Cpx} [E.IsTermwiseFiniteFree] {j : ℤ}
    (hcycles : Module.Projective R (E.cycles j) ∧ Module.Finite R (E.cycles j))
    (hj : IsZero (E.homology j)) :
    Module.Projective R (E.cycles (j - 1)) ∧ Module.Finite R (E.cycles (j - 1)) := by
  let S : ShortComplex (ModuleCat R) := E.sc j
  letI : Module.Projective R (E.cycles j) := hcycles.1
  let eCyclesToConcrete :
      E.cycles j ≅ ModuleCat.of R (LinearMap.ker S.g.hom) := by
    -- The owner short complex computes the same cycles object in degree `j`.
    simpa [S] using S.moduleCatCyclesIso
  letI : Module.Projective R (LinearMap.ker S.g.hom) :=
    Module.Projective.of_equiv eCyclesToConcrete.toLinearEquiv
  let π : S.X₁ ⟶ ModuleCat.of R (LinearMap.ker S.g.hom) := ModuleCat.ofHom S.moduleCatToCycles
  have hsurj_cycles : Function.Surjective π.hom := by
    simpa [π, S] using sc_moduleCatToCycles_surjective_of_isZero_homology (R := R) (E := E) hj
  letI : Epi π := (ModuleCat.epi_iff_surjective _).2 hsurj_cycles
  let σ : ModuleCat.of R (LinearMap.ker S.g.hom) ⟶ S.X₁ :=
    Projective.factorThru (𝟙 _) π
  have hσ_cat : σ ≫ π = 𝟙 _ := by
    -- The projective lift is a genuine section of the surjection `π`.
    exact Projective.factorThru_comp (𝟙 (ModuleCat.of R (LinearMap.ker S.g.hom))) π
  have hσ : π.hom.comp σ.hom = LinearMap.id := by
    -- Splitting the surjection gives a right inverse on the concrete cycles module.
    simpa using congrArg ModuleCat.Hom.hom hσ_cat
  let r : S.X₁ →ₗ[R] LinearMap.ker S.moduleCatToCycles :=
    kernel_retraction_of_section (R := R) S.moduleCatToCycles σ.hom (by simpa [π] using hσ)
  have hr : r.comp (LinearMap.ker S.moduleCatToCycles).subtype = LinearMap.id := by
    -- The subtraction correction vanishes on the kernel subtype, so this is a genuine retraction.
    exact kernel_retraction_of_section_comp_subtype (R := R) S.moduleCatToCycles σ.hom
      (by simpa [π] using hσ)
  letI : Module.Projective R S.X₁ := by
    change Module.Projective R (E.X ((ComplexShape.up ℤ).prev j))
    infer_instance
  have hprojective_ker : Module.Projective R (LinearMap.ker S.moduleCatToCycles) :=
    Module.Projective.of_split (LinearMap.ker S.moduleCatToCycles).subtype r hr
  letI : Module.Finite R S.X₁ := by
    change Module.Finite R (E.X ((ComplexShape.up ℤ).prev j))
    infer_instance
  have hsurj_r : Function.Surjective r := by
    intro x
    refine ⟨x, ?_⟩
    simpa using LinearMap.congr_fun hr x
  have hfinite_ker : Module.Finite R (LinearMap.ker S.moduleCatToCycles) :=
    Module.Finite.of_surjective r hsurj_r
  let Sprev : ShortComplex (ModuleCat R) := E.sc (j - 1)
  let ePrev :
      E.cycles (j - 1) ≅ ModuleCat.of R (LinearMap.ker S.moduleCatToCycles) := by
    -- Route correction: rebuild the predecessor-cycles bridge via the owner cycles kernel of
    -- `E.sc (j - 1)`, then normalize the outgoing kernel and finally the owner `moduleCatToCycles`
    -- kernel for `E.sc j`.
    let ePrevConcrete :
        E.cycles (j - 1) ≅ ModuleCat.of R (LinearMap.ker Sprev.g.hom) := by
      simpa [Sprev] using Sprev.moduleCatCyclesIso
    let ePrevDifferential :
        ModuleCat.of R (LinearMap.ker Sprev.g.hom) ≅
          ModuleCat.of R (LinearMap.ker (E.d (j - 1) ((j - 1) + 1)).hom) :=
      (sc_kernel_iso_d_kernel (R := R) (E := E) (j - 1)).symm
    have htarget : (j - 1) + 1 = j := by omega
    let ePrevTarget :
        ModuleCat.of R (LinearMap.ker (E.d (j - 1) ((j - 1) + 1)).hom) ≅
          ModuleCat.of R (LinearMap.ker (E.d (j - 1) j).hom) :=
      d_kernel_iso_of_target_eq (R := R) (E := E) (i := j - 1) htarget
    let ePrevKernel :
        ModuleCat.of R (LinearMap.ker (E.d (j - 1) j).hom) ≅
          ModuleCat.of R (LinearMap.ker S.moduleCatToCycles) := by
      simpa [S] using
        (sc_moduleCatToCycles_kernel_iso_prev_d_kernel (R := R) (E := E) j).symm
    exact ePrevConcrete ≪≫ ePrevDifferential ≪≫ ePrevTarget ≪≫ ePrevKernel
  constructor
  · -- Transport projectivity from the split kernel back to the previous cycles object.
    exact Module.Projective.of_equiv ePrev.symm.toLinearEquiv
  · -- Transport finite generation across the same identification of previous cycles.
    exact Module.Finite.equiv ePrev.symm.toLinearEquiv

/-- Helper for Lemma 15.65.3: bounded-above descent on the width `Int.toNat (b - j)` transports
finite/projective cycles from the top degree `b` down to degree `j`. -/
lemma finite_projective_cycles_descend_from_top_aux
    {E : Cpx} [E.IsTermwiseFiniteFree] :
    ∀ n : ℕ, ∀ {j b : ℤ}, Int.toNat (b - j) = n → j ≤ b → E.IsStrictlyLE b →
      (∀ i : ℤ, j < i → IsZero (E.homology i)) →
      Module.Projective R (E.cycles j) ∧ Module.Finite R (E.cycles j)
  | 0, j, b, hn, hjb, hE, _ => by
      -- Base case: zero width forces `j = b`, so the top-cycle argument applies directly.
      have hwidth : b - j = 0 := by
        rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hjb)]
        exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
      have hjb_eq : j = b := by
        omega
      subst j
      simpa using
        finite_projective_cycles_top_of_isStrictlyLE (R := R) (E := E) hE
  | n + 1, j, b, hn, hjb, hE, hvanish => by
      -- Route correction: package the source-proof descent as induction on the global width
      -- `Int.toNat (b - j)`, so the predecessor step only uses the degree-`j + 1` vanishing.
      have hwidth : b - j = ((n + 1 : ℕ) : ℤ) := by
        rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hjb)]
        exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
      have hjltb : j < b := by
        omega
      have hj1b : j + 1 ≤ b := by
        omega
      have hn' : Int.toNat (b - (j + 1)) = n := by
        rw [show b - (j + 1) = (n : ℤ) by omega]
        simp
      have hvanish' : ∀ i : ℤ, j + 1 < i → IsZero (E.homology i) := by
        intro i hi
        exact hvanish i (by omega)
      have hcycles_succ :
          Module.Projective R (E.cycles (j + 1)) ∧ Module.Finite R (E.cycles (j + 1)) :=
        finite_projective_cycles_descend_from_top_aux (E := E) n
          (j := j + 1) (b := b) hn' hj1b hE hvanish'
      have hj1 : IsZero (E.homology (j + 1)) := by
        exact hvanish (j + 1) (by omega)
      -- One predecessor step turns finite/projective cycles in degree `j + 1` into the same
      -- statement in degree `j`.
      have hprev :
          Module.Projective R (E.cycles ((j + 1) - 1)) ∧
            Module.Finite R (E.cycles ((j + 1) - 1)) :=
        finite_projective_cycles_prev_of_isZero_homology
          (R := R) (E := E) hcycles_succ hj1
      have hjpred : j = (j + 1) - 1 := by
        omega
      rw [hjpred]
      exact hprev

/-- Helper for Lemma 15.65.3: descending exactness from the top finite-free term shows that the
cycle object in every degree `j` below the chosen upper bound is finite projective once all
cohomology above `j` vanishes. -/
lemma finite_projective_cycles_of_isStrictlyLE_of_isZero_homology_gt
    {E : Cpx} [E.IsTermwiseFiniteFree] {j b : ℤ}
    (hE : E.IsStrictlyLE b) (hjb : j ≤ b)
    (hvanish : ∀ i : ℤ, j < i → IsZero (E.homology i)) :
    Module.Projective R (E.cycles j) ∧ Module.Finite R (E.cycles j) := by
  -- The bounded-above source proof is now packaged as a width induction from `b` down to `j`.
  exact
    finite_projective_cycles_descend_from_top_aux (R := R) (E := E)
      (Int.toNat (b - j)) rfl hjb hE hvanish

/-- Helper for Lemma 15.65.3: finite projective top cycles make the top homology finitely
presented, because `homologyπ` is the quotient of those cycles by the finitely generated image of
the previous differential. -/
lemma homology_finitePresentation_of_finite_projective_cycles
    {E : Cpx} [E.IsTermwiseFiniteFree] {i : ℤ}
    (hcycles : Module.Projective R (E.cycles i) ∧ Module.Finite R (E.cycles i)) :
    Module.FinitePresentation R (E.homology i) := by
  let S : ShortComplex (ModuleCat R) := E.sc i
  -- Install the finite/projective structure on the owner cycles object.
  letI : Module.Projective R S.cycles := by
    simpa [S] using hcycles.1
  letI : Module.Finite R S.cycles := by
    simpa [S] using hcycles.2
  have hfp_cycles : Module.FinitePresentation R S.cycles :=
    Module.finitePresentation_of_projective R S.cycles
  -- Transport finite presentation to the concrete kernel module used by `moduleCatToCycles`.
  letI : Module.FinitePresentation R (LinearMap.ker S.g.hom) :=
    Module.FinitePresentation.of_equiv S.moduleCatCyclesIso.toLinearEquiv
  letI : Module.FinitePresentation R S.moduleCatLeftHomologyData.K := by
    change Module.FinitePresentation R (LinearMap.ker S.g.hom)
    infer_instance
  have hfg_kernel :
      Submodule.FG (LinearMap.ker S.moduleCatLeftHomologyData.π.hom) := by
    -- The quotient kernel is exactly the range of the previous differential.
    change Submodule.FG (LinearMap.ker ((LinearMap.range S.moduleCatToCycles).mkQ))
    simpa [Submodule.ker_mkQ] using
      (fg_range_moduleCatToCycles (R := R) (E := E) i)
  have hfp_quotient : Module.FinitePresentation R S.moduleCatLeftHomologyData.H :=
    Module.finitePresentation_of_surjective S.moduleCatLeftHomologyData.π.hom
      (mkQ_surjective_range_moduleCatToCycles S) hfg_kernel
  -- Move the finitely presented quotient back through the owner left-homology and homology isos.
  letI : Module.FinitePresentation R S.leftHomology :=
    Module.FinitePresentation.of_equiv S.moduleCatLeftHomologyData.leftHomologyIso.symm.toLinearEquiv
  exact
    Module.FinitePresentation.of_equiv
      (sc_leftHomology_iso_homology (R := R) (E := E) i).toLinearEquiv

-- Proof sketch: choose a bounded-above finite-projective approximation `E^• ⟶ K^•` from the
-- definition of `m`-pseudo-coherence. Under the stated vanishing hypotheses, replace `E^•` by a
-- bounded finite-projective complex, peel off the top nonzero term inductively, and identify the
-- surviving top cohomology as a quotient of a finite module in degree `m` and as a cokernel of a
-- map between finite projectives in degree `m + 1`.
/-- Lemma 15.65.3: if an `R`-module cochain complex `K^•` is `m`-pseudo-coherent, then vanishing
of `H^i(K^•)` for `i > m` implies that `H^m(K^•)` is a finite `R`-module, and vanishing of
`H^i(K^•)` for `i > m + 1` implies that `H^{m + 1}(K^•)` is finitely presented. -/
theorem homology_finite_and_finitePresentation_of_isMPseudoCoherent
    {K : Cpx} {m : ℤ} (hK : K.IsMPseudoCoherent m) :
    ((∀ i : ℤ, m < i → IsZero (K.homology i)) → Module.Finite R (K.homology m)) ∧
      ((∀ i : ℤ, m + 1 < i → IsZero (K.homology i)) →
        Module.FinitePresentation R (K.homology (m + 1))) := by
  rcases hK with ⟨E, ⟨a, b, hEge, hEle⟩, hEfree, α, hαiso, hαepi⟩
  letI : E.IsTermwiseFiniteFree := hEfree
  constructor
  · intro hvanishK
    have hfiniteE : Module.Finite R (E.homology m) := by
      by_cases hmb : m ≤ b
      · -- Inside the bounded-above window, descend the finite/projective cycles to degree `m`.
        have hvanishE : ∀ i : ℤ, m < i → IsZero (E.homology i) := by
          intro i hi
          letI : IsIso ((H i).map α) := hαiso i hi
          exact (homology_iso_of_derived_map (R := R) α i).isZero_iff.2 (hvanishK i hi)
        have hcycles :
            Module.Projective R (E.cycles m) ∧ Module.Finite R (E.cycles m) :=
          finite_projective_cycles_of_isStrictlyLE_of_isZero_homology_gt
            (R := R) (E := E) hEle hmb hvanishE
        letI : Module.Finite R (E.cycles m) := hcycles.2
        -- Homology is the quotient of cycles by boundaries.
        exact Module.Finite.of_surjective (E.homologyπ m).hom
          ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      · have hbm : b < m := by omega
        have hEm : E.IsStrictlyLE m := by
          letI : E.IsStrictlyLE b := hEle
          rw [CochainComplex.isStrictlyLE_iff]
          intro i hi
          exact E.isZero_of_isStrictlyLE b i (lt_trans hbm hi)
        -- Above the chosen support bound, the top-degree quotient argument applies directly.
        exact homology_finite_of_termwiseFiniteFree_of_isStrictlyLE (R := R) (E := E) hEm
    let β : E.homology m ⟶ K.homology m := homology_map_of_derived_map (R := R) α m
    have hβsurj : Function.Surjective β.hom := (ModuleCat.epi_iff_surjective _).1 inferInstance
    -- Transport finiteness across the epimorphism provided by the pseudo-coherent witness.
    exact Module.Finite.of_surjective β.hom hβsurj
  · intro hvanishK
    have hfpE : Module.FinitePresentation R (E.homology (m + 1)) := by
      by_cases hm1b : m + 1 ≤ b
      · -- In degree `m + 1`, descending finite/projective cycles makes homology finitely presented.
        have hvanishE : ∀ i : ℤ, m + 1 < i → IsZero (E.homology i) := by
          intro i hi
          have hmi : m < i := by omega
          letI : IsIso ((H i).map α) := hαiso i hmi
          exact (homology_iso_of_derived_map (R := R) α i).isZero_iff.2 (hvanishK i hi)
        have hcycles :
            Module.Projective R (E.cycles (m + 1)) ∧ Module.Finite R (E.cycles (m + 1)) :=
          finite_projective_cycles_of_isStrictlyLE_of_isZero_homology_gt
            (R := R) (E := E) hEle hm1b hvanishE
        exact homology_finitePresentation_of_finite_projective_cycles
          (R := R) (E := E) hcycles
      · have hbm1 : b < m + 1 := by omega
        have hEm1 : E.IsStrictlyLE (m + 1) := by
          letI : E.IsStrictlyLE b := hEle
          rw [CochainComplex.isStrictlyLE_iff]
          intro i hi
          exact E.isZero_of_isStrictlyLE b i (lt_trans hbm1 hi)
        have hcycles :
            Module.Projective R (E.cycles (m + 1)) ∧ Module.Finite R (E.cycles (m + 1)) :=
          finite_projective_cycles_top_of_isStrictlyLE (R := R) (E := E) hEm1
        -- Once the complex is already zero above `m + 1`, the top-cycle presentation applies.
        exact homology_finitePresentation_of_finite_projective_cycles
          (R := R) (E := E) hcycles
    have hmIso : m < m + 1 := by omega
    letI : IsIso ((H (m + 1)).map α) := hαiso (m + 1) hmIso
    let e : E.homology (m + 1) ≅ K.homology (m + 1) :=
      homology_iso_of_derived_map (R := R) α (m + 1)
    -- The witness is an isomorphism on degree `m + 1`, so finite presentation transfers across it.
    exact Module.FinitePresentation.of_equiv e.toLinearEquiv

-- Proof sketch: apply the first component of
-- `homology_finite_and_finitePresentation_of_isMPseudoCoherent` to the given vanishing range.
/-- The top surviving cohomology of an `m`-pseudo-coherent complex is finite when all higher
cohomology vanishes. -/
theorem homology_finite_of_isMPseudoCoherent
    {K : Cpx} {m : ℤ} (hK : K.IsMPseudoCoherent m)
    (hvanish : ∀ i : ℤ, m < i → IsZero (K.homology i)) :
    Module.Finite R (K.homology m) := by
  -- Project the first clause of the main theorem and apply it to the given vanishing range.
  exact (homology_finite_and_finitePresentation_of_isMPseudoCoherent hK).1 hvanish

-- Proof sketch: apply the second component of
-- `homology_finite_and_finitePresentation_of_isMPseudoCoherent` to the stronger vanishing range
-- above degree `m + 1`.
/-- The next cohomology of an `m`-pseudo-coherent complex is finitely presented when all
cohomology above degree `m + 1` vanishes. -/
theorem homology_finitePresentation_of_isMPseudoCoherent
    {K : Cpx} {m : ℤ} (hK : K.IsMPseudoCoherent m)
    (hvanish : ∀ i : ℤ, m + 1 < i → IsZero (K.homology i)) :
    Module.FinitePresentation R (K.homology (m + 1)) := by
  -- Project the second clause of the main theorem and apply it to the stated vanishing range.
  exact (homology_finite_and_finitePresentation_of_isMPseudoCoherent hK).2 hvanish

end CochainComplex
