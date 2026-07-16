import Mathlib.LinearAlgebra.TensorProduct.Tower
import stacks_proof.stacks_project.Chap15.Lemma_15_96_10
import stacks_proof.stacks_project.Chap15.Lemma_15_97_3
import stacks_proof.stacks_project.Chap15.Lemma_15_97_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open BerthelotOgusEtaReduction.Nat
open scoped nonZeroDivisors
open scoped TensorProduct

noncomputable section

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "CpxA" => NatModuleCochainComplex A
local notation "baseChange" =>
  Functor.mapHomologicalComplex (ModuleCat.extendScalars (algebraMap A B)) (up ℕ)

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendScalarsTermLinearEquiv
    (K : CpxA) (i : ℕ) :
    ((((baseChange).obj K).X i : ModuleCat B)) ≃ₗ[B] (B ⊗[A] (K.X i)) := by
  simpa [Functor.mapHomologicalComplex_obj_X, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl A (K.X i)))

private theorem etaFDegreeSubmodule_toBaseChange_bijective
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    Function.Bijective ((etaFDegreeSubmodule f M i).toBaseChange B) := by
  -- The tensor of a submodule is canonically identified with its base change.
  simpa using
    (Submodule.toBaseChange.toLinearEquiv B (etaFDegreeSubmodule f M i)).bijective

/-- Helper for Lemma 15.97.6: the nat-indexed determinantal ideal of the base-changed complex is
the image of the source determinantal ideal under `A → B`. -/
private theorem eta_determinantal_ideal_base_change_nat
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (i : ℕ) :
    (((baseChange).obj M).etaDeterminantalIdeal (algebraMap A B f) i) =
      Ideal.map (algebraMap A B) (M.etaDeterminantalIdeal f i) := by
  -- Rewrite the nat-indexed owner through extension by zero and apply Lemma 15.97.3 in degree
  -- `(i : ℤ)`.
  simpa [NatModuleCochainComplex.etaDeterminantalIdeal, baseChange] using
    (etaDeterminantalIdeal_baseChange (A := A) (B := B) (f := f)
      (M := M.extend embeddingUpNat) (i := (i : ℤ)))

/-- Helper for Lemma 15.97.6: on the tensor-product model, multiplying by the image of `a`
is exactly the base change of multiplication by `a`. -/
private theorem tensor_lsmul_eq_baseChange_lsmul
    {N : Type u} [AddCommGroup N] [Module A N] (a : A) :
    LinearMap.lsmul B (B ⊗[A] N) (algebraMap A B a) =
      (LinearMap.lsmul A N a).baseChange B := by
  -- Proof comment: both maps agree on pure tensors, so tensor induction identifies them globally.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro b x
    simp [LinearMap.baseChange_tmul, LinearMap.lsmul_apply, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
  · intro x y hx hy
    simp [hx, hy]

/-- Helper for Lemma 15.97.6: after the standard scalar-extension identification in degree `n`,
the tensorized submodule `f^n M^n` becomes `g^n (M^n ⊗_A B)` for `g = algebraMap A B f`. -/
private theorem powerSubmodule_baseChange_map_eq
    (f : A) (M : CpxA) (n : ℕ) :
    ((powerSubmodule f M n).baseChange B).map
        ((extendScalarsTermLinearEquiv M n).symm.toLinearMap) =
      powerSubmodule (algebraMap A B f) ((baseChange).obj M) n := by
  let e := extendScalarsTermLinearEquiv M n
  let μA : M.X n →ₗ[A] M.X n := LinearMap.lsmul A (M.X n) (f ^ n)
  let μB :
      ((((baseChange).obj M).X n : ModuleCat B)) →ₗ[B] (((baseChange).obj M).X n : ModuleCat B) :=
    LinearMap.lsmul B ((((baseChange).obj M).X n : ModuleCat B)) ((algebraMap A B f) ^ n)
  have hconj :
      e.symm.toLinearMap.comp (μA.baseChange B) = μB.comp e.symm.toLinearMap := by
    -- Proof comment: transport the tensorized source multiplication map through the ambient
    -- scalar-extension equivalence, then rewrite `algebraMap (f ^ n)` as `g ^ n`.
    apply LinearMap.ext
    intro z
    apply e.injective
    simp [LinearMap.comp_apply, μB]
    rw [← map_pow]
    simpa [μA] using
      congrArg (fun φ : B ⊗[A] M.X n →ₗ[B] B ⊗[A] M.X n ↦ φ z)
        (tensor_lsmul_eq_baseChange_lsmul (A := A) (B := B) (N := M.X n) (a := f ^ n)).symm
  have hsurj :
      LinearMap.range (e.symm.toLinearMap) = ⊤ := by
    -- Proof comment: a linear equivalence is surjective, so its range is all of the target term.
    rw [LinearMap.range_eq_top]
    exact e.symm.surjective
  -- Proof comment: rewrite both power submodules as ranges of multiplication maps and transport
  -- those ranges across the scalar-extension equivalence.
  rw [powerSubmodule, powerSubmodule,
    ← range_lsmul_eq_principalIdeal_smul_top (A := A) (N := M.X n) (a := f ^ n),
    ← range_lsmul_eq_principalIdeal_smul_top
      (A := B) (N := (((baseChange).obj M).X n : ModuleCat B))
      (a := (algebraMap A B f) ^ n)]
  calc
    ((LinearMap.range μA).baseChange B).map e.symm.toLinearMap =
        (LinearMap.range (μA.baseChange B)).map e.symm.toLinearMap := by
          rw [Submodule.baseChange,
            range_subtype_baseChange_eq_range_baseChange (A := A) (B := B) (f := μA)]
    _ = LinearMap.range (e.symm.toLinearMap.comp (μA.baseChange B)) := by
          rw [LinearMap.range_comp]
    _ = LinearMap.range (μB.comp e.symm.toLinearMap) := by
          rw [hconj]
    _ = Submodule.map μB (LinearMap.range (e.symm.toLinearMap)) := by
          rw [LinearMap.range_comp]
    _ = Submodule.map μB ⊤ := by
          rw [hsurj]
    _ = LinearMap.range μB := by
          rw [Submodule.map_top, ← LinearMap.range_eq_map]

/-- Helper for Lemma 15.97.6: the two tensorized source power submodules identify with the common
target pair `g^i N^i × g^(i + 1) N^(i + 1)` after the degreewise scalar-extension equivalences. -/
private theorem pair_power_submodules_baseChange_map_eq
    (f : A) (M : CpxA) (i : ℕ) :
    (((powerSubmodule f M i).baseChange B).map
        ((extendScalarsTermLinearEquiv M i).symm.toLinearMap) =
      powerSubmodule (algebraMap A B f) ((baseChange).obj M) i) ∧
    (((nextPowerSubmodule f M i).baseChange B).map
        ((extendScalarsTermLinearEquiv M (i + 1)).symm.toLinearMap) =
      nextPowerSubmodule (algebraMap A B f) ((baseChange).obj M) i) := by
  constructor
  · -- Proof comment: degree `i` is exactly the first coordinate of the common product.
    exact powerSubmodule_baseChange_map_eq (A := A) (B := B) (f := f) (M := M) i
  · -- Proof comment: the second coordinate is the same statement in degree `i + 1`.
    simpa [nextPowerSubmodule] using
      powerSubmodule_baseChange_map_eq (A := A) (B := B) (f := f) (M := M) (i + 1)

/-- Helper for Lemma 15.97.6: on pure tensors, the degreewise scalar-extension equivalence
intertwines the base-changed differential with the tensorized original differential. -/
private theorem extendScalarsTermLinearEquiv_differential_tensor_apply
    (K : CpxA) (i : ℕ) (b : B) (x : K.X i) :
    (extendScalarsTermLinearEquiv K (i + 1))
      ((((baseChange).obj K).d i (i + 1)).hom
        ((extendScalarsTermLinearEquiv K i).symm (b ⊗ₜ[A] x))) =
      (((K.d i (i + 1)).hom).baseChange B) (b ⊗ₜ[A] x) := by
  -- Proof comment: rewrite the differential of the scalar-extended complex as
  -- `LinearMap.baseChange` and evaluate it on the pure tensor representative.
  change
    (LinearMap.baseChange B (ModuleCat.Hom.hom (K.d i (i + 1)))) (b ⊗ₜ[A] x) =
      (((K.d i (i + 1)).hom).baseChange B) (b ⊗ₜ[A] x)
  simp [extendScalarsTermLinearEquiv, restrictScalarsSelfEquiv, baseChange,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d, ModuleCat.extendScalars,
    ModuleCat.ExtendScalars.obj', ModuleCat.ExtendScalars.map', LinearMap.baseChange_tmul,
    LinearMap.lTensor_tmul]

/-- Helper for Lemma 15.97.6: after transporting a base-changed term to the tensor model, the
degreewise differential becomes the tensorized original differential. -/
private theorem extendScalarsTermLinearEquiv_differential_apply
    (K : CpxA) (i : ℕ) (x : (((baseChange).obj K).X i : ModuleCat B)) :
    (extendScalarsTermLinearEquiv K (i + 1))
      ((((baseChange).obj K).d i (i + 1)).hom x) =
      (((K.d i (i + 1)).hom).baseChange B) ((extendScalarsTermLinearEquiv K i) x) := by
  -- Proof comment: every scalar-extended vector comes from a tensor, so tensor induction reduces
  -- the comparison to the pure-tensor identity above.
  obtain ⟨z, rfl⟩ := (extendScalarsTermLinearEquiv K i).surjective x
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro b y
    simpa using
      extendScalarsTermLinearEquiv_differential_tensor_apply (A := A) (B := B) (K := K)
        (i := i) b y
  · intro z₁ z₂ hz₁ hz₂
    simp [LinearMap.map_add, hz₁, hz₂]

/-- Helper for Lemma 15.97.6: after distributing tensors across a product target, the base change
of a pair-valued linear map is the pair of the base-changed coordinate maps. -/
private theorem baseChange_pairMap_eq_prod_baseChange_coordinates
    {M' N₁ N₂ : Type u}
    [AddCommGroup M'] [Module A M']
    [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂]
    (s : M' →ₗ[A] N₁ × N₂) :
    (TensorProduct.prodRight A B B N₁ N₂).toLinearMap.comp (s.baseChange B) =
      LinearMap.prod (((LinearMap.fst A N₁ N₂).comp s).baseChange B)
        (((LinearMap.snd A N₁ N₂).comp s).baseChange B) := by
  -- Proof comment: evaluate both tensorized maps on pure tensors and extend by bilinearity.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · rfl
  · intro b x
    ext <;> simp [LinearMap.baseChange_tmul]
  · intro z₁ z₂ hz₁ hz₂
    simp [LinearMap.map_add, hz₁, hz₂]

/-- Helper for Lemma 15.97.6: regularity of a scalar on a module propagates to all of its powers.
-/
private theorem isSMulRegular_pow
    {M : Type u} [AddCommGroup M] [Module B M]
    {g : B} [hreg : IsSMulRegular M g] (n : ℕ) :
    IsSMulRegular M (g ^ n) := by
  -- Proof comment: peel off one copy of `g` at a time and use the given regularity inductively.
  induction n with
  | zero =>
      intro x hx
      simpa using hx
  | succ n ihn =>
      intro x hx
      apply ihn
      apply hreg
      simpa [pow_succ', smul_smul] using hx

/-- Helper for Lemma 15.97.6: a regular scalar on an ambient module remains regular on every
submodule. -/
private theorem isSMulRegular_submodule
    {M : Type u} [AddCommGroup M] [Module B M]
    {g : B} (P : Submodule B M) [hreg : IsSMulRegular M g] :
    IsSMulRegular P g := by
  -- Proof comment: forget to the ambient module, use regularity there, and then lift back to the
  -- subtype.
  intro x hx
  apply Subtype.ext
  exact hreg (x : M) <| by
    simpa using congrArg Subtype.val hx

/-- Helper for Lemma 15.97.6: for a module where `g` acts regularly, the canonical localization
map at powers of `g` is injective. -/
private theorem mkLinearMap_injective_of_isSMulRegular
    {M : Type u} [AddCommGroup M] [Module B M]
    {g : B} [hreg : IsSMulRegular M g] :
    Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers g) M) := by
  -- Proof comment: if `x - y` localizes to zero, a denominator `g^n` kills `x - y`; regularity of
  -- `g^n` then forces `x = y`.
  intro x y hxy
  have hzero :
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (x - y) = 0 := by
    rw [LinearMap.map_sub, hxy, sub_self]
  change
    IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
      (x - y) (1 : Submonoid.powers g) = 0 at hzero
  rw [IsLocalizedModule.mk'_eq_zero'] at hzero
  rcases hzero with ⟨s, hs⟩
  obtain ⟨n, hn⟩ := s.2
  have hpow : IsSMulRegular M (g ^ n) :=
    isSMulRegular_pow (B := B) (M := M) (g := g) n
  apply sub_eq_zero.mp
  exact hpow (x - y) <| by
    rw [← hn]
    simpa [smul_sub] using hs

/-- Helper for Lemma 15.97.6: quotienting by the image of a split monomorphism is canonically the
same as taking the kernel of a chosen retraction. -/
private theorem quotient_range_linearEquiv_ker_retraction
    {U E : Type u} [AddCommGroup U] [Module B U] [AddCommGroup E] [Module B E]
    (u : U →ₗ[B] E) (r : E →ₗ[B] U) (hr : r.comp u = LinearMap.id) :
    (E ⧸ LinearMap.range u) ≃ₗ[B] LinearMap.ker r := by
  let p : E →ₗ[B] E := LinearMap.id - u.comp r
  have hker : LinearMap.ker p = LinearMap.range u := by
    -- Proof comment: `p = 1 - u ∘ r` is the complementary projector to the split image of `u`.
    ext x
    constructor
    · intro hx
      refine ⟨r x, ?_⟩
      have hx' : x - u (r x) = 0 := by
        simpa [p, LinearMap.sub_apply, LinearMap.comp_apply] using hx
      exact (sub_eq_zero.mp hx').symm
    · rintro ⟨y, rfl⟩
      change u y - u (r (u y)) = 0
      simpa [hr, LinearMap.comp_apply]
  have hrange : LinearMap.range p = LinearMap.ker r := by
    -- Proof comment: the complementary projector lands in `ker r`, and every kernel element is
    -- fixed by that projector because `r` vanishes on it.
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change r (y - u (r y)) = 0
      simp [p, hr, LinearMap.sub_apply, LinearMap.comp_apply]
    · intro hx
      refine ⟨x, ?_⟩
      change x - u (r x) = x
      have hx' : r x = 0 := hx
      simp [p, hx', LinearMap.sub_apply, LinearMap.comp_apply]
  -- Proof comment: replace the quotient by `range u` with the quotient by `ker p`, then use the
  -- standard quotient-kernel/range identification for `p`.
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (p.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

/-- Helper for Lemma 15.97.6: if the quotient map by `range u` kills `v`, then every value of `v`
already lies in `range u`. -/
private theorem range_le_of_mkQ_comp_eq_zero
    {U V E : Type u} [AddCommGroup U] [Module B U] [AddCommGroup V] [Module B V]
    [AddCommGroup E] [Module B E]
    (u : U →ₗ[B] E) (v : V →ₗ[B] E)
    (hzero : (LinearMap.range u).mkQ.comp v = 0) :
    LinearMap.range v ≤ LinearMap.range u := by
  -- Proof comment: evaluate the zero composite on a representative of a point in `range v`, then
  -- use exactness of `subtype → mkQ` for the quotient by `range u`.
  intro y hy
  rcases hy with ⟨x, rfl⟩
  have hx : (LinearMap.range u).mkQ (v x) = 0 := by
    exact LinearMap.congr_fun (congrArg (fun φ : V →ₗ[B] E ⧸ LinearMap.range u ↦ φ) hzero) x
  rcases (LinearMap.exact_subtype_mkQ (LinearMap.range u) (v x)).1 hx with ⟨z, hz⟩
  exact ⟨z, hz⟩

/-- Helper for Lemma 15.97.6: for a split monomorphism into a regular ambient module, vanishing of
the localized quotient composite already forces vanishing before localization. -/
private theorem mkQ_comp_eq_zero_of_localized_zero_and_split
    {U V E : Type u} [AddCommGroup U] [Module B U] [AddCommGroup V] [Module B V]
    [AddCommGroup E] [Module B E]
    (g : B) [hreg : IsSMulRegular E g]
    (u : U →ₗ[B] E) (v : V →ₗ[B] E)
    (r : E →ₗ[B] U) (hr : r.comp u = LinearMap.id)
    (hlocalized :
      LocalizedModule.map (Submonoid.powers g) ((LinearMap.range u).mkQ.comp v) = 0) :
    (LinearMap.range u).mkQ.comp v = 0 := by
  let eQuot :=
    quotient_range_linearEquiv_ker_retraction (B := B) u r hr
  have hkerReg : IsSMulRegular (LinearMap.ker r) g :=
    isSMulRegular_submodule (B := B) (P := LinearMap.ker r)
  have hquotReg : IsSMulRegular (E ⧸ LinearMap.range u) g :=
    (LinearEquiv.isSMulRegular_congr eQuot g).2 hkerReg
  have hmkInj :
      Function.Injective
        (LocalizedModule.mkLinearMap (Submonoid.powers g) (E ⧸ LinearMap.range u)) :=
    mkLinearMap_injective_of_isSMulRegular (B := B) (M := E ⧸ LinearMap.range u) (g := g)
  -- Proof comment: evaluate the localized zero map on numerator generators and cancel the
  -- localization map in the quotient module.
  ext x
  have hlocx :
      LocalizedModule.map (Submonoid.powers g) ((LinearMap.range u).mkQ.comp v)
        (LocalizedModule.mk x (1 : Submonoid.powers g)) = 0 := by
    exact LinearMap.congr_fun hlocalized (LocalizedModule.mk x (1 : Submonoid.powers g))
  rw [LocalizedModule.map_mk] at hlocx
  exact hmkInj hlocx

/-- Helper for Lemma 15.97.6: if a graph map into a product has first coordinate equal to the
submodule inclusion, then first projection maps its image back to that domain submodule. -/
private theorem fst_map_graph_range_eq_domain
    {X Y : Type u} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    (P : Submodule B X) (u : P →ₗ[B] X × Y)
    (hu : (LinearMap.fst B X Y).comp u = P.subtype) :
    Submodule.map (LinearMap.fst B X Y) (LinearMap.range u) = P := by
  -- Proof comment: elements of the range of `u` project to the given domain element, and every
  -- domain element is hit by projecting the image of its own graph point.
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases hy with ⟨z, rfl⟩
    change (LinearMap.fst B X Y) (u z) = x at hxy
    rw [LinearMap.congr_fun hu z] at hxy
    simpa [Submodule.coe_mk] using hxy.symm
  · intro hx
    refine ⟨u ⟨x, hx⟩, ?_, ?_⟩
    · exact ⟨⟨x, hx⟩, rfl⟩
    · change (LinearMap.fst B X Y) (u ⟨x, hx⟩) = x
      simpa using LinearMap.congr_fun hu ⟨x, hx⟩

private theorem etaFDegreeSubmodule_baseChange_map_eq
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    ((etaFDegreeSubmodule f M i).baseChange B).map
        ((extendScalarsTermLinearEquiv M i).symm.toLinearMap) =
      etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) i := by
  -- Route correction: isolate the source-proof setup first. The principality hypothesis transports
  -- to the base-changed complex, so both graph maps are split monos before the remaining localized
  -- image comparison step.
  have hIbase :
      ∀ j : ℕ,
        ((((baseChange).obj M).etaDeterminantalIdeal (algebraMap A B f) j)).IsPrincipal := by
    intro j
    rw [eta_determinantal_ideal_base_change_nat (A := A) (B := B) (f := f) (M := M) j]
    exact Submodule.IsPrincipal.map_ringHom (algebraMap A B) (hI j)
  have hsplitSource :
      IsSplitMono (ModuleCat.ofHom (etaPairMap f M i)) := by
    -- Lemma 15.97.5 makes the source graph inclusion a direct summand.
    simpa using
      (etaFDegreePairMap_isSplitMono_of_determinantalIdeal_isPrincipal
        (A := A) (f := f) (M := M) (i := i) (hf := hf) (hI := hI i))
  have hsplitTarget :
      IsSplitMono
        (ModuleCat.ofHom (etaPairMap (algebraMap A B f) ((baseChange).obj M) i)) := by
    -- The same split-mono statement holds after base change by the transported principality.
    simpa using
      (etaFDegreePairMap_isSplitMono_of_determinantalIdeal_isPrincipal
        (A := B) (f := algebraMap A B f) (M := (baseChange).obj M) (i := i)
        (hf := hg) (hI := hIbase i))
  have hpairPower :
      (((powerSubmodule f M i).baseChange B).map
          ((extendScalarsTermLinearEquiv M i).symm.toLinearMap) =
        powerSubmodule (algebraMap A B f) ((baseChange).obj M) i) ∧
      (((nextPowerSubmodule f M i).baseChange B).map
          ((extendScalarsTermLinearEquiv M (i + 1)).symm.toLinearMap) =
        nextPowerSubmodule (algebraMap A B f) ((baseChange).obj M) i) :=
    pair_power_submodules_baseChange_map_eq (A := A) (B := B) (f := f) (M := M) i
  let g : B := algebraMap A B f
  let N : CpxA := (baseChange).obj M
  let eEta :
      ((etaFDegreeSubmodule f M i).baseChange B) ≃ₗ[B]
        (B ⊗[A] etaFDegreeSubmodule f M i) :=
    (Submodule.toBaseChange.toLinearEquiv B (etaFDegreeSubmodule f M i)).symm
  let ePow :
      ((powerSubmodule f M i).baseChange B) ≃ₗ[B] powerSubmodule g N i :=
    ((extendScalarsTermLinearEquiv M i).symm).ofSubmodules _ _ hpairPower.1
  let eNext :
      ((nextPowerSubmodule f M i).baseChange B) ≃ₗ[B] nextPowerSubmodule g N i :=
    ((extendScalarsTermLinearEquiv M (i + 1)).symm).ofSubmodules _ _ hpairPower.2
  let sTensor :
      B ⊗[A] etaFDegreeSubmodule f M i →ₗ[B]
        (B ⊗[A] powerSubmodule f M i) × (B ⊗[A] nextPowerSubmodule f M i) :=
    (TensorProduct.prodRight A B B (powerSubmodule f M i) (nextPowerSubmodule f M i)).toLinearMap.comp
      ((etaPairMap f M i).baseChange B)
  let s :
      ((etaFDegreeSubmodule f M i).baseChange B) →ₗ[B]
        powerSubmodule g N i × nextPowerSubmodule g N i :=
    ((LinearEquiv.prodCongr ePow eNext).toLinearMap.comp sTensor).comp eEta.toLinearMap
  let t :
      etaFDegreeSubmodule g N i →ₗ[B]
        powerSubmodule g N i × nextPowerSubmodule g N i :=
    etaPairMap g N i
  have hsTensor :
      sTensor =
        LinearMap.prod
          (((LinearMap.fst A (powerSubmodule f M i) (nextPowerSubmodule f M i)).comp
              (etaPairMap f M i)).baseChange B)
          (((LinearMap.snd A (powerSubmodule f M i) (nextPowerSubmodule f M i)).comp
              (etaPairMap f M i)).baseChange B) := by
    -- Proof comment: the tensorized source pair map splits into its tensorized coordinate maps.
    simpa [sTensor] using
      baseChange_pairMap_eq_prod_baseChange_coordinates (A := A) (B := B)
        (s := etaPairMap f M i)
  -- TODO: the remaining source-faithful blocker is the localized graph comparison. Using the
  -- explicit maps `s` and `t`, prove that after localizing at powers of `g`, both maps become
  -- the same graph of the localized differential; then use the already-established split-mono
  -- descent API from this file to descend equality of their ranges.
  let _ := hsTensor
  let _ := hsplitSource
  let _ := hsplitTarget
  let _ := s
  let _ := t
  sorry

private noncomputable def etaFDegreeTensorBaseChangeIso
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    (B ⊗[A] (((η[f] M).X i : ModuleCat A))) ≃ₗ[B] (etaFDegreeSubmodule f M i).baseChange B := by
  simpa using
    (LinearEquiv.ofBijective
      ((etaFDegreeSubmodule f M i).toBaseChange B)
      (etaFDegreeSubmodule_toBaseChange_bijective f M hf hg hI i) :
        (B ⊗[A] etaFDegreeSubmodule f M i) ≃ₗ[B] (etaFDegreeSubmodule f M i).baseChange B)

/-- Helper for Lemma 15.97.6: after forgetting the base-changed subtype, the tensor/base-change
identification is exactly the tensorized subtype inclusion. -/
private theorem etaFDegreeTensorBaseChangeIso_subtype_comp
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    ((etaFDegreeSubmodule f M i).baseChange B).subtype.comp
        (etaFDegreeTensorBaseChangeIso f M hf hg hI i).toLinearMap =
      ((etaFDegreeSubmodule f M i).subtype).baseChange B := by
  -- Proof comment: `Submodule.toBaseChange` is defined by tensoring the subtype inclusion.
  ext x
  rfl

/-- Helper for Lemma 15.97.6: on elements, the tensor/base-change identification has ambient
value equal to the tensorized subtype inclusion. -/
private theorem etaFDegreeTensorBaseChangeIso_apply
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ)
    (x : B ⊗[A] etaFDegreeSubmodule f M i) :
    (((etaFDegreeTensorBaseChangeIso f M hf hg hI i x :
        (etaFDegreeSubmodule f M i).baseChange B) :
        B ⊗[A] M.X i)) =
      (((etaFDegreeSubmodule f M i).subtype).baseChange B) x := by
  -- Proof comment: evaluate the normalized subtype composition at the chosen tensor.
  exact LinearMap.congr_fun
    (etaFDegreeTensorBaseChangeIso_subtype_comp f M hf hg hI i) x

private noncomputable def etaFDegreeBaseChangeIso
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    (((baseChange).obj (η[f] M)).X i) ≅
      (η[algebraMap A B f] ((baseChange).obj M)).X i := by
  let eLeft :
      ((((baseChange).obj (η[f] M)).X i : ModuleCat B)) ≃ₗ[B]
        (B ⊗[A] (((η[f] M).X i : ModuleCat A))) :=
    extendScalarsTermLinearEquiv (η[f] M) i
  let eRight :
      (etaFDegreeSubmodule f M i).baseChange B ≃ₗ[B]
        etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) i :=
    ((extendScalarsTermLinearEquiv M i).symm).ofSubmodules _ _
      (etaFDegreeSubmodule_baseChange_map_eq f M hf hg hI i)
  exact ((eLeft.trans (etaFDegreeTensorBaseChangeIso f M hf hg hI i)).trans
    eRight).toModuleIso

/-- Helper for Lemma 15.97.6: the source `η_f` differential followed by the ambient subtype
inclusion is the ambient differential followed by the source subtype inclusion. -/
private theorem etaFDegreeSubmodule_differential_subtype_comp
    (f : A) (M : CpxA) (i : ℕ) :
    (etaFDegreeSubmodule f M (i + 1)).subtype.comp (((η[f] M).d i (i + 1)).hom) =
      (M.d i (i + 1)).hom.comp (etaFDegreeSubmodule f M i).subtype := by
  -- Proof comment: the differential on `η[f] M` is the codomain restriction of the ambient
  -- differential, so forgetting the subtype restores the original map.
  ext x
  rfl

/-- Helper for Lemma 15.97.6: after forgetting the target subtype, the degreewise
base-change-vs-eta submodule bridge is the ambient scalar-extension equivalence in degree `i`. -/
private theorem etaFDegreeBaseChangeSubmoduleIso_subtype_comp
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    (etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) i).subtype.comp
        ((((extendScalarsTermLinearEquiv M i).symm).ofSubmodules _ _
          (etaFDegreeSubmodule_baseChange_map_eq f M hf hg hI i)).toLinearMap) =
      ((extendScalarsTermLinearEquiv M i).symm.toLinearMap).comp
        (((etaFDegreeSubmodule f M i).baseChange B).subtype) := by
  -- Normalize the `LinearEquiv.ofSubmodules` bridge once so later proofs only see the ambient
  -- degreewise scalar-extension equivalence.
  ext x
  rfl

/-- Helper for Lemma 15.97.6: on elements, the degreewise submodule bridge applies the ambient
scalar-extension equivalence from the tensorized source term to the common base-changed term. -/
private theorem etaFDegreeBaseChangeSubmoduleIso_apply
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ)
    (x : (etaFDegreeSubmodule f M i).baseChange B) :
    (((((extendScalarsTermLinearEquiv M i).symm).ofSubmodules _ _
        (etaFDegreeSubmodule_baseChange_map_eq f M hf hg hI i)) x :
        etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) i) :
        (((baseChange).obj M).X i : ModuleCat B)) =
      ((extendScalarsTermLinearEquiv M i).symm) x := by
  -- Evaluate the normalized subtype composition on the chosen element.
  exact LinearMap.congr_fun
    (etaFDegreeBaseChangeSubmoduleIso_subtype_comp f M hf hg hI i) x

/-- Helper for Lemma 15.97.6: on elements, the full degreewise comparison isomorphism has ambient
value given by first moving to the tensor model and then applying the target scalar-extension
equivalence inverse. -/
private theorem etaFDegreeBaseChangeIso_apply
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ)
    (x : (((baseChange).obj (η[f] M)).X i : ModuleCat B)) :
    ((((etaFDegreeBaseChangeIso f M hf hg hI i).hom x :
        etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) i) :
        (((baseChange).obj M).X i : ModuleCat B))) =
      (extendScalarsTermLinearEquiv M i).symm
        ((etaFDegreeTensorBaseChangeIso f M hf hg hI i)
          ((extendScalarsTermLinearEquiv (η[f] M) i) x)) := by
  -- Proof comment: unfold the component isomorphism only up to the final submodule bridge, then
  -- use the normalized ambient-value lemma for that bridge.
  simpa [etaFDegreeBaseChangeIso, LinearEquiv.trans_apply] using
    etaFDegreeBaseChangeSubmoduleIso_apply f M hf hg hI i
      ((etaFDegreeTensorBaseChangeIso f M hf hg hI i)
        ((extendScalarsTermLinearEquiv (η[f] M) i) x))

private theorem etaFDegreeBaseChangeIso_comm_succ
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    (etaFDegreeBaseChangeIso f M hf hg hI i).hom ≫
        (η[algebraMap A B f] ((baseChange).obj M)).d i (i + 1) =
      ((baseChange).obj (η[f] M)).d i (i + 1) ≫
        (etaFDegreeBaseChangeIso f M hf hg hI (i + 1)).hom := by
  -- Proof comment: compare both composites after forgetting the final subtype. On the tensor
  -- model, both sides become the tensorized ambient differential thanks to the source and target
  -- scalar-extension compatibility lemmas.
  apply ModuleCat.hom_ext
  ext x
  apply Subtype.ext
  let xTensor : B ⊗[A] etaFDegreeSubmodule f M i :=
    (extendScalarsTermLinearEquiv (η[f] M) i) x
  let yBase : (etaFDegreeSubmodule f M i).baseChange B :=
    etaFDegreeTensorBaseChangeIso f M hf hg hI i xTensor
  let yTensor : B ⊗[A] M.X i := yBase
  have hyTensor :
      yTensor = (((etaFDegreeSubmodule f M i).subtype).baseChange B) xTensor := by
    -- Proof comment: the tensor/base-change identification has the expected ambient value.
    exact etaFDegreeTensorBaseChangeIso_apply f M hf hg hI i xTensor
  have hleftAmbient :
      (extendScalarsTermLinearEquiv M (i + 1))
        ((((baseChange).obj M).d i (i + 1)).hom
          ((extendScalarsTermLinearEquiv M i).symm yTensor)) =
        (((M.d i (i + 1)).hom).baseChange B) yTensor := by
    -- Proof comment: the target scalar-extension equivalence carries the ambient differential to
    -- the tensorized differential.
    exact extendScalarsTermLinearEquiv_differential_apply (A := A) (B := B) (K := M)
      (i := i) ((extendScalarsTermLinearEquiv M i).symm yTensor)
  have hsourceAmbient :
      (((etaFDegreeSubmodule f M (i + 1)).subtype).baseChange B)
          ((((η[f] M).d i (i + 1)).hom).baseChange B xTensor) =
        (((M.d i (i + 1)).hom).baseChange B)
          ((((etaFDegreeSubmodule f M i).subtype).baseChange B) xTensor) := by
    -- Proof comment: tensoring the source identity
    -- `subtype ∘ d_η = d_M ∘ subtype` identifies the tensorized source differential with the
    -- tensorized ambient differential.
    simpa [LinearMap.comp_apply] using
      congrArg (fun φ : B ⊗[A] etaFDegreeSubmodule f M i →ₗ[B] B ⊗[A] M.X (i + 1) ↦ φ xTensor)
        (congrArg (fun φ : etaFDegreeSubmodule f M i →ₗ[A] M.X (i + 1) => φ.baseChange B)
          (etaFDegreeSubmodule_differential_subtype_comp (A := A) (f := f) (M := M) (i := i)))
  have hrightAmbient :
      (extendScalarsTermLinearEquiv M (i + 1))
        ((((etaFDegreeBaseChangeIso f M hf hg hI (i + 1)).hom)
          ((((baseChange).obj (η[f] M)).d i (i + 1)).hom x) :
            etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) (i + 1)) :
            (((baseChange).obj M).X (i + 1) : ModuleCat B))) =
        (((M.d i (i + 1)).hom).baseChange B) yTensor := by
    -- Proof comment: rewrite the right composite through the component isomorphism in degree
    -- `i + 1`, then use the source scalar-extension compatibility and the tensorized subtype
    -- identity.
    calc
      (extendScalarsTermLinearEquiv M (i + 1))
          ((((etaFDegreeBaseChangeIso f M hf hg hI (i + 1)).hom)
            ((((baseChange).obj (η[f] M)).d i (i + 1)).hom x) :
              etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) (i + 1)) :
              (((baseChange).obj M).X (i + 1) : ModuleCat B))) =
        (((etaFDegreeSubmodule f M (i + 1)).subtype).baseChange B)
          ((extendScalarsTermLinearEquiv (η[f] M) (i + 1))
            ((((baseChange).obj (η[f] M)).d i (i + 1)).hom x)) := by
            rw [etaFDegreeBaseChangeIso_apply (A := A) (B := B) (f := f) (M := M)
              (hf := hf) (hg := hg) (hI := hI) (i := i + 1)
              (x := ((((baseChange).obj (η[f] M)).d i (i + 1)).hom x))]
            exact etaFDegreeTensorBaseChangeIso_apply f M hf hg hI (i + 1) _
      _ = (((etaFDegreeSubmodule f M (i + 1)).subtype).baseChange B)
            ((((η[f] M).d i (i + 1)).hom).baseChange B xTensor) := by
            rw [extendScalarsTermLinearEquiv_differential_apply (A := A) (B := B)
              (K := η[f] M) (i := i) (x := x)]
      _ = (((M.d i (i + 1)).hom).baseChange B)
            ((((etaFDegreeSubmodule f M i).subtype).baseChange B) xTensor) := by
            exact hsourceAmbient
      _ = (((M.d i (i + 1)).hom).baseChange B) yTensor := by
            rw [hyTensor]
  -- Proof comment: both sides have the same image under the target scalar-extension equivalence,
  -- so injectivity of that equivalence finishes the ambient equality.
  apply (extendScalarsTermLinearEquiv M (i + 1)).injective
  calc
    (extendScalarsTermLinearEquiv M (i + 1))
        (((((η[algebraMap A B f] ((baseChange).obj M)).d i (i + 1)).hom)
          (((etaFDegreeBaseChangeIso f M hf hg hI i).hom x :
            etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) i) :
            (((baseChange).obj M).X i : ModuleCat B))) :
          etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) (i + 1)) :
          (((baseChange).obj M).X (i + 1) : ModuleCat B)) =
      (extendScalarsTermLinearEquiv M (i + 1))
        ((((baseChange).obj M).d i (i + 1)).hom
          ((extendScalarsTermLinearEquiv M i).symm yTensor)) := by
            simp [etaFDegreeBaseChangeIso_apply (A := A) (B := B) (f := f) (M := M)
              (hf := hf) (hg := hg) (hI := hI) (i := i) (x := x), yTensor]
    _ = (((M.d i (i + 1)).hom).baseChange B) yTensor := by
          exact hleftAmbient
    _ = (extendScalarsTermLinearEquiv M (i + 1))
          ((((etaFDegreeBaseChangeIso f M hf hg hI (i + 1)).hom)
            ((((baseChange).obj (η[f] M)).d i (i + 1)).hom x) :
              etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) (i + 1)) :
              (((baseChange).obj M).X (i + 1) : ModuleCat B))) := by
            exact hrightAmbient.symm

private theorem etaFDegreeBaseChangeIso_comm
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i j : ℕ) (hij : (up ℕ).Rel i j) :
    (etaFDegreeBaseChangeIso f M hf hg hI i).hom ≫
        (η[algebraMap A B f] ((baseChange).obj M)).d i j =
      ((baseChange).obj (η[f] M)).d i j ≫
        (etaFDegreeBaseChangeIso f M hf hg hI j).hom := by
  cases hij
  simpa using etaFDegreeBaseChangeIso_comm_succ f M hf hg hI i

/-
Domain-style sampling:
- primary domain: scalar extension of the source-facing Berthelot-Ogus complex `η[f] M` on
  `ℕ`-indexed cochain complexes of finite free modules;
- sampled owner declarations:
  `η[_] _`,
  `NatModuleCochainComplex.etaDeterminantalIdeal`,
  `etaDeterminantalIdeal_baseChange`,
  `etaFDegreePairMap_isSplitMono_of_determinantalIdeal_isPrincipal`,
  `Functor.mapHomologicalComplex`;
- best owner abstraction:
  `source-facing`: the canonical base-change isomorphism for `η[f] M`;
  `core/canonical`: the owners `η[_] _`, `NatModuleCochainComplex.etaDeterminantalIdeal`, and
    scalar extension by `baseChange`;
  `bridge/view`: the comparison between `baseChange.obj (η[f] M)` and
    `η[algebraMap A B f] (baseChange.obj M)`;
- primitive data vs derived API: the primitive data are the finite-free complex `M`, the
  nonzerodivisor hypotheses on `f` and its image, and principality of the source
  determinantal ideals. The comparison isomorphism is derived bridge data and should stay a direct
  named isomorphism rather than a wrapper around auxiliary comparison packages. -/

/-- Lemma 15.97.6: let `A → B` be a ring map, let `f ∈ A` be a nonzerodivisor, and let `M^\bullet`
be a complex of finite free `A`-modules. If the image of `f` in `B` is a nonzerodivisor and every
determinantal ideal `I_i(M^\bullet, f)` is principal, then the base change of `η_f M^\bullet` is
canonically isomorphic to `η_g(M^\bullet ⊗_A B)` for `g = algebraMap A B f`. No bounded-above
hypothesis is needed for this comparison. -/
@[stacks 0F7X]
noncomputable def etaFComplex_baseChangeIso_of_determinantalIdeal_isPrincipal
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal) :
    ((baseChange).obj (η[f] M)) ≅ η[algebraMap A B f] ((baseChange).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (etaFDegreeBaseChangeIso f M hf hg hI)
    (etaFDegreeBaseChangeIso_comm f M hf hg hI)

end
