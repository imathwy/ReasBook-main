import stacks_proof.stacks_project.Chap15.Definition_15_8_3
import stacks_proof.stacks_project.Chap10.Definition_10_78_1
import stacks_proof.stacks_project.Chap15.Lemma_15_3_2
import stacks_proof.stacks_project.Chap15.Lemma_15_26_4
import stacks_proof.stacks_project.Chap15.Lemma_15_26_5
import stacks_proof.stacks_project.Chap15.Lemma_15_96_2
import stacks_proof.stacks_project.Chap15.BerthelotOgusEtaReductionNatPairMap
import stacks_proof.stacks_project.Chap15.Lemma_15_97_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open BerthelotOgusEtaReduction.Nat
open scoped nonZeroDivisors

universe u

section

variable {A : Type u} [CommRing A]
local notation "CpxA" => NatModuleCochainComplex A

/-
Domain-style sampling:
- primary domain: Berthelot-Ogus `η_f` for bounded-above `ℕ`-indexed cochain complexes, together
  with the degree-`i` determinantal ideal `I_i(M^•, f)`;
- sampled owner declarations:
  `_root_.etaDeterminantalIdeal`,
  `CochainComplex.IsStrictlyLE`,
  `etaFDegreeSubmodule`,
  `etaPairMap`,
  `Module.Free`,
  `Module.FiniteLocallyFreeOfRank`;
- best owner abstraction:
  `source-facing`: the two theorems of this file about `(η_f M)^i`, the unreduced map
    `(1, d^i)`, and the degree-`i` ideal `I_i(M^•, f)` on `M : NatModuleCochainComplex A`;
  `core/canonical`: the chapter owner `etaDeterminantalIdeal` on `ℤ`-indexed complexes together
    with the `ℤ`-indexed bounded-above predicate on `M.extend embeddingUpNat`;
  `bridge/view`: extension by zero along `embeddingUpNat`, used only internally to recall the
    `ℤ`-indexed determinantal-ideal owner and bounded-above predicate.
- primitive data vs derived API: the primitive public data are the degreewise finite-free terms of
  `M` and the nat-level ideal `M.etaDeterminantalIdeal f i`; the extension-by-zero presentation is
  derived bridge data and should not remain in theorem interfaces. -/

private noncomputable instance extend_embeddingUpNat_term_moduleFree
    (M : CpxA) (i : ℕ) [Module.Free A (M.X i)] :
    Module.Free A ((M.extend embeddingUpNat).X (i : ℤ)) := by
  let e : (((M.extend embeddingUpNat).X (i : ℤ)) : ModuleCat A) ≃ₗ[A] M.X i :=
    (M.extendXIso embeddingUpNat rfl).toLinearEquiv
  exact Module.Free.of_equiv e.symm

private noncomputable instance extend_embeddingUpNat_term_moduleFinite
    (M : CpxA) (i : ℕ) [Module.Finite A (M.X i)] :
    Module.Finite A ((M.extend embeddingUpNat).X (i : ℤ)) := by
  let e : (((M.extend embeddingUpNat).X (i : ℤ)) : ModuleCat A) ≃ₗ[A] M.X i :=
    (M.extendXIso embeddingUpNat rfl).toLinearEquiv
  exact Module.Finite.equiv e.symm

private noncomputable instance extend_embeddingUpNat_succ_term_moduleFree
    (M : CpxA) (i : ℕ) [Module.Free A (M.X (i + 1))] :
    Module.Free A ((M.extend embeddingUpNat).X ((i : ℤ) + 1)) := by
  let e : (((M.extend embeddingUpNat).X ((i : ℤ) + 1)) : ModuleCat A) ≃ₗ[A] M.X (i + 1) := by
    simpa using (M.extendXIso embeddingUpNat (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv
  exact Module.Free.of_equiv e.symm

private noncomputable instance extend_embeddingUpNat_succ_term_moduleFinite
    (M : CpxA) (i : ℕ) [Module.Finite A (M.X (i + 1))] :
    Module.Finite A ((M.extend embeddingUpNat).X ((i : ℤ) + 1)) := by
  let e : (((M.extend embeddingUpNat).X ((i : ℤ) + 1)) : ModuleCat A) ≃ₗ[A] M.X (i + 1) := by
    simpa using (M.extendXIso embeddingUpNat (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv
  exact Module.Finite.equiv e.symm

namespace NatModuleCochainComplex

/-- A bounded-below complex is bounded above if its extension by zero vanishes above some
nonnegative degree. This keeps the `ℤ`-indexed support bridge internal to the owner. -/
abbrev IsBoundedAbove (M : CpxA) : Prop :=
  ∃ b : ℕ, CochainComplex.IsStrictlyLE (M.extend embeddingUpNat) (b : ℤ)

/-- The degree-`i` Berthelot-Ogus determinantal ideal `I_i(M^•, f)` for a bounded-below complex,
viewed through the canonical extension-by-zero bridge. -/
abbrev etaDeterminantalIdeal
    (M : CpxA) (f : A) (i : ℕ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    Ideal A :=
  _root_.etaDeterminantalIdeal f (M.extend embeddingUpNat) (i : ℤ)

end NatModuleCochainComplex

variable (f : A) (M : CpxA) (i : ℕ)
variable [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
variable [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
variable (hf : f ∈ nonZeroDivisors A)
variable (hI : (M.etaDeterminantalIdeal f i).IsPrincipal)

/-- Helper for Lemma 15.97.5: a finite free module is finite locally free of rank equal to its
`Module.finrank`. -/
private theorem finiteLocallyFreeOfRank_of_finite_free
    {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Free A N] [Module.Finite A N] :
    Module.FiniteLocallyFreeOfRank A N (Module.finrank A N) := by
  rcases finite_free_linearEquiv_fin (R := A) (F := N) with ⟨n, ⟨e⟩⟩
  have hn : Module.finrank A N = n := Module.finrank_eq_of_equiv e
  letI : Module.FiniteLocallyFreeOfRank A (Fin n → A) n :=
    fin_pi_finiteLocallyFreeOfRank (A := A) n
  have hN : Module.FiniteLocallyFreeOfRank A N n :=
    finiteLocallyFreeOfRank_of_equiv (A := A) (N₁ := N) (N₂ := Fin n → A) e
  simpa [hn] using hN

/-- Helper for Lemma 15.97.5: on a finite free module, multiplication by a nonzerodivisor is
injective. -/
private theorem lsmul_injective_of_nonZeroDivisor_of_finite_free
    {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Free A N] [Module.Finite A N] {a : A}
    (ha : a ∈ nonZeroDivisors A) :
    Function.Injective (LinearMap.lsmul A N a) := by
  rcases finite_free_linearEquiv_fin (R := A) (F := N) with ⟨n, ⟨e⟩⟩
  rw [mem_nonZeroDivisors_iff_left] at ha
  intro x y hxy
  apply e.injective
  ext j
  have hzero :
      ((LinearMap.lsmul A (Fin n → A) a) (e (x - y))) j = 0 := by
    -- Proof comment: transport the vanishing of `a • (x - y)` to coordinates.
    have hxy' : (LinearMap.lsmul A N a) (x - y) = 0 := by
      simp [LinearMap.lsmul_apply, hxy]
    simpa [LinearMap.lsmul_apply, map_sub] using
      congrArg (fun z : N ↦ e z j) hxy'
  have hcoord : (e (x - y)) j = 0 := by
    simpa [LinearMap.lsmul_apply] using ha hzero
  simpa [map_sub] using hcoord

/-- Helper for Lemma 15.97.5: on a finite free module, multiplication by a nonzerodivisor
identifies the module with the principal-ideal power submodule it generates. -/
private theorem nonempty_linearEquiv_principalIdeal_smul_top_of_nonZeroDivisor_of_finite_free
    {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Free A N] [Module.Finite A N] {a : A}
    (ha : a ∈ nonZeroDivisors A) :
    Nonempty (N ≃ₗ[A] principalIdeal a • (⊤ : Submodule A N)) := by
  let μ : N →ₗ[A] N := LinearMap.lsmul A N a
  have hμinj : Function.Injective μ :=
    lsmul_injective_of_nonZeroDivisor_of_finite_free
      (A := A) (N := N) ha
  refine ⟨(LinearEquiv.ofInjective μ hμinj).trans ?_⟩
  exact LinearEquiv.ofEq _ _
    (range_lsmul_eq_principalIdeal_smul_top (A := A) (N := N) a)

/-- Helper for Lemma 15.97.5: the source term `M^i` is linearly equivalent to the textbook power
submodule `f^i M^i`. -/
private theorem powerSubmodule_linearEquiv_of_nonZeroDivisor_pow :
    Nonempty (M.X i ≃ₗ[A] powerSubmodule f M i) := by
  -- Proof comment: `f^i` is still a nonzerodivisor, so multiplication by `f^i` identifies `M^i`
  -- with the principal-ideal power submodule.
  simpa [powerSubmodule] using
    nonempty_linearEquiv_principalIdeal_smul_top_of_nonZeroDivisor_of_finite_free
      (A := A) (N := M.X i) (pow_mem hf i)

/-- Helper for Lemma 15.97.5: the source term `M^{i + 1}` is linearly equivalent to the textbook
power submodule `f^(i + 1) M^{i + 1}`. -/
private theorem nextPowerSubmodule_linearEquiv_of_nonZeroDivisor_pow :
    Nonempty (M.X (i + 1) ≃ₗ[A] nextPowerSubmodule f M i) := by
  -- Proof comment: the same regular-scalar argument identifies the next power submodule.
  simpa [nextPowerSubmodule] using
    nonempty_linearEquiv_principalIdeal_smul_top_of_nonZeroDivisor_of_finite_free
      (A := A) (N := M.X (i + 1)) (pow_mem hf (i + 1))

/-- Helper for Lemma 15.97.5: the textbook power submodule `f^i M^i` is finite locally free of
rank `rk(M^i)`. -/
private theorem powerSubmodule_finiteLocallyFreeOfRank_of_nonZeroDivisor_pow :
    Module.FiniteLocallyFreeOfRank A (powerSubmodule f M i) (Module.finrank A (M.X i)) := by
  rcases powerSubmodule_linearEquiv_of_nonZeroDivisor_pow
      (A := A) (f := f) (M := M) (i := i) hf with ⟨e⟩
  letI : Module.FiniteLocallyFreeOfRank A (M.X i) (Module.finrank A (M.X i)) :=
    finiteLocallyFreeOfRank_of_finite_free (A := A) (N := M.X i)
  exact finiteLocallyFreeOfRank_of_equiv (A := A) (N₁ := powerSubmodule f M i)
    (N₂ := M.X i) e.symm

/-- Helper for Lemma 15.97.5: the textbook power submodule `f^(i + 1) M^{i + 1}` is finite
locally free of rank `rk(M^{i + 1})`. -/
private theorem nextPowerSubmodule_finiteLocallyFreeOfRank_of_nonZeroDivisor_pow :
    Module.FiniteLocallyFreeOfRank A (nextPowerSubmodule f M i)
      (Module.finrank A (M.X (i + 1))) := by
  rcases nextPowerSubmodule_linearEquiv_of_nonZeroDivisor_pow
      (A := A) (f := f) (M := M) (i := i) hf with ⟨e⟩
  letI : Module.FiniteLocallyFreeOfRank A (M.X (i + 1))
      (Module.finrank A (M.X (i + 1))) :=
    finiteLocallyFreeOfRank_of_finite_free (A := A) (N := M.X (i + 1))
  exact finiteLocallyFreeOfRank_of_equiv (A := A) (N₁ := nextPowerSubmodule f M i)
    (N₂ := M.X (i + 1)) e.symm

/-- Helper for Lemma 15.97.5: the extension-by-zero presentation quotient has the expected
principal Fitting ideal generated by the chosen generator of `I_i(M^\bullet, f)`. -/
private theorem presentation_quotient_fittingIdeal_eq_principalIdeal_generator :
    let K := M.extend embeddingUpNat
    let N := etaPresentationQuotient f K (i : ℤ)
    let g := Submodule.IsPrincipal.generator (M.etaDeterminantalIdeal f i)
    Fit[A]_(Module.finrank A (M.X (i + 1)))(N) = principalIdeal g := by
  letI : (M.etaDeterminantalIdeal f i).IsPrincipal := hI
  dsimp
  have hfin :
      Module.finrank A ((M.extend embeddingUpNat).X ((i : ℤ) + 1)) =
        Module.finrank A (M.X (i + 1)) := by
    let e : (((M.extend embeddingUpNat).X ((i : ℤ) + 1)) : ModuleCat A) ≃ₗ[A] M.X (i + 1) := by
      simpa using
        (M.extendXIso embeddingUpNat
          (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv
    simpa using Module.finrank_eq_of_equiv e
  -- Proof comment: rewrite the `ℤ`-indexed owner through the degreewise `extendXIso`, then use
  -- the principal generator description of `I_i(M^\bullet, f)`.
  calc
    Fit[A]_(Module.finrank A (M.X (i + 1)))
        (etaPresentationQuotient f (M.extend embeddingUpNat) (i : ℤ)) =
      Fit[A]_(Module.finrank A ((M.extend embeddingUpNat).X ((i : ℤ) + 1)))
        (etaPresentationQuotient f (M.extend embeddingUpNat) (i : ℤ)) := by
          rw [hfin]
    _ = M.etaDeterminantalIdeal f i := by
          rfl
    _ = principalIdeal (Submodule.IsPrincipal.generator (M.etaDeterminantalIdeal f i)) := by
          simpa [principalIdeal] using
            (Ideal.span_singleton_generator (M.etaDeterminantalIdeal f i)).symm

/-- Helper for Lemma 15.97.5: the middle term
`f^i M^i ⊕ f^(i + 1) M^{i + 1}` is finite locally free of the expected total rank. -/
private theorem etaPairMiddle_finiteLocallyFreeOfRank :
    Module.FiniteLocallyFreeOfRank A
      (powerSubmodule f M i × nextPowerSubmodule f M i)
      (Module.finrank A (M.X i) + Module.finrank A (M.X (i + 1))) := by
  rcases powerSubmodule_linearEquiv_of_nonZeroDivisor_pow
      (A := A) (f := f) (M := M) (i := i) hf with ⟨e₀⟩
  rcases nextPowerSubmodule_linearEquiv_of_nonZeroDivisor_pow
      (A := A) (f := f) (M := M) (i := i) hf with ⟨e₁⟩
  let e :
      powerSubmodule f M i × nextPowerSubmodule f M i ≃ₗ[A]
        M.X i × M.X (i + 1) :=
    LinearEquiv.prodCongr e₀.symm e₁.symm
  have hprod :
      Module.FiniteLocallyFreeOfRank A (M.X i × M.X (i + 1))
        (Module.finrank A (M.X i × M.X (i + 1))) :=
    finiteLocallyFreeOfRank_of_finite_free (A := A) (N := M.X i × M.X (i + 1))
  have hsum :
      Module.finrank A (M.X i × M.X (i + 1)) =
        Module.finrank A (M.X i) + Module.finrank A (M.X (i + 1)) := by
    simpa using Module.finrank_prod (R := A) (M := M.X i) (N := M.X (i + 1))
  have hmiddle :
      Module.FiniteLocallyFreeOfRank A (powerSubmodule f M i × nextPowerSubmodule f M i)
        (Module.finrank A (M.X i × M.X (i + 1))) :=
    finiteLocallyFreeOfRank_of_equiv (A := A)
      (N₁ := powerSubmodule f M i × nextPowerSubmodule f M i)
      (N₂ := M.X i × M.X (i + 1)) e
  simpa [hsum] using hmiddle

/-- Helper for Lemma 15.97.5: the image of scalar multiplication by `a` is exactly `aM`. -/
private theorem range_lsmul_eq_principalIdeal_smul_top
    {N : Type*} [AddCommGroup N] [Module A N] (a : A) :
    LinearMap.range (LinearMap.lsmul A N a) =
      principalIdeal a • (⊤ : Submodule A N) := by
  ext x
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    -- Proof comment: a visible `a`-multiple lies in `aN` by construction.
    simpa [principalIdeal, LinearMap.lsmul_apply] using
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a)
        (show y ∈ (⊤ : Submodule A N) by simp))
  · intro hx
    -- Proof comment: every generator of `aN` is in the range of multiplication by `a`.
    have hle :
        principalIdeal a • (⊤ : Submodule A N) ≤ LinearMap.range (LinearMap.lsmul A N a) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      rcases Ideal.mem_span_singleton.mp hr with ⟨b, rfl⟩
      refine LinearMap.mem_range.mpr ⟨b • y, ?_⟩
      simp [LinearMap.lsmul_apply, smul_smul, mul_comm]
    exact hle hx

/-- Helper for Lemma 15.97.5: quotienting by the image of the first inclusion recovers the second
factor. -/
private noncomputable def quotient_range_inl_linearEquiv
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂] :
    ((N₁ × N₂) ⧸ LinearMap.range (LinearMap.inl A N₁ N₂)) ≃ₗ[A] N₂ := by
  let π : N₁ × N₂ →ₗ[A] N₂ := LinearMap.snd A N₁ N₂
  have hker : LinearMap.ker π = LinearMap.range (LinearMap.inl A N₁ N₂) := by
    -- Proof comment: the kernel of the second projection is exactly the first summand.
    ext z
    constructor
    · intro hz
      rw [LinearMap.mem_ker] at hz
      refine LinearMap.mem_range.mpr ⟨z.1, ?_⟩
      ext <;> simp [hz]
    · rintro ⟨x, rfl⟩
      simp [LinearMap.mem_ker]
  have hrange : LinearMap.range π = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨(0, y), by simp [π]⟩
  -- Proof comment: rewrite by the actual kernel of `snd`, then collapse its full image.
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (π.quotKerEquivRange.trans
        ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))

/-- Helper for Lemma 15.97.5: the standard shear automorphism of a product attached to `φ`. -/
private noncomputable def product_shear
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    (φ : N₁ →ₗ[A] N₂) :
    (N₁ × N₂) ≃ₗ[A] (N₁ × N₂) where
  toFun x := (x.1, x.2 - φ x.1)
  invFun x := (x.1, x.2 + φ x.1)
  left_inv x := by
    ext <;> simp
  right_inv x := by
    ext <;> simp
  map_add' x y := by
    ext <;> simp [map_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  map_smul' a x := by
    ext <;> simp [map_smul, smul_sub]

/-- Helper for Lemma 15.97.5: the shear automorphism carries the graph of `φ` onto the first
summand. -/
private theorem product_shear_maps_graph_range_to_inl_range
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    (φ : N₁ →ₗ[A] N₂) :
    (LinearMap.range (LinearMap.prod (LinearMap.id : N₁ →ₗ[A] N₁) φ)).map
        (product_shear (A := A) φ).toLinearMap =
      LinearMap.range (LinearMap.inl A N₁ N₂) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    -- Proof comment: the shear kills the second coordinate on graph points `(y, φ y)`.
    refine LinearMap.mem_range.mpr ⟨y, ?_⟩
    ext <;> simp [product_shear]
  · intro hz
    rcases LinearMap.mem_range.mp hz with ⟨x, rfl⟩
    -- Proof comment: each point of the first summand is the sheared image of a graph point.
    refine Submodule.mem_map.mpr ⟨(LinearMap.prod (LinearMap.id : N₁ →ₗ[A] N₁) φ) x,
      LinearMap.mem_range_self _ x, ?_⟩
    ext <;> simp [product_shear]

/-- Helper for Lemma 15.97.5: quotienting a product by the graph of `φ` recovers the second
factor. -/
private noncomputable def graph_quotient_linearEquiv_right
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    (φ : N₁ →ₗ[A] N₂) :
    ((N₁ × N₂) ⧸ LinearMap.range (LinearMap.prod (LinearMap.id : N₁ →ₗ[A] N₁) φ)) ≃ₗ[A] N₂ :=
  -- Proof comment: shear the graph of `φ` onto the first factor and then project away that
  -- factor.
  (Submodule.Quotient.equiv
      (LinearMap.range (LinearMap.prod (LinearMap.id : N₁ →ₗ[A] N₁) φ))
      (LinearMap.range (LinearMap.inl A N₁ N₂))
      (product_shear (A := A) φ)
      (product_shear_maps_graph_range_to_inl_range (A := A) φ)).trans
    (quotient_range_inl_linearEquiv (A := A))

/-- Helper for Lemma 15.97.5: membership in `aM` is equivalent to being an explicit `a`-multiple.
-/
private theorem exists_smul_eq_of_mem_principalIdeal_smul_top
    {N : Type*} [AddCommGroup N] [Module A N] (a : A) {x : N}
    (hx : x ∈ principalIdeal a • (⊤ : Submodule A N)) :
    ∃ y, a • y = x := by
  -- Proof comment: rewrite `aN` as the range of multiplication by `a`.
  have hx' : x ∈ LinearMap.range (LinearMap.lsmul A N a) := by
    rwa [range_lsmul_eq_principalIdeal_smul_top (A := A) (N := N) a]
  simpa [LinearMap.lsmul_apply] using LinearMap.mem_range.mp hx'

/-- Helper for Lemma 15.97.5: the target of the unreduced map `(d^i, -1)` is `f^i M^{i + 1}`. -/
private abbrev etaPairDeltaTarget : Submodule A (M.X (i + 1)) :=
  principalIdeal (f ^ i) • (⊤ : Submodule A (M.X (i + 1)))

/-- Helper for Lemma 15.97.5: scaling by `f^i` lands in the textbook submodule `f^i M^i`. -/
private theorem lsmul_pow_mem_powerSubmodule (x : M.X i) :
    (LinearMap.lsmul A (M.X i) (f ^ i)) x ∈ powerSubmodule f M i := by
  -- Proof comment: the image of multiplication by `f^i` is exactly the principal-ideal power
  -- submodule by the range computation already established above.
  rw [powerSubmodule, ← range_lsmul_eq_principalIdeal_smul_top
    (A := A) (N := M.X i) (a := f ^ i)]
  exact LinearMap.mem_range_self _ x

/-- Helper for Lemma 15.97.5: scaling by `f^(i + 1)` lands in `f^(i + 1) M^{i + 1}`. -/
private theorem lsmul_nextPow_mem_nextPowerSubmodule (y : M.X (i + 1)) :
    (LinearMap.lsmul A (M.X (i + 1)) (f ^ (i + 1))) y ∈ nextPowerSubmodule f M i := by
  -- Proof comment: this is the same range description in the successor degree.
  rw [nextPowerSubmodule, ← range_lsmul_eq_principalIdeal_smul_top
    (A := A) (N := M.X (i + 1)) (a := f ^ (i + 1))]
  exact LinearMap.mem_range_self _ y

/-- Helper for Lemma 15.97.5: scaling by `f^i` lands in the target submodule `f^i M^{i + 1}`. -/
private theorem lsmul_pow_mem_etaPairDeltaTarget (y : M.X (i + 1)) :
    (LinearMap.lsmul A (M.X (i + 1)) (f ^ i)) y ∈ etaPairDeltaTarget f M i := by
  -- Proof comment: the target submodule is itself the range of multiplication by `f^i`.
  rw [etaPairDeltaTarget, ← range_lsmul_eq_principalIdeal_smul_top
    (A := A) (N := M.X (i + 1)) (a := f ^ i)]
  exact LinearMap.mem_range_self _ y

/-- Helper for Lemma 15.97.5: multiplication by `f^i` viewed as a map onto the textbook
submodule `f^i M^i`. -/
private abbrev powerSubmoduleLift :
    M.X i →ₗ[A] powerSubmodule f M i :=
  (LinearMap.lsmul A (M.X i) (f ^ i)).codRestrict
    (powerSubmodule f M i)
    (lsmul_pow_mem_powerSubmodule (A := A) (f := f) (M := M) (i := i))

/-- Helper for Lemma 15.97.5: multiplication by `f^(i + 1)` viewed as a map onto
`f^(i + 1) M^{i + 1}`. -/
private abbrev nextPowerSubmoduleLift :
    M.X (i + 1) →ₗ[A] nextPowerSubmodule f M i :=
  (LinearMap.lsmul A (M.X (i + 1)) (f ^ (i + 1))).codRestrict
    (nextPowerSubmodule f M i)
    (lsmul_nextPow_mem_nextPowerSubmodule (A := A) (f := f) (M := M) (i := i))

/-- Helper for Lemma 15.97.5: multiplication by `f^i` viewed as a map onto the target submodule
for `(d^i, -1)`. -/
private abbrev etaPairDeltaTargetLift :
    M.X (i + 1) →ₗ[A] etaPairDeltaTarget f M i :=
  (LinearMap.lsmul A (M.X (i + 1)) (f ^ i)).codRestrict
    (etaPairDeltaTarget f M i)
    (lsmul_pow_mem_etaPairDeltaTarget (A := A) (f := f) (M := M) (i := i))

/-- Helper for Lemma 15.97.5: the source-side raw map `(d^i, -f)` before transporting into the
textbook power submodules. -/
private abbrev etaPresentationRawDelta :
    M.X i × M.X (i + 1) →ₗ[A] M.X (i + 1) :=
  LinearMap.sub
    ((M.d i (i + 1)).hom.comp (LinearMap.fst A (M.X i) (M.X (i + 1))))
    ((LinearMap.lsmul A (M.X (i + 1)) f).comp
      (LinearMap.snd A (M.X i) (M.X (i + 1))))

/-- Helper for Lemma 15.97.5: the nat-level presentation map `(f, d^i)` used for the raw
quotient model before transporting to the `ℤ`-indexed owner. -/
private abbrev natEtaPresentationMap :
    M.X i →ₗ[A] M.X i × M.X (i + 1) :=
  LinearMap.prod ((f • LinearMap.id : M.X i →ₗ[A] M.X i)) (M.d i (i + 1)).hom

/-- Helper for Lemma 15.97.5: the nat-level quotient model presented by `(f, d^i)`. This is the
source-faithful cokernel used to descend `(d^i, -f)` before the remaining `extend`-side
transport. -/
private abbrev natEtaPresentationQuotient :=
  (M.X i × M.X (i + 1)) ⧸ LinearMap.range (natEtaPresentationMap (A := A) (f := f) (M := M) (i := i))

/-- Helper for Lemma 15.97.5: transporting the canonical `ℤ`-indexed presentation quotient along
the degreewise `extendXIso` identifies it with the nat-level quotient presented by `(f, d^i)`. -/
private theorem nonempty_eta_presentation_quotient_linearEquiv_nat_presentation_quotient :
    Nonempty
      (etaPresentationQuotient f (M.extend embeddingUpNat) (i : ℤ) ≃ₗ[A]
        natEtaPresentationQuotient (A := A) (f := f) (M := M) (i := i)) := by
  let e₀ : (((M.extend embeddingUpNat).X (i : ℤ)) : ModuleCat A) ≃ₗ[A] M.X i :=
    (M.extendXIso embeddingUpNat rfl).toLinearEquiv
  let e₁ : (((M.extend embeddingUpNat).X ((i : ℤ) + 1)) : ModuleCat A) ≃ₗ[A] M.X (i + 1) := by
    simpa using
      (M.extendXIso embeddingUpNat
        (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv
  let e :
      ((((M.extend embeddingUpNat).X (i : ℤ)) : ModuleCat A) ×
          (((M.extend embeddingUpNat).X ((i : ℤ) + 1)) : ModuleCat A)) ≃ₗ[A]
        (M.X i × M.X (i + 1)) :=
    LinearEquiv.prodCongr e₀ e₁
  have happly :
      ∀ x : ((M.extend embeddingUpNat).X (i : ℤ)),
        e (etaPresentationLinearMap f (M.extend embeddingUpNat) (i : ℤ) x) =
          natEtaPresentationMap (A := A) (f := f) (M := M) (i := i) (e₀ x) := by
    intro x
    ext
    · simp [etaPresentationLinearMap, natEtaPresentationMap, e]
    · have hd :=
        congrArg ModuleCat.Hom.hom
          (HomologicalComplex.extend_d_eq
            (K := M) (e := embeddingUpNat)
            (i' := (i : ℤ)) (j' := (i : ℤ) + 1)
            (i := i) (j := i + 1)
            rfl
            (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1))
      have hd' := LinearMap.congr_fun hd x
      -- Route correction: transport only the canonical quotient across `extendXIso`; the local
      -- cokernel analysis remains on the nat-level quotient model.
      rw [hd']
      change e₁ (e₁.symm ((M.d i (i + 1)).hom (e₀ x))) = (M.d i (i + 1)).hom (e₀ x)
      simp
  have hrange :
      (LinearMap.range (etaPresentationLinearMap f (M.extend embeddingUpNat) (i : ℤ))).map
          e.toLinearMap =
        LinearMap.range (natEtaPresentationMap (A := A) (f := f) (M := M) (i := i)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases LinearMap.mem_range.mp hx with ⟨z, rfl⟩
      refine LinearMap.mem_range.mpr ⟨e₀ z, ?_⟩
      simpa using (happly z)
    · rintro ⟨z, rfl⟩
      refine Submodule.mem_map.mpr ⟨etaPresentationLinearMap f (M.extend embeddingUpNat) (i : ℤ)
          (e₀.symm z), LinearMap.mem_range_self _ (e₀.symm z), ?_⟩
      simpa using happly (e₀.symm z)
  -- Proof comment: once the presentation ranges match under the ambient product equivalence, the
  -- quotient transport is exactly `Submodule.Quotient.equiv`.
  exact ⟨Submodule.Quotient.equiv
    (LinearMap.range (etaPresentationLinearMap f (M.extend embeddingUpNat) (i : ℤ)))
    (LinearMap.range (natEtaPresentationMap (A := A) (f := f) (M := M) (i := i)))
    e
    hrange⟩

/-- Helper for Lemma 15.97.5: the nat-level presentation quotient carries the same principal
Fitting ideal as the canonical `extend`-side quotient. -/
private theorem nat_presentation_quotient_fittingIdeal_eq_principalIdeal_generator :
    Fit[A]_(Module.finrank A (M.X (i + 1)))
      (natEtaPresentationQuotient (A := A) (f := f) (M := M) (i := i)) =
        principalIdeal (Submodule.IsPrincipal.generator (M.etaDeterminantalIdeal f i)) := by
  rcases nonempty_eta_presentation_quotient_linearEquiv_nat_presentation_quotient
      (A := A) (f := f) (M := M) (i := i) with ⟨e⟩
  -- Proof comment: transport the intrinsic Fitting ideal across the quotient equivalence and then
  -- reuse the canonical presentation-quotient computation already proved above.
  calc
    Fit[A]_(Module.finrank A (M.X (i + 1)))
        (natEtaPresentationQuotient (A := A) (f := f) (M := M) (i := i)) =
      Fit[A]_(Module.finrank A (M.X (i + 1)))
        (etaPresentationQuotient f (M.extend embeddingUpNat) (i : ℤ)) := by
          symm
          simpa using
            fittingIdeal_eq_of_linearEquiv (R := A)
              (M := etaPresentationQuotient f (M.extend embeddingUpNat) (i : ℤ))
              (M' := natEtaPresentationQuotient (A := A) (f := f) (M := M) (i := i))
              (k := Module.finrank A (M.X (i + 1))) e
    _ = principalIdeal (Submodule.IsPrincipal.generator (M.etaDeterminantalIdeal f i)) := by
          simpa using
            presentation_quotient_fittingIdeal_eq_principalIdeal_generator
              (A := A) (f := f) (M := M) (i := i) hf hI

/-- Helper for Lemma 15.97.5: the raw delta map annihilates the image of the nat-level
presentation map `(f, d^i)`. -/
private theorem eta_presentation_raw_delta_kills_nat_presentation :
    LinearMap.range (natEtaPresentationMap (A := A) (f := f) (M := M) (i := i)) ≤
      LinearMap.ker ((etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i)).rangeRestrict) := by
  intro z hz
  rcases LinearMap.mem_range.mp hz with ⟨x, rfl⟩
  -- Proof comment: on a presentation generator `(f x, d x)`, the two terms of `(d^i, -f)`
  -- cancel exactly.
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  simp [natEtaPresentationMap, etaPresentationRawDelta, LinearMap.lsmul_apply, map_smul,
    LinearMap.comp_apply]

/-- Helper for Lemma 15.97.5: the raw map `(d^i, -f)` descended to the nat-level presentation
quotient. -/
private abbrev nat_eta_presentation_descended_delta :
    natEtaPresentationQuotient (A := A) (f := f) (M := M) (i := i) →ₗ[A]
      LinearMap.range (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i)) :=
  Submodule.liftQ
    (LinearMap.range (natEtaPresentationMap (A := A) (f := f) (M := M) (i := i)))
    ((etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i)).rangeRestrict)
    (eta_presentation_raw_delta_kills_nat_presentation (A := A) (f := f) (M := M) (i := i))

/-- Helper for Lemma 15.97.5: the descended raw delta map computes on quotient generators by the
obvious formula. -/
private theorem nat_eta_presentation_descended_delta_apply_mk (x : M.X i × M.X (i + 1)) :
    nat_eta_presentation_descended_delta (A := A) (f := f) (M := M) (i := i)
        (Submodule.Quotient.mk x) =
      (⟨etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i) x,
        LinearMap.mem_range_self _ x⟩ :
        LinearMap.range (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i))) := by
  -- Proof comment: the descended map was built by `Submodule.liftQ`, so it evaluates directly on
  -- a chosen representative.
  simpa [nat_eta_presentation_descended_delta] using
    DFunLike.congr_fun
      (Submodule.liftQ_mkQ
        (p := LinearMap.range (natEtaPresentationMap (A := A) (f := f) (M := M) (i := i)))
        (f := (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i)).rangeRestrict)
        (h := eta_presentation_raw_delta_kills_nat_presentation (A := A) (f := f) (M := M)
          (i := i)))
      x

/-- Helper for Lemma 15.97.5: the raw delta range has no `f`-power torsion. The source proof uses
that this range sits inside the finite free ambient module `M^{i + 1}`, where multiplication by
powers of the nonzerodivisor `f` is injective. -/
private theorem raw_delta_range_torsion'_eq_bot :
    Submodule.torsion' A
      (LinearMap.range (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i)))
      (Submonoid.powers f) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion'_iff] at hx
  rcases hx with ⟨a, ha⟩
  rcases Submonoid.mem_powers_iff.mp a.2 with ⟨n, rfl⟩
  -- Proof comment: forget the subtype and cancel `f^n` inside the ambient finite free module.
  have hsmul :
      (LinearMap.lsmul A (M.X (i + 1)) (f ^ n)) (x : M.X (i + 1)) =
        (LinearMap.lsmul A (M.X (i + 1)) (f ^ n)) 0 := by
    simpa [LinearMap.lsmul_apply] using congrArg Subtype.val ha
  have hinj :
      Function.Injective (LinearMap.lsmul A (M.X (i + 1)) (f ^ n)) :=
    lsmul_injective_of_nonZeroDivisor_of_finite_free
      (A := A) (N := M.X (i + 1)) (pow_mem hf n)
  apply Subtype.ext
  exact hinj hsmul

/-- Helper for Lemma 15.97.5: the kernel of the descended raw delta map is exactly the
`f`-power-torsion submodule of the nat-level presentation quotient. This is the textbook kernel
computation before the remaining transport back to the canonical `extend`-side quotient. -/
private theorem nat_eta_presentation_descended_delta_ker_eq_fPowerTorsion :
    LinearMap.ker (nat_eta_presentation_descended_delta (A := A) (f := f) (M := M) (i := i)) =
      Submodule.torsion' A
        (natEtaPresentationQuotient (A := A) (f := f) (M := M) (i := i))
        (Submonoid.powers f) := by
  ext q
  constructor
  · intro hq
    rw [LinearMap.mem_ker] at hq
    rcases Submodule.mkQ_surjective
        (LinearMap.range (natEtaPresentationMap (A := A) (f := f) (M := M) (i := i))) q with
      ⟨x, rfl⟩
    rcases x with ⟨u, v⟩
    rw [Submodule.mem_torsion'_iff]
    refine ⟨⟨f, Submonoid.mem_powers_iff.mpr ⟨1, by simp⟩⟩, ?_⟩
    -- Proof comment: if `(d^i, -f)` vanishes on `(u,v)`, then `f * [u,v]` is represented by the
    -- presentation vector `(f u, d u)` and hence dies in the quotient.
    have huv :
        (M.d i (i + 1)).hom u = f • v := by
      exact congrArg Subtype.val <| by
        simpa [nat_eta_presentation_descended_delta_apply_mk] using hq
    refine (Submodule.Quotient.mk_eq_zero
      (LinearMap.range (natEtaPresentationMap (A := A) (f := f) (M := M) (i := i)))).2 ?_
    refine LinearMap.mem_range.mpr ⟨u, ?_⟩
    ext <;> simp [natEtaPresentationMap, huv]
  · intro hq
    rw [LinearMap.mem_ker]
    -- Proof comment: any `f`-power-torsion class maps to `f`-power torsion in the raw range,
    -- which is impossible by the previous torsion-freeness lemma.
    have htors :
        nat_eta_presentation_descended_delta (A := A) (f := f) (M := M) (i := i) q ∈
          Submodule.torsion' A
            (LinearMap.range (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i)))
            (Submonoid.powers f) := by
      rw [Submodule.mem_torsion'_iff] at hq ⊢
      rcases hq with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      simpa [map_smul] using congrArg
        (nat_eta_presentation_descended_delta (A := A) (f := f) (M := M) (i := i)) ha
    have hbot :
        nat_eta_presentation_descended_delta (A := A) (f := f) (M := M) (i := i) q ∈
          (⊥ : Submodule A
            (LinearMap.range (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i)))) := by
      simpa [raw_delta_range_torsion'_eq_bot (A := A) (f := f) (M := M) (i := i)] using htors
    simpa using hbot

/-- Helper for Lemma 15.97.5: quotienting the nat-level presentation by its `f`-power torsion is
canonically equivalent to the raw delta range. -/
private noncomputable abbrev nat_eta_presentation_quotient_mod_fPowerTorsion_equiv_raw_delta_range :
    (natEtaPresentationQuotient (A := A) (f := f) (M := M) (i := i) ⧸
      Submodule.torsion' A
        (natEtaPresentationQuotient (A := A) (f := f) (M := M) (i := i))
        (Submonoid.powers f)) ≃ₗ[A]
      LinearMap.range (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i)) :=
  (Submodule.quotEquivOfEq _ _
      (nat_eta_presentation_descended_delta_ker_eq_fPowerTorsion
        (A := A) (f := f) (M := M) (i := i)).symm).trans
    (nat_eta_presentation_descended_delta (A := A) (f := f) (M := M) (i := i)).quotKerEquivRange

/-- Helper for Lemma 15.97.5: the scaling map onto `f^i M^i` is surjective by construction. -/
private theorem powerSubmoduleLift_range_eq_top :
    LinearMap.range (powerSubmoduleLift (A := A) (f := f) (M := M) (i := i)) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro x
  rcases exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (N := M.X i) (a := f ^ i) x.2 with ⟨y, hy⟩
  -- Proof comment: every point of `f^i M^i` is visibly an `f^i`-multiple.
  refine ⟨y, ?_⟩
  apply Subtype.ext
  simpa [powerSubmoduleLift, LinearMap.lsmul_apply] using hy

/-- Helper for Lemma 15.97.5: the scaling map onto `f^(i + 1) M^{i + 1}` is surjective by
construction. -/
private theorem nextPowerSubmoduleLift_range_eq_top :
    LinearMap.range (nextPowerSubmoduleLift (A := A) (f := f) (M := M) (i := i)) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro x
  rcases exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (N := M.X (i + 1)) (a := f ^ (i + 1)) x.2 with ⟨y, hy⟩
  -- Proof comment: the successor-degree power submodule is the same explicit image.
  refine ⟨y, ?_⟩
  apply Subtype.ext
  simpa [nextPowerSubmoduleLift, LinearMap.lsmul_apply] using hy

/-- Helper for Lemma 15.97.5: scaling by `f^i` is surjective onto the target `f^i M^{i + 1}`. -/
private theorem etaPairDeltaTargetLift_range_eq_top :
    LinearMap.range (etaPairDeltaTargetLift (A := A) (f := f) (M := M) (i := i)) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro x
  rcases exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (N := M.X (i + 1)) (a := f ^ i) x.2 with ⟨y, hy⟩
  -- Proof comment: the target subtype is another principal-ideal multiple, so the same witness
  -- argument applies.
  refine ⟨y, ?_⟩
  apply Subtype.ext
  simpa [etaPairDeltaTargetLift, LinearMap.lsmul_apply] using hy

/-- Helper for Lemma 15.97.5: scaling both source coordinates surjects onto
`f^i M^i × f^(i + 1) M^{i + 1}`. -/
private theorem etaPairScaledSourceMap_range_eq_top :
    LinearMap.range
        (LinearMap.prodMap
          (powerSubmoduleLift (A := A) (f := f) (M := M) (i := i))
          (nextPowerSubmoduleLift (A := A) (f := f) (M := M) (i := i))) = ⊤ := by
  rw [LinearMap.range_eq_top]
  rintro ⟨u, v⟩
  rcases exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (N := M.X i) (a := f ^ i) u.2 with ⟨x, hx⟩
  rcases exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (N := M.X (i + 1)) (a := f ^ (i + 1)) v.2 with ⟨y, hy⟩
  -- Proof comment: solve both coordinates separately and then combine the two witnesses.
  refine ⟨(x, y), ?_⟩
  ext
  · apply Subtype.ext
    simpa [powerSubmoduleLift, LinearMap.prodMap_apply, LinearMap.lsmul_apply] using hx
  · apply Subtype.ext
    simpa [nextPowerSubmoduleLift, LinearMap.prodMap_apply, LinearMap.lsmul_apply] using hy

/-- Helper for Lemma 15.97.5: the differential sends `f^i M^i` into `f^i M^{i + 1}`. -/
private theorem powerSubmodule_differential_mem_etaPairDeltaTarget
    (x : powerSubmodule f M i) :
    (M.d i (i + 1)).hom x ∈ etaPairDeltaTarget f M i := by
  rcases exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (N := M.X i) (a := f ^ i) x.2 with
    ⟨y, hy⟩
  -- Proof comment: differentiate an explicit `f^i`-multiple and keep the same scalar factor.
  rw [etaPairDeltaTarget, ← range_lsmul_eq_principalIdeal_smul_top
    (A := A) (N := M.X (i + 1)) (a := f ^ i)]
  refine LinearMap.mem_range.mpr ⟨(M.d i (i + 1)).hom y, ?_⟩
  calc
    (LinearMap.lsmul A (M.X (i + 1)) (f ^ i)) ((M.d i (i + 1)).hom y) =
        (M.d i (i + 1)).hom ((LinearMap.lsmul A (M.X i) (f ^ i)) y) := by
          simp [LinearMap.lsmul_apply]
    _ = (M.d i (i + 1)).hom x := by
          rw [hy]

/-- Helper for Lemma 15.97.5: the deeper power submodule `f^(i + 1) M^{i + 1}` lies inside
`f^i M^{i + 1}`. -/
private theorem nextPowerSubmodule_le_etaPairDeltaTarget :
    nextPowerSubmodule f M i ≤ etaPairDeltaTarget f M i := by
  intro x hx
  rw [etaPairDeltaTarget, ← range_lsmul_eq_principalIdeal_smul_top
    (A := A) (N := M.X (i + 1)) (a := f ^ i)]
  rw [← range_lsmul_eq_principalIdeal_smul_top
    (A := A) (N := M.X (i + 1)) (a := f ^ (i + 1))] at hx
  rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
  -- Proof comment: factor `f^(i + 1)` as `f^i * f` and absorb the extra factor into the witness.
  refine LinearMap.mem_range.mpr ⟨f • y, ?_⟩
  simp [LinearMap.lsmul_apply, pow_succ, smul_smul, mul_assoc]

/-- Helper for Lemma 15.97.5: the first leg of `(d^i, -1)` on
`f^i M^i ⊕ f^(i + 1) M^(i + 1)`. -/
private abbrev powerSubmoduleDifferentialToEtaPairDeltaTarget :
    powerSubmodule f M i →ₗ[A] etaPairDeltaTarget f M i :=
  ((M.d i (i + 1)).hom.comp (powerSubmodule f M i).subtype).codRestrict
    (etaPairDeltaTarget f M i)
    (powerSubmodule_differential_mem_etaPairDeltaTarget (f := f) (M := M) (i := i))

/-- Helper for Lemma 15.97.5: the unreduced map `(d^i, -1)` on
`f^i M^i ⊕ f^(i + 1) M^(i + 1)`. -/
private abbrev etaPairDeltaMap :
    powerSubmodule f M i × nextPowerSubmodule f M i →ₗ[A] etaPairDeltaTarget f M i :=
  LinearMap.sub
    (powerSubmoduleDifferentialToEtaPairDeltaTarget (f := f) (M := M) (i := i)).comp
      (LinearMap.fst A (powerSubmodule f M i) (nextPowerSubmodule f M i))
    ((Submodule.inclusion (nextPowerSubmodule_le_etaPairDeltaTarget
      (f := f) (M := M) (i := i))).comp
      (LinearMap.snd A (powerSubmodule f M i) (nextPowerSubmodule f M i)))

/-- Helper for Lemma 15.97.5: after scaling both source coordinates by the textbook powers, the
map `(d^i, -1)` is exactly the raw presentation map `(d^i, -f)` followed by the target scaling by
`f^i`. -/
private theorem etaPairDeltaMap_comp_scaled_eq :
    (etaPairDeltaMap f M i).comp
        (LinearMap.prodMap
          (powerSubmoduleLift (A := A) (f := f) (M := M) (i := i))
          (nextPowerSubmoduleLift (A := A) (f := f) (M := M) (i := i))) =
      (etaPairDeltaTargetLift (A := A) (f := f) (M := M) (i := i)).comp
        (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i)) := by
  ext z
  rcases z with ⟨x, y⟩
  -- Proof comment: once the three codomain restrictions are expanded, both sides become the same
  -- explicit element `f^i • (d^i x - f • y)` of `f^i M^{i + 1}`.
  apply Subtype.ext
  simp [etaPairDeltaMap, etaPresentationRawDelta, powerSubmoduleLift, nextPowerSubmoduleLift,
    etaPairDeltaTargetLift, powerSubmoduleDifferentialToEtaPairDeltaTarget,
    LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.sub_apply, LinearMap.lsmul_apply,
    map_smul, pow_succ, smul_sub, smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 15.97.5: the actual delta range is the image of the raw range under the
single remaining target scaling map. -/
private theorem etaPairDeltaMap_range_eq_rawDelta_range_map :
    LinearMap.range (etaPairDeltaMap f M i) =
      (LinearMap.range (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i))).map
        (etaPairDeltaTargetLift (A := A) (f := f) (M := M) (i := i)) := by
  -- Proof comment: the surjective source scaling maps remove the domain transport, and the final
  -- range computation packages the remaining target transport as a single `Submodule.map`.
  calc
    LinearMap.range (etaPairDeltaMap f M i) =
      LinearMap.range
        ((etaPairDeltaMap f M i).comp
          (LinearMap.prodMap
            (powerSubmoduleLift (A := A) (f := f) (M := M) (i := i))
            (nextPowerSubmoduleLift (A := A) (f := f) (M := M) (i := i))) := by
          symm
          rw [LinearMap.range_comp_of_range_eq_top]
          exact etaPairScaledSourceMap_range_eq_top (A := A) (f := f) (M := M) (i := i)
    _ = LinearMap.range
          ((etaPairDeltaTargetLift (A := A) (f := f) (M := M) (i := i)).comp
            (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i))) := by
          rw [etaPairDeltaMap_comp_scaled_eq (A := A) (f := f) (M := M) (i := i)]
    _ = (LinearMap.range (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i))).map
          (etaPairDeltaTargetLift (A := A) (f := f) (M := M) (i := i)) := by
          symm
          simpa [LinearMap.range_comp] using
            LinearMap.range_comp
              (etaPresentationRawDelta (A := A) (f := f) (M := M) (i := i))
              (etaPairDeltaTargetLift (A := A) (f := f) (M := M) (i := i))

/-- Helper for Lemma 15.97.5: the kernel of `(d^i, -1)` is exactly the image of `(1, d^i)`. -/
private theorem etaPairDeltaMap_ker_eq_range :
    LinearMap.ker (etaPairDeltaMap f M i) = LinearMap.range (etaPairMap f M i) := by
  ext z
  constructor
  · intro hz
    rcases z with ⟨u, v⟩
    have huv_zero :
        ((etaPairDeltaMap f M i) (u, v) : M.X (i + 1)) = 0 := by
      exact congrArg Subtype.val hz
    have huv :
        (M.d i (i + 1)).hom u = v := by
      simpa [etaPairDeltaMap, powerSubmoduleDifferentialToEtaPairDeltaTarget, sub_eq_zero] using
        huv_zero
    let xEta : etaFDegreeSubmodule f M i :=
      ⟨u, ⟨u.2, by
        simpa [huv] using v.2⟩⟩
    -- Proof comment: a kernel pair is determined by its first coordinate, which already lies in
    -- the Berthelot-Ogus degree term because its differential lands in `f^(i + 1) M^(i + 1)`.
    refine LinearMap.mem_range.mpr ⟨xEta, ?_⟩
    ext
    · rfl
    · apply Subtype.ext
      exact huv
  · rintro ⟨x, rfl⟩
    -- Proof comment: on the image of `(1, d^i)`, the two coordinates cancel by definition.
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    simp [etaPairDeltaMap, etaPairMap,
      powerSubmoduleDifferentialToEtaPairDeltaTarget,
      BerthelotOgusEtaReduction.Nat.degreeDifferentialToNextPowerSubmodule]

/-- Helper for Lemma 15.97.5: `rangeRestrict` does not change the kernel of `(d^i, -1)`. -/
private theorem etaPairDeltaMap_rangeRestrict_ker_eq :
    LinearMap.ker ((etaPairDeltaMap f M i).rangeRestrict) =
      LinearMap.ker (etaPairDeltaMap f M i) := by
  ext z
  constructor
  · intro hz
    exact congrArg Subtype.val hz
  · intro hz
    apply Subtype.ext
    exact hz

/-- Helper for Lemma 15.97.5: `(d^i, -1)` vanishes on the image of `(1, d^i)`. -/
private theorem etaPairDeltaMap_rangeRestrict_comp_etaPairMap_eq_zero :
    ((etaPairDeltaMap f M i).rangeRestrict).comp (etaPairMap f M i) = 0 := by
  ext x
  apply Subtype.ext
  simp [etaPairDeltaMap, etaPairMap,
    powerSubmoduleDifferentialToEtaPairDeltaTarget,
    BerthelotOgusEtaReduction.Nat.degreeDifferentialToNextPowerSubmodule]

/-- Helper for Lemma 15.97.5: the textbook row
`0 → (η_f M)^i → f^i M^i ⊕ f^(i + 1) M^(i + 1) → im(d^i,-1) → 0`
as a short complex. -/
private abbrev etaPairRangeShortComplex : ShortComplex (ModuleCat A) :=
  ShortComplex.mk
    (ModuleCat.ofHom (etaPairMap f M i))
    (ModuleCat.ofHom ((etaPairDeltaMap f M i).rangeRestrict))
    (congrArg ModuleCat.ofHom
      (etaPairDeltaMap_rangeRestrict_comp_etaPairMap_eq_zero (f := f) (M := M) (i := i)))

/-- Helper for Lemma 15.97.5: the textbook row with cokernel replaced by `im(d^i,-1)` is short
exact. -/
private theorem etaPairRangeShortComplex_shortExact :
    (etaPairRangeShortComplex f M i).ShortExact := by
  let S : ShortComplex (ModuleCat A) := etaPairRangeShortComplex f M i
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: the middle exactness is exactly the kernel/range computation for `(d^i,-1)`.
    change S.Exact
    rw [S.moduleCat_exact_iff_range_eq_ker]
    calc
      LinearMap.range S.f.hom = LinearMap.range (etaPairMap f M i) := by
        rfl
      _ = LinearMap.ker (etaPairDeltaMap f M i) := (etaPairDeltaMap_ker_eq_range
          (f := f) (M := M) (i := i)).symm
      _ = LinearMap.ker ((etaPairDeltaMap f M i).rangeRestrict) := by
        symm
        exact etaPairDeltaMap_rangeRestrict_ker_eq (f := f) (M := M) (i := i)
      _ = LinearMap.ker S.g.hom := by
        rfl
  · -- Proof comment: the first coordinate of `(1, d^i)` is the subtype inclusion, hence injective.
    refine (ModuleCat.mono_iff_injective _).2 ?_
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun p ↦ (p.1 : M.X i)) hxy
  · -- Proof comment: `rangeRestrict` is surjective onto its own range by construction.
    exact (ModuleCat.epi_iff_surjective _).2 (etaPairDeltaMap f M i).surjective_rangeRestrict

/-- Helper for Lemma 15.97.5: once `im(d^i,-1)` is projective, the short exact row splits and
`(1, d^i)` is split mono. -/
private theorem etaPairMap_isSplitMono_of_deltaRange_projective
    [Module.Projective A (LinearMap.range (etaPairDeltaMap f M i))] :
    IsSplitMono (ModuleCat.ofHom (etaPairMap f M i)) := by
  let S : ShortComplex (ModuleCat A) := etaPairRangeShortComplex f M i
  have hS : S.ShortExact := etaPairRangeShortComplex_shortExact (f := f) (M := M) (i := i)
  letI : IsSplitMono S.f := (hS.splittingOfProjective).isSplitMono_f
  simpa [S, etaPairRangeShortComplex]

-- Proof sketch: after localizing at each prime, choose a generator of the principal ideal
-- `I_i(M^\bullet, f)` and apply Lemma `15.8.10` to the quotient by the torsion of the cokernel of
-- `(f, d^i)`. The textbook argument identifies `(η_f M)^i` with the kernel of `(d^i, -1)` inside
-- the split exact three-term complex built from `f^i M^i`, `f^(i + 1) M^i`, and
-- `f^(i + 1) M^(i + 1)`, which yields the claimed local freeness and rank.
/-- Lemma 15.97.5: if `f` is a nonzerodivisor in `A`, the terms `M^i` and `M^{i + 1}` are finite
free, and `I_i(M^\bullet, f)` is principal, then the degree-`i` term `(η_f M)^i` is finite locally
free of rank `rk(M^i)`. -/
@[stacks 0F7W]
theorem etaFDegree_finiteLocallyFreeOfRank_of_determinantalIdeal_isPrincipal
    :
    Module.FiniteLocallyFreeOfRank A ((η[f] M).X i) (Module.finrank A (M.X i)) := by
  -- TODO: the principal Fitting-ideal transport is now established on the nat-level quotient via
  -- `nat_presentation_quotient_fittingIdeal_eq_principalIdeal_generator`. The remaining
  -- source-faithful blocker is the away-local graph-quotient step identifying the localized nat
  -- presentation quotient with the localized next term, so that Lemma `15.8.10` can be applied
  -- to transport projectivity and the rank `rk(M^{i+1})` from the torsion-free quotient back to
  -- `LinearMap.range (etaPairDeltaMap f M i)`, after which the short exact row computes the rank
  -- of `(η_f M)^i`.
  sorry

-- Proof sketch: with the same local normal form as in the rank statement, the image of
-- `(1, d^i)` identifies with the kernel of `(d^i, -1)` in a short exact sequence whose cokernel
-- is the torsion-free quotient controlled by Lemma `15.8.10`. The quotient is projective, so the
-- short exact sequence splits and `(1, d^i)` becomes the inclusion of a direct summand.
/-- Under the principal-ideal hypothesis on `I_i(M^\bullet, f)`, the canonical map
`(1, d^i) : (η_f M)^i → f^i M^i × f^(i + 1) M^(i + 1)` is a split monomorphism, i.e. the
inclusion of a direct summand. -/
theorem etaFDegreePairMap_isSplitMono_of_determinantalIdeal_isPrincipal
    :
    IsSplitMono (ModuleCat.ofHom (etaPairMap f M i)) := by
  -- TODO: once the remaining away-local quotient bridge feeds Lemma `15.8.10`, projectivity of
  -- `LinearMap.range (etaPairDeltaMap f M i)` will follow from the already-established nat-level
  -- quotient transport, and this theorem will then close immediately via
  -- `etaPairMap_isSplitMono_of_deltaRange_projective`.
  sorry

end
