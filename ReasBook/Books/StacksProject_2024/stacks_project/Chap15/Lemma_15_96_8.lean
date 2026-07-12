import StacksProject_2024.Chap15.BerthelotOgusEtaReductionNatPairMap
import StacksProject_2024.Chap15.LinearMapIdentifiesWithProdSubmodules

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open HomologicalComplex

universe u

section

variable {A : Type u} [CommRing A]

namespace BerthelotOgusInt

/-- Helper for Lemma 15.96.8: a `ℤ`-indexed cochain complex is termwise `f`-torsion free if
multiplication by `f` is injective in every degree. -/
class IsTermwiseFTorsionFree (f : A) (K : ModuleComplex A) : Prop where
  /-- Helper for Lemma 15.96.8: multiplication by `f` is injective in degree `i`. -/
  isSMulRegular (i : ℤ) : IsSMulRegular (K.X i) f

/-- Helper for Lemma 15.96.8: the owner torsion-free class gives the degreewise regularity
instance. -/
instance (f : A) (K : ModuleComplex A) [h : IsTermwiseFTorsionFree f K] (i : ℤ) :
    IsSMulRegular (K.X i) f :=
  h.isSMulRegular i

end BerthelotOgusInt

namespace IsTermwiseFTorsionFree

/-- Helper for Lemma 15.96.8: extension by zero carries bounded-below termwise `f`-torsion
freeness to the owner `ℤ`-indexed torsion-freeness predicate. -/
theorem toIsTermwiseFTorsionFree
    {f : A} {M : NatModuleCochainComplex A} (hM : IsTermwiseFTorsionFree f M) :
    BerthelotOgusInt.IsTermwiseFTorsionFree f (M.extend ComplexShape.embeddingUpNat) := by
  constructor
  intro j
  by_cases hj : 0 ≤ j
  · let e :
        ((M.extend ComplexShape.embeddingUpNat).X j) ≃ₗ[A] M.X j.toNat :=
      (M.extendXIso ComplexShape.embeddingUpNat (Int.toNat_of_nonneg hj)).toLinearEquiv
    -- In nonnegative degrees, extension by zero is identified with the original term.
    exact (LinearEquiv.isSMulRegular_congr e f).2 (hM.isSMulRegular j.toNat)
  · let hzero : CategoryTheory.Limits.IsZero ((M.extend ComplexShape.embeddingUpNat).X j) :=
      M.isZero_extend_X ComplexShape.embeddingUpNat j (by
        intro n hnj
        exact hj (hnj ▸ Int.natCast_nonneg n))
    letI : Subsingleton ((M.extend ComplexShape.embeddingUpNat).X j) :=
      ModuleCat.subsingleton_of_isZero hzero
    -- In negative degrees, the extended complex is zero, so regularity is automatic.
    exact IsSMulRegular.of_right_eq_zero_of_smul (fun x _hx => Subsingleton.elim _ _)

end IsTermwiseFTorsionFree

namespace ModFSquared

/-- Helper for Lemma 15.96.8: `(f²)M` is contained in `fM`. -/
private theorem principalIdeal_sq_smul_top_le
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) :
    principalIdeal (f ^ 2) • (⊤ : Submodule A M) ≤
      Submodule.comap (LinearMap.id : M →ₗ[A] M)
        (principalIdeal f • (⊤ : Submodule A M)) := by
  have hpow : principalIdeal (f ^ 2) ≤ principalIdeal f := by
    refine (Ideal.span_singleton_le_iff_mem _).2 ?_
    rw [principalIdeal, pow_two]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  simpa using Submodule.smul_mono hpow le_rfl

/-- Helper for Lemma 15.96.8: the reduction `K / f²K → K / fK` in degree `i`. -/
private abbrev reductionComponent (f : A) (K : ModuleComplex A) (i : ℤ) :
    (CochainComplex.reduceModIdealA (A := A) (principalIdeal (f ^ 2)) K).X i ⟶
      (CochainComplex.reduceModIdealA (A := A) (principalIdeal f) K).X i :=
  ModuleCat.ofHom <|
    Submodule.mapQ
      (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
      (principalIdeal f • (⊤ : Submodule A (K.X i)))
      (LinearMap.id : K.X i →ₗ[A] K.X i)
      (principalIdeal_sq_smul_top_le (A := A) f)

/-- Helper for Lemma 15.96.8: the reduction component is induced by the identity on
representatives. -/
private theorem reductionComponent_apply_mk
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : K.X i) :
    (reductionComponent (A := A) f K i).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x :
        K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := by
  simpa [reductionComponent, LinearMap.id_apply] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ
        (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
        (principalIdeal f • (⊤ : Submodule A (K.X i)))
        (LinearMap.id : K.X i →ₗ[A] K.X i))
      x

/-- Helper for Lemma 15.96.8: the reduction components commute with the reduced differentials. -/
private theorem reductionComponent_comm
    (f : A) (K : ModuleComplex A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    CommSq
      (reductionComponent (A := A) f K i)
      ((CochainComplex.reduceModIdealA (A := A) (principalIdeal (f ^ 2)) K).d i j)
      ((CochainComplex.reduceModIdealA (A := A) (principalIdeal f) K).d i j)
      (reductionComponent (A := A) f K j) := by
  rcases hij with rfl
  apply CommSq.mk
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun q ↦ ?_
  refine Quotient.inductionOn' q ?_
  intro x
  change
    ((CochainComplex.reduceModIdealA (A := A) (principalIdeal f) K).d i (i + 1)).hom
        ((reductionComponent (A := A) f K i).hom (Submodule.Quotient.mk x)) =
      (reductionComponent (A := A) f K (i + 1)).hom
        (((CochainComplex.reduceModIdealA (A := A) (principalIdeal (f ^ 2)) K).d i (i + 1)).hom
          (Submodule.Quotient.mk x))
  rw [reductionComponent_apply_mk, reductionComponent_apply_mk]
  calc
    ((CochainComplex.reduceModIdealA (A := A) (principalIdeal f) K).d i (i + 1)).hom
        (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk ((K.d i (i + 1)).hom x) :
        K.X (i + 1) ⧸ principalIdeal f • (⊤ : Submodule A (K.X (i + 1)))) := by
          exact reduceModIdealA_d_apply_mk_owner
            (A := A) (I := principalIdeal f) (L := K) (j := i) x
    _ = (reductionComponent (A := A) f K (i + 1)).hom
          (Submodule.Quotient.mk ((K.d i (i + 1)).hom x) :
            K.X (i + 1) ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X (i + 1)))) := by
          rw [reductionComponent_apply_mk]
    _ = (reductionComponent (A := A) f K (i + 1)).hom
          (((CochainComplex.reduceModIdealA (A := A) (principalIdeal (f ^ 2)) K).d i (i + 1)).hom
            (Submodule.Quotient.mk x)) := by
          exact congrArg
            ((reductionComponent (A := A) f K (i + 1)).hom)
            (reduceModIdealA_d_apply_mk_owner
              (A := A) (I := principalIdeal (f ^ 2)) (L := K) (j := i) x).symm

/-- Helper for Lemma 15.96.8: the reduction map `K / f²K → K / fK`. -/
private def reductionMap (f : A) (K : ModuleComplex A) :
    CochainComplex.reduceModIdealA (A := A) (principalIdeal (f ^ 2)) K ⟶
      CochainComplex.reduceModIdealA (A := A) (principalIdeal f) K where
  f i := reductionComponent (A := A) f K i
  comm' i j hij := (reductionComponent_comm (A := A) f K i j hij).w

/-- The condition that `Ker(d mod f²) → Ker(d mod f)` is surjective on the owner complex. -/
abbrev cyclesReductionSurjective (f : A) (K : ModuleComplex A) (i : ℤ) : Prop :=
  Epi (cyclesMap (reductionMap (A := A) f K) i)

namespace Nat

/-- The bounded-below bridge/view of `Ker(d mod f²) → Ker(d mod f)` being surjective. -/
abbrev cyclesReductionSurjective
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) : Prop :=
  ModFSquared.cyclesReductionSurjective (A := A) f
    (M.extend ComplexShape.embeddingUpNat) (i : ℤ)

end Nat

end ModFSquared

namespace BerthelotOgusEtaReduction

/-- Helper for Lemma 15.96.8: the reduced Berthelot-Ogus complex `(η_f K) / f (η_f K)`. -/
abbrev complex (f : A) (K : ModuleComplex A) :
    ModuleComplex (A ⧸ principalIdeal f) :=
  CochainComplex.reduceModIdeal (A := A) (principalIdeal f) (BerthelotOgusInt.complex f K)

/- Domain-style sampling:
- primary domain: the Berthelot-Ogus reduction complex for arbitrary cochain complexes of
  `A`-modules, together with the reduced canonical map `(1, d^i)` from
  `(η_f K)^i / f(η_f K)^i`;
- sampled owner declarations:
  `BerthelotOgusInt.degreeSubmodule`,
  `BerthelotOgusEtaReduction.complex`,
  `BerthelotOgusEtaReduction.toCycles`,
  `CochainComplex.reduceModIdeal`,
  `LinearMap.reduceModIdeal`;
- best owner abstraction:
  `source-facing`: the reduced pair map
    `(η_f K)^i / f(η_f K)^i → f^i K^i / f^(i + 1) K^i ×
      f^(i + 1) K^(i + 1) / f^(i + 2) K^(i + 1)`
    for `K : ModuleComplex A` and `i : ℤ`;
  `core/canonical`: the existing owner `ModuleComplex A` together with the canonical reduced
    Berthelot-Ogus complex `BerthelotOgusEtaReduction.complex f K` over `A ⧸ (f)` and cocycle map
    `toCycles f K i`;
  `bridge/view`: the bounded-below `Nat` specialization obtained from the standard extension
    `M.extend ComplexShape.embeddingUpNat` and direct use of
    `CochainComplex.reduceModIdeal (principalIdeal f) (η[f] M)`;
- primitive data vs derived API: the primitive owner data are the canonical source owner
  `(complex f K).X i`, the quotient targets, and the reduced pair map. The bounded-below
  `Nat` statements should be derived bridge lemmas, not the main public owner. -/

private theorem range_lsmul_eq_principalIdeal_smul_top
    {M : Type*} [AddCommGroup M] [Module A M] (a : A) :
    LinearMap.range (LinearMap.lsmul A M a) =
      principalIdeal a • (⊤ : Submodule A M) := by
  ext x
  constructor
  · intro hx
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    -- A visible `a`-multiple already lies in the principal-ideal multiple by construction.
    simpa [principalIdeal, LinearMap.lsmul_apply] using
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a)
        (show y ∈ (⊤ : Submodule A M) by simp))
  · intro hx
    -- To recover a range witness, it is enough to expand the generators of `aM`.
    have hle : principalIdeal a • (⊤ : Submodule A M) ≤ LinearMap.range (LinearMap.lsmul A M a) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      rcases Ideal.mem_span_singleton.mp hr with ⟨b, rfl⟩
      refine LinearMap.mem_range.mpr ⟨b • y, ?_⟩
      simp [LinearMap.lsmul_apply, smul_smul, mul_comm]
    exact hle hx

/-- Helper for Lemma 15.96.8: multiplication by a power of an `f`-regular scalar stays
injective. -/
private theorem lsmul_pow_injective_owner
    {N : Type*} [AddCommGroup N] [Module A N] {f : A}
    (hf : IsSMulRegular N f) (n : ℕ) :
    Function.Injective (LinearMap.lsmul A N (f ^ n)) := by
  intro x y hxy
  induction n with
  | zero =>
      -- In degree zero, multiplication by `1` is the identity.
      simpa using hxy
  | succ n ih =>
      -- Cancel one visible factor of `f`, then invoke the induction hypothesis on `f ^ n`.
      apply ih
      apply hf
      simpa [LinearMap.lsmul_apply, pow_succ, smul_smul, mul_comm, mul_left_comm, mul_assoc]
        using hxy

/-- Helper for Lemma 15.96.8: an owner degree term carries its canonical witness in the range of
multiplication by `f ^ Int.toNat i`. -/
private abbrev eta_degree_to_power_range_owner
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    BerthelotOgusInt.degreeSubmodule f K i →ₗ[A]
      LinearMap.range (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)) :=
  LinearMap.codRestrict
    (LinearMap.range (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)))
    (BerthelotOgusInt.degreeSubmodule f K i).subtype
    (fun x ↦ x.2.1)

/-- Helper for Lemma 15.96.8: the visible `f ^ Int.toNat i` factor identifies `K.X i` with its
image in the owner degree term. -/
private noncomputable abbrev power_range_equiv_owner
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (hK : BerthelotOgusInt.IsTermwiseFTorsionFree f K) :
    K.X i ≃ₗ[A] LinearMap.range (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)) :=
  LinearEquiv.ofInjective
    (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i))
    (lsmul_pow_injective_owner (A := A) (N := K.X i) (f := f) (hK.isSMulRegular i)
      (Int.toNat i))

/-- Helper for Lemma 15.96.8: divide an owner degree-term representative by its visible
`f ^ Int.toNat i` factor. -/
private noncomputable abbrev divide_eta_degree_repr_owner
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (hK : BerthelotOgusInt.IsTermwiseFTorsionFree f K) :
    BerthelotOgusInt.degreeSubmodule f K i →ₗ[A] K.X i :=
  ((power_range_equiv_owner f K i hK).symm : _ ≃ₗ[A] _).toLinearMap.comp
    (eta_degree_to_power_range_owner f K i)

/-- Helper for Lemma 15.96.8: multiplying the divided owner representative by the visible power
recovers the original degree-term element. -/
private theorem smul_divide_eta_degree_repr_owner
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (hK : BerthelotOgusInt.IsTermwiseFTorsionFree f K)
    (x : BerthelotOgusInt.degreeSubmodule f K i) :
    (f ^ Int.toNat i) • divide_eta_degree_repr_owner f K i hK x = x := by
  -- The divided representative is chosen as the inverse image of the stored range witness.
  change
    (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i))
        (((power_range_equiv_owner f K i hK).symm) ⟨x.1, x.2.1⟩) = x.1
  simpa [power_range_equiv_owner] using
    congrArg Subtype.val ((power_range_equiv_owner f K i hK).apply_symm_apply ⟨x.1, x.2.1⟩)

/-- Helper for Lemma 15.96.8: in nonnegative degrees, the differential of the divided owner
representative is divisible by `f`. -/
private theorem divide_eta_degree_d_mem_principal_owner
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (hK : BerthelotOgusInt.IsTermwiseFTorsionFree f K)
    (hi : 0 ≤ i)
    (x : BerthelotOgusInt.degreeSubmodule f K i) :
    (K.d i (i + 1)).hom (divide_eta_degree_repr_owner f K i hK x) ∈
      principalIdeal f • (⊤ : Submodule A (K.X (i + 1))) := by
  rcases x.2.2 with ⟨y, hy⟩
  -- Apply the differential to the recovered equality `x = f ^ Int.toNat i • x'`.
  have hmul :
      (f ^ Int.toNat i) •
          ((K.d i (i + 1)).hom (divide_eta_degree_repr_owner f K i hK x)) =
        (f ^ Int.toNat i) • (f • y) := by
    calc
      (f ^ Int.toNat i) •
          ((K.d i (i + 1)).hom (divide_eta_degree_repr_owner f K i hK x)) =
        (K.d i (i + 1)).hom ((f ^ Int.toNat i) • divide_eta_degree_repr_owner f K i hK x) := by
          rw [_root_.map_smul]
      _ = (K.d i (i + 1)).hom x := by
          rw [smul_divide_eta_degree_repr_owner f K i hK x]
      _ = (f ^ Int.toNat (i + 1)) • y := by
          simpa [LinearMap.lsmul_apply] using hy.symm
      _ = (f ^ Int.toNat i) • (f • y) := by
          have hi_succ : 0 ≤ i + 1 := by linarith
          rw [Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hi_succ]
          simp [pow_succ, smul_smul, mul_comm]
  have hcancel :
      (K.d i (i + 1)).hom (divide_eta_degree_repr_owner f K i hK x) = f • y := by
    exact
      (lsmul_pow_injective_owner (A := A) (N := K.X (i + 1)) (f := f)
        (hK.isSMulRegular (i + 1)) (Int.toNat i)) hmul
  -- Once the differential is written as `f • y`, it lies in `(f) K.X (i + 1)`.
  rw [hcancel]
  simpa [principalIdeal] using
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f)
      (show y ∈ (⊤ : Submodule A (K.X (i + 1))) by simp))

/-- Helper for Lemma 15.96.8: transporting a cycle through `moduleCatCyclesIso.hom` forgets to
the same ambient element as the canonical cycle inclusion. -/
private theorem moduleCatCyclesIso_hom_iCycles_owner
    (S : ShortComplex (ModuleCat A)) (z : S.cycles) :
    (S.moduleCatCyclesIso.hom z).1 = S.iCycles.hom z := by
  -- The categorical cycles object is definitionally the same kernel used by
  -- `moduleCatCyclesIso`.
  rfl

/-- Helper for Lemma 15.96.8: transporting a concrete kernel element back through
`moduleCatCyclesIso.inv` forgets to its original ambient representative. -/
private theorem moduleCatCyclesIso_inv_iCycles_owner
    (S : ShortComplex (ModuleCat A)) (u : LinearMap.ker S.g.hom) :
    S.iCycles.hom (S.moduleCatCyclesIso.inv.hom u) = u.1 := by
  -- Compare the transported cycle with `u` after pushing it forward again through
  -- `moduleCatCyclesIso.hom`.
  calc
    S.iCycles.hom (S.moduleCatCyclesIso.inv.hom u) =
        (S.moduleCatCyclesIso.hom (S.moduleCatCyclesIso.inv.hom u)).1 := by
          symm
          exact moduleCatCyclesIso_hom_iCycles_owner
            (S := S) (z := S.moduleCatCyclesIso.inv.hom u)
    _ = u.1 := by
          simpa using congrArg Subtype.val (S.moduleCatCyclesIso.inv_hom_id_apply u)

/-- Helper for Lemma 15.96.8: the successor degree in `K.sc i` is exactly `i + 1`. -/
private theorem shortComplex_next_degree_transport_owner (i : ℤ) :
    (ComplexShape.up ℤ).next i = i + 1 := by
  -- For the cochain shape on `ℤ`, the chosen successor is the evident adjacent degree.
  classical
  simp [ComplexShape.next, ComplexShape.up, ComplexShape.up']

/-- Helper for Lemma 15.96.8: an ambient element in degree `i + 1` whose next differential
vanishes packages canonically as a cycle in degree `i + 1`. -/
private theorem exists_cycle_of_d_next_eq_zero_owner
    (K : ModuleComplex A) (i : ℤ) {y : K.X (i + 1)}
    (hy : (K.d (i + 1) ((i + 1) + 1)).hom y = 0) :
    ∃ q : K.cycles (i + 1), (K.iCycles (i + 1)).hom q = y := by
  let u : LinearMap.ker (((K.sc (i + 1)).g).hom) := by
    refine ⟨y, ?_⟩
    -- The owner short complex in degree `i + 1` uses the outgoing differential to `(i + 1) + 1`.
    change (K.d (i + 1) ((ComplexShape.up ℤ).next (i + 1))).hom y = 0
    rw [shortComplex_next_degree_transport_owner (i := i + 1)]
    exact hy
  refine ⟨(K.sc (i + 1)).moduleCatCyclesIso.inv.hom u, ?_⟩
  -- Forgetting the transported cycle recovers the original representative.
  simpa [u] using
    moduleCatCyclesIso_inv_iCycles_owner (S := K.sc (i + 1)) (u := u)

variable (f : A) (K : ModuleComplex A) (i : ℤ)

/-- The submodule `f^i K^i` appearing in degree `i` of the Berthelot-Ogus construction. -/
abbrev powerSubmodule : Submodule A (K.X i) :=
  principalIdeal (f ^ Int.toNat i) • (⊤ : Submodule A (K.X i))

/-- The submodule `f^(i + 1) K^(i + 1)` appearing in the target of `(1, d^i)`. -/
abbrev nextPowerSubmodule : Submodule A (K.X (i + 1)) :=
  principalIdeal (f ^ Int.toNat (i + 1)) • (⊤ : Submodule A (K.X (i + 1)))

/-- The degree-`i` Berthelot-Ogus term is a submodule of `f^i K^i`. -/
theorem degreeSubmodule_le_powerSubmodule :
    BerthelotOgusInt.degreeSubmodule f K i ≤ powerSubmodule f K i :=
  by
    simpa [powerSubmodule, range_lsmul_eq_principalIdeal_smul_top] using
      (show
        BerthelotOgusInt.degreeSubmodule f K i ≤
          LinearMap.range (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)) from
        inf_le_left)

/-- The differential on `η_f K` followed by the inclusion into `f^(i + 1) K^(i + 1)`. -/
abbrev degreeDifferentialToNextPowerSubmodule :
    BerthelotOgusInt.degreeSubmodule f K i →ₗ[A] nextPowerSubmodule f K i :=
  (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f K (i + 1))) ∘ₗ
    BerthelotOgusInt.differentialLinear f K i

/-- The canonical reduction of `(1, d^i)` modulo `f` on the chapter's `ModuleComplex` owner. -/
abbrev etaReductionPairMap :
    (complex f K).X i →ₗ[A ⧸ principalIdeal f]
      ((powerSubmodule f K i ⧸
          principalIdeal f • (⊤ : Submodule A (powerSubmodule f K i))) ×
        (nextPowerSubmodule f K i ⧸
          principalIdeal f • (⊤ : Submodule A (nextPowerSubmodule f K i)))) :=
  LinearMap.prod
    (LinearMap.reduceModIdeal (principalIdeal f)
      (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f K i)))
    (LinearMap.reduceModIdeal (principalIdeal f)
      (degreeDifferentialToNextPowerSubmodule f K i))

/-- Helper for Lemma 15.96.8: the first coordinate of the reduced pair map. -/
private abbrev etaReductionPairMapFst :
    (complex f K).X i →ₗ[A ⧸ principalIdeal f]
      (powerSubmodule f K i ⧸
        principalIdeal f • (⊤ : Submodule A (powerSubmodule f K i))) :=
  (LinearMap.fst (A ⧸ principalIdeal f)
      (powerSubmodule f K i ⧸
        principalIdeal f • (⊤ : Submodule A (powerSubmodule f K i)))
      (nextPowerSubmodule f K i ⧸
        principalIdeal f • (⊤ : Submodule A (nextPowerSubmodule f K i)))).comp
    (etaReductionPairMap f K i)

/-- Helper for Lemma 15.96.8: the second coordinate of the reduced pair map. -/
private abbrev etaReductionPairMapSnd :
    (complex f K).X i →ₗ[A ⧸ principalIdeal f]
      (nextPowerSubmodule f K i ⧸
        principalIdeal f • (⊤ : Submodule A (nextPowerSubmodule f K i))) :=
  (LinearMap.snd (A ⧸ principalIdeal f)
      (powerSubmodule f K i ⧸
        principalIdeal f • (⊤ : Submodule A (powerSubmodule f K i)))
      (nextPowerSubmodule f K i ⧸
        principalIdeal f • (⊤ : Submodule A (nextPowerSubmodule f K i)))).comp
    (etaReductionPairMap f K i)

/-- Helper for Lemma 15.96.8: on quotient generators, the first coordinate of `(1, d^i)` is the
class of the ambient inclusion into `f^i K^i`. -/
private theorem etaReductionPairMapFst_apply_mk
    (x : BerthelotOgusInt.degreeSubmodule f K i) :
    etaReductionPairMapFst f K i (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk
        ((Submodule.inclusion (degreeSubmodule_le_powerSubmodule f K i)) x) :
          powerSubmodule f K i ⧸
            principalIdeal f • (⊤ : Submodule A (powerSubmodule f K i))) := by
  -- The first coordinate is the quotient map induced by the degreewise inclusion.
  simp [etaReductionPairMapFst, etaReductionPairMap, LinearMap.reduceModIdeal_apply]

/-- Helper for Lemma 15.96.8: on quotient generators, the second coordinate of `(1, d^i)` is the
class of the restricted differential in `f^(i + 1) K^(i + 1)`. -/
private theorem etaReductionPairMapSnd_apply_mk
    (x : BerthelotOgusInt.degreeSubmodule f K i) :
    etaReductionPairMapSnd f K i (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk
        (degreeDifferentialToNextPowerSubmodule f K i x) :
          nextPowerSubmodule f K i ⧸
            principalIdeal f • (⊤ : Submodule A (nextPowerSubmodule f K i))) := by
  -- The second coordinate is the quotient map induced by the restricted differential.
  simp [etaReductionPairMapSnd, etaReductionPairMap, LinearMap.reduceModIdeal_apply]

/-- Helper for Lemma 15.96.8: the two ambient reduced complexes used in the representative lift
argument. -/
private abbrev modFComplexOwner (f : A) (K : ModuleComplex A) :=
  CochainComplex.reduceModIdealA (principalIdeal f) K

/-- Helper for Lemma 15.96.8: the reduction modulo `f²` of the owner complex. -/
private abbrev modFSquaredComplexOwner (f : A) (K : ModuleComplex A) :=
  CochainComplex.reduceModIdealA (principalIdeal (f ^ 2)) K

/-- Helper for Lemma 15.96.8: the owner reduction map `K / f²K → K / fK`. -/
private abbrev reductionMapOwner (f : A) (K : ModuleComplex A) :
    modFSquaredComplexOwner f K ⟶ modFComplexOwner f K :=
  ModFSquared.reductionMap (A := A) f K

/-- Helper for Lemma 15.96.8: membership in `fM` is equivalent to being an explicit `f`-multiple.
-/
private theorem exists_smul_eq_of_mem_principalIdeal_smul_top
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) {x : M}
    (hx : x ∈ principalIdeal f • (⊤ : Submodule A M)) :
    ∃ y, f • y = x := by
  -- Rewrite the denominator as the range of multiplication by `f`.
  have hx' : x ∈ LinearMap.range (LinearMap.lsmul A M f) := by
    rwa [range_lsmul_eq_principalIdeal_smul_top (A := A) (M := M) f]
  simpa [LinearMap.lsmul_apply] using LinearMap.mem_range.mp hx'

/-- Helper for Lemma 15.96.8: every visible `f`-multiple vanishes in the quotient by `fM`. -/
private theorem quotient_mk_smul_eq_zero
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) (x : M) :
    (Submodule.Quotient.mk (f • x) :
      M ⧸ principalIdeal f • (⊤ : Submodule A M)) = 0 := by
  -- The class vanishes because `f • x` already lies in the denominator `fM`.
  have hx_top : x ∈ (⊤ : Submodule A M) := by simp
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  simpa [principalIdeal] using
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) hx_top)

/-- Helper for Lemma 15.96.8: on quotient generators, the differential of `K / IK` is the
quotient class of the original differential. -/
private theorem reduceModIdeal_d_apply_mk_owner
    {ι : Type*} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (L : CochainComplex (ModuleCat A) ι) (j : ι) (x : L.X j) :
    (ModuleCat.Hom.hom ((CochainComplex.reduceModIdeal I L).d j (j + 1)))
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((L.d j (j + 1)).hom x) := by
  classical
  delta CochainComplex.reduceModIdeal
  rw [@CochainComplex.of_d _ _ _ ι _ _ (Classical.decEq ι)]
  simpa only [ModuleCat.hom_ofHom] using
    (LinearMap.reduceModIdeal_apply (I := I) (f := (L.d j (j + 1)).hom) x)

/-- Helper for Lemma 15.96.8: scalar restriction does not change the reduced differential on
quotient generators. -/
private theorem reduceModIdealA_d_apply_mk_owner
    {ι : Type*} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (L : CochainComplex (ModuleCat A) ι) (j : ι) (x : L.X j) :
    (ModuleCat.Hom.hom ((CochainComplex.reduceModIdealA I L).d j (j + 1)))
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((L.d j (j + 1)).hom x) := by
  simpa [CochainComplex.reduceModIdealA] using
    reduceModIdeal_d_apply_mk_owner (A := A) (I := I) (L := L) (j := j) x

/-- Helper for Lemma 15.96.8: the owner reduction map `K / f²K → K / fK` is induced by the
identity on representatives. -/
private theorem reductionMapOwner_f_apply_mk
    (f : A) (K : ModuleComplex A) (i : ℤ) (x : K.X i) :
    ((reductionMapOwner f K).f i).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x :
        K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := by
  -- The owner reduction map is the quotient map induced by the identity linear map.
  simpa [reductionMapOwner] using
    ModFSquared.reductionComponent_apply_mk (A := A) (f := f) (K := K) (i := i) (x := x)

/-- Helper for Lemma 15.96.8: after forgetting to ambient degree `i`, the cycles map induced by
`K / f²K → K / fK` is the ambient reduction map. -/
private theorem cyclesMap_reduction_iCycles_owner
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (z' : (modFSquaredComplexOwner f K).cycles i) :
    ((modFComplexOwner f K).iCycles i).hom
        ((cyclesMap (reductionMapOwner f K) i).hom z') =
      ((reductionMapOwner f K).f i).hom
        (((modFSquaredComplexOwner f K).iCycles i).hom z') := by
  let φ :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.up ℤ) i).map
      (reductionMapOwner f K)
  -- Evaluate the standard naturality square for `ShortComplex.cyclesMap`.
  exact congrArg
    (fun g : (modFSquaredComplexOwner f K).cycles i ⟶ (modFComplexOwner f K).X i ↦ g.hom z')
    (by
      simpa [φ, HomologicalComplex.shortComplexFunctor, HomologicalComplex.cyclesMap,
        reductionMapOwner] using
        (ShortComplex.cyclesMap_i φ))

/-- Helper for Lemma 15.96.8: surjectivity on reduced cycles lifts an ambient representative
whose differential is divisible by `f` to one whose differential is divisible by `f²` while
preserving the class modulo `f`. -/
private theorem cyclesReductionSurjective_lift_representative
    (hf : IsRegular f)
    (hK : BerthelotOgusInt.IsTermwiseFTorsionFree f K)
    (hsurj : ModFSquared.cyclesReductionSurjective f K i)
    (a : K.X i)
    (ha : (K.d i (i + 1)).hom a ∈ principalIdeal f • (⊤ : Submodule A (K.X (i + 1)))) :
    ∃ a' : K.X i,
      a' - a ∈ principalIdeal f • (⊤ : Submodule A (K.X i)) ∧
        (K.d i (i + 1)).hom a' ∈ principalIdeal (f ^ 2) •
          (⊤ : Submodule A (K.X (i + 1))) := by
  -- The class of `a` modulo `f` is a cycle because `d a` is already divisible by `f`.
  have ha_cycle :
      ((modFComplexOwner f K).d i (i + 1)).hom
          (Submodule.Quotient.mk a :
            K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) = 0 := by
    calc
      ((modFComplexOwner f K).d i (i + 1)).hom
          (Submodule.Quotient.mk a :
            K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) =
        (Submodule.Quotient.mk ((K.d i (i + 1)).hom a) :
          K.X (i + 1) ⧸ principalIdeal f • (⊤ : Submodule A (K.X (i + 1)))) := by
            exact reduceModIdealA_d_apply_mk_owner
              (A := A) (I := principalIdeal f) (L := K) (j := i) a
      _ = 0 := by
            exact (Submodule.Quotient.mk_eq_zero _).2 ha
  obtain ⟨z, hz⟩ :=
    exists_cycle_of_d_next_eq_zero_owner
      (A := A) (K := modFComplexOwner f K) (i := i) (y := Submodule.Quotient.mk a) ha_cycle
  have hcycles_surj :
      Function.Surjective (cyclesMap (reductionMapOwner f K) i).hom := by
    let _ : Epi (cyclesMap (reductionMapOwner f K) i) := hsurj
    exact (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨z', hz'⟩ := hcycles_surj z
  obtain ⟨a', ha'⟩ :=
    Submodule.mkQ_surjective
      (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
      (((modFSquaredComplexOwner f K).iCycles i).hom z')
  refine ⟨a', ?_⟩
  constructor
  · -- Comparing the lifted cycle after reduction shows that `a'` and `a` agree modulo `f`.
    have hmk :
        (Submodule.Quotient.mk a' :
          K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) =
        (Submodule.Quotient.mk a :
          K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := by
      calc
        (Submodule.Quotient.mk a' :
            K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) =
          ((reductionMapOwner f K).f i).hom
            (Submodule.Quotient.mk a' :
              K.X i ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i))) := by
              symm
              exact reductionMapOwner_f_apply_mk (A := A) (f := f) (K := K) (i := i) a'
        _ = ((reductionMapOwner f K).f i).hom
              (((modFSquaredComplexOwner f K).iCycles i).hom z') := by
              rw [ha']
        _ = ((modFComplexOwner f K).iCycles i).hom
              ((cyclesMap (reductionMapOwner f K) i).hom z') := by
              symm
              exact cyclesMap_reduction_iCycles_owner (A := A) (f := f) (K := K) (i := i) z'
        _ = ((modFComplexOwner f K).iCycles i).hom z := by
              rw [hz']
        _ = (Submodule.Quotient.mk a :
              K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := hz
    have hsub_zero :
        (Submodule.Quotient.mk (a' - a) :
          K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) = 0 := by
      calc
        (Submodule.Quotient.mk (a' - a) :
            K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) =
          (Submodule.Quotient.mk a' :
            K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) -
            (Submodule.Quotient.mk a :
              K.X i ⧸ principalIdeal f • (⊤ : Submodule A (K.X i))) := by
                simp
        _ = 0 := by
              simpa using sub_eq_zero.mpr hmk
    exact (Submodule.Quotient.mk_eq_zero _).1 hsub_zero
  · -- Because `z'` is a cycle modulo `f²`, the differential of `a'` is divisible by `f²`.
    have hz'_cycle :
        ((modFSquaredComplexOwner f K).d i (i + 1)).hom
            (((modFSquaredComplexOwner f K).iCycles i).hom z') = 0 := by
      exact LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom ((modFSquaredComplexOwner f K).iCycles_d i (i + 1))) z'
    rw [ha'] at hz'_cycle
    have hd_zero :
        (Submodule.Quotient.mk ((K.d i (i + 1)).hom a') :
          K.X (i + 1) ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X (i + 1)))) = 0 := by
      calc
        (Submodule.Quotient.mk ((K.d i (i + 1)).hom a') :
            K.X (i + 1) ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X (i + 1)))) =
          ((modFSquaredComplexOwner f K).d i (i + 1)).hom
            (Submodule.Quotient.mk a' :
              K.X i ⧸ principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i))) := by
              symm
              exact reduceModIdealA_d_apply_mk_owner
                (A := A) (I := principalIdeal (f ^ 2)) (L := K) (j := i) a'
        _ = 0 := hz'_cycle
    exact (Submodule.Quotient.mk_eq_zero _).1 hd_zero

/-- Helper for Lemma 15.96.8: if the first coordinate is already realized on the kernel of the
second coordinate and the two coordinate kernels meet trivially, then the pair map identifies its
source with a product of submodules. -/
private theorem identifiesWithProdSubmodules_of_fst_lift_and_kernel_separation
    {R : Type*} [CommRing R]
    {M N₁ N₂ : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    (s : M →ₗ[R] N₁ × N₂)
    (hfst :
      LinearMap.range
        (((LinearMap.fst R N₁ N₂).comp s).domRestrict
          (LinearMap.ker ((LinearMap.snd R N₁ N₂).comp s))) =
        LinearMap.range ((LinearMap.fst R N₁ N₂).comp s))
    (hker :
      LinearMap.ker ((LinearMap.fst R N₁ N₂).comp s) ⊓
        LinearMap.ker ((LinearMap.snd R N₁ N₂).comp s) = ⊥) :
    s.identifiesWithProdSubmodules := by
  let α : M →ₗ[R] N₁ := (LinearMap.fst R N₁ N₂).comp s
  let β : M →ₗ[R] N₂ := (LinearMap.snd R N₁ N₂).comp s
  let P₁ : Submodule R N₁ := LinearMap.range (α.domRestrict (LinearMap.ker β))
  let P₂ : Submodule R N₂ := LinearMap.range (β.domRestrict (LinearMap.ker α))
  refine ⟨P₁, P₂, ?_, ?_⟩
  · intro x y hxy
    -- A coincidence under the pair map forces both coordinate differences to vanish.
    have hs : s (x - y) = 0 := by
      rw [LinearMap.map_sub, hxy, sub_self]
    have hmem : x - y ∈ LinearMap.ker α ⊓ LinearMap.ker β := by
      constructor
      · change α (x - y) = 0
        simpa [α] using congrArg Prod.fst hs
      · change β (x - y) = 0
        simpa [β] using congrArg Prod.snd hs
    have hzero : x - y ∈ (⊥ : Submodule R M) := by
      simpa [hker] using hmem
    exact sub_eq_zero.mp hzero
  · ext z
    constructor
    · rintro ⟨x, rfl⟩
      -- Replace the source element by one with the same first coordinate and vanishing second
      -- coordinate, then record the complementary second-coordinate correction inside `ker α`.
      have hxα : α x ∈ LinearMap.range α := LinearMap.mem_range.mpr ⟨x, rfl⟩
      rw [← hfst] at hxα
      rcases LinearMap.mem_range.mp hxα with ⟨x₀, hx₀⟩
      have hx₀β : β x₀ = 0 := x₀.2
      have hα : α x₀ = α x := by
        simpa [α] using hx₀
      have hx_minus : x - x₀ ∈ LinearMap.ker α := by
        change α (x - x₀) = 0
        rw [LinearMap.map_sub, hα, sub_self]
      constructor
      · change α x ∈ P₁
        exact LinearMap.mem_range.mpr ⟨x₀, by simpa [α] using hα⟩
      · change β x ∈ P₂
        refine LinearMap.mem_range.mpr ⟨⟨x - x₀, hx_minus⟩, ?_⟩
        have hβ : β (x - x₀) = β x := by
          rw [LinearMap.map_sub, hx₀β, sub_zero]
        simpa [β] using hβ.symm
    · intro hz
      rcases hz with ⟨hz₁, hz₂⟩
      rcases LinearMap.mem_range.mp hz₁ with ⟨x₀, hx₀⟩
      rcases LinearMap.mem_range.mp hz₂ with ⟨y₀, hy₀⟩
      -- Summing representatives from `ker β` and `ker α` realizes an arbitrary pair in
      -- `P₁.prod P₂`.
      refine LinearMap.mem_range.mpr ⟨x₀ + y₀, ?_⟩
      ext
      · have hy₀α : α y₀ = 0 := y₀.2
        change α (x₀ + y₀) = z.1
        rw [LinearMap.map_add, hy₀α, add_zero]
        simpa [α] using hx₀
      · have hx₀β : β x₀ = 0 := x₀.2
        change β (x₀ + y₀) = z.2
        rw [LinearMap.map_add, hx₀β, zero_add]
        simpa [β] using hy₀

/-- Helper for Lemma 15.96.8: surjectivity of `Ker(d mod f²) → Ker(d mod f)` should realize every
first coordinate of the reduced pair map on the kernel of the second coordinate. -/
private theorem exists_same_fst_zero_snd_class_of_divided_lift
    (hK : BerthelotOgusInt.IsTermwiseFTorsionFree f K)
    (hi : 0 ≤ i)
    (x : BerthelotOgusInt.degreeSubmodule f K i)
    {a' : K.X i}
    (ha' :
      a' - divide_eta_degree_repr_owner f K i hK x ∈
        principalIdeal f • (⊤ : Submodule A (K.X i)))
    (hda' :
      (K.d i (i + 1)).hom a' ∈
        principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X (i + 1)))) :
    ∃ x' : BerthelotOgusInt.degreeSubmodule f K i,
      etaReductionPairMapFst f K i (Submodule.Quotient.mk x') =
        etaReductionPairMapFst f K i (Submodule.Quotient.mk x) ∧
        etaReductionPairMapSnd f K i (Submodule.Quotient.mk x') = 0 := by
  let a := divide_eta_degree_repr_owner f K i hK x
  have hi_succ : 0 ≤ i + 1 := by linarith
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (f := f ^ 2) (M := K.X (i + 1)) hda'
  have hx'_range :
      (f ^ Int.toNat i) • a' ∈ LinearMap.range (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)) := by
    exact ⟨a', rfl⟩
  have hx'_d :
      (K.d i (i + 1)).hom ((f ^ Int.toNat i) • a') ∈
        LinearMap.range (LinearMap.lsmul A (K.X (i + 1)) (f ^ Int.toNat (i + 1))) := by
    refine ⟨f • c, ?_⟩
    -- Proof comment: the lifted representative has differential divisible by `f²`, so after
    -- multiplying back by the visible `f ^ i` factor it lands in `f ^ (i + 1)`.
    calc
      (f ^ Int.toNat (i + 1)) • (f • c) = (f ^ Int.toNat i * f) • (f • c) := by
        rw [Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hi_succ, pow_succ]
      _ = (f ^ Int.toNat i) • ((f * f) • c) := by
        simp [smul_smul, mul_assoc]
      _ = (f ^ Int.toNat i) • ((f ^ 2) • c) := by
        rw [pow_two]
      _ = (f ^ Int.toNat i) • (K.d i (i + 1)).hom a' := by
        rw [hc]
      _ = (K.d i (i + 1)).hom ((f ^ Int.toNat i) • a') := by
        rw [_root_.map_smul]
  have hx'_mem :
      (f ^ Int.toNat i) • a' ∈ BerthelotOgusInt.degreeSubmodule f K i := by
    exact ⟨hx'_range, hx'_d⟩
  let x' : BerthelotOgusInt.degreeSubmodule f K i := ⟨(f ^ Int.toNat i) • a', hx'_mem⟩
  obtain ⟨b, hb⟩ :=
    exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (f := f) (M := K.X i) (by simpa [a] using ha')
  have hw_mem : (f ^ Int.toNat i) • b ∈ powerSubmodule f K i := by
    change (f ^ Int.toNat i) • b ∈ principalIdeal (f ^ Int.toNat i) •
        (⊤ : Submodule A (K.X i))
    simpa [principalIdeal] using
      (Submodule.smul_mem_smul
        (Ideal.mem_span_singleton_self (f ^ Int.toNat i))
        (show b ∈ (⊤ : Submodule A (K.X i)) by simp))
  let w : powerSubmodule f K i := ⟨(f ^ Int.toNat i) • b, hw_mem⟩
  have hfst_val :
      (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f K i)) x' -
          (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f K i)) x =
        f • w := by
    apply Subtype.ext
    -- Proof comment: modulo the first target, the difference is exactly the visible `f`-multiple
    -- coming from `a' - a ∈ f K^i`.
    change (f ^ Int.toNat i) • a' - x = f • ((f ^ Int.toNat i) • b)
    calc
      (f ^ Int.toNat i) • a' - x =
          (f ^ Int.toNat i) • a' - (f ^ Int.toNat i) • a := by
            rw [smul_divide_eta_degree_repr_owner (f := f) (K := K) (i := i) (hK := hK) (x := x)]
      _ = (f ^ Int.toNat i) • (a' - a) := by
            rw [smul_sub]
      _ = (f ^ Int.toNat i) • (f • b) := by
            rw [hb]
      _ = f • ((f ^ Int.toNat i) • b) := by
            simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
  have hfst :
      etaReductionPairMapFst f K i (Submodule.Quotient.mk x') =
        etaReductionPairMapFst f K i (Submodule.Quotient.mk x) := by
    rw [etaReductionPairMapFst_apply_mk, etaReductionPairMapFst_apply_mk]
    apply (Submodule.Quotient.eq _).2
    -- Proof comment: the first coordinates differ by an explicit `f`-multiple inside
    -- `powerSubmodule`.
    rw [hfst_val]
    simpa [principalIdeal] using
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f)
        (show w ∈ (⊤ : Submodule A (powerSubmodule f K i)) by simp))
  have hz_mem : (f ^ Int.toNat (i + 1)) • c ∈ nextPowerSubmodule f K i := by
    change (f ^ Int.toNat (i + 1)) • c ∈ principalIdeal (f ^ Int.toNat (i + 1)) •
        (⊤ : Submodule A (K.X (i + 1)))
    simpa [principalIdeal] using
      (Submodule.smul_mem_smul
        (Ideal.mem_span_singleton_self (f ^ Int.toNat (i + 1)))
        (show c ∈ (⊤ : Submodule A (K.X (i + 1))) by simp))
  let z : nextPowerSubmodule f K i := ⟨(f ^ Int.toNat (i + 1)) • c, hz_mem⟩
  have hsnd_val :
      degreeDifferentialToNextPowerSubmodule f K i x' = f • z := by
    apply Subtype.ext
    -- Proof comment: the lifted representative has second coordinate visibly divisible by `f`,
    -- so its quotient class in the second target vanishes.
    change (K.d i (i + 1)).hom ((f ^ Int.toNat i) • a') =
      f • ((f ^ Int.toNat (i + 1)) • c)
    calc
      (K.d i (i + 1)).hom ((f ^ Int.toNat i) • a') =
          (f ^ Int.toNat i) • (K.d i (i + 1)).hom a' := by
            rw [_root_.map_smul]
      _ = (f ^ Int.toNat i) • ((f ^ 2) • c) := by
            rw [hc]
      _ = f • ((f ^ Int.toNat (i + 1)) • c) := by
            rw [Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hi_succ, pow_succ]
            simp [pow_two, smul_smul, mul_assoc, mul_left_comm, mul_comm]
  have hsnd :
      etaReductionPairMapSnd f K i (Submodule.Quotient.mk x') = 0 := by
    rw [etaReductionPairMapSnd_apply_mk, hsnd_val]
    simpa using quotient_mk_smul_eq_zero (A := A) (f := f) z
  exact ⟨x', hfst, hsnd⟩

private theorem first_range_eq_range_on_second_ker_of_cyclesReductionSurjective
    (hf : IsRegular f)
    (hK : BerthelotOgusInt.IsTermwiseFTorsionFree f K)
    (hsurj : ModFSquared.cyclesReductionSurjective f K i)
    (hi : 0 ≤ i) :
    LinearMap.range
      ((etaReductionPairMapFst f K i).domRestrict
        (LinearMap.ker (etaReductionPairMapSnd f K i))) =
      LinearMap.range (etaReductionPairMapFst f K i) := by
  -- Route correction: the original owner-level statement is false in negative degrees, so the
  -- source-faithful lifting argument is carried out only when `i` is nonnegative, exactly as in
  -- the textbook bounded-below situation.
  apply le_antisymm
  · intro y hy
    rcases LinearMap.mem_range.mp hy with ⟨x, rfl⟩
    exact LinearMap.mem_range.mpr ⟨x.1, rfl⟩
  · intro y hy
    rcases LinearMap.mem_range.mp hy with ⟨q, rfl⟩
    refine Quotient.inductionOn' q ?_
    intro x
    let a := divide_eta_degree_repr_owner f K i hK x
    have ha :
        (K.d i (i + 1)).hom a ∈ principalIdeal f • (⊤ : Submodule A (K.X (i + 1))) := by
      simpa [a] using
        divide_eta_degree_d_mem_principal_owner (f := f) (K := K) (i := i) hK hi x
    obtain ⟨a', ha', hda'⟩ :=
      cyclesReductionSurjective_lift_representative
        (f := f) (K := K) (i := i) hf hK hsurj a ha
    obtain ⟨x', hfst, hsnd⟩ :=
      exists_same_fst_zero_snd_class_of_divided_lift
        (f := f) (K := K) (i := i) hK hi x ha' hda'
    exact
      LinearMap.mem_range.mpr ⟨⟨Submodule.Quotient.mk x', hsnd⟩, hfst⟩

/-- Helper for Lemma 15.96.8: regularity and termwise `f`-torsion-freeness force the two
coordinate kernels of the reduced pair map to intersect trivially. -/
private theorem exists_smul_eq_of_pair_map_fst_eq_zero_and_snd_eq_zero
    (hK : BerthelotOgusInt.IsTermwiseFTorsionFree f K)
    (hi : 0 ≤ i)
    (x : BerthelotOgusInt.degreeSubmodule f K i)
    (hfst :
      etaReductionPairMapFst f K i (Submodule.Quotient.mk x) = 0)
    (hsnd :
      etaReductionPairMapSnd f K i (Submodule.Quotient.mk x) = 0) :
    ∃ y : BerthelotOgusInt.degreeSubmodule f K i, f • y = x := by
  let a := divide_eta_degree_repr_owner f K i hK x
  have hi_succ : 0 ≤ i + 1 := by linarith
  have hfst_mem :
      (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f K i)) x ∈
        principalIdeal f • (⊤ : Submodule A (powerSubmodule f K i)) := by
    rw [etaReductionPairMapFst_apply_mk] at hfst
    exact (Submodule.Quotient.mk_eq_zero _).1 hfst
  obtain ⟨u, hu⟩ :=
    exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (f := f) (M := powerSubmodule f K i) hfst_mem
  obtain ⟨b, hb_range⟩ :=
    exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (f := f ^ Int.toNat i) (M := K.X i) (by
        change (u : K.X i) ∈ principalIdeal (f ^ Int.toNat i) • (⊤ : Submodule A (K.X i))
        simpa [powerSubmodule] using u.2)
  have ha_eq : a = f • b := by
    apply (lsmul_pow_injective_owner (A := A) (N := K.X i) (f := f)
      (hK.isSMulRegular i) (Int.toNat i))
    -- Proof comment: the first-coordinate vanishing says that the visible `f ^ i` factor of `x`
    -- comes from an additional factor of `f`.
    calc
      (f ^ Int.toNat i) • a = x := by
        simpa [a] using smul_divide_eta_degree_repr_owner (f := f) (K := K) (i := i) hK x
      _ = (f • u : powerSubmodule f K i) := by
        simpa using congrArg Subtype.val hu.symm
      _ = f • ((f ^ Int.toNat i) • b) := by
        rw [hb_range]
      _ = (f ^ Int.toNat i) • (f • b) := by
        simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
  have hsnd_mem :
      degreeDifferentialToNextPowerSubmodule f K i x ∈
        principalIdeal f • (⊤ : Submodule A (nextPowerSubmodule f K i)) := by
    rw [etaReductionPairMapSnd_apply_mk] at hsnd
    exact (Submodule.Quotient.mk_eq_zero _).1 hsnd
  obtain ⟨v, hv⟩ :=
    exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (f := f) (M := nextPowerSubmodule f K i) hsnd_mem
  obtain ⟨c, hc_range⟩ :=
    exists_smul_eq_of_mem_principalIdeal_smul_top
      (A := A) (f := f ^ Int.toNat (i + 1)) (M := K.X (i + 1)) (by
        change (v : K.X (i + 1)) ∈ principalIdeal (f ^ Int.toNat (i + 1)) •
            (⊤ : Submodule A (K.X (i + 1)))
        simpa [nextPowerSubmodule] using v.2)
  have hda_eq :
      (K.d i (i + 1)).hom a = (f ^ 2) • c := by
    apply (lsmul_pow_injective_owner (A := A) (N := K.X (i + 1)) (f := f)
      (hK.isSMulRegular (i + 1)) (Int.toNat i))
    -- Proof comment: the vanishing second coordinate upgrades divisibility of `d a` from `f` to
    -- `f²`.
    calc
      (f ^ Int.toNat i) • (K.d i (i + 1)).hom a =
          (K.d i (i + 1)).hom ((f ^ Int.toNat i) • a) := by
            rw [_root_.map_smul]
      _ = (K.d i (i + 1)).hom x := by
            rw [smul_divide_eta_degree_repr_owner (f := f) (K := K) (i := i) (hK := hK) (x := x)]
      _ = (degreeDifferentialToNextPowerSubmodule f K i x : nextPowerSubmodule f K i) := by
            rfl
      _ = (f • v : nextPowerSubmodule f K i) := by
            simpa using congrArg Subtype.val hv.symm
      _ = f • ((f ^ Int.toNat (i + 1)) • c) := by
            rw [hc_range]
      _ = (f ^ Int.toNat i) • ((f ^ 2) • c) := by
            rw [Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hi_succ, pow_succ]
            simp [pow_two, smul_smul, mul_assoc, mul_left_comm, mul_comm]
  have hdb :
      (K.d i (i + 1)).hom b ∈ principalIdeal f • (⊤ : Submodule A (K.X (i + 1))) := by
    have hdb_eq : (K.d i (i + 1)).hom b = f • c := by
      apply hK.isSMulRegular (i + 1)
      -- Proof comment: cancel the extra `f` once more after rewriting `a = f • b`.
      calc
        f • (K.d i (i + 1)).hom b =
            (K.d i (i + 1)).hom (f • b) := by
              rw [← _root_.map_smul]
        _ = (K.d i (i + 1)).hom a := by
              rw [ha_eq]
        _ = (f ^ 2) • c := hda_eq
        _ = f • (f • c) := by
              rw [pow_two]
              simp [smul_smul]
    rw [hdb_eq]
    simpa [principalIdeal] using
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f)
        (show c ∈ (⊤ : Submodule A (K.X (i + 1))) by simp))
  have hy_range :
      (f ^ Int.toNat i) • b ∈ LinearMap.range (LinearMap.lsmul A (K.X i) (f ^ Int.toNat i)) := by
    exact ⟨b, rfl⟩
  have hy_d :
      (K.d i (i + 1)).hom ((f ^ Int.toNat i) • b) ∈
        LinearMap.range (LinearMap.lsmul A (K.X (i + 1)) (f ^ Int.toNat (i + 1))) := by
    obtain ⟨c', hc'⟩ :=
      exists_smul_eq_of_mem_principalIdeal_smul_top
        (A := A) (f := f) (M := K.X (i + 1)) hdb
    refine ⟨c', ?_⟩
    -- Proof comment: once `d b` is an explicit `f`-multiple, multiplying by the visible `f ^ i`
    -- factor puts `d ((f ^ i) • b)` in `f ^ (i + 1)`.
    calc
      (f ^ Int.toNat (i + 1)) • c' = (f ^ Int.toNat i * f) • c' := by
        rw [Int.toNat_of_nonneg hi, Int.toNat_of_nonneg hi_succ, pow_succ]
      _ = (f ^ Int.toNat i) • (f • c') := by
        simp [smul_smul, mul_assoc]
      _ = (f ^ Int.toNat i) • (K.d i (i + 1)).hom b := by
        rw [hc']
      _ = (K.d i (i + 1)).hom ((f ^ Int.toNat i) • b) := by
        rw [_root_.map_smul]
  have hy_mem :
      (f ^ Int.toNat i) • b ∈ BerthelotOgusInt.degreeSubmodule f K i := by
    exact ⟨hy_range, hy_d⟩
  let y : BerthelotOgusInt.degreeSubmodule f K i := ⟨(f ^ Int.toNat i) • b, hy_mem⟩
  have hy_eq : f • y = x := by
    apply Subtype.ext
    -- Proof comment: multiplying the predecessor candidate by `f` recovers the original source
    -- generator because the divided representative was itself `f • b`.
    change f • ((f ^ Int.toNat i) • b) = x
    calc
      f • ((f ^ Int.toNat i) • b) = (f ^ Int.toNat i) • (f • b) := by
        simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
      _ = (f ^ Int.toNat i) • a := by
        rw [ha_eq]
      _ = x := by
        simpa [a] using smul_divide_eta_degree_repr_owner (f := f) (K := K) (i := i) hK x
  exact ⟨y, hy_eq⟩

private theorem fst_ker_inf_snd_ker_etaReductionPairMap_eq_bot
    (hf : IsRegular f)
    (hK : BerthelotOgusInt.IsTermwiseFTorsionFree f K)
    (hi : 0 ≤ i) :
    LinearMap.ker (etaReductionPairMapFst f K i) ⊓
      LinearMap.ker (etaReductionPairMapSnd f K i) = ⊥ := by
  -- Route correction: the kernel-separation argument also uses positivity of the visible `f`
  -- factor in degree `i`, so we record that hypothesis explicitly on the owner-side helper.
  apply le_antisymm
  · intro q hq
    refine Submodule.mem_bot.2 ?_
    refine Quotient.inductionOn' q ?_ hq
    intro x hq
    have hfst : etaReductionPairMapFst f K i (Submodule.Quotient.mk x) = 0 := hq.1
    have hsnd : etaReductionPairMapSnd f K i (Submodule.Quotient.mk x) = 0 := hq.2
    obtain ⟨y, hy⟩ :=
      exists_smul_eq_of_pair_map_fst_eq_zero_and_snd_eq_zero
        (f := f) (K := K) (i := i) hK hi x hfst hsnd
    -- Proof comment: once the source representative is an explicit `f`-multiple, its quotient
    -- class in `(η_f K)^i / f (η_f K)^i` is zero.
    calc
      (Submodule.Quotient.mk x : (complex f K).X i) = Submodule.Quotient.mk (f • y) := by
        rw [hy]
      _ = 0 := by
        simpa using quotient_mk_smul_eq_zero (A := A) (f := f) y
  · exact bot_le

-- Proof sketch: with the regularity and termwise `f`-torsion-free hypotheses from Remark
-- `15.96.5`, surjectivity of `Ker(d^i mod f²) → Ker(d^i mod f)` yields a section of the cocycle
-- projection `toCycles f K i`. Combining that section with the existential maps `s` and `s'` from
-- Remark `15.96.5` splits the short exact row
-- `0 → B^{i + 1} → (η_f K)^i / f(η_f K)^i → Z^i → 0`, and the differential compatibilities
-- identify the image of the reduced pair map `(1, d^i)` with a product submodule `Z.prod B` in
-- the two quotient target modules.
/-- Lemma 15.96.8 on the chapter's canonical `ModuleComplex` owner: for the source-facing
Berthelot-Ogus reduction data of Remark `15.96.5`, if `f` is regular, the complex is termwise
`f`-torsion free, and the cocycle reduction map `Ker(d^i mod f²) → Ker(d^i mod f)` is
surjective, then the canonical reduced map `(1, d^i)` identifies `(η_f K)^i / f(η_f K)^i` with
a direct sum of submodules of `f^i K^i / f^(i + 1) K^i` and
`f^(i + 1) K^(i + 1) / f^(i + 2) K^(i + 1)` in the canonical range/product sense. -/
theorem etaReductionPairMap_identifiesWithProdSubmodules_of_cyclesReductionSurjective
    (hf : IsRegular f)
    (hK : BerthelotOgusInt.IsTermwiseFTorsionFree f K)
    (hsurj : ModFSquared.cyclesReductionSurjective f K i)
    (hi : 0 ≤ i) :
    (etaReductionPairMap f K i).identifiesWithProdSubmodules := by
  -- Route correction: without `hi`, the owner-level `ℤ` statement is false in negative degrees.
  -- The source proof itself is bounded-below, so the formal product-range reduction is executed
  -- only in the nonnegative regime used by the `Nat` bridge below.
  -- The source proof decomposes `(1, d^i)` into its two coordinates and then proves the two
  -- structural facts needed for the formal product-range argument.
  refine identifiesWithProdSubmodules_of_fst_lift_and_kernel_separation
    (s := etaReductionPairMap f K i) ?_ ?_
  · -- The cycle-lifting hypothesis provides the first-coordinate lift on `ker β`.
    exact
      first_range_eq_range_on_second_ker_of_cyclesReductionSurjective
        (f := f) (K := K) (i := i) hf hK hsurj hi
  · -- Regularity and termwise torsion-freeness give the kernel-separation statement.
    exact fst_ker_inf_snd_ker_etaReductionPairMap_eq_bot
      (f := f) (K := K) (i := i) hf hK hi

namespace Nat

section

variable (f : A) (M : NatModuleCochainComplex A) (i : ℕ)

-- Route correction: the stable Nat pair-map owner now lives in
-- `BerthelotOgusEtaReductionNatPairMap`, so downstream files no longer import this unfinished
-- theorem file just to access the canonical definitions.
-- Proof sketch: apply the owner-level statement to `M.extend ComplexShape.embeddingUpNat` in degree
-- `(i : ℤ)` and transport the source, target, and pair map across the canonical bounded-below
-- degreewise identifications.
/-- Helper for Lemma 15.96.8: the degreewise `extendXIso` identifies the visible `f ^ i`-range in
the owner degree with the bounded-below `f ^ i`-range. -/
private theorem extendXIso_mem_scaled_range_iff
    (x : (M.extend ComplexShape.embeddingUpNat).X (i : ℤ)) :
    x ∈ LinearMap.range
        (LinearMap.lsmul A ((M.extend ComplexShape.embeddingUpNat).X (i : ℤ))
          (f ^ Int.toNat (i : ℤ))) ↔
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv x) ∈
        LinearMap.range (LinearMap.lsmul A (M.X i) (f ^ i)) := by
  let e := (M.extendXIso ComplexShape.embeddingUpNat
    (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv
  constructor
  · rintro ⟨y, rfl⟩
    -- Transport the visible `f ^ i` multiple through the degreewise linear equivalence.
    refine ⟨e y, ?_⟩
    simp [e, LinearMap.lsmul_apply]
  · rintro ⟨y, hy⟩
    -- Pull the range witness back along the inverse degree identification.
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    simpa [e, LinearMap.lsmul_apply] using hy

/-- Helper for Lemma 15.96.8: after applying the successor-degree `extendXIso`, the owner
differential becomes the bounded-below differential. -/
private theorem extendXIso_d_apply
    (x : (M.extend ComplexShape.embeddingUpNat).X (i : ℤ)) :
    ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv)
        (((M.extend ComplexShape.embeddingUpNat).d (i : ℤ) ((i + 1 : ℕ) : ℤ)).hom x) =
      (M.d i (i + 1)).hom
        (((M.extendXIso ComplexShape.embeddingUpNat
            (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv) x) := by
  let e0 := (M.extendXIso ComplexShape.embeddingUpNat
    (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv
  let e1 := (M.extendXIso ComplexShape.embeddingUpNat
    (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv
  -- Rewrite the extended differential once, then cancel the successor-degree identification.
  have hd :=
    congrArg ModuleCat.Hom.hom
      (HomologicalComplex.extend_d_eq
        (K := M) (e := ComplexShape.embeddingUpNat)
        (i' := (i : ℤ)) (j' := ((i + 1 : ℕ) : ℤ))
        (i := i) (j := i + 1) (by simp : ((i : ℕ) : ℤ) = (i : ℤ))
        (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1))
  have hd' := LinearMap.congr_fun hd x
  rw [hd']
  change e1 (e1.symm ((M.d i (i + 1)).hom (e0 x))) =
      (M.d i (i + 1)).hom (e0 x)
  simp

/-- Helper for Lemma 15.96.8: the differential divisibility condition in the owner degree term
transports to the bounded-below condition. -/
private theorem extendXIso_d_mem_scaled_range_iff
    (x : (M.extend ComplexShape.embeddingUpNat).X (i : ℤ)) :
    (((M.extend ComplexShape.embeddingUpNat).d (i : ℤ) ((i + 1 : ℕ) : ℤ)).hom x) ∈
        LinearMap.range
          (LinearMap.lsmul A
            ((M.extend ComplexShape.embeddingUpNat).X ((i + 1 : ℕ) : ℤ))
            (f ^ Int.toNat (((i + 1 : ℕ) : ℤ)))) ↔
      (M.d i (i + 1)).hom
          (((M.extendXIso ComplexShape.embeddingUpNat
              (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv) x) ∈
        LinearMap.range (LinearMap.lsmul A (M.X (i + 1)) (f ^ (i + 1))) := by
  let y :=
    ((M.extend ComplexShape.embeddingUpNat).d (i : ℤ) ((i + 1 : ℕ) : ℤ)).hom x
  constructor
  · intro hx
    -- First move the scaled-range witness to `M.X (i + 1)`, then rewrite the differential.
    have hx' :=
      (extendXIso_mem_scaled_range_iff (f := f) (M := M) (i := i + 1) (x := y)).1 hx
    have hx'' :
        ∃ z, f ^ (i + 1) • z =
          ((M.extendXIso ComplexShape.embeddingUpNat
                (by simp : (((i + 1 : ℕ) : ℕ) : ℤ) = ((i + 1 : ℕ) : ℤ))).toLinearEquiv)
            (((M.extend ComplexShape.embeddingUpNat).d (i : ℤ) ((i + 1 : ℕ) : ℤ)).hom x) := by
      simpa [y] using hx'
    rcases hx'' with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← extendXIso_d_apply (f := f) (M := M) (i := i) (x := x)]
    exact hz
  · intro hx
    rcases hx with ⟨z, hz⟩
    have hx' :
        ((M.extendXIso ComplexShape.embeddingUpNat
              (by simp : (((i + 1 : ℕ) : ℕ) : ℤ) = ((i + 1 : ℕ) : ℤ))).toLinearEquiv y) ∈
          LinearMap.range (LinearMap.lsmul A (M.X (i + 1)) (f ^ (i + 1))) := by
      refine ⟨z, ?_⟩
      have hy_eq :
          ((M.extendXIso ComplexShape.embeddingUpNat
                (by simp : (((i + 1 : ℕ) : ℕ) : ℤ) = ((i + 1 : ℕ) : ℤ))).toLinearEquiv y) =
            (M.d i (i + 1)).hom
              (((M.extendXIso ComplexShape.embeddingUpNat
                    (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv) x) := by
        simpa [y] using extendXIso_d_apply (f := f) (M := M) (i := i) (x := x)
      rw [hy_eq]
      exact hz
    exact (extendXIso_mem_scaled_range_iff (f := f) (M := M) (i := i + 1) (x := y)).2 hx'

/-- Helper for Lemma 15.96.8: `extendXIso` carries the owner Berthelot-Ogus degree term onto the
bounded-below degree term. -/
private theorem extendXIso_maps_eta_degree_submodule :
    (BerthelotOgusInt.degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)).map
        ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv.toLinearMap) =
      etaFDegreeSubmodule f M i := by
  let e := (M.extendXIso ComplexShape.embeddingUpNat
    (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv
  -- Route correction: identify the mapped submodule pointwise under `extendXIso`.
  ext y
  constructor
  · intro hy
    rw [Submodule.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (extendXIso_mem_scaled_range_iff (f := f) (M := M) (i := i) (x := x)).1 hx.1
    · exact (extendXIso_d_mem_scaled_range_iff (f := f) (M := M) (i := i) (x := x)).1 hx.2
  · intro hy
    rw [Submodule.mem_map]
    refine ⟨e.symm y, ?_, by simp [e]⟩
    refine ⟨?_, ?_⟩
    · exact
        (extendXIso_mem_scaled_range_iff (f := f) (M := M) (i := i) (x := e.symm y)).2
          (by simpa [e] using hy.1)
    · exact
        (extendXIso_d_mem_scaled_range_iff (f := f) (M := M) (i := i) (x := e.symm y)).2
          (by simpa [e] using hy.2)

/-- Helper for Lemma 15.96.8: the owner degree term in degree `i` is linearly equivalent to the
bounded-below degree term. -/
private noncomputable abbrev owner_eta_degree_linearEquiv :
    BerthelotOgusInt.degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (i : ℤ) ≃ₗ[A]
      etaFDegreeSubmodule f M i :=
  (M.extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv.ofSubmodules _ _
    (extendXIso_maps_eta_degree_submodule (f := f) (M := M) (i := i))

/-- Helper for Lemma 15.96.8: after forgetting the target subtype, the owner degree-term bridge is
the ambient `extendXIso`. -/
private theorem owner_eta_degree_linearEquiv_subtype_comp :
    (etaFDegreeSubmodule f M i).subtype.comp
        (owner_eta_degree_linearEquiv (f := f) (M := M) (i := i)).toLinearMap =
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv.toLinearMap).comp
        (BerthelotOgusInt.degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)).subtype := by
  -- Normalize the `ofSubmodules` bridge once so later proofs only see the ambient `extendXIso`.
  ext x
  rfl

/-- Helper for Lemma 15.96.8: on elements, the owner degree-term bridge applies `extendXIso` to
the ambient representative. -/
private theorem owner_eta_degree_linearEquiv_apply
    (x : BerthelotOgusInt.degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)) :
    (((owner_eta_degree_linearEquiv (f := f) (M := M) (i := i) x : etaFDegreeSubmodule f M i) :
        M.X i)) =
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv) x := by
  -- Evaluate the normalized subtype composition at the chosen element.
  exact LinearMap.congr_fun
    (owner_eta_degree_linearEquiv_subtype_comp (f := f) (M := M) (i := i)) x

/-- Helper for Lemma 15.96.8: `extendXIso` carries the owner first target submodule `f^i M^i`
onto the bounded-below first target submodule. -/
private theorem extendXIso_maps_power_submodule :
    (BerthelotOgusEtaReduction.powerSubmodule f
        (M.extend ComplexShape.embeddingUpNat) (i : ℤ)).map
        ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv.toLinearMap) =
      BerthelotOgusEtaReduction.Nat.powerSubmodule f M i := by
  -- Rewrite both sides as visible `f ^ i` multiples of `⊤` and transport them by `extendXIso`.
  rw [BerthelotOgusEtaReduction.powerSubmodule, BerthelotOgusEtaReduction.Nat.powerSubmodule]
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  simp

/-- Helper for Lemma 15.96.8: the owner first target submodule is linearly equivalent to the
bounded-below first target submodule. -/
private noncomputable abbrev owner_powerSubmodule_linearEquiv :
    BerthelotOgusEtaReduction.powerSubmodule f (M.extend ComplexShape.embeddingUpNat) (i : ℤ) ≃ₗ[A]
      BerthelotOgusEtaReduction.Nat.powerSubmodule f M i :=
  (M.extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv.ofSubmodules _ _
    (extendXIso_maps_power_submodule (f := f) (M := M) (i := i))

/-- Helper for Lemma 15.96.8: after forgetting the target subtype, the first-target bridge is the
ambient `extendXIso`. -/
private theorem owner_powerSubmodule_linearEquiv_subtype_comp :
    (BerthelotOgusEtaReduction.Nat.powerSubmodule f M i).subtype.comp
        (owner_powerSubmodule_linearEquiv (f := f) (M := M) (i := i)).toLinearMap =
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv.toLinearMap).comp
        (BerthelotOgusEtaReduction.powerSubmodule f
          (M.extend ComplexShape.embeddingUpNat) (i : ℤ)).subtype := by
  -- Normalize the first-target bridge to the ambient degreewise `extendXIso`.
  ext x
  rfl

/-- Helper for Lemma 15.96.8: on elements, the first-target bridge applies `extendXIso` to the
ambient representative. -/
private theorem owner_powerSubmodule_linearEquiv_apply
    (x : BerthelotOgusEtaReduction.powerSubmodule f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)) :
    (((owner_powerSubmodule_linearEquiv (f := f) (M := M) (i := i) x :
        BerthelotOgusEtaReduction.Nat.powerSubmodule f M i) : M.X i)) =
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv) x := by
  -- Evaluate the normalized subtype composition at the chosen first-target element.
  exact LinearMap.congr_fun
    (owner_powerSubmodule_linearEquiv_subtype_comp (f := f) (M := M) (i := i)) x

/-- Helper for Lemma 15.96.8: `extendXIso` carries the owner second target submodule
`f^(i + 1) M^(i + 1)` onto the bounded-below second target submodule. -/
private theorem extendXIso_maps_nextPower_submodule :
    (BerthelotOgusEtaReduction.nextPowerSubmodule f
        (M.extend ComplexShape.embeddingUpNat) (i : ℤ)).map
        ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv.toLinearMap) =
      BerthelotOgusEtaReduction.Nat.nextPowerSubmodule f M i := by
  -- Rewrite both sides as visible `f ^ (i + 1)` multiples of `⊤` and transport them by the
  -- successor-degree `extendXIso`.
  rw [BerthelotOgusEtaReduction.nextPowerSubmodule,
    BerthelotOgusEtaReduction.Nat.nextPowerSubmodule]
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  simp

/-- Helper for Lemma 15.96.8: the owner second target submodule is linearly equivalent to the
bounded-below second target submodule. -/
private noncomputable abbrev owner_nextPowerSubmodule_linearEquiv :
    BerthelotOgusEtaReduction.nextPowerSubmodule f
        (M.extend ComplexShape.embeddingUpNat) (i : ℤ) ≃ₗ[A]
      BerthelotOgusEtaReduction.Nat.nextPowerSubmodule f M i :=
  ((M.extendXIso ComplexShape.embeddingUpNat
      (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv).ofSubmodules _ _
    (extendXIso_maps_nextPower_submodule (f := f) (M := M) (i := i))

/-- Helper for Lemma 15.96.8: after forgetting the target subtype, the second-target bridge is
the ambient successor-degree `extendXIso`. -/
private theorem owner_nextPowerSubmodule_linearEquiv_subtype_comp :
    (BerthelotOgusEtaReduction.Nat.nextPowerSubmodule f M i).subtype.comp
        (owner_nextPowerSubmodule_linearEquiv (f := f) (M := M) (i := i)).toLinearMap =
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv.toLinearMap).comp
        (BerthelotOgusEtaReduction.nextPowerSubmodule f
          (M.extend ComplexShape.embeddingUpNat) (i : ℤ)).subtype := by
  -- Normalize the second-target bridge to the ambient successor-degree `extendXIso`.
  ext x
  rfl

/-- Helper for Lemma 15.96.8: on elements, the second-target bridge applies the successor-degree
`extendXIso` to the ambient representative. -/
private theorem owner_nextPowerSubmodule_linearEquiv_apply
    (x : BerthelotOgusEtaReduction.nextPowerSubmodule f
        (M.extend ComplexShape.embeddingUpNat) (i : ℤ)) :
    (((owner_nextPowerSubmodule_linearEquiv (f := f) (M := M) (i := i) x :
        BerthelotOgusEtaReduction.Nat.nextPowerSubmodule f M i) : M.X (i + 1))) =
      ((M.extendXIso ComplexShape.embeddingUpNat
          (by simp : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1)).toLinearEquiv) x := by
  -- Evaluate the normalized subtype composition at the chosen second-target element.
  exact LinearMap.congr_fun
    (owner_nextPowerSubmodule_linearEquiv_subtype_comp (f := f) (M := M) (i := i)) x

/-- Helper for Lemma 15.96.8: the owner restricted differential is carried by the target bridges to
the bounded-below restricted differential. -/
private theorem owner_degreeDifferentialToNextPowerSubmodule_apply
    (x : BerthelotOgusInt.degreeSubmodule f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)) :
    owner_nextPowerSubmodule_linearEquiv (f := f) (M := M) (i := i)
        (BerthelotOgusEtaReduction.degreeDifferentialToNextPowerSubmodule f
          (M.extend ComplexShape.embeddingUpNat) (i : ℤ) x) =
      BerthelotOgusEtaReduction.Nat.degreeDifferentialToNextPowerSubmodule f M i
        (owner_eta_degree_linearEquiv (f := f) (M := M) (i := i) x) := by
  -- Compare the two restricted differentials after forgetting to the ambient successor module.
  apply Subtype.ext
  have hd_nat : (η[f] M).d i (i + 1) = ModuleCat.ofHom (etaFDifferentialLinear f M i) := by
    simpa [etaFComplex] using
      (CochainComplex.of_d
        (fun n ↦ ModuleCat.of A (etaFDegreeSubmodule f M n))
        (fun n ↦ ModuleCat.ofHom (etaFDifferentialLinear f M n))
        (fun n ↦ etaFDifferential_sq f M n)
        i)
  rw [owner_nextPowerSubmodule_linearEquiv_apply, owner_eta_degree_linearEquiv_apply, hd_nat]
  simpa [BerthelotOgusEtaReduction.degreeDifferentialToNextPowerSubmodule,
    BerthelotOgusEtaReduction.Nat.degreeDifferentialToNextPowerSubmodule,
    BerthelotOgusInt.differentialLinear, etaFDifferentialLinear] using
    extendXIso_d_apply (f := f) (M := M) (i := i) (x := x)

/-- Helper for Lemma 15.96.8: reducing a linear equivalence modulo `f` and then its inverse is
the identity on the target quotient. -/
private theorem reduceModIdeal_linearEquiv_left_inv
    {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) :
    (LinearMap.reduceModIdeal (principalIdeal f) e.toLinearMap).comp
        (LinearMap.reduceModIdeal (principalIdeal f) e.symm.toLinearMap) =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro x
  -- Check the composition on quotient generators and reduce to `e (e.symm x) = x`.
  have hg :
      (LinearMap.reduceModIdeal (principalIdeal f) e.symm.toLinearMap)
          (Submodule.Quotient.mk x) =
        (Submodule.Quotient.mk (e.symm x) :
          V ⧸ principalIdeal f • (⊤ : Submodule A V)) := by
    simpa using
      (LinearMap.reduceModIdeal_apply
        (I := principalIdeal f) (f := e.symm.toLinearMap) x)
  rw [LinearMap.comp_apply, hg]
  have hf :
      (LinearMap.reduceModIdeal (principalIdeal f) e.toLinearMap)
          (Submodule.Quotient.mk (e.symm x)) =
        (Submodule.Quotient.mk (e (e.symm x)) :
          W ⧸ principalIdeal f • (⊤ : Submodule A W)) := by
    simpa using
      (LinearMap.reduceModIdeal_apply
        (I := principalIdeal f) (f := e.toLinearMap) (e.symm x))
  rw [hf]
  simp

/-- Helper for Lemma 15.96.8: reducing a linear equivalence inverse modulo `f` and then the
equivalence itself is the identity on the source quotient. -/
private theorem reduceModIdeal_linearEquiv_right_inv
    {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) :
    (LinearMap.reduceModIdeal (principalIdeal f) e.symm.toLinearMap).comp
        (LinearMap.reduceModIdeal (principalIdeal f) e.toLinearMap) =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro x
  -- Check the composition on quotient generators and reduce to `e.symm (e x) = x`.
  have hf :
      (LinearMap.reduceModIdeal (principalIdeal f) e.toLinearMap)
          (Submodule.Quotient.mk x) =
        (Submodule.Quotient.mk (e x) :
          W ⧸ principalIdeal f • (⊤ : Submodule A W)) := by
    simpa using
      (LinearMap.reduceModIdeal_apply
        (I := principalIdeal f) (f := e.toLinearMap) x)
  rw [LinearMap.comp_apply, hf]
  have hg :
      (LinearMap.reduceModIdeal (principalIdeal f) e.symm.toLinearMap)
          (Submodule.Quotient.mk (e x)) =
        (Submodule.Quotient.mk (e.symm (e x)) :
          V ⧸ principalIdeal f • (⊤ : Submodule A V)) := by
    simpa using
      (LinearMap.reduceModIdeal_apply
        (I := principalIdeal f) (f := e.symm.toLinearMap) (e x))
  rw [hg]
  simp

/-- Helper for Lemma 15.96.8: reducing an `A`-linear equivalence modulo `f` yields a linear
equivalence over `A ⧸ (f)`. -/
private noncomputable def reduceModIdeal_linearEquiv
    {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) :
    (V ⧸ principalIdeal f • (⊤ : Submodule A V)) ≃ₗ[A ⧸ principalIdeal f]
      (W ⧸ principalIdeal f • (⊤ : Submodule A W)) :=
  LinearEquiv.ofLinear
    (LinearMap.reduceModIdeal (principalIdeal f) e.toLinearMap)
    (LinearMap.reduceModIdeal (principalIdeal f) e.symm.toLinearMap)
    (reduceModIdeal_linearEquiv_left_inv (f := f) e)
    (reduceModIdeal_linearEquiv_right_inv (f := f) e)

/-- Helper for Lemma 15.96.8: the reduced quotient equivalence induced by a linear equivalence
sends quotient generators to quotient generators. -/
private theorem reduceModIdeal_linearEquiv_apply_mk
    {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) (x : V) :
    reduceModIdeal_linearEquiv (f := f) e (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (e x) :
        W ⧸ principalIdeal f • (⊤ : Submodule A W)) := by
  -- Unfold the forward map once and use the standard reduction-on-generators formula.
  simpa [reduceModIdeal_linearEquiv] using
    (LinearMap.reduceModIdeal_apply (I := principalIdeal f) (f := e.toLinearMap) x)

/-- Helper for Lemma 15.96.8: on quotient generators, the Nat first coordinate is the class of
the ambient inclusion into `f^i M^i`. -/
private theorem etaReductionPairMapFst_apply_mk
    (x : etaFDegreeSubmodule f M i) :
    (((LinearMap.fst (A ⧸ principalIdeal f)
          (BerthelotOgusEtaReduction.Nat.powerSubmodule f M i ⧸
            principalIdeal f • (⊤ : Submodule A (BerthelotOgusEtaReduction.Nat.powerSubmodule f M i)))
          (BerthelotOgusEtaReduction.Nat.nextPowerSubmodule f M i ⧸
            principalIdeal f • (⊤ : Submodule A (BerthelotOgusEtaReduction.Nat.nextPowerSubmodule f M i)))).comp
        (BerthelotOgusEtaReduction.Nat.etaReductionPairMap f M i))
        (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk
        ((Submodule.inclusion
          (BerthelotOgusEtaReduction.Nat.degreeSubmodule_le_powerSubmodule f M i)) x) :
          BerthelotOgusEtaReduction.Nat.powerSubmodule f M i ⧸
            principalIdeal f • (⊤ : Submodule A (BerthelotOgusEtaReduction.Nat.powerSubmodule f M i))) := by
  -- The first coordinate is the quotient map induced by the degreewise inclusion.
  simp [BerthelotOgusEtaReduction.Nat.etaReductionPairMap, LinearMap.reduceModIdeal_apply]

/-- Helper for Lemma 15.96.8: on quotient generators, the Nat second coordinate is the class of
the bounded-below restricted differential. -/
private theorem etaReductionPairMapSnd_apply_mk
    (x : etaFDegreeSubmodule f M i) :
    (((LinearMap.snd (A ⧸ principalIdeal f)
          (BerthelotOgusEtaReduction.Nat.powerSubmodule f M i ⧸
            principalIdeal f • (⊤ : Submodule A (BerthelotOgusEtaReduction.Nat.powerSubmodule f M i)))
          (BerthelotOgusEtaReduction.Nat.nextPowerSubmodule f M i ⧸
            principalIdeal f • (⊤ : Submodule A (BerthelotOgusEtaReduction.Nat.nextPowerSubmodule f M i)))).comp
        (BerthelotOgusEtaReduction.Nat.etaReductionPairMap f M i))
        (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk
        (BerthelotOgusEtaReduction.Nat.degreeDifferentialToNextPowerSubmodule f M i x) :
          BerthelotOgusEtaReduction.Nat.nextPowerSubmodule f M i ⧸
            principalIdeal f • (⊤ : Submodule A (BerthelotOgusEtaReduction.Nat.nextPowerSubmodule f M i))) := by
  -- The second coordinate is the quotient map induced by the restricted differential.
  simp [BerthelotOgusEtaReduction.Nat.etaReductionPairMap, LinearMap.reduceModIdeal_apply]

/-- Helper for Lemma 15.96.8: the owner reduced pair map is conjugate to the bounded-below pair
map by the degreewise quotient transports. -/
private theorem owner_pair_map_congr :
    let eSrc :=
      reduceModIdeal_linearEquiv (f := f)
        (owner_eta_degree_linearEquiv (f := f) (M := M) (i := i))
    let ePow :=
      reduceModIdeal_linearEquiv (f := f)
        (owner_powerSubmodule_linearEquiv (f := f) (M := M) (i := i))
    let eNext :=
      reduceModIdeal_linearEquiv (f := f)
        (owner_nextPowerSubmodule_linearEquiv (f := f) (M := M) (i := i))
    (LinearEquiv.prodCongr ePow eNext).toLinearMap.comp
        (BerthelotOgusEtaReduction.etaReductionPairMap f
          (M.extend ComplexShape.embeddingUpNat) (i : ℤ)) =
      (BerthelotOgusEtaReduction.Nat.etaReductionPairMap f M i).comp eSrc.toLinearMap := by
  dsimp
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro x
  -- Compare both reduced pair maps on quotient generators and then split into the two
  -- coordinates.
  apply Prod.ext
  · -- The first coordinate is just the transported quotient class of the ambient inclusion.
    change
      reduceModIdeal_linearEquiv (f := f)
          (owner_powerSubmodule_linearEquiv (f := f) (M := M) (i := i))
          (BerthelotOgusEtaReduction.etaReductionPairMapFst f
            (M.extend ComplexShape.embeddingUpNat) (i : ℤ) (Submodule.Quotient.mk x)) =
        BerthelotOgusEtaReduction.Nat.etaReductionPairMapFst f M i
          (reduceModIdeal_linearEquiv (f := f)
            (owner_eta_degree_linearEquiv (f := f) (M := M) (i := i))
            (Submodule.Quotient.mk x))
    rw [BerthelotOgusEtaReduction.etaReductionPairMapFst_apply_mk,
      BerthelotOgusEtaReduction.Nat.etaReductionPairMapFst_apply_mk,
      reduceModIdeal_linearEquiv_apply_mk,
      reduceModIdeal_linearEquiv_apply_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    -- Both transported inclusions have the same ambient value under `extendXIso`.
    calc
      (((owner_powerSubmodule_linearEquiv (f := f) (M := M) (i := i)
            ((Submodule.inclusion
              (BerthelotOgusEtaReduction.degreeSubmodule_le_powerSubmodule f
                (M.extend ComplexShape.embeddingUpNat) (i : ℤ))) x) :
            BerthelotOgusEtaReduction.Nat.powerSubmodule f M i) : M.X i)) =
        ((M.extendXIso ComplexShape.embeddingUpNat
            (by simp : ((i : ℕ) : ℤ) = (i : ℤ))).toLinearEquiv) x := by
          simpa using
            owner_powerSubmodule_linearEquiv_apply (f := f) (M := M) (i := i)
              ((Submodule.inclusion
                (BerthelotOgusEtaReduction.degreeSubmodule_le_powerSubmodule f
                  (M.extend ComplexShape.embeddingUpNat) (i : ℤ))) x)
      _ = (((owner_eta_degree_linearEquiv (f := f) (M := M) (i := i) x :
            etaFDegreeSubmodule f M i) : M.X i)) := by
          symm
          exact owner_eta_degree_linearEquiv_apply (f := f) (M := M) (i := i) x
  · -- The second coordinate is the transported restricted differential.
    change
      reduceModIdeal_linearEquiv (f := f)
          (owner_nextPowerSubmodule_linearEquiv (f := f) (M := M) (i := i))
          (BerthelotOgusEtaReduction.etaReductionPairMapSnd f
            (M.extend ComplexShape.embeddingUpNat) (i : ℤ) (Submodule.Quotient.mk x)) =
        BerthelotOgusEtaReduction.Nat.etaReductionPairMapSnd f M i
          (reduceModIdeal_linearEquiv (f := f)
            (owner_eta_degree_linearEquiv (f := f) (M := M) (i := i))
            (Submodule.Quotient.mk x))
    rw [BerthelotOgusEtaReduction.etaReductionPairMapSnd_apply_mk,
      BerthelotOgusEtaReduction.Nat.etaReductionPairMapSnd_apply_mk,
      reduceModIdeal_linearEquiv_apply_mk,
      reduceModIdeal_linearEquiv_apply_mk]
    -- The dedicated differential-transport lemma is exactly the needed representative identity.
    exact congrArg Submodule.Quotient.mk
      (owner_degreeDifferentialToNextPowerSubmodule_apply (f := f) (M := M) (i := i) x)

/-- Helper for Lemma 15.96.8: `identifiesWithProdSubmodules` is preserved when one conjugates a
pair map by source and target linear equivalences. -/
private theorem identifiesWithProdSubmodules_prodCongr
    {S T U₁ U₂ V₁ V₂ : Type*}
    [AddCommGroup S] [Module (A ⧸ principalIdeal f) S]
    [AddCommGroup T] [Module (A ⧸ principalIdeal f) T]
    [AddCommGroup U₁] [Module (A ⧸ principalIdeal f) U₁]
    [AddCommGroup U₂] [Module (A ⧸ principalIdeal f) U₂]
    [AddCommGroup V₁] [Module (A ⧸ principalIdeal f) V₁]
    [AddCommGroup V₂] [Module (A ⧸ principalIdeal f) V₂]
    (s : S →ₗ[A ⧸ principalIdeal f] U₁ × U₂)
    (t : T →ₗ[A ⧸ principalIdeal f] V₁ × V₂)
    (eS : S ≃ₗ[A ⧸ principalIdeal f] T)
    (e₁ : U₁ ≃ₗ[A ⧸ principalIdeal f] V₁)
    (e₂ : U₂ ≃ₗ[A ⧸ principalIdeal f] V₂)
    (hconj :
      (LinearEquiv.prodCongr e₁ e₂).toLinearMap.comp s =
        t.comp eS.toLinearMap) :
    s.identifiesWithProdSubmodules → t.identifiesWithProdSubmodules := by
  rintro ⟨P₁, P₂, hs_injective, hs_range⟩
  refine ⟨P₁.map e₁.toLinearMap, P₂.map e₂.toLinearMap, ?_, ?_⟩
  · intro x y hxy
    -- Pull equality back to the source along `eS.symm`, then cancel the target equivalence.
    have hsxy :
        s (eS.symm x) = s (eS.symm y) := by
      apply (LinearEquiv.prodCongr e₁ e₂).injective
      calc
        (LinearEquiv.prodCongr e₁ e₂) (s (eS.symm x)) = t x := by
          simpa [LinearMap.comp_apply] using
            (LinearMap.congr_fun hconj (eS.symm x))
        _ = t y := hxy
        _ = (LinearEquiv.prodCongr e₁ e₂) (s (eS.symm y)) := by
          simpa [LinearMap.comp_apply] using
            (LinearMap.congr_fun hconj (eS.symm y)).symm
    exact eS.symm.injective (hs_injective hsxy)
  · ext z
    constructor
    · rintro ⟨x, rfl⟩
      have hs_mem : s (eS.symm x) ∈ P₁.prod P₂ := by
        rw [← hs_range]
        exact LinearMap.mem_range.mpr ⟨eS.symm x, rfl⟩
      constructor
      · refine Submodule.mem_map.2 ⟨(s (eS.symm x)).1, hs_mem.1, ?_⟩
        -- The conjugation identity identifies the first coordinate after applying `e₁`.
        simpa [LinearMap.comp_apply] using congrArg Prod.fst
          (LinearMap.congr_fun hconj (eS.symm x))
      · refine Submodule.mem_map.2 ⟨(s (eS.symm x)).2, hs_mem.2, ?_⟩
        -- The same generator computation handles the second coordinate.
        simpa [LinearMap.comp_apply] using congrArg Prod.snd
          (LinearMap.congr_fun hconj (eS.symm x))
    · intro hz
      rcases hz with ⟨hz₁, hz₂⟩
      rcases Submodule.mem_map.1 hz₁ with ⟨u, hu, hu_eq⟩
      rcases Submodule.mem_map.1 hz₂ with ⟨v, hv, hv_eq⟩
      have huv_mem : (u, v) ∈ P₁.prod P₂ := ⟨hu, hv⟩
      rw [← hs_range] at huv_mem
      rcases LinearMap.mem_range.1 huv_mem with ⟨a, ha⟩
      refine LinearMap.mem_range.2 ⟨eS a, ?_⟩
      -- Realize the mapped pair by transporting a source-range witness through `eS`.
      apply Prod.ext
      · calc
          (t (eS a)).1 = ((LinearEquiv.prodCongr e₁ e₂) (s a)).1 := by
            simpa [LinearMap.comp_apply] using
              congrArg Prod.fst (LinearMap.congr_fun hconj a).symm
          _ = (e₁ u) := by
            rw [ha]
            rfl
          _ = z.1 := hu_eq
      · calc
          (t (eS a)).2 = ((LinearEquiv.prodCongr e₁ e₂) (s a)).2 := by
            simpa [LinearMap.comp_apply] using
              congrArg Prod.snd (LinearMap.congr_fun hconj a).symm
          _ = (e₂ v) := by
            rw [ha]
            rfl
          _ = z.2 := hv_eq

/-- The bounded-below bridge/view of Lemma `15.96.8`. -/
theorem etaReductionPairMap_identifiesWithProdSubmodules_of_cyclesReductionSurjective
    (hf : IsRegular f)
    (hM : IsTermwiseFTorsionFree f M)
    (hsurj : ModFSquared.Nat.cyclesReductionSurjective f M i) :
    (etaReductionPairMap f M i).identifiesWithProdSubmodules := by
  let eSrc :=
    reduceModIdeal_linearEquiv (f := f)
      (owner_eta_degree_linearEquiv (f := f) (M := M) (i := i))
  let ePow :=
    reduceModIdeal_linearEquiv (f := f)
      (owner_powerSubmodule_linearEquiv (f := f) (M := M) (i := i))
  let eNext :=
    reduceModIdeal_linearEquiv (f := f)
      (owner_nextPowerSubmodule_linearEquiv (f := f) (M := M) (i := i))
  have howner :
      (BerthelotOgusEtaReduction.etaReductionPairMap f
        (M.extend ComplexShape.embeddingUpNat) (i : ℤ)).identifiesWithProdSubmodules := by
    -- Apply the owner theorem in nonnegative degree `(i : ℤ)`.
    exact
      BerthelotOgusEtaReduction.etaReductionPairMap_identifiesWithProdSubmodules_of_cyclesReductionSurjective
        (f := f) (K := M.extend ComplexShape.embeddingUpNat) (i := (i : ℤ)) hf
        (IsTermwiseFTorsionFree.toIsTermwiseFTorsionFree (f := f) (M := M) hM)
        hsurj (by exact_mod_cast Nat.zero_le i)
  -- Transport the owner product decomposition across the bounded-below source and target
  -- equivalences.
  exact
    (identifiesWithProdSubmodules_prodCongr (f := f)
      (s := BerthelotOgusEtaReduction.etaReductionPairMap f
        (M.extend ComplexShape.embeddingUpNat) (i : ℤ))
      (t := BerthelotOgusEtaReduction.Nat.etaReductionPairMap f M i)
      (eS := eSrc) (e₁ := ePow) (e₂ := eNext)
      (by simpa [eSrc, ePow, eNext] using owner_pair_map_congr (f := f) (M := M) (i := i)))
      howner

end

end Nat
end BerthelotOgusEtaReduction

end
