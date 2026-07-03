import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Regular.IsSMulRegular

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_96_7 (from Chap15) -/
open CategoryTheory
open CochainComplex
open HomologicalComplex

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: short exact sequences and connecting morphisms for cochain complexes of
  `A`-modules;
  `NatModuleCochainComplex`, `CochainComplex.reduceModIdealA`,
  together with the owner boundary `ShortComplex.ShortExact.δ` and the mathlib owner
  `Submodule.torsionBy`;
- best owner abstraction:
  `source-facing`: the bounded-below Berthelot-Ogus Bockstein operator and the surjectivity
    criterion on cycles;
  `core/canonical`: the `ModuleComplex A` short exact sequence
    `K/fK --f→ K/f²K → K/fK`, its connecting morphism, and the induced cycles map;
  `bridge/view`: the nonnegative `NatModuleCochainComplex A` surface used by the source-facing
    statements below;
- primitive data vs derived API: the primitive owner data are the quotient complexes, the
  short exact sequence, and the standard `a`-torsion owner `Submodule.torsionBy`. The Bockstein
  map and the cycle-surjectivity predicate are derived from those owners, so the bounded-below
  bridge should not expose a second public copy of the reduction-sequence data. -/

-- Proof sketch: if `x = f ^ 2 • y`, then also `x = f • (f • y)`, so every element of `f²M`
-- already lies in `fM`.
/-- The quotient submodule `(f²)M` is contained in `fM`. -/
private theorem principalIdeal_sq_smul_top_le
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) :
    principalIdeal (f ^ 2) • (⊤ : Submodule A M) ≤
      Submodule.comap (LinearMap.id : M →ₗ[A] M) (principalIdeal f • (⊤ : Submodule A M)) :=
  sorry

-- Proof sketch: if `x = f • y`, then multiplying by `f` gives `f • x = f² • y`, so the
-- multiplication-by-`f` map carries `fM` into `f²M`.
/-- Multiplication by `f` sends `fM` into `f²M`. -/
private theorem principalIdeal_smul_top_le_sq_preimage
    {M : Type*} [AddCommGroup M] [Module A M] (f : A) :
    principalIdeal f • (⊤ : Submodule A M) ≤
      Submodule.comap (f • (LinearMap.id : M →ₗ[A] M))
        (principalIdeal (f ^ 2) • (⊤ : Submodule A M)) := sorry

namespace ModFSquared

open BerthelotOgusInt

/- The canonical owner for the `f²`-to-`f` reduction sequence lives on the chapter's
`ModuleComplex A` owner. The bounded-below `Nat` API below is the bridge/view used by the
source-facing lemmas in this file, while downstream `ℤ`-indexed files should reuse the owner
declarations in this namespace directly. -/

/-- The reduction `K^\bullet / fK^\bullet` on the `ModuleComplex A` owner. -/
private abbrev modFComplex (f : A) (K : ModuleComplex A) :=
  reduceModIdealA (principalIdeal f) K

/-- The reduction `K^\bullet / f²K^\bullet` on the `ModuleComplex A` owner. -/
private abbrev modFSquaredComplex (f : A) (K : ModuleComplex A) :=
  reduceModIdealA (principalIdeal (f ^ 2)) K

/-- The termwise reduction map `K/f²K → K/fK`. -/
private abbrev reductionComponent (f : A) (K : ModuleComplex A) (i : ℤ) :
    (modFSquaredComplex f K).X i ⟶ (modFComplex f K).X i :=
  let _ : Module A ↑((reduceModIdeal (principalIdeal (f ^ 2)) K).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal (f ^ 2)))
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) K).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  ModuleCat.ofHom <|
    Submodule.mapQ
      (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
      (principalIdeal f • (⊤ : Submodule A (K.X i)))
      (LinearMap.id : K.X i →ₗ[A] K.X i)
      (principalIdeal_sq_smul_top_le f)

/-- The termwise multiplication map `K/fK → K/f²K` induced by `x ↦ f x`. -/
private abbrev multiplicationComponent (f : A) (K : ModuleComplex A) (i : ℤ) :
    (modFComplex f K).X i ⟶ (modFSquaredComplex f K).X i :=
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) K).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  let _ : Module A ↑((reduceModIdeal (principalIdeal (f ^ 2)) K).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal (f ^ 2)))
  ModuleCat.ofHom <|
    Submodule.mapQ
      (principalIdeal f • (⊤ : Submodule A (K.X i)))
      (principalIdeal (f ^ 2) • (⊤ : Submodule A (K.X i)))
      (f • (LinearMap.id : K.X i →ₗ[A] K.X i))
      (principalIdeal_smul_top_le_sq_preimage f)

/-- The reduction maps `K/f²K → K/fK` commute with the reduced differentials. -/
private theorem reductionComponent_comm
    (f : A) (K : ModuleComplex A) (i j : ℤ) :
    CommSq
      (reductionComponent f K i)
      ((modFSquaredComplex f K).d i j)
      ((modFComplex f K).d i j)
      (reductionComponent f K j) := sorry

/-- The multiplication maps `K/fK → K/f²K` commute with the reduced differentials. -/
private theorem multiplicationComponent_comm
    (f : A) (K : ModuleComplex A) (i j : ℤ) :
    CommSq
      (multiplicationComponent f K i)
      ((modFComplex f K).d i j)
      ((modFSquaredComplex f K).d i j)
      (multiplicationComponent f K j) := sorry

/-- The cochain map `K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet`. -/
private def reductionMap (f : A) (K : ModuleComplex A) :
    modFSquaredComplex f K ⟶ modFComplex f K where
  f i := reductionComponent f K i
  comm' i j _ := (reductionComponent_comm f K i j).w

/-- The cochain map `K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet` induced by multiplication by
`f`. -/
private def multiplicationMap (f : A) (K : ModuleComplex A) :
    modFComplex f K ⟶ modFSquaredComplex f K where
  f i := multiplicationComponent f K i
  comm' i j _ := (multiplicationComponent_comm f K i j).w

/-- The composite `K/fK → K/f²K → K/fK` is zero. -/
private theorem multiplicationMap_comp_reductionMap
    (f : A) (K : ModuleComplex A) :
    multiplicationMap f K ≫ reductionMap f K = 0 := sorry

/-- The short complex
`0 → K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet`. -/
private abbrev shortComplex (f : A) (K : ModuleComplex A) :
    ShortComplex (ModuleComplex A) :=
  ShortComplex.mk (multiplicationMap f K) (reductionMap f K)
    (multiplicationMap_comp_reductionMap f K)

/-- The reduction sequence
`0 → K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet → 0`
is short exact when `K^\bullet` is termwise `f`-torsion free. -/
private theorem shortExact (f : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree f K) :
    (shortComplex f K).ShortExact := sorry

/-- The Berthelot-Ogus Bockstein morphism on the canonical `ModuleComplex A` owner, obtained as
the connecting morphism of
`0 → K^\bullet/fK^\bullet → K^\bullet/f²K^\bullet → K^\bullet/fK^\bullet → 0`. -/
noncomputable abbrev bockstein
    (f : A) (K : ModuleComplex A) (i : ℤ)
    (hK : IsTermwiseFTorsionFree f K) :
    (reduceModIdealA (principalIdeal f) K).homology i ⟶
      (reduceModIdealA (principalIdeal f) K).homology (i + 1) :=
  (shortExact f K hK).δ i (i + 1) (ComplexShape.up_mk i (i + 1) rfl)

/-- The condition that `Ker(d^i mod f²) → Ker(d^i mod f)` is surjective, expressed as the
epimorphy of the induced map on cycles on the canonical `ModuleComplex` owner. -/
abbrev cyclesReductionSurjective (f : A) (K : ModuleComplex A) (i : ℤ) : Prop :=
  Epi (cyclesMap (reductionMap f K) i)

-- Proof sketch: identify the owner-level Berthelot-Ogus `β` with the connecting morphism of the
-- canonical short exact sequence above and apply exactness of the long exact homology sequence.
/-- Owner-level form of Lemma `15.96.7`: surjectivity of
`Ker(d^i mod f²) → Ker(d^i mod f)` is equivalent to vanishing of the canonical Bockstein
morphism. -/
theorem cyclesReductionSurjective_iff_bockstein_eq_zero
    (f : A) (K : ModuleComplex A) (hK : IsTermwiseFTorsionFree f K)
    (i : ℤ) :
    cyclesReductionSurjective f K i ↔ bockstein f K i hK = 0 := sorry

-- Proof sketch: the factorization from `15.96.5.1` shows that the owner-level Bockstein factors
-- through the `f`-torsion in homology.
/-- If `H^{i+1}(K^\bullet)[f] = 0`, then the owner-level cycles map
`Ker(d^i mod f²) → Ker(d^i mod f)` is surjective. -/
theorem cyclesReductionSurjective_of_homology_f_torsion_eq_bot
    (f : A) (K : ModuleComplex A) (hK : IsTermwiseFTorsionFree f K)
    (i : ℤ) (hH : Submodule.torsionBy A (K.homology (i + 1)) f = ⊥) :
    cyclesReductionSurjective f K i := sorry

namespace Nat

/-- The bounded-below bridge/view of the Berthelot-Ogus Bockstein morphism
`H^i(M^\bullet/fM^\bullet) → H^{i+1}(M^\bullet/fM^\bullet)` coming from the short exact
sequence on the owner complex `M.extend ComplexShape.embeddingUpNat`, transported back to the
bounded-below model along the canonical reduction homology identifications from
`Remark_15_96_5`. In the textbook Berthelot-Ogus setting, this is the map
`β : H^i(M^\bullet ⊗_A f^iA/f^{i+1}A) → H^{i+1}(M^\bullet ⊗_A f^{i+1}A/f^{i+2}A)`. -/
noncomputable abbrev bockstein
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ)
    (hM : IsTermwiseFTorsionFree f M) :
    (reduceModIdealA (principalIdeal f) M).homology i ⟶
      (reduceModIdealA (principalIdeal f) M).homology (i + 1) :=
  (reduceModIdealAHomologyIso (principalIdeal f) M i).inv ≫
    ModFSquared.bockstein f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)
      hM.toIsTermwiseFTorsionFree ≫
      (reduceModIdealAHomologyIso (principalIdeal f) M (i + 1)).hom

/-- The bounded-below bridge/view of the condition that
`Ker(d^i mod f²) → Ker(d^i mod f)` is surjective, expressed as the epimorphy of the induced map
on cycles. This is the bounded-below bridge/view of the owner predicate
`ModFSquared.cyclesReductionSurjective` on `M.extend ComplexShape.embeddingUpNat`. -/
abbrev cyclesReductionSurjective
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) : Prop :=
  ModFSquared.cyclesReductionSurjective f (M.extend ComplexShape.embeddingUpNat) (i : ℤ)

-- Proof sketch: identify the textbook `β` with the connecting morphism of
-- `0 → M^\bullet/fM^\bullet → M^\bullet/f²M^\bullet → M^\bullet/fM^\bullet → 0`; exactness of
-- the long exact homology sequence then says that surjectivity on cycles is equivalent to the
-- vanishing of this connecting morphism.
/-- Lemma 15.96.7, bounded-below bridge/view: for a cochain complex of `f`-torsion-free
`A`-modules, surjectivity of `Ker(d^i mod f²) → Ker(d^i mod f)` is equivalent to the vanishing of
the Berthelot-Ogus Bockstein morphism
`β : H^i(M^\bullet ⊗_A f^iA/f^{i+1}A) → H^{i+1}(M^\bullet ⊗_A f^{i+1}A/f^{i+2}A)`. -/
theorem cyclesReductionSurjective_iff_bockstein_eq_zero
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M)
    (i : ℕ) :
    cyclesReductionSurjective f M i ↔ bockstein f M i hM = 0 := sorry

-- Proof sketch: by the factorization from `15.96.5.1`, the Bockstein map factors through the
-- `f`-torsion in `H^{i+1}(M^\bullet)`. If that torsion submodule is zero, then the Bockstein map
-- vanishes; the equivalence above then gives surjectivity on cycles.
/-- If `H^{i+1}(M^\bullet)[f] = 0`, then `Ker(d^i mod f²) → Ker(d^i mod f)` is surjective. -/
theorem cyclesReductionSurjective_of_homology_f_torsion_eq_bot
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M)
    (i : ℕ) (hH : Submodule.torsionBy A (M.homology (i + 1)) f = ⊥) :
    cyclesReductionSurjective f M i := sorry

end Nat

end ModFSquared

end

/-! ### Lemma_15_96_8 (from Chap15) -/
noncomputable section

open CategoryTheory
open HomologicalComplex

universe u

section

variable {A : Type u} [CommRing A]

namespace BerthelotOgusEtaReduction

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
  sorry

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
    (hsurj : ModFSquared.cyclesReductionSurjective f K i) :
    (etaReductionPairMap f K i).identifiesWithProdSubmodules := by
  sorry

namespace Nat

section

variable (f : A) (M : NatModuleCochainComplex A) (i : ℕ)

/-- The submodule `f^i M^i` in the bounded-below bridge/view of Lemma `15.96.8`. -/
abbrev powerSubmodule : Submodule A (M.X i) :=
  principalIdeal (f ^ i) • (⊤ : Submodule A (M.X i))

/-- The submodule `f^(i + 1) M^(i + 1)` in the target of the bounded-below bridge pair map. -/
abbrev nextPowerSubmodule : Submodule A (M.X (i + 1)) :=
  principalIdeal (f ^ (i + 1)) • (⊤ : Submodule A (M.X (i + 1)))

/-- The degree-`i` Berthelot-Ogus term is a submodule of `f^i M^i` in the bounded-below
bridge/view. -/
theorem degreeSubmodule_le_powerSubmodule :
    etaFDegreeSubmodule f M i ≤ powerSubmodule f M i :=
  by
    simpa [powerSubmodule, range_lsmul_eq_principalIdeal_smul_top] using
      (show
        etaFDegreeSubmodule f M i ≤
          LinearMap.range (LinearMap.lsmul A (M.X i) (f ^ i)) from
        inf_le_left)

/-- The differential on `η_f M` followed by the inclusion into `f^(i + 1) M^(i + 1)` in the
bounded-below bridge/view. -/
abbrev degreeDifferentialToNextPowerSubmodule :
    etaFDegreeSubmodule f M i →ₗ[A] nextPowerSubmodule f M i :=
  (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f M (i + 1))) ∘ₗ
    ((η[f] M).d i (i + 1)).hom

/-- The bounded-below unreduced pair map `(1, d^i)` from `(η_f M)^i` to
`f^i M^i × f^(i + 1) M^(i + 1)`. -/
abbrev etaPairMap :
    etaFDegreeSubmodule f M i →ₗ[A] powerSubmodule f M i × nextPowerSubmodule f M i :=
  LinearMap.prod
    (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f M i))
    (degreeDifferentialToNextPowerSubmodule f M i)

/-- The bounded-below bridge/view of the canonical reduction of `(1, d^i)` modulo `f`. -/
abbrev etaReductionPairMap :
    (CochainComplex.reduceModIdeal (principalIdeal f) (η[f] M)).X i →ₗ[A ⧸ principalIdeal f]
      ((powerSubmodule f M i ⧸
          principalIdeal f • (⊤ : Submodule A (powerSubmodule f M i))) ×
        (nextPowerSubmodule f M i ⧸
          principalIdeal f • (⊤ : Submodule A (nextPowerSubmodule f M i)))) :=
  LinearMap.prod
    (LinearMap.reduceModIdeal (principalIdeal f)
      (Submodule.inclusion (degreeSubmodule_le_powerSubmodule f M i)))
    (LinearMap.reduceModIdeal (principalIdeal f)
      (degreeDifferentialToNextPowerSubmodule f M i))

-- Proof sketch: apply the owner-level statement to `M.extend ComplexShape.embeddingUpNat` in degree
-- `(i : ℤ)` and transport the source, target, and pair map across the canonical bounded-below
-- degreewise identifications.
/-- The bounded-below bridge/view of Lemma `15.96.8`. -/
theorem etaReductionPairMap_identifiesWithProdSubmodules_of_cyclesReductionSurjective
    (hf : IsRegular f)
    (hM : IsTermwiseFTorsionFree f M)
    (hsurj : ModFSquared.Nat.cyclesReductionSurjective f M i) :
    (etaReductionPairMap f M i).identifiesWithProdSubmodules := by
  sorry

end

end Nat
end BerthelotOgusEtaReduction

end

/-! ### Lemma_15_96_9 (from Chap15) -/
noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

/-
Domain-style sampling:
- primary domain: composition of the Berthelot-Ogus operator `η_f` on cochain complexes of
  `A`-modules;
- sampled owner declarations in this domain:
  `BerthelotOgusInt.complex`,
  `BerthelotOgusInt.IsTermwiseFTorsionFree`,
  `etaFComplex`;
- best owner abstraction:
  `source-facing`: the bounded-below `ℕ`-indexed statement that iterating `η_g` and then `η_f`
    agrees with `η_(fg)`;
  `core/canonical`: the source-facing owner `etaFComplex` on `NatModuleCochainComplex A`;
  `bridge/view`: the corresponding `ℤ`-indexed extension-by-zero construction
    `BerthelotOgusInt.complex` on `ModuleComplex A` under `[K.IsStrictlyGE 0]`;
- primitive data vs derived API: the primitive inputs are the scalars `f`, `g`, the bounded-below
  complex `M`, and the termwise `(fg)`-torsion-freeness hypothesis. The `ℤ`-indexed equality is
  only a bridge statement for complexes concentrated in nonnegative degrees. -/

namespace BerthelotOgusInt

open scoped BerthelotOgusInt

-- Proof sketch: unfold the degree-`n` defining intersections for `η_f (η_g M)` and `η_{fg} M`.
-- The hypothesis that multiplication by `fg` is injective on every term already forces the
-- iterated range conditions to agree with the single range condition for `(fg)^n`, while the
-- differential condition is unchanged after rewriting powers in the commutative ring `A`. The
-- source nonzerodivisor assumptions on `f` and `g` are therefore redundant for this equality.
/-- Bounded-below `ℤ`-indexed bridge form of Lemma `15.96.9`: if multiplication by `fg` is
injective on every term of a cochain complex concentrated in nonnegative degrees, then applying the
Berthelot-Ogus operator first for `g` and then for `f` agrees with applying it once for `fg`. -/
theorem complex_comp_eq_complex_mul
    (f g : A) (K : ModuleComplex A) [K.IsStrictlyGE 0]
    (hK : IsTermwiseFTorsionFree (f * g) K) :
    η[f] (η[g] K) = η[f * g] K := by
  sorry

end BerthelotOgusInt

-- Proof sketch: transport the owner equality
-- `BerthelotOgusInt.complex f
--     (BerthelotOgusInt.complex g (M.extend ComplexShape.embeddingUpNat)) =
--   BerthelotOgusInt.complex (f * g) (M.extend ComplexShape.embeddingUpNat)` to the source-facing
-- `ℕ`-indexed complexes by restricting to nonnegative degrees and using the defining
-- degreewise transport built into `η[f] M`.
/-- Lemma 15.96.9 in the bounded-below bridge/view: if multiplication by `fg` is injective on
every term of `M^\bullet`, then applying the Berthelot-Ogus operator first for `g` and then for
`f` gives the same `ℕ`-indexed cochain complex as applying it once for `fg`. -/
theorem etaFComplex_comp_eq_etaFComplex_mul
    (f g : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree (f * g) M) :
    η[f] (η[g] M) = η[f * g] M := by
  sorry

end

/-! ### Lemma_15_96_10 (from Chap15) -/
noncomputable section

open scoped nonZeroDivisors

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]

/- Domain-style sampling:
- primary domain: flat base change for nonzerodivisors and for the owner predicate
  `BerthelotOgusInt.IsTermwiseFTorsionFree` on cochain complexes of modules;
- sampled owner declarations in this domain:
  `Module.Flat.isSMulRegular_of_nonZeroDivisors`,
  `isSMulRegular_algebraMap_iff`,
  `BerthelotOgusInt.IsTermwiseFTorsionFree`,
  `Functor.mapHomologicalComplex`,
  `ModuleCat.extendScalars`;
- best owner abstraction:
  `source-facing`: flat base change for a nonzerodivisor `f` and for termwise `f`-torsion-free
    complexes `K : ModuleComplex A`;
  `core/canonical`: the regularity owners
    `Module.Flat.isSMulRegular_of_nonZeroDivisors`,
    `isSMulRegular_algebraMap_iff`, and the chapter owner
    `BerthelotOgusInt.IsTermwiseFTorsionFree`;
  `bridge/view`: the mapped complex
    `((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K`;
- primitive data vs derived API: the primitive inputs are the algebra `A → B`, the element `f`,
  the complex `K`, and the owner-level termwise `f`-torsion-free hypothesis. The image
  nonzerodivisor statement and the mapped-complex torsion-freeness statement are derived from the
  regularity owners, so this file should keep only those source-facing consequences. -/

-- Proof sketch: use flatness of `B` over `A` to preserve the injectivity of multiplication by
-- `f` after tensoring the exact sequence `0 → A --f→ A`. The resulting map on `B` is
-- multiplication by `algebraMap A B f`, so the image element is again a nonzerodivisor.
/-- Lemma 15.96.10 (1): if `f` is a nonzerodivisor in `A`, then its image in the flat `A`-algebra
`B` is a nonzerodivisor in `B`. -/
theorem algebraMap_mem_nonZeroDivisors_of_flat
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    algebraMap A B f ∈ nonZeroDivisors B := by
  sorry

namespace BerthelotOgusInt

-- Proof sketch: in each degree `n`, tensor the injective endomorphism `f • ·` on `M.X n` with the
-- flat `A`-module `B`. The induced endomorphism on the scalar extension is multiplication by the
-- image of `f`, so each term of the base-changed complex is `g`-torsion free.
/-- Lemma 15.96.10 (2): if `K^•` is a cochain complex of `f`-torsion-free `A`-modules, then the
base-changed complex `K^• ⊗_A B` is termwise `g`-torsion free for `g = algebraMap A B f`. This is
the owner-level base-change theorem for `BerthelotOgusInt.IsTermwiseFTorsionFree`. -/
theorem IsTermwiseFTorsionFree.extendScalars
    (f : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree f K) :
    IsTermwiseFTorsionFree (algebraMap A B f)
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K) := by
  sorry

end BerthelotOgusInt

end
