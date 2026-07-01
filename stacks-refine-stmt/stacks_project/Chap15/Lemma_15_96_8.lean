import stacks_project.Chap15.Lemma_15_96_7
import stacks_project.Chap15.LinearMapIdentifiesWithProdSubmodules

-- Declarations for this item will be appended below by the statement pipeline.

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
