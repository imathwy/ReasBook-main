import Mathlib
import stacks_proof.stacks_project.Chap09.Lemma_9_21_5
import stacks_proof.stacks_project.Chap15.Definition_15_112_7
import stacks_proof.stacks_project.Chap15.Lemma_15_115_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open IntermediateField Ideal IsLocalRing Algebra

/- Domain-style sampling:
- primary domain: tame ramification of finite separable extensions of the fraction field of a
  discrete valuation ring;
- sampled canonical declarations in this domain:
  `IsTamelyRamifiedWithRespectTo`,
  `normalClosure K L (AlgebraicClosure L)`,
  `isGalois_normalClosure_of_separable`,
  `isTamelyRamifiedWithRespectTo_of_tower`;
- best owner abstraction: the chapter owner `IsTamelyRamifiedWithRespectTo A L`, with the
  canonical Galois-closure field `normalClosure K L (AlgebraicClosure L)` as the preferred witness
  for the source-facing existence statement;
- primitive-vs-derived split: the primitive public data are the ambient DVR `A`, the fraction-field
  extension `L / FractionRing A`, and the tame owner on that extension. Galoisness,
  finite-dimensionality, and the scalar-tower compatibility of the chosen overfield witness are
  derived API and should not remain primitive existential fields.

Source/core/bridge triage:
- `source-facing`: the two Stacks Project existence statements in Lemma `15.115.8`;
- `core/canonical`: `IsTamelyRamifiedWithRespectTo` and `normalClosure`;
- `bridge/view`: the canonical normal-closure witness for clause `(1)` and the common-overfield
  existence statement for clause `(2)`.
-/

end

section

open IntermediateField Ideal IsLocalRing Algebra

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- Helper for Lemma 15.115.8: the source proof of both clauses starts by fixing a uniformizer of
the base discrete valuation ring. -/
private theorem exists_uniformizer_data :
    ∃ π : A, Irreducible π ∧ maximalIdeal A = Ideal.span ({π} : Set A) := by
  -- Choose an irreducible element and read it as a generator of the maximal ideal.
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  exact ⟨π, hπirr, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπirr⟩

section NormalClosure

variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

local notation "K" => FractionRing A
local notation "N" => normalClosure K L (AlgebraicClosure L)

-- Proof sketch: replace the existential Galois overfield by the canonical normal closure
-- `normalClosure K L (AlgebraicClosure L)`, use Lemma `9.21.5` for its Galois structure over `K`,
-- and prove separately that tame ramification is preserved by passage to this normal closure.
/-- Helper for Lemma 15.115.8: once a tame overfield of the canonical normal closure is
constructed by the source tensor-product argument, tameness descends back to the normal closure
along the final field tower. -/
private theorem normalClosure_tame_of_tame_overfield
    {M : Type w} [Field M] [Algebra A M] [Algebra K M] [Algebra N M]
    [IsScalarTower A K M] [IsScalarTower K N M]
    [FiniteDimensional K N] [Algebra.IsSeparable K N]
    [FiniteDimensional N M] [Algebra.IsSeparable N M]
    (hM : IsTamelyRamifiedWithRespectTo A M) :
    IsTamelyRamifiedWithRespectTo A N := by
  -- Route correction: isolate the final descent step now, so the remaining source-faithful work
  -- is only to construct the tame overfield `M` from the Kummer tensor branches.
  exact
    isTamelyRamifiedWithRespectTo_of_tower
      (A := A) (L := N) (M := M) hM

/-- Helper for Lemma 15.115.8: once the normal closure is known to be tame, it is already the
canonical Galois witness required by clause `(1)`. -/
private theorem exists_galois_witness_of_normalClosure_tame
    (hN : IsTamelyRamifiedWithRespectTo A N) :
    ∃ (M : Type v) (_ : Field M) (_ : Algebra A M) (_ : Algebra K M) (_ : Algebra L M)
      (_ : IsScalarTower A K M),
      IsScalarTower K L M ∧ FiniteDimensional K M ∧ IsGalois K M ∧
        IsTamelyRamifiedWithRespectTo A M := by
  -- Package the canonical normal closure with its standard Galois structure over `K`.
  refine ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  -- The only nontrivial input is the tame-ramification owner for the normal closure itself.
  exact
    ⟨inferInstance, ⟨inferInstance,
      ⟨isGalois_normalClosure_of_separable, hN⟩⟩⟩

/-- Companion bridge for Lemma 15.115.8 (1): the canonical normal closure witness inside
`AlgebraicClosure L` is itself tamely ramified with respect to `A`. -/
theorem isTamelyRamifiedWithRespectTo_normalClosure
    (hL : IsTamelyRamifiedWithRespectTo A L) :
    IsTamelyRamifiedWithRespectTo A N := by
  -- The source proof begins by fixing a uniformizer of `A` and then applying the Kummer criterion.
  obtain ⟨π, hπirr, hπ⟩ := exists_uniformizer_data (A := A)
  -- TODO: follow the source tensor-product proof after reducing `L` to an unramified lift over
  -- `A[π^(1/e)]`. The final descent step is now isolated by
  -- `normalClosure_tame_of_tame_overfield`; the remaining blocker is the source-faithful
  -- construction of a tame overfield of `N` from the Kummer tensor factors.
  let _ := π
  let _ := hπirr
  let _ := hπ
  let _ := hL
  sorry

/-- Lemma 15.115.8 (1): if `L / FractionRing A` is a finite separable extension tamely ramified
with respect to the discrete valuation ring `A`, then `L` is contained in a finite Galois
extension of `FractionRing A` that is still tamely ramified with respect to `A`. The canonical
witness is the normal closure of `L / FractionRing A` inside `AlgebraicClosure L`. -/
@[stacks 0EXX]
theorem exists_isGalois_tamelyRamifiedWithRespectTo
    (hL : IsTamelyRamifiedWithRespectTo A L) :
    ∃ (M : Type v) (_ : Field M) (_ : Algebra A M) (_ : Algebra K M) (_ : Algebra L M)
      (_ : IsScalarTower A K M),
      IsScalarTower K L M ∧ FiniteDimensional K M ∧ IsGalois K M ∧
        IsTamelyRamifiedWithRespectTo A M := by
  -- Once clause `(1)` is proved for the canonical normal closure, the existential statement is
  -- immediate by packaging that field as the witness.
  exact
    exists_galois_witness_of_normalClosure_tame
      (A := A) (L := L)
      (hN := isTamelyRamifiedWithRespectTo_normalClosure hL)

end NormalClosure

section CommonExtension

variable {L₁ : Type v} [Field L₁] [Algebra A L₁] [Algebra (FractionRing A) L₁]
variable [IsScalarTower A (FractionRing A) L₁]
variable {L₂ : Type w} [Field L₂] [Algebra A L₂] [Algebra (FractionRing A) L₂]
variable [IsScalarTower A (FractionRing A) L₂]
variable [FiniteDimensional (FractionRing A) L₁] [FiniteDimensional (FractionRing A) L₂]
variable [Algebra.IsSeparable (FractionRing A) L₁] [Algebra.IsSeparable (FractionRing A) L₂]

local notation "K" => FractionRing A

-- Proof sketch: first pass to canonical tame Galois closures of `L₁ / K` and `L₂ / K`, then embed
-- those closures into a common finite separable overfield and descend tameness to the resulting
-- intermediate compositum.
/-- Lemma 15.115.8 (2): if `L₁ / FractionRing A` and `L₂ / FractionRing A` are finite separable
extensions tamely ramified with respect to the discrete valuation ring `A`, then they are both
contained in a common finite separable extension of `FractionRing A` that is still tamely
ramified with respect to `A`. -/
@[stacks 0EXX]
theorem exists_common_tamelyRamifiedWithRespectTo_extension
    (hL₁ : IsTamelyRamifiedWithRespectTo A L₁)
    (hL₂ : IsTamelyRamifiedWithRespectTo A L₂) :
    ∃ (L : Type (max v w)) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : Algebra L₁ L) (_ : Algebra L₂ L) (_ : IsScalarTower A K L),
      IsScalarTower K L₁ L ∧ IsScalarTower K L₂ L ∧
        FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
        IsTamelyRamifiedWithRespectTo A L := by
  -- The source proof again starts by fixing a uniformizer and comparing both fields after the
  -- same radical extension `A[π^(1/e)]`.
  obtain ⟨π, hπirr, hπ⟩ := exists_uniformizer_data (A := A)
  -- TODO: follow the source proof by adjoining a common root of a uniformizer, embedding both
  -- fields into unramified extensions over the same radical extension, and then shrinking the
  -- resulting common tame witness to the public universe `max v w`.
  let _ := π
  let _ := hπirr
  let _ := hπ
  let _ := hL₁
  let _ := hL₂
  sorry

end CommonExtension

end
