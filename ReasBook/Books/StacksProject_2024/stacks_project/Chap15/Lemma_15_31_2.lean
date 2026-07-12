import Mathlib
import StacksProject_2024.Chap10.Lemma_10_70_6
import StacksProject_2024.Chap15.Definition_15_30_1
import StacksProject_2024.Chap15.Lemma_15_28_4
import StacksProject_2024.Chap15.Lemma_15_30_5
import StacksProject_2024.Chap15.Lemma_15_30_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory.Limits
open scoped Matrix
open scoped AffineBlowupChart

section

variable {R : Type u} [CommRing R]
variable {r : ℕ} (f : Fin (r + 1) → R)

local notation "I" => Ideal.span (Set.range f)
local notation "a" => tupleSpanFirst f
local notation "Q" => affineBlowupTuplePresentationQuotient f
local notation "Chart" => R[I / a]

/- Domain triage:
* primary domain: affine blowup charts and their canonical quotient presentations;
* sampled owner declarations: `affineBlowupTuplePresentationMap`,
  `affineBlowupTuplePresentationQuotient`, `tupleSpanFirst`, and the chart owner `R[I / a]`;
* best owner abstraction: the Chapter 10 presentation map is the primitive owner, and this file
  adds the `H₁`-regularity specialization upgrading that map to an equivalence;
* primitive data: the quotient presentation and its canonical map to the affine blowup chart;
* derived API: bijectivity of that map under `IsH1RegularSequence` and the resulting `AlgEquiv`.
-/

/-- Under `H₁`-regularity, the canonical presentation map to the affine blowup algebra is
bijective. -/
-- Proof sketch: Lemma `10.70.6` gives a surjective presentation map whose kernel is the
-- `a₁`-power torsion. The `H₁`-regularity hypothesis implies the quotient presentation is
-- `a₁`-torsion free, so that kernel is zero and the canonical map is injective.
private theorem affineBlowupTuplePresentationMap_bijective_of_isH1RegularSequence
    (hreg : RingTheory.Sequence.IsH1RegularSequence f) :
    Function.Bijective (affineBlowupTuplePresentationMap f) := by
  sorry

/-- Lemma 15.31.2: if `a₁, …, aᵣ₊₁` is an `H_1`-regular sequence in `R`, then the affine blowup
algebra of the ideal it generates at `a₁` is canonically isomorphic to the quotient
`R[y₂, …, yᵣ₊₁] / (a₁ yᵢ - aᵢ₊₁)`. -/
noncomputable def affineBlowupTuplePresentationOfIsH1RegularSequence
    (hreg : RingTheory.Sequence.IsH1RegularSequence f) : Q ≃ₐ[R] Chart :=
  AlgEquiv.ofBijective (affineBlowupTuplePresentationMap f)
    (affineBlowupTuplePresentationMap_bijective_of_isH1RegularSequence f hreg)

/-- The canonical isomorphism of Lemma 15.31.2 is the Chapter 10 presentation map equipped with
its `H₁`-regularity inverse. -/
theorem affineBlowupTuplePresentationOfIsH1RegularSequence_toAlgHom
    (hreg : RingTheory.Sequence.IsH1RegularSequence f) :
    (affineBlowupTuplePresentationOfIsH1RegularSequence f hreg).toAlgHom =
      affineBlowupTuplePresentationMap f := rfl

end
