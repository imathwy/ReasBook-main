import Mathlib
import stacks_project.Chap12.Definition_12_20_2
import stacks_project.Chap12.Definition_12_21_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

local notation "ExactCoupleCat" => @ExactCouple C _ _

/- Domain-style sampling for Lemma 12.21.4:
- primary domain: the spectral sequence canonically attached to an exact couple, together with the
  source-facing filtration pieces `B_{r+1}` and `Z_{r+1}` on the original `E`-term;
- sampled owner declarations in the immediate chapter/project domain:
  `ExactCouple.associatedSpectralSequence`,
  `SpectralSequence.cycle`,
  `SpectralSequence.boundary`,
  `SpectralSequence.boundary_le_cycle`;
- best owner abstraction: the exact-couple owner `ExactCouple.associatedSpectralSequence`, with
  the recursive page-subquotient data owned by `SpectralSequence`;
- primitive data: the exact couple `X` and the iterates `α^r` of its endomorphism `α`;
- derived API in this file: the source-facing identifications
  `B_{r+1} = g(Ker(α^r))`, `Z_{r+1} = f⁻¹(Im(α^r))`, the monotone filtration chain on `E`, the
  canonical inclusion `B_{r+1} ≤ Z_{r+1}`, the quotient-to-page comparison
  `Z_{r+1} / B_{r+1} ≅ E_{r+1}`, and the representative-level description of the induced
  differential on the actual quotient `Z_{r+1} / B_{r+1}`;
- source/core/bridge triage:
  `source-facing`: the filtration formulas, the chain
  `0 = B₁ ⊆ ⋯ ⊆ B_{r+1} ⊆ ⋯ ⊆ Z_{r+1} ⊆ ⋯ ⊆ Z₁ = E`, and the quotient differential rule in
  Lemma 12.21.4;
  `core/canonical`: `ExactCouple.associatedSpectralSequence` together with the owner
  `SpectralSequence.cycle`, `boundary`, `boundary_le_cycle`, and `cycleToPage`;
  `bridge/view`: the equalities below identifying those owner subobjects with the concrete exact-
  couple image/kernel formulas, and the quotient-to-page map built from those identifications.

This item is therefore source-facing, not a pure recall: it should reuse the canonical owner
spectral sequence while keeping the textbook `B_{r+1}`/`Z_{r+1}` formulas, filtration chain, and
quotient description explicit. -/

/-- The `r`-fold iterate `α^r` of the endomorphism `α` of an exact couple. -/
def alphaIterate (X : ExactCoupleCat) (r : ℕ) : X.A ⟶ X.A :=
  End.asHom ((End.of X.α) ^ r)

/-- The positive owner page index corresponding to the source-facing stage `r + 1`. -/
private abbrev ownerPageIndex (r : ℕ) : ℕ+ :=
  Nat.succPNat r

/-- The owner cycle piece on page `r + 1`, viewed inside the original `E`-term. -/
private abbrev ownerCyclesSubobject (X : ExactCoupleCat) (r : ℕ) : Subobject X.E :=
  X.associatedSpectralSequence.cycle PUnit.unit (ownerPageIndex r)

/-- The owner boundary piece on page `r + 1`, viewed inside the original `E`-term. -/
private abbrev ownerBoundariesSubobject (X : ExactCoupleCat) (r : ℕ) : Subobject X.E :=
  X.associatedSpectralSequence.boundary PUnit.unit (ownerPageIndex r)

/-- The source-facing cycle piece `Z_{r + 1} = f⁻¹(Im(α^r))` inside the original `E`-term. -/
abbrev cyclesSubobject (X : ExactCoupleCat) (r : ℕ) : Subobject X.E :=
  (Subobject.pullback X.f).obj (imageSubobject (X.alphaIterate r))

/-- The source-facing boundary piece `B_{r + 1} = g(Ker(α^r))` inside the original `E`-term. -/
abbrev boundariesSubobject (X : ExactCoupleCat) (r : ℕ) : Subobject X.E :=
  imageSubobject ((kernelSubobject (X.alphaIterate r)).arrow ≫ X.g)

/-- Textbook-style notation `Z_(r)(X)` for the source-facing cycle piece `Z_{r + 1}` inside the
original `E`-term. -/
notation:max "Z_(" r ")(" X:max ")" =>
  CategoryTheory.ExactCouple.cyclesSubobject X r

/-- Textbook-style notation `B_(r)(X)` for the source-facing boundary piece `B_{r + 1}` inside
the original `E`-term. -/
notation:max "B_(" r ")(" X:max ")" =>
  CategoryTheory.ExactCouple.boundariesSubobject X r

/-- Lemma 12.21.4: in the spectral sequence attached to an exact couple, the boundary piece
`B_{r + 1}` on the original `E`-term is `g(Ker(α^r))`. -/
theorem associatedSpectralSequence_boundary_eq_image_kernel_alphaIterate
    (X : ExactCoupleCat) (r : ℕ+) :
    X.associatedSpectralSequence.boundary PUnit.unit r = B_(r.natPred)(X) :=
  sorry

/-- Lemma 12.21.4: in the spectral sequence attached to an exact couple, the cycle piece
`Z_{r + 1}` on the original `E`-term is `f⁻¹(Im(α^r))`. -/
theorem associatedSpectralSequence_cycle_eq_preimage_image_alphaIterate
    (X : ExactCoupleCat) (r : ℕ+) :
    X.associatedSpectralSequence.cycle PUnit.unit r = Z_(r.natPred)(X) :=
  sorry

/-- Lemma 12.21.4: the first boundary piece is zero, i.e. `B₁ = 0`. -/
theorem boundariesSubobject_zero (X : ExactCoupleCat) :
    B_(0)(X) = (⊥ : Subobject X.E) :=
  sorry

/-- Lemma 12.21.4: the first cycle piece is all of `E`, i.e. `Z₁ = E`. -/
theorem cyclesSubobject_zero (X : ExactCoupleCat) :
    Z_(0)(X) = (⊤ : Subobject X.E) :=
  sorry

/-- Lemma 12.21.4: the boundary pieces form an increasing filtration
`B_{r + 1} ⊆ B_{s + 1}` for `r ≤ s`. -/
theorem boundariesSubobject_mono (X : ExactCoupleCat) {r s : ℕ} (hrs : r ≤ s) :
    (B_(r)(X) : Subobject X.E) ≤ (B_(s)(X) : Subobject X.E) :=
  sorry

/-- Lemma 12.21.4: the cycle pieces form a decreasing filtration
`Z_{s + 1} ⊆ Z_{r + 1}` for `r ≤ s`. -/
theorem cyclesSubobject_antitone (X : ExactCoupleCat) {r s : ℕ} (hrs : r ≤ s) :
    (Z_(s)(X) : Subobject X.E) ≤ (Z_(r)(X) : Subobject X.E) :=
  sorry

/-- Lemma 12.21.4: the source-facing boundary piece `B_{r + 1}` is contained in the
source-facing cycle piece `Z_{r + 1}`. -/
theorem boundariesSubobject_le_cyclesSubobject (X : ExactCoupleCat) (r : ℕ) :
    (B_(r)(X) : Subobject X.E) ≤ (Z_(r)(X) : Subobject X.E) :=
  by
    have hBoundaries :
        X.associatedSpectralSequence.boundary PUnit.unit (ownerPageIndex r) =
          B_(r)(X) := by
      simpa [ownerPageIndex] using
        associatedSpectralSequence_boundary_eq_image_kernel_alphaIterate X (ownerPageIndex r)
    have hCycles :
        X.associatedSpectralSequence.cycle PUnit.unit (ownerPageIndex r) =
          Z_(r)(X) := by
      simpa [ownerPageIndex] using
        associatedSpectralSequence_cycle_eq_preimage_image_alphaIterate X (ownerPageIndex r)
    simpa [hBoundaries, hCycles] using
      X.associatedSpectralSequence.boundary_le_cycle PUnit.unit (ownerPageIndex r)

/-- The canonical inclusion `B_{r + 1} ⟶ Z_{r + 1}` for the source-facing filtration pieces. -/
private abbrev boundariesToCycles (X : ExactCoupleCat) (r : ℕ) :
    (B_(r)(X) : C) ⟶ (Z_(r)(X) : C) :=
  Subobject.ofLE
    (X.boundariesSubobject r)
    (X.cyclesSubobject r)
    (boundariesSubobject_le_cyclesSubobject X r)

/-- The literal source-facing quotient `Z_{r + 1} / B_{r + 1}`. -/
abbrev pageSubquotient (X : ExactCoupleCat) (r : ℕ) : C :=
  cokernel (X.boundariesToCycles r)

/-- The canonical page object `E_{r+1}` of the owner spectral sequence. -/
private noncomputable abbrev ownerPageObjectIso (X : ExactCoupleCat) (r : ℕ) :
    X.associatedSpectralSequence.pageObject PUnit.unit (ownerPageIndex r) ≅ (X.iterateDerived r).E :=
  eqToIso (by simpa using X.associatedSpectralSequence_pageObject r)

/-- The canonical inclusion of the owner boundary piece into the owner cycle piece on page
`r + 1`. -/
private abbrev ownerBoundariesToCycles (X : ExactCoupleCat) (r : ℕ) :
    (X.ownerBoundariesSubobject r : C) ⟶ (X.ownerCyclesSubobject r : C) :=
  Subobject.ofLE
    (X.ownerBoundariesSubobject r)
    (X.ownerCyclesSubobject r)
    (X.associatedSpectralSequence.boundary_le_cycle PUnit.unit (ownerPageIndex r))

/-- The literal source-facing quotient `Z_{r + 1} / B_{r + 1}` identifies canonically with the
owner quotient `Z_{r + 1} / B_{r + 1}` coming from `SpectralSequence.pageQuotientToPage`. -/
private noncomputable def pageSubquotientToOwnerPageQuotient (X : ExactCoupleCat) (r : ℕ) :
    X.pageSubquotient r ≅ cokernel (X.ownerBoundariesToCycles r) :=
  cokernel.mapIso
    (X.boundariesToCycles r)
    (X.ownerBoundariesToCycles r)
    (Subobject.isoOfEq _ _
      (associatedSpectralSequence_boundary_eq_image_kernel_alphaIterate X (ownerPageIndex r)).symm)
    (Subobject.isoOfEq _ _
      (associatedSpectralSequence_cycle_eq_preimage_image_alphaIterate X (ownerPageIndex r)).symm)
    (by
      simp [boundariesToCycles, ownerBoundariesToCycles, Subobject.ofLE_comp_ofLE])

/-- The canonical map from the source-facing quotient `Z_{r + 1} / B_{r + 1}` to the page
object `E_{r + 1}`. -/
private noncomputable def ownerPageQuotientToPageIso (X : ExactCoupleCat) (r : ℕ) :
    cokernel (X.ownerBoundariesToCycles r) ≅
      X.associatedSpectralSequence.pageObject PUnit.unit (ownerPageIndex r) := by
  simpa [ownerBoundariesToCycles, ownerBoundariesSubobject, ownerCyclesSubobject] using
    (by
      letI :
          IsIso (X.associatedSpectralSequence.pageQuotientToPage PUnit.unit (ownerPageIndex r)) :=
        by
          simpa using
            (SpectralSequence.pageQuotientToPage_isIso
              X.associatedSpectralSequence PUnit.unit (ownerPageIndex r))
      exact asIso (X.associatedSpectralSequence.pageQuotientToPage PUnit.unit (ownerPageIndex r)) :
        cokernel
          (Subobject.ofLE
            (X.associatedSpectralSequence.boundary PUnit.unit (ownerPageIndex r))
            (X.associatedSpectralSequence.cycle PUnit.unit (ownerPageIndex r))
            (X.associatedSpectralSequence.boundary_le_cycle PUnit.unit (ownerPageIndex r))) ≅
          X.associatedSpectralSequence.pageObject PUnit.unit (ownerPageIndex r))

/-- The canonical map from the source-facing quotient `Z_{r + 1} / B_{r + 1}` to the page
object `E_{r + 1}`. -/
private noncomputable def pageSubquotientToPageIso (X : ExactCoupleCat) (r : ℕ) :
    X.pageSubquotient r ≅ (X.iterateDerived r).E := by
  exact
    X.pageSubquotientToOwnerPageQuotient r ≪≫
      X.ownerPageQuotientToPageIso r ≪≫
        X.ownerPageObjectIso r

/-- The canonical map from the source-facing quotient `Z_{r + 1} / B_{r + 1}` to the page
object `E_{r + 1}`. -/
noncomputable def pageSubquotientToPage (X : ExactCoupleCat) (r : ℕ) :
    X.pageSubquotient r ⟶ (X.iterateDerived r).E :=
  (X.pageSubquotientToPageIso r).hom

/-- The canonical map `Z_{r + 1} / B_{r + 1} ⟶ E_{r + 1}` is an isomorphism. -/
theorem pageSubquotientToPage_isIso (X : ExactCoupleCat) (r : ℕ) :
    IsIso (X.pageSubquotientToPage r) :=
  by
    change IsIso (X.pageSubquotientToPageIso r).hom
    infer_instance

/-- The differential on the source-facing quotient `Z_{r + 1} / B_{r + 1}`, transported from the
owner page differential along the canonical comparison with `E_{r + 1}`. -/
noncomputable def pageSubquotientDifferential (X : ExactCoupleCat) (r : ℕ) :
    X.pageSubquotient r ⟶ X.pageSubquotient r :=
  letI : IsIso (X.pageSubquotientToPage r) := pageSubquotientToPage_isIso X r
  X.pageSubquotientToPage r ≫ (X.iterateDerived r).d ≫ inv (X.pageSubquotientToPage r)

/-- The source-facing quotient differential agrees with the owner differential after the canonical
comparison `Z_{r + 1} / B_{r + 1} ≅ E_{r + 1}`. -/
theorem pageSubquotientDifferential_comm (X : ExactCoupleCat) (r : ℕ) :
    X.pageSubquotientDifferential r ≫ X.pageSubquotientToPage r =
      X.pageSubquotientToPage r ≫ (X.iterateDerived r).d :=
  sorry

/-- Lemma 12.21.4: on the source-facing quotient presentation
`E_{r + 1} = Z_(r)(X) / B_(r)(X)` (that is, `Z_{r + 1} / B_{r + 1}`), the differential sends the
class of a representative `x` to the class of `g ∘ y` whenever `f ∘ x = α^r ∘ y`. -/
theorem associatedSpectralSequence_differential_eq_on_representatives
    (X : ExactCoupleCat) {T : C} (r : ℕ)
    (x : T ⟶ (Z_(r)(X) : C))
    (y : T ⟶ X.A)
    (hy : x ≫ (Z_(r)(X)).arrow ≫ X.f = y ≫ X.alphaIterate r) :
    ∃ gy : T ⟶ (Z_(r)(X) : C),
      gy ≫ (Z_(r)(X)).arrow = y ≫ X.g ∧
        x ≫ cokernel.π (X.boundariesToCycles r) ≫ X.pageSubquotientDifferential r =
          gy ≫ cokernel.π (X.boundariesToCycles r) :=
  sorry

end ExactCouple
end CategoryTheory
