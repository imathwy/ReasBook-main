import Mathlib
import StacksProject_2024.Chap12.Definition_12_19_3
import StacksProject_2024.Chap12.Definition_12_20_2
import StacksProject_2024.Chap12.Definition_12_21_3

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
  Nat.rec (𝟙 X.A) (fun _ f ↦ f ≫ X.α) r

/-- Helper for Lemma 12.21.4: iterates of `α` compose by addition of exponents. -/
theorem alphaIterate_add (X : ExactCoupleCat) (r s : ℕ) :
    X.alphaIterate (r + s) = X.alphaIterate r ≫ X.alphaIterate s := by
  induction s with
  | zero =>
      -- The zero-th iterate is the identity.
      simp [alphaIterate]
  | succ s ih =>
      -- Extend the factorization of `α^(r+s)` by one more copy of `α`.
      simpa [Nat.add_assoc, alphaIterate, Category.assoc] using
        congrArg (fun k : X.A ⟶ X.A ↦ k ≫ X.α) ih

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
@[stacks 011T]
theorem associatedSpectralSequence_boundary_eq_image_kernel_alphaIterate
    (X : ExactCoupleCat) (r : ℕ+) :
    X.associatedSpectralSequence.boundary PUnit.unit r = B_(r.natPred)(X) :=
  -- TODO: identify the owner recursive boundary on page `r` with the page-one boundary of
  -- `X.iterateDerived r.natPred`, then rewrite that boundary using Lemma 12.21.2 on the
  -- iterated derived exact couple.
  sorry

/-- Lemma 12.21.4: in the spectral sequence attached to an exact couple, the cycle piece
`Z_{r + 1}` on the original `E`-term is `f⁻¹(Im(α^r))`. -/
@[stacks 011T]
theorem associatedSpectralSequence_cycle_eq_preimage_image_alphaIterate
    (X : ExactCoupleCat) (r : ℕ+) :
    X.associatedSpectralSequence.cycle PUnit.unit r = Z_(r.natPred)(X) :=
  -- TODO: identify the owner recursive cycle on page `r` with the page-one cycles of
  -- `X.iterateDerived r.natPred`, then rewrite `Ker(d)` as `f⁻¹(Im(α^r))` by iterating
  -- Lemma 12.21.2 through the derived exact-couple construction.
  sorry

/-- Lemma 12.21.4: the first boundary piece is zero, i.e. `B₁ = 0`. -/
@[stacks 011T]
theorem boundariesSubobject_zero (X : ExactCoupleCat) :
    B_(0)(X) = (⊥ : Subobject X.E) :=
  by
    -- At stage `0`, `α^0 = 𝟙`, so the relevant kernel is zero and its image under `g` is zero.
    have hker : kernelSubobject (𝟙 X.A) = (⊥ : Subobject X.A) := by
      rw [Subobject.mk_eq_bot_iff_zero]
      simpa using (kernelSubobject_arrow_comp (𝟙 X.A))
    simpa [boundariesSubobject, alphaIterate] using
      congrArg (fun S : Subobject X.A ↦ imageSubobject (S.arrow ≫ X.g))
        hker

/-- Lemma 12.21.4: the first cycle piece is all of `E`, i.e. `Z₁ = E`. -/
@[stacks 011T]
theorem cyclesSubobject_zero (X : ExactCoupleCat) :
    Z_(0)(X) = (⊤ : Subobject X.E) :=
  by
    -- At stage `0`, `α^0 = 𝟙`, so `Im(α^0) = A`; pulling back the top subobject gives all of `E`.
    simpa [cyclesSubobject, alphaIterate, Subobject.pullback_top] using
      congrArg ((Subobject.pullback X.f).obj)
        (Limits.imageSubobject_eq_top_of_epi (𝟙 (X.A)))

/-- Lemma 12.21.4: the boundary pieces form an increasing filtration
`B_{r + 1} ⊆ B_{s + 1}` for `r ≤ s`. -/
@[stacks 011T]
theorem boundariesSubobject_mono (X : ExactCoupleCat) {r s : ℕ} (hrs : r ≤ s) :
    (B_(r)(X) : Subobject X.E) ≤ (B_(s)(X) : Subobject X.E) :=
  by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrs
    -- A vector killed by `α^r` is also killed by `α^(r+t)` because the latter factors through
    -- the former.
    have hker :
        kernelSubobject (X.alphaIterate r) ≤ kernelSubobject (X.alphaIterate (r + t)) := by
      refine le_kernelSubobject _ _ ?_
      rw [alphaIterate_add]
      simpa [Category.assoc] using
        congrArg (fun k : (kernelSubobject (X.alphaIterate r) : C) ⟶ X.A ↦ k ≫ X.alphaIterate t)
          (kernelSubobject_arrow_comp (X.alphaIterate r))
    -- Apply `g` to the larger kernel and use the universal property of the image.
    rw [boundariesSubobject, boundariesSubobject, ← Subobject.factorThru_arrow _ _ hker,
      Category.assoc]
    exact imageSubobject_comp_le _ _

/-- Lemma 12.21.4: the cycle pieces form a decreasing filtration
`Z_{s + 1} ⊆ Z_{r + 1}` for `r ≤ s`. -/
@[stacks 011T]
theorem cyclesSubobject_antitone (X : ExactCoupleCat) {r s : ℕ} (hrs : r ≤ s) :
    (Z_(s)(X) : Subobject X.E) ≤ (Z_(r)(X) : Subobject X.E) :=
  by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrs
    -- The iterate `α^(r+t)` factors through `α^r`, so its image is contained in `Im(α^r)`.
    have himage :
        imageSubobject (X.alphaIterate (r + t)) ≤ imageSubobject (X.alphaIterate r) := by
      rw [Nat.add_comm, alphaIterate_add]
      exact imageSubobject_comp_le _ _
    -- Pulling back along `f` preserves the order on subobjects.
    simpa [cyclesSubobject] using (Subobject.pullback X.f).monotone himage

/-- Lemma 12.21.4: the source-facing boundary piece `B_{r + 1}` is contained in the
source-facing cycle piece `Z_{r + 1}`. -/
@[stacks 011T]
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
  by
    -- Expand the transported differential and cancel the comparison isomorphism.
    letI : IsIso (X.pageSubquotientToPage r) := pageSubquotientToPage_isIso X r
    simp [pageSubquotientDifferential, Category.assoc]

/-- Lemma 12.21.4: on the source-facing quotient presentation
`E_{r + 1} = Z_(r)(X) / B_(r)(X)` (that is, `Z_{r + 1} / B_{r + 1}`), the differential sends the
class of a representative `x` to the class of `g ∘ y` whenever `f ∘ x = α^r ∘ y`. -/
@[stacks 011T]
theorem associatedSpectralSequence_differential_eq_on_representatives
    (X : ExactCoupleCat) {T : C} (r : ℕ)
    (x : T ⟶ (Z_(r)(X) : C))
    (y : T ⟶ X.A)
    (hy : x ≫ (Z_(r)(X)).arrow ≫ X.f = y ≫ X.alphaIterate r) :
    ∃ gy : T ⟶ (Z_(r)(X) : C),
      gy ≫ (Z_(r)(X)).arrow = y ≫ X.g ∧
        x ≫ cokernel.π (X.boundariesToCycles r) ≫ X.pageSubquotientDifferential r =
          gy ≫ cokernel.π (X.boundariesToCycles r) :=
  -- TODO: first factor `y ≫ g` through `Z_(r)(X)` using the pullback description of
  -- `Z_(r)(X) = f⁻¹(Im(α^r))`, then compose both sides with `pageSubquotientToPage r`,
  -- rewrite via `pageSubquotientDifferential_comm`, and evaluate the owner differential on the
  -- represented class using the exact-couple description on `X.iterateDerived r`.
  sorry

end ExactCouple
end CategoryTheory
