import Mathlib
import StacksProject_2024.Chap12.Aux_12_20_3_1
import StacksProject_2024.Chap12.Remark_12_21_5_Variant

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Domain-style sampling for Remark 12.22.6 (Variant):
- primary domain: page-zero extensions of shifted spectral sequences attached to shifted exact
  couples;
- sampled owner declarations in the immediate chapter/project domain:
  `ShiftedExactCouple.associatedSpectralSequence`,
  `ShiftedExactCouple.associatedSpectralSequence_pageObject`,
  `ShiftedExactCouple.associatedSpectralSequence_differential`,
  `ShiftedDifferentialObject.pullbackToPreviousPage`;
- best owner abstraction: the positive pages and recursive `Z_r`/`B_r` filtration are already
  owned by `ShiftedExactCouple.associatedSpectralSequence`, while the source-facing zeroth page
  `E₀ = S⁻¹Q` is the canonical `previousPage` of the quotient differential object `Q`;
- primitive data: a shifted exact couple `X`, a shifted differential object `Q`, and the explicit
  page-one comparison `e : X.E ≅ Q.previousPage.homology`;
- derived API in this file: the zero-based page family `page`, the source-facing page-one
  comparison to `S⁻¹ H(Q)`, and the zero-based filtration pieces `cycle` and `boundary`;
- source/core/bridge triage:
  `source-facing`: `page`, `cycle`, `boundary`;
  `core/canonical`: `ShiftedExactCouple.associatedSpectralSequence`;
  `bridge/view`: the explicit comparison `e` identifying `E₁` with the homology of `E₀`.

This file is therefore a bridge/view file: it extends the owner-level shifted spectral sequence by
the source-facing page `E₀ = S⁻¹Q`, while reusing the canonical positive-page filtration from
`ShiftedExactCouple.associatedSpectralSequence` instead of introducing a parallel local owner. -/

namespace ShiftedExactCouple

variable {S T : C ≌ C} (X : ShiftedExactCouple S T)
variable (Q : ShiftedDifferentialObject S.functor)

/-- The source-facing zero-based page shifts: page `0` has the original shift `S`, and the
positive pages are the owner shifts of `X.associatedSpectralSequence`. -/
def zeroPageShift (S T : C ≌ C) (r : ℕ) : C ≌ C :=
  match r with
  | 0 => S
  | r + 1 => pageShift S T ⟨r + 1, Nat.succ_pos _⟩

/-- The source-facing zero-based page family associated to the shifted exact couple `X` and the
page-zero differential object `Q.previousPage = S⁻¹Q`. The zeroth page is `E₀`, and from page
`1` onward this is exactly the owner spectral sequence of `X`. -/
def page (r : ℕ) :
    ShiftedDifferentialObject ((zeroPageShift S T r).functor) :=
  match r with
  | 0 => Q.previousPage
  | r + 1 => X.associatedSpectralSequence.page ⟨r + 1, Nat.succ_pos _⟩

@[simp] theorem page_zero :
    page X Q 0 = Q.previousPage :=
  rfl

@[simp] theorem page_succ (r : ℕ) :
    page X Q (r + 1) = X.associatedSpectralSequence.page ⟨r + 1, Nat.succ_pos _⟩ :=
  rfl

/-- The zeroth page is the previous-page differential object `S⁻¹Q`. -/
theorem page_zero_obj :
    (page X Q 0).obj = Q.previousPage.obj :=
  rfl

/-- The differential `d₀` is the previous-page differential on `S⁻¹Q`. -/
theorem page_zero_d :
    (page X Q 0).d = Q.previousPage.d :=
  rfl

/-- The positive page `E_{r + 1}` has the owner page object of the shifted spectral sequence
attached to `X`. -/
theorem page_succ_obj (r : ℕ) :
    (page X Q (r + 1)).obj = (X.iterateDerived r).E := by
  simpa [page] using X.associatedSpectralSequence_pageObject r

/-- The differential on the positive page `E_{r + 1}` is the differential induced from the
`r`-fold derived shifted exact couple. -/
theorem page_succ_d (r : ℕ) :
    (page X Q (r + 1)).d = (X.iterateDerived r).d := by
  simpa [page] using X.associatedSpectralSequence_differential r

/-- Helper for Remark 12.22.6 (Variant): the first positive page is the `E` object of the
original shifted exact couple. -/
@[simp] theorem page_one_obj :
    (page X Q 1).obj = X.E := by
  -- Page `1` is the `r = 0` owner page, so the object is exactly the original `E`.
  simpa using page_succ_obj (X := X) (Q := Q) 0

/-- Helper for Remark 12.22.6 (Variant): the first positive differential is the original
differential of the shifted exact couple. -/
@[simp] theorem page_one_d :
    (page X Q 1).d = X.d := by
  -- Page `1` is the `r = 0` owner page, so the differential is exactly the original `d`.
  simpa using page_succ_d (X := X) (Q := Q) 0

/-- The source-facing comparison `E₁ ≅ H(E₀) = H(S⁻¹Q)`. -/
abbrev pageOneIso (e : X.E ≅ Q.previousPage.homology) :
    (page X Q 1).obj ≅ Q.previousPage.homology :=
  e

/-- The page-one object is canonically the shifted homology `S⁻¹ H(Q)`. -/
abbrev pageOneShiftedHomologyIso (e : X.E ≅ Q.previousPage.homology) :
    (page X Q 1).obj ≅ (S.functor.inv).obj Q.homology :=
  e ≪≫ Q.previousPage_homologyIso

/-- Pull a subobject of `E₁` back to the corresponding subobject of `E₀ = S⁻¹Q` via the
canonical map `ker(d₀) ⟶ E₁`. -/
private noncomputable def pullbackToPageZero
    (e : X.E ≅ Q.previousPage.homology) (Z : Subobject X.E) :
    Subobject Q.previousPage.obj :=
  Q.pullbackToPreviousPage
    ((Subobject.map (e.hom ≫ Q.previousPage_homologyIso.hom)).obj Z)

/-- Remark `12.22.6` (Variant): the recursive cycle piece `Z_r` inside the page-`E₀` object
`S⁻¹Q`. The zero stage is `Z₀ = E₀`, and for `r + 1` the source-facing filtration is pulled back
from the canonical owner filtration on `E₁`. -/
def cycle (e : X.E ≅ Q.previousPage.homology) :
    ℕ → Subobject Q.previousPage.obj
  | 0 => ⊤
  | r + 1 =>
      pullbackToPageZero X Q e
        (X.associatedSpectralSequence.cycle ⟨r + 1, Nat.succ_pos _⟩)

/-- Remark `12.22.6` (Variant): the recursive boundary piece `B_r` inside the page-`E₀` object
`S⁻¹Q`. The zero stage is `B₀ = 0`, and for `r + 1` the source-facing filtration is pulled back
from the canonical owner boundary filtration on `E₁`. -/
def boundary (e : X.E ≅ Q.previousPage.homology) :
    ℕ → Subobject Q.previousPage.obj
  | 0 => ⊥
  | r + 1 =>
      pullbackToPageZero X Q e
        (X.associatedSpectralSequence.boundary ⟨r + 1, Nat.succ_pos _⟩)

/-- Helper for Remark 12.22.6 (Variant): at a positive stage, the source-facing cycle piece is
obtained by pulling the owner cycle piece on `E₁` back along the canonical map from `E₀`. -/
@[simp] theorem cycle_succ (e : X.E ≅ Q.previousPage.homology) (r : ℕ) :
    cycle X Q e (r + 1) =
      pullbackToPageZero X Q e
        (X.associatedSpectralSequence.cycle ⟨r + 1, Nat.succ_pos _⟩) := by
  -- Unfold the recursive definition at the first positive stage.
  rfl

/-- Helper for Remark 12.22.6 (Variant): at a positive stage, the source-facing boundary piece is
obtained by pulling the owner boundary piece on `E₁` back along the canonical map from `E₀`. -/
@[simp] theorem boundary_succ (e : X.E ≅ Q.previousPage.homology) (r : ℕ) :
    boundary X Q e (r + 1) =
      pullbackToPageZero X Q e
        (X.associatedSpectralSequence.boundary ⟨r + 1, Nat.succ_pos _⟩) := by
  -- Unfold the recursive definition at the first positive stage.
  rfl

@[simp] theorem cycle_zero (e : X.E ≅ Q.previousPage.homology) :
    cycle X Q e 0 = ⊤ :=
  rfl

@[simp] theorem boundary_zero (e : X.E ≅ Q.previousPage.homology) :
    boundary X Q e 0 = ⊥ :=
  rfl

end ShiftedExactCouple

end CategoryTheory
