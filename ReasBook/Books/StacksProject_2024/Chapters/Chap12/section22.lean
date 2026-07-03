import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_22_1 (from Chap12) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/- Domain-style sampling for Definition 12.22.1:
- primary domain: differential objects in a category with zero morphisms, expressed here in the
  chapter's one-object homological-complex language;
- sampled core/canonical declarations:
  `HomologicalComplex C (ComplexShape.refl PUnit.{1})`,
  `HomologicalComplex.d_comp_d`,
  `HomologicalComplex.Hom.comm`,
  `ExactCouple.page`;
- sampled more general upstream declaration:
  `CategoryTheory.DifferentialObject`, which packages a shifted differential
  `X ⟶ X⟦(1 : S)⟧` and therefore lives at a different owner level from the source's unshifted
  endomorphism-squared-zero notion;
- best owner abstraction for this item:
  `HomologicalComplex C (ComplexShape.refl PUnit.{1})`;
- primitive data: the single object together with the unique differential of the one-object
  complex;
- derived API: square-zero of that differential via `HomologicalComplex.d_comp_d`, and
  commutation of morphisms with it via `HomologicalComplex.Hom.comm`;
- source/core/bridge triage:
  `source-facing`: the textbook differential object, i.e. an object with an endomorphism whose
    square is zero;
  `core/canonical`: the one-object homological-complex owner
    `HomologicalComplex C (ComplexShape.refl PUnit.{1})`;
  `bridge/view`: source-facing unpacking into the unique component and differential, as used by
    `ExactCouple.page`.

No local wrapper is needed: in this chapter the source notion is already canonically owned by the
one-object `HomologicalComplex` specialization. -/
/- Definition 12.22.1: in the abelian-category setting of the chapter, a differential object is
canonically the one-object homological complex `HomologicalComplex C (ComplexShape.refl PUnit.{1})`,
equivalently an object equipped with an endomorphism whose square is zero; morphisms are the chain
maps, i.e. the maps commuting with the distinguished endomorphisms. -/
#check (HomologicalComplex C (ComplexShape.refl PUnit.{1}))

/- Companion recall: the unique differential of a one-object homological complex squares to zero by
specializing the owner lemma `HomologicalComplex.d_comp_d`. -/
recall HomologicalComplex.d_comp_d

/- Companion recall: a morphism of one-object homological complexes commutes with the unique
differential by the owner lemma `HomologicalComplex.Hom.comm`. -/
recall HomologicalComplex.Hom.comm

end CategoryTheory

/-! ### Lemma_12_22_2 (from Chap12) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Domain-style sampling for Lemma 12.22.2:
- primary domain: differential objects in an abelian category, realized in this chapter as
  one-object homological complexes;
- sampled owner declarations in the local/canonical ecosystem:
  `HomologicalComplex C (ComplexShape.refl PUnit.{1})`,
  `HomologicalComplex.instAbelian`,
  `HomologicalComplex.d_comp_d`,
  `HomologicalComplex.Hom.comm`;
- best owner abstraction: the chapter owner
  `HomologicalComplex C (ComplexShape.refl PUnit.{1})`;
- primitive data: for this lemma, only the ambient abelian category and the owner category of
  one-object complexes;
- derived API: the abelian-category instance supplied canonically by
  `HomologicalComplex.instAbelian`;
- source/core/bridge triage:
  `source-facing`: the differential-object language introduced in Definition 12.22.1;
  `core/canonical`: the instance `HomologicalComplex.instAbelian` specialized to the one-object
    shape;
  `bridge/view`: Definition 12.22.1, which identifies the source notion with the owner
    `HomologicalComplex C (ComplexShape.refl PUnit.{1})`.

This file is therefore a pure core/canonical recall, not a place for any new wrapper API. -/
/- Lemma 12.22.2: the category of differential objects of `C`, identified in
Definition 12.22.1 with the category of one-object homological complexes in `C`,
is an abelian category. This is the one-object specialization of the canonical
owner instance `HomologicalComplex.instAbelian`. -/
recall HomologicalComplex.instAbelian

end CategoryTheory

/-! ### Definition_12_22_3 (from Chap12) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Domain-style sampling for Definition 12.22.3:
- primary domain: homology of differential objects in an abelian category, realized in this
  chapter as one-object homological complexes;
- sampled canonical declarations in the local/mathlib owner ecosystem:
  `HomologicalComplex.homology`,
  `HomologicalComplex.homologyFunctor`,
  `HomologicalComplex.homologyMap`,
  `ShortComplex.homology`;
- best owner abstraction: the one-object specialization of `HomologicalComplex.homology` at
  `PUnit.unit`;
- primitive data: the ambient abelian category and a one-object homological complex `A`;
- derived API: functoriality via
  `HomologicalComplex.homologyFunctor C (ComplexShape.refl PUnit.{1}) PUnit.unit` and the induced
  map `HomologicalComplex.homologyMap φ PUnit.unit`;
- source/core/bridge triage:
  `source-facing`: the homology object `H(A,d) = ker d / im d` of a differential object;
  `core/canonical`: `HomologicalComplex.homology`;
  `bridge/view`: Definition 12.22.1, which identifies differential objects with one-object
    homological complexes, together with evaluation of the owner construction at `PUnit.unit`.

This item is therefore a source-facing bridge/view on the canonical owner: the public surface
should expose the one-object specialization `H(A)` rather than only the fully general owner
`HomologicalComplex.homology`, without introducing a second public owner alias. -/

scoped notation "H(" A ")" => HomologicalComplex.homology A PUnit.unit

variable (A : HomologicalComplex C (ComplexShape.refl PUnit.{1}))

/- Definition 12.22.3: for a differential object `A`, the source-facing homology object is
`H(A)`, i.e. the one-object specialization of `HomologicalComplex.homology` at `PUnit.unit`. -/
#check H(A)

/- Companion recall: the source-facing homology of differential objects is functorial via the
one-object specialization of `HomologicalComplex.homologyFunctor`. -/
#check (HomologicalComplex.homologyFunctor C (ComplexShape.refl PUnit.{1}) PUnit.unit)

end CategoryTheory

/-! ### Lemma_12_22_4 (from Chap12) -/
open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

/-
Domain-style sampling for Lemma 12.22.4:
- primary domain: periodic homology exact sequences for differential objects in an abelian
  category, realized in this chapter as one-object homological complexes;
- sampled owner declarations:
  `HomologicalComplex.HomologySequence.composableArrows₅`,
  `HomologicalComplex.HomologySequence.composableArrows₅_exact`,
  `ShortComplex.ShortExact.homology_exact₁`,
  `ShortComplex.ShortExact.homology_exact₂`,
  `ShortComplex.ShortExact.homology_exact₃`;
- best owner abstraction: the canonical five-term homology segment
  `HomologicalComplex.HomologySequence.composableArrows₅_exact`, specialized to the one-object
  shape `ComplexShape.refl PUnit`;
- primitive data: a short exact sequence `hS : S.ShortExact` of one-object homological complexes;
- derived API: the periodic exact segment and its three consecutive exactness pieces.

Source/core/bridge triage:
- `source-facing`: the periodic homology segment attached to a short exact sequence of
  differential objects;
- `core/canonical`: `HomologicalComplex.HomologySequence.composableArrows₅_exact`;
- `bridge/view`: the specialization to `ComplexShape.refl PUnit`, using the Chapter 12
  identification of differential objects with one-object homological complexes.

No local exact-sequence theorem is needed here: the source statement is exactly this owner
specialization. -/

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (HomologicalComplex C (ComplexShape.refl PUnit.{1}))}
  (hS : S.ShortExact)

/- Lemma 12.22.4: a short exact sequence of differential objects in an abelian category yields
the exact periodic homology segment
`H(A, d) ⟶ H(B, d) ⟶ H(C, d) ⟶ H(A, d) ⟶ H(B, d) ⟶ H(C, d)`.

This is the `ComplexShape.refl PUnit` specialization of the canonical owner declaration
`HomologicalComplex.HomologySequence.composableArrows₅_exact`. -/
#check (composableArrows₅_exact hS PUnit.unit PUnit.unit rfl :
  (composableArrows₅ hS PUnit.unit PUnit.unit rfl).Exact)

end CategoryTheory

/-! ### Definition_12_22_5 (from Chap12) -/
/-
Domain-style sampling for Definition 12.22.5:
- primary domain: spectral sequences attached to differential objects in an abelian category;
- sampled core/canonical declarations:
  `SpectralSequence C (fun _ : ℤ ↦ ComplexShape.refl PUnit.{1}) 1`,
  `SpectralSequence.cycle`,
  `SpectralSequence.boundary`,
  `ExactCouple.associatedSpectralSequence`;
- best owner abstraction: the page-`1` spectral-sequence owner
  `ExactCouple.associatedSpectralSequence (exactCouple α)`;
- primitive data: the source-facing page-`E₀` owner `spectralSequence α`, whose zeroth page is
  `cokernel α`, and the canonical page-`1` spectral-sequence owner attached to the exact couple;
- derived API in this file: the page-`0` spectral sequence and the source-facing zero-based
  pullback filtrations `cycle`/`boundary` on `E₀`;
- source/core/bridge triage:
  `source-facing`: `spectralSequence`, `cycle`, `boundary`;
  `core/canonical`: `ExactCouple.associatedSpectralSequence`;
  `bridge/view`: the pullback of the canonical page-`1` filtration along `ker(d₀) ⟶ E₁`.

The public source-facing content here is the page-`E₀` presentation. The positive-stage `Z_{r+1}`/
`B_{r+1}` objects on page `E₁` are already owned upstream by `SpectralSequence.cycle` and
`SpectralSequence.boundary`, so this file should reuse that owner directly while adding the
explicit zero-stage source terms `Z₀ = E₀` and `B₀ = 0` instead of rebuilding a parallel
page-`1` wrapper.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory
open HomologicalComplex.HomologySequence
open scoped SpectralSequence

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DifferentialObjectAssociatedSpectralSequence

open ExactCouple

variable {A : HomologicalComplex C (ComplexShape.refl PUnit.{1})}
variable (α : A ⟶ A)

/-- The exact couple obtained from the periodic homology sequence of
`0 ⟶ (A,d) --α→ (A,d) ⟶ (A / α A,d) ⟶ 0`. Its outer object is `H(A)`, its inner object is
`H(cokernel α)`, the endomorphism is induced by `α`, the map `H(A) ⟶ H(cokernel α)` is induced by
the quotient map, and the return map is the connecting morphism. -/
private noncomputable def exactCouple [Mono α] : @CategoryTheory.ExactCouple C _ _ := by
  let S : ShortComplex (HomologicalComplex C (ComplexShape.refl PUnit.{1})) :=
    ShortComplex.mk α (cokernel.π α) (cokernel.condition α)
  let hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel α) (inferInstance : Mono S.f) (inferInstance : Epi S.g)
  exact
    { A := H(A)
      E := H(cokernel α)
      α := HomologicalComplex.homologyMap α PUnit.unit
      f := hS.δ PUnit.unit PUnit.unit rfl
      g := HomologicalComplex.homologyMap (cokernel.π α) PUnit.unit
      f_comp_α := by
        simpa [S] using hS.δ_comp PUnit.unit PUnit.unit rfl
      g_comp_f := by
        simpa [S] using hS.comp_δ PUnit.unit PUnit.unit rfl
      α_comp_g := by
        rw [← HomologicalComplex.homologyMap_comp, cokernel.condition, HomologicalComplex.homologyMap_zero]
      exact_f_α := by
        simpa [S] using hS.homology_exact₁ PUnit.unit PUnit.unit rfl
      exact_g_f := by
        simpa [S] using hS.homology_exact₃ PUnit.unit PUnit.unit rfl
      exact_α_g := by
        simpa [S] using hS.homology_exact₂ PUnit.unit }

/-- Definition 12.22.5: the spectral sequence associated to a differential object `(A,d)` and a
monomorphism `α : (A,d) ⟶ (A,d)` starts at page `E₀ = (A / α A,d)`, with `d₀` the induced
differential on the quotient, and from page `1` onward is the canonical spectral sequence of the
exact couple attached to the short exact sequence
`0 ⟶ (A,d) --α→ (A,d) ⟶ (A / α A,d) ⟶ 0`. In particular `E₁ = H(A / α A,d)`. -/
noncomputable def spectralSequence [Mono α] :
    SpectralSequence C (fun _ : ℤ ↦ ComplexShape.refl PUnit.{1}) 0 where
  page r hr := match r with
    | Int.ofNat 0 => cokernel α
    | Int.ofNat (n + 1) => (exactCouple α).associatedSpectralSequence.page (Int.ofNat (n + 1))
    | Int.negSucc _ => nomatch hr
  iso r r' _ hrr' hr := match r with
    | Int.ofNat 0 => match hrr' with
      | rfl => eqToIso (by
          simpa using (associatedSpectralSequence_pageObject (exactCouple α) 0).symm)
    | Int.ofNat (n + 1) => match hrr' with
      | rfl => by
          simpa using
            (exactCouple α).associatedSpectralSequence.iso
              (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) PUnit.unit
    | Int.negSucc _ => nomatch hr

section

variable [Mono α]

/-- The zeroth page is the quotient differential object `(A / α A, d)`. -/
theorem page_zero :
    (spectralSequence α).page 0 = cokernel α := rfl

/-- The unique object on page `E₀` is the quotient object `A / α A`. -/
theorem page_zero_obj :
    ((spectralSequence α).page 0).X PUnit.unit = (cokernel α).X PUnit.unit := rfl

/-- The differential `d₀` is the induced differential on the quotient complex `A / α A`. -/
theorem page_zero_d :
    ((spectralSequence α).page 0).d PUnit.unit PUnit.unit =
      (cokernel α).d PUnit.unit PUnit.unit := rfl

/-- The kernel subobject maps canonically to the cycles object. -/
private noncomputable def kernelSubobjectToCycles
    {κ : Type*} {c : ComplexShape κ} (K : HomologicalComplex C c) (pq : κ) :
    (kernelSubobject (K.dFrom pq) : C) ⟶ K.cycles pq :=
  K.liftCycles (kernelSubobject (K.dFrom pq)).arrow (c.next pq) rfl
    (kernelSubobject_arrow_comp (K.dFrom pq))

/-- The cycle object of the quotient differential object, viewed as a subobject of `E₀`. -/
private noncomputable abbrev pageZeroCycles :
    Subobject ((cokernel α).X PUnit.unit) :=
  kernelSubobject ((cokernel α).dFrom PUnit.unit)

/-- The canonical map `Z₁ = ker(d₀) ⟶ H(A / α A,d) = E₁`. Pulling back the owner filtration of
`(exactCouple α).associatedSpectralSequence` along this morphism recovers the recursive source
filtration on `E₀`. -/
private noncomputable def pageZeroCyclesToHomology :
    (pageZeroCycles α : C) ⟶ H(cokernel α) :=
  kernelSubobjectToCycles (cokernel α) PUnit.unit ≫
    (cokernel α).homologyπ PUnit.unit

/-- Pull a subobject of `H(A / α A,d) = E₁` back to the corresponding subobject of
`E₀ = A / α A` via the canonical map `ker(d₀) ⟶ H(A / α A,d)`. -/
private noncomputable def pullbackToPageZero
    (Z : Subobject (H(cokernel α))) :
    Subobject ((cokernel α).X PUnit.unit) :=
  (Subobject.map (pageZeroCycles α).arrow).obj
    ((Subobject.pullback (pageZeroCyclesToHomology α)).obj Z)

/-- The positive owner page number corresponding to the source-facing stage `r + 1` on `E₀`. -/
private abbrev ownerPageIndex (r : ℕ) : ℕ+ :=
  ⟨r + 1, Nat.succ_pos _⟩

/-- Definition 12.22.5: the recursive cycle piece `Z_r` inside the page-`E₀` object
`A / α A`. The zero stage is `Z₀ = E₀`, and for `r + 1` this is the source-facing filtration on
`E₀` obtained from the canonical owner filtration on the page-`E₁` view by pullback along
`ker(d₀) ⟶ E₁`. -/
def cycle : ℕ → Subobject ((cokernel α).X PUnit.unit)
  | 0 => ⊤
  | r + 1 =>
      pullbackToPageZero α
        ((exactCouple α).associatedSpectralSequence.cycle PUnit.unit (ownerPageIndex r))

/-- Definition 12.22.5: the recursive boundary piece `B_r` inside the page-`E₀` object
`A / α A`. The zero stage is `B₀ = 0`, and for `r + 1` this is the source-facing boundary
filtration obtained from the canonical owner filtration on the page-`E₁` view by pullback along
`ker(d₀) ⟶ E₁`. -/
def boundary : ℕ → Subobject ((cokernel α).X PUnit.unit)
  | 0 => ⊥
  | r + 1 =>
      pullbackToPageZero α
        ((exactCouple α).associatedSpectralSequence.boundary PUnit.unit (ownerPageIndex r))

/-- The zero-stage cycle piece is the whole page-`E₀` object. -/
theorem cycle_zero :
    cycle α 0 = ⊤ :=
  rfl

/-- The zero-stage boundary piece is zero. -/
theorem boundary_zero :
    boundary α 0 = ⊥ :=
  rfl

/-- The first page is the differential-homology object `H(A / α A,d)`. -/
theorem page_one :
    ((spectralSequence α).page 1).X PUnit.unit = H(cokernel α) := by
  simpa [spectralSequence] using
    associatedSpectralSequence_pageObject (exactCouple α) 0

end

end DifferentialObjectAssociatedSpectralSequence

end CategoryTheory

/-! ### Remark_12_22_6_Variant (from Chap12) -/
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

@[simp] theorem cycle_zero (e : X.E ≅ Q.previousPage.homology) :
    cycle X Q e 0 = ⊤ :=
  rfl

@[simp] theorem boundary_zero (e : X.E ≅ Q.previousPage.homology) :
    boundary X Q e 0 = ⊥ :=
  rfl

end ShiftedExactCouple

end CategoryTheory
