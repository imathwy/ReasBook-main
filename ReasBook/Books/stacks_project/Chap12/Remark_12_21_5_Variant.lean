import Mathlib
import stacks_project.Chap12.Remark_12_20_3_Variant

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroMorphisms C]

/- Domain-style sampling for Remark 12.21.5 (Variant):
- primary domain: shifted exact couples and the shifted spectral sequences canonically attached to
  them;
- sampled owner declarations in the immediate project domain:
  `ShiftedDifferentialObject`,
  `ShiftedDifferentialObject.shortComplex`,
  `ShiftedSpectralSequence`,
  `ShiftedSpectralSequence.toSpectralSequence`;
- best owner abstraction: the chapter owner `ShiftedSpectralSequence`;
- primitive data: the source-facing shifted exact-couple objects `A`, `E`, the translated outer
  map `T A ⟶ A`, the maps `f`, `g`, the three vanishing composites, and the three exactness
  assertions;
- derived API: the adjoint form `α`, the page-one shifted differential object, the derived shifted
  exact couple, the recursive pages `iterateDerived`, and the associated shifted spectral sequence;
- source/core/bridge triage:
  `source-facing`: `ShiftedExactCouple`;
  `core/canonical`: `ShiftedSpectralSequence` and `ShiftedDifferentialObject`;
  `bridge/view`: `ShiftedExactCouple.d`, `ShiftedExactCouple.α`, the coercion to
  `ShiftedDifferentialObject`, and the page-identification lemmas for
  `ShiftedExactCouple.associatedSpectralSequence`.

The owner in this file is therefore the shifted exact couple itself; the shifted differential
object and the shifted spectral sequence are canonical downstream views derived from that source
data. -/
/-- Remark 12.21.5 (Variant): for shift autoequivalences `S` and `T`, a variant exact couple
consists of objects `A` and `E`, the intrinsic comparison map `T A ⟶ A` of the exact sequence
`T E ⟶ T A ⟶ A ⟶ S E ⟶ S A`, together with `f : E ⟶ A` and `g : A ⟶ S E`. The source-facing
map `α : A ⟶ T⁻¹ A` is recovered canonically as the adjoint transpose of `tAlpha`. As in
Definition 12.21.1, the ambient abelian hypothesis is only needed later for the derived/homology
constructions, not for this source-facing owner itself. -/
structure ShiftedExactCouple (S T : C ≌ C) where
  /-- The `A`-object of the shifted exact couple. -/
  A : C
  /-- The `E`-object of the shifted exact couple. -/
  E : C
  /-- The translated morphism `T A ⟶ A` in the exact-couple sequence. -/
  tAlpha : T.functor.obj A ⟶ A
  /-- The morphism `f : E ⟶ A`. -/
  f : E ⟶ A
  /-- The morphism `g : A ⟶ S E`. -/
  g : A ⟶ S.functor.obj E
  /-- The composite `T f` followed by `T A ⟶ A` vanishes. -/
  Tf_comp_tAlpha : T.functor.map f ≫ tAlpha = 0
  /-- The composite `T A ⟶ A ⟶ S E` vanishes. -/
  tAlpha_comp_g : tAlpha ≫ g = 0
  /-- The composite `A ⟶ S E ⟶ S A` vanishes. -/
  g_comp_Sf : g ≫ S.functor.map f = 0
  /-- Exactness of `T E ⟶ T A ⟶ A`. -/
  exact_Tf_tAlpha :
    (ShortComplex.mk (T.functor.map f) tAlpha Tf_comp_tAlpha).Exact
  /-- Exactness of `T A ⟶ A ⟶ S E`. -/
  exact_tAlpha_g :
    (ShortComplex.mk tAlpha g tAlpha_comp_g).Exact
  /-- Exactness of `A ⟶ S E ⟶ S A`. -/
  exact_g_Sf :
    (ShortComplex.mk g (S.functor.map f) g_comp_Sf).Exact

end

section

variable [Abelian C]

namespace ShiftedExactCouple

variable {S T : C ≌ C} (X : ShiftedExactCouple S T)

/-- The shift on the `r`-th page of the spectral sequence associated to a shifted exact couple:
it is `S` on page `1` and is obtained by precomposing by `T` at each successive page, giving
`T^(r - 1) ∘ S`. -/
def pageShift (S T : C ≌ C) (r : ℕ+) : C ≌ C :=
  Nat.rec S (fun _ e ↦ e.trans T) r.natPred

/-- The page-one differential on the middle object of a shifted exact couple. -/
abbrev d : X.E ⟶ S.functor.obj X.E :=
  X.f ≫ X.g

/-- The source-facing adjoint form `α : A ⟶ T⁻¹ A` of the translated map `T A ⟶ A`. -/
abbrev α : X.A ⟶ T.inverse.obj X.A :=
  (T.toAdjunction.homEquiv X.A X.A) X.tAlpha

/-- A shifted exact couple determines the page-one shifted differential object `E ⟶ S E`. -/
instance : CoeOut (ShiftedExactCouple S T) (ShiftedDifferentialObject S.functor) where
  coe X :=
    { obj := X.E
      d := X.d
      d_squared := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ X.f ≫ k ≫ S.functor.map X.g) X.g_comp_Sf }

end ShiftedExactCouple

namespace ShiftedExactCouple

variable {S T : C ≌ C} (X : ShiftedExactCouple S T)

/-- The page-one shifted differential object carried by a shifted exact couple. -/
private abbrev page : ShiftedDifferentialObject S.functor :=
  X

/-- The outer object `A'` of the derived shifted exact couple. -/
private abbrev derivedA : C :=
  image X.tAlpha

/-- The middle object `E'` of the derived shifted exact couple. -/
private abbrev derivedE : C :=
  X.page.homology

/-- The short complex attached to the underlying shifted differential object. -/
private noncomputable abbrev pageSc : ShortComplex C :=
  X.page.shortComplex

/-- The translated outer map `T A' ⟶ A'` of the derived shifted exact couple. -/
private noncomputable abbrev derivedTAlpha : T.functor.obj X.derivedA ⟶ X.derivedA :=
  (PreservesImage.iso T.functor X.tAlpha).inv ≫
    image.map (Arrow.homMk' _ _ rfl)

-- Proof sketch: a cycle `z : Z₁ ⟶ E` satisfies `z ≫ f ≫ g = 0`, so `z ≫ f` lands in
-- `ker(g) = im(TA ⟶ A)` and therefore factors canonically through `A' = image(tAlpha)`.
/-- The map from cycles of the page-one differential to `A'` induced by `f`. -/
private noncomputable def derivedfCycles : X.pageSc.cycles ⟶ X.derivedA :=
  let hImage := X.exact_tAlpha_g.isLimitImage'
  hImage.lift
    (KernelFork.ofι (X.pageSc.iCycles ≫ X.f) (by
      simpa [ShiftedDifferentialObject.shortComplex, ShiftedDifferentialObject.homology,
        shiftedPageShortComplex, Category.assoc] using
          X.pageSc.iCycles_g))

-- Proof sketch: a boundary in `cycles(d₁)` is represented by the previous differential
-- `S⁻¹E ⟶ E`; after composing with `f`, exactness identifies the result with zero in `A'`.
/-- The cycles-to-`A'` map induced by `f` vanishes on boundaries. -/
private theorem toCycles_comp_derivedfCycles_zero :
    X.pageSc.toCycles ≫ X.derivedfCycles = 0 := sorry

/-- The map `f' : E' ⟶ A'` in the derived shifted exact couple. -/
private noncomputable abbrev derivedf : X.derivedE ⟶ X.derivedA :=
  X.pageSc.descHomology X.derivedfCycles X.toCycles_comp_derivedfCycles_zero

/-- The `(TS)`-shifted page-one short complex whose homology is `(TS)E'`. -/
private noncomputable abbrev derivedgPageSc : ShortComplex C :=
  (S.trans T).functor.mapShortComplex.obj X.pageSc

-- Proof sketch: `g : A ⟶ SE` followed by `S(d₁)` is zero because
-- `d₁ = f ≫ g` and the exact-couple relation `g ≫ S(f) = 0` forces
-- `g ≫ S(f) ≫ S(g) = 0`; applying `T` preserves this vanishing.
/-- The map `T(g) : T A ⟶ TS(E)` lands in the cycles of the `(TS)`-shifted page-one complex. -/
private theorem derivedgFromTA_comp_d_zero :
    T.functor.map X.g ≫ X.derivedgPageSc.g = 0 := sorry

/-- The map from `T A` to the cycles of the `(TS)`-shifted page-one complex induced by `g`. -/
private noncomputable def derivedgCycles :
    T.functor.obj X.A ⟶ X.derivedgPageSc.cycles :=
  X.derivedgPageSc.liftCycles (T.functor.map X.g) X.derivedgFromTA_comp_d_zero

/-- The homology-class map `T A ⟶ (TS)E'` induced by `T(g)`. -/
private noncomputable abbrev derivedgFromTA :
    T.functor.obj X.A ⟶ (S.trans T).functor.obj X.derivedE :=
  X.derivedgCycles ≫ X.derivedgPageSc.homologyπ ≫ (X.pageSc.mapHomologyIso (S.trans T).functor).hom

-- Proof sketch: on `T(E)`, the map `T(g)` represents the differential of the `(TS)`-shifted
-- page-one complex, hence its class in homology vanishes; exactness identifies `A'` as the
-- cokernel of `T(f)`.
/-- The homology-class map induced by `T(g)` vanishes on `T(f)`, so it descends to `A'`. -/
private theorem Tf_comp_derivedgFromTA_zero :
    T.functor.map X.f ≫ X.derivedgFromTA = 0 := sorry

/-- The canonical connecting map in the derived shifted exact couple. -/
private noncomputable def derivedg : X.derivedA ⟶ (S.trans T).functor.obj X.derivedE :=
  let hImage := X.exact_Tf_tAlpha.isColimitImage
  hImage.desc (CokernelCofork.ofπ X.derivedgFromTA X.Tf_comp_derivedgFromTA_zero)

-- Proof sketch: `T(f')` is induced from `f` on the page-one homology and `α'` is adjoint to the
-- translated outer map on `A'`; the exactness of the original couple forces the composite to
-- vanish in the derived exact couple.
/-- In the derived shifted exact couple, the composite `T(f') ≫ Tα'` vanishes. -/
private theorem derived_Tf_comp_tAlpha_zero :
    T.functor.map X.derivedf ≫ X.derivedTAlpha = 0 := sorry

-- Proof sketch: the derived `α'` and `g'` encode the next translated connecting morphism, whose
-- composite vanishes by construction of the derived exact couple.
/-- In the derived shifted exact couple, the composite `T A' ⟶ A' ⟶ (TS) E'` vanishes. -/
private theorem derived_tAlpha_comp_derivedg_zero :
    X.derivedTAlpha ≫ X.derivedg = 0 := sorry

-- Proof sketch: `g'` lands in the next page and `f'` is induced from boundaries, so the
-- resulting composite is zero in the derived exact couple.
/-- In the derived shifted exact couple, the composite `g' ≫ TS(f')` vanishes. -/
private theorem derivedg_comp_TSf_zero :
    X.derivedg ≫ (S.trans T).functor.map X.derivedf = 0 := sorry

-- Proof sketch: identify `A'` with the image of `T A ⟶ A` and use the original exactness after
-- passage to the derived page-one homology.
/-- Exactness of the derived shifted exact couple at `T A' ⟶ A'`. -/
private theorem derived_exact_Tf_tAlpha :
    (ShortComplex.mk (T.functor.map X.derivedf) X.derivedTAlpha
      X.derived_Tf_comp_tAlpha_zero).Exact := sorry

-- Proof sketch: this is the central exactness statement for the derived couple obtained from the
-- original exact couple by passing to the page-one homology.
/-- Exactness of the derived shifted exact couple at `A' ⟶ (TS) E'`. -/
private theorem derived_exact_tAlpha_g :
    (ShortComplex.mk X.derivedTAlpha X.derivedg
      X.derived_tAlpha_comp_derivedg_zero).Exact := sorry

-- Proof sketch: the image of the connecting morphism in the derived couple is the kernel of the
-- next `TS(f')`, as in the standard derived exact-couple construction.
/-- Exactness of the derived shifted exact couple at `(TS) E' ⟶ (TS) A'`. -/
private theorem derived_exact_g_TSf :
    (ShortComplex.mk X.derivedg ((S.trans T).functor.map X.derivedf)
      X.derivedg_comp_TSf_zero).Exact := sorry

/-- Remark 12.21.5 (Variant): the derived shifted exact couple attached to `X`. Its outer object
is the image of `T A ⟶ A`, its middle object is the homology of the page-one differential
`E ⟶ S E`, and its page shift is `T ∘ S`. -/
def derived : ShiftedExactCouple (S.trans T) T where
  A := X.derivedA
  E := X.derivedE
  tAlpha := X.derivedTAlpha
  f := X.derivedf
  g := X.derivedg
  Tf_comp_tAlpha := X.derived_Tf_comp_tAlpha_zero
  tAlpha_comp_g := X.derived_tAlpha_comp_derivedg_zero
  g_comp_Sf := X.derivedg_comp_TSf_zero
  exact_Tf_tAlpha := X.derived_exact_Tf_tAlpha
  exact_tAlpha_g := X.derived_exact_tAlpha_g
  exact_g_Sf := X.derived_exact_g_TSf

/-- The `n`-fold iterated derived shifted exact couple. The page-one differential of
`iterateDerived X n` is the source-facing differential on the page `E_{n+1}`. -/
def iterateDerived (X : ShiftedExactCouple S T) :
    (n : ℕ) →
      ShiftedExactCouple (pageShift S T ⟨n + 1, Nat.succ_pos _⟩) T
  | 0 => X
  | n + 1 => derived (iterateDerived X n)

/-- Remark 12.21.5 (Variant): a shifted exact couple yields a shifted spectral sequence whose
page shifts are `T^(r - 1) ∘ S`, whose first page is `E`, and whose second page is the homology
`Ker(d₁) / Im(S⁻¹ d₁)` of the induced page-one differential. -/
noncomputable def associatedSpectralSequence (X : ShiftedExactCouple S T) :
    ShiftedSpectralSequence (pageShift S T) :=
  { page := fun
      | ⟨n + 1, _⟩ => X.iterateDerived n
    iso := fun
      | ⟨n + 1, _⟩ => Iso.refl (X.iterateDerived (n + 1)).E }

/-- The textbook page `E_{r+1}` of the shifted spectral sequence associated to `X` is the
page-one shifted differential object carried by the `r`-fold derived shifted exact couple. -/
theorem associatedSpectralSequence_page (X : ShiftedExactCouple S T) (r : ℕ) :
    X.associatedSpectralSequence.page ⟨r + 1, Nat.succ_pos _⟩ = X.iterateDerived r :=
  rfl

/-- The textbook page object `E_{r+1}` of the shifted spectral sequence associated to `X` is the
middle object of the `r`-fold derived shifted exact couple. -/
theorem associatedSpectralSequence_pageObject (X : ShiftedExactCouple S T) (r : ℕ) :
    (X.associatedSpectralSequence.page ⟨r + 1, Nat.succ_pos _⟩).obj = (X.iterateDerived r).E :=
  rfl

/-- The textbook differential `d_{r+1}` of the shifted spectral sequence associated to `X` is the
page-one differential of the `r`-fold derived shifted exact couple. -/
theorem associatedSpectralSequence_differential (X : ShiftedExactCouple S T) (r : ℕ) :
    (X.associatedSpectralSequence.page ⟨r + 1, Nat.succ_pos _⟩).d = (X.iterateDerived r).d :=
  rfl

end ShiftedExactCouple

end

end CategoryTheory
