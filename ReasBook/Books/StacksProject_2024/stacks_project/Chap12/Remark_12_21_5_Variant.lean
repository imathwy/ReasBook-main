import Mathlib
import StacksProject_2024.stacks_project.Chap12.Remark_12_20_3_Variant

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

namespace ShortComplex

variable {F : C ⥤ C}
variable [F.PreservesZeroMorphisms]
variable {S : ShortComplex C} [HasHomology S] [HasHomology (S.map F)]
variable [F.PreservesLeftHomologyOf S]

/-- Helper for Remark 12.21.5 (Variant): the cycles comparison for the chosen left homology data
is the identity isomorphism. -/
private theorem leftHomologyData_cyclesIso_eq_refl :
    S.leftHomologyData.cyclesIso = Iso.refl _ := by
  ext
  -- Compare after the mono `iCycles`, where both sides become the chosen cycles inclusion.
  apply (cancel_mono S.iCycles).1
  calc
    S.leftHomologyData.cyclesIso.hom ≫ S.iCycles = S.iCycles := by
      simpa using S.leftHomologyData.cyclesIso_hom_comp_i
    _ = (Iso.refl S.cycles).hom ≫ S.iCycles := by
      simp

/-- Helper for Remark 12.21.5 (Variant): the homology descent is obtained from the chosen left
homology descent by precomposing with `leftHomologyIso.inv`. -/
private theorem descHomology_eq_leftHomologyIso_inv_comp_descH {A : C}
    (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) :
    S.descHomology k hk = S.leftHomologyIso.inv ≫ S.leftHomologyData.descH k hk := by
  -- Compare after `homologyπ`, where both morphisms evaluate to the same cycles representative.
  apply (cancel_epi S.homologyπ).1
  calc
    S.homologyπ ≫ S.descHomology k hk = k := by
      simp
    _ = S.leftHomologyπ ≫ S.leftHomologyData.descH k hk := by
      simpa [ShortComplex.leftHomologyπ] using
        (S.leftHomologyData.π_descH k hk).symm
    _ = S.homologyπ ≫ (S.leftHomologyIso.inv ≫ S.leftHomologyData.descH k hk) := by
      rw [S.homologyπ_comp_leftHomologyIso_inv]
      simp [Category.assoc]

/-- Helper for Remark 12.21.5 (Variant): mapping a homology descent through
`mapHomologyIso` agrees with the homology descent of the mapped cycles representative. -/
theorem mapHomologyIso_hom_comp_descHomology {A : C}
    (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0)
    (hk_map : (S.map F).toCycles ≫ ((S.mapCyclesIso F).hom ≫ F.map k) = 0) :
    (S.mapHomologyIso F).hom ≫ F.map (S.descHomology k hk) =
      (S.map F).descHomology ((S.mapCyclesIso F).hom ≫ F.map k) hk_map := by
  -- Route correction: rewrite `descHomology` through the chosen left homology presentation once,
  -- so the mapped comparison can be proved by canceling `homologyπ`.
  rw [S.descHomology_eq_leftHomologyIso_inv_comp_descH k hk, Functor.map_comp]
  rw [S.leftHomologyData.mapHomologyIso_eq (F := F),
    ShortComplex.LeftHomologyData.homologyIso_leftHomologyData (S := S)]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Functor.map_comp,
    Iso.hom_inv_id, id_comp]
  apply (cancel_epi (S.map F).homologyπ).1
  -- After precomposing by `homologyπ`, both sides are the same mapped cycles representative.
  calc
    (S.map F).homologyπ ≫
        (S.leftHomologyData.map F).homologyIso.hom ≫
          F.map (S.leftHomologyData.descH k hk) =
      (S.leftHomologyData.map F).cyclesIso.hom ≫ F.map k := by
        rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
        simp [Functor.map_comp]
    _ = (S.mapCyclesIso F).hom ≫ F.map k := by
        rw [S.leftHomologyData.mapCyclesIso_eq (F := F)]
        simp [S.leftHomologyData_cyclesIso_eq_refl]
    _ =
      (S.map F).homologyπ ≫
        (S.map F).descHomology ((S.mapCyclesIso F).hom ≫ F.map k) hk_map := by
          simp

end ShortComplex

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

/-- Helper for Remark 12.21.5 (Variant): the cycles-to-`A'` map induced by `f` agrees with
the ambient morphism `X.pageSc.iCycles ≫ X.f` after composing with the image inclusion. -/
private theorem derivedfCycles_comp_image_iota :
    X.derivedfCycles ≫ image.ι X.tAlpha = X.pageSc.iCycles ≫ X.f := by
  -- This is the defining computation rule for the lift through `image X.tAlpha`.
  simp only [derivedfCycles]
  erw [Fork.IsLimit.lift_ι]
  rfl

-- Proof sketch: a boundary in `cycles(d₁)` is represented by the previous differential
-- `S⁻¹E ⟶ E`; after composing with `f`, exactness identifies the result with zero in `A'`.
/-- The cycles-to-`A'` map induced by `f` vanishes on boundaries. -/
private theorem toCycles_comp_derivedfCycles_zero :
    X.pageSc.toCycles ≫ X.derivedfCycles = 0 := by
  -- Compare after the mono `image.ι X.tAlpha`; then the boundary computation reduces to
  -- the shifted previous differential followed by `f`, which vanishes by `g ≫ S(f) = 0`.
  apply (cancel_mono (image.ι X.tAlpha)).1
  rw [Category.assoc, X.derivedfCycles_comp_image_iota, ← Category.assoc, X.pageSc.toCycles_i]
  have hnat :
      X.pageSc.f ≫ X.f =
        S.functor.inv.map X.f ≫ shiftedPreviousDifferential S.functor
          (X.g ≫ S.functor.map X.f) := by
    have hcomm : X.f ≫ (X.g ≫ S.functor.map X.f) = X.d ≫ S.functor.map X.f := by
      simp [ShiftedExactCouple.d, Category.assoc]
    simpa [ShiftedExactCouple.pageSc, ShiftedExactCouple.page,
      ShiftedDifferentialObject.shortComplex, shiftedPageShortComplex, ShiftedExactCouple.d,
      Category.assoc] using
      (shiftedPreviousDifferential_naturality S.functor X.f hcomm).symm
  have hzero :
      S.functor.inv.map X.f ≫
          shiftedPreviousDifferential S.functor (X.g ≫ S.functor.map X.f) = 0 := by
    have hprev :
        shiftedPreviousDifferential S.functor (X.g ≫ S.functor.map X.f) = 0 := by
      simpa [shiftedPreviousDifferential] using
        congrArg (shiftedPreviousDifferential S.functor) X.g_comp_Sf
    simpa [hprev]
  simpa using hnat.trans hzero

/-- The map `f' : E' ⟶ A'` in the derived shifted exact couple. -/
private noncomputable abbrev derivedf : X.derivedE ⟶ X.derivedA :=
  X.pageSc.descHomology X.derivedfCycles X.toCycles_comp_derivedfCycles_zero

/-- The `(TS)`-shifted page-one short complex whose homology is `(TS)E'`. -/
private noncomputable abbrev derivedgPageSc : ShortComplex C :=
  (S.trans T).functor.mapShortComplex.obj X.pageSc

/-- Helper for Remark 12.21.5 (Variant): precomposing the mapped previous differential of a
shifted page-one short complex by the counit inverse recovers the original differential. -/
private theorem counitInv_comp_map_shiftedPageShortComplex_f
    {E : C} (d : E ⟶ S.functor.obj E) (hd : d ≫ S.functor.map d = 0) :
    S.functor.asEquivalence.counitInv.app E ≫
      S.functor.map ((shiftedPageShortComplex S.functor d hd).f) = d := by
  -- Route correction: normalize the transport at the shifted short-complex level once, so the
  -- later homology computation can use the standard boundary-to-zero lemma directly.
  have hmap :
      S.functor.map ((shiftedPageShortComplex S.functor d hd).f) =
        S.functor.map (S.functor.inv.map d) ≫
          S.functor.map (S.functor.asEquivalence.unitInv.app E) := by
    -- Unfold only the shifted previous differential and map the resulting composite.
    simp [shiftedPageShortComplex, shiftedPreviousDifferential, Functor.map_comp]
  have hpre := congrArg (fun m ↦ S.functor.asEquivalence.counitInv.app E ≫ m) hmap
  have hfun :=
      congrArg
        (fun m ↦ S.functor.asEquivalence.counitInv.app E ≫ m ≫
          S.functor.map (S.functor.asEquivalence.unitInv.app E))
        (S.functor.asEquivalence.fun_inv_map (X := E) (Y := S.functor.obj E) d)
  have htail :=
      congrArg
        (fun m ↦ S.functor.asEquivalence.counitInv.app E ≫
          S.functor.asEquivalence.counit.app E ≫ d ≫
            S.functor.asEquivalence.counitInv.app (S.functor.obj E) ≫ m)
        (S.functor.asEquivalence.counit_app_functor E).symm
  have hcancel_tail :=
      congrArg
        (fun m ↦ S.functor.asEquivalence.counitInv.app E ≫
          S.functor.asEquivalence.counit.app E ≫ d ≫ m)
        (S.functor.asEquivalence.counitIso.inv_hom_id_app (S.functor.obj E))
  have hhead :=
      congrArg (fun m ↦ m ≫ d) (S.functor.asEquivalence.counitIso.inv_hom_id_app E)
  have htriangle :
      S.functor.asEquivalence.counitInv.app E ≫
        (S.functor.map (S.functor.inv.map d) ≫
          S.functor.map (S.functor.asEquivalence.unitInv.app E)) = d := by
    -- Replace `S.map (S.inv.map d)` by the counit-normalized form and then collapse the two
    -- residual counit/unit composites.
    have hstep1 :
        S.functor.asEquivalence.counitInv.app E ≫
            (S.functor.map (S.functor.inv.map d) ≫
              S.functor.map (S.functor.asEquivalence.unitInv.app E)) =
          S.functor.asEquivalence.counitInv.app E ≫
            (S.functor.asEquivalence.counit.app E ≫ d ≫
              S.functor.asEquivalence.counitInv.app (S.functor.obj E)) ≫
                S.functor.map (S.functor.asEquivalence.unitInv.app E) := by
      simpa [Category.assoc] using hfun
    have hstep2a :
        S.functor.asEquivalence.counitInv.app E ≫
            (S.functor.asEquivalence.counit.app E ≫ d ≫
              S.functor.asEquivalence.counitInv.app (S.functor.obj E)) ≫
                S.functor.map (S.functor.asEquivalence.unitInv.app E) =
          S.functor.asEquivalence.counitInv.app E ≫
            S.functor.asEquivalence.counit.app E ≫
              d ≫ S.functor.asEquivalence.counitInv.app (S.functor.obj E) ≫
                S.functor.asEquivalence.counit.app (S.functor.obj E) := by
      simpa [Category.assoc] using htail
    have hstep2b :
        S.functor.asEquivalence.counitInv.app E ≫
            S.functor.asEquivalence.counit.app E ≫
              d ≫ S.functor.asEquivalence.counitInv.app (S.functor.obj E) ≫
                S.functor.asEquivalence.counit.app (S.functor.obj E) =
          S.functor.asEquivalence.counitInv.app E ≫
            S.functor.asEquivalence.counit.app E ≫ d := by
      simpa [Category.assoc] using hcancel_tail
    have hstep3 :
        S.functor.asEquivalence.counitInv.app E ≫
            S.functor.asEquivalence.counit.app E ≫ d = d := by
      simpa [Category.assoc] using hhead
    exact hstep1.trans (hstep2a.trans (hstep2b.trans hstep3))
  exact hpre.trans htriangle

-- Proof sketch: `g : A ⟶ SE` followed by `S(d₁)` is zero because
-- `d₁ = f ≫ g` and the exact-couple relation `g ≫ S(f) = 0` forces
-- `g ≫ S(f) ≫ S(g) = 0`; applying `T` preserves this vanishing.
/-- The map `T(g) : T A ⟶ TS(E)` lands in the cycles of the `(TS)`-shifted page-one complex. -/
private theorem derivedgFromTA_comp_d_zero :
    T.functor.map X.g ≫ X.derivedgPageSc.g = 0 := by
  -- After unfolding the mapped short complex, this is just `T.map` applied to
  -- the original relation `g ≫ S(f) = 0`, followed by `T.map` of the remaining `g`.
  simpa [ShiftedExactCouple.derivedgPageSc, ShiftedExactCouple.pageSc, ShiftedExactCouple.page,
    ShiftedDifferentialObject.shortComplex, shiftedPageShortComplex, ShiftedExactCouple.d,
    Category.assoc, Functor.map_comp] using
      congrArg (fun k ↦ T.functor.map k ≫ T.functor.map (S.functor.map X.g)) X.g_comp_Sf

/-- The map from `T A` to the cycles of the `(TS)`-shifted page-one complex induced by `g`. -/
private noncomputable def derivedgCycles :
    T.functor.obj X.A ⟶ X.derivedgPageSc.cycles :=
  X.derivedgPageSc.liftCycles (T.functor.map X.g) X.derivedgFromTA_comp_d_zero

/-- The homology-class map `T A ⟶ (TS)E'` induced by `T(g)`. -/
private noncomputable abbrev derivedgFromTA :
    T.functor.obj X.A ⟶ (S.trans T).functor.obj X.derivedE :=
  X.derivedgCycles ≫ X.derivedgPageSc.homologyπ ≫ (X.pageSc.mapHomologyIso (S.trans T).functor).hom

/-- Helper for Remark 12.21.5 (Variant): the first map of the mapped page-one short complex
becomes the original differential after precomposition by the translated counit inverse. -/
private theorem mapped_previous_differential_boundary :
    T.functor.map (S.functor.asEquivalence.counitInv.app X.E) ≫ X.derivedgPageSc.f =
      T.functor.map X.f ≫ T.functor.map X.g := by
  have hd : X.d ≫ S.functor.map X.d = 0 := by
    -- The page-one differential is exactly the shifted differential carried by `X`.
    simpa using ((X : ShiftedDifferentialObject S.functor).d_squared)
  have hmap :
      X.derivedgPageSc.f =
        T.functor.map (S.functor.map (shiftedPreviousDifferential S.functor X.d)) := by
    -- Unfold only the mapped short complex and its first differential.
    simp [ShiftedExactCouple.pageSc, ShiftedExactCouple.page, ShiftedDifferentialObject.shortComplex,
      shiftedPageShortComplex, ShiftedExactCouple.d, ShortComplex.map]
  -- Apply the generic shifted-page normalization and then transport it through `T`.
  have hstep1 :
      T.functor.map (S.functor.asEquivalence.counitInv.app X.E) ≫ X.derivedgPageSc.f =
        T.functor.map (S.functor.asEquivalence.counitInv.app X.E) ≫
          T.functor.map (S.functor.map (shiftedPreviousDifferential S.functor X.d)) := by
    exact congrArg (fun m ↦ T.functor.map (S.functor.asEquivalence.counitInv.app X.E) ≫ m) hmap
  have hstep2 :
      T.functor.map (S.functor.asEquivalence.counitInv.app X.E) ≫
          T.functor.map (S.functor.map (shiftedPreviousDifferential S.functor X.d)) =
        T.functor.map X.d := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ T.functor.map k)
        (counitInv_comp_map_shiftedPageShortComplex_f (S := S) (d := X.d) (hd := hd))
  have hstep3 : T.functor.map X.d = T.functor.map X.f ≫ T.functor.map X.g := by
    simp [ShiftedExactCouple.d, Functor.map_comp]
  exact hstep1.trans (hstep2.trans hstep3)

/-- Helper for Remark 12.21.5 (Variant): the representative `T(f) ≫ T(g)` is a cycle in the
mapped page-one short complex. -/
private theorem Tf_Tg_comp_derivedgPageSc_g_zero :
    (T.functor.map X.f ≫ T.functor.map X.g) ≫ X.derivedgPageSc.g = 0 := by
  -- The original cycle relation for `T(g)` remains valid after precomposition by `T(f)`.
  calc
    (T.functor.map X.f ≫ T.functor.map X.g) ≫ X.derivedgPageSc.g =
        T.functor.map X.f ≫ (T.functor.map X.g ≫ X.derivedgPageSc.g) := by
          simp [Category.assoc]
    _ = T.functor.map X.f ≫ 0 := by rw [X.derivedgFromTA_comp_d_zero]
    _ = 0 := by rw [comp_zero]

/-- Helper for Remark 12.21.5 (Variant): precomposing the cycle lift induced by `T(g)` with
`T(f)` gives the boundary cycle of the mapped page-one short complex. -/
private theorem Tf_comp_derivedgCycles_boundary :
    T.functor.map X.f ≫ X.derivedgCycles =
      X.derivedgPageSc.liftCycles (T.functor.map X.f ≫ T.functor.map X.g)
        X.Tf_Tg_comp_derivedgPageSc_g_zero := by
  -- This is the standard precomposition formula for `liftCycles`.
  simpa [ShiftedExactCouple.derivedgCycles] using
    (ShortComplex.comp_liftCycles (S := X.derivedgPageSc)
      (k := T.functor.map X.g) (hk := X.derivedgFromTA_comp_d_zero)
      (α := T.functor.map X.f))

/-- Helper for Remark 12.21.5 (Variant): the boundary representative `T(f) ≫ T(g)` is zero in
the homology of the mapped page-one short complex. -/
private theorem Tf_comp_derivedgCycles_homologyπ_zero :
    T.functor.map X.f ≫ X.derivedgCycles ≫ X.derivedgPageSc.homologyπ = 0 := by
  have hboundary :
      T.functor.map X.f ≫ T.functor.map X.g =
        T.functor.map (S.functor.asEquivalence.counitInv.app X.E) ≫ X.derivedgPageSc.f := by
    -- This is the normalized boundary statement from the previous helper, rewritten so that the
    -- boundary representative is exactly `T(f) ≫ T(g)`.
    simpa [ShiftedExactCouple.d, Functor.map_comp, Category.assoc] using
      X.mapped_previous_differential_boundary.symm
  -- A boundary class is zero in homology by the standard `ShortComplex` lemma.
  calc
    T.functor.map X.f ≫ X.derivedgCycles ≫ X.derivedgPageSc.homologyπ =
        X.derivedgPageSc.liftCycles (T.functor.map X.f ≫ T.functor.map X.g)
          X.Tf_Tg_comp_derivedgPageSc_g_zero ≫ X.derivedgPageSc.homologyπ := by
            rw [← Category.assoc, X.Tf_comp_derivedgCycles_boundary]
    _ = 0 := by
          simpa [Category.assoc] using
            (ShortComplex.liftCycles_homologyπ_eq_zero_of_boundary (S := X.derivedgPageSc)
              (k := T.functor.map X.f ≫ T.functor.map X.g)
              (x := T.functor.map (S.functor.asEquivalence.counitInv.app X.E)) hboundary)

/-- Helper for Remark 12.21.5 (Variant): postcomposing a zero morphism with the homology
comparison isomorphism remains zero. -/
private theorem zero_comp_mapHomologyIso_hom :
    (0 : T.functor.obj X.E ⟶ X.derivedgPageSc.homology) ≫
      (X.pageSc.mapHomologyIso (S.trans T).functor).hom = 0 := by
  -- This is the final transport normalization after the boundary class is shown to vanish.
  rw [zero_comp]

-- Proof sketch: on `T(E)`, the map `T(g)` represents the differential of the `(TS)`-shifted
-- page-one complex, hence its class in homology vanishes; exactness identifies `A'` as the
-- cokernel of `T(f)`.
/-- The homology-class map induced by `T(g)` vanishes on `T(f)`, so it descends to `A'`. -/
private theorem Tf_comp_derivedgFromTA_zero :
    T.functor.map X.f ≫ X.derivedgFromTA = 0 := by
  -- Expand `derivedgFromTA` once: the homology class already vanishes before the comparison
  -- isomorphism `mapHomologyIso`.
  calc
    T.functor.map X.f ≫ X.derivedgFromTA =
        (T.functor.map X.f ≫ X.derivedgCycles ≫ X.derivedgPageSc.homologyπ) ≫
          (X.pageSc.mapHomologyIso (S.trans T).functor).hom := by
            simp [ShiftedExactCouple.derivedgFromTA, Category.assoc]
    _ = (0 : T.functor.obj X.E ⟶ X.derivedgPageSc.homology) ≫
          (X.pageSc.mapHomologyIso (S.trans T).functor).hom := by
            rw [X.Tf_comp_derivedgCycles_homologyπ_zero]
    _ = 0 := by
            rw [X.zero_comp_mapHomologyIso_hom]

/-- The canonical connecting map in the derived shifted exact couple. -/
private noncomputable def derivedg : X.derivedA ⟶ (S.trans T).functor.obj X.derivedE :=
  let hImage := X.exact_Tf_tAlpha.isColimitImage
  hImage.desc (CokernelCofork.ofπ X.derivedgFromTA X.Tf_comp_derivedgFromTA_zero)

/-- Helper for Remark 12.21.5 (Variant): the derived translated outer map is represented on the
image inclusion by the original translated map `tAlpha`. -/
private theorem derivedTAlpha_comp_image_iota :
    X.derivedTAlpha ≫ image.ι X.tAlpha =
      T.functor.map (image.ι X.tAlpha) ≫ X.tAlpha := by
  -- Expand the image map once, then collapse the preserved-image transport on the image
  -- inclusion of `tAlpha`.
  have himage_map :
      image.map (Arrow.homMk' (T.functor.map X.tAlpha) X.tAlpha rfl) ≫ image.ι X.tAlpha =
        image.ι (T.functor.map X.tAlpha) ≫ X.tAlpha := by
    simpa using
      (image.map_ι (sq := Arrow.homMk' (T.functor.map X.tAlpha) X.tAlpha rfl))
  calc
    X.derivedTAlpha ≫ image.ι X.tAlpha =
        (PreservesImage.iso T.functor X.tAlpha).inv ≫
          image.ι (T.functor.map X.tAlpha) ≫ X.tAlpha := by
            simpa [ShiftedExactCouple.derivedTAlpha, Category.assoc] using
              congrArg (fun k ↦ (PreservesImage.iso T.functor X.tAlpha).inv ≫ k) himage_map
    _ = T.functor.map (image.ι X.tAlpha) ≫ X.tAlpha := by
          simpa [Category.assoc] using
            (CategoryTheory.PreservesImage.inv_comp_image_ι_map_assoc (L := T.functor)
              X.tAlpha X.tAlpha)

/-- Helper for Remark 12.21.5 (Variant): after composing with the image inclusion of `tAlpha`,
the derived `f`-map is still represented by the original map `f` on cycles. -/
private theorem homologyπ_comp_derivedf_comp_image_iota :
    X.pageSc.homologyπ ≫ X.derivedf ≫ image.ι X.tAlpha = X.pageSc.iCycles ≫ X.f := by
  -- First evaluate the homology descent map on `homologyπ`, then use the defining image
  -- factorization for `derivedfCycles`.
  calc
    X.pageSc.homologyπ ≫ X.derivedf ≫ image.ι X.tAlpha =
        X.derivedfCycles ≫ image.ι X.tAlpha := by
          simp [ShiftedExactCouple.derivedf]
    _ = X.pageSc.iCycles ≫ X.f := X.derivedfCycles_comp_image_iota

/-- Helper for Remark 12.21.5 (Variant): the mapped representative of the composite
`homologyπ ≫ derivedf ≫ image.ι tAlpha` already vanishes after postcomposition with `tAlpha`. -/
private theorem map_homologyπ_comp_derivedf_comp_image_iota_comp_tAlpha_zero :
    T.functor.map (X.pageSc.homologyπ ≫ X.derivedf ≫ image.ι X.tAlpha) ≫ X.tAlpha = 0 := by
  -- Replace the derived representative by the original cycle map `iCycles ≫ f`, then apply the
  -- original exact-couple vanishing `T(f) ≫ tAlpha = 0`.
  rw [X.homologyπ_comp_derivedf_comp_image_iota]
  simp [Functor.map_comp, Category.assoc, X.Tf_comp_tAlpha]

/-- Helper for Remark 12.21.5 (Variant): the three mapped factors occurring after the `homologyπ`
descent can be reassociated into a single `T.map` of the source-level composite. -/
private theorem map_homologyπ_derivedf_image_iota_normalization :
    T.functor.map X.pageSc.homologyπ ≫ T.functor.map X.derivedf ≫
        T.functor.map (image.ι X.tAlpha) =
      T.functor.map (X.pageSc.homologyπ ≫ X.derivedf ≫ image.ι X.tAlpha) := by
  -- This is the transport-stable functorial reassociation needed after canceling `T.map(homologyπ)`
  -- and `image.ι tAlpha` in the derived exact-couple proof.
  rw [← Category.assoc, ← Functor.map_comp]
  have hdesc : X.pageSc.homologyπ ≫ X.derivedf = X.derivedfCycles := by
    -- Evaluating the homology descent map on `homologyπ` recovers the underlying cycle morphism.
    simp [ShiftedExactCouple.derivedf]
  rw [hdesc, ← Functor.map_comp]
  congr 1
  -- The remaining composite is exactly the same source representative written in the original form.
  simp [ShiftedExactCouple.derivedf]

/-- Helper for Remark 12.21.5 (Variant): convert the inverse-form naturality square for
`mapHomologyIso` into the forward form `F.map (homologyMap φ) = ...` used by the derived
exact-couple transport arguments. -/
private theorem map_homologyMap_via_mapHomologyIso
    {F : C ⥤ C} [F.Additive]
    {S₁ S₂ : ShortComplex C}
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂]
    (φ : S₁ ⟶ S₂) :
    F.map (ShortComplex.homologyMap φ) =
      (S₁.mapHomologyIso F).inv ≫
        ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫
          (S₂.mapHomologyIso F).hom := by
  -- Rewrite the inverse-form naturality square from mathlib into the forward shape needed for
  -- mapped derived differentials.
  calc
    F.map (ShortComplex.homologyMap φ) =
        F.map (ShortComplex.homologyMap φ) ≫
          (S₂.mapHomologyIso F).inv ≫ (S₂.mapHomologyIso F).hom := by
            simp
    _ =
        (S₁.mapHomologyIso F).inv ≫
          ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫
            (S₂.mapHomologyIso F).hom := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫ (S₂.mapHomologyIso F).hom)
                  (ShortComplex.mapHomologyIso_inv_naturality (F := F) (φ := φ))

-- Proof sketch: `T(f')` is induced from `f` on the page-one homology and `α'` is adjoint to the
-- translated outer map on `A'`; the exactness of the original couple forces the composite to
-- vanish in the derived exact couple.
/-- In the derived shifted exact couple, the composite `T(f') ≫ Tα'` vanishes. -/
private theorem derived_Tf_comp_tAlpha_zero :
    T.functor.map X.derivedf ≫ X.derivedTAlpha = 0 := by
  -- Route correction: the earlier proof attempts stalled on a transport-heavy mapped composite.
  -- Cancel the source-faithful epi/mono pair first, then use the dedicated normalization lemma.
  apply (cancel_epi (T.functor.map X.pageSc.homologyπ)).1
  apply (cancel_mono (image.ι X.tAlpha)).1
  -- Compare the canceled composite directly with zero after rewriting the tail factor
  -- `derivedTAlpha ≫ image.ι _`.
  simpa [Category.assoc] using
    (show T.functor.map X.pageSc.homologyπ ≫
        T.functor.map X.derivedf ≫ X.derivedTAlpha ≫ image.ι X.tAlpha = 0 from by
      calc
        T.functor.map X.pageSc.homologyπ ≫
            T.functor.map X.derivedf ≫ X.derivedTAlpha ≫ image.ι X.tAlpha =
            T.functor.map X.pageSc.homologyπ ≫
              T.functor.map X.derivedf ≫ (X.derivedTAlpha ≫ image.ι X.tAlpha) := by
                simp [Category.assoc]
        _ = T.functor.map X.pageSc.homologyπ ≫
              T.functor.map X.derivedf ≫ (T.functor.map (image.ι X.tAlpha) ≫ X.tAlpha) := by
                rw [X.derivedTAlpha_comp_image_iota]
        _ = T.functor.map X.pageSc.homologyπ ≫
              T.functor.map X.derivedf ≫ T.functor.map (image.ι X.tAlpha) ≫ X.tAlpha := by
                simp
        _ = T.functor.map (X.pageSc.homologyπ ≫ X.derivedf ≫ image.ι X.tAlpha) ≫ X.tAlpha := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ X.tAlpha)
                  X.map_homologyπ_derivedf_image_iota_normalization
        _ = 0 := X.map_homologyπ_comp_derivedf_comp_image_iota_comp_tAlpha_zero)

/-- Helper for Remark 12.21.5 (Variant): the mapped original left differential still kills the
factor-through-image map of `T.map X.tAlpha`. -/
private theorem mapped_tAlpha_factorThruImage_zero :
    T.functor.map (T.functor.map X.f) ≫ factorThruImage (T.functor.map X.tAlpha) = 0 := by
  -- Compare after the mono `image.ι (T.map X.tAlpha)`, where the statement becomes the mapped
  -- original vanishing `T.map (T.map X.f ≫ X.tAlpha) = 0`.
  apply (cancel_mono (image.ι (T.functor.map X.tAlpha))).1
  -- After postcomposing with the image inclusion, `factorThruImage` collapses to the underlying
  -- morphism `T.map X.tAlpha`.
  simpa [Category.assoc, Functor.map_comp] using
    congrArg (fun k ↦ T.functor.map k) X.Tf_comp_tAlpha

/-- Helper for Remark 12.21.5 (Variant): mapping the original exact row
`T(E) ⟶ T(A) ⟶ A` by `T` gives the canonical cokernel owner for
`factorThruImage (T.map X.tAlpha)`. -/
private theorem mapped_tAlpha_isColimitImage :
    Nonempty
      (IsColimit
        (CokernelCofork.ofπ (factorThruImage (T.functor.map X.tAlpha))
          X.mapped_tAlpha_factorThruImage_zero)) := by
  -- The source proof route first maps the original exact row by `T`; the mapped exactness owner
  -- then identifies the image of `T.map X.tAlpha` as the cokernel of `T.map (T.map X.f)`.
  let S : ShortComplex C :=
    (ShortComplex.mk (T.functor.map X.f) X.tAlpha X.Tf_comp_tAlpha).map T.functor
  have hExact : S.Exact := by
    simpa [S] using X.exact_Tf_tAlpha.map T.functor
  -- Unfold the mapped short complex only at the end so the owner has the transport-stable shape
  -- needed for the later derived cokernel comparison.
  exact ⟨by
    simpa [S, ShortComplex.map, Functor.map_comp, Category.assoc,
      X.mapped_tAlpha_factorThruImage_zero] using hExact.isColimitImage⟩

/-- Helper for Remark 12.21.5 (Variant): after precomposing the derived translated outer map by
`T.map (factorThruImage X.tAlpha)`, the preserved-image transport collapses to the mapped source
factorization `T.map X.tAlpha ≫ factorThruImage X.tAlpha`. -/
private theorem map_factorThruImage_comp_derivedTAlpha :
    T.functor.map (factorThruImage X.tAlpha) ≫ X.derivedTAlpha =
      T.functor.map X.tAlpha ≫ factorThruImage X.tAlpha := by
  -- Rewrite the mapped factor-through-image map through the preserved-image isomorphism, and then
  -- use the standard image-map factorization for the square `T(tAlpha)`.
  have htransport :
      T.functor.map (factorThruImage X.tAlpha) ≫ (PreservesImage.iso T.functor X.tAlpha).inv =
        factorThruImage (T.functor.map X.tAlpha) := by
    apply (cancel_mono (image.ι (T.functor.map X.tAlpha))).1
    calc
      (T.functor.map (factorThruImage X.tAlpha) ≫
          (PreservesImage.iso T.functor X.tAlpha).inv) ≫
            image.ι (T.functor.map X.tAlpha) =
        T.functor.map (factorThruImage X.tAlpha) ≫ T.functor.map (image.ι X.tAlpha) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ T.functor.map (factorThruImage X.tAlpha) ≫ k)
              (PreservesImage.inv_comp_image_ι_map (L := T.functor) (f := X.tAlpha))
      _ = T.functor.map X.tAlpha := by
          rw [← Functor.map_comp, image.fac]
      _ = factorThruImage (T.functor.map X.tAlpha) ≫ image.ι (T.functor.map X.tAlpha) := by
          rw [image.fac]
  rw [ShiftedExactCouple.derivedTAlpha, ← Category.assoc, htransport]
  simpa [Category.assoc] using
    (image.factor_map (sq := Arrow.homMk' (T.functor.map X.tAlpha) X.tAlpha rfl))

/-- Helper for Remark 12.21.5 (Variant): the descended map `derivedg` is represented on `A` by
the source-level homology class map `derivedgFromTA`. -/
private theorem factorThruImage_comp_derivedg :
    factorThruImage X.tAlpha ≫ X.derivedg = X.derivedgFromTA := by
  -- This is the defining computation rule for the cokernel descent used to define `derivedg`.
  simpa [ShiftedExactCouple.derivedg] using
    (Cofork.IsColimit.π_desc
      (t := CokernelCofork.ofπ X.derivedgFromTA X.Tf_comp_derivedgFromTA_zero)
      X.exact_Tf_tAlpha.isColimitImage)

/-- Helper for Remark 12.21.5 (Variant): the cycle lift defining `derivedgFromTA` is already
killed by the mapped translated outer map `T.map X.tAlpha`. -/
private theorem mapped_tAlpha_comp_derivedgCycles_zero :
    T.functor.map X.tAlpha ≫ X.derivedgCycles = 0 := by
  -- Compare after the mono of cycles: the statement becomes the mapped vanishing
  -- `T.map (X.tAlpha ≫ X.g) = 0`.
  apply (cancel_mono X.derivedgPageSc.iCycles).1
  rw [zero_comp]
  calc
    (T.functor.map X.tAlpha ≫ X.derivedgCycles) ≫ X.derivedgPageSc.iCycles =
        T.functor.map X.tAlpha ≫ T.functor.map X.g := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ T.functor.map X.tAlpha ≫ k)
              (ShortComplex.liftCycles_i (S := X.derivedgPageSc)
                (k := T.functor.map X.g) (hk := X.derivedgFromTA_comp_d_zero))
    _ = 0 := by
          simpa [Functor.map_comp, Category.assoc] using
            congrArg (fun k ↦ T.functor.map k) X.tAlpha_comp_g

/-- Helper for Remark 12.21.5 (Variant): the source-level representative of `derivedg` vanishes
after precomposition by `T.map X.tAlpha`. -/
private theorem mapped_tAlpha_comp_derivedgFromTA_zero :
    T.functor.map X.tAlpha ≫ X.derivedgFromTA = 0 := by
  -- Once the cycle lift is zero, the induced homology class is zero as well.
  calc
    T.functor.map X.tAlpha ≫ X.derivedgFromTA =
        (T.functor.map X.tAlpha ≫ X.derivedgCycles) ≫ X.derivedgPageSc.homologyπ ≫
          (X.pageSc.mapHomologyIso (S.trans T).functor).hom := by
            simp [ShiftedExactCouple.derivedgFromTA, Category.assoc]
    _ = 0 ≫ X.derivedgPageSc.homologyπ ≫
          (X.pageSc.mapHomologyIso (S.trans T).functor).hom := by
            rw [X.mapped_tAlpha_comp_derivedgCycles_zero]
    _ = 0 := by simp only [zero_comp]

-- Proof sketch: the derived `α'` and `g'` encode the next translated connecting morphism, whose
-- composite vanishes by construction of the derived exact couple.
/-- In the derived shifted exact couple, the composite `T A' ⟶ A' ⟶ (TS) E'` vanishes. -/
private theorem derived_tAlpha_comp_derivedg_zero :
    X.derivedTAlpha ≫ X.derivedg = 0 := by
  -- Route correction: precompose by `T.map (factorThruImage X.tAlpha)` so the derived image
  -- transport is replaced by the source-level composite `T.map X.tAlpha ≫ derivedgFromTA`.
  apply (cancel_epi (T.functor.map (factorThruImage X.tAlpha))).1
  calc
    T.functor.map (factorThruImage X.tAlpha) ≫ X.derivedTAlpha ≫ X.derivedg =
        (T.functor.map (factorThruImage X.tAlpha) ≫ X.derivedTAlpha) ≫ X.derivedg := by
          simp [Category.assoc]
    _ = (T.functor.map X.tAlpha ≫ factorThruImage X.tAlpha) ≫ X.derivedg := by
          rw [X.map_factorThruImage_comp_derivedTAlpha]
    _ = T.functor.map X.tAlpha ≫ (factorThruImage X.tAlpha ≫ X.derivedg) := by
          simp [Category.assoc]
    _ = T.functor.map X.tAlpha ≫ X.derivedgFromTA := by
          rw [X.factorThruImage_comp_derivedg]
    _ = 0 := X.mapped_tAlpha_comp_derivedgFromTA_zero
    _ = T.functor.map (factorThruImage X.tAlpha) ≫ 0 := by
          symm
          exact comp_zero

-- Proof sketch: `g'` lands in the next page and `f'` is induced from boundaries, so the
-- resulting composite is zero in the derived exact couple.
/-- Helper for Remark 12.21.5 (Variant): the mapped cycles map induced by `derivedfCycles`
is transported through the canonical cycles isomorphism of the mapped page-one short complex. -/
private noncomputable abbrev mappedDerivedfCycles :
    X.derivedgPageSc.cycles ⟶ (S.trans T).functor.obj X.derivedA :=
  (X.pageSc.mapCyclesIso (S.trans T).functor).hom ≫ (S.trans T).functor.map X.derivedfCycles

/-- Helper for Remark 12.21.5 (Variant): the mapped cycles representative of `derivedf`
vanishes on the mapped boundaries of the page-one short complex. -/
private theorem mapped_toCycles_comp_mapped_derivedfCycles_zero :
    X.derivedgPageSc.toCycles ≫ X.mappedDerivedfCycles = 0 := by
  -- Mapping the boundary-to-cycles vanishing for `derivedfCycles` gives the corresponding
  -- vanishing on the mapped page-one short complex.
  have htoCycles :
      X.derivedgPageSc.toCycles ≫ (X.pageSc.mapCyclesIso (S.trans T).functor).hom =
        (S.trans T).functor.map X.pageSc.toCycles := by
    apply (cancel_mono ((S.trans T).functor.map X.pageSc.iCycles)).1
    have hleft :
        (X.derivedgPageSc.toCycles ≫ (X.pageSc.mapCyclesIso (S.trans T).functor).hom) ≫
            (S.trans T).functor.map X.pageSc.iCycles =
          X.derivedgPageSc.toCycles ≫ X.derivedgPageSc.iCycles := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ X.derivedgPageSc.toCycles ≫ k)
          (X.pageSc.mapCyclesIso_hom_iCycles (F := (S.trans T).functor))
    have hmid :
        X.derivedgPageSc.toCycles ≫ X.derivedgPageSc.iCycles =
          (S.trans T).functor.map X.pageSc.f := by
      simpa [ShiftedExactCouple.derivedgPageSc, ShortComplex.map] using
        (ShortComplex.toCycles_i (S := X.derivedgPageSc))
    have hright :
        (S.trans T).functor.map X.pageSc.f =
          ((S.trans T).functor.map X.pageSc.toCycles) ≫
            (S.trans T).functor.map X.pageSc.iCycles := by
      rw [← Functor.map_comp, ShortComplex.toCycles_i]
    exact hleft.trans (hmid.trans hright)
  apply (cancel_mono ((S.trans T).functor.map (image.ι X.tAlpha))).1
  rw [zero_comp]
  calc
    (X.derivedgPageSc.toCycles ≫ X.mappedDerivedfCycles) ≫
        (S.trans T).functor.map (image.ι X.tAlpha) =
      (X.derivedgPageSc.toCycles ≫ (X.pageSc.mapCyclesIso (S.trans T).functor).hom) ≫
        (S.trans T).functor.map (X.derivedfCycles ≫ image.ι X.tAlpha) := by
          simp [ShiftedExactCouple.mappedDerivedfCycles, Functor.map_comp, Category.assoc]
    _ = ((S.trans T).functor.map X.pageSc.toCycles) ≫
        (S.trans T).functor.map (X.derivedfCycles ≫ image.ι X.tAlpha) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ (S.trans T).functor.map (X.derivedfCycles ≫ image.ι X.tAlpha))
              htoCycles
    _ = 0 := by
          have hz : X.pageSc.toCycles ≫ X.derivedfCycles ≫ image.ι X.tAlpha = 0 := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ image.ι X.tAlpha) X.toCycles_comp_derivedfCycles_zero
          simpa [Functor.map_comp, Category.assoc] using
            congrArg (fun k ↦ (S.trans T).functor.map k) hz

/-- Helper for Remark 12.21.5 (Variant): under the homology comparison isomorphism, the mapped
homology descent defining `derivedf` is represented by `mappedDerivedfCycles`. -/
private theorem mapHomologyIso_hom_comp_mapped_derivedf :
    (X.pageSc.mapHomologyIso (S.trans T).functor).hom ≫ (S.trans T).functor.map X.derivedf =
      X.derivedgPageSc.descHomology X.mappedDerivedfCycles
        X.mapped_toCycles_comp_mapped_derivedfCycles_zero := by
  -- Specialize the abstract `ShortComplex` compatibility to the page-one short complex of `X`.
  simpa [ShiftedExactCouple.derivedf, ShiftedExactCouple.mappedDerivedfCycles] using
    (ShortComplex.mapHomologyIso_hom_comp_descHomology
      (S := X.pageSc) (F := (S.trans T).functor) X.derivedfCycles
      X.toCycles_comp_derivedfCycles_zero
      X.mapped_toCycles_comp_mapped_derivedfCycles_zero)

/-- Helper for Remark 12.21.5 (Variant): the source-level representative of the derived
connecting map is killed by the mapped derived `f`-map. -/
private theorem derivedgFromTA_comp_mapped_derivedf_zero :
    X.derivedgFromTA ≫ (S.trans T).functor.map X.derivedf = 0 := by
  -- Rewrite the mapped homology descent on the source page, then compare after the mapped image
  -- inclusion of `tAlpha`, where the composite becomes `T.map (g ≫ S.map f)`.
  apply (cancel_mono ((S.trans T).functor.map (image.ι X.tAlpha))).1
  rw [zero_comp]
  have hcycles :
      X.derivedgCycles ≫ (X.pageSc.mapCyclesIso (S.trans T).functor).hom ≫
          (S.trans T).functor.map X.pageSc.iCycles = T.functor.map X.g := by
    have hmap :
        X.derivedgCycles ≫ (X.pageSc.mapCyclesIso (S.trans T).functor).hom ≫
            (S.trans T).functor.map X.pageSc.iCycles =
          X.derivedgCycles ≫ X.derivedgPageSc.iCycles := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ X.derivedgCycles ≫ k)
          (X.pageSc.mapCyclesIso_hom_iCycles (F := (S.trans T).functor))
    have hlift :
        X.derivedgCycles ≫ X.derivedgPageSc.iCycles = T.functor.map X.g := by
      simpa [ShiftedExactCouple.derivedgCycles] using
        (ShortComplex.liftCycles_i (S := X.derivedgPageSc)
          (k := T.functor.map X.g) (hk := X.derivedgFromTA_comp_d_zero))
    exact hmap.trans hlift
  calc
    (X.derivedgFromTA ≫ (S.trans T).functor.map X.derivedf) ≫
        (S.trans T).functor.map (image.ι X.tAlpha) =
      X.derivedgCycles ≫ X.derivedgPageSc.homologyπ ≫
          ((X.pageSc.mapHomologyIso (S.trans T).functor).hom ≫
            (S.trans T).functor.map X.derivedf) ≫
              (S.trans T).functor.map (image.ι X.tAlpha) := by
                simp [ShiftedExactCouple.derivedgFromTA, Category.assoc]
    _ =
      X.derivedgCycles ≫ X.derivedgPageSc.homologyπ ≫
          X.derivedgPageSc.descHomology X.mappedDerivedfCycles
            X.mapped_toCycles_comp_mapped_derivedfCycles_zero ≫
              (S.trans T).functor.map (image.ι X.tAlpha) := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k ↦ X.derivedgCycles ≫ X.derivedgPageSc.homologyπ ≫ k ≫
                      (S.trans T).functor.map (image.ι X.tAlpha))
                    X.mapHomologyIso_hom_comp_mapped_derivedf
    _ =
      X.derivedgCycles ≫ X.mappedDerivedfCycles ≫
        (S.trans T).functor.map (image.ι X.tAlpha) := by
          simp
    _ =
      X.derivedgCycles ≫ (X.pageSc.mapCyclesIso (S.trans T).functor).hom ≫
        (S.trans T).functor.map (X.derivedfCycles ≫ image.ι X.tAlpha) := by
          simp [ShiftedExactCouple.mappedDerivedfCycles, Functor.map_comp, Category.assoc]
    _ = X.derivedgCycles ≫ (X.pageSc.mapCyclesIso (S.trans T).functor).hom ≫
          (S.trans T).functor.map (X.pageSc.iCycles ≫ X.f) := by
          rw [X.derivedfCycles_comp_image_iota]
    _ = (X.derivedgCycles ≫ (X.pageSc.mapCyclesIso (S.trans T).functor).hom ≫
          (S.trans T).functor.map X.pageSc.iCycles) ≫ (S.trans T).functor.map X.f := by
          simp [Functor.map_comp, Category.assoc]
    _ = T.functor.map X.g ≫ (S.trans T).functor.map X.f := by
          rw [hcycles]
          rfl
    _ = 0 := by
          simpa [Functor.map_comp, Category.assoc] using
            congrArg (fun k ↦ T.functor.map k) X.g_comp_Sf

/-- In the derived shifted exact couple, the composite `g' ≫ TS(f')` vanishes. -/
private theorem derivedg_comp_TSf_zero :
    X.derivedg ≫ (S.trans T).functor.map X.derivedf = 0 := by
  -- Route correction: descend to the source-level representative on `A` first, so the
  -- remaining work is only the homology-to-cycles normalization from the current plan.
  apply (cancel_epi (factorThruImage X.tAlpha)).1
  calc
    factorThruImage X.tAlpha ≫ X.derivedg ≫ (S.trans T).functor.map X.derivedf =
        (factorThruImage X.tAlpha ≫ X.derivedg) ≫ (S.trans T).functor.map X.derivedf := by
          simp [Category.assoc]
    _ = X.derivedgFromTA ≫ (S.trans T).functor.map X.derivedf := by
          rw [X.factorThruImage_comp_derivedg]
    _ = 0 := X.derivedgFromTA_comp_mapped_derivedf_zero
    _ = factorThruImage X.tAlpha ≫ 0 := by
          symm
          exact comp_zero

-- Proof sketch: identify `A'` with the image of `T A ⟶ A` and use the original exactness after
-- passage to the derived page-one homology.
/-- Helper for Remark 12.21.5 (Variant): the derived translated outer map is a cokernel of the
mapped derived `f`-map. -/
private noncomputable def derivedTAlpha_isColimitCokernel :
    IsColimit (CokernelCofork.ofπ X.derivedTAlpha X.derived_Tf_comp_tAlpha_zero) := sorry

/-- Exactness of the derived shifted exact couple at `T A' ⟶ A'`. -/
private theorem derived_exact_Tf_tAlpha :
    (ShortComplex.mk (T.functor.map X.derivedf) X.derivedTAlpha
      X.derived_Tf_comp_tAlpha_zero).Exact := by
  -- Once the cokernel owner is available, exactness is immediate.
  exact ShortComplex.exact_of_g_is_cokernel _ X.derivedTAlpha_isColimitCokernel

-- Proof sketch: this is the central exactness statement for the derived couple obtained from the
-- original exact couple by passing to the page-one homology.
/-- Helper for Remark 12.21.5 (Variant): the derived connecting map is a cokernel of the derived
translated outer map. -/
private noncomputable def derivedg_isColimitCokernel :
    IsColimit (CokernelCofork.ofπ X.derivedg X.derived_tAlpha_comp_derivedg_zero) := sorry

/-- Exactness of the derived shifted exact couple at `A' ⟶ (TS) E'`. -/
private theorem derived_exact_tAlpha_g :
    (ShortComplex.mk X.derivedTAlpha X.derivedg
      X.derived_tAlpha_comp_derivedg_zero).Exact := by
  -- This exactness statement is the cokernel owner for the derived connecting morphism.
  exact ShortComplex.exact_of_g_is_cokernel _ X.derivedg_isColimitCokernel

-- Proof sketch: the image of the connecting morphism in the derived couple is the kernel of the
-- next `TS(f')`, as in the standard derived exact-couple construction.
/-- Helper for Remark 12.21.5 (Variant): the derived connecting map is a kernel of the mapped
derived `f`-map on the next page. -/
private noncomputable def derivedg_isLimitKernel :
    IsLimit (KernelFork.ofι X.derivedg X.derivedg_comp_TSf_zero) := sorry

/-- Exactness of the derived shifted exact couple at `(TS) E' ⟶ (TS) A'`. -/
private theorem derived_exact_g_TSf :
    (ShortComplex.mk X.derivedg ((S.trans T).functor.map X.derivedf)
      X.derivedg_comp_TSf_zero).Exact := by
  -- The final exactness statement is the kernel owner for the next-page differential.
  exact ShortComplex.exact_of_f_is_kernel _ X.derivedg_isLimitKernel

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
