import StacksProject_2024.Chap19.Lemma_19_12_2
import StacksProject_2024.Chap13.«13_18_6_1»
import StacksProject_2024.Chap13.Definition_13_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open ComplexShape
open HomotopyCategory

universe v u

namespace CategoryTheory
namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Abelian C]

local notation "Cpx" => CochainComplex C ℤ
local notation "Q" => quotient C (up ℤ)
/- Domain-style sampling for Lemma 19.12.3:
- primary domain: K-injective cochain complexes in an abelian category, detected by vanishing of
  morphisms from acyclic complexes in the homotopy category and refined here using the small
  bounded-above acyclic generators supplied by the Chapter 19 owner predicate
  `MinusAcyclicSubobjectCardinalLE C κ`;
- sampled owner declarations:
  `CochainComplex.IsKInjective`,
  `CochainComplex.isKInjective_iff_rightOrthogonal`,
  `CochainComplex.isKInjective_iff_homotopyCategory_from_acyclic_eq_zero`,
  `CochainComplex.MinusAcyclicSubobjectCardinalLE`,
  `CochainComplex.SmallAcyclicSubcomplexBound`,
  `CochainComplex.minus`;
- best owner abstraction: the canonical owner is the target complex `I : Cpx` with property
  `I.IsKInjective`; the source-side smallness hypothesis is now expressed by the Chapter 19 owner
  predicate `SmallAcyclicSubcomplexBound C κ`, while the actual test objects are packaged by the
  Chapter 19 single-complex owner `MinusAcyclicSubobjectCardinalLE C κ`;
- primitive data: the cardinal `κ`, the owner predicates
  `MinusAcyclicSubobjectCardinalLE C κ` and `SmallAcyclicSubcomplexBound C κ`, the complex `I`,
  and the termwise injectivity hypothesis `∀ j, Injective (I.X j)`;
- derived API: the vanishing statement in the homotopy category for bounded-above acyclic
  `κ`-small complexes, which is a source-facing bridge to the canonical owner `I.IsKInjective`.

Source/core/bridge triage:
- `source-facing`: the Stacks-style reduction criterion saying it suffices to test vanishing on the
  bounded-above acyclic `κ`-small complexes encoded by
  `MinusAcyclicSubobjectCardinalLE C κ`;
- `core/canonical`: `CochainComplex.IsKInjective`;
- `bridge/view`: the homotopy-category vanishing condition
  `∀ f : (quotient C (up ℤ)).obj M ⟶ (quotient C (up ℤ)).obj I, f = 0` for the chosen source
  complexes.
-/

-- Proof sketch: use the nonzero bounded-above acyclic `κ`-small subcomplexes from the first
-- conclusion encoded by `SmallAcyclicSubcomplexBound C κ` inside any nonzero acyclic complex.
-- The termwise injectivity of `I` lets one descend along these subcomplexes and force vanishing
-- in the homotopy category, contradicting the existence of a nonzero morphism from an acyclic
-- source. The canonical owner theorem
-- `CochainComplex.isKInjective_iff_homotopyCategory_from_acyclic_eq_zero` then upgrades this
-- vanishing criterion to K-injectivity.
/-- Helper for Lemma 19.12.3: vanishing in the homotopy category for a `κ`-small bounded-above
acyclic complex upgrades to a chain-level null-homotopy. -/
lemma nullHomotopic_of_small_boundedAbove_acyclic_vanishing
    (κ : Cardinal)
    (I : Cpx)
    (hvanish :
      ∀ (M : Cpx) (_ : MinusAcyclicSubobjectCardinalLE C κ M)
        (f : (Q).obj M ⟶ (Q).obj I), f = 0)
    {M : Cpx} (hM : MinusAcyclicSubobjectCardinalLE C κ M) (α : M ⟶ I) :
    Nonempty (Homotopy α 0) := by
  -- Translate the homotopy-category vanishing hypothesis back to a chain-level null-homotopy.
  exact (HomotopyCategory.quotient_map_eq_zero_iff α).1 (hvanish M hM ((Q).map α))

/-- Helper for Lemma 19.12.3: a map between acyclic complexes is automatically a
quasi-isomorphism. -/
lemma quasiIso_of_acyclic_source_target
    {L M : Cpx} (f : L ⟶ M) (hL : L.Acyclic) (hM : M.Acyclic) :
    QuasiIso f := by
  -- Compare the homology map in each degree after identifying both homology objects with zero.
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hLZero : IsZero (L.homology n) := by
    -- Acyclicity rewrites the source homology object to zero.
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := L) (i := n)).1
      ((HomologicalComplex.acyclic_iff L).1 hL n)
  have hMZero : IsZero (M.homology n) := by
    -- The same zero-homology argument applies to the target.
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := M) (i := n)).1
      ((HomologicalComplex.acyclic_iff M).1 hM n)
  exact CategoryTheory.Limits.isIso_of_source_target_iso_zero
    ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map f)
    hLZero.isoZero hMZero.isoZero

/-- Helper for Lemma 19.12.3: the quotient of an acyclic complex by an acyclic subcomplex is
again acyclic. -/
lemma acyclicCokernelOfMonoBetweenAcyclic
    {L M : Cpx} (f : L ⟶ M) [Mono f] (hL : L.Acyclic) (hM : M.Acyclic) :
    (cokernel f).Acyclic := by
  -- First identify the inclusion as a quasi-isomorphism because both endpoints are acyclic.
  letI : QuasiIso f := quasiIso_of_acyclic_source_target (C := C) f hL hM
  have hmono : ∀ n : ℤ, Mono (f.f n) := by
    intro n
    -- Evaluation preserves monomorphisms, so each component of the inclusion is mono.
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map f)
    infer_instance
  -- Then apply the Chapter 13 cokernel-acyclicity bridge for termwise mono quasi-isomorphisms.
  exact cokernel_acyclic_of_termwiseMono_quasiIso (α := f) hmono

/-- Helper for Lemma 19.12.3: degree-`0` homology of the Hom complex computes morphisms in the
homotopy category. -/
noncomputable def homologyZeroToHomotopyCategoryAddEquiv
    (L I : Cpx) :
    (CochainComplex.HomComplex L I).homology (0 : ℤ) ≃+
      ((Q).obj L ⟶ (Q).obj I) :=
  (CochainComplex.HomComplex.homologyAddEquiv L I (0 : ℤ)).trans
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv

/-- Helper for Lemma 19.12.3: transport of morphisms across isomorphisms is additive in a
preadditive category. -/
private lemma iso_homCongr_map_add
    {D : Type*} [Category D] [Preadditive D] {X Y X₁ Y₁ : D} (α : X ≅ X₁) (β : Y ≅ Y₁)
    (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- Proof comment: `Iso.homCongr` is implemented by composing with the chosen isomorphisms.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 19.12.3: an isomorphism on source and target induces an additive
equivalence on the corresponding Hom groups. -/
private noncomputable def isoHomCongrAddEquiv
    {D : Type*} [Category D] [Preadditive D] {X Y X₁ Y₁ : D} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) where
  toEquiv := α.homCongr β
  map_add' := iso_homCongr_map_add α β

/-- Helper for Lemma 19.12.3: the shift-adjunction Hom equivalence is additive on Hom groups in
any preadditive shifted category. -/
private lemma shift_hom_equiv_symm_map_add
    {D : Type*} [Category D] [HasShift D ℤ] [Preadditive D]
    (n : ℤ) (L I : D) (f g : L ⟶ I⟦n⟧) :
    (((shiftEquiv D n).symm.toAdjunction.homEquiv L I).symm) (f + g) =
      (((shiftEquiv D n).symm.toAdjunction.homEquiv L I).symm) f +
        (((shiftEquiv D n).symm.toAdjunction.homEquiv L I).symm) g := by
  -- Proof comment: the adjunction Hom equivalence is additive because its formula is linear in
  -- the transported morphism.
  simp

/-- Helper for Lemma 19.12.3: homotopy morphisms into a shifted target identify additively with
homotopy morphisms from the oppositely shifted source. -/
private noncomputable def homotopyCategoryHomShiftTargetAddEquiv
    (L I : Cpx) (n : ℤ) :
    ((Q).obj L ⟶ (Q).obj (I⟦n⟧)) ≃+ ((Q).obj (L⟦-n⟧) ⟶ (Q).obj I) :=
  -- Proof comment: first commute the shift through the quotient functor, then move it from the
  -- target to the source via the shift adjunction, and finally commute the source shift back.
  (isoHomCongrAddEquiv (Iso.refl _) (((Q).commShiftIso n).app I)).trans <|
    (AddEquiv.ofEquiv
        (((shiftEquiv Q n).symm.toAdjunction.homEquiv ((Q).obj L) ((Q).obj I)).symm)
        (shift_hom_equiv_symm_map_add (D := Q) n ((Q).obj L) ((Q).obj I))).trans
      (isoHomCongrAddEquiv (((Q).commShiftIso (-n)).app L).symm (Iso.refl _))

/-- Helper for Lemma 19.12.3: isomorphic terms have equally large subobject lattices. -/
lemma subobjectCardinal_eq_of_iso
    {A B : C} (e : A ≅ B) :
    Cardinal.mk (Subobject A) = Cardinal.mk (Subobject B) := by
  -- Proof comment: the canonical order isomorphism on subobjects preserves cardinality.
  exact Cardinal.mk_congr (Subobject.mapIsoToOrderIso e).toEquiv

/-- Helper for Lemma 19.12.3: a monotone ordinal-indexed chain of subobjects stabilizes once the
cofinality of the index ordinal dominates the cardinality of the ambient subobject lattice. -/
lemma monotoneSubobjectSequenceEventuallyConstantOfCofGtSubobjectCardinal
    {X : C} (α : Ordinal.{max u v}) (hα : Cardinal.mk (Subobject X) < α.cof)
    (A : α.ToType → Subobject X) (hA : Monotone A) :
    ∃ a₀ : α.ToType, ∀ b : α.ToType, a₀ ≤ b → A b = A a₀ := by
  classical
  let J : Set α.ToType := { a | ∀ b : α.ToType, b < a → A b < A a }
  by_contra hEventual
  have hJ_cofinal : IsCofinal J := by
    -- Proof comment: if the jump indices were bounded, monotonicity would force a constant tail.
    intro a
    by_contra hnot
    push_neg at hnot
    have htail : ∀ b : α.ToType, a ≤ b → A b = A a := by
      intro b
      induction b using WellFoundedLT.induction with
      | ind b IH =>
          intro hab
          by_cases hbJ : b ∈ J
          · exact False.elim ((hnot b hbJ).not_ge hab)
          · have h_not_lt : ∃ c : α.ToType, c < b ∧ ¬ A c < A b := by
              simpa [J] using hbJ
            rcases h_not_lt with ⟨c, hcb, hAcb⟩
            have hcb_le : A c ≤ A b := hA hcb.le
            have hbc_le : A b ≤ A c := by
              by_contra hbc_le
              exact hAcb (lt_of_le_of_ne hcb_le fun hEq => hbc_le hEq.ge)
            have hEqcb : A c = A b := le_antisymm hcb_le hbc_le
            by_cases hac : a ≤ c
            · calc
                A b = A c := hEqcb.symm
                _ = A a := IH c hcb hac
            · have hca : c < a := lt_of_not_ge hac
              have hca_le : A c ≤ A a := hA hca.le
              have haa_le : A a ≤ A c := by
                simpa [hEqcb] using hA hab
              calc
                A b = A c := hEqcb.symm
                _ = A a := le_antisymm hca_le haa_le
    exact hEventual ⟨a, htail⟩
  have hJ_card : Cardinal.mk J ≤ Cardinal.mk (Subobject X) := by
    -- Proof comment: along the jump subsequence, the subobjects are strictly increasing.
    let f : J → Subobject X := fun j ↦ A j
    have hf : StrictMono f := by
      intro i j hij
      exact j.2 i hij
    exact Cardinal.mk_le_of_injective hf.injective
  have hcof_le : α.cof ≤ Cardinal.mk J := by
    -- Proof comment: any cofinal subset of `α.ToType` has cardinality at least `α.cof`.
    rw [← Ordinal.cof_toType α]
    exact Order.cof_le hJ_cofinal
  have hlt : Cardinal.mk J < α.cof := lt_of_le_of_lt hJ_card hα
  exact (not_lt_of_ge hcof_le) hlt

/-- Helper for Lemma 19.12.3: acyclicity is invariant under cochain shifts. -/
lemma acyclic_shift_of_acyclic
    {M : Cpx} (hM : M.Acyclic) (n : ℤ) :
    (M⟦n⟧).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let e :
      M.homology (i + n) ≅ (M⟦n⟧).homology i :=
    ((CochainComplex.ShiftSequence.shiftIso C n i (i + n) (add_comm n i)).app M).symm
  have hZero : IsZero (M.homology (i + n)) := by
    -- Proof comment: acyclicity identifies every source homology object with zero.
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := M) (i := i + n)).1
      ((HomologicalComplex.acyclic_iff M).1 hM (i + n))
  -- Proof comment: transport the zero homology object across the canonical shift comparison.
  exact hZero.of_iso e

/-- Helper for Lemma 19.12.3: shifting preserves the bounded-above acyclic `κ`-small owner
predicate. -/
lemma minusAcyclicSubobjectCardinalLE_shift
    (κ : Cardinal) {M : Cpx}
    (hM : MinusAcyclicSubobjectCardinalLE C κ M) (n : ℤ) :
    MinusAcyclicSubobjectCardinalLE C κ (M⟦n⟧) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: bounded-above support is stable under shifts.
    simpa using
      (CochainComplex.minus C).le_shift n M
        (MinusAcyclicSubobjectCardinalLE.minus (C := C) hM)
  · -- Proof comment: acyclicity is invariant under cochain shifts.
    exact acyclic_shift_of_acyclic (C := C)
      (MinusAcyclicSubobjectCardinalLE.acyclic (C := C) hM) n
  · intro i
    -- Proof comment: the shifted term in degree `i` is canonically isomorphic to the original
    -- term in degree `i + n`, so the subobject-cardinality bound transports across that iso.
    calc
      Cardinal.lift.{max u v + 1, max u v}
          (Cardinal.mk (Subobject ((M⟦n⟧).X i)))
          =
        Cardinal.lift.{max u v + 1, max u v}
          (Cardinal.mk (Subobject (M.X (i + n)))) := by
            rw [subobjectCardinal_eq_of_iso (C := C)
              (M.shiftFunctorObjXIso n i (i + n) rfl)]
      _ ≤ κ :=
        MinusAcyclicSubobjectCardinalLE.subobjectCardinalLE (C := C) hM (i + n)

/-- Helper for Lemma 19.12.3: vanishing on every `κ`-small bounded-above acyclic source forces
the full Hom complex from such a source into `I` to be acyclic. -/
lemma homComplexAcyclic_of_small_boundedAbove_acyclic_vanishing
    (κ : Cardinal)
    (I : Cpx)
    (hvanish :
      ∀ (L : Cpx) (_ : MinusAcyclicSubobjectCardinalLE C κ L)
        (f : (Q).obj L ⟶ (Q).obj I), f = 0)
    {L : Cpx} (hL : MinusAcyclicSubobjectCardinalLE C κ L) :
    (CochainComplex.HomComplex L I).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let e :
      AddCommGrpCat.of ((CochainComplex.HomComplex L I).homology n) ≅
        AddCommGrpCat.of (((Q).obj (L⟦-n⟧) ⟶ (Q).obj I)) :=
    ((CochainComplex.HomComplex.homologyAddEquiv L I n).trans
      (homotopyCategoryHomShiftTargetAddEquiv (C := C) L I n)).toAddCommGrpIso
  let hShift : MinusAcyclicSubobjectCardinalLE C κ (L⟦-n⟧) :=
    minusAcyclicSubobjectCardinalLE_shift (C := C) κ hL (-n)
  have hzero :
      IsZero (AddCommGrpCat.of (((Q).obj (L⟦-n⟧) ⟶ (Q).obj I))) := by
    -- Proof comment: the target Hom group is zero because every morphism from the shifted small
    -- source vanishes in the homotopy category.
    refine AddCommGrpCat.isZero_of_subsingleton _
    refine ⟨fun f g ↦ by rw [hvanish _ hShift f, hvanish _ hShift g]⟩
  -- Proof comment: transport the zero object statement back along the additive comparison.
  simpa using e.isZero_iff.2 hzero

/-- Helper for Lemma 19.12.3: precomposition on fixed-degree Hom-complex cochains is additive. -/
lemma homComplexPrecomp_map_add
    {L M I : Cpx} (f : L ⟶ M) (n : ℤ)
    (z z' : CochainComplex.HomComplex.Cochain M I n) :
    (CochainComplex.HomComplex.Cochain.ofHom f).comp (z + z') (zero_add n) =
      (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n) +
        (CochainComplex.HomComplex.Cochain.ofHom f).comp z' (zero_add n) := by
  -- Proof comment: precomposition is bilinear because composition in the Hom-complex is bilinear.
  ext p q hpq
  simp [Preadditive.comp_add]

/-- Helper for Lemma 19.12.3: precomposition with a cochain-complex morphism induces an additive
map on Hom-complex cochains of fixed degree. -/
noncomputable def homComplexPrecompAddMonoidHom
    {L M I : Cpx} (f : L ⟶ M) (n : ℤ) :
    CochainComplex.HomComplex.Cochain M I n →+
      CochainComplex.HomComplex.Cochain L I n where
  toFun := fun z ↦ (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n)
  map_zero' := by
    -- Proof comment: precomposition with the zero cochain is again zero.
    ext p q hpq
    simp
  map_add' := homComplexPrecomp_map_add f n

/-- Helper for Lemma 19.12.3: Hom-complex precomposition commutes with the Hom-complex
differential. -/
lemma homComplexPrecomp_comm
    {L M I : Cpx} (f : L ⟶ M) (i j : ℤ) (_hij : (ComplexShape.up ℤ).Rel i j) :
    AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) i) ≫
        (CochainComplex.HomComplex L I).d i j =
      (CochainComplex.HomComplex M I).d i j ≫
        AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) j) := by
  -- Proof comment: the Hom-complex differential is natural with respect to precomposition.
  ext z
  simpa using
    (CochainComplex.HomComplex.δ_comp_ofHom (f := f) (z := z) (m := j))

/-- Helper for Lemma 19.12.3: precomposition with a cochain-complex morphism induces a chain map
between Hom complexes. -/
noncomputable def homComplexPrecomp
    {L M I : Cpx} (f : L ⟶ M) :
    CochainComplex.HomComplex M I ⟶ CochainComplex.HomComplex L I where
  f n := AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) n)
  comm' := homComplexPrecomp_comm (f := f)

/-- Helper for Lemma 19.12.3: Hom-complex precomposition is functorial under composition of the
source map. -/
lemma homComplexPrecomp_comp
    {L M N I : Cpx} (f : L ⟶ M) (g : M ⟶ N) :
    homComplexPrecomp (f := f ≫ g) (I := I) =
      homComplexPrecomp (f := g) (I := I) ≫ homComplexPrecomp (f := f) (I := I) := by
  -- Proof comment: both sides are iterated precomposition by the same composite.
  ext n z
  rfl

/-- Helper for Lemma 19.12.3: precomposition by the identity is the identity on the Hom complex.
-/
lemma homComplexPrecomp_id
    {L I : Cpx} :
    homComplexPrecomp (f := 𝟙 L) (I := I) = 𝟙 (CochainComplex.HomComplex L I) := by
  -- Proof comment: precomposing with the identity leaves each cochain unchanged.
  ext n z
  rfl

/-- Helper for Lemma 19.12.3: precomposition on fixed-degree Hom-complex cochains is injective
when the source map is epic. -/
lemma homComplexPrecomp_injective_of_epi
    {L M I : Cpx} (f : L ⟶ M) [Epi f] (n : ℤ) :
    Function.Injective (homComplexPrecompAddMonoidHom (f := f) (I := I) n) := by
  intro z z' h
  -- Proof comment: degreewise, an epic source map can be cancelled on the left.
  ext p q hpq
  have hcomp := congrArg (fun t ↦ t p q hpq) h
  change f.f p ≫ z p q hpq = f.f p ≫ z' p q hpq at hcomp
  exact (cancel_epi (f.f p)).1 hcomp

/-- Helper for Lemma 19.12.3: precomposition on fixed-degree Hom-complex cochains is surjective
along a monomorphism into a termwise injective target. -/
lemma homComplexPrecomp_surjective_of_mono
    {L M I : Cpx} (f : L ⟶ M) [Mono f] (hI : ∀ j : ℤ, Injective (I.X j)) (n : ℤ) :
    Function.Surjective (homComplexPrecompAddMonoidHom (f := f) (I := I) n) := by
  intro z
  refine ⟨CochainComplex.HomComplex.Cochain.mk (fun p q hpq ↦ ?_), ?_⟩
  · -- Proof comment: extend each component across the monomorphism `f.f p` into the injective
    -- target term `I.X q`.
    letI : Mono (f.f p) := by
      change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).map f)
      infer_instance
    exact Injective.factorThru (z p q hpq) (f.f p)
  · -- Proof comment: the extensions were chosen so that composing back with `f` recovers `z`.
    ext p q hpq
    letI : Mono (f.f p) := by
      change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).map f)
      infer_instance
    simpa [homComplexPrecompAddMonoidHom] using
      (Injective.comp_factorThru (g := z p q hpq) (f := f.f p))

/-- Helper for Lemma 19.12.3: exactness of a short exact row of complexes induces exactness on
fixed-degree Hom-complex cochains against a termwise injective target. -/
lemma homComplexPrecomp_exact_of_shortExact
    (S : ShortComplex Cpx) (hS : S.ShortExact)
    (I : Cpx) (hI : ∀ j : ℤ, Injective (I.X j)) (n : ℤ) :
    Function.Exact
      (homComplexPrecompAddMonoidHom (f := S.g) (I := I) n)
      (homComplexPrecompAddMonoidHom (f := S.f) (I := I) n) := by
  intro x hx
  refine ⟨CochainComplex.HomComplex.Cochain.mk (fun p q hpq ↦ ?_), ?_⟩
  · -- Proof comment: for each source degree, exactness of the evaluated short exact row lets us
    -- descend the component of `x` across `S.g`.
    let Sp : ShortComplex C := S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) p)
    have hSp : Sp.ShortExact :=
      (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS p
    have hxpq : Sp.f ≫ x p q hpq = 0 := by
      have hcomp := congrArg (fun t ↦ t p q hpq) hx
      simpa [Sp, homComplexPrecompAddMonoidHom] using hcomp
    exact (hSp.exact.descToInjective (x p q hpq) hxpq)
  · -- Proof comment: the chosen descended cochain maps back to `x` by the defining property of
    -- `descToInjective`.
    ext p q hpq
    let Sp : ShortComplex C := S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) p)
    have hSp : Sp.ShortExact :=
      (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS p
    have hxpq : Sp.f ≫ x p q hpq = 0 := by
      have hcomp := congrArg (fun t ↦ t p q hpq) hx
      simpa [Sp, homComplexPrecompAddMonoidHom] using hcomp
    simpa [Sp, homComplexPrecompAddMonoidHom] using
      (hSp.exact.comp_descToInjective (f := x p q hpq) hxpq)

/-- Helper for Lemma 19.12.3: a short exact row of complexes induces a short exact row of Hom
complexes against a termwise injective target. -/
lemma homComplexShortExactOfTermwiseInjective
    (S : ShortComplex Cpx) (hS : S.ShortExact)
    (I : Cpx) (hI : ∀ j : ℤ, Injective (I.X j)) :
    ({ X₁ := CochainComplex.HomComplex S.X₃ I
       X₂ := CochainComplex.HomComplex S.X₂ I
       X₃ := CochainComplex.HomComplex S.X₁ I
       f := homComplexPrecomp (f := S.g) (I := I)
       g := homComplexPrecomp (f := S.f) (I := I)
       zero := by
         ext n z p q hpq
         simp [homComplexPrecomp, homComplexPrecompAddMonoidHom, S.zero] } :
      ShortComplex (CochainComplex AddCommGrpCat ℤ)).ShortExact := by
  let T : ShortComplex (CochainComplex AddCommGrpCat ℤ) :=
    { X₁ := CochainComplex.HomComplex S.X₃ I
      X₂ := CochainComplex.HomComplex S.X₂ I
      X₃ := CochainComplex.HomComplex S.X₁ I
      f := homComplexPrecomp (f := S.g) (I := I)
      g := homComplexPrecomp (f := S.f) (I := I)
      zero := by
        ext n z p q hpq
        simp [homComplexPrecomp, homComplexPrecompAddMonoidHom, S.zero] }
  refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
  intro n
  refine CategoryTheory.ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: exactness is the cochain-level exactness proved above.
    rw [CategoryTheory.ShortComplex.ab_exact_iff_function_exact]
    simpa [T] using
      homComplexPrecomp_exact_of_shortExact (S := S) hS I hI n
  · -- Proof comment: degreewise injectivity comes from cancelling the epic map `S.g`.
    refine CategoryTheory.ConcreteCategory.mono_of_injective _ ?_
    simpa [T] using
      homComplexPrecomp_injective_of_epi
        (f := (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).g) (I := AddCommGrpCat.of)
        0
  · -- Proof comment: degreewise surjectivity comes from extending across the monomorphism `S.f`
    -- into the injective target term.
    refine CategoryTheory.ConcreteCategory.epi_of_surjective _ ?_
    simpa [T] using
      homComplexPrecomp_surjective_of_mono
        (f := (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).f)
        (I := AddCommGrpCat.of) (fun j ↦ by infer_instance) 0

/-- Helper for Lemma 19.12.3: a proper acyclic subcomplex of an acyclic complex has a nonzero
`κ`-small bounded-above acyclic subcomplex in the quotient. -/
lemma existsSmallAcyclicSubcomplexInCokernel_of_proper
    (κ : Cardinal) (hκ_sub : SmallAcyclicSubcomplexBound C κ)
    {M : Cpx} (hM : M.Acyclic)
    (K : Subobject M) (hK : (K : Cpx).Acyclic) (hKne : K ≠ ⊤) :
    ∃ N : Subobject (cokernel K.arrow),
      ¬ IsZero (N : Cpx) ∧ MinusAcyclicSubobjectCardinalLE C κ (N : Cpx) := by
  -- Proof comment: the quotient is acyclic because it is the cokernel of a mono between acyclic
  -- complexes, and it is nonzero because a zero cokernel would force the inclusion to be iso.
  have hquotAcyclic : (cokernel K.arrow).Acyclic := by
    exact acyclicCokernelOfMonoBetweenAcyclic (C := C) (f := K.arrow) hK hM
  have hquotNonzero : ¬ IsZero (cokernel K.arrow) := by
    intro hzero
    letI : Epi K.arrow := epi_of_isZero_cokernel K.arrow hzero
    have hIso : IsIso K.arrow := isIso_of_mono_of_epi K.arrow
    exact hKne ((Subobject.isIso_arrow_iff_eq_top K).1 hIso)
  rcases hκ_sub (cokernel K.arrow) hquotAcyclic hquotNonzero with ⟨N, hNnonzero, hNsmall⟩
  exact ⟨N, hNnonzero, hNsmall⟩

/-- Helper for Lemma 19.12.3: the remaining source-faithful step is to promote vanishing on the
`κ`-small bounded-above acyclic test complexes to vanishing on every acyclic source complex. -/
lemma nullHomotopic_of_acyclic_of_small_boundedAbove_vanishing
    (κ : Cardinal)
    (hκ_sub : SmallAcyclicSubcomplexBound C κ)
    (I : Cpx) (hI : ∀ j : ℤ, Injective (I.X j))
    (hvanish :
      ∀ (M : Cpx) (_ : MinusAcyclicSubobjectCardinalLE C κ M)
        (f : (Q).obj M ⟶ (Q).obj I), f = 0)
    {M : Cpx} (hM : M.Acyclic) (α : M ⟶ I) :
    Nonempty (Homotopy α 0) := by
  -- Route correction: a single vanishing restriction `Q.map N.arrow ≫ Q.map α = 0` does not imply
  -- `Q.map α = 0`; the source proof needs a transfinite tower of acyclic subcomplexes.
  -- The quotient-acyclicity bridge is now available as
  -- `acyclicCokernelOfMonoBetweenAcyclic`, the successor-step small quotient extraction is now
  -- packaged by `existsSmallAcyclicSubcomplexInCokernel_of_proper`, and the Hom-complex transport
  -- is now packaged by
  -- `homotopyCategoryHomShiftTargetAddEquiv`, `homComplexAcyclic_of_small_boundedAbove_acyclic_vanishing`,
  -- and `homComplexPrecomp`.
  -- TODO: build the Stacks-style transfinite exhaustion of `M`, using
  -- `monotoneSubobjectSequenceEventuallyConstantOfCofGtSubobjectCardinal` for the stabilization
  -- step, then prove successor-step vanishing from the degree-`0` exactness row induced by
  -- `homComplexPrecomp`, prove the limit step via the inverse-limit description of
  -- `HomComplex(-, I)`, and finally force the tower to reach `⊤`.
  sorry

/-- Lemma 19.12.3: if `κ` satisfies the bounded-above acyclic small-subcomplex conclusion of
Lemma `19.12.2`, encoded by `SmallAcyclicSubcomplexBound C κ`, a cochain complex `I`
with injective terms is K-injective provided that every morphism in the homotopy category from a
`κ`-small bounded-above acyclic complex to `I` is zero. -/
theorem isKInjective_of_termwise_injective_of_small_boundedAbove_acyclic_vanishing
    (κ : Cardinal)
    (hκ_sub : SmallAcyclicSubcomplexBound C κ)
    (I : Cpx) (hI : ∀ j : ℤ, Injective (I.X j))
    (hvanish :
      ∀ (M : Cpx) (_ : MinusAcyclicSubobjectCardinalLE C κ M)
        (f : (Q).obj M ⟶ (Q).obj I), f = 0) :
    I.IsKInjective := by
  rw [CochainComplex.isKInjective_iff_homotopyCategory_from_acyclic_eq_zero]
  intro M hM f
  -- Work with a chain-map representative so the source proof can be executed at chain level.
  obtain ⟨α, rfl⟩ := (Q).map_surjective f
  -- The main theorem is now reduced to the transfinite null-homotopy statement for acyclic sources.
  exact (HomotopyCategory.quotient_map_eq_zero_iff α).2
    (nullHomotopic_of_acyclic_of_small_boundedAbove_vanishing
      (C := C) κ hκ_sub I hI hvanish hM α)

end

end CochainComplex
end CategoryTheory
