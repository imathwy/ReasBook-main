import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_11_1 (from Chap13) -/
open CategoryTheory ComplexShape

universe v u

variable (A : Type u) [Category.{v} A] [Abelian A]

local notation "H" => HomotopyCategory.homologyFunctor A (up ℤ)

/- Domain-style sampling for Lemma 13.11.1:
- primary domain: homological functors on the homotopy category of cochain complexes in an
  abelian category;
- sampled owner declarations:
  `Functor.IsHomological`,
  `Functor.IsHomological.mk'`,
  `Functor.map_distinguished_exact`,
  `HomotopyCategory.homologyFunctor`,
  the canonical instance
    `(homologyFunctor C (ComplexShape.up ℤ) n).IsHomological`;
- best owner abstraction: the canonical functor `H 0` together with its
  `Functor.IsHomological` instance;
- source/core/bridge triage:
  `source-facing`: the degree-zero homology functor `H^0 : K(\mathcal A) ⥤ \mathcal A`;
  `core/canonical`: `Functor.IsHomological`;
  `bridge/view`: none, because the source statement is already the canonical owner instance.

Primitive data are only the ambient abelian category and the homology functor. Homologicality is
derived API supplied upstream, so this file should use the existing owner declarations directly
rather than introduce a one-off local alias or parallel theorem.
-/

/- Companion recall: the degree-`n` homology functor on the homotopy category is the canonical
owner `HomotopyCategory.homologyFunctor`. -/
recall HomotopyCategory.homologyFunctor

/- Lemma 13.11.1: for an abelian category `\mathcal A`, the degree-zero homology functor
`H^0 : K(\mathcal A) ⥤ \mathcal A` is homological. This is the canonical instance on `H 0`. -/
#check (inferInstance : (H 0).IsHomological)

/-! ### Lemma_13_11_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe w v u

variable (A : Type u) [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 13.11.2:
- primary domain: Verdier localization of triangulated categories, specialized to the homotopy
  category of cochain complexes and the homological kernel of `H^0`;
- sampled owner declarations:
  `HomotopyCategory.subcategoryAcyclic`,
  `HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W`,
  `Functor.homologicalKernel`,
  `CategoryTheory.kernel_triangulatedLocalization_eq_retractClosure`,
  `ObjectProperty.retractClosure_eq_self`,
  `Localization.equivalenceFromModel`,
  `Localization.compEquivalenceFromModelInverseIso`,
  `Localization.qCompEquivalenceFromModelFunctorIso`;
- `source-facing`: the bridge statement identifying the kernel of `DerivedCategory.Qh` with the
  acyclic subcategory;
- `core/canonical`: the homological-kernel owner `HomotopyCategory.subcategoryAcyclic A` and the
  retract-closure fixed-point API for its Verdier quotient kernel, together with the localization
  equivalence owner attached to `DerivedCategory.Qh.IsLocalization`;
- `bridge/view`: transport the canonical kernel statement from the constructed localization
  `(subcategoryAcyclic A).trW.Q` to the chosen derived-category localization `DerivedCategory.Qh`
  using `Localization.equivalenceFromModel`.

Primitive data are only the acyclic object property and the chosen localization functor.
Retract-stability is derived API from the generic homological-kernel owner and should not remain a
parallel local instance.
-/

/- Lemma 13.11.2: in the homotopy category `K(\mathcal A)` of cochain complexes in an abelian
category `\mathcal A`, the saturated multiplicative system attached to the strictly full
triangulated subcategory of acyclic complexes is exactly the class of quasi-isomorphisms. -/
recall HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W

/- Companion recall: the acyclic complexes form a triangulated subcategory of
`K(\mathcal A)`. -/
#check (inferInstance :
  (HomotopyCategory.subcategoryAcyclic A).IsTriangulated)

/- Companion recall: the acyclic complexes form a strictly full subcategory of
`K(\mathcal A)`. -/
#check (inferInstance :
  (HomotopyCategory.subcategoryAcyclic A).IsClosedUnderIsomorphisms)

/- Companion recall: the acyclic complexes are stable under retracts/direct summands. This is the
owner-facing retract-stability instance for `HomotopyCategory.subcategoryAcyclic A`, inherited
from the generic homological-kernel owner. -/
#check (show ObjectProperty.IsStableUnderRetracts (HomotopyCategory.subcategoryAcyclic A) from by
  dsimp [HomotopyCategory.subcategoryAcyclic]
  infer_instance)

section

variable [HasDerivedCategory.{w} A]

local notation "Ac" => HomotopyCategory.subcategoryAcyclic A
local notation "Q" =>
  (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)

-- Proof sketch: identify the kernel of the canonical Verdier quotient `Ac.trW.Q` with the
-- retract closure of `Ac`, collapse that retract closure using the owner theorem
-- `retractClosure_eq_self`, and transport the resulting kernel equality to
-- `DerivedCategory.Qh` through the canonical localization equivalence
-- `Localization.equivalenceFromModel`.
/-- The kernel of the localization functor from the homotopy category to the derived category is
the subcategory of acyclic complexes. -/
theorem subcategoryAcyclic_kernel_Qh :
    Functor.kernel Q = Ac := by
  letI : ObjectProperty.IsStableUnderRetracts Ac := by
    dsimp [HomotopyCategory.subcategoryAcyclic]
    infer_instance
  let W := (HomotopyCategory.subcategoryAcyclic A).trW
  let E := Localization.equivalenceFromModel Q W
  let η := Localization.qCompEquivalenceFromModelFunctorIso Q W
  let ε := Localization.compEquivalenceFromModelInverseIso Q W
  have hkernel :
      Functor.kernel W.Q = Ac := by
    rw [kernel_triangulatedLocalization_eq_retractClosure Ac]
    simpa using (HomotopyCategory.subcategoryAcyclic A).retractClosure_eq_self
  ext X
  constructor
  · intro hX
    have hX' : IsZero (E.inverse.obj (DerivedCategory.Qh.obj X)) :=
      E.inverse.map_isZero hX
    have hX'' : IsZero (W.Q.obj X) :=
      (ε.app X).isZero_iff.1 hX'
    have hker : Functor.kernel W.Q X := hX''
    rw [hkernel] at hker
    exact hker
  · intro hX
    have hker : Functor.kernel W.Q X := by
      rw [hkernel]
      exact hX
    have hX' : IsZero (E.functor.obj (W.Q.obj X)) :=
      E.functor.map_isZero hker
    exact (η.app X).isZero_iff.1 hX'

/- Companion recall: the degree-zero homology functor on the homotopy category factors through the
localization `Q : K(\mathcal A) ⥤ D(\mathcal A)`. -/
#check (DerivedCategory.homologyFunctorFactorsh A 0)

end

/-! ### Definition_13_11_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure

noncomputable section

universe u v

namespace CategoryTheory

universe w

scoped notation "D(" A:arg ")" => DerivedCategory A

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The bounded-below derived category `D^+(\mathcal A)` as a full subcategory of
`D(\mathcal A)` cut out by the canonical `t`-structure owner `t.plus`. -/
abbrev boundedBelowDerivedCategory : Type (max u v) :=
  (t.plus : ObjectProperty (D(𝒜))).FullSubcategory

/-- The bounded-above derived category `D^-(\mathcal A)` as a full subcategory of
`D(\mathcal A)` cut out by the canonical `t`-structure owner `t.minus`. -/
abbrev boundedAboveDerivedCategory : Type (max u v) :=
  (t.minus : ObjectProperty (D(𝒜))).FullSubcategory

/-- The bounded derived category `D^b(\mathcal A)` as a full subcategory of `D(\mathcal A)`
cut out by the canonical `t`-structure owner `t.bounded`. -/
abbrev boundedDerivedCategory : Type (max u v) :=
  (t.bounded : ObjectProperty (D(𝒜))).FullSubcategory

scoped notation "D⁺(" A:arg ")" => boundedBelowDerivedCategory A
scoped notation "D⁻(" A:arg ")" => boundedAboveDerivedCategory A
scoped notation "Dᵇ(" A:arg ")" => boundedDerivedCategory A

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/- Domain-style sampling:
- primary domain: the derived category as a localization/Verdier quotient of the homotopy
  category, together with the canonical `t`-structure on `DerivedCategory 𝒜`;
- sampled owner declarations:
  `DerivedCategory`,
  `DerivedCategory.Qh`,
  `DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso`,
  `DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhTrWSubcategoryAcyclic`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.TStructure.t`,
  `t.plus`,
  `t.minus`,
  `t.bounded`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.isGE_iff`,
  `DerivedCategory.isLE_iff`;
- best owner abstraction: the primitive source data are the localization owner
  `DerivedCategory.Qh.IsLocalization` for quasi-isomorphisms, equivalently for the acyclic
  Verdier quotient, together with the canonical `t`-structure owners `t.plus`, `t.minus`, and
  `t.bounded`; the categories `D^+(\mathcal A)`, `D^-(\mathcal A)`, and `D^b(\mathcal A)` should
  therefore be exposed directly as the corresponding full subcategories, and the eventual
  vanishing formulations should stay as companion bridge lemmas rather than a second owner layer.
- source/core/bridge triage:
  `source-facing`: the chapter vocabulary `D(\mathcal A)`, `D^+(\mathcal A)`, `D^-(\mathcal A)`,
    `D^b(\mathcal A)` and the eventual cohomology-vanishing reformulations used in the text;
  `core/canonical`: `DerivedCategory 𝒜`, the localization owner
    `DerivedCategory.Qh.IsLocalization`, and the canonical `t`-structure owners `t.plus`,
    `t.minus`, `t.bounded`;
  `bridge/view`: the full-subcategory models for `D^+(\mathcal A)`, `D^-(\mathcal A)`,
    `D^b(\mathcal A)`, and the `_iff` lemmas translating the owner predicates into the textbook
    eventual-vanishing form;
- primitive vs. derived API: the localization owner facts for `DerivedCategory.Qh` and the
  `t`-structure owners `t.plus`, `t.minus`, `t.bounded` are primitive; the full subcategories
  `D^+(\mathcal A)`, `D^-(\mathcal A)`, `D^b(\mathcal A)` and the eventual homology-vanishing
  criteria are the derived/source-facing API.
-/

/- Definition 13.11.3: for an abelian category `𝒜`, the derived category `D(𝒜)` is the
canonical localization `DerivedCategory 𝒜` of the homotopy category `K(𝒜)` at
quasi-isomorphisms, equivalently the Verdier quotient of `K(𝒜)` by the acyclic complexes. The
companion declarations below record the degree-zero cohomology functor and the bounded-below,
bounded-above, and bounded derived subcategories. -/
#check (D(𝒜))

/- The defining owner statement is that the quotient functor `K(𝒜) ⥤ D(𝒜)` localizes the
homotopy category at quasi-isomorphisms. -/
recall DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso :
  DerivedCategory.Qh.IsLocalization (HomotopyCategory.quasiIso 𝒜 (up ℤ))

/- Equivalently, `D(𝒜)` is the Verdier quotient of `K(𝒜)` by the triangulated subcategory of
acyclic complexes. -/
recall DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhTrWSubcategoryAcyclic :
  DerivedCategory.Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic 𝒜).trW

/- Companion recall: the quotient functor `K(𝒜) ⥤ D(𝒜)` itself is `DerivedCategory.Qh`. -/
recall DerivedCategory.Qh

/- Companion recall: the cohomology functors on `D(𝒜)` are `DerivedCategory.homologyFunctor`; in
degree `0` this is the textbook functor `H^0 : D(𝒜) ⥤ 𝒜`. -/
recall DerivedCategory.homologyFunctor

/- Companion recall: the canonical factorization of `H^0` on the homotopy category through the
quotient functor `K(𝒜) ⥤ D(𝒜)` is `DerivedCategory.homologyFunctorFactorsh 𝒜 0`. -/
recall DerivedCategory.homologyFunctorFactorsh

/- Companion recall: cohomological boundedness on `D(𝒜)` is measured by the canonical
`t`-structure predicates `DerivedCategory.IsGE` and `DerivedCategory.IsLE`. -/
recall DerivedCategory.IsGE

/- Companion recall: cohomological boundedness on `D(𝒜)` is measured by the canonical
`t`-structure predicates `DerivedCategory.IsGE` and `DerivedCategory.IsLE`. -/
recall DerivedCategory.IsLE

/- Companion recall: the bounded-below derived category `D^+(\mathcal A)` is the full
subcategory cut out by the canonical owner `t.plus`. -/
#check (t.plus : ObjectProperty (D(𝒜)))
#check (D⁺(𝒜))

/- Companion recall: the bounded-above derived category `D^-(\mathcal A)` is the full
subcategory cut out by the canonical owner `t.minus`. -/
#check (t.minus : ObjectProperty (D(𝒜)))
#check (D⁻(𝒜))

/- Companion recall: the bounded derived category `D^b(\mathcal A)` is the full subcategory cut
out by the canonical owner `t.bounded`. -/
#check (t.bounded : ObjectProperty (D(𝒜)))
#check (Dᵇ(𝒜))

/-- Unfolding membership in `t.plus` gives the textbook eventual low-degree vanishing criterion
for `D(\mathcal A)`. -/
theorem derivedCategory_t_plus_iff
    (K : D(𝒜)) :
    (t.plus : ObjectProperty (D(𝒜))) K ↔
      ∃ n : ℤ, ∀ i : ℤ, i < n →
        IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj K) := by
  simp [Triangulated.TStructure.plus, DerivedCategory.isGE_iff]

/-- Unfolding membership in `t.minus` gives the textbook eventual high-degree vanishing criterion
for `D(\mathcal A)`. -/
theorem derivedCategory_t_minus_iff
    (K : D(𝒜)) :
    (t.minus : ObjectProperty (D(𝒜))) K ↔
      ∃ n : ℤ, ∀ i : ℤ, n < i →
        IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj K) := by
  simp [Triangulated.TStructure.minus, DerivedCategory.isLE_iff]

/-- Unfolding membership in `t.bounded` says that homology vanishes in sufficiently low and
sufficiently high degrees. -/
theorem derivedCategory_t_bounded_iff
    (K : D(𝒜)) :
    (t.bounded : ObjectProperty (D(𝒜))) K ↔
      (∃ a : ℤ, ∀ i : ℤ, i < a →
        IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj K)) ∧
      (∃ b : ℤ, ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj K)) := by
  simp [Triangulated.TStructure.bounded, derivedCategory_t_plus_iff, derivedCategory_t_minus_iff]

end CategoryTheory

/-! ### Remark_13_11_4 (from Chap13) -/
open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Localization
open ComplexShape HomotopyCategory
open CochainComplex

universe w v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Remark 13.11.4:
- primary domain: quasi-isomorphism localizations of cochain complexes and the computation of
  derived-category morphisms by K-injective targets;
- sampled owner declarations:
  `Localization.HasSmallLocalizedHom`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `Localization.hasSmallLocalizedHom_iff_target`,
  `DerivedCategory.quotientCompQhIso`;
- best owner abstraction:
  `source-facing`: smallness of morphism types in the localization at quasi-isomorphisms once the
    target admits a quasi-isomorphism to a K-injective complex;
  `core/canonical`: `HasSmallLocalizedHom` together with the canonical K-injective bijection
    `IsKInjective.Qh_map_bijective`;
  `bridge/view`: target transport along a quasi-isomorphism via
    `Localization.hasSmallLocalizedHom_iff_target`.
- primitive data: a source complex `K`, a target complex `L`, and a quasi-isomorphism from `L` to
  some K-injective replacement `I`;
- derived API: the smallness statement in the localization, obtained by transporting smallness of
  homotopy-category Hom-types through the canonical localization comparison maps.

The owner theorem here is therefore `HasSmallLocalizedHom`; the K-injective case is the core
computation statement, the explicit quasi-isomorphism-to-K-injective theorem is the primitive
bridge/view layer, and the source-facing remark is the existential corollary obtained from that
bridge.
-/

local notation "Qis" => HomologicalComplex.quasiIso 𝒜 (up ℤ)

-- Proof sketch: Lemma 13.31.2 identifies morphisms into a K-injective complex in the
-- quasi-isomorphism localization with morphisms in the homotopy category, and the latter form a
-- `w`-small type whenever the ambient category is `w`-locally small.
/-- A K-injective target computes morphisms in the quasi-isomorphism localization by morphisms in
the homotopy category, so the resulting localized Hom-type is small. -/
theorem hasSmallLocalizedHom_of_isKInjective
    [LocallySmall.{w} 𝒜] (K I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    HasSmallLocalizedHom.{w} Qis K I := by
  let Kq := quotient 𝒜 (up ℤ)
  rw [hasSmallLocalizedHom_iff Qis DerivedCategory.Q]
  have hKHom :
      Small.{w} ((Kq.obj K) ⟶ (Kq.obj I)) := by
    let _ : LocallySmall.{w} (CochainComplex 𝒜 ℤ) := by infer_instance
    exact small_of_surjective Kq.map_surjective
  have hQh :
      Small.{w}
        (DerivedCategory.Qh.obj (Kq.obj K) ⟶ DerivedCategory.Qh.obj (Kq.obj I)) :=
    (small_congr
      (Equiv.ofBijective DerivedCategory.Qh.map
        (IsKInjective.Qh_map_bijective (Kq.obj K) I))).1 hKHom
  exact (small_congr
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso 𝒜).app K)
      ((DerivedCategory.quotientCompQhIso 𝒜).app I))).2 hQh

-- Proof sketch: use the given quasi-isomorphism from `L` to a K-injective complex `I`, apply
-- `hasSmallLocalizedHom_of_isKInjective` to `I`, and transport smallness back along that
-- comparison quasi-isomorphism.
/-- If `L^•` admits a quasi-isomorphism to a K-injective complex `I^•`, then morphisms
`K^• ⟶ L^•` in the localization at quasi-isomorphisms form a small type. -/
theorem hasSmallLocalizedHom_of_quasiIso_to_isKInjective
    [LocallySmall.{w} 𝒜] (K : CochainComplex 𝒜 ℤ) {L I : CochainComplex 𝒜 ℤ}
    [I.IsKInjective] (f : L ⟶ I) (hf : QuasiIso f) :
    HasSmallLocalizedHom.{w} Qis K L := by
  exact (hasSmallLocalizedHom_iff_target Qis K f hf).2
    (hasSmallLocalizedHom_of_isKInjective K I)

-- Proof sketch: unpack the existential K-injective replacement and apply the explicit
-- quasi-isomorphism-to-K-injective bridge theorem above.
/-- Remark 13.11.4: if `L^•` is quasi-isomorphic to a K-injective complex, then morphisms
`K^• ⟶ L^•` in the localization at quasi-isomorphisms form a small type; equivalently,
`Hom_{D(\mathcal A)}(K^•, L^•)` is a set. -/
theorem hasSmallLocalizedHom_of_hasKInjectiveReplacement
    [LocallySmall.{w} 𝒜] (K L : CochainComplex 𝒜 ℤ)
    (hL : ∃ (I : CochainComplex 𝒜 ℤ) (_ : I.IsKInjective) (f : L ⟶ I), QuasiIso f) :
    HasSmallLocalizedHom.{w} Qis K L := by
  obtain ⟨I, hI, f, hf⟩ := hL
  let _ : I.IsKInjective := hI
  exact hasSmallLocalizedHom_of_quasiIso_to_isKInjective K f hf

end

/-! ### Lemma_13_11_5 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : CochainComplex C ℤ)

/- Domain-style sampling:
- primary domain: canonical truncations of cochain complexes and the quasi-isomorphism criteria
  attached to the maps `πTruncGE`, `ιTruncLE`, and `truncGEMap`;
- sampled owner declarations:
  `CochainComplex.πTruncGE`,
  `CochainComplex.ιTruncLE`,
  `CochainComplex.truncGEMap`,
  `CochainComplex.quasiIso_πTruncGE_iff`,
  `CochainComplex.quasiIso_ιTruncLE_iff`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the primitive data are the canonical truncation objects/maps and the
  boundedness predicates `IsGE`, `IsLE`, `IsStrictlyGE`, `IsStrictlyLE`; the existence results in
  this file are derived API and should be stated directly in terms of those owners rather than
  through a separate wrapper class;
- source/core/bridge triage:
  `source-facing`: existence of bounded truncation replacements for a complex with eventually
    vanishing homology;
  `core/canonical`: the truncation maps and boundedness owners on `CochainComplex C ℤ`;
  `bridge/view`: the commuting-square formulation for the simultaneous lower/upper truncation.
-/

-- Proof sketch: choose a lower bound `a` below which all homology objects of `K` vanish, deduce
-- `K.IsGE a` from `HomologicalComplex.exactAt_iff_isZero_homology`, and then use the canonical
-- `QuasiIso` instance for `K.πTruncGE a`.
/-- Lemma 13.11.5 (1): if the homology of `K` vanishes in sufficiently negative degrees, then for
some lower truncation bound `a` the canonical map `K ⟶ K.truncGE a` is a quasi-isomorphism, and
`K.truncGE a` is bounded below. -/
theorem exists_quasiIso_to_truncGE_of_eventually_isZero_homology
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    ∃ a : ℤ, QuasiIso (K.πTruncGE a) ∧ (K.truncGE a).IsStrictlyGE a := by
  rcases hK with ⟨a, ha⟩
  have hGE : K.IsGE a := by
    rw [isGE_iff]
    intro n hn
    rw [exactAt_iff_isZero_homology]
    exact ha n hn
  letI : K.IsGE a := hGE
  exact ⟨a, inferInstance, inferInstance⟩

-- Proof sketch: choose an upper bound `b` above which all homology objects of `K` vanish, deduce
-- `K.IsLE b` from `HomologicalComplex.exactAt_iff_isZero_homology`, and then use the canonical
-- `QuasiIso` instance for `K.ιTruncLE b`.
/-- Lemma 13.11.5 (2): if the homology of `K` vanishes in sufficiently positive degrees, then for
some upper truncation bound `b` the canonical map `K.truncLE b ⟶ K` is a quasi-isomorphism, and
`K.truncLE b` is bounded above. -/
theorem exists_quasiIso_from_truncLE_of_eventually_isZero_homology
    (hK : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.homology n)) :
    ∃ b : ℤ, QuasiIso (K.ιTruncLE b) ∧ (K.truncLE b).IsStrictlyLE b := by
  rcases hK with ⟨b, hb⟩
  have hLE : K.IsLE b := by
    rw [isLE_iff]
    intro n hn
    rw [exactAt_iff_isZero_homology]
    exact hb n hn
  letI : K.IsLE b := hLE
  exact ⟨b, inferInstance, inferInstance⟩

-- Proof sketch: choose bounds `a ≪ 0 ≪ b` so that the homology of `K` vanishes outside `[a, b]`,
-- take the canonical square formed by `K`, `K.truncGE a`, `K.truncLE b`, and
-- `(K.truncLE b).truncGE a`, use the first two clauses for the vertical and horizontal maps, and
-- use truncation naturality for commutativity.
/-- Lemma 13.11.5 (3): if the homology of `K` vanishes outside a finite range, then there are
truncation bounds `a ≤ b` for which the canonical square
`K ⟶ K.truncGE a`, `K.truncLE b ⟶ K`, `(K.truncLE b).truncGE a ⟶ K.truncGE a`
consists of quasi-isomorphisms, commutes, and has bounded middle-bottom complex. -/
theorem exists_quasiIso_truncation_square_of_eventually_isZero_homology
    (hK : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.homology n)) :
    ∃ a b : ℤ,
      a ≤ b ∧
      QuasiIso (K.πTruncGE a) ∧
      QuasiIso (K.ιTruncLE b) ∧
      QuasiIso ((K.truncLE b).πTruncGE a) ∧
      QuasiIso (truncGEMap (K.ιTruncLE b) a) ∧
      CommSq
        ((K.truncLE b).πTruncGE a)
        (K.ιTruncLE b)
        (truncGEMap (K.ιTruncLE b) a)
        (K.πTruncGE a) ∧
      ((K.truncLE b).truncGE a).IsStrictlyGE a ∧
      ((K.truncLE b).truncGE a).IsStrictlyLE b := by
  rcases hK with ⟨a₀, b₀, h⟩
  let a := min a₀ b₀
  let b := max a₀ b₀
  have hab : a ≤ b := by
    simpa [a, b] using min_le_max a₀ b₀
  have hGE : K.IsGE a := by
    rw [isGE_iff]
    intro n hn
    rw [exactAt_iff_isZero_homology]
    exact h n <| Or.inl <| lt_of_lt_of_le hn <| by
      dsimp [a]
      exact Int.min_le_left _ _
  have hLE : K.IsLE b := by
    rw [isLE_iff]
    intro n hn
    rw [exactAt_iff_isZero_homology]
    exact h n <| Or.inr <| lt_of_le_of_lt (by
      dsimp [b]
      exact Int.le_max_right _ _) hn
  letI : K.IsGE a := hGE
  letI : K.IsLE b := hLE
  have hTruncLEGE : (K.truncLE b).IsGE a := by
    rw [isGE_iff]
    intro n hn
    exact (exactAt_iff_of_quasiIsoAt (K.ιTruncLE b) n).2 <| by
      rw [exactAt_iff_isZero_homology]
      exact h n <| Or.inl <| lt_of_lt_of_le hn <| by
        dsimp [a]
        exact Int.min_le_left _ _
  letI : (K.truncLE b).IsGE a := hTruncLEGE
  refine ⟨a, b, hab, inferInstance, inferInstance, inferInstance, ?_, ?_, inferInstance,
    inferInstance⟩
  · have hQuasi :
        QuasiIso (truncGEMap (K.ιTruncLE b) a) ↔
          ∀ n : ℤ, a ≤ n → QuasiIsoAt (K.ιTruncLE b) n :=
      CochainComplex.quasiIso_truncGEMap_iff (K.ιTruncLE b) a
    exact hQuasi.2 fun n hn ↦ inferInstance
  · exact ⟨πTruncGE_naturality (K.ιTruncLE b) a⟩

/-! ### Lemma_13_11_6 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 13.11.6:
- primary domain: derived-category localization of bounded homotopy categories by
  quasi-isomorphisms;
- sampled owner declarations:
  `HomotopyCategory.quasiIso`,
  `HomotopyCategory.subcategoryAcyclic`,
  `ObjectProperty.inverseImage`,
  `ObjectProperty.lift`,
  `DerivedCategory.Qh`,
  `Functor.kernel`;
- best owner abstraction: the ambient owners are the unbounded quasi-isomorphism morphism
  property `HomotopyCategory.quasiIso 𝒜 (up ℤ)` and the acyclic triangulated subcategory
  `HomotopyCategory.subcategoryAcyclic 𝒜`; on the bounded categories, the source-facing objects
  are their inverse-image/restricted views along the inclusion `ObjectProperty.ι`.
- primitive vs. derived API: the primitive data are the bounded homotopy object properties from
  `Definition_13_8_1`, the canonical quotient functor `DerivedCategory.Qh`, and the ambient
  quasi-isomorphism / acyclic owners. The bounded localization functors and their kernel /
  localization statements are the derived bridge/view layer.
- source/core/bridge triage:
  `source-facing`: `Qis⁺(𝒜)`, `Qis⁻(𝒜)`, `Qisᵇ(𝒜)`, the bounded derived functors, and the nine
    localization statements of Lemma 13.11.6;
  `core/canonical`: `HomotopyCategory.quasiIso 𝒜 (up ℤ)`,
    `HomotopyCategory.subcategoryAcyclic 𝒜`, `DerivedCategory.Qh`, and `Functor.kernel`;
  `bridge/view`: inverse images to `K⁺(𝒜)`, `K⁻(𝒜)`, `Kᵇ(𝒜)` and the induced functors
    `K^*(𝒜) ⥤ D^*(𝒜)`.

The bounded quasi-isomorphism morphism properties are high-frequency bridge owners used downstream,
so they remain named here. The bounded acyclic object properties are only the direct inverse-image
views of `HomotopyCategory.subcategoryAcyclic 𝒜`, so this file uses source-facing notation for
them rather than introducing a second public owner layer. -/

/- Reuse the Chapter 13 boundedness owners on cochain complexes and their homotopy categories from
`Definition_13_8_1` and the bounded derived-category owners from `Definition_13_11_3`; this file
adds localization results on top of that canonical API rather than redeclaring parallel
bounded-derived notions. -/

/-- The quasi-isomorphisms in `K^+(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedBelowHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (K⁺(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (ObjectProperty.ι (boundedBelowHomotopyProperty 𝒜))

/-- The quasi-isomorphisms in `K^-(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedAboveHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (K⁻(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (ObjectProperty.ι (boundedAboveHomotopyProperty 𝒜))

/-- The quasi-isomorphisms in `K^b(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (Kᵇ(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (ObjectProperty.ι (boundedHomotopyProperty 𝒜))

scoped notation "Qis⁺(" A:arg ")" => boundedBelowHomotopyQuasiIso A
scoped notation "Qis⁻(" A:arg ")" => boundedAboveHomotopyQuasiIso A
scoped notation "Qisᵇ(" A:arg ")" => boundedHomotopyQuasiIso A

scoped notation "Ac⁺(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (boundedBelowHomotopyProperty A))
scoped notation "Ac⁻(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (boundedAboveHomotopyProperty A))
scoped notation "Acᵇ(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (boundedHomotopyProperty A))

/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded-below homotopy objects
to bounded-below derived objects. -/
theorem qh_obj_mem_t_plus
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X : K⁺(𝒜)) :
    (t.plus : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := sorry

/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded-above homotopy objects
to bounded-above derived objects. -/
theorem qh_obj_mem_t_minus
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X : K⁻(𝒜)) :
    (t.minus : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := sorry

-- Proof sketch: a bounded complex has cohomology vanishing outside a finite interval, and the
-- identity functor sends bounded complexes to the same derived objects, so both the bounded-below
-- and bounded-above vanishing conditions hold in the image.
/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded homotopy objects to
bounded derived objects. -/
theorem qh_obj_mem_t_bounded
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X : Kᵇ(𝒜)) :
    (t.bounded : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := sorry

/-- The canonical functor `K^+(\mathcal A) ⟶ D^+(\mathcal A)`. -/
abbrev mapBoundedBelowHomotopyToDerivedBelow
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    K⁺(𝒜) ⥤ D⁺(𝒜) :=
  ObjectProperty.lift
    (t.plus : ObjectProperty (D(𝒜)))
    (ObjectProperty.ι (boundedBelowHomotopyProperty 𝒜) ⋙ DerivedCategory.Qh)
    (qh_obj_mem_t_plus 𝒜)

/-- The canonical functor `K^-(\mathcal A) ⟶ D^-(\mathcal A)`. -/
abbrev mapBoundedAboveHomotopyToDerivedAbove
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    K⁻(𝒜) ⥤ D⁻(𝒜) :=
  ObjectProperty.lift
    (t.minus : ObjectProperty (D(𝒜)))
    (ObjectProperty.ι (boundedAboveHomotopyProperty 𝒜) ⋙ DerivedCategory.Qh)
    (qh_obj_mem_t_minus 𝒜)

/-- The canonical functor `K^b(\mathcal A) ⟶ D^b(\mathcal A)`. -/
abbrev mapBoundedHomotopyToDerivedBounded
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Kᵇ(𝒜) ⥤ Dᵇ(𝒜) :=
  ObjectProperty.lift
    (t.bounded : ObjectProperty (D(𝒜)))
    (ObjectProperty.ι (boundedHomotopyProperty 𝒜) ⋙ DerivedCategory.Qh)
    (qh_obj_mem_t_bounded 𝒜)

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Companion recall: the acyclic bounded-below objects define a triangulated full subcategory
`Ac^{+}(\mathcal A) ⊆ K^{+}(\mathcal A)`. This is the generic inverse-image triangulated
instance applied to `HomotopyCategory.subcategoryAcyclic 𝒜`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (Ac⁺(𝒜)))

/- Companion recall: the acyclic bounded-below subcategory `Ac^{+}(\mathcal A)` is saturated,
i.e. stable under retracts in `K^{+}(\mathcal A)`. This is the generic inverse-image retract
stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (Ac⁺(𝒜)) from by
  dsimp [HomotopyCategory.subcategoryAcyclic]
  infer_instance)

-- Proof sketch: identify quasi-isomorphisms in the ambient homotopy category with the Verdier
-- morphism property of the acyclic subcategory, then restrict along the inclusion
-- `K^{+}(\mathcal A) ⥤ K(\mathcal A)`.
/-- Lemma 13.11.6 (1): the saturated multiplicative system corresponding to
`Ac^{+}(\mathcal A)` is precisely `Qis^{+}(\mathcal A)`. -/
theorem boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Ac⁺(𝒜)).trW =
      Qis⁺(𝒜) := sorry

-- Proof sketch: an object of `K^{+}(\mathcal A)` maps to zero in `D^{+}(\mathcal A)` exactly
-- when its image in the unbounded derived category is acyclic, which is the defining condition of
-- `Ac^{+}(\mathcal A)`.
/-- Lemma 13.11.6 (2): the kernel of `K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)` is
`Ac^{+}(\mathcal A)`. -/
theorem kernel_mapBoundedBelowHomotopyToDerivedBelow_eq_acyclic
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.kernel (mapBoundedBelowHomotopyToDerivedBelow 𝒜) =
      Ac⁺(𝒜) := sorry

-- Proof sketch: Lemma 13.11.5 makes the bounded-below quasi-isomorphisms cofinal in the ambient
-- derived-category localization, so the canonical functor `K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)`
-- satisfies the universal property of localization at `Qis^{+}(\mathcal A)`.
/-- Lemma 13.11.6 (3): the canonical functor `K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)` realizes
`D^{+}(\mathcal A)` as the localization of `K^{+}(\mathcal A)` at `Qis^{+}(\mathcal A)`. -/
theorem mapBoundedBelowHomotopyToDerivedBelow_isLocalization
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.IsLocalization
      (mapBoundedBelowHomotopyToDerivedBelow 𝒜)
      (Qis⁺(𝒜)) := sorry

/- Companion recall: the acyclic bounded-above objects define a triangulated full subcategory
`Ac^{-}(\mathcal A) ⊆ K^{-}(\mathcal A)`. This is the generic inverse-image triangulated
instance applied to `HomotopyCategory.subcategoryAcyclic 𝒜`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (Ac⁻(𝒜)))

/- Companion recall: the acyclic bounded-above subcategory `Ac^{-}(\mathcal A)` is saturated,
i.e. stable under retracts in `K^{-}(\mathcal A)`. This is the generic inverse-image retract
stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (Ac⁻(𝒜)) from by
  dsimp [HomotopyCategory.subcategoryAcyclic]
  infer_instance)

-- Proof sketch: use the unbounded identification between quasi-isomorphisms and the Verdier
-- morphism property of acyclic complexes, then restrict it to the bounded-above full subcategory.
/-- Lemma 13.11.6 (4): the saturated multiplicative system corresponding to
`Ac^{-}(\mathcal A)` is precisely `Qis^{-}(\mathcal A)`. -/
theorem boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Ac⁻(𝒜)).trW =
      Qis⁻(𝒜) := sorry

-- Proof sketch: bounded-above objects die in `D^{-}(\mathcal A)` exactly when their image in the
-- unbounded derived category is acyclic, giving the same kernel criterion as in the bounded-below
-- case.
/-- Lemma 13.11.6 (5): the kernel of `K^{-}(\mathcal A) ⟶ D^{-}(\mathcal A)` is
`Ac^{-}(\mathcal A)`. -/
theorem kernel_mapBoundedAboveHomotopyToDerivedAbove_eq_acyclic
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.kernel (mapBoundedAboveHomotopyToDerivedAbove 𝒜) =
      Ac⁻(𝒜) := sorry

-- Proof sketch: Lemma 13.11.5 yields bounded-above representatives for the denominators in the
-- ambient localization, so the bounded-above functor has the universal property of localization at
-- `Qis^{-}(\mathcal A)`.
/-- Lemma 13.11.6 (6): the canonical functor `K^{-}(\mathcal A) ⟶ D^{-}(\mathcal A)` realizes
`D^{-}(\mathcal A)` as the localization of `K^{-}(\mathcal A)` at `Qis^{-}(\mathcal A)`. -/
theorem mapBoundedAboveHomotopyToDerivedAbove_isLocalization
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.IsLocalization
      (mapBoundedAboveHomotopyToDerivedAbove 𝒜)
      (Qis⁻(𝒜)) := sorry

/- Companion recall: the acyclic bounded objects define a triangulated full subcategory
`Ac^{b}(\mathcal A) ⊆ K^{b}(\mathcal A)`. This is the generic inverse-image triangulated
instance applied to `HomotopyCategory.subcategoryAcyclic 𝒜`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (Acᵇ(𝒜)))

/- Companion recall: the acyclic bounded subcategory `Ac^{b}(\mathcal A)` is saturated, i.e.
stable under retracts in `K^{b}(\mathcal A)`. This is the generic inverse-image retract
stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (Acᵇ(𝒜)) from by
  dsimp [HomotopyCategory.subcategoryAcyclic]
  infer_instance)

-- Proof sketch: identify quasi-isomorphisms with the Verdier morphism property of acyclic
-- complexes in the ambient homotopy category and restrict to the bounded full subcategory.
/-- Lemma 13.11.6 (7): the saturated multiplicative system corresponding to
`Ac^{b}(\mathcal A)` is precisely `Qis^{b}(\mathcal A)`. -/
theorem boundedAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Acᵇ(𝒜)).trW =
      Qisᵇ(𝒜) := sorry

-- Proof sketch: a bounded homotopy object becomes zero in `D^{b}(\mathcal A)` exactly when its
-- image in `D(\mathcal A)` is acyclic, so the kernel is the bounded acyclic subcategory.
/-- Lemma 13.11.6 (8): the kernel of `K^{b}(\mathcal A) ⟶ D^{b}(\mathcal A)` is
`Ac^{b}(\mathcal A)`. -/
theorem kernel_mapBoundedHomotopyToDerivedBounded_eq_acyclic
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.kernel (mapBoundedHomotopyToDerivedBounded 𝒜) =
      Acᵇ(𝒜) := sorry

-- Proof sketch: combine the bounded-above localization argument with the fact that bounded
-- denominators can be chosen inside `K^{b}(\mathcal A)`, again using the bounded replacement
-- statement from Lemma 13.11.5.
/-- Lemma 13.11.6 (9): the canonical functor `K^{b}(\mathcal A) ⟶ D^{b}(\mathcal A)` realizes
`D^{b}(\mathcal A)` as the localization of `K^{b}(\mathcal A)` at `Qis^{b}(\mathcal A)`. -/
theorem mapBoundedHomotopyToDerivedBounded_isLocalization
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.IsLocalization
      (mapBoundedHomotopyToDerivedBounded 𝒜)
      (Qisᵇ(𝒜)) := sorry

end

end CategoryTheory
