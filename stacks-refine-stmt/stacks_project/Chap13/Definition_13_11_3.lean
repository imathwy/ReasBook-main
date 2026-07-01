import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory
open DerivedCategory.TStructure

noncomputable section

universe u v

namespace CategoryTheory

universe w

scoped notation "D(" A:arg ")" => DerivedCategory A
scoped notation:max "H^" i:max => DerivedCategory.homologyFunctor _ i

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

/-- The `i`-th cohomology functor on `D^b(\mathcal A)`. -/
abbrev boundedDerivedHomologyFunctor (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (i : ℤ) :
    Dᵇ(𝒜) ⥤ 𝒜 :=
  t.bounded.ι ⋙ H^i

/-- The degree-zero cohomology functor on `D^b(\mathcal A)`. -/
abbrev boundedDerivedZeroHomologyFunctor (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] :
    Dᵇ(𝒜) ⥤ 𝒜 :=
  t.bounded.ι ⋙ H^0

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
  Qh.IsLocalization (HomotopyCategory.quasiIso 𝒜 (up ℤ))

/- Equivalently, `D(𝒜)` is the Verdier quotient of `K(𝒜)` by the triangulated subcategory of
acyclic complexes. -/
recall DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhTrWSubcategoryAcyclic :
  Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic 𝒜).trW

/- Companion recall: the quotient functor `K(𝒜) ⥤ D(𝒜)` itself is `Qh`. -/
recall Qh

/- Companion recall: the cohomology functors on `D(𝒜)` are `homologyFunctor`; in
degree `0` this is the textbook functor `H^0 : D(𝒜) ⥤ 𝒜`. -/
recall homologyFunctor

/- Companion notation recall: the source-facing cohomology functor notation is `H^i`. -/
#check (H^0 : D(𝒜) ⥤ 𝒜)

/- Companion recall: the canonical factorization of `H^0` on the homotopy category through the
quotient functor `K(𝒜) ⥤ D(𝒜)` is `homologyFunctorFactorsh 𝒜 0`. -/
recall homologyFunctorFactorsh

/- Companion recall: cohomological boundedness on `D(𝒜)` is measured by the canonical
`t`-structure predicates `IsGE` and `IsLE`. -/
recall IsGE

/- Companion recall: cohomological boundedness on `D(𝒜)` is measured by the canonical
`t`-structure predicates `IsGE` and `IsLE`. -/
recall IsLE

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
      ∃ n : ℤ, ∀ i < n, IsZero ((H^i).obj K) := by
  simp [Triangulated.TStructure.plus, isGE_iff]

/-- Unfolding membership in `t.minus` gives the textbook eventual high-degree vanishing criterion
for `D(\mathcal A)`. -/
theorem derivedCategory_t_minus_iff
    (K : D(𝒜)) :
    (t.minus : ObjectProperty (D(𝒜))) K ↔
      ∃ n : ℤ, ∀ i > n, IsZero ((H^i).obj K) := by
  simp [Triangulated.TStructure.minus, isLE_iff]

/-- Unfolding membership in `t.bounded` says that homology vanishes in sufficiently low and
sufficiently high degrees. -/
theorem derivedCategory_t_bounded_iff
    (K : D(𝒜)) :
    (t.bounded : ObjectProperty (D(𝒜))) K ↔
      (∃ a : ℤ, ∀ i < a, IsZero ((H^i).obj K)) ∧
      (∃ b : ℤ, ∀ i > b, IsZero ((H^i).obj K)) := by
  simp [Triangulated.TStructure.bounded, derivedCategory_t_plus_iff, derivedCategory_t_minus_iff]

end CategoryTheory
