import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape

universe v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C]

section

variable [HasZeroMorphisms C]

/- Domain-style sampling:
- primary domain: bounded cochain-complex categories and their homotopy categories;
- relevant upstream owner declarations in this domain:
  `CochainComplex.plus`,
  `CochainComplex.plus_iff`,
  `CochainComplex.Plus`,
  `HomotopyCategory C (up ℤ)`;
- source/core/bridge triage:
  `source-facing`: the bounded cochain-complex categories `Comp⁺(C)`, `Comp⁻(C)`, `Compᵇ(C)` and
    the bounded homotopy categories `K⁺(C)`, `K⁻(C)`, `Kᵇ(C)`;
  `core/canonical`: the owner categories `CochainComplex.Plus C`, `CochainComplex.Minus C`, and
    `CochainComplex.Bounded C`;
  `bridge/view`: the corresponding bounded full-subcategory realizations inside
    `K(C) = HomotopyCategory C (up ℤ)`.

Primitive data is the cochain-complex category and its actual boundedness predicates. The bounded
homotopy full subcategories of `K(C)` are therefore only a view on these owner categories, not
their primary public definition.
-/

/- The canonical bounded-below owner already exists in mathlib as `CochainComplex.plus` /
`CochainComplex.Plus`; this file adds only the analogous bounded-above and bounded owners needed
for the Chapter 13 source-facing vocabulary. -/
#check (CochainComplex.plus C : ObjectProperty (CochainComplex C ℤ))
recall CochainComplex.plus_iff
#check (CochainComplex.Plus C)

/-- The object property of bounded-above cochain complexes. -/
protected def minus : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ n : ℤ, K.IsStrictlyLE n

lemma minus_iff (K : CochainComplex C ℤ) :
    CochainComplex.minus C K ↔ ∃ n : ℤ, K.IsStrictlyLE n := Iff.rfl

instance : (CochainComplex.minus C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨n, hn⟩
    exact ⟨n, isStrictlyLE_of_iso e n⟩

/-- The category `Comp^-(C)` of bounded-above cochain complexes. -/
abbrev Minus :=
  (CochainComplex.minus C).FullSubcategory

namespace Minus

/-- The inclusion `Comp^-(C) ⥤ Comp(C)` of bounded-above cochain complexes. -/
abbrev ι : Minus C ⥤ CochainComplex C ℤ :=
  ObjectProperty.ι _

/-- The inclusion `Comp^-(C) ⥤ Comp(C)` is fully faithful. -/
def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance (J : Type*) [SmallCategory J] [FinCategory J]
    [CategoryTheory.Limits.HasLimitsOfShape J C] :
    (CochainComplex.minus C).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ∀ j : J, (p.diag.obj j).IsStrictlyLE n := by
      choose n hn using p.prop_diag_obj
      refine ⟨Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by simp⟩, fun j ↦ ?_⟩
      have hnj :
          n j ≤ Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by simp⟩ :=
        Finset.le_max' _ _ <| Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_image.mpr ⟨j, by simp, rfl⟩
      haveI := hn j
      exact (p.diag.obj j).isStrictlyLE_of_le _ _ hnj
    refine ⟨n, ?_⟩
    rw [isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (HomologicalComplex.eval _ _ i) p.isLimit).hom_ext <| fun j ↦ by
      haveI := hn j
      exact (isZero_of_isStrictlyLE (p.diag.obj j) n i).eq_of_tgt _ _

instance (J : Type*) [SmallCategory J] [FinCategory J]
    [CategoryTheory.Limits.HasColimitsOfShape J C] :
    (CochainComplex.minus C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ∀ j : J, (p.diag.obj j).IsStrictlyLE n := by
      choose n hn using p.prop_diag_obj
      refine ⟨Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by simp⟩, fun j ↦ ?_⟩
      have hnj :
          n j ≤ Finset.max' (Finset.image n ⊤ ∪ {0}) ⟨0, by simp⟩ :=
        Finset.le_max' _ _ <| Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_image.mpr ⟨j, by simp, rfl⟩
      haveI := hn j
      exact (p.diag.obj j).isStrictlyLE_of_le _ _ hnj
    refine ⟨n, ?_⟩
    rw [isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isColimitOfPreserves (HomologicalComplex.eval _ _ i) p.isColimit).hom_ext <| fun j ↦ by
      haveI := hn j
      exact (isZero_of_isStrictlyLE (p.diag.obj j) n i).eq_of_src _ _

instance [CategoryTheory.Limits.HasFiniteLimits C] :
    CategoryTheory.Limits.HasFiniteLimits (Minus C) where
  out J _ _ := by infer_instance

instance [CategoryTheory.Limits.HasFiniteColimits C] :
    CategoryTheory.Limits.HasFiniteColimits (Minus C) where
  out J _ _ := by infer_instance

end Minus

/-- The object property of bounded cochain complexes. -/
protected def bounded : ObjectProperty (CochainComplex C ℤ) :=
  CochainComplex.plus C ⊓ CochainComplex.minus C

lemma bounded_iff (K : CochainComplex C ℤ) :
    CochainComplex.bounded C K ↔
      CochainComplex.plus C K ∧ CochainComplex.minus C K := Iff.rfl

/-- The category `Comp^b(C)` of bounded cochain complexes. -/
abbrev Bounded :=
  (CochainComplex.bounded C).FullSubcategory

namespace Bounded

/-- The inclusion `Comp^b(C) ⥤ Comp(C)` of bounded cochain complexes. -/
abbrev ι : Bounded C ⥤ CochainComplex C ℤ :=
  ObjectProperty.ι _

/-- The inclusion `Comp^b(C) ⥤ Comp(C)` is fully faithful. -/
def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance (J : Type*) [SmallCategory J] [FinCategory J]
    [CategoryTheory.Limits.HasLimitsOfShape J C] :
    (CochainComplex.bounded C).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro K ⟨p⟩
    refine ⟨?_, ?_⟩
    · exact (CochainComplex.plus C).prop_of_isLimit p.isLimit fun j ↦ (p.prop_diag_obj j).1
    · exact (CochainComplex.minus C).prop_of_isLimit p.isLimit fun j ↦ (p.prop_diag_obj j).2

instance (J : Type*) [SmallCategory J] [FinCategory J]
    [CategoryTheory.Limits.HasColimitsOfShape J C] :
    (CochainComplex.bounded C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro K ⟨p⟩
    refine ⟨?_, ?_⟩
    · exact (CochainComplex.plus C).prop_of_isColimit p.isColimit fun j ↦ (p.prop_diag_obj j).1
    · exact (CochainComplex.minus C).prop_of_isColimit p.isColimit fun j ↦ (p.prop_diag_obj j).2

instance [CategoryTheory.Limits.HasFiniteLimits C] :
    CategoryTheory.Limits.HasFiniteLimits (Bounded C) where
  out J _ _ := by infer_instance

instance [CategoryTheory.Limits.HasFiniteColimits C] :
    CategoryTheory.Limits.HasFiniteColimits (Bounded C) where
  out J _ _ := by infer_instance

end Bounded

end

section

variable [Preadditive C]

namespace Minus

instance [CategoryTheory.Limits.HasFiniteColimits C] :
    CategoryTheory.Limits.HasFiniteBiproducts (Minus C) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

instance [CategoryTheory.Limits.HasFiniteColimits C] :
    CategoryTheory.Limits.HasBinaryBiproducts (Minus C) :=
  hasBinaryBiproducts_of_finite_biproducts _

@[instance 10] instance [CategoryTheory.Limits.HasBinaryBiproducts C] :
    CategoryTheory.Limits.HasBinaryBiproducts (Minus C) := by
  let _ : CategoryTheory.Limits.HasBinaryCoproducts (Minus C) := by infer_instance
  exact HasBinaryBiproducts.of_hasBinaryCoproducts

end Minus

instance : (CochainComplex.minus C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨fun K ⟨k, hk⟩ ↦ ⟨k - n, K.isStrictlyLE_shift k n _ (by lia)⟩⟩

namespace Bounded

instance [CategoryTheory.Limits.HasFiniteColimits C] :
    CategoryTheory.Limits.HasFiniteBiproducts (Bounded C) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

instance [CategoryTheory.Limits.HasFiniteColimits C] :
    CategoryTheory.Limits.HasBinaryBiproducts (Bounded C) :=
  hasBinaryBiproducts_of_finite_biproducts _

@[instance 10] instance [CategoryTheory.Limits.HasBinaryBiproducts C] :
    CategoryTheory.Limits.HasBinaryBiproducts (Bounded C) := by
  let _ : CategoryTheory.Limits.HasBinaryCoproducts (Bounded C) := by infer_instance
  exact HasBinaryBiproducts.of_hasBinaryCoproducts

end Bounded

instance : (CochainComplex.bounded C).IsStableUnderShift ℤ := by
  refine ⟨fun n ↦ ?_⟩
  refine ⟨fun K hK ↦ ?_⟩
  exact ⟨(CochainComplex.plus C).le_shift n K hK.1,
    (CochainComplex.minus C).le_shift n K hK.2⟩

namespace Plus

instance [CategoryTheory.Limits.HasFiniteColimits C] :
    CategoryTheory.Limits.HasFiniteBiproducts (CochainComplex.Plus C) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

instance [CategoryTheory.Limits.HasFiniteColimits C] :
    CategoryTheory.Limits.HasBinaryBiproducts (CochainComplex.Plus C) :=
  hasBinaryBiproducts_of_finite_biproducts _

@[instance 10] instance [CategoryTheory.Limits.HasBinaryBiproducts C] :
    CategoryTheory.Limits.HasBinaryBiproducts (CochainComplex.Plus C) := by
  let _ : CategoryTheory.Limits.HasBinaryCoproducts (CochainComplex.Plus C) := by infer_instance
  exact HasBinaryBiproducts.of_hasBinaryCoproducts

end Plus

end

end CochainComplex

namespace CategoryTheory

scoped notation "Comp(" A:arg ")" => CochainComplex A ℤ
scoped notation "Comp⁺(" A:arg ")" => CochainComplex.Plus A
scoped notation "Comp⁻(" A:arg ")" => CochainComplex.Minus A
scoped notation "Compᵇ(" A:arg ")" => CochainComplex.Bounded A
scoped notation "K(" A:arg ")" => HomotopyCategory A (up ℤ)

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

/- Domain-style sampling:
- primary domain: bounded cochain-complex categories and their homotopy categories;
- relevant upstream owner declarations in this domain:
  `CochainComplex.plus`,
  `CochainComplex.plus_iff`,
  `CochainComplex.Plus`,
  `HomotopyCategory 𝒜 (up ℤ)`;
- source/core/bridge triage:
  `source-facing`: the textbook categories `Comp(𝒜)`, `Comp⁺(𝒜)`, `Comp⁻(𝒜)`, `Compᵇ(𝒜)`,
    `K(𝒜)`, `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)`;
  `core/canonical`: the owner categories `CochainComplex 𝒜 ℤ`, `CochainComplex.Plus 𝒜`,
    `CochainComplex.Minus 𝒜`, and `CochainComplex.Bounded 𝒜`;
  `bridge/view`: the bounded object properties and corresponding full subcategories of the ambient
    homotopy category `K(𝒜)`.

Primitive data is the cochain-complex category and its boundedness predicates. The owner layer is
therefore the bounded cochain-complex category itself. At the homotopy layer, the source-facing
categories `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)` are realized as bounded full subcategories of the ambient
homotopy category `K(𝒜)`, while the comparison functors from `Comp⁺(𝒜)`, `Comp⁻(𝒜)`, and
`Compᵇ(𝒜)` are separate bridge data.
-/

/- Definition 13.8.1: the textbook category `\mathrm{Comp}(\mathcal A)=\mathrm{CoCh}(\mathcal A)`
is the canonical category `CochainComplex 𝒜 ℤ` of cochain complexes in the additive category
`𝒜`; the boundedness conditions and the associated owner categories are recorded below in terms of
this canonical API. -/
#check (Comp(𝒜))

/- Companion recall: the textbook bounded-below condition on a cochain complex is the canonical
object property `CochainComplex.plus 𝒜`, characterized by `CochainComplex.plus_iff`. -/
#check (CochainComplex.plus 𝒜 : ObjectProperty (Comp(𝒜)))
recall CochainComplex.plus_iff

/- Companion recall: the category `\mathrm{Comp}^{+}(\mathcal A)` of bounded-below cochain
complexes is the canonical owner `CochainComplex.Plus 𝒜`. -/
#check (Comp⁺(𝒜))

/- Companion recall: the category `\mathrm{Comp}^{-}(\mathcal A)` of bounded-above cochain
complexes is the owner `CochainComplex.Minus 𝒜`, characterized by `CochainComplex.minus_iff`. -/
#check (CochainComplex.minus 𝒜 : ObjectProperty (Comp(𝒜)))
recall CochainComplex.minus_iff
#check (Comp⁻(𝒜))

/- Companion recall: the category `\mathrm{Comp}^{b}(\mathcal A)` of bounded cochain complexes
is the owner `CochainComplex.Bounded 𝒜`, characterized by `CochainComplex.bounded_iff`. -/
#check (CochainComplex.bounded 𝒜 : ObjectProperty (Comp(𝒜)))
recall CochainComplex.bounded_iff
#check (Compᵇ(𝒜))

/- The zero cochain complex lies in each boundedness owner. These primitive `ContainsZero`
witnesses let the bounded cochain-complex categories inherit zero objects. -/
theorem zero_mem_plus (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]
    [CategoryTheory.Limits.HasZeroObject 𝒜] :
    CochainComplex.plus 𝒜 (HomologicalComplex.zero : Comp(𝒜)) := by
  refine ⟨0, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (HomologicalComplex.eval 𝒜 (up ℤ) i).map_isZero
    (HomologicalComplex.isZero_zero : IsZero (HomologicalComplex.zero : Comp(𝒜)))

theorem zero_mem_minus (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]
    [CategoryTheory.Limits.HasZeroObject 𝒜] :
    CochainComplex.minus 𝒜 (HomologicalComplex.zero : Comp(𝒜)) := by
  refine ⟨0, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (HomologicalComplex.eval 𝒜 (up ℤ) i).map_isZero
    (HomologicalComplex.isZero_zero : IsZero (HomologicalComplex.zero : Comp(𝒜)))

theorem zero_mem_bounded (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]
    [CategoryTheory.Limits.HasZeroObject 𝒜] :
    CochainComplex.bounded 𝒜 (HomologicalComplex.zero : Comp(𝒜)) :=
  ⟨zero_mem_plus 𝒜, zero_mem_minus 𝒜⟩

instance [CategoryTheory.Limits.HasZeroObject 𝒜] :
    (CochainComplex.plus 𝒜).ContainsZero where
  exists_zero := ⟨_, HomologicalComplex.isZero_zero, zero_mem_plus 𝒜⟩

instance [CategoryTheory.Limits.HasZeroObject 𝒜] :
    (CochainComplex.minus 𝒜).ContainsZero where
  exists_zero := ⟨_, HomologicalComplex.isZero_zero, zero_mem_minus 𝒜⟩

instance [CategoryTheory.Limits.HasZeroObject 𝒜] :
    (CochainComplex.bounded 𝒜).ContainsZero where
  exists_zero := ⟨_, HomologicalComplex.isZero_zero, zero_mem_bounded 𝒜⟩

section

variable (𝒜)

/- The textbook homotopy category `K(\mathcal A)` is the canonical homotopy category
`HomotopyCategory 𝒜 (ComplexShape.up ℤ)` of cochain complexes in `𝒜`. -/
#check (K(𝒜))

/-- The bounded-below view of `K^+(\mathcal A)` inside `K(\mathcal A)`. -/
abbrev boundedBelowHomotopyProperty : ObjectProperty (K(𝒜)) :=
  fun K ↦ CochainComplex.plus 𝒜 K.as

/-- The bounded-above view of `K^-(\mathcal A)` inside `K(\mathcal A)`. -/
abbrev boundedAboveHomotopyProperty : ObjectProperty (K(𝒜)) :=
  fun K ↦ CochainComplex.minus 𝒜 K.as

/-- The bounded view of `K^b(\mathcal A)` inside `K(\mathcal A)`. -/
abbrev boundedHomotopyProperty : ObjectProperty (K(𝒜)) :=
  fun K ↦ CochainComplex.bounded 𝒜 K.as

/- The textbook notations `K^+(\mathcal A)`, `K^-(\mathcal A)`, and `K^b(\mathcal A)` are the
corresponding full subcategories of `K(\mathcal A)` cut out by the boundedness object
properties above. -/
scoped notation "K⁺(" A:arg ")" =>
  ObjectProperty.FullSubcategory
    (boundedBelowHomotopyProperty A :
      ObjectProperty (HomotopyCategory A (up ℤ)))
scoped notation "K⁻(" A:arg ")" =>
  ObjectProperty.FullSubcategory
    (boundedAboveHomotopyProperty A :
      ObjectProperty (HomotopyCategory A (up ℤ)))
scoped notation "Kᵇ(" A:arg ")" =>
  ObjectProperty.FullSubcategory
    (boundedHomotopyProperty A :
      ObjectProperty (HomotopyCategory A (up ℤ)))

/- Companion recall: the bounded-below homotopy category `K^+(\mathcal A)` is the full
subcategory of `K(\mathcal A)` cut out by the canonical bounded-below object property above. -/
#check (K⁺(𝒜))

/- Companion recall: the bounded-above homotopy category `K^-(\mathcal A)` is the full
subcategory of `K(\mathcal A)` cut out by the canonical bounded-above object property above. -/
#check (K⁻(𝒜))

/- Companion recall: the bounded homotopy category `K^b(\mathcal A)` is the full subcategory of
`K(\mathcal A)` cut out by the canonical bounded object property above. -/
#check (Kᵇ(𝒜))

namespace ObjectProperty.FullSubcategory

/-- The `n`-th cochain term of an object in a full subcategory of `K(\mathcal A)`. -/
def term {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
    {P : ObjectProperty (K(𝒜))} (A : P.FullSubcategory) (n : ℤ) : 𝒜 :=
  A.obj.as.X n

end ObjectProperty.FullSubcategory

/- The bounded cochain-complex categories are the primitive owners on the complex side. The
functors below are the explicit quotient bridges from those categories to the source-facing bounded
homotopy categories inside `K(𝒜)`. -/
/-- The canonical quotient bridge `Comp^+(\mathcal A) ⥤ K^+(\mathcal A)` from the owner category
of bounded-below cochain complexes to its bounded-below view inside `K(\mathcal A)`. -/
abbrev boundedBelowHomotopyQuotient :
    Comp⁺(𝒜) ⥤ K⁺(𝒜) :=
  ObjectProperty.lift (boundedBelowHomotopyProperty 𝒜)
    (CochainComplex.Plus.ι 𝒜 ⋙ HomotopyCategory.quotient 𝒜 (up ℤ))
    (fun K ↦ by
      simpa [boundedBelowHomotopyProperty] using K.property)

/-- The canonical quotient bridge `Comp^-(\mathcal A) ⥤ K^-(\mathcal A)` from the owner category
of bounded-above cochain complexes to its bounded-above view inside `K(\mathcal A)`. -/
abbrev boundedAboveHomotopyQuotient :
    Comp⁻(𝒜) ⥤ K⁻(𝒜) :=
  ObjectProperty.lift (boundedAboveHomotopyProperty 𝒜)
    (CochainComplex.Minus.ι 𝒜 ⋙ HomotopyCategory.quotient 𝒜 (up ℤ))
    (fun K ↦ by
      simpa [boundedAboveHomotopyProperty] using K.property)

/-- The canonical quotient bridge `Comp^b(\mathcal A) ⥤ K^b(\mathcal A)` from the owner category
of bounded cochain complexes to its bounded view inside `K(\mathcal A)`. -/
abbrev boundedHomotopyQuotient :
    Compᵇ(𝒜) ⥤ Kᵇ(𝒜) :=
  ObjectProperty.lift (boundedHomotopyProperty 𝒜)
    (CochainComplex.Bounded.ι 𝒜 ⋙ HomotopyCategory.quotient 𝒜 (up ℤ))
    (fun K ↦ by
      simpa [boundedHomotopyProperty] using K.property)

end

end CategoryTheory
