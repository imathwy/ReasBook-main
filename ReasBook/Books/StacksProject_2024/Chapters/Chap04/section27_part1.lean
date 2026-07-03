import Mathlib
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall
import «StacksProject_2024».«Chap04».«4_27_7_1»
import «StacksProject_2024».«Chap04».«Lemma_4_19_2»

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_27_1 (from Chap04) -/
universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling:
- primary domain: calculus of fractions for morphism properties
- core/canonical owners already present in mathlib:
  `MorphismProperty.HasLeftCalculusOfFractions`,
  `MorphismProperty.HasRightCalculusOfFractions`,
  `MorphismProperty.IsMultiplicative`,
  `MorphismProperty.Q`
- best owner abstraction: the source notion “multiplicative system” is not a third owner; it is
  the direct conjunction of the two canonical calculus-of-fractions owners
- primitive data: exactly the left and right calculus-of-fractions owner instances
- derived API: the direct source-facing conjunction statement

Source/core/bridge triage:
- `source-facing`: the Stacks phrase “multiplicative system”
- `core/canonical`: `W.HasLeftCalculusOfFractions` and `W.HasRightCalculusOfFractions`
- `bridge/view`: the direct conjunction `W.HasLeftCalculusOfFractions ∧
  W.HasRightCalculusOfFractions`
-/

/- Companion recall: a left multiplicative system on a category is the canonical mathlib notion
`MorphismProperty.HasLeftCalculusOfFractions`, encoding closure under identities and composition,
left Ore completion, and left cancellation. -/
recall HasLeftCalculusOfFractions

/- Companion recall: a right multiplicative system on a category is the canonical mathlib notion
`MorphismProperty.HasRightCalculusOfFractions`, encoding closure under identities and composition,
right Ore completion, and right cancellation. -/
recall HasRightCalculusOfFractions

variable (W : MorphismProperty C)

/- Definition 4.27.1: a set of arrows in a category is a multiplicative system if it is both a
left multiplicative system and a right multiplicative system, i.e. if the corresponding morphism
property has both the left and right calculus of fractions. -/
#check W.HasLeftCalculusOfFractions ∧ W.HasRightCalculusOfFractions

/-- The class of isomorphisms in any category has both left and right calculus of fractions. -/
instance : (isomorphisms C).HasLeftCalculusOfFractions := by
  simpa using Adjunction.hasLeftCalculusOfFractions' (Adjunction.id : 𝟭 C ⊣ 𝟭 C)

instance : (isomorphisms C).HasRightCalculusOfFractions := by
  simpa using Adjunction.hasRightCalculusOfFractions' (Adjunction.id : 𝟭 C ⊣ 𝟭 C)

end MorphismProperty
end CategoryTheory

/-! ### Lemma_4_27_2 (from Chap04) -/
universe v u

namespace CategoryTheory

open MorphismProperty
open MorphismProperty.LeftFraction
open MorphismProperty.LeftFraction.Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable {X Y Z : C}

/- Domain-style sampling for Lemma 4.27.2:
- primary domain: left-fraction localizations and their canonical equivalence relation;
- source-facing content: the equivalence relation on left fractions and the fact that composition
  of represented morphisms depends only on equivalence classes;
- core/canonical owner abstraction: `MorphismProperty.LeftFractionRel` together with the induced
  morphism
  `LeftFraction.Localization.homMk : W.LeftFraction X Y → (Q W).obj X ⟶ (Q W).obj Y`
  in `W.Localization`;
- upstream owner facts inspected before refining:
  `MorphismProperty.equivalenceLeftFractionRel`,
  `LeftFraction.map_eq_iff`,
  `LeftFraction.Localization.homMk_eq_of_leftFractionRel`,
  `Category.assoc`.

Primitive data: a pair of left fractions and proofs that they are related by `LeftFractionRel`.
Derived API: the induced localization morphism `homMk` and equality of such morphisms coming from
`homMk_eq_of_leftFractionRel`. The source-facing well-definedness statement should therefore use
`homMk` rather than repeat the generic map expression through `W.Q`.

Source/core/bridge triage:
- `source-facing`: `leftFractionComp_wellDefined`;
- `core/canonical`: `LeftFractionRel`, `equivalenceLeftFractionRel`, and `homMk`;
- `bridge/view`: the passage from equivalence-class representatives to equality after composition.
-/

/- Canonical recall: for a left multiplicative system `W`, the relation on left fractions is the
canonical relation `LeftFractionRel`, and its equivalence-relation statement is exactly
`equivalenceLeftFractionRel`. -/
recall equivalenceLeftFractionRel

-- Proof sketch: convert both relation hypotheses to equalities of the induced localization
-- morphisms via the owner theorem `LeftFraction.Localization.homMk_eq_of_leftFractionRel`,
-- then use congruence of composition.
/-- Lemma 4.27.2: composition of left fractions is well defined on equivalence classes. -/
theorem leftFractionComp_wellDefined
    (z₁ z₁' : W.LeftFraction X Y) (z₂ z₂' : W.LeftFraction Y Z)
    (h₁ : LeftFractionRel z₁ z₁') (h₂ : LeftFractionRel z₂ z₂') :
    homMk z₁ ≫ homMk z₂ = homMk z₁' ≫ homMk z₂' := by
  -- Translate the source-level relation on the first representative into equality in the
  -- localization.
  have hhom₁ : homMk z₁ = homMk z₁' := homMk_eq_of_leftFractionRel z₁ z₁' h₁
  -- Do the same for the second representative so the target equality becomes a formal rewrite.
  have hhom₂ : homMk z₂ = homMk z₂' := homMk_eq_of_leftFractionRel z₂ z₂' h₂
  -- Once both factors agree in the localization, composition agrees by congruence.
  calc
    homMk z₁ ≫ homMk z₂ = homMk z₁' ≫ homMk z₂ := by rw [hhom₁]
    _ = homMk z₁' ≫ homMk z₂' := by rw [hhom₂]

/- Canonical recall: composition in the left-fraction localization is associative; this is the
canonical associativity axiom `CategoryTheory.Category.assoc` in `W.Localization`. -/
recall Category.assoc

/- Canonical recall: the identity morphism is a left unit for composition in `W.Localization`;
this is the canonical axiom `CategoryTheory.Category.id_comp`. -/
recall Category.id_comp

/- Canonical recall: the identity morphism is a right unit for composition in `W.Localization`;
this is the canonical axiom `CategoryTheory.Category.comp_id`. -/
recall Category.comp_id

end CategoryTheory

/-! ### Remark_4_27_3 (from Chap04) -/
open CategoryTheory
open CategoryTheory.MorphismProperty
open OreLocalization

universe u

variable {R : Type u}

namespace CategoryTheory.SingleObj

variable [Monoid R]

/-- The morphism property on the one-object category `SingleObj R` induced by a submonoid
`S : Submonoid R`. -/
def submonoidProperty (S : Submonoid R) : MorphismProperty (SingleObj R) :=
  fun _ _ f ↦ f ∈ S

@[simp]
theorem submonoidProperty_iff (S : Submonoid R) {X Y : SingleObj R} (f : X ⟶ Y) :
    submonoidProperty S f ↔ f ∈ S :=
  Iff.rfl

section Monoid

variable (S : Submonoid R)

local notation "W" => submonoidProperty S

private def endHom {M : Type*} [Monoid M] {C : Type*} [Category C]
    (F : SingleObj M ⥤ C) : M →* End (F.obj (star M)) where
  toFun m := F.map m
  map_one' := by simpa [id_as_one] using F.map_id (star M)
  map_mul' m n := by
    simpa [comp_as_mul] using F.map_comp n m

/- Domain-style sampling for Remark 4.27.3:
- primary domain: Ore localization and categorical localization on the one-object category
  `SingleObj R`;
- declarations inspected:
  `SingleObj.submonoidProperty`,
  `MorphismProperty.IsMultiplicative`,
  `OreLocalization.OreSet`,
  `OreLocalization.nonempty_oreSet_iff`,
  `Functor.IsLocalization`,
  `Localization.equivalenceFromModel`;
- best owner abstractions:
  `(SingleObj.submonoidProperty S).IsMultiplicative` for the unconditional MS1 content,
  `OreSet S` for the monoid-side left denominator data, and
  `(numeratorHom.toFunctor : SingleObj R ⥤ SingleObj R[S⁻¹]).IsLocalization
    (SingleObj.submonoidProperty S)`
  for the categorical localization statement;
- primitive data: the submonoid `S` and the induced morphism property
  `SingleObj.submonoidProperty S` on `SingleObj R`;
- derived API: the multiplicative-system bridge `W.IsMultiplicative`, the left/right
  denominator conditions, the induced calculus-of-fractions structures, and the localization
  equivalence supplied by `Localization.equivalenceFromModel`.

This item is a `bridge/view`: it translates the source-facing denominator conditions into the
canonical owner objects `(SingleObj.submonoidProperty S).IsMultiplicative`, `OreSet S`, and
`Functor.IsLocalization`. The public API should therefore use those owners directly rather than
parallel wrapper declarations or `Nonempty (OreSet S)` shells. -/

/-- Remark 4.27.3, MS1 clause: for a submonoid `S` of a monoid `R`, the induced morphism
property on the one-object category `SingleObj R` is multiplicative. -/
@[instance]
theorem submonoidProperty_isMultiplicative : (submonoidProperty S).IsMultiplicative := by
  exact
    { id_mem := fun _ ↦ show (1 : R) ∈ S from S.one_mem
      comp_mem := fun f g hf hg ↦ by
        simpa [comp_as_mul] using S.mul_mem hg hf }

-- Proof sketch: unwind `HasRightCalculusOfFractions` for the morphism property defined by `S` on
-- `SingleObj R`; because there is only one object and composition is reversed multiplication, the
-- right Ore-completion and right-cancellation axioms become exactly the right permutable and
-- right reversible conditions.
/-- Companion translation of the right calculus-of-fractions axioms on `SingleObj R` into the
usual right denominator-set conditions on the submonoid `S`. -/
theorem hasRightCalculusOfFractions_iff_rightDenominatorConditions :
    (submonoidProperty S).HasRightCalculusOfFractions ↔
      (∀ (r : R) (s : S), ∃ (r' : R) (s' : S), r * s' = s * r') ∧
        ∀ (r₁ r₂ : R) (s : S), s * r₁ = s * r₂ → ∃ s' : S, r₁ * s' = r₂ * s' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro r s
      let φ : LeftFraction W (star R) (star R) :=
        { Y' := star R
          f := r
          s := (s : R)
          hs := s.2 }
      obtain ⟨ψ, hψ⟩ := h.exists_rightFraction φ
      refine ⟨ψ.f, ⟨ψ.s, ψ.hs⟩, ?_⟩
      simpa [comp_as_mul] using hψ
    · intro r₁ r₂ s hs
      let f₁ : star R ⟶ star R := r₁
      let f₂ : star R ⟶ star R := r₂
      let s₀ : star R ⟶ star R := s
      obtain ⟨_, t, ht, ht_eq⟩ :=
        h.ext f₁ f₂ s₀ s.2 (by simpa [f₁, f₂, s₀, comp_as_mul] using hs)
      refine ⟨⟨t, ht⟩, ?_⟩
      simpa [f₁, f₂, s₀, comp_as_mul] using ht_eq
  · rintro ⟨hOre, hCancel⟩
    refine
      { toIsMultiplicative := inferInstance
        exists_rightFraction := ?_
        ext := ?_ }
    · intro X Y φ
      obtain ⟨r', s', hs'⟩ := hOre φ.f ⟨φ.s, φ.hs⟩
      refine ⟨{ X' := star R, s := (s' : R), hs := s'.2, f := r' }, ?_⟩
      simpa [comp_as_mul] using hs'
    · intro X Y Y' f₁ f₂ s hs h_eq
      obtain ⟨t, ht⟩ := hCancel f₁ f₂ ⟨s, hs⟩ (by simpa [comp_as_mul] using h_eq)
      refine ⟨star R, (t : R), t.2, ?_⟩
      simpa [comp_as_mul] using ht

-- Proof sketch: with an `OreSet S`, the canonical owner fields `ore_right_cancel`, `oreNum`,
-- `oreDenom`, and `ore_eq` supply exactly the extension and Ore-completion data required by
-- `HasLeftCalculusOfFractions` for the morphism property `W` on `SingleObj R`.
/-- Remark 4.27.3, first clause, owner-level direction: the canonical left Ore-set structure
`OreSet S` induces a left calculus of fractions on `SingleObj R` for the morphism property coming
from `S`. -/
@[instance]
theorem submonoidProperty_hasLeftCalculusOfFractions [OreSet S] :
    (submonoidProperty S).HasLeftCalculusOfFractions := by
  exact
    { toIsMultiplicative := inferInstance
      exists_leftFraction := by
        intro X Y φ
        refine ⟨.mk (oreNum φ.f ⟨φ.s, φ.hs⟩) (oreDenom φ.f ⟨φ.s, φ.hs⟩)
          (oreDenom φ.f ⟨φ.s, φ.hs⟩).2, ?_⟩
        simpa [comp_as_mul] using ore_eq φ.f ⟨φ.s, φ.hs⟩
      ext := by
        intro X' X Y f₁ f₂ s hs h_eq
        obtain ⟨t, ht⟩ := ore_right_cancel f₁ f₂ ⟨s, hs⟩
          (by simpa [comp_as_mul] using h_eq)
        refine ⟨star R, (t : R), t.2, ?_⟩
        simpa [comp_as_mul] using ht }

-- Proof sketch: the forward implication is obtained by unwinding the left-fraction axioms on
-- `SingleObj R`; conversely, the denominator conditions are exactly `nonempty_oreSet_iff`, and
-- any resulting `OreSet S` feeds the instance above.
/-- Companion reformulation of Remark 4.27.3, first clause, in the traditional left
denominator-set conditions. -/
theorem hasLeftCalculusOfFractions_iff_leftDenominatorConditions :
    (submonoidProperty S).HasLeftCalculusOfFractions ↔
      (∀ (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s → ∃ s' : S, s' * r₁ = s' * r₂) ∧
        ∀ (r : R) (s : S), ∃ (r' : R) (s' : S), s' * r = r' * s := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro r₁ r₂ s hs
      let f₁ : star R ⟶ star R := r₁
      let f₂ : star R ⟶ star R := r₂
      let s₀ : star R ⟶ star R := s
      obtain ⟨_, t, ht, ht_eq⟩ :=
        h.ext f₁ f₂ s₀ s.2 (by simpa [f₁, f₂, s₀, comp_as_mul] using hs)
      refine ⟨⟨t, ht⟩, ?_⟩
      simpa [f₁, f₂, s₀, comp_as_mul] using ht_eq
    · intro r s
      let φ : RightFraction W (star R) (star R) :=
        { X' := star R
          s := (s : R)
          hs := s.2
          f := r }
      obtain ⟨ψ, hψ⟩ := h.exists_leftFraction φ
      refine ⟨ψ.f, ⟨ψ.s, ψ.hs⟩, ?_⟩
      simpa [comp_as_mul] using hψ
  · intro h
    rw [← nonempty_oreSet_iff] at h
    rcases h with ⟨hS⟩
    letI : OreSet S := hS
    exact inferInstance

private noncomputable def oreUnitHom {C : Type*} [Category C] (F : SingleObj R ⥤ C)
    (hF : (submonoidProperty S).IsInvertedBy F) : S →* Units (End (F.obj (star R))) :=
  Units.liftRight ((endHom F).comp S.subtype)
    (fun s ↦ by
      let f : star R ⟶ star R := s
      letI : IsIso (F.map f) := hF f s.2
      exact ⟨F.map f, inv (F.map f), by simp, by simp⟩)
    fun _ ↦ rfl

private def numeratorUnitHom {C : Type*} [Category C] [OreSet S]
    (F : SingleObj R[S⁻¹] ⥤ C) : S →* Units (End (F.obj (star R[S⁻¹]))) :=
  Units.liftRight ((endHom F).comp (numeratorHom.comp S.subtype))
    (fun s ↦ Units.map (endHom F) (numeratorUnit s))
    fun s ↦ by
      change (endHom F) ((s : R) /ₒ (1 : S)) = (endHom F) ((s : R) /ₒ (1 : S))
      rfl

@[simp]
private theorem coe_oreUnitHom {C : Type*} [Category C] (F : SingleObj R ⥤ C)
    (hF : (submonoidProperty S).IsInvertedBy F) (s : S) :
    ↑(oreUnitHom S F hF s) = endHom F s := by
  simp [oreUnitHom, endHom]

@[simp]
private theorem coe_numeratorUnitHom {C : Type*} [Category C] [OreSet S]
    (F : SingleObj R[S⁻¹] ⥤ C) (s : S) :
    ↑(numeratorUnitHom S F s) = endHom F (numeratorHom (s : R)) := by
  simp [numeratorUnitHom, endHom, numeratorHom_apply]

@[simp]
private theorem endHom_comp_numerator {C : Type*} [Category C] [OreSet S]
    (F : SingleObj R[S⁻¹] ⥤ C) (s : S) :
    endHom (numeratorHom.toFunctor ⋙ F) s = endHom F (numeratorHom (s : R)) := by
  rfl

private noncomputable def oreLocalizationStrictUniversalPropertyFixedTarget
    (E : Type*) [Category E] [OreSet S] :
    Localization.StrictUniversalPropertyFixedTarget
      ((numeratorHom : R →* R[S⁻¹]).toFunctor) (submonoidProperty S) E
    where
  inverts := by
    intro X Y f hf
    cases X
    cases Y
    let g : End (star R[S⁻¹]) := numeratorHom.toFunctor.map f
    have hunit :
        IsUnit g := by
      simpa using numerator_isUnit ⟨f, hf⟩
    exact (CategoryTheory.isUnit_iff_isIso g).1 hunit
  lift F hF := by
    let φ := endHom F
    let φS := oreUnitHom S F hF
    let hφ : ∀ s : S, φ s = (φS s : End (F.obj (star R))) := fun s ↦ by
      simp [φ, φS]
    exact functor (universalMulHom φ φS hφ)
  fac F hF := by
    let φ := endHom F
    let φS := oreUnitHom S F hF
    let hφ : ∀ s : S, φ s = (φS s : End (F.obj (star R))) := fun s ↦ by
      simp [φ, φS]
    change numeratorHom.toFunctor ⋙ functor (universalMulHom φ φS hφ) = F
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro X Y f
    cases X
    cases Y
    change universalMulHom φ φS hφ (numeratorHom f) = eqToHom rfl ≫ F.map f ≫ eqToHom rfl.symm
    simpa [φ] using
      (universalMulHom_commutes φ φS hφ :
        universalMulHom φ φS hφ (numeratorHom f) = φ f)
  uniq F₁ F₂ hFF := by
    let φ₁ := endHom F₁
    let φS := numeratorUnitHom S F₁
    let hφ : ∀ s : S,
        (endHom (numeratorHom.toFunctor ⋙ F₁)) s =
          (φS s : End (F₁.obj (star R[S⁻¹]))) := fun s ↦ by
      simpa [φS] using (endHom_comp_numerator S F₁ s)
    have hX : F₁.obj (star R[S⁻¹]) = F₂.obj (star R[S⁻¹]) :=
      Functor.congr_obj hFF (star R)
    let ψ₂ : R[S⁻¹] →* End (F₁.obj (star R[S⁻¹])) :=
      { toFun := fun x ↦ eqToHom hX ≫ F₂.map x ≫ eqToHom hX.symm
        map_one' := by
          change eqToHom hX ≫ F₂.map (𝟙 (star R[S⁻¹])) ≫ eqToHom hX.symm = 𝟙 _
          simp
        map_mul' := by
          intro x y
          let fx : star R[S⁻¹] ⟶ star R[S⁻¹] := x
          let fy : star R[S⁻¹] ⟶ star R[S⁻¹] := y
          let a : End (F₁.obj (star R[S⁻¹])) := eqToHom hX ≫ F₂.map x ≫ eqToHom hX.symm
          let b : End (F₁.obj (star R[S⁻¹])) := eqToHom hX ≫ F₂.map y ≫ eqToHom hX.symm
          change eqToHom hX ≫ F₂.map (x * y) ≫ eqToHom hX.symm = a * b
          rw [show x * y = fy ≫ fx by simp [fx, fy, comp_as_mul], F₂.map_comp]
          simp [a, b, CategoryTheory.End.mul_def, Category.assoc, fx, fy] }
    have hφ₁ :
        φ₁ = universalMulHom (endHom (numeratorHom.toFunctor ⋙ F₁)) φS hφ :=
      universalMulHom_unique (endHom (numeratorHom.toFunctor ⋙ F₁)) φS hφ φ₁
        (fun r ↦ rfl)
    have hnum :
        ∀ r : R, ψ₂ (numeratorHom r) = (endHom (numeratorHom.toFunctor ⋙ F₁)) r := by
      intro r
      simpa [ψ₂, endHom] using
        (Functor.congr_hom hFF r).symm
    have hψ₂ :
        ψ₂ = universalMulHom (endHom (numeratorHom.toFunctor ⋙ F₁)) φS hφ :=
      universalMulHom_unique (endHom (numeratorHom.toFunctor ⋙ F₁)) φS hφ ψ₂ hnum
    have hmapHom : φ₁ = ψ₂ := hφ₁.trans hψ₂.symm
    refine CategoryTheory.Functor.ext (fun _ ↦ hX) ?_
    intro X Y x
    cases X
    cases Y
    have hx := congrArg (fun h : R[S⁻¹] →* End (F₁.obj (star R[S⁻¹])) ↦ h x) hmapHom
    simpa [φ₁, ψ₂, endHom] using hx

section OreSet

variable [OreSet S]

/-- Remark 4.27.3, second clause: for a left denominator set `S`, the canonical functor from the
one-object category of `R` to the one-object category of the Ore localization `R[S⁻¹]` is a
localization of `SingleObj R` at the morphisms coming from `S`. -/
instance oreLocalizationFunctor_isLocalization :
    (numeratorHom.toFunctor : SingleObj R ⥤ SingleObj R[S⁻¹]).IsLocalization
      (submonoidProperty S) := by
  exact Functor.IsLocalization.mk' _ _
    (oreLocalizationStrictUniversalPropertyFixedTarget S (SingleObj R[S⁻¹]))
    (oreLocalizationStrictUniversalPropertyFixedTarget S
      (MorphismProperty.Localization (submonoidProperty S)))

/- Remark 4.27.3, second clause: once the canonical functor
`numeratorHom.toFunctor` is recognized as a localization at the morphisms coming from `S`, the
resulting equivalence with the constructed localization is exactly the canonical
`Localization.equivalenceFromModel`. -/
#check
  (Localization.equivalenceFromModel
      (numeratorHom.toFunctor : SingleObj R ⥤ SingleObj R[S⁻¹]) (submonoidProperty S) :
    MorphismProperty.Localization (submonoidProperty S) ≌ SingleObj R[S⁻¹])

end OreSet

end Monoid

end CategoryTheory.SingleObj

/-! ### Definition_4_27_4 (from Chap04) -/
universe v u

namespace CategoryTheory
namespace MorphismProperty

open LeftFraction
open LeftFraction.Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]

/- Domain-style sampling for Definition 4.27.4:
- primary domain: left-fraction localizations of categories with a left calculus of fractions
- upstream owner declarations inspected:
  `LeftFraction.Localization.homMk`,
  `LeftFraction.Localization.Q_map_comp_Qinv`,
  `LeftFraction.Localization.homMk_eq_iff_leftFractionRel`,
  `LeftFraction.Localization.Qinv`
- best owner abstraction: `LeftFraction.Localization.homMk : W.LeftFraction X Y → (Q W).obj X ⟶
  (Q W).obj Y`

Primitive data: a left fraction `mk f s hs`.
Derived API: the source-facing notation `s⁻¹ f`, expanding directly to the canonical owner
`homMk (mk f s hs)`. The bridge to the composite `Q(f) ≫ Qinv(s)` is already owned upstream by
`LeftFraction.Localization.Q_map_comp_Qinv`, so this file reuses that theorem directly and keeps
only the source-facing notation surface.

Source/core/bridge triage:
- `source-facing`: the textbook fraction notation `s⁻¹ f`;
- `core/canonical`: the owner morphism `homMk (mk f s hs)` in `LeftFraction.Localization W`;
- `bridge/view`: the owner theorem `Q_map_comp_Qinv`, reused directly below. -/

/-- Definition 4.27.4: for a left multiplicative system `W`, a morphism `f : X ⟶ Y'`, and a
denominator `s : Y ⟶ Y'` in `W`, `left_fraction_hom W f s hs` is the morphism
`s⁻¹ f : (LeftFraction.Localization.Q W).obj X ⟶ (LeftFraction.Localization.Q W).obj Y`
in the left-fraction localization represented by the roof `(f, s)`. -/
noncomputable abbrev left_fraction_hom {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (LeftFraction.Localization.Q W).obj X ⟶ (LeftFraction.Localization.Q W).obj Y :=
  homMk (mk f s hs)

namespace LeftFractionNotation

scoped notation:80 s "⁻¹ " f:81 => left_fraction_hom _ f s ‹_›

end LeftFractionNotation

open scoped LeftFractionNotation

/-- The textbook fraction `s⁻¹ f` agrees with the canonical composite `Q(f) ≫ Qinv(s)` in the
left-fraction localization. -/
-- Proof sketch: unfold `left_fraction_hom` and apply the owner theorem
-- `LeftFraction.Localization.Q_map_comp_Qinv`.
theorem left_fraction_hom_eq_Q_map_comp_Qinv {X Y Y' : C}
    (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    left_fraction_hom W f s hs =
      (LeftFraction.Localization.Q W).map f ≫ Qinv s hs := by
  -- Unfold the source-facing roof notation to the canonical localization morphism.
  simpa [left_fraction_hom] using
    (LeftFraction.Localization.Q_map_comp_Qinv (W := W) f s hs).symm

end MorphismProperty
end CategoryTheory

/-! ### Lemma_4_27_5 (from Chap04) -/
open CategoryTheory
open MorphismProperty

universe u v w w'

namespace CategoryTheory
namespace Localization

variable {C : Type u} {D : Type w'} [Category.{v} C] [Category D]
variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
variable [W.HasLeftCalculusOfFractions]

/- Domain-style sampling for Lemma 4.27.5:
- primary domain: localization by a left calculus of fractions;
- inspected owner declarations:
  `Localization.exists_leftFraction`,
  `MorphismProperty.RightFraction.leftFraction`,
  `MorphismProperty.RightFraction.leftFraction_fac`,
  `MorphismProperty.LeftFraction.map_eq_iff`,
  `Localization.exists_leftFraction₂`;
- best owner abstraction: `MorphismProperty.LeftFraction` as the canonical representation of a
  localized morphism by a roof;
- primitive data: a finite family `g i : L.obj (X i) ⟶ L.obj Y`;
- derived API: existence of representatives with one common denominator.

Source/core/bridge triage:
- `source-facing`: `exists_leftFraction_finite`;
- `core/canonical`: the owner-level left-fraction localization API above;
- `bridge/view`: the operational `Finset`-indexed common-denominator statement
  used internally to derive the finite theorem. -/

/-- Helper for Lemma 4.27.5: postcomposing a left-fraction representative to a common
refinement of its denominator does not change the represented localized morphism. -/
private lemma leftFraction_map_postcomp_eq {X Y Z : C} (φ : W.LeftFraction X Y)
    (t : φ.Y' ⟶ Z) (ht : W (φ.s ≫ t)) :
    φ.map L (inverts L W) =
      (LeftFraction.mk (φ.f ≫ t) (φ.s ≫ t) ht).map L (inverts L W) := by
  -- Compare the two roofs using the obvious common refinement through `Z`.
  exact (MorphismProperty.LeftFraction.map_eq_iff (L := L) (W := W) _ _).2 <| by
    refine ⟨Z, t, 𝟙 Z, ?_, ?_, ht⟩
    · simp
    · simp

/-- Helper for Lemma 4.27.5: an Ore-square equality lets one replace the denominator of a
left-fraction representative by an equal common refinement. -/
private lemma leftFraction_map_eq_of_ore_refinement {X Y Z Z' : C} (φ : W.LeftFraction X Y)
    (a : φ.Y' ⟶ Z') (b : Z ⟶ Z') {s₁ : Y ⟶ Z} (ht : W (s₁ ≫ b))
    (h : φ.s ≫ a = s₁ ≫ b) :
    φ.map L (inverts L W) =
      (LeftFraction.mk (φ.f ≫ a) (s₁ ≫ b) ht).map L (inverts L W) := by
  -- Use the Ore-square identity as the comparison witness between the two roofs.
  exact (MorphismProperty.LeftFraction.map_eq_iff (L := L) (W := W) _ _).2 <| by
    refine ⟨Z', a, 𝟙 Z', ?_, ?_, ?_⟩
    · simpa using h
    · simp
    · rw [h]
      exact ht

/-- Helper for Lemma 4.27.5: for a finite subfamily of morphisms in a
localization with common target, one can choose left-fraction representatives with a single common
denominator in `W`. -/
private theorem exists_leftFraction_finset {ι : Type w} {X : ι → C} (s : Finset ι) {Z : C}
    (g : ∀ i, L.obj (X i) ⟶ L.obj Z) :
    ∃ (Z' : C) (t : Z ⟶ Z') (ht : W t) (f : ∀ i, i ∈ s → (X i ⟶ Z')),
      ∀ i (hi : i ∈ s), g i = (LeftFraction.mk (f i hi) t ht).map L (inverts L W) := by
  classical
  -- Induct on the finite family, maintaining a single denominator for the treated indices.
  induction s using Finset.induction with
  | empty =>
      refine ⟨Z, 𝟙 Z, W.id_mem Z, fun i hi ↦ False.elim <| Finset.notMem_empty i hi, ?_⟩
      intro i hi
      exact False.elim <| Finset.notMem_empty i hi
  | @insert a s ha ih =>
      -- First keep a common denominator for the old subfamily.
      obtain ⟨Z₁, s₁, hs₁, f₁, hf₁⟩ := ih
      -- Then choose one left-fraction representative for the new morphism.
      obtain ⟨φ₀, hφ₀⟩ := exists_leftFraction L W (g a)
      -- The Ore square refines the two competing denominators to a common one.
      let α : W.LeftFraction φ₀.Y' Z₁ := (RightFraction.mk φ₀.s φ₀.hs s₁).leftFraction
      have hα : φ₀.s ≫ α.f = s₁ ≫ α.s := by
        simpa [α] using
          (RightFraction.leftFraction_fac (RightFraction.mk φ₀.s φ₀.hs s₁)).symm
      let t : Z ⟶ α.Y' := s₁ ≫ α.s
      have ht : W t := W.comp_mem _ _ hs₁ α.hs
      let f : ∀ i, i ∈ insert a s → (X i ⟶ α.Y') := fun i hi ↦
        if h : i = a then
          h.symm.rec (φ₀.f ≫ α.f)
        else
          f₁ i ((Finset.mem_insert.1 hi).resolve_left h) ≫ α.s
      refine ⟨α.Y', t, ht, f, ?_⟩
      intro i hi
      by_cases h : i = a
      · subst h
        rw [hφ₀]
        -- The new index is handled directly by the Ore square.
        simpa [t, f, α] using
          leftFraction_map_eq_of_ore_refinement (L := L) (W := W)
            (φ := φ₀) (a := α.f) (b := α.s) (s₁ := s₁) (ht := ht) hα
      · have hi' : i ∈ s := (Finset.mem_insert.1 hi).resolve_left h
        rw [hf₁ i hi']
        -- Old indices are postcomposed into the refined common denominator.
        simpa [t, f, h] using
          (leftFraction_map_postcomp_eq (L := L) (W := W)
            (φ := LeftFraction.mk (f₁ i hi') s₁ hs₁) (t := α.s) (Z := α.Y') ht)

-- Proof sketch: choose a left-fraction representative for each `g i`. Then induct on the finite
-- index type, using the left Ore condition to replace two denominators by a common refinement in
-- `W`, and compose the previously chosen numerators with the comparison maps into that refinement.
/-- Lemma 4.27.5: a finite family of morphisms in a localization with common target admits
representatives by left fractions with a single common denominator in `W`. -/
theorem exists_leftFraction_finite {ι : Type w} [Finite ι] {X : ι → C} {Y : C}
    (g : ∀ i, L.obj (X i) ⟶ L.obj Y) :
    ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
      ∀ i, g i = (LeftFraction.mk (f i) s hs).map L (inverts L W) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Apply the finite-set statement to the whole index type.
  obtain ⟨Y', s, hs, f, hf⟩ := exists_leftFraction_finset L W Finset.univ g
  refine ⟨Y', s, hs, fun i ↦ f i (Finset.mem_univ i), ?_⟩
  intro i
  exact hf i (Finset.mem_univ i)

end Localization
end CategoryTheory

/-! ### Lemma_4_27_6 (from Chap04) -/
universe v u

namespace CategoryTheory
namespace MorphismProperty

open LeftFraction
open LeftFraction.Localization
open scoped CategoryTheory.MorphismProperty.LeftFractionNotation

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable {X Y Y' : C}

local notation "Q" => LeftFraction.Localization.Q

/-
Domain-style sampling for Lemma 4.27.6:
- primary domain: left-fraction localizations and equality criteria for roofs with fixed
  denominator;
- inspected owner declarations:
  `LeftFraction.Localization.homMk_eq_iff_leftFractionRel`,
  `LeftFraction.Localization.Q_map_comp_Qinv`,
  `MorphismProperty.LeftFractionRel`,
  `MorphismProperty.map_eq_iff_postcomp`;
- best owner abstraction: the localization functor `Q W`, with the represented morphism `s⁻¹ f`
  viewed through the owner morphism `homMk (mk f s hs)` and the canonical comparison
  `Q_map_comp_Qinv`;
- primitive data: numerators `f`, `g` and a common denominator `s` with `W s`;
- derived API: the fixed-denominator equality criterion below, together with the canonical
  postcomposition criterion extracted by `map_eq_iff_postcomp`.

Source/core/bridge triage:
- `source-facing`: `left_fraction_hom_eq_iff_exists_postcomp`;
- `core/canonical`: the owner-level localization API above;
- `bridge/view`: the relation witness for the fixed-denominator fractions
  `mk f s hs` and `mk g s hs`, used to discharge condition `(3)` of the TFAE statement. -/

/-- A morphism of `W` with source `Y'` that equalizes the numerators `f` and `g` by
postcomposition. -/
def left_fraction_has_postcomp_eq
    (f g : X ⟶ Y') :
    Prop :=
  ∃ (Y'' : C) (t : Y' ⟶ Y''), W t ∧ f ≫ t = g ≫ t

/-- A postcomposition equalizer for `f` and `g` whose composite with the denominator `s`
lies in `W`. -/
def left_fraction_has_postcomp_comp_eq
    (f g : X ⟶ Y') (s : Y ⟶ Y') :
    Prop :=
  ∃ (Y'' : C) (a : Y' ⟶ Y''), f ≫ a = g ≫ a ∧ W (s ≫ a)

/-- Helper for Lemma 4.27.6: canceling a common denominator reduces equality of two roofs to
 equality of the localized numerator maps. -/
lemma left_fraction_hom_eq_iff_Q_map_eq
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    s⁻¹ f = s⁻¹ g ↔ (Q W).map f = (Q W).map g := by
  constructor
  · intro h
    -- Rewrite both roofs as `Q.map _ ≫ Qinv s` and cancel the common inverse denominator.
    have hroof : (Q W).map f ≫ Qinv s hs = (Q W).map g ≫ Qinv s hs := by
      simpa [left_fraction_hom_eq_Q_map_comp_Qinv (W := W) f s hs,
        left_fraction_hom_eq_Q_map_comp_Qinv (W := W) g s hs] using h
    exact (cancel_mono (Qinv s hs)).1 hroof
  · intro h
    -- Reinsert the common inverse denominator to recover equality of the roofs.
    calc
      s⁻¹ f = (Q W).map f ≫ Qinv s hs := left_fraction_hom_eq_Q_map_comp_Qinv (W := W) f s hs
      _ = (Q W).map g ≫ Qinv s hs := by
        simpa using congrArg (fun k ↦ k ≫ Qinv s hs) h
      _ = s⁻¹ g := (left_fraction_hom_eq_Q_map_comp_Qinv (W := W) g s hs).symm

/-- Helper for Lemma 4.27.6: a common postcomposition equalizer whose composite with the
 denominator lies in `W` identifies the corresponding fixed-denominator roofs. -/
lemma left_fraction_hom_eq_of_has_postcomp_comp_eq
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    left_fraction_has_postcomp_comp_eq W f g s → s⁻¹ f = s⁻¹ g := by
  rintro ⟨Y'', a, hfg, hsa⟩
  -- The owner relation is witnessed by the same refinement `a` on both roofs.
  have hmk : homMk (mk f s hs) = homMk (mk g s hs) := by
    rw [homMk_eq_iff_leftFractionRel]
    exact ⟨Y'', a, a, rfl, hfg, hsa⟩
  simpa [left_fraction_hom] using hmk

/-- Equality of left fractions with fixed denominator is equivalent to postcomposition
equalization in `W`. -/
-- Proof sketch: rewrite `s⁻¹ f = s⁻¹ g` using `Q_map_comp_Qinv`, then apply the canonical
-- localization criterion `map_eq_iff_postcomp`.
theorem left_fraction_hom_eq_iff_has_postcomp_eq
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    s⁻¹ f = s⁻¹ g ↔ left_fraction_has_postcomp_eq W f g := by
  constructor
  · intro h
    -- Cancel the common denominator and apply the localization criterion for map equality.
    obtain ⟨Y'', t, ht, hfg⟩ := (map_eq_iff_postcomp (L := Q W) (W := W) f g).1
      ((left_fraction_hom_eq_iff_Q_map_eq (W := W) f g s hs).1 h)
    exact ⟨Y'', t, ht, hfg⟩
  · rintro ⟨Y'', t, ht, hfg⟩
    -- A postcomposition witness in `W` gives equality of the localized numerators.
    exact (left_fraction_hom_eq_iff_Q_map_eq (W := W) f g s hs).2 <|
      (map_eq_iff_postcomp (L := Q W) (W := W) f g).2 ⟨Y'', t, ht, hfg⟩

/-- Lemma 4.27.6: for two left fractions with common denominator `s`, the following are
equivalent:

1. the induced morphisms in the localization are equal;
2. the numerators become equal after postcomposition with a morphism of `W`;
3. the numerators become equal after postcomposition with a morphism whose composite with `s`
   lies in `W`. -/
-- Proof sketch: use `left_fraction_hom_eq_iff_has_postcomp_eq` for `(1) ↔ (2)`, and compare
-- clauses `(2)` and `(3)` by composing with `s` and by invoking the fixed-denominator relation
-- criterion `homMk_eq_iff_leftFractionRel`.
theorem left_fraction_hom_tfae
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    [ s⁻¹ f = s⁻¹ g,
      left_fraction_has_postcomp_eq W f g,
      left_fraction_has_postcomp_comp_eq W f g s ].TFAE := by
  -- First identify equality of roofs with equality after postcomposition by a morphism in `W`.
  tfae_have 1 ↔ 2 := by
    simpa using left_fraction_hom_eq_iff_has_postcomp_eq (W := W) f g s hs
  -- Next any witness in `W` also gives a witness whose composite with `s` still lies in `W`.
  tfae_have 2 → 3 := by
    rintro ⟨Y'', t, ht, hfg⟩
    exact ⟨Y'', t, hfg, W.comp_mem _ _ hs ht⟩
  -- Finally a refinement equalizing the numerators yields equality of the original roofs.
  tfae_have 3 → 1 := by
    exact left_fraction_hom_eq_of_has_postcomp_comp_eq (W := W) f g s hs
  -- These three implications assemble the desired equivalence of conditions.
  tfae_finish

end MorphismProperty
end CategoryTheory

/-! ### Remark_4_27_7 (from Chap04) -/
universe v u

namespace CategoryTheory
namespace MorphismProperty

open Limits
open LeftFraction
open MorphismProperty

scoped[MorphismPropertyUnder] notation:80 Y " / " W =>
  CategoryTheory.MorphismProperty.Under W ⊤ Y

open scoped MorphismPropertyUnder

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (Y : C)

/- Domain-style sampling for Remark 4.27.7:
- primary domain: left calculus of fractions and the canonical denominator category `Y / W`;
- inspected owner declarations:
  `MorphismProperty.Under.mk`,
  `MorphismProperty.Under.homMk`,
  `MorphismProperty.RightFraction.leftFraction`,
  `MorphismProperty.RightFraction.leftFraction_fac`,
  `MorphismProperty.HasLeftCalculusOfFractions.ext`;
- best owner abstraction: the source-facing denominator category is already the owner object
  `Y / W`, realized by `MorphismProperty.Under W ⊤ Y`, so refinement should reuse its
  constructors instead of rebuilding objects by hand.

Primitive-vs-derived split:
- primitive data: an arrow `s : Y ⟶ Y'` together with `W s`;
- derived API: the corresponding object of `Y / W` via `Under.mk`, and its comparison morphisms
  via `Under.homMk`/`Under.Hom.ext`. -/

/- Source/core/bridge triage:
- `source-facing`: `localizationTargetArrows_isFiltered`;
- `core/canonical`: the denominator category owner `Y / W = MorphismProperty.Under W ⊤ Y`;
- `bridge/view`: the `Under.mk` / `Under.homMk` constructors expressing the textbook arrows and
  commutative triangles inside that owner category. -/

-- Proof sketch: use the identity arrow `𝟙 Y` for nonemptiness; apply the left Ore condition to
-- produce a common successor of two arrows out of `Y`; and use the left-cancellation axiom to
-- equalize parallel morphisms in the canonical denominator category `Y / W`.
/-- Remark 4.27.7: for a left multiplicative system `W`, the category `Y / W` of arrows
`s : Y ⟶ Y'` lying in `W`, with morphisms given by commutative triangles under `Y`, is filtered.
Equivalently, the canonical denominator category `Y / W`, i.e. `W.Under ⊤ Y`, is filtered. -/
instance localizationTargetArrows_isFiltered :
    IsFiltered (Y / W) where
  nonempty := ⟨Under.mk (⊤ : MorphismProperty C) (𝟙 Y) (W.id_mem Y)⟩
  cocone_objs s t := by
    let φ : W.RightFraction s.right t.right := RightFraction.mk s.hom s.prop t.hom
    let ψ := φ.leftFraction
    let u : Y / W := Under.mk (⊤ : MorphismProperty C) (t.hom ≫ ψ.s)
      (W.comp_mem _ _ t.prop ψ.hs)
    refine ⟨u, Under.homMk ψ.f (by simpa [u] using φ.leftFraction_fac.symm), Under.homMk ψ.s rfl,
      trivial⟩
  cocone_maps {s t} f g := by
    have hfg : s.hom ≫ f.right = s.hom ≫ g.right := by
      rw [Under.w f, Under.w g]
    obtain ⟨Z, h, hh, heq⟩ :=
      (inferInstance : W.HasLeftCalculusOfFractions).ext f.right g.right s.hom s.prop hfg
    let u : Y / W := Under.mk (⊤ : MorphismProperty C) (t.hom ≫ h) (W.comp_mem _ _ t.prop hh)
    refine ⟨u, Under.homMk h rfl, ?_⟩
    apply Under.Hom.ext
    exact heq

variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C)

/- Domain-style sampling for `4.27.7.1`:
- primary domain: calculus of left fractions and localized Hom-sets.
- inspected owner-level declarations:
  `localizationTargetArrows_isFiltered`,
  `MorphismProperty.Under.forget`,
  `uliftCoyoneda.obj`,
  `MorphismProperty.Q`,
  `Localization.exists_leftFraction`,
  `LeftFraction.Localization.homMk`,
  `LeftFraction.Localization.homMk_eq_iff_leftFractionRel`,
  `Functor.CoconeTypes.isColimit_iff`.
- best owner abstraction: the indexed Hom-diagram is owned by
  `uliftCoyoneda.obj (Opposite.op X)` on the canonical denominator category `Y / W`, while the
  localized target morphisms are owned by the canonical left-fraction localization model via
  `LeftFraction.Localization.homMk : W.LeftFraction X Y → (W.Q.obj X ⟶ W.Q.obj Y)`.

Primitive-vs-derived split:
- primitive data: the diagram on `Y / W` and its canonical cocone into
  `Hom_{W^{-1} C}(X, Y)`.
- derived API: the `Type`-colimit witness and the resulting colimit isomorphism.

Source/core/bridge triage:
- `source-facing`: `left_localization_hom_colimit`.
- `core/canonical`: `uliftCoyoneda.obj (Opposite.op X)` together with the left-fraction owner
  morphism `LeftFraction.Localization.homMk` in the canonical localization `W.Q`.
- `bridge/view`: the cocone identifying the source diagram with the localized Hom-set. -/

private abbrev leftLocalizationHomDiagram (W : MorphismProperty C) (X Y : C) :
    (Y / W) ⥤ Type (max u v) :=
  Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
    uliftCoyoneda.{u}.obj (Opposite.op X)

/-- The cocone leg at `s : Y / W` sends `f : Hom_C(X, Y')` to the roof
`X ⟶ Y' ← Y` in the localized category. -/
private noncomputable def leftLocalizationHomCoconeApp
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) (s : Y / W) :
    (leftLocalizationHomDiagram W X Y).obj s →
      ((Localization.Q W).obj X ⟶ (Localization.Q W).obj Y) :=
  fun f ↦
    let g : X ⟶ s.right := by
      simpa using f.down
    let hs : Y ⟶ s.right := by
      simpa using s.hom
    have hhs : W hs := by
      simpa [hs] using s.prop
    LeftFraction.Localization.homMk (LeftFraction.mk g hs hhs)

/- Naturality of the canonical cocone from the `Y/S` hom diagram to the localized hom-set. -/
-- Proof sketch: if `f : s ⟶ t` in `Y/S`, then `t.hom = s.hom ≫ f.right`; after localizing,
-- `W.Q.map f.right` is invertible, so the two corresponding roofs represent the same morphism.
private theorem leftLocalizationHomCocone_naturality
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C)
    {s t : Y / W} (f : s ⟶ t) :
    (leftLocalizationHomDiagram W X Y).map f ≫ leftLocalizationHomCoconeApp W X Y t =
      leftLocalizationHomCoconeApp W X Y s := by
  funext g
  let ht : Y ⟶ t.right := by
    simpa using t.hom
  have hht : W ht := by
    simpa [ht] using t.prop
  let hs : Y ⟶ s.right := by
    simpa using s.hom
  have hhs : W hs := by
    simpa [hs] using s.prop
  let φ : W.LeftFraction X Y :=
    LeftFraction.mk (g.down ≫ f.right) ht hht
  let ψ : W.LeftFraction X Y :=
    LeftFraction.mk g.down hs hhs
  suffices hφψ : LeftFraction.Localization.homMk φ = LeftFraction.Localization.homMk ψ by
    simpa [leftLocalizationHomDiagram, leftLocalizationHomCoconeApp, φ, ψ] using hφψ
  rw [LeftFraction.Localization.homMk_eq_iff_leftFractionRel]
  refine ⟨t.right, 𝟙 _, f.right, ?_, ?_, ?_⟩
  · simpa [φ, ψ, ht, hs] using (Under.w f).symm
  · simp [φ, ψ]
  · simpa [φ, ht] using hht

/-- The cocone over the `Y / W` hom diagram whose point is the localized hom-set
`Hom_{W^{-1} C}(X, Y)`. -/
private noncomputable def leftLocalizationHomCocone
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) :
    Cocone (leftLocalizationHomDiagram W X Y) where
  pt := (Localization.Q W).obj X ⟶ (Localization.Q W).obj Y
  ι :=
    { app := leftLocalizationHomCoconeApp W X Y
      naturality := fun _ _ f ↦ leftLocalizationHomCocone_naturality W X Y f }

private theorem leftLocalizationHomCoconeTypes_isColimit
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) :
    let F : (Y / W) ⥤ Type (max u v) := leftLocalizationHomDiagram W X Y
    let c : F.CoconeTypes := F.coconeTypesEquiv.symm (leftLocalizationHomCocone W X Y)
    c.IsColimit := by
  let F : (Y / W) ⥤ Type (max u v) := leftLocalizationHomDiagram W X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (leftLocalizationHomCocone W X Y)
  refine ⟨?_⟩
  constructor
  · rw [Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered]
    intro s t f g hfg
    let hs : Y ⟶ s.right := by
      simpa using s.hom
    have hhs : W hs := by
      simpa [hs] using s.prop
    let ht : Y ⟶ t.right := by
      simpa using t.hom
    have hht : W ht := by
      simpa [ht] using t.prop
    let φ : W.LeftFraction X Y := LeftFraction.mk f.down hs hhs
    let ψ : W.LeftFraction X Y := LeftFraction.mk g.down ht hht
    change leftLocalizationHomCoconeApp W X Y s f = leftLocalizationHomCoconeApp W X Y t g at hfg
    dsimp [leftLocalizationHomCoconeApp, φ, ψ] at hfg
    obtain ⟨Z, a, b, hab, hfg', hW⟩ :=
      (LeftFraction.Localization.homMk_eq_iff_leftFractionRel φ ψ).mp hfg
    let u : Y / W := Under.mk (⊤ : MorphismProperty C) (s.hom ≫ a) hW
    refine ⟨u, ?_, ?_, ?_⟩
    · exact Under.homMk a rfl
    · exact Under.homMk b (by simpa [u] using hab.symm)
    change ULift.up (f.down ≫ a) = ULift.up (g.down ≫ b)
    simpa using hfg'
  · rw [Functor.CoconeTypes.descColimitType_surjective_iff]
    change ∀ z : ((Localization.Q W).obj X ⟶ (Localization.Q W).obj Y),
      ∃ s x, leftLocalizationHomCoconeApp W X Y s x = z
    intro z
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction (Localization.Q W) W z
    let s : Y / W := Under.mk (⊤ : MorphismProperty C) φ.s φ.hs
    refine ⟨s, ULift.up φ.f, ?_⟩
    change LeftFraction.Localization.homMk (LeftFraction.mk φ.f φ.s φ.hs) = z
    rw [LeftFraction.Localization.homMk_eq]
    simpa using hφ.symm

/-- The cocone `leftLocalizationHomCocone W X Y` is a colimit cocone. -/
private noncomputable def leftLocalizationHomCocone_isColimit
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) :
    IsColimit (leftLocalizationHomCocone W X Y) := by
  let F : (Y / W) ⥤ Type (max u v) := leftLocalizationHomDiagram W X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (leftLocalizationHomCocone W X Y)
  have hc : c.IsColimit := by
    simpa [F, c] using leftLocalizationHomCoconeTypes_isColimit W X Y
  exact Nonempty.some <| by
    simpa [c] using (Functor.CoconeTypes.isColimit_iff c).mp hc

/-- 4.27.7.1: for a left multiplicative system `W`, the localized Hom-set
`Hom_{W^{-1} C}(X, Y)` is canonically isomorphic to the colimit over `Y / W` of the Hom-sets
`Hom_C(X, Y')`, where `s : Y ⟶ Y'` ranges over arrows of `W`. -/
noncomputable def left_localization_hom_colimit
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) :
    let F : (Y / W) ⥤ Type (max u v) :=
      Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
        uliftCoyoneda.{u}.obj (Opposite.op X)
    colimit F ≅ ((Localization.Q W).obj X ⟶ (Localization.Q W).obj Y) := by
  let F : (Y / W) ⥤ Type (max u v) := leftLocalizationHomDiagram W X Y
  let c : ColimitCocone F :=
    ⟨leftLocalizationHomCocone W X Y, leftLocalizationHomCocone_isColimit W X Y⟩
  let _ : HasColimit F := HasColimit.mk c
  change colimit F ≅ c.cocone.pt
  simpa [F, leftLocalizationHomDiagram] using colimit.isoColimitCocone c

end MorphismProperty
end CategoryTheory

/-! ### Lemma_4_27_8 (from Chap04) -/
universe v u

namespace CategoryTheory

open MorphismProperty.LeftFraction.Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]

/- Companion recall: the canonical functor from `C` to the left-fraction localization of `W` is
`Q W : C ⥤ LeftFraction.Localization W`. -/
recall Q

/- Companion recall: if `s : X ⟶ Y` lies in `W`, then its image under `Q W` is canonically an
isomorphism, namely `Qiso s hs`. -/
recall Qiso

/- Companion recall: the strict universal property for the left-fraction model is packaged by
`strictUniversalPropertyFixedTarget`. -/
recall strictUniversalPropertyFixedTarget

/- Domain-style sampling in the left-fraction localization owner API:
- source-facing model: `LeftFraction.Localization W`
- core/canonical owner predicate: `Functor.IsLocalization`
- canonical localization functor: `Q W`
- canonical inverted isomorphisms: `Qiso`
- universal property owner: `strictUniversalPropertyFixedTarget`
- owner instance for the left-fraction model: `instIsLocalizationQ`

Primitive data: the morphism property `W` together with its left-calculus-of-fractions structure.
Derived API: the localized category, the functor `Q W`, the inverted morphisms `Qiso`, and the
strict universal property.

The main labeled entry below should therefore be a direct recall of the canonical localization
owner instance, rather than a new wrapper theorem restating the same universal property. -/
/- Lemma 4.27.8: for a left multiplicative system `W`, the rules `X ↦ X` and
`f : X ⟶ Y ↦ (f, 𝟙 Y)` define the canonical functor `Q W : C ⥤ LeftFraction.Localization W`;
every `s ∈ W` becomes an isomorphism under `Q W`; and `Q W` satisfies the universal property that
any functor out of `C` inverting `W` factors uniquely through `LeftFraction.Localization W`.
This is the owner-level localization statement `Functor.IsLocalization` for `Q W`. -/
recall instIsLocalizationQ : (Q W).IsLocalization W

end CategoryTheory

/-! ### Lemma_4_27_9 (from Chap04) -/
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

open MorphismProperty Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

/-- Helper for Lemma 4.27.9: the denominator category indexing the left-fraction presentation of
`Hom(Q(-), Q(Y))`. -/
abbrev localization_denominator_category [W.HasLeftCalculusOfFractions] (Y : C) :=
  CategoryTheory.MorphismProperty.Under W ⊤ Y

/-- Helper for Lemma 4.27.9: the presheaf diagram of representables indexed by arrows
`Y ⟶ Y'` in `W`. -/
abbrev localization_denominator_diagram [W.HasLeftCalculusOfFractions] (Y : C) :
    localization_denominator_category W Y ⥤ Cᵒᵖ ⥤ Type (max u v) :=
  CategoryTheory.MorphismProperty.Under.forget W ⊤ Y ⋙ CategoryTheory.Under.forget Y ⋙
    uliftYoneda.{u}

/-- Helper for Lemma 4.27.9: the filtered colimit of the denominator diagram preserves finite
limits, so any presheaf identified with that colimit is left exact. -/
lemma localization_presheaf_preservesFiniteLimits_of_iso [W.HasLeftCalculusOfFractions] (Y : C)
    (e : colimit (localization_denominator_diagram W Y) ≅
      W.Q.op ⋙ yoneda.obj (W.Q.obj Y) ⋙ uliftFunctor.{u}) :
    PreservesFiniteLimits (W.Q.op ⋙ yoneda.obj (W.Q.obj Y) ⋙ uliftFunctor.{u}) := by
  -- Each denominator object contributes a representable presheaf, hence a finite-limit-preserving
  -- functor; we combine those objectwise and then apply the filtered-colimit theorem in `Type`.
  have hflip : PreservesFiniteLimits (localization_denominator_diagram W Y).flip := by
    apply preservesFiniteLimits_of_evaluation
    intro s
    simpa [localization_denominator_diagram] using
      (show PreservesFiniteLimits (yoneda.obj s.right ⋙ uliftFunctor.{u}) from by
        letI : PreservesFiniteLimits (yoneda.obj s.right) := by infer_instance
        exact Limits.comp_preservesFiniteLimits _ _)
  have hcolim :
      PreservesFiniteLimits
        (colim :
          (localization_denominator_category W Y ⥤ Type (max u v)) ⥤ Type (max u v)) := by
    infer_instance
  have hcomp :
      PreservesFiniteLimits ((localization_denominator_diagram W Y).flip ⋙ colim) := by
    exact Limits.comp_preservesFiniteLimits _ _
  have hsource : PreservesFiniteLimits (colimit (localization_denominator_diagram W Y)) := by
    exact preservesFiniteLimits_of_natIso
      (colimitIsoFlipCompColim (localization_denominator_diagram W Y)).symm
  -- The comparison isomorphism transfers the finite-limit preservation to the localized Hom
  -- presheaf at the model object `Q(Y)`.
  exact preservesFiniteLimits_of_natIso e

/-- Helper for Lemma 4.27.9: the localized Hom-presheaf represented by `Q(Y)`. -/
noncomputable abbrev localization_target_presheaf [W.HasLeftCalculusOfFractions] (Y : C) :
    Cᵒᵖ ⥤ Type (max u v) :=
  W.Q.op ⋙ yoneda.obj (W.Q.obj Y) ⋙ uliftFunctor.{u}

/-- Helper for Lemma 4.27.9: the underlying denominator map `Y ⟶ s.right` attached to an object
of the denominator category. -/
noncomputable abbrev localization_denominator_hom [W.HasLeftCalculusOfFractions] {Y : C}
    (s : localization_denominator_category W Y) :
    Y ⟶ s.right := by
  simpa using s.hom

/-- Helper for Lemma 4.27.9: the denominator map of an object of `Y / W` lies in `W`. -/
lemma localization_denominator_hom_mem [W.HasLeftCalculusOfFractions] {Y : C}
    (s : localization_denominator_category W Y) :
    W (localization_denominator_hom (W := W) s) := by
  simpa [localization_denominator_hom] using s.prop

/-- Helper for Lemma 4.27.9: the basic roof from `Q(s.right)` to `Q(Y)` indexed by `s : Y / W`. -/
noncomputable def localization_basic_fraction [W.HasLeftCalculusOfFractions] {Y : C}
    (s : localization_denominator_category W Y) :
    W.Q.obj s.right ⟶ W.Q.obj Y :=
  (MorphismProperty.LeftFraction.ofInv (localization_denominator_hom (W := W) s)
    (localization_denominator_hom_mem (W := W) s)).map W.Q (Localization.inverts W.Q W)

/-- Helper for Lemma 4.27.9: for a morphism in the denominator category, the basic roof
`Q(t.right) ⟶ Q(Y)` pulls back to the corresponding roof at the source. -/
lemma localization_basic_fraction_naturality [W.HasLeftCalculusOfFractions] {Y : C}
    {s t : localization_denominator_category W Y} (f : s ⟶ t) :
    W.Q.map f.right ≫ localization_basic_fraction (W := W) t =
      localization_basic_fraction (W := W) s := by
  -- Postcompose with `Q(s_t)` and use that the basic roofs are inverses to localized denominators.
  letI : IsIso (W.Q.map (localization_denominator_hom (W := W) t)) :=
    Localization.inverts W.Q W _ (localization_denominator_hom_mem (W := W) t)
  apply (cancel_mono (W.Q.map (localization_denominator_hom (W := W) t))).1
  rw [localization_basic_fraction, Category.assoc, MorphismProperty.LeftFraction.map_ofInv_hom_id]
  calc
    W.Q.map f.right = (𝟙 (W.Q.obj s.right)) ≫ W.Q.map f.right := by simp
    _ = localization_basic_fraction (W := W) s ≫
          W.Q.map (localization_denominator_hom (W := W) s) ≫ W.Q.map f.right := by
      simp [localization_basic_fraction]
    _ = localization_basic_fraction (W := W) s ≫
          W.Q.map (localization_denominator_hom (W := W) s ≫ f.right) := by
      rw [← W.Q.map_comp]
    _ = localization_basic_fraction (W := W) s ≫
          W.Q.map (localization_denominator_hom (W := W) t) := by
      simpa [localization_denominator_hom] using congrArg
        (fun k ↦ localization_basic_fraction (W := W) s ≫ W.Q.map k)
        (MorphismProperty.Under.w f)

/-- Helper for Lemma 4.27.9: the cocone leg indexed by a denominator `s : Y / W` is represented
by the basic roof `(𝟙, s)`. -/
noncomputable def localization_presheaf_cocone_app [W.HasLeftCalculusOfFractions] {Y : C}
    (s : localization_denominator_category W Y) :
    uliftYoneda.obj s.right ⟶ localization_target_presheaf W Y :=
  uliftYonedaEquiv.symm (ULift.up (localization_basic_fraction (W := W) s))

/-- Helper for Lemma 4.27.9: the cocone legs are natural in the denominator category. -/
lemma localization_presheaf_cocone_naturality [W.HasLeftCalculusOfFractions] {Y : C}
    {s t : localization_denominator_category W Y} (f : s ⟶ t) :
    (localization_denominator_diagram W Y).map f ≫
        localization_presheaf_cocone_app (W := W) t =
      localization_presheaf_cocone_app (W := W) s := by
  -- Check the equality objectwise: evaluating at `X` and `g : X ⟶ s.right` gives the same roof
  -- by `localization_basic_fraction_naturality`.
  ext X g
  cases X using Opposite.rec with
  | _ X =>
      cases g using ULift.rec with
      | _ g =>
          change
            ULift.up (W.Q.map (g ≫ f.right) ≫ localization_basic_fraction (W := W) t) =
              ULift.up (W.Q.map g ≫ localization_basic_fraction (W := W) s)
          rw [Functor.map_comp]
          simp [localization_basic_fraction_naturality (W := W) f]

/-- Helper for Lemma 4.27.9: the presheaf cocone whose point is the localized Hom-presheaf at
`Q(Y)`. -/
noncomputable def localization_presheaf_cocone [W.HasLeftCalculusOfFractions] (Y : C) :
    Cocone (localization_denominator_diagram W Y) :=
  { pt := localization_target_presheaf W Y
    ι :=
      { app := localization_presheaf_cocone_app (W := W)
        naturality := fun _ _ f ↦ localization_presheaf_cocone_naturality (W := W) f } }

/-- Helper for Lemma 4.27.9: evaluating the denominator diagram at `X` recovers the `Type`-valued
Hom-diagram used in the left-fraction presentation of `Hom(Q(X), Q(Y))`. -/
abbrev localization_evaluation_diagram [W.HasLeftCalculusOfFractions] (X Y : C) :
    localization_denominator_category W Y ⥤ Type (max u v) :=
  localization_denominator_diagram W Y ⋙ (evaluation Cᵒᵖ (Type (max u v))).obj (Opposite.op X)

/-- Helper for Lemma 4.27.9: the evaluated cocone leg at `s : Y / W` sends `g : X ⟶ s.right` to
the roof `(g, s)` in the localization. -/
noncomputable def localization_evaluation_cocone_app [W.HasLeftCalculusOfFractions] (X Y : C)
    (s : localization_denominator_category W Y) :
    (localization_evaluation_diagram W X Y).obj s →
      (localization_target_presheaf W Y).obj (Opposite.op X) :=
  fun g ↦ ULift.up (W.Q.map g.down ≫
    localization_basic_fraction (W := W) s)

/-- Helper for Lemma 4.27.9: evaluating the leg indexed by `s` at a numerator `g : X ⟶ s.right`
gives the image of the left fraction `(g, s)`. -/
lemma localization_evaluation_cocone_app_eq_map [W.HasLeftCalculusOfFractions] (X Y : C)
    (s : localization_denominator_category W Y) (g : X ⟶ s.right) :
    localization_evaluation_cocone_app (W := W) X Y s (ULift.up g) =
      ULift.up
        ((LeftFraction.mk g (localization_denominator_hom (W := W) s)
            (localization_denominator_hom_mem (W := W) s)).map W.Q
          (Localization.inverts W.Q W)) := by
  -- The fraction `(g, s)` factors as `ofHom g` followed by the basic inverse roof for `s`.
  change ULift.up (W.Q.map g ≫ localization_basic_fraction (W := W) s) = _
  apply congrArg ULift.up
  simpa [localization_basic_fraction, LeftFraction.comp₀, Category.assoc,
    MorphismProperty.LeftFraction.map_ofHom] using
    (MorphismProperty.LeftFraction.map_comp_map_eq_map
      (MorphismProperty.LeftFraction.ofHom W g)
      (MorphismProperty.LeftFraction.ofInv (localization_denominator_hom (W := W) s)
        (localization_denominator_hom_mem (W := W) s))
      (MorphismProperty.LeftFraction.ofHom W (𝟙 s.right)) (by simp) W.Q)

/-- Helper for Lemma 4.27.9: the evaluated cocone legs are natural in the denominator category. -/
lemma localization_evaluation_cocone_naturality [W.HasLeftCalculusOfFractions] (X Y : C)
    {s t : localization_denominator_category W Y} (f : s ⟶ t) :
    (localization_evaluation_diagram W X Y).map f ≫
        localization_evaluation_cocone_app (W := W) X Y t =
      localization_evaluation_cocone_app (W := W) X Y s := by
  funext g
  -- After evaluating at `X`, naturality is the same roof identity as above, now postcomposed by
  -- the numerator `g`.
  change
    ULift.up (W.Q.map (g.down ≫ f.right) ≫
      localization_basic_fraction (W := W) t) =
      ULift.up (W.Q.map g.down ≫ localization_basic_fraction (W := W) s)
  rw [Functor.map_comp]
  simp [Category.assoc, localization_basic_fraction_naturality (W := W) f]

/-- Helper for Lemma 4.27.9: the explicit evaluated roof cocone in `Type`. -/
noncomputable def localization_evaluation_cocone [W.HasLeftCalculusOfFractions] (X Y : C) :
    Cocone (localization_evaluation_diagram W X Y) :=
  { pt := (localization_target_presheaf W Y).obj (Opposite.op X)
    ι :=
      { app := localization_evaluation_cocone_app (W := W) X Y
        naturality := fun _ _ f ↦ localization_evaluation_cocone_naturality (W := W) X Y f } }

/-- Helper for Lemma 4.27.9: the explicit evaluated roof cocone is colimiting. -/
private theorem localization_evaluation_coconeTypes_isColimit
    [W.HasLeftCalculusOfFractions] (X Y : C) :
    let F : localization_denominator_category W Y ⥤ Type (max u v) :=
      localization_evaluation_diagram W X Y
    let c : F.CoconeTypes := F.coconeTypesEquiv.symm (localization_evaluation_cocone (W := W) X Y)
    c.IsColimit := by
  let F : localization_denominator_category W Y ⥤ Type (max u v) :=
    localization_evaluation_diagram W X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (localization_evaluation_cocone (W := W) X Y)
  refine ⟨?_⟩
  constructor
  · rw [Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered]
    intro s t f g hfg
    let φ : W.LeftFraction X Y := LeftFraction.mk f.down
      (localization_denominator_hom (W := W) s) (localization_denominator_hom_mem (W := W) s)
    let ψ : W.LeftFraction X Y := LeftFraction.mk g.down
      (localization_denominator_hom (W := W) t) (localization_denominator_hom_mem (W := W) t)
    change localization_evaluation_cocone_app (W := W) X Y s f =
        localization_evaluation_cocone_app (W := W) X Y t g at hfg
    have hmap :
        φ.map W.Q (Localization.inverts W.Q W) =
          ψ.map W.Q (Localization.inverts W.Q W) := by
      have hmapUp :
          ULift.up (φ.map W.Q (Localization.inverts W.Q W)) =
            ULift.up (ψ.map W.Q (Localization.inverts W.Q W)) := by
        have hsEq :
            ULift.up (φ.map W.Q (Localization.inverts W.Q W)) =
              localization_evaluation_cocone_app (W := W) X Y s (ULift.up f.down) := by
          symm
          simpa [φ, localization_denominator_hom] using
            localization_evaluation_cocone_app_eq_map (W := W) X Y s f.down
        have hfgEq :
            localization_evaluation_cocone_app (W := W) X Y s (ULift.up f.down) =
              localization_evaluation_cocone_app (W := W) X Y t (ULift.up g.down) := by
          simpa using hfg
        have htEq :
            localization_evaluation_cocone_app (W := W) X Y t (ULift.up g.down) =
              ULift.up (ψ.map W.Q (Localization.inverts W.Q W)) := by
          simpa [ψ, localization_denominator_hom] using
            localization_evaluation_cocone_app_eq_map (W := W) X Y t g.down
        exact hsEq.trans (hfgEq.trans htEq)
      exact congrArg ULift.down hmapUp
    obtain ⟨Z, a, b, hab, hfg', hW⟩ :=
      (MorphismProperty.LeftFraction.map_eq_iff (L := W.Q) (W := W) φ ψ).mp hmap
    let u : localization_denominator_category W Y :=
      MorphismProperty.Under.mk (⊤ : MorphismProperty C)
        (localization_denominator_hom (W := W) s ≫ a) hW
    refine ⟨u, ?_, ?_, ?_⟩
    · exact MorphismProperty.Under.homMk a rfl
    · exact MorphismProperty.Under.homMk b (by simpa [u, localization_denominator_hom] using hab.symm)
    change ULift.up (f.down ≫ a) = ULift.up (g.down ≫ b)
    simpa using hfg'
  · rw [Functor.CoconeTypes.descColimitType_surjective_iff]
    change ∀ z : (localization_target_presheaf W Y).obj (Opposite.op X),
        ∃ s x, localization_evaluation_cocone_app (W := W) X Y s x = z
    intro z
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction W.Q W z.down
    let s : localization_denominator_category W Y :=
      MorphismProperty.Under.mk (⊤ : MorphismProperty C) φ.s φ.hs
    refine ⟨s, ULift.up φ.f, ?_⟩
    -- Every localized morphism is represented by some left fraction, so it lies in the image of
    -- the leg indexed by that denominator.
    have hsEq :
        localization_evaluation_cocone_app (W := W) X Y s (ULift.up φ.f) =
          ULift.up (φ.map W.Q (Localization.inverts W.Q W)) := by
      simpa [s, localization_denominator_hom] using
        localization_evaluation_cocone_app_eq_map (W := W) X Y s φ.f
    have hzEq : ULift.up (φ.map W.Q (Localization.inverts W.Q W)) = ULift.up z.down :=
      congrArg ULift.up hφ.symm
    have hzRefl : ULift.up z.down = z := by
      cases z
      rfl
    exact hsEq.trans (hzEq.trans hzRefl)

/-- Helper for Lemma 4.27.9: each evaluated roof cocone is colimiting. -/
noncomputable def localization_evaluation_cocone_isColimit
    [W.HasLeftCalculusOfFractions] (X Y : C) :
    IsColimit (localization_evaluation_cocone (W := W) X Y) := by
  let F : localization_denominator_category W Y ⥤ Type (max u v) :=
    localization_evaluation_diagram W X Y
  let c : F.CoconeTypes := F.coconeTypesEquiv.symm (localization_evaluation_cocone (W := W) X Y)
  have hc : c.IsColimit := by
    simpa [F, c] using localization_evaluation_coconeTypes_isColimit (W := W) X Y
  exact Nonempty.some <| by
    simpa [c] using (Functor.CoconeTypes.isColimit_iff c).mp hc

/-- Helper for Lemma 4.27.9: evaluating the presheaf cocone at `X` produces the explicit roof
cocone. -/
noncomputable def localization_presheaf_cocone_eval_iso [W.HasLeftCalculusOfFractions] (X Y : C) :
    ((evaluation Cᵒᵖ (Type (max u v))).obj (Opposite.op X)).mapCocone
        (localization_presheaf_cocone (W := W) Y) ≅
      localization_evaluation_cocone (W := W) X Y := by
  refine Cocone.ext (Iso.refl _) ?_
  intro s
  ext g
  cases g using ULift.rec with
  | _ g =>
      rfl

/-- Helper for Lemma 4.27.9: each evaluation of the presheaf cocone is a colimit cocone. -/
noncomputable def localization_presheaf_cocone_eval_isColimit [W.HasLeftCalculusOfFractions] (Y : C)
    (X : Cᵒᵖ) :
    IsColimit (((evaluation Cᵒᵖ (Type (max u v))).obj X).mapCocone
      (localization_presheaf_cocone (W := W) Y)) := by
  -- Evaluate at `X`, replace the result by the explicit roof cocone, and use the `Type`-valued
  -- left-fraction colimit argument.
  refine IsColimit.ofIsoColimit
    (localization_evaluation_cocone_isColimit (W := W) X.unop Y) ?_
  simpa using (localization_presheaf_cocone_eval_iso (W := W) X.unop Y).symm

/-- Helper for Lemma 4.27.9: the explicit presheaf roof cocone is colimiting. -/
noncomputable def localization_presheaf_colimitCocone [W.HasLeftCalculusOfFractions] (Y : C) :
    ColimitCocone (localization_denominator_diagram W Y) :=
  { cocone := localization_presheaf_cocone (W := W) Y
    isColimit := Limits.evaluationJointlyReflectsColimits _
      (fun X ↦ localization_presheaf_cocone_eval_isColimit (W := W) Y X) }

/-- Helper for Lemma 4.27.9: the localized Hom-presheaf at `Q(Y)` is the filtered colimit of the
representables indexed by the denominator category `Y / W`. -/
noncomputable def localization_presheaf_iso_of_left_fractions [W.HasLeftCalculusOfFractions]
    (Y : C) :
    colimit (localization_denominator_diagram W Y) ≅
      W.Q.op ⋙ yoneda.obj (W.Q.obj Y) ⋙ uliftFunctor.{u} :=
  colimit.isoColimitCocone (localization_presheaf_colimitCocone (W := W) Y)

/-- Helper for Lemma 4.27.9: for a model object `Q(Y)`, the Yoneda presheaf of localized morphisms
sends the chosen colimit cocone of `K` to a limit cone. -/
noncomputable def localized_yoneda_limit_at_model_obj [W.HasLeftCalculusOfFractions]
    {J : Type w} [SmallCategory J] [FinCategory J] (K : J ⥤ C)
    (c : Cocone K) (hc : IsColimit c) (Y : C) :
    IsLimit ((yoneda.obj (W.Q.obj Y)).mapCone (W.Q.mapCocone c).op) := by
  -- First show the ulifted localized Hom-presheaf is left exact by expressing it as the filtered
  -- colimit over `Y / W` of representables.
  have hpresULift :
      PreservesFiniteLimits (W.Q.op ⋙ yoneda.obj (W.Q.obj Y) ⋙ uliftFunctor.{u}) := by
    exact localization_presheaf_preservesFiniteLimits_of_iso (W := W) Y
      (localization_presheaf_iso_of_left_fractions (W := W) Y)
  have hpres :
      PreservesFiniteLimits (W.Q.op ⋙ yoneda.obj (W.Q.obj Y)) := by
    have hpresAssoc :
        PreservesFiniteLimits (((W.Q.op ⋙ yoneda.obj (W.Q.obj Y)) ⋙ uliftFunctor.{u})) := by
      simpa [Functor.assoc] using hpresULift
    letI :
        PreservesFiniteLimits (((W.Q.op ⋙ yoneda.obj (W.Q.obj Y)) ⋙ uliftFunctor.{u})) :=
      hpresAssoc
    exact preservesFiniteLimits_of_reflects_of_preserves _ uliftFunctor.{u}
  -- Applying that presheaf to the opposite of a colimit cocone yields a limit cone.
  have hlimit :
      IsLimit ((W.Q.op ⋙ yoneda.obj (W.Q.obj Y)).mapCone c.op) := by
    exact isLimitOfPreserves (W.Q.op ⋙ yoneda.obj (W.Q.obj Y)) hc.op
  have hmap :
      IsLimit ((yoneda.obj (W.Q.obj Y)).mapCone ((W.Q.op).mapCone c.op)) := by
    exact IsLimit.ofIsoLimit hlimit
      (Functor.mapConeMapCone (H := W.Q.op) (H' := yoneda.obj (W.Q.obj Y)) c.op).symm
  -- The opposite of `W.Q.mapCocone` is definitionally the same cone up to the canonical cone iso.
  exact IsLimit.ofIsoLimit hmap (Cone.ext (Iso.refl _) (by simp))

/-- Helper for Lemma 4.27.9: essential surjectivity transports the model-object Yoneda limit
statement to every object of the localization. -/
noncomputable def localized_yoneda_limit_at_any_obj [W.HasLeftCalculusOfFractions]
    {J : Type w} [SmallCategory J] [FinCategory J] (K : J ⥤ C)
    (c : Cocone K) (hc : IsColimit c) (X : W.Localization) :
    IsLimit ((yoneda.obj X).mapCone (W.Q.mapCocone c).op) := by
  -- Every localization object is isomorphic to some `Q(Y)`, so we transport the limit statement
  -- across the induced Yoneda isomorphism.
  let Y := W.Q.objPreimage X
  let e : W.Q.obj Y ≅ X := W.Q.objObjPreimageIso X
  exact IsLimit.mapConeEquiv (yoneda.mapIso e)
    (localized_yoneda_limit_at_model_obj (W := W) K c hc Y)

/-- Helper for Lemma 4.27.9: the image under `W.Q` of the chosen colimit cocone of `K` is again a
colimit cocone. -/
noncomputable def localization_mapCocone_isColimit [W.HasLeftCalculusOfFractions]
    {J : Type w} [SmallCategory J] [FinCategory J] (K : J ⥤ C)
    (c : Cocone K) (hc : IsColimit c) :
    IsColimit (W.Q.mapCocone c) := by
  -- Yoneda detects colimits, so it is enough to verify the corresponding limit statement for all
  -- representable presheaves on the localization.
  exact (Limits.Cocone.isColimitYonedaEquiv (W.Q.mapCocone c)).2
    (localized_yoneda_limit_at_any_obj (W := W) K c hc)

/- Domain-style sampling for Lemma 4.27.9:
- primary domain: localization of morphism properties and finite-colimit preservation;
- inspected owner declarations:
  `Functor.IsLocalization`,
  `Functor.q_isLocalization`,
  `Functor.IsLocalization.pi`,
  `Localization.equivalenceFromModel`,
  `Localization.qCompEquivalenceFromModelFunctorIso`;
- best owner abstraction: `Functor.IsLocalization`, with `PreservesFiniteColimits L` as derived API
  for a localization functor `L`, transported from the canonical model `W.Q` along the owner
  equivalence `equivalenceFromModel`.

Primitive-vs-derived split:
- primitive data: the morphism property `W` and a localization functor `L`;
- derived API: the instance `PreservesFiniteColimits L`, transported from the canonical owner
  functor `W.Q`.

Source/core/bridge triage:
- source-facing: the instance `PreservesFiniteColimits W.Q`;
- core/canonical: `Functor.IsLocalization`;
- bridge/view: `Functor.IsLocalization.preservesFiniteColimits`, which transports the owner
  instance along `equivalenceFromModel` and `qCompEquivalenceFromModelFunctorIso`. -/

-- Proof sketch: for each object `Y`, represent `Hom_{W.Localization}(W.Q.obj -, W.Q.obj Y)` as a
-- filtered colimit of representable functors using `4.27.7.1`; then filtered colimits commute
-- with finite limits in `Type`, so these hom-functors send finite colimits in `C` to limits, which
-- is exactly the universal property that `W.Q` preserves finite colimits.
/-- Lemma 4.27.9: if `W` is a left multiplicative system in `C`, then the localization functor
`W.Q : C ⥤ W.Localization` commutes with finite colimits. -/
instance localization_Q_preservesFiniteColimits [W.HasLeftCalculusOfFractions] :
    PreservesFiniteColimits W.Q where
  -- Route correction: package the left-fraction comparison as one presheaf colimit, deduce that
  -- each localized Hom-presheaf preserves finite limits, and conclude via Yoneda detection.
  preservesFiniteColimits J _ _ := by
    constructor
    intro K
    constructor
    intro c hc
    exact ⟨localization_mapCocone_isColimit (W := W) K c hc⟩

namespace Functor.IsLocalization

-- Proof sketch: transport finite-colimit preservation from the canonical localization functor
-- `W.Q` across the equivalence `equivalenceFromModel L W`, using the natural isomorphism
-- `qCompEquivalenceFromModelFunctorIso L W`.
/-- Any localization functor of a left multiplicative system is canonically identified with
`W.Q`, so it also preserves finite colimits. -/
theorem preservesFiniteColimits
    {D : Type w} [Category.{v} D] (L : C ⥤ D) [W.HasLeftCalculusOfFractions]
    [L.IsLocalization W] : PreservesFiniteColimits L := by
  -- Transport the canonical finite-colimit preservation of `W.Q` across the chosen equivalence
  -- from the localization model `W.Localization` to the target category `D`.
  let e := Localization.equivalenceFromModel L W
  letI : PreservesFiniteColimits W.Q := localization_Q_preservesFiniteColimits W
  letI : PreservesFiniteColimits e.functor := by infer_instance
  letI : PreservesFiniteColimits (W.Q ⋙ e.functor) :=
    Limits.comp_preservesFiniteColimits W.Q e.functor
  exact
    preservesFiniteColimits_of_natIso
      (Localization.qCompEquivalenceFromModelFunctorIso L W)

end Functor.IsLocalization

end CategoryTheory
