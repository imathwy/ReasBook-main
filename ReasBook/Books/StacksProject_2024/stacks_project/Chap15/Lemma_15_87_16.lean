import Mathlib
import StacksProject_2024.stacks_project.Chap04.Remark_4_22_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_87_14_Emmanouil

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat
local instance : OfNat AddCommGrpCat 0 := ⟨⊥_ AddCommGrpCat⟩

namespace CategoryTheory

namespace SequentialInverseSystem

/- Domain-style sampling for Lemma 15.87.16:
- primary domain: sequential inverse systems of abelian groups, their vanishing as pro-objects,
  inverse limits, and the first derived inverse limit;
- sampled owner declarations:
  `CategoryTheory.HasProObjectValue`,
  `SequentialInverseSystem.IsMittagLeffler`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `countableCoproduct`,
  `isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero`,
  `CategoryTheory.limit`;
- best owner abstraction: the canonical owner for "the tower is zero as a pro-object" is
  `HasProObjectValue A (0 : AddCommGrpCat)`; the remaining owners are `limit A`,
  `firstDerivedLimit A`, and the stagewise countable coproduct tower `A.countableCoproduct`;
- primitive-vs-derived split:
  primitive data are only the inverse system `A`;
  `A.transitionMap`, the eventual-zero-image condition, `limit A`, `firstDerivedLimit A`, and the
  countable-coproduct tower are derived API, so the main theorem should use
  `HasProObjectValue A (0 : AddCommGrpCat)` directly and keep the eventual-zero-image formulation
  only as a bridge.

Source/core/bridge triage:
- `source-facing`: the eventual-zero-image criterion on transition maps;
- `core/canonical`: `HasProObjectValue`, `limit`, `firstDerivedLimit`,
  `countableCoproduct`, and `IsMittagLeffler`;
- `bridge/view`: the equivalence below between
  `HasProObjectValue A (0 : AddCommGrpCat)` and the eventual-zero-image condition, followed by the
  vanishing criterion for `A` and its stagewise countable coproduct tower. -/

/-- Helper for Lemma 15.87.16: long transition maps factor through every intermediate stage. -/
theorem transitionMap_comp
    (A : AbSeq) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    A.transitionMap (Nat.le_trans hij hjk) = A.transitionMap hjk ≫ A.transitionMap hij := by
  -- The unique arrow `k ⟶ i` in `ℕᵒᵖ` factors through the intermediate stage `j`.
  have hh :
      (homOfLE (Nat.le_trans hij hjk)).op = (homOfLE hjk).op ≫ (homOfLE hij).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap, Functor.map_comp] using congrArg A.map hh

/-- Helper for Lemma 15.87.16: the concrete range subgroup inclusion is mono in
`AddCommGrpCat`. -/
private instance rangeSubtype_mono {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    Mono (AddCommGrpCat.ofHom f.hom.range.subtype) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- Helper for Lemma 15.87.16: the chosen representative of `imageSubobject f` lands in the
concrete range subgroup of `f`. -/
private theorem imageSubobject_to_range_arrow {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    ((imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom) ≫
      AddCommGrpCat.ofHom f.hom.range.subtype = (imageSubobject f).arrow := by
  -- Rewrite the categorical image arrow through the canonical concrete-range model.
  rw [Category.assoc]
  change (imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom ≫
      AddCommGrpCat.image.ι f = (imageSubobject f).arrow
  rw [show (AddCommGrpCat.imageIsoRange f).hom ≫ AddCommGrpCat.image.ι f = image.ι f by
    simpa [AddCommGrpCat.imageIsoRange] using
      (IsImage.isoExt_hom_m (hF := Image.isImage f) (hF' := AddCommGrpCat.isImage f))]
  simp

/-- Helper for Lemma 15.87.16: every element of the image subobject of a morphism in
`AddCommGrpCat` has a concrete source preimage. -/
private theorem exists_preimage_of_imageSubobject_element
    {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y)
    (y : ↑(Subobject.underlying.obj (imageSubobject f))) :
    ∃ x : X, (imageSubobject f).arrow y = f x := by
  sorry

/-- Helper for Lemma 15.87.16: inclusion of image subobjects implies inclusion of the underlying
set-theoretic ranges. -/
private theorem range_subset_of_imageSubobject_le
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : imageSubobject f ≤ imageSubobject g) : Set.range f.hom ⊆ Set.range g.hom := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  let φ : X₁ ⟶ AddCommGrpCat.of g.hom.range :=
    factorThruImageSubobject f ≫ Subobject.ofLE _ _ h ≫
      (imageSubobjectIso g).hom ≫ (AddCommGrpCat.imageIsoRange g).hom
  have hφmor : φ ≫ AddCommGrpCat.ofHom g.hom.range.subtype = f := by
    -- Compare the factorization through `imageSubobject g` with the original map `f`.
    dsimp [φ]
    calc
      factorThruImageSubobject f ≫
          Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
            (imageSubobjectIso g).hom ≫
              (AddCommGrpCat.imageIsoRange g).hom ≫
                AddCommGrpCat.ofHom g.hom.range.subtype
          = factorThruImageSubobject f ≫
              Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
                (((imageSubobjectIso g).hom ≫ (AddCommGrpCat.imageIsoRange g).hom) ≫
                  AddCommGrpCat.ofHom g.hom.range.subtype) := by
              simp [Category.assoc]
      _ = factorThruImageSubobject f ≫
            Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
              (imageSubobject g).arrow := by
            rw [imageSubobject_to_range_arrow]
      _ = factorThruImageSubobject f ≫ (imageSubobject f).arrow := by
            rw [Subobject.ofLE_arrow]
      _ = f := by
            rw [imageSubobject_arrow_comp]
  refine ⟨(φ.hom x).2.choose, ?_⟩
  have hφ := congrArg (fun u ↦ u.hom x) hφmor
  exact ((φ.hom x).2.choose_spec).trans hφ

/-- Helper for Lemma 15.87.16: equality of image subobjects gives equality of the underlying
set-theoretic ranges. -/
private theorem range_eq_of_imageSubobject_eq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : imageSubobject f = imageSubobject g) : Set.range f.hom = Set.range g.hom := by
  -- Compare the concrete ranges by reducing both inclusions to the previous lemma.
  refine Set.Subset.antisymm ?_ ?_
  · exact range_subset_of_imageSubobject_le h.le
  · exact range_subset_of_imageSubobject_le h.symm.le

/-- Helper for Lemma 15.87.16: if the image subobject of a morphism is bottom, then the morphism
itself is zero. -/
theorem transitionMap_eq_zero_of_imageSubobject_eq_bot
    {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) (hf : imageSubobject f = ⊥) :
    f = 0 := by
  -- First force the image inclusion itself to be zero, then read off the original map.
  have harrowZero : (imageSubobject f).arrow = 0 := by
    apply (Subobject.mk_eq_bot_iff_zero).1
    simpa using hf
  calc
    f = factorThruImageSubobject f ≫ (imageSubobject f).arrow := by
          rw [imageSubobject_arrow_comp]
    _ = 0 := by simp [harrowZero]

/-- Helper for Lemma 15.87.16: from the Mittag-Leffler hypothesis one may choose a monotone
sequence of stabilization indices for the image subobjects. -/
private theorem choose_monotone_stabilization_indices
    (A : AbSeq) (hA : A.IsMittagLeffler) :
    ∃ c : ℕ → ℕ, StrictMono c ∧
      ∀ i : ℕ, ∃ hic : i ≤ c i, ∀ k : ℕ, ∀ hck : c i ≤ k,
        imageSubobject (A.transitionMap (hic.trans hck)) =
          imageSubobject (A.transitionMap hic) := by
  classical
  choose d hd_ge hd_stable using hA
  let c : ℕ → ℕ := Nat.rec (d 0) (fun n cn ↦ max (cn + 1) (d (n + 1)))
  have hd_le_c : ∀ i, d i ≤ c i := by
    intro i
    induction i with
    | zero =>
        simp [c]
    | succ n ih =>
        simp [c]
  have hc_strict : StrictMono c := by
    refine strictMono_nat_of_lt_succ ?_
    intro n
    exact lt_of_lt_of_le (Nat.lt_succ_self (c n)) (by simp [c])
  refine ⟨c, hc_strict, ?_⟩
  intro i
  refine ⟨(hd_ge i).trans (hd_le_c i), ?_⟩
  intro k hck
  calc
    imageSubobject (A.transitionMap (((hd_ge i).trans (hd_le_c i)).trans hck))
        = imageSubobject (A.transitionMap ((hd_ge i).trans ((hd_le_c i).trans hck))) := by
            simp
    _ = imageSubobject (A.transitionMap (hd_ge i)) := hd_stable i ((hd_le_c i).trans hck)
    _ = imageSubobject (A.transitionMap ((hd_ge i).trans (hd_le_c i))) := by
          symm
          exact hd_stable i (hd_le_c i)
    _ = imageSubobject (A.transitionMap ((hd_ge i).trans (hd_le_c i))) := rfl

/-- Helper for Lemma 15.87.16: a point in a stable image at stage `k` lifts to every later
stabilized source stage. -/
private theorem exists_lift_to_later_stable_stage
    (A : AbSeq) {m : ℕ → ℕ} (hm_ge : ∀ i, i ≤ m i)
    (hm_stable :
      ∀ i : ℕ, ∀ k : ℕ, ∀ hik : m i ≤ k,
        imageSubobject (A.transitionMap ((hm_ge i).trans hik)) =
          imageSubobject (A.transitionMap (hm_ge i)))
    {k l : ℕ} (hkl : m k ≤ l) {b : A.obj (op k)}
    (hb : ∃ x : A.obj (op (m k)), A.transitionMap (hm_ge k) x = b) :
    ∃ x : A.obj (op l), A.transitionMap ((hm_ge k).trans hkl) x = b := by
  sorry

/-- Helper for Lemma 15.87.16: a compatible family in the underlying `Type`-valued diagram of
abelian groups defines a point of the categorical inverse limit. -/
private noncomputable def limit_of_underlying_sections
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    (s : (F ⋙ forget AddCommGrpCat).sections) :
    ↑(limit F) :=
  (preservesLimitIso (forget AddCommGrpCat) F).inv
    ((Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s)

/-- Helper for Lemma 15.87.16: a point of the inverse limit determines its compatible family of
stagewise coordinates. -/
private noncomputable def underlying_sections_of_limit
    (A : AbSeq) (x : ↑(limit A)) :
    (A ⋙ forget AddCommGrpCat).sections :=
  Types.limitEquivSections _ ((preservesLimitIso (forget AddCommGrpCat) A).hom x)

/-- Helper for Lemma 15.87.16: the compatible-family description of a limit point is injective. -/
private theorem underlying_sections_of_limit_injective
    (A : AbSeq) :
    Function.Injective (underlying_sections_of_limit A) := by
  sorry

/-- Helper for Lemma 15.87.16: reading off the compatible family of a limit element recovers each
limit projection. -/
private theorem limit_π_underlying_sections_of_limit
    (A : AbSeq) (x : ↑(limit A)) (j : ℕᵒᵖ) :
    limit.π A j x = (underlying_sections_of_limit A x).val j := by
  sorry

/-- Helper for Lemma 15.87.16: the limit point built from an underlying compatible family has the
expected coordinate at every stage. -/
private theorem limit_π_limit_of_underlying_sections
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    (s : (F ⋙ forget AddCommGrpCat).sections) (j : J) :
    limit.π F j (limit_of_underlying_sections F s) = s.val j := by
  sorry

/-- Helper for Lemma 15.87.16: a point in the stabilized image at stage `n` determines a point of
the inverse limit whose `n`-th coordinate is that image-point. -/
private theorem limit_point_of_stable_image_element
    (A : AbSeq) {m : ℕ → ℕ} (hm_ge : ∀ i, i ≤ m i)
    (hm_mono : StrictMono m)
    (hm_stable :
      ∀ i : ℕ, ∀ k : ℕ, ∀ hik : m i ≤ k,
        imageSubobject (A.transitionMap ((hm_ge i).trans hik)) =
          imageSubobject (A.transitionMap (hm_ge i)))
    {n : ℕ} (y : ↑(Subobject.underlying.obj (imageSubobject (A.transitionMap (hm_ge n))))) :
    ∃ x : ↑(limit A),
      limit.π A (op n) x = (imageSubobject (A.transitionMap (hm_ge n))).arrow y := by
  sorry

/-- Helper for Lemma 15.87.16: if all transition-map images eventually vanish, then every
Hom-colimit of the associated pro-system is a subsingleton. -/
private theorem proSystemHomColimit_subsingleton_of_eventually_zero_image
    (A : AbSeq)
    (hA : ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m,
      imageSubobject (A.transitionMap hnm) = ⊥) :
    ∀ W : AddCommGrpCat, Subsingleton (colimit (A.op ⋙ uliftYoneda.obj W)) := by
  sorry

/-- Helper for Lemma 15.87.16: a subsingleton Hom-colimit identifies the corresponding
`proSystemHomColimitFunctor` value as a subsingleton as well. -/
private theorem proSystemHomColimitFunctor_obj_subsingleton_of_colimit_subsingleton
    (A : AbSeq) (W : AddCommGrpCat)
    (hW : Subsingleton (colimit (A.op ⋙ uliftYoneda.obj W))) :
    Subsingleton ((proSystemHomColimitFunctor A).obj W) := by
  sorry

/-- Helper for Lemma 15.87.16: when a stabilized image point yields a point of a zero inverse
limit, the stabilized image itself must be zero. -/
private theorem stable_imageSubobject_eq_bot_of_limit_isZero
    (A : AbSeq) {m : ℕ → ℕ} (hm_ge : ∀ i, i ≤ m i)
    (hm_mono : StrictMono m)
    (hm_stable :
      ∀ i : ℕ, ∀ k : ℕ, ∀ hik : m i ≤ k,
        imageSubobject (A.transitionMap ((hm_ge i).trans hik)) =
          imageSubobject (A.transitionMap (hm_ge i)))
    (hlim : IsZero (limit A)) (n : ℕ) :
    imageSubobject (A.transitionMap (hm_ge n)) = ⊥ := by
  sorry

/-- Helper for Lemma 15.87.16: equality in the Hom-colimit can be checked after transporting both
representatives to a common later stage. -/
private theorem hom_colimit_eq_at_common_stage
    (A : AbSeq) (W : AddCommGrpCat) {i j : ℕ}
    {f : A.obj (op i) ⟶ W} {g : A.obj (op j) ⟶ W}
    (h :
      colimit.ι (A.op ⋙ uliftYoneda.obj W) (op (op i)) (ULift.up f) =
        colimit.ι (A.op ⋙ uliftYoneda.obj W) (op (op j)) (ULift.up g)) :
    ∃ k, ∃ hi : i ≤ k, ∃ hj : j ≤ k,
      A.transitionMap hi ≫ f = A.transitionMap hj ≫ g := by
  sorry

/-- Helper for Lemma 15.87.16: if the pro-object of `A` is represented by `0`, then every fixed
stage is hit by a later zero transition map. -/
private theorem exists_later_zero_transition_of_hasProObjectValue_zero
    (A : AbSeq) (hA : HasProObjectValue A (0 : AddCommGrpCat)) :
    ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m, A.transitionMap hnm = 0 := by
  sorry

-- Proof sketch: if the pro-object defined by `A` is corepresented by `0`, then every map from a
-- later stage to a fixed stage factors through the zero cone after passing far enough out, so the
-- image of a sufficiently late transition map is zero. Conversely, if all transition-map images
-- eventually vanish at each stage, then the associated pro-object is eventually zero and hence is
-- corepresented by the zero object.
/-- A sequential inverse system of abelian groups has pro-object value `0` if and only if, for
every fixed stage, the image of a sufficiently far transition map into that stage is zero. -/
theorem hasProObjectValue_zero_iff_eventually_zero_image
    (A : AbSeq) :
    HasProObjectValue A (0 : AddCommGrpCat) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m,
        imageSubobject (A.transitionMap hnm) = ⊥ := by
  sorry

-- Proof sketch: if `A` is zero as a pro-object, then the eventual-zero-image condition forces
-- the stabilized images at every stage to be zero; this gives `lim A = 0`, and the stabilization
-- itself is exactly the Mittag-Leffler condition. Conversely, if `A` is Mittag-Leffler and
-- `lim A = 0`, then the stable images inside each stage are nonempty and have zero inverse limit,
-- hence are zero, which recovers the eventual-zero-image criterion.
/-- The zero pro-object criterion in owner form: a sequential inverse system of abelian groups is
zero as a pro-object exactly when `\varprojlim A` vanishes and `A` is Mittag-Leffler. -/
theorem hasProObjectValue_zero_iff_limit_isZero_and_isMittagLeffler
    (A : AbSeq) :
    HasProObjectValue A (0 : AddCommGrpCat) ↔
      IsZero (limit A) ∧ A.IsMittagLeffler := by
  sorry

/-- Lemma 15.87.16: a sequential inverse system of abelian groups is zero as a pro-object if and
only if `\varprojlim A`, `R^1 \!\varprojlim A`, and
`R^1 \!\varprojlim (A.countableCoproduct)` vanish, where `A.countableCoproduct` is the inverse
system obtained by taking countable direct sums stagewise. -/
theorem hasProObjectValue_zero_iff_limit_and_firstDerivedLimit_isZero_and_countableCoproduct
    (A : AbSeq) :
    HasProObjectValue A (0 : AddCommGrpCat) ↔
      IsZero (limit A) ∧
        IsZero A.firstDerivedLimit ∧
          IsZero A.countableCoproduct.firstDerivedLimit := by
  constructor
  · intro hA
    have hlim_ml := (hasProObjectValue_zero_iff_limit_isZero_and_isMittagLeffler A).1 hA
    have hfirst :=
      (isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero A).1
        hlim_ml.2
    exact ⟨hlim_ml.1, hfirst.1, hfirst.2⟩
  · rintro ⟨hlim, hfirst, hcoprodfirst⟩
    exact
      (hasProObjectValue_zero_iff_limit_isZero_and_isMittagLeffler A).2
        ⟨hlim,
          (isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
            A).2 ⟨hfirst, hcoprodfirst⟩⟩

end SequentialInverseSystem

end CategoryTheory
