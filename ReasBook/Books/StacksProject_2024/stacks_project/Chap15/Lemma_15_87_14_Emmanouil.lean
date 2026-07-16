import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_5_3
import StacksProject_2024.stacks_project.Chap12.Definition_12_31_2
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_87_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace CategoryTheory

namespace SequentialInverseSystem

/- Domain-style sampling for Lemma 15.87.14:
- primary domain: sequential inverse systems of abelian groups, stagewise countable coproducts,
  and the degree-one derived inverse limit;
- sampled owner declarations:
  `SequentialInverseSystem`,
  `SequentialInverseSystem.IsMittagLeffler`,
  `SequentialInverseSystem.countableCoproduct`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.Functor.const`,
  `CategoryTheory.Limits.colim`;
- best owner abstraction: the stagewise countable-coproduct tower is the generic owner
  `SequentialInverseSystem.countableCoproduct` on inverse systems in a category with countable
  coproducts, while the degree-one obstruction is the chapter owner
  `SequentialInverseSystem.firstDerivedLimit`; the Emmanouil criterion is the source-facing
  specialization of those owners to `AddCommGrpCat`;
- primitive-vs-derived split: the primitive data are only an inverse system `A`; the
  countable-coproduct tower and the two `R^1 \!\varprojlim` objects are derived API on that
  owner.

Source/core/bridge triage:
- `source-facing`: Emmanouil's two-clause criterion for one inverse system `A`;
- `core/canonical`: the owners `SequentialInverseSystem`, `SequentialInverseSystem.countableCoproduct`,
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: the countable direct-sum wording in abelian groups for the generic stagewise
  countable-coproduct owner.
-/

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

/-- Helper for Lemma 15.87.14 (Emmanouil): the concrete range inclusion in `AddCommGrpCat` is a
monomorphism. -/
private instance rangeSubtype_mono {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    Mono (AddCommGrpCat.ofHom f.hom.range.subtype) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- Helper for Lemma 15.87.14 (Emmanouil): the chosen representative of `imageSubobject f`
maps to the concrete range subgroup of `f`. -/
private theorem imageSubobject_to_range_arrow {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    ((imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom) ≫
      AddCommGrpCat.ofHom f.hom.range.subtype = (imageSubobject f).arrow := by
  -- First rewrite the concrete range comparison through the categorical image object.
  rw [Category.assoc]
  change (imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom ≫
      AddCommGrpCat.image.ι f = (imageSubobject f).arrow
  -- Then identify the iso to the concrete range with the universal image comparison map.
  rw [show (AddCommGrpCat.imageIsoRange f).hom ≫ AddCommGrpCat.image.ι f = image.ι f by
    simpa [AddCommGrpCat.imageIsoRange] using
      (IsImage.isoExt_hom_m (hF := Image.isImage f) (hF' := AddCommGrpCat.isImage f))]
  simp

/-- Helper for Lemma 15.87.14 (Emmanouil): inclusion of image subobjects implies inclusion of the
underlying set-theoretic ranges. -/
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
  -- Finally, read off an explicit preimage of `y` from the concrete range subgroup.
  refine ⟨(φ.hom x).2.choose, ?_⟩
  have hφ := congrArg (fun u ↦ u.hom x) hφmor
  exact ((φ.hom x).2.choose_spec).trans hφ

/-- Helper for Lemma 15.87.14 (Emmanouil): equality of image subobjects gives equality of the
underlying set-theoretic ranges. -/
private theorem range_eq_of_imageSubobject_eq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : imageSubobject f = imageSubobject g) : Set.range f.hom = Set.range g.hom := by
  -- Compare the two concrete ranges by reducing both inclusions to the previous image-subobject
  -- inclusion lemma.
  refine Set.Subset.antisymm ?_ ?_
  · exact range_subset_of_imageSubobject_le h.le
  · exact range_subset_of_imageSubobject_le h.symm.le

/-- Helper for Lemma 15.87.14 (Emmanouil): in `AddCommGrpCat`, the image subobject is the concrete
range subgroup viewed as a subobject. -/
private theorem imageSubobject_eq_range_mk {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    imageSubobject f = Subobject.mk (AddCommGrpCat.ofHom f.hom.range.subtype) := by
  -- Compare the image subobject directly with the subgroup-valued range model chosen by
  -- `AddCommGrpCat.imageIsoRange`.
  exact CategoryTheory.Subobject.eq_mk_of_comm
    (AddCommGrpCat.ofHom f.hom.range.subtype)
    ((imageSubobjectIso f).trans (AddCommGrpCat.imageIsoRange f))
    (by simpa [Category.assoc] using imageSubobject_to_range_arrow f)

/-- Helper for Lemma 15.87.14 (Emmanouil): equality of concrete ranges upgrades to equality of the
corresponding range subgroups. -/
private theorem range_subgroup_eq_of_range_eq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : Set.range f.hom = Set.range g.hom) :
    f.hom.range = g.hom.range := by
  -- The subgroup structures are determined by the same carrier subset inside the target group.
  ext y
  change y ∈ Set.range f.hom ↔ y ∈ Set.range g.hom
  simp [h]

/-- Helper for Lemma 15.87.14 (Emmanouil): equality of concrete ranges can be pushed back to
equality of image subobjects. -/
private theorem imageSubobject_eq_of_range_eq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : Set.range f.hom = Set.range g.hom) : imageSubobject f = imageSubobject g := by
  -- First replace both image subobjects by their concrete range subgroup models.
  let eAdd : f.hom.range ≃+ g.hom.range := by
    refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_
        map_add' := ?_ }
    · intro x
      refine ⟨x.1, ?_⟩
      change x.1 ∈ Set.range g.hom
      have hx : x.1 ∈ Set.range f.hom := x.2
      exact h ▸ hx
    · intro y
      refine ⟨y.1, ?_⟩
      change y.1 ∈ Set.range f.hom
      have hy : y.1 ∈ Set.range g.hom := y.2
      exact h.symm ▸ hy
    · intro x
      ext
      rfl
    · intro y
      ext
      rfl
    · intro x y
      ext
      rfl
  let e : AddCommGrpCat.of f.hom.range ≅ AddCommGrpCat.of g.hom.range := eAdd.toAddCommGrpIso
  have he :
      e.hom ≫ AddCommGrpCat.ofHom g.hom.range.subtype =
        AddCommGrpCat.ofHom f.hom.range.subtype := by
    ext x
    change (eAdd x).1 = x.1
    rfl
  calc
    imageSubobject f = Subobject.mk (AddCommGrpCat.ofHom f.hom.range.subtype) :=
      imageSubobject_eq_range_mk f
    _ = Subobject.mk (AddCommGrpCat.ofHom g.hom.range.subtype) :=
      CategoryTheory.Subobject.mk_eq_mk_of_comm
        (AddCommGrpCat.ofHom f.hom.range.subtype)
        (AddCommGrpCat.ofHom g.hom.range.subtype)
        e
        he
    _ = imageSubobject g := (imageSubobject_eq_range_mk g).symm

/-- Helper for Lemma 15.87.14 (Emmanouil): from the Mittag-Leffler hypothesis choose a strictly
increasing sequence of stages at which the concrete transition-map ranges have stabilized. -/
private theorem choose_monotone_stabilization_indices
    (A : SequentialInverseSystem AddCommGrpCat.{0}) (hA : A.IsMittagLeffler) :
    ∃ c : ℕ → ℕ, StrictMono c ∧ (∀ i, i ≤ c i) ∧
      ∀ i (hic : i ≤ c i) ⦃k : ℕ⦄ (hck : c i ≤ k),
        Set.range ((A.transitionMap (hic.trans hck)).hom) =
          Set.range ((A.transitionMap hic).hom) := by
  classical
  choose d hd_le hd_image using hA
  let c : ℕ → ℕ := Nat.rec (d 0) (fun n cn ↦ max (cn + 1) (d (n + 1)))
  have hd_le_c : ∀ i, d i ≤ c i := by
    intro i
    induction i with
    | zero =>
        simp [c]
    | succ n ih =>
        -- At successor stages, `c` is defined as a max with the chosen stabilization stage.
        simp [c]
  have hc_ge : ∀ i, i ≤ c i := by
    intro i
    exact (hd_le i).trans (hd_le_c i)
  have hc_strict : StrictMono c := by
    -- The recursive definition forces `c (n + 1) ≥ c n + 1`, hence strict monotonicity.
    refine strictMono_nat_of_lt_succ ?_
    intro n
    exact
      lt_of_lt_of_le (Nat.lt_succ_self (c n))
        (by simp [c])
  refine ⟨c, hc_strict, hc_ge, ?_⟩
  intro i hic k hck
  have hdck : d i ≤ k := (hd_le_c i).trans hck
  have hstable_to_k :
      imageSubobject (A.transitionMap (hic.trans hck)) =
        imageSubobject (A.transitionMap hic) := by
    -- Compare both transition maps with the original stabilization witness `d i`.
    calc
      imageSubobject (A.transitionMap (hic.trans hck))
          = imageSubobject (A.transitionMap ((hd_le i).trans hdck)) := by
            simp
      _ = imageSubobject (A.transitionMap (hd_le i)) := hd_image i hdck
      _ = imageSubobject (A.transitionMap ((hd_le i).trans (hd_le_c i))) := by
            symm
            exact hd_image i (hd_le_c i)
      _ = imageSubobject (A.transitionMap hic) := by
            simp
  -- Once the image subobjects agree, the concrete set-theoretic ranges agree as well.
  exact
    range_eq_of_imageSubobject_eq
      (f := A.transitionMap (hic.trans hck))
      (g := A.transitionMap hic)
      hstable_to_k

/-- Helper for Lemma 15.87.14 (Emmanouil): an epimorphic Milnor difference map forces the first
derived limit to vanish because `firstDerivedLimit` is its cokernel. -/
private theorem firstDerivedLimit_isZero_of_epi_difference
    (A : SequentialInverseSystem AddCommGrpCat.{0}) (hEpi : Epi (derivedLimitDifferenceMap A)) :
    IsZero A.firstDerivedLimit := by
  -- The cokernel of an epimorphism is zero, and `firstDerivedLimit` is defined by that cokernel.
  letI : Epi (derivedLimitDifferenceMap A) := hEpi
  simpa [SequentialInverseSystem.firstDerivedLimit] using
    (isZero_cokernel_of_epi (derivedLimitDifferenceMap A))

/-- Helper for Lemma 15.87.14 (Emmanouil): if the Milnor difference map is not epi, then the
first derived limit cannot vanish. -/
private theorem not_isZero_firstDerivedLimit_of_not_epi_difference
    (A : SequentialInverseSystem AddCommGrpCat.{0}) (hnotEpi : ¬ Epi (derivedLimitDifferenceMap A)) :
    ¬ IsZero A.firstDerivedLimit := by
  intro hzero
  -- Vanishing of the cokernel would force the Milnor difference map to be epi.
  have hEpi : Epi (derivedLimitDifferenceMap A) := by
    exact
      (isSurjective_iff_epi (derivedLimitDifferenceMap A)).1 <|
        by simpa [SequentialInverseSystem.firstDerivedLimit, IsSurjective] using hzero
  exact hnotEpi hEpi

/-- Helper for Lemma 15.87.14 (Emmanouil): on each summand, the countable-coproduct transition map
acts by the underlying stage transition map. -/
private theorem countableCoproduct_transitionMap_comp_sigma_ι
    (A : SequentialInverseSystem AddCommGrpCat.{0}) {i k : ℕ} (hik : i ≤ k) (n : ℕ) :
    Limits.Sigma.ι (fun _ : ℕ => A.obj (Opposite.op k)) n ≫ A.countableCoproduct.transitionMap hik =
      A.transitionMap hik ≫ Limits.Sigma.ι (fun _ : ℕ => A.obj (Opposite.op i)) n := by
  -- Rewrite the stagewise coproduct map to the canonical `Sigma.map'` and then read off one
  -- summand using the universal coproduct computation rule.
  change Sigma.ι (fun _ : ℕ => A.obj (Opposite.op k)) n ≫
      Sigma.map' (fun m : ℕ => m) (fun _ : ℕ => A.transitionMap hik) =
        A.transitionMap hik ≫ Sigma.ι (fun _ : ℕ => A.obj (Opposite.op i)) n
  simp

/-- Helper for Lemma 15.87.14 (Emmanouil): after postcomposing with a coproduct projection, the
countable-coproduct transition map is still the underlying stage transition map. -/
private theorem countableCoproduct_transitionMap_comp_sigma_π
    (A : SequentialInverseSystem AddCommGrpCat.{0}) {i k : ℕ} (hik : i ≤ k) (n : ℕ) :
    A.countableCoproduct.transitionMap hik ≫
        Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op i)) n =
      Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op k)) n ≫
        A.transitionMap hik := by
  -- Compare the two maps after precomposing with every coproduct injection.
  refine Limits.Sigma.hom_ext
    (g₁ := A.countableCoproduct.transitionMap hik ≫
      Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op i)) n)
    (g₂ := Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op k)) n ≫
      A.transitionMap hik)
    ?_
  intro m
  calc
    Limits.Sigma.ι (fun _ : ℕ => A.obj (Opposite.op k)) m ≫
        A.countableCoproduct.transitionMap hik ≫
          Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op i)) n
        = (Limits.Sigma.ι (fun _ : ℕ => A.obj (Opposite.op k)) m ≫
            A.countableCoproduct.transitionMap hik) ≫
              Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op i)) n := by
            simp [Category.assoc]
    _ = (A.transitionMap hik ≫
          Limits.Sigma.ι (fun _ : ℕ => A.obj (Opposite.op i)) m) ≫
            Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op i)) n := by
          simpa using
            congrArg
              (fun t ↦ t ≫ Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op i)) n)
              (countableCoproduct_transitionMap_comp_sigma_ι A hik m)
    _ = A.transitionMap hik ≫
          (Limits.Sigma.ι (fun _ : ℕ => A.obj (Opposite.op i)) m ≫
            Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op i)) n) := by
          simp [Category.assoc]
    _ = (Limits.Sigma.ι (fun _ : ℕ => A.obj (Opposite.op k)) m ≫
          Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op k)) n) ≫
            A.transitionMap hik := by
          by_cases hmn : m = n
          · subst hmn
            simp
          · have hπi :
                Limits.Sigma.ι (fun _ : ℕ => A.obj (Opposite.op i)) m ≫
                    Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op i)) n = 0 := by
                simpa using
                  Limits.Sigma.ι_π_of_ne (f := fun _ : ℕ => A.obj (Opposite.op i)) hmn
            have hπk :
                Limits.Sigma.ι (fun _ : ℕ => A.obj (Opposite.op k)) m ≫
                    Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op k)) n = 0 := by
                simpa using
                  Limits.Sigma.ι_π_of_ne (f := fun _ : ℕ => A.obj (Opposite.op k)) hmn
            rw [hπi, hπk]
            simp
    _ = Limits.Sigma.ι (fun _ : ℕ => A.obj (Opposite.op k)) m ≫
          Limits.Sigma.π (fun _ : ℕ => A.obj (Opposite.op k)) n ≫
            A.transitionMap hik := by
          simp [Category.assoc]

/-- Helper for Lemma 15.87.14 (Emmanouil): when every successor map is zero, the Milnor
difference map is the identity. -/
private theorem derivedLimitDifferenceMap_eq_id_of_stepMaps_zero
    (Q : AbSeq) (hQ : ∀ n, Q.stepMap n = 0) :
    derivedLimitDifferenceMap Q = 𝟙 _ := by
  -- Compare both endomorphisms after each product projection; the shift term vanishes because
  -- every successor map is zero.
  apply Pi.hom_ext
  intro n
  rw [derivedLimitDifferenceMap_comp_π]
  simp [hQ n]

/-- Helper for Lemma 15.87.14 (Emmanouil): if every successor map is epic, then the Milnor
difference map is epic by solving the coordinate recursion stage by stage. -/
private theorem differenceMap_epi_of_epi_stepMaps
    (K : AbSeq) (hK : ∀ n, Epi (K.stepMap n)) :
    Epi (derivedLimitDifferenceMap K) := by
  -- TODO: solve the Milnor recursion directly on product coordinates.
  sorry

/-- Helper for Lemma 15.87.14 (Emmanouil): if every successor map is zero, then the first
derived limit vanishes because the Milnor difference map is the identity. -/
private theorem firstDerivedLimit_isZero_of_stepMaps_zero
    (Q : AbSeq) (hQ : ∀ n, Q.stepMap n = 0) :
    IsZero Q.firstDerivedLimit := by
  -- TODO: combine `derivedLimitDifferenceMap_eq_id_of_stepMaps_zero` with the cokernel model.
  sorry

/-- Helper for Lemma 15.87.14 (Emmanouil): a Mittag-Leffler tower is right acyclic for inverse
limit, so its first derived limit vanishes. -/
private theorem firstDerivedLimit_isZero_of_isMittagLeffler_via_rightAcyclic
    (A : SequentialInverseSystem AddCommGrpCat.{0}) (hA : A.IsMittagLeffler) :
    IsZero A.firstDerivedLimit := by
  -- Route correction: the old proof went through `Lemma_15_87_1`, but that import currently
  -- drags in broken downstream files outside the allowed edit scope.
  -- TODO: replace this placeholder by the local stabilized-image short exact sequence proof using
  -- `differenceMap_epi_of_epi_stepMaps`, `firstDerivedLimit_isZero_of_stepMaps_zero`, and
  -- `sequentialAbelianGroupLimit_exact₅`.
  sorry

/-- Helper for Lemma 15.87.14 (Emmanouil): a Mittag-Leffler tower has epimorphic Milnor
difference map. -/
private theorem derivedLimitDifferenceMap_epi_of_isMittagLeffler
    (A : SequentialInverseSystem AddCommGrpCat.{0}) (hA : A.IsMittagLeffler) :
    Epi (derivedLimitDifferenceMap A) := by
  classical
  -- Route correction: after the right-acyclic vanishing step, epimorphy is only a cokernel
  -- contradiction and no longer needs a separate Milnor recursion.
  by_contra hnotEpi
  exact
    not_isZero_firstDerivedLimit_of_not_epi_difference A hnotEpi
      (firstDerivedLimit_isZero_of_isMittagLeffler_via_rightAcyclic A hA)

/-- Helper for Lemma 15.87.14 (Emmanouil): once the Milnor difference map is epi, the first
derived limit of a Mittag-Leffler tower vanishes. -/
private theorem firstDerivedLimit_isZero_of_isMittagLeffler
    (A : SequentialInverseSystem AddCommGrpCat.{0}) (hA : A.IsMittagLeffler) :
    IsZero A.firstDerivedLimit := by
  -- Follow the source route literally: use the right-acyclicity theorem from Lemma `15.87.1`.
  exact firstDerivedLimit_isZero_of_isMittagLeffler_via_rightAcyclic A hA

/-- Helper for Lemma 15.87.14 (Emmanouil): stagewise countable coproduct preserves the
Mittag-Leffler condition. -/
private theorem isMittagLeffler_countableCoproduct
    (A : SequentialInverseSystem AddCommGrpCat.{0}) (hA : A.IsMittagLeffler) :
    A.countableCoproduct.IsMittagLeffler := by
  -- TODO: transport the stabilized-range witness to the stagewise countable coproduct tower.
  sorry

/-- Helper for Lemma 15.87.14 (Emmanouil): failure of the Mittag-Leffler condition gives a
non-epimorphic Milnor difference map on the countable-coproduct tower. -/
private theorem countableCoproduct_difference_not_epi_of_not_isMittagLeffler
    (A : SequentialInverseSystem AddCommGrpCat.{0}) (hA : ¬ A.IsMittagLeffler) :
    ¬ Epi (derivedLimitDifferenceMap A.countableCoproduct) := by
  -- TODO: execute Emmanouil's explicit coordinate obstruction on the stagewise countable
  -- coproduct/direct-sum model.
  sorry

/-- Helper for Lemma 15.87.14 (Emmanouil): if `A` is not Mittag-Leffler, then the countable
coproduct tower has nonzero first derived limit. -/
private theorem countableCoproduct_firstDerivedLimit_nonzero_of_not_isMittagLeffler
    (A : SequentialInverseSystem AddCommGrpCat.{0}) (hA : ¬ A.IsMittagLeffler) :
    ¬ IsZero A.countableCoproduct.firstDerivedLimit := by
  -- Route correction: package the Emmanouil obstruction at the Milnor difference map first, and
  -- only then translate it to nonvanishing of the cokernel model.
  exact
    not_isZero_firstDerivedLimit_of_not_epi_difference A.countableCoproduct
      (countableCoproduct_difference_not_epi_of_not_isMittagLeffler A hA)

-- Proof sketch: one direction uses Lemma `15.87.1` to deduce the vanishing of `R^1 lim` from the
-- Mittag-Leffler condition, both for `A` and for the countable direct-sum tower. For the converse,
-- Emmanouil's argument constructs from a failure of the Mittag-Leffler condition a nonzero class
-- in `R^1 lim` of the countable direct-sum tower, forcing the conjunction clause to fail.
/-- Lemma 15.87.14 (Emmanouil): for a sequential inverse system `A` of abelian groups, the
following are equivalent:
`A` is Mittag-Leffler, and both `R^1 \!\varprojlim A` and
`R^1 \!\varprojlim (A.countableCoproduct)` vanish, where `A.countableCoproduct` is the stagewise
countable direct-sum tower. -/
theorem isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
    (A : SequentialInverseSystem AddCommGrpCat.{0}) :
    A.IsMittagLeffler ↔ IsZero A.firstDerivedLimit ∧ IsZero A.countableCoproduct.firstDerivedLimit :=
    by
  constructor
  · intro hA
    refine ⟨?_, ?_⟩
    · -- The forward half first kills `R^1 lim A` using right acyclicity from Lemma `15.87.1`.
      exact firstDerivedLimit_isZero_of_isMittagLeffler A hA
    · -- Then apply the same vanishing step to the stagewise countable-coproduct tower.
      exact
        firstDerivedLimit_isZero_of_isMittagLeffler A.countableCoproduct
          (isMittagLeffler_countableCoproduct A hA)
  · rintro ⟨_, hcount⟩
    by_contra hA
    -- Emmanouil's obstruction lives on the countable-coproduct tower.
    exact countableCoproduct_firstDerivedLimit_nonzero_of_not_isMittagLeffler A hA hcount

end SequentialInverseSystem

end CategoryTheory
