import StacksProject_2024.Chap12.Definition_12_19_3
import StacksProject_2024.Chap13.Definition_13_13_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open FilteredObject.Hom
open scoped CategoryTheory ZeroObject

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

local notation "FilF" => Fil^f(𝒜)

section FilteredInjectives

/-- Helper for Lemma 13.26.5: a finite filtered object is filtered injective when each graded
piece is injective in the ambient abelian category. -/
class IsFilteredInjective (I : FilF) : Prop where
  injective (p : ℤ) : Injective (gr^{p} I.obj)

attribute [instance] IsFilteredInjective.injective

/-- The strictly full subcategory `𝓘^f ⊂ Fil^f(𝒜)` of filtered injective objects. -/
abbrev filteredInjectiveSubcategory (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  FullSubcategory (IsFilteredInjective : ObjectProperty (Fil^f(𝒜)))

/- The Stacks Project writes the full subcategory of filtered injective finite filtered objects as
`𝓘^f(𝒜)`. This is notation for the chapter owner `filteredInjectiveSubcategory 𝒜`. -/
scoped notation "𝓘^f(" C:arg ")" => filteredInjectiveSubcategory C

instance (I : 𝓘^f(𝒜)) : IsFilteredInjective I.obj :=
  I.property

/-- The inclusion `𝓘^f(𝒜) ⥤ Fil^f(𝒜)` forgetting that an object is filtered injective. -/
abbrev filteredInjectiveInclusion (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    𝓘^f(𝒜) ⥤ Fil^f(𝒜) :=
  ObjectProperty.ι (IsFilteredInjective : ObjectProperty (Fil^f(𝒜)))

end FilteredInjectives

section

/-- Helper for Lemma 13.26.5: the local interval-tail model uses finite biproducts available in
every abelian category. -/
local instance filteredInjective_hasFiniteBiproducts : HasFiniteBiproducts 𝒜 :=
  Abelian.hasFiniteBiproducts

/-- Helper for Lemma 13.26.5: once a filtration stage is zero, every later stage is zero. -/
private theorem filtration_eq_bot_of_le {X : FilteredObject 𝒜} {p q : ℤ}
    (hpq : p ≤ q) (hp : X.filtration p = ⊥) :
    X.filtration q = ⊥ := by
  -- Proof comment: decreasing filtrations only get smaller as the index increases.
  apply bot_unique
  simpa [hp] using X.filtration.antitone_obj hpq

/-- Helper for Lemma 13.26.5: once a filtration stage is the whole object, every earlier stage is
also the whole object. -/
private theorem filtration_eq_top_of_le {X : FilteredObject 𝒜} {p q : ℤ}
    (hpq : p ≤ q) (hq : X.filtration q = ⊤) :
    X.filtration p = ⊤ := by
  -- Proof comment: decreasing filtrations only get larger as the index decreases.
  apply top_unique
  simpa [hq] using X.filtration.antitone_obj hpq

/-- Helper for Lemma 13.26.5: the `p`-th stage of a finite filtered object. -/
private abbrev finiteStage (A : FilF) (p : ℤ) : Subobject A.obj.obj :=
  let X : FilteredObject 𝒜 := A.obj
  X.filtration.obj p

/-- Helper for Lemma 13.26.5: choose an ordered finite window containing all nontrivial
filtration behaviour. -/
private theorem ordered_window_of_isFinite (A : FilF) :
    ∃ a b : ℤ, a ≤ b ∧ finiteStage A a = ⊤ ∧ finiteStage A (b + 1) = ⊥ := by
  rcases A.property with ⟨t, m, htop, hbot⟩
  refine ⟨min t m, max t m, min_le_max, ?_, ?_⟩
  · -- Proof comment: moving left from a top stage keeps the filtration equal to `⊤`.
    exact filtration_eq_top_of_le (min_le_left _ _) htop
  · -- Proof comment: moving right from a zero stage keeps the filtration equal to `⊥`.
    have hm : m ≤ max t m + 1 := by
      omega
    exact filtration_eq_bot_of_le hm hbot

/-- Helper for Lemma 13.26.5: a subobject identifies canonically with the kernel of its cokernel
projection. -/
private theorem subobject_eq_kernel_cokernel {A : 𝒜} (X : Subobject A) :
    X = kernelSubobject (cokernel.π X.arrow) := by
  -- Proof comment: replace the subobject by the image of its mono arrow, then use the standard
  -- exact row `X ⟶ A ⟶ A/X`.
  calc
    X = imageSubobject X.arrow := by
      symm
      simpa using (Limits.imageSubobject_mono X.arrow)
    _ = kernelSubobject (cokernel.π X.arrow) := by
      simpa using
        (ShortComplex.exact_iff_image_eq_kernel
          (ShortComplex.mk X.arrow (cokernel.π X.arrow) (cokernel.condition X.arrow))).1
          (ShortComplex.exact_cokernel X.arrow)

/-- Helper for Lemma 13.26.5: the stage quotient `X/F^pX` used in the textbook embedding
construction. -/
private abbrev stage_quotient (X : FilteredObject 𝒜) (p : ℤ) : 𝒜 :=
  cokernel (X.filtration.obj p).arrow

/-- Helper for Lemma 13.26.5: pulling back the zero subobject along a monomorphism stays zero. -/
private theorem pullback_bot_of_mono {X Y : 𝒜} (f : X ⟶ Y) [Mono f] :
    (Subobject.pullback f).obj (⊥ : Subobject Y) = (⊥ : Subobject X) := by
  -- Proof comment: the pullback arrow composes to zero with the mono `f`, so cancellation forces
  -- that pullback arrow itself to be zero.
  rw [Subobject.pullback_obj]
  apply (Subobject.mk_eq_bot_iff_zero).2
  apply (cancel_mono f).1
  simpa using
    (show pullback.snd (⊥ : Subobject Y).arrow f ≫ f =
        pullback.fst (⊥ : Subobject Y).arrow f ≫ (⊥ : Subobject Y).arrow from
      pullback.condition.symm)

/-- Helper for Lemma 13.26.5: for a monomorphism of filtered objects, strictness is equivalent to
recovering the source filtration by pulling back the target filtration. -/
private theorem strict_iff_induced_filtration_of_mono
    {X Y : FilteredObject 𝒜} (f : X ⟶ Y) [Mono f.hom] :
    Strict f ↔
      X.filtration = (Subobject.pullback f.hom).toOrderHom.comp Y.filtration := by
  constructor
  · intro hf
    refine OrderHom.ext _ _ ?_
    funext i
    have hi := congrArg ((Subobject.pullback f.hom).obj)
      ((FilteredObject.Hom.strict_iff_quotient_eq_inf f).1 hf i)
    simpa [DecreasingFiltration.quotient, Subobject.exists_iso_map,
      Limits.imageSubobject_mono, Subobject.inf_pullback, Subobject.pullback_self] using hi
  · intro h
    refine (FilteredObject.Hom.strict_iff_quotient_eq_inf f).2 ?_
    intro i
    have hi := congrArg (fun F ↦ F i) h
    calc
      X.filtration.quotient f.hom i
          = (Subobject.map f.hom).obj ((Subobject.pullback f.hom).obj (Y.filtration i)) := by
              simpa [DecreasingFiltration.quotient, Subobject.exists_iso_map] using
                congrArg ((Subobject.«exists» f.hom).obj) hi
      _ = Limits.imageSubobject f.hom ⊓ Y.filtration i := by
              simpa [Subobject.inf_def, Limits.imageSubobject_mono] using
                (Subobject.inf_eq_map_pullback' (MonoOver.mk f.hom) (Y.filtration i)).symm

/-- Helper for Lemma 13.26.5: the `i`-th component of the textbook map is the quotient projection
to `A/F^(i + 1)A` followed by the chosen injective presentation. -/
private abbrev quotient_presentation_component
    {A : FilF} {a b : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)))
    (i : Set.Icc a b) :
    A.obj.obj ⟶ (P i).J :=
  cokernel.π (finiteStage A (i.1 + 1)).arrow ≫ (P i).f

/-- Helper for Lemma 13.26.5: on `F^p A`, every component indexed strictly below `p` vanishes. -/
private theorem quotient_presentation_component_stage_zero_of_lt
    {A : FilF} {a b p : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)))
    (i : Set.Icc a b) (hip : i.1 < p) :
    (finiteStage A p).arrow ≫ quotient_presentation_component P i = 0 := by
  let X : FilteredObject 𝒜 := A.obj
  let Fp : Subobject A.obj.obj := finiteStage A p
  let Fi : Subobject A.obj.obj := finiteStage A (i.1 + 1)
  let v : (Fp : 𝒜) ⟶ (Fi : 𝒜) :=
    Subobject.ofLE _ _ (X.filtration.antitone_obj (by omega))
  have hquot :
      Fp.arrow ≫ cokernel.π Fi.arrow = 0 := by
    calc
      Fp.arrow ≫ cokernel.π Fi.arrow
          =
            (v ≫ Fi.arrow) ≫ cokernel.π Fi.arrow := by
                simp [v]
      _ = v ≫
            (Fi.arrow ≫ cokernel.π Fi.arrow) := by
              simp [Category.assoc]
      _ = v ≫ 0 := by
            rw [cokernel.condition]
      _ = 0 := by
            simp
  -- Proof comment: if `i < p`, then `F^p A` already lies inside `F^(i + 1) A`, so the quotient
  -- map to `A/F^(i + 1) A` kills the whole `p`-th stage.
  simpa [quotient_presentation_component, Category.assoc] using
    congrArg (fun k ↦ k ≫ (P i).f) hquot

/-- Helper for Lemma 13.26.5: the canonical tail inclusion of the interval-indexed biproduct is
split by the corresponding projection. -/
private theorem intervalTailSubobject_local_splitMono
    {a b : ℤ} (J : Set.Icc a b → 𝒜) (p : ℤ) :
    IsSplitMono (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1) := by
  -- Proof comment: the canonical projection onto the same subtype is a retraction.
  exact IsSplitMono.mk'
    { retraction := biproduct.toSubtype J fun i : Set.Icc a b ↦ p ≤ i.1
      id := biproduct.fromSubtype_toSubtype J fun i : Set.Icc a b ↦ p ≤ i.1 }

/-- Helper for Lemma 13.26.5: the `p`-tail direct sum inside the interval-indexed biproduct. -/
@[reducible] private noncomputable def intervalTailSubobject_local
    {a b : ℤ} (J : Set.Icc a b → 𝒜) (p : ℤ) :
    Subobject (⨁ J) :=
  letI := intervalTailSubobject_local_splitMono J p
  Subobject.mk (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1)

/-- Helper for Lemma 13.26.5: the carrier of the local `p`-tail subobject is canonically the
corresponding subtype biproduct. -/
@[reducible] private noncomputable def intervalTailSubobject_local_iso_subtype_biproduct
    {a b : ℤ} (J : Set.Icc a b → 𝒜) (p : ℤ) :
    (((intervalTailSubobject_local J p : Subobject (⨁ J)) : 𝒜)) ≅
      (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1) :=
  letI := intervalTailSubobject_local_splitMono J p
  Subobject.underlyingIso (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1)

/-- Helper for Lemma 13.26.5: under the canonical tail-carrier identification, the subobject
arrow is the expected `biproduct.fromSubtype`. -/
private theorem intervalTailSubobject_local_iso_subtype_biproduct_hom_comp_fromSubtype
    {a b : ℤ} (J : Set.Icc a b → 𝒜) (p : ℤ) :
    (intervalTailSubobject_local_iso_subtype_biproduct J p).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
      (intervalTailSubobject_local J p).arrow := by
  -- Proof comment: `intervalTailSubobject_local` is defined by the same split mono, so the
  -- canonical underlying isomorphism composes back to the defining subobject arrow.
  letI := intervalTailSubobject_local_splitMono J p
  change
    ((Subobject.underlyingIso (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1))).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) =
      (intervalTailSubobject_local J p).arrow
  rw [Subobject.underlyingIso_hom_comp_eq_mk]

/-- Helper for Lemma 13.26.5: in the same identification, the inverse map followed by the
subobject arrow is again the canonical `biproduct.fromSubtype`. -/
private theorem intervalTailSubobject_local_iso_subtype_biproduct_inv_comp_arrow
    {a b : ℤ} (J : Set.Icc a b → 𝒜) (p : ℤ) :
    (intervalTailSubobject_local_iso_subtype_biproduct J p).inv ≫
        (intervalTailSubobject_local J p).arrow =
      biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) := by
  -- Proof comment: compose the previous arrow formula on the left with the inverse of the
  -- canonical carrier identification.
  calc
    (intervalTailSubobject_local_iso_subtype_biproduct J p).inv ≫
        (intervalTailSubobject_local J p).arrow
        =
          (intervalTailSubobject_local_iso_subtype_biproduct J p).inv ≫
            ((intervalTailSubobject_local_iso_subtype_biproduct J p).hom ≫
              biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) := by
                rw [intervalTailSubobject_local_iso_subtype_biproduct_hom_comp_fromSubtype J p]
    _ = biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) := by
          simp [Category.assoc]

/-- Helper for Lemma 13.26.5: increasing the filtration index shrinks the interval tail. -/
private theorem intervalTailSubobject_local_antitone
    {a b : ℤ} (J : Set.Icc a b → 𝒜) {p q : ℤ} (hpq : p ≤ q) :
    intervalTailSubobject_local J q ≤ intervalTailSubobject_local J p := by
  -- Proof comment: every `q`-tail summand also satisfies the weaker bound `p ≤ i.1`, so the
  -- `q`-tail inclusion factors through the `p`-tail by the larger-tail projection.
  letI := intervalTailSubobject_local_splitMono J p
  letI := intervalTailSubobject_local_splitMono J q
  refine Subobject.mk_le_mk_of_comm
    (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ q ≤ i.1) ≫
      biproduct.toSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) ?_
  ext i
  by_cases hqi : q ≤ i.1
  · have hpi : p ≤ i.1 := le_trans hpq hqi
    simp [biproduct.fromSubtype_π, biproduct.toSubtype_π, hqi, hpi, Category.assoc]
  · by_cases hpi : p ≤ i.1
    · simp [biproduct.fromSubtype_π, biproduct.toSubtype_π, hqi, hpi, Category.assoc]
    · simp [biproduct.fromSubtype_π, biproduct.toSubtype_π, hqi, hpi, Category.assoc]

/-- Helper for Lemma 13.26.5: the `q`-tail carrier maps canonically into the `p`-tail carrier
whenever `p ≤ q`. -/
@[reducible] private noncomputable def intervalTailSubobject_local_factor_of_le
    {a b : ℤ} (J : Set.Icc a b → 𝒜) {p q : ℤ} (hpq : p ≤ q) :
    (((intervalTailSubobject_local J q : Subobject (⨁ J)) : 𝒜)) ⟶
      (((intervalTailSubobject_local J p : Subobject (⨁ J)) : 𝒜)) :=
  Subobject.ofLE _ _ (intervalTailSubobject_local_antitone J hpq)

/-- Helper for Lemma 13.26.5: the canonical map from the `q`-tail carrier to the `p`-tail
carrier composes to the expected ambient tail inclusion. -/
private theorem intervalTailSubobject_local_factor_of_le_arrow
    {a b : ℤ} (J : Set.Icc a b → 𝒜) {p q : ℤ} (hpq : p ≤ q) :
    intervalTailSubobject_local_factor_of_le J hpq ≫
        (intervalTailSubobject_local J p).arrow =
      (intervalTailSubobject_local J q).arrow := by
  -- Proof comment: this is just the defining commutative square for the canonical subobject map.
  simpa [intervalTailSubobject_local_factor_of_le] using
    (Subobject.ofLE_arrow (intervalTailSubobject_local_antitone J hpq))

/-- Helper for Lemma 13.26.5: the interval tails define a decreasing filtration. -/
private theorem intervalTailFiltration_local_monotone
    {a b : ℤ} (J : Set.Icc a b → 𝒜) :
    Monotone (fun p : ℤᵒᵈ ↦ intervalTailSubobject_local J p) := by
  intro p q hpq
  -- Proof comment: monotonicity on `ℤᵒᵈ` is exactly the antitonicity statement on `ℤ`.
  simpa using
    intervalTailSubobject_local_antitone J
      (show OrderDual.ofDual q ≤ OrderDual.ofDual p from hpq)

/-- Helper for Lemma 13.26.5: the tail subobjects package into a finite decreasing filtration on
the interval biproduct. -/
@[reducible] private noncomputable def intervalTailFiltration_local
    {a b : ℤ} (J : Set.Icc a b → 𝒜) :
    DecreasingFiltration (⨁ J) :=
  { toFun := fun p ↦ intervalTailSubobject_local J p
    monotone' := intervalTailFiltration_local_monotone J }

/-- Helper for Lemma 13.26.5: every stage weakly to the left of the interval is the whole
interval biproduct. -/
private theorem intervalTailSubobject_local_eq_top_of_le_left
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) (hp : p ≤ a) :
    intervalTailSubobject_local J p = ⊤ := by
  -- Proof comment: every index in `[a, b]` satisfies `p ≤ i.1`, so the tail inclusion is an
  -- isomorphism with inverse the corresponding subtype projection.
  letI := intervalTailSubobject_local_splitMono J p
  change Subobject.mk (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) = ⊤
  apply le_antisymm le_top
  refine Subobject.mk_le_mk_of_comm
    (biproduct.toSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) ?_
  ext i
  have hi : p ≤ i.1 := le_trans hp i.2.1
  simp [hi, Category.assoc]

/-- Helper for Lemma 13.26.5: every stage strictly to the right of the interval is zero. -/
private theorem intervalTailSubobject_local_eq_bot_of_right_lt
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) (hp : b < p) :
    intervalTailSubobject_local J p = ⊥ := by
  -- Proof comment: no index in `[a, b]` survives beyond the right endpoint, so the tail
  -- inclusion is the zero morphism and hence defines the bottom subobject.
  letI := intervalTailSubobject_local_splitMono J p
  change Subobject.mk (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) = ⊥
  apply (Subobject.mk_eq_bot_iff_zero).2
  apply biproduct.hom_ext
  intro i
  have hib : i.1 ≤ b := i.2.2
  have hi : ¬ p ≤ i.1 := by
    omega
  simp [biproduct.fromSubtype_π, hi]

/-- Helper for Lemma 13.26.5: the local interval-tail model has finite filtration bounded by the
chosen window. -/
private theorem intervalSplitFilteredObject_local_isFinite
    {a b : ℤ} (J : Set.Icc a b → 𝒜) :
    ({ obj := ⨁ J
       filtration := intervalTailFiltration_local J } : FilteredObject 𝒜).IsFinite := by
  refine ⟨a, b + 1, ?_, ?_⟩
  · -- Proof comment: the left endpoint already contains every interval summand.
    simpa [intervalTailFiltration_local] using
      intervalTailSubobject_local_eq_top_of_le_left J le_rfl
  · -- Proof comment: the stage immediately to the right of the window is the empty tail.
    simpa [intervalTailFiltration_local] using
      intervalTailSubobject_local_eq_bot_of_right_lt J (by omega)

/-- Helper for Lemma 13.26.5: the finite filtered object built from the interval-indexed injective
targets with the tail filtration. -/
@[reducible] private noncomputable def intervalSplitFilteredObject_local
    (a b : ℤ) (J : Set.Icc a b → 𝒜) :
    FilF :=
  ⟨{ obj := ⨁ J
     filtration := intervalTailFiltration_local J },
    intervalSplitFilteredObject_local_isFinite J⟩

/-- Helper for Lemma 13.26.5: the `p`-th stage of the local interval-split filtered object. -/
private abbrev intervalSplitStage
    (a b : ℤ) (J : Set.Icc a b → 𝒜) (p : ℤ) :
    Subobject (intervalSplitFilteredObject_local a b J).obj.obj :=
  let X : FilteredObject 𝒜 := (intervalSplitFilteredObject_local a b J).obj
  X.filtration.obj p

/-- Helper for Lemma 13.26.5: the `p`-th stage of the local interval-tail object is canonically
isomorphic to the expected tail biproduct, and under this identification its arrow is the canonical
tail inclusion. -/
private theorem intervalSplitFilteredObject_stage_arrow_eq_fromSubtype_local
    (a b p : ℤ) (J : Set.Icc a b → 𝒜) :
    ∃ e :
      (((intervalSplitStage a b J p : Subobject _ ) : 𝒜)) ≅
        (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1),
      e.hom ≫ biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
        (intervalSplitStage a b J p).arrow := by
  -- Proof comment: the `p`-th stage is definitionally the local tail subobject, so we can reuse
  -- the canonical tail-carrier identification instead of rebuilding it ad hoc.
  letI := intervalTailSubobject_local_splitMono J p
  refine ⟨intervalTailSubobject_local_iso_subtype_biproduct J p, ?_⟩
  simpa [intervalSplitFilteredObject_local, intervalTailFiltration_local] using
    intervalTailSubobject_local_iso_subtype_biproduct_hom_comp_fromSubtype J p

/-- Helper for Lemma 13.26.5: the `p`-th stage carrier of the local interval-split object is the
corresponding subtype biproduct. -/
@[reducible] private noncomputable def intervalSplitFilteredObject_local_stageIso
    (a b p : ℤ) (J : Set.Icc a b → 𝒜) :
    (((intervalSplitStage a b J p : Subobject _ ) : 𝒜)) ≅
      (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1) :=
  intervalTailSubobject_local_iso_subtype_biproduct J p

/-- Helper for Lemma 13.26.5: under the canonical stage identification, the stage arrow is the
expected `fromSubtype` inclusion. -/
private theorem intervalSplitFilteredObject_local_stageIso_hom_comp_fromSubtype
    (a b p : ℤ) (J : Set.Icc a b → 𝒜) :
    (intervalSplitFilteredObject_local_stageIso a b p J).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
      (intervalSplitStage a b J p).arrow := by
  -- Proof comment: the local interval-split object uses the same tail subobject definition, so
  -- the stage arrow formula is exactly the tail-subobject arrow formula after unfolding names.
  simpa [intervalSplitFilteredObject_local, intervalTailFiltration_local,
    intervalSplitFilteredObject_local_stageIso] using
    intervalTailSubobject_local_iso_subtype_biproduct_hom_comp_fromSubtype J p

/-- Helper for Lemma 13.26.5: the `p`-th stage subobject of the local interval-split object is
the canonical interval tail. -/
private theorem intervalSplitFilteredObject_local_stage_eq_tail
    (a b p : ℤ) (J : Set.Icc a b → 𝒜) :
    intervalSplitStage a b J p = intervalTailSubobject_local J p := by
  -- Proof comment: the local interval-split filtration is defined from the interval-tail
  -- subobjects, so the stage identification is by unfolding the owner definitions.
  rfl

/-- Helper for Lemma 13.26.5: the inverse stage identification followed by the stage arrow is the
canonical `fromSubtype` inclusion. -/
private theorem intervalSplitFilteredObject_local_stageIso_inv_comp_arrow
    (a b p : ℤ) (J : Set.Icc a b → 𝒜) :
    (intervalSplitFilteredObject_local_stageIso a b p J).inv ≫
        (intervalSplitStage a b J p).arrow =
      biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) := by
  -- Proof comment: this is the inverse-direction companion to the previous stage-arrow formula.
  simpa [intervalSplitFilteredObject_local, intervalTailFiltration_local,
    intervalSplitFilteredObject_local_stageIso] using
    intervalTailSubobject_local_iso_subtype_biproduct_inv_comp_arrow J p

/-- Helper for Lemma 13.26.5: the textbook ambient map `A.obj ⟶ ⨁ J_i` obtained by summing the
quotient-presentation components. -/
private noncomputable def quotientPresentationUnderlyingHom_local
    {A : FilF} {a b : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1))) :
    A.obj.obj ⟶ (intervalSplitFilteredObject_local a b (fun i ↦ (P i).J)).obj.obj :=
  biproduct.lift (fun i ↦ quotient_presentation_component P i)

/-- Helper for Lemma 13.26.5: the `i`-th projection of the summed textbook map is the chosen
quotient-presentation component. -/
@[simp]
private theorem quotientPresentationUnderlyingHom_local_π
    {A : FilF} {a b : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)))
    (i : Set.Icc a b) :
    quotientPresentationUnderlyingHom_local P ≫
        biproduct.π (fun j : Set.Icc a b ↦ (P j).J) i =
      quotient_presentation_component P i := by
  -- Proof comment: this is exactly the defining projection formula for the biproduct lift.
  simp [quotientPresentationUnderlyingHom_local]

/-- Helper for Lemma 13.26.5: on `F^p A`, every excluded component of the summed textbook map
still vanishes. -/
private theorem quotientPresentationUnderlyingHom_local_stage_component_zero_of_lt
    {A : FilF} {a b p : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)))
    (i : Set.Icc a b) (hip : i.1 < p) :
    (finiteStage A p).arrow ≫ quotientPresentationUnderlyingHom_local P ≫
        biproduct.π (fun j : Set.Icc a b ↦ (P j).J) i =
      0 := by
  -- Proof comment: after projecting the biproduct lift to the `i`-th summand, this is the
  -- previously established componentwise vanishing statement.
  calc
    (finiteStage A p).arrow ≫ quotientPresentationUnderlyingHom_local P ≫
        biproduct.π (fun j : Set.Icc a b ↦ (P j).J) i
        =
          (finiteStage A p).arrow ≫ quotient_presentation_component P i := by
            simp [quotientPresentationUnderlyingHom_local_π]
    _ = 0 := quotient_presentation_component_stage_zero_of_lt P i hip

/-- Helper for Lemma 13.26.5: if a component index is not in the `p`-tail, then the
corresponding stage component of the summed quotient map vanishes. -/
private theorem quotientPresentationUnderlyingHom_local_stage_component_zero_of_not_le
    {A : FilF} {a b p : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)))
    (i : Set.Icc a b) (hip : ¬ p ≤ i.1) :
    (finiteStage A p).arrow ≫ quotientPresentationUnderlyingHom_local P ≫
        biproduct.π (fun j : Set.Icc a b ↦ (P j).J) i =
      0 := by
  -- Proof comment: on integers, `¬ p ≤ i` is exactly `i < p`, so the previously proved
  -- componentwise vanishing lemma applies directly.
  exact quotientPresentationUnderlyingHom_local_stage_component_zero_of_lt P i (lt_of_not_ge hip)

/-- Helper for Lemma 13.26.5: a morphism into the interval biproduct factors through the `p`-tail
exactly when every excluded component vanishes. -/
private theorem intervalTailSubobject_local_factors_iff_componentZero
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) {W : 𝒜} (g : W ⟶ ⨁ J) :
    (intervalTailSubobject_local J p).Factors g ↔
      ∀ i : Set.Icc a b, ¬ p ≤ i.1 → g ≫ biproduct.π J i = 0 := by
  letI := intervalTailSubobject_local_splitMono J p
  change (Subobject.mk
      (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1))).Factors g ↔ _
  constructor
  · intro hg i hip
    rcases (Subobject.mk_factors_iff
        (biproduct.fromSubtype J (fun j : Set.Icc a b ↦ p ≤ j.1)) g).1 hg with
      ⟨gTail, hgTail⟩
    -- Proof comment: once the map factors through the tail inclusion, every projection to an
    -- excluded summand dies by the `fromSubtype_π` computation.
    calc
      g ≫ biproduct.π J i
          = gTail ≫ biproduct.fromSubtype J (fun j : Set.Icc a b ↦ p ≤ j.1) ≫
              biproduct.π J i := by
                rw [← hgTail]
                simp [Category.assoc]
      _ = 0 := by
            simp [biproduct.fromSubtype_π, hip, Category.assoc]
  · intro hg
    rw [Subobject.mk_factors_iff]
    let gTail : W ⟶ ⨁ fun j : { i : Set.Icc a b // p ≤ i.1 } ↦ J j.1 :=
      biproduct.lift (fun j : { i : Set.Icc a b // p ≤ i.1 } ↦ g ≫ biproduct.π J j.1)
    refine ⟨gTail, ?_⟩
    -- Proof comment: rebuild the factorization by taking exactly the surviving components of `g`
    -- on the subtype-indexed tail biproduct.
    apply biproduct.hom_ext
    intro i
    by_cases hip : p ≤ i.1
    · let j : { i : Set.Icc a b // p ≤ i.1 } := ⟨i, hip⟩
      have hπbase :
          biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) ≫ biproduct.π J i =
            biproduct.π (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) j := by
        simpa [biproduct.fromSubtype_π, j, hip]
      have hπ :
          (gTail ≫ biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) ≫
              biproduct.π J i =
            gTail ≫ biproduct.π (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) j := by
        rw [Category.assoc]
        exact congrArg (fun k ↦ gTail ≫ k) hπbase
      have hLift :
          gTail ≫ biproduct.π (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) j =
            g ≫ biproduct.π J i := by
        dsimp [gTail]
        simpa [j] using
          (show
            (biproduct.lift
                (fun j : { i : Set.Icc a b // p ≤ i.1 } ↦ g ≫ biproduct.π J j.1)) ≫
                biproduct.π (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) j =
              g ≫ biproduct.π J i from
            biproduct.lift_π
              (fun j : { i : Set.Icc a b // p ≤ i.1 } ↦ g ≫ biproduct.π J j.1)
              j)
      exact hπ.trans hLift
    · simp [biproduct.fromSubtype_π, hip, hg i hip, Category.assoc]

/-- Helper for Lemma 13.26.5: the summed quotient-presentation map sends `F^p A` into the `p`-tail
stage of the interval-split target. -/
private theorem quotientPresentationUnderlyingHom_local_preservesStage
    {A : FilF} {a b p : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1))) :
    (intervalSplitStage a b (fun i ↦ (P i).J) p).Factors
      ((finiteStage A p).arrow ≫ quotientPresentationUnderlyingHom_local P) := by
  -- Route correction: use the generic tail-factorization criterion so the proof stays entirely in
  -- the ambient biproduct spelling and never re-enters a witness-specific reassociation.
  rw [intervalSplitFilteredObject_local_stage_eq_tail]
  refine (intervalTailSubobject_local_factors_iff_componentZero
      (fun i : Set.Icc a b ↦ (P i).J)
      ((finiteStage A p).arrow ≫ quotientPresentationUnderlyingHom_local P)).2 ?_
  intro i hip
  -- Proof comment: the excluded components are exactly the components already proved to vanish on
  -- `F^p A`.
  simpa [Category.assoc] using
    quotientPresentationUnderlyingHom_local_stage_component_zero_of_not_le P i hip

/-- Helper for Lemma 13.26.5: package the summed quotient-presentation map as an ambient filtered
morphism into the interval-split target. -/
private abbrev quotientPresentationFilteredHom_local
    {A : FilF} {a b : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1))) :
    A.obj ⟶ (intervalSplitFilteredObject_local a b (fun i ↦ (P i).J)).obj :=
  { hom := quotientPresentationUnderlyingHom_local P
    preserves := fun p ↦ by
      let q : ℤ := OrderDual.ofDual p
      change (intervalSplitStage a b (fun i ↦ (P i).J) q).Factors
        ((finiteStage A q).arrow ≫ quotientPresentationUnderlyingHom_local P)
      exact quotientPresentationUnderlyingHom_local_preservesStage P }

/-- Helper for Lemma 13.26.5: if the next filtration stage is `⊥`, then the corresponding
quotient-presentation component is monic. -/
private theorem quotientPresentationComponent_mono_of_stageEqBot_local
    {A : FilF} {a b : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)))
    (i : Set.Icc a b) (hi : finiteStage A (i.1 + 1) = ⊥) :
    Mono (quotient_presentation_component P i) := by
  have hArrow :
      (finiteStage A (i.1 + 1)).arrow = (0 : (finiteStage A (i.1 + 1) : 𝒜) ⟶ A.obj.obj) := by
    -- Proof comment: rewriting the stage itself to `⊥` turns its subobject arrow into the
    -- explicit zero map.
    let e : (finiteStage A (i.1 + 1) : 𝒜) ≅ 0 :=
      Subobject.isoOfEqMk (finiteStage A (i.1 + 1))
        (0 : (0 : 𝒜) ⟶ A.obj.obj) (by
          simpa [Subobject.bot_eq_zero] using hi)
    exact (Limits.IsZero.of_iso (Limits.isZero_zero 𝒜) e).eq_of_src _ _
  haveI : IsIso (cokernel.π (finiteStage A (i.1 + 1)).arrow) := by
    -- Proof comment: the quotient map of a zero stage is the cokernel of a zero morphism.
    rw [hArrow]
    infer_instance
  -- Proof comment: the quotient factor is now an isomorphism, so the component map is monic by
  -- composition with the injective-presentation mono.
  rw [quotient_presentation_component]
  infer_instance

/-- Helper for Lemma 13.26.5: the bottom stage of a filtered object has the explicit zero-subobject
description. -/
private theorem stageEqMkZeroOfEqBot_local (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊥) :
    X.filtration.obj p = Subobject.mk (0 : (0 : 𝒜) ⟶ X.obj) := by
  -- Proof comment: rewrite the bottom subobject into the explicit zero-arrow model.
  simpa [Subobject.bot_eq_zero] using hp

/-- Helper for Lemma 13.26.5: a filtration stage equal to `⊥` has zero underlying object. -/
private theorem stageIsZeroOfEqBot_local (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊥) :
    IsZero (F^{p} X) := by
  let e : F^{p} X ≅ 0 :=
    Subobject.isoOfEqMk (X.filtration.obj p) (0 : (0 : 𝒜) ⟶ X.obj)
      (stageEqMkZeroOfEqBot_local X p hp)
  -- Proof comment: transport the zero-object structure across the canonical zero-stage
  -- isomorphism.
  exact Limits.IsZero.of_iso (Limits.isZero_zero 𝒜) e

/-- Helper for Lemma 13.26.5: vanishing after the quotient map means the morphism already factors
through the `p`-th filtration stage. -/
private theorem stageFactorsOfCokernelPiEqZero_local
    (X : FilteredObject 𝒜) {W : 𝒜} (g : W ⟶ X.obj) (p : ℤ)
    (hg : g ≫ cokernel.π (X.filtration.obj p).arrow = 0) :
    (X.filtration.obj p).Factors g := by
  have hKernel : (kernelSubobject (cokernel.π (X.filtration.obj p).arrow)).Factors g :=
    ⟨kernel.lift _ g hg, by simp⟩
  -- Proof comment: identify the stage with the kernel of its quotient projection and reuse the
  -- universal kernel factorization.
  rw [subobject_eq_kernel_cokernel (X.filtration.obj p)]
  exact hKernel

/-- Helper for Lemma 13.26.5: any morphism factoring through the `p`-tail of the interval-split
object has zero `i`-component whenever `i < p`. -/
private theorem intervalSplitFilteredObject_local_stage_component_eq_zero_of_lt
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) {W : 𝒜}
    (g : W ⟶ (intervalSplitFilteredObject_local a b J).obj.obj)
    (hg : (intervalSplitStage a b J p).Factors g)
    (i : Set.Icc a b) (hip : i.1 < p) :
    g ≫ biproduct.π J i = 0 := by
  letI := intervalTailSubobject_local_splitMono J p
  -- Route correction: unpack the factorization only after normalizing the target stage to the
  -- `Subobject.mk` owner; then the excluded projection is killed by `fromSubtype_π`.
  change (Subobject.mk
      (biproduct.fromSubtype J (fun j : Set.Icc a b ↦ p ≤ j.1))).Factors g at hg
  rcases (Subobject.mk_factors_iff
      (biproduct.fromSubtype J (fun j : Set.Icc a b ↦ p ≤ j.1)) g).1 hg with ⟨gTail, hgTail⟩
  have hi : ¬ p ≤ i.1 := by
    omega
  -- Proof comment: the factorization lands in the `p`-tail, so the `i`-projection vanishes
  -- whenever `i` lies strictly to the left of the tail.
  calc
    g ≫ biproduct.π J i
        = gTail ≫ biproduct.fromSubtype J (fun j : Set.Icc a b ↦ p ≤ j.1) ≫
            biproduct.π J i := by
              rw [← hgTail]
              simp [Category.assoc]
    _ = 0 := by
          simp [biproduct.fromSubtype_π, hi, Category.assoc]

/-- Helper for Lemma 13.26.5: if the `(p + 1)`-st filtration stage is already `⊤`, then the
`p`-th graded piece vanishes. -/
private theorem gradedPieceIsZeroOfSuccEqTop_local
    (X : FilteredObject 𝒜) (p : ℤ) (h : X.filtration.obj (p + 1) = ⊤) :
    IsZero (gr^{p} X) := by
  have hp : X.filtration.obj p = ⊤ := filtration_eq_top_of_le (by omega) h
  letI : IsIso (X.filtration.obj p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hp
  letI : IsIso (X.filtration.obj (p + 1)).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
  have hstage :
      X.filtration.stageInclusion p =
        (X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow := by
    -- Proof comment: both sides are the unique map whose composite with the `p`-stage arrow is
    -- the ambient inclusion of `F^(p + 1) X`.
    apply (cancel_mono (X.filtration.obj p).arrow).1
    calc
      X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow
          = (X.filtration.obj (p + 1)).arrow := by
              exact Subobject.ofLE_arrow _
      _ =
          ((X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow) ≫
            (X.filtration.obj p).arrow := by
              simp
  let f : F^{p + 1} X ⟶ F^{p} X :=
    (X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow
  letI : Epi f := by
    infer_instance
  -- Proof comment: the graded piece is the cokernel of an epimorphism, so it is zero.
  simpa [FilteredObject.gradedPiece, DecreasingFiltration.gradedPiece, f, hstage] using
    (Limits.isZero_cokernel_of_epi f)

/-- Helper for Lemma 13.26.5: if the `p`-th filtration stage is already `⊥`, then the `p`-th
graded piece vanishes. -/
private theorem gradedPieceIsZeroOfEqBot_local
    (X : FilteredObject 𝒜) (p : ℤ) (h : X.filtration.obj p = ⊥) :
    IsZero (gr^{p} X) := by
  have hp1 : X.filtration.obj (p + 1) = ⊥ := filtration_eq_bot_of_le (by omega) h
  let hzeroSucc : IsZero (F^{p + 1} X) := stageIsZeroOfEqBot_local X (p + 1) hp1
  let hzero : IsZero (F^{p} X) := stageIsZeroOfEqBot_local X p h
  letI : IsIso (X.filtration.stageInclusion p) := hzeroSucc.isIso hzero _
  -- Proof comment: both adjacent stages are zero, so the stage inclusion is an isomorphism and
  -- its cokernel, namely the graded piece, vanishes.
  simpa [FilteredObject.gradedPiece, DecreasingFiltration.gradedPiece] using
    (Limits.isZero_cokernel_of_epi (X.filtration.stageInclusion p))

/-- Helper for Lemma 13.26.5: an integer outside the interval `[a, b]` lies strictly to one side
of the window. -/
private theorem lt_left_or_right_of_not_mem_Icc
    {a b p : ℤ} (hp : p ∉ Set.Icc a b) :
    p < a ∨ b < p := by
  -- Proof comment: negating interval membership leaves exactly the two strict outside cases.
  by_contra h
  push_neg at h
  exact hp ⟨h.1, h.2⟩

/-- Helper for Lemma 13.26.5: the distinguished `p`-index lies in the `p`-tail but not in the
`(p + 1)`-tail. -/
private theorem distinguishedIndex_not_mem_succTail
    {a b p : ℤ} (hp : p ∈ Set.Icc a b) :
    ¬ p + 1 ≤ (⟨p, hp⟩ : Set.Icc a b).1 := by
  -- Proof comment: the distinguished interval index has value exactly `p`, so it cannot satisfy
  -- the stricter successor inequality.
  simpa using (show p < p + 1 by omega).not_ge

/-- Helper for Lemma 13.26.5: the local stage inclusion is the unique map whose composite with
the `p`-stage arrow is the ambient arrow of the `(p + 1)`-stage. -/
private theorem intervalSplitFilteredObject_local_stageInclusion_comp_arrow
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) :
    let X : FilteredObject 𝒜 := (intervalSplitFilteredObject_local a b J).obj
    X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow =
      (X.filtration.obj (p + 1)).arrow := by
  -- Proof comment: this is the defining `Subobject.ofLE_arrow` identity for adjacent stages in
  -- the decreasing filtration.
  let X : FilteredObject 𝒜 := (intervalSplitFilteredObject_local a b J).obj
  exact Subobject.ofLE_arrow _

/-- Helper for Lemma 13.26.5: the local stage-inclusion identity is available in the full owner
form, so later rewrites do not depend on a theorem-local `let`. -/
private theorem intervalSplitFilteredObject_local_stageInclusion_comp_arrow_owner
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) :
    ((intervalSplitFilteredObject_local a b J).obj.filtration.stageInclusion p) ≫
        ((intervalSplitFilteredObject_local a b J).obj.filtration.obj p).arrow =
      ((intervalSplitFilteredObject_local a b J).obj.filtration.obj (p + 1)).arrow := by
  -- Proof comment: this is the same `Subobject.ofLE_arrow` identity as above, but stated directly
  -- on the owner expression so later `rw` calls stay definitionally stable.
  simpa using
    intervalSplitFilteredObject_local_stageInclusion_comp_arrow (a := a) (b := b) (p := p) J

/-- Helper for Lemma 13.26.5: the local `p`-stage arrow is definitionally the canonical
`biproduct.fromSubtype` map for the `p`-tail after passing through the canonical stage carrier
identification. -/
private theorem intervalSplitFilteredObject_local_stage_arrow_eq_fromSubtype
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) :
    (intervalSplitFilteredObject_local_stageIso a b p J).inv ≫
        (intervalSplitStage a b J p).arrow =
      biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) := by
  -- Route correction: stay in the raw `Subobject.mk` owner instead of transporting through the
  -- old ad hoc stage decompositions; this is the one bridge from the stage carrier back to the
  -- canonical subtype biproduct.
  simpa using intervalSplitFilteredObject_local_stageIso_inv_comp_arrow a b p J

/-- Helper for Lemma 13.26.5: the distinguished `p`-summand of the `p`-tail stage becomes the
ambient `p`-summand after applying the local stage identification and stage arrow. -/
private theorem intervalSplitFilteredObject_local_distinguishedSummand_arrow
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) (hp : p ∈ Set.Icc a b) :
    let jp : { i : Set.Icc a b // p ≤ i.1 } := ⟨⟨p, hp⟩, le_rfl⟩
    biproduct.ι (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) jp ≫
        (intervalSplitFilteredObject_local_stageIso a b p J).inv ≫
        (intervalSplitStage a b J p).arrow =
      biproduct.ι J ⟨p, hp⟩ := by
  -- Proof comment: once the local stage carrier is rewritten to the canonical `p`-tail
  -- biproduct, the distinguished summand is just the standard subtype inclusion.
  dsimp
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ biproduct.ι (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J)
        ⟨⟨p, hp⟩, le_rfl⟩ ≫ k)
      (intervalSplitFilteredObject_local_stage_arrow_eq_fromSubtype (a := a) (b := b) (p := p) J)

/-- Helper for Lemma 13.26.5: the stage endomorphism used in the local stage isomorphism acts as
the identity on the strict successor tail. -/
private theorem intervalSplitFilteredObject_local_successorTailMap_eq
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) :
    biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) ≫
        biproduct.map (fun j : Set.Icc a b ↦ if p < j.1 then 𝟙 (J j) else 0) =
      biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) := by
  -- Proof comment: every index in the strict successor tail satisfies `p < i`, so the stage map
  -- restricts to the identity on each surviving summand.
  apply biproduct.hom_ext
  intro i
  by_cases hi : p + 1 ≤ i.1
  · have hpi : p < i.1 := by omega
    simp [biproduct.fromSubtype_π, hi, hpi, Category.assoc]
  · simp [biproduct.fromSubtype_π, hi, Category.assoc]

private theorem intervalSplitFilteredObject_local_successorTailRetract
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) :
    (intervalSplitStage a b J (p + 1)).arrow ≫
        biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) ≫
        (intervalSplitFilteredObject_local_stageIso a b (p + 1) J).inv =
      𝟙 _ := by
  -- Proof comment: cancel against the stage-carrier isomorphism and reduce the middle ambient
  -- composite to the standard `fromSubtype ≫ toSubtype = 𝟙` identity.
  apply (cancel_mono (intervalSplitFilteredObject_local_stageIso a b (p + 1) J).hom).1
  calc
    ((intervalSplitStage a b J (p + 1)).arrow ≫
        biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) ≫
        (intervalSplitFilteredObject_local_stageIso a b (p + 1) J).inv) ≫
        (intervalSplitFilteredObject_local_stageIso a b (p + 1) J).hom
        =
          (intervalSplitFilteredObject_local_stageIso a b (p + 1) J).hom ≫
            (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) ≫
              biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1)) := by
                rw [← intervalSplitFilteredObject_local_stageIso_hom_comp_fromSubtype (a := a)
                  (b := b) (p := p + 1) J]
                simp [Category.assoc]
    _ = (intervalSplitFilteredObject_local_stageIso a b (p + 1) J).hom := by
          have hmiddle :=
            congrArg
              (fun k ↦ (intervalSplitFilteredObject_local_stageIso a b (p + 1) J).hom ≫ k)
              (biproduct.fromSubtype_toSubtype (f := J)
                (p := fun i : Set.Icc a b ↦ p + 1 ≤ i.1))
          simpa [Category.assoc] using hmiddle

/-- Helper for Lemma 13.26.5: inside the interval window, the `p`-th graded piece of the local
interval-split object is canonically the distinguished `p`-summand. -/
private noncomputable def intervalSplitFilteredObject_local_gradedPieceIsoComponent
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) (hp : p ∈ Set.Icc a b) :
    gr^{p} ((intervalSplitFilteredObject_local a b J).obj) ≅ J ⟨p, hp⟩ := by
  -- TODO: split `F^p` as the distinguished `p`-summand plus the successor tail using
  -- `intervalSplitFilteredObject_local_successorTailRetract`, then identify the graded piece by
  -- transporting `biprod.isCokernelInrCokernelFork` across that binary split.
  sorry

/-- Helper for Lemma 13.26.5: the local interval-split target is filtered injective as soon as
each chosen summand is injective. -/
private theorem intervalSplitFilteredObject_local_isFilteredInjective
    {a b : ℤ} (J : Set.Icc a b → 𝒜) (hJ : ∀ i, Injective (J i)) :
    IsFilteredInjective (intervalSplitFilteredObject_local a b J) := by
  refine ⟨fun p ↦ ?_⟩
  by_cases hp : p ∈ Set.Icc a b
  · let e := intervalSplitFilteredObject_local_gradedPieceIsoComponent (J := J) hp
    -- Proof comment: inside the interval, the `p`-th graded piece is exactly the chosen
    -- `p`-summand.
    exact Injective.of_iso e.symm (hJ ⟨p, hp⟩)
  · have hp' : p < a ∨ b < p :=
      lt_left_or_right_of_not_mem_Icc hp
    rcases hp' with hpa | hbp
    · have htop :
        (intervalSplitFilteredObject_local a b J).obj.filtration.obj (p + 1) = ⊤ := by
        simpa [intervalSplitFilteredObject_local, intervalTailFiltration_local] using
          intervalTailSubobject_local_eq_top_of_le_left (J := J) (p := p + 1) (by omega)
      -- Proof comment: weakly left of the interval, the next stage is already top, so the
      -- graded piece vanishes.
      exact (gradedPieceIsZeroOfSuccEqTop_local
        ((intervalSplitFilteredObject_local a b J).obj) p htop).injective
    · have hbot :
        (intervalSplitFilteredObject_local a b J).obj.filtration.obj p = ⊥ := by
        simpa [intervalSplitFilteredObject_local, intervalTailFiltration_local] using
          intervalTailSubobject_local_eq_bot_of_right_lt (J := J) (p := p) hbp
      -- Proof comment: strictly right of the interval, the `p`-tail is empty, so the graded
      -- piece vanishes as well.
      exact (gradedPieceIsZeroOfEqBot_local
        ((intervalSplitFilteredObject_local a b J).obj) p hbot).injective

/-- Helper for Lemma 13.26.5: if the top quotient component is monic, then the full summed
quotient-presentation map is monic. -/
private theorem quotientPresentationUnderlyingHom_local_mono
    {A : FilF} {a b : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)))
    (hab : a ≤ b) (hb : finiteStage A (b + 1) = ⊥) :
    Mono (quotientPresentationUnderlyingHom_local P) := by
  let i : Set.Icc a b := ⟨b, hab, le_rfl⟩
  letI : Mono (quotient_presentation_component P i) :=
    quotientPresentationComponent_mono_of_stageEqBot_local P i hb
  have hcomp :
      quotientPresentationUnderlyingHom_local P ≫
          biproduct.π (fun j : Set.Icc a b ↦ (P j).J) i =
        quotient_presentation_component P i := by
    -- Proof comment: the `b`-th biproduct projection of the summed map is exactly the top
    -- quotient-presentation component.
    simpa using quotientPresentationUnderlyingHom_local_π P i
  -- Proof comment: the full summed map is monic because one of its projections is already monic.
  exact show Mono (quotientPresentationUnderlyingHom_local P) from mono_of_mono_fac hcomp

/-- Helper for Lemma 13.26.5: in the middle range `a < p ≤ b + 1`, the pullback of the `p`-th
target stage along the summed quotient map lies inside `F^p A`. -/
private theorem quotientPresentationFilteredHom_local_pullbackStage_le_mid
    {A : FilF} {a b p : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)))
    (hpa : a < p) (hpb : p ≤ b + 1) :
    ((Subobject.pullback (quotientPresentationFilteredHom_local P).hom).obj
      (intervalSplitStage a b (fun i ↦ (P i).J) p)) ≤ finiteStage A p := by
  let uAmbient := quotientPresentationFilteredHom_local P
  let T := intervalSplitStage a b (fun i ↦ (P i).J) p
  let S := (Subobject.pullback uAmbient.hom).obj T
  let i : Set.Icc a b := ⟨p - 1, by omega, by omega⟩
  have hi_succ : i.1 + 1 = p := by
    change (p - 1) + 1 = p
    omega
  refine Subobject.le_of_factors ?_
  have hTargetFactors : T.Factors (S.arrow ≫ uAmbient.hom) := by
    -- Proof comment: the pullback arrow is defined by the universal factorization into the target
    -- `p`-stage.
    exact (pullback_factors_iff uAmbient.hom T S.arrow).1 (Subobject.factors_self S)
  have hComponentZero :
      S.arrow ≫ uAmbient.hom ≫ biproduct.π (fun j : Set.Icc a b ↦ (P j).J) i = 0 := by
    -- Proof comment: the chosen index `i = p - 1` lies strictly to the left of the `p`-tail, so
    -- the corresponding component must vanish on any morphism landing in that tail stage.
    have hi_lt : i.1 < p := by
      change p - 1 < p
      omega
    simpa [uAmbient, T, S, Category.assoc] using
      intervalSplitFilteredObject_local_stage_component_eq_zero_of_lt
        (fun j : Set.Icc a b ↦ (P j).J) (S.arrow ≫ uAmbient.hom) hTargetFactors i hi_lt
  have hQuotientComponentZero :
      S.arrow ≫ quotient_presentation_component P i = 0 := by
    -- Proof comment: the chosen biproduct component is exactly the `i`-th quotient-presentation
    -- component of the summed map.
    simpa [uAmbient, quotientPresentationFilteredHom_local, Category.assoc] using hComponentZero
  have hQuotientZero :
      S.arrow ≫ cokernel.π (finiteStage A p).arrow = 0 := by
    -- Proof comment: the chosen injective-presentation component is monic, so the vanishing of
    -- the composed component already forces the quotient map itself to vanish.
    have hQuotientZero_i :
        S.arrow ≫ cokernel.π (finiteStage A (i.1 + 1)).arrow = 0 := by
      apply (cancel_mono (P i).f).1
      simpa [quotient_presentation_component, stage_quotient, Category.assoc] using
        hQuotientComponentZero
    rw [← hi_succ]
    exact hQuotientZero_i
  -- Proof comment: a morphism killed by the quotient map factors through the corresponding
  -- filtration stage.
  exact stageFactorsOfCokernelPiEqZero_local A.obj S.arrow p hQuotientZero

/-- Helper for Lemma 13.26.5: every pullback stage of the summed quotient-presentation map lies in
the corresponding source stage. -/
private theorem quotientPresentationFilteredHom_local_pullbackStage_le
    {A : FilF} {a b q : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)))
    [Mono (quotientPresentationFilteredHom_local P).hom]
    (ha : finiteStage A a = ⊤) (_hb : finiteStage A (b + 1) = ⊥) :
    ((Subobject.pullback (quotientPresentationFilteredHom_local P).hom).obj
      (intervalSplitStage a b (fun i ↦ (P i).J) q)) ≤ finiteStage A q := by
  by_cases hqa : q ≤ a
  · have htop : finiteStage A q = ⊤ := by
      exact filtration_eq_top_of_le hqa ha
    rw [htop]
    exact le_top
  · have hlt : a < q := by
      omega
    by_cases hqb : q ≤ b + 1
    · exact quotientPresentationFilteredHom_local_pullbackStage_le_mid
        P hlt hqb
    · have htarget :
          intervalSplitStage a b (fun i ↦ (P i).J) q = ⊥ := by
        rw [intervalSplitFilteredObject_local_stage_eq_tail]
        have hright : b < q := by
          omega
        exact intervalTailSubobject_local_eq_bot_of_right_lt (fun i ↦ (P i).J) hright
      rw [htarget, pullback_bot_of_mono]
      exact bot_le

/-- Helper for Lemma 13.26.5: the assembled interval-split embedding is strict. -/
private theorem quotientPresentationFilteredHom_local_strict
    {A : FilF} {a b : ℤ}
    (hab : a ≤ b) (ha : finiteStage A a = ⊤) (hb : finiteStage A (b + 1) = ⊥)
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1))) :
    Strict (quotientPresentationFilteredHom_local P) := by
  haveI : Mono (quotientPresentationFilteredHom_local P).hom :=
    quotientPresentationUnderlyingHom_local_mono P hab hb
  -- Proof comment: strictness is exactly the induced-filtration identity. The forward inclusion is
  -- stage preservation, while the reverse inclusion is handled by the left/middle/right interval
  -- analysis extracted above.
  refine (strict_iff_induced_filtration_of_mono (quotientPresentationFilteredHom_local P)).2 ?_
  refine OrderHom.ext _ _ ?_
  funext p
  let q : ℤ := OrderDual.ofDual p
  change finiteStage A q =
    (Subobject.pullback (quotientPresentationFilteredHom_local P).hom).obj
      (intervalSplitStage a b (fun i ↦ (P i).J) q)
  refine le_antisymm ?_ ?_
  · simpa [q] using FilteredObject.Hom.pullback_preserves
      (quotientPresentationFilteredHom_local P) q
  · exact quotientPresentationFilteredHom_local_pullbackStage_le
      P ha hb

-- Proof sketch: choose a finite interval `[a, b]` supporting the filtration of `A`, embed each
-- quotient `A/F^(n + 1)A` into an injective object, assemble these component maps into an
-- interval-split filtered object, detect monicity on the top quotient, and prove strictness from
-- the induced-filtration criterion.
/-- Lemma 13.26.5: every object of `Fil^f(𝒜)` admits a strict monomorphism into a filtered
injective object. -/
@[stacks 05TS]
theorem exists_strictMono_to_filteredInjective
    (A : Fil^f(𝒜)) :
    ∃ (I : 𝓘^f(𝒜)) (u : A ⟶ I.obj), Mono u ∧ Strict u.hom := by
  rcases ordered_window_of_isFinite A with ⟨a, b, hab, ha, hb⟩
  let P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)) :=
    fun i ↦ (EnoughInjectives.presentation (stage_quotient A.obj (i.1 + 1))).some
  let target : FilF := intervalSplitFilteredObject_local a b (fun i ↦ (P i).J)
  let uAmbient : A.obj ⟶ target.obj := quotientPresentationFilteredHom_local P
  haveI : Mono uAmbient.hom :=
    quotientPresentationUnderlyingHom_local_mono P hab hb
  have hStrictAmbient : Strict uAmbient := by
    simpa [uAmbient] using
      quotientPresentationFilteredHom_local_strict hab ha hb P
  let I : 𝓘^f(𝒜) :=
    ⟨target,
      intervalSplitFilteredObject_local_isFilteredInjective
        (fun i ↦ (P i).J) (fun i ↦ inferInstance)⟩
  let u : A ⟶ I.obj := ObjectProperty.homMk uAmbient
  have hMonoAmbient : Mono uAmbient := by
    exact FilteredObject.forget.mono_of_mono_map (show Mono uAmbient.hom by infer_instance)
  have hMono : Mono u := by
    let ιfin : FilF ⥤ Fil(𝒜) :=
      ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))
    exact ιfin.mono_of_mono_map (by simpa [u] using hMonoAmbient)
  have hStrict : Strict u.hom := by
    -- Proof comment: `ObjectProperty.homMk` does not change the underlying filtered morphism, so
    -- strictness is exactly the ambient strictness already proved.
    simpa [u] using hStrictAmbient
  exact ⟨I, u, hMono, hStrict⟩

end

end CategoryTheory
