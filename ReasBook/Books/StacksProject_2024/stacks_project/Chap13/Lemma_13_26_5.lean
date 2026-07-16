import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_19_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_13_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open FilteredObject.Hom
open scoped CategoryTheory

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

/-- Helper for Lemma 13.26.5: choose an ordered finite window containing all nontrivial
filtration behaviour. -/
private theorem ordered_window_of_isFinite (A : FilF) :
    ∃ a b : ℤ, a ≤ b ∧ A.obj.filtration.obj a = ⊤ ∧ A.obj.filtration.obj (b + 1) = ⊥ := by
  rcases A.property with ⟨t, m, htop, hbot⟩
  refine ⟨min t m, max t m, min_le_max, ?_, ?_⟩
  · -- Proof comment: moving left from a top stage keeps the filtration equal to `⊤`.
    exact filtration_eq_top_of_le (X := A.obj) (min_le_left _ _) htop
  · -- Proof comment: moving right from a zero stage keeps the filtration equal to `⊥`.
    have hm : m ≤ max t m + 1 := by
      omega
    exact filtration_eq_bot_of_le (X := A.obj) hm hbot

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
  simpa using (pullback.condition (f := (⊥ : Subobject Y).arrow) (g := f)).symm

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
  cokernel.π (A.obj.filtration.obj (i.1 + 1)).arrow ≫ (P i).f

/-- Helper for Lemma 13.26.5: on `F^p A`, every component indexed strictly below `p` vanishes. -/
private theorem quotient_presentation_component_stage_zero_of_lt
    {A : FilF} {a b p : ℤ}
    (P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)))
    (i : Set.Icc a b) (hip : i.1 < p) :
    (A.obj.filtration.obj p).arrow ≫ quotient_presentation_component P i = 0 := by
  let v :
      (A.obj.filtration.obj p : 𝒜) ⟶ (A.obj.filtration.obj (i.1 + 1) : 𝒜) :=
    Subobject.ofLE _ _ (A.obj.filtration.antitone_obj (by omega))
  have hquot :
      (A.obj.filtration.obj p).arrow ≫
        cokernel.π (A.obj.filtration.obj (i.1 + 1)).arrow = 0 := by
    calc
      (A.obj.filtration.obj p).arrow ≫
          cokernel.π (A.obj.filtration.obj (i.1 + 1)).arrow
          =
            (v ≫ (A.obj.filtration.obj (i.1 + 1)).arrow) ≫
              cokernel.π (A.obj.filtration.obj (i.1 + 1)).arrow := by
                simp [v]
      _ = v ≫
            ((A.obj.filtration.obj (i.1 + 1)).arrow ≫
              cokernel.π (A.obj.filtration.obj (i.1 + 1)).arrow) := by
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
  letI := intervalTailSubobject_local_splitMono (J := J) p
  Subobject.mk (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1)

/-- Helper for Lemma 13.26.5: the carrier of the local `p`-tail subobject is canonically the
corresponding subtype biproduct. -/
@[reducible] private noncomputable def intervalTailSubobject_local_iso_subtype_biproduct
    {a b : ℤ} (J : Set.Icc a b → 𝒜) (p : ℤ) :
    (((intervalTailSubobject_local (J := J) p : Subobject (⨁ J)) : 𝒜)) ≅
      (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1) :=
  letI := intervalTailSubobject_local_splitMono (J := J) p
  Subobject.underlyingIso (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1)

/-- Helper for Lemma 13.26.5: under the canonical tail-carrier identification, the subobject
arrow is the expected `biproduct.fromSubtype`. -/
private theorem intervalTailSubobject_local_iso_subtype_biproduct_hom_comp_fromSubtype
    {a b : ℤ} (J : Set.Icc a b → 𝒜) (p : ℤ) :
    (intervalTailSubobject_local_iso_subtype_biproduct (J := J) p).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
      (intervalTailSubobject_local (J := J) p).arrow := by
  -- Proof comment: `intervalTailSubobject_local` is defined by the same split mono, so the
  -- canonical underlying isomorphism composes back to the defining subobject arrow.
  letI := intervalTailSubobject_local_splitMono (J := J) p
  change
    ((Subobject.underlyingIso (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1))).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) =
      (intervalTailSubobject_local (J := J) p).arrow
  rw [Subobject.underlyingIso_hom_comp_eq_mk]

/-- Helper for Lemma 13.26.5: in the same identification, the inverse map followed by the
subobject arrow is again the canonical `biproduct.fromSubtype`. -/
private theorem intervalTailSubobject_local_iso_subtype_biproduct_inv_comp_arrow
    {a b : ℤ} (J : Set.Icc a b → 𝒜) (p : ℤ) :
    (intervalTailSubobject_local_iso_subtype_biproduct (J := J) p).inv ≫
        (intervalTailSubobject_local (J := J) p).arrow =
      biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) := by
  -- Proof comment: compose the previous arrow formula on the left with the inverse of the
  -- canonical carrier identification.
  calc
    (intervalTailSubobject_local_iso_subtype_biproduct (J := J) p).inv ≫
        (intervalTailSubobject_local (J := J) p).arrow
        =
          (intervalTailSubobject_local_iso_subtype_biproduct (J := J) p).inv ≫
            ((intervalTailSubobject_local_iso_subtype_biproduct (J := J) p).hom ≫
              biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) := by
                rw [intervalTailSubobject_local_iso_subtype_biproduct_hom_comp_fromSubtype
                  (J := J) (p := p)]
    _ = biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) := by
          simp [Category.assoc]

/-- Helper for Lemma 13.26.5: increasing the filtration index shrinks the interval tail. -/
private theorem intervalTailSubobject_local_antitone
    {a b : ℤ} (J : Set.Icc a b → 𝒜) {p q : ℤ} (hpq : p ≤ q) :
    intervalTailSubobject_local (J := J) q ≤ intervalTailSubobject_local (J := J) p := by
  -- Proof comment: every `q`-tail summand also satisfies the weaker bound `p ≤ i.1`, so the
  -- `q`-tail inclusion factors through the `p`-tail by the larger-tail projection.
  letI := intervalTailSubobject_local_splitMono (J := J) p
  letI := intervalTailSubobject_local_splitMono (J := J) q
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
    (((intervalTailSubobject_local (J := J) q : Subobject (⨁ J)) : 𝒜)) ⟶
      (((intervalTailSubobject_local (J := J) p : Subobject (⨁ J)) : 𝒜)) :=
  Subobject.ofLE _ _ (intervalTailSubobject_local_antitone (J := J) hpq)

/-- Helper for Lemma 13.26.5: the canonical map from the `q`-tail carrier to the `p`-tail
carrier composes to the expected ambient tail inclusion. -/
private theorem intervalTailSubobject_local_factor_of_le_arrow
    {a b : ℤ} (J : Set.Icc a b → 𝒜) {p q : ℤ} (hpq : p ≤ q) :
    intervalTailSubobject_local_factor_of_le (J := J) hpq ≫
        (intervalTailSubobject_local (J := J) p).arrow =
      (intervalTailSubobject_local (J := J) q).arrow := by
  -- Proof comment: this is just the defining commutative square for the canonical subobject map.
  simpa [intervalTailSubobject_local_factor_of_le] using
    (Subobject.ofLE_arrow (intervalTailSubobject_local_antitone (J := J) hpq))

/-- Helper for Lemma 13.26.5: the interval tails define a decreasing filtration. -/
private theorem intervalTailFiltration_local_monotone
    {a b : ℤ} (J : Set.Icc a b → 𝒜) :
    Monotone (fun p : ℤᵒᵈ ↦ intervalTailSubobject_local (J := J) p) := by
  intro p q hpq
  -- Proof comment: monotonicity on `ℤᵒᵈ` is exactly the antitonicity statement on `ℤ`.
  simpa using
    intervalTailSubobject_local_antitone (J := J)
      (p := OrderDual.ofDual q) (q := OrderDual.ofDual p)
      (show OrderDual.ofDual q ≤ OrderDual.ofDual p from hpq)

/-- Helper for Lemma 13.26.5: the tail subobjects package into a finite decreasing filtration on
the interval biproduct. -/
@[reducible] private noncomputable def intervalTailFiltration_local
    {a b : ℤ} (J : Set.Icc a b → 𝒜) :
    DecreasingFiltration (⨁ J) :=
  { toFun := fun p ↦ intervalTailSubobject_local (J := J) p
    monotone' := intervalTailFiltration_local_monotone (J := J) }

/-- Helper for Lemma 13.26.5: every stage weakly to the left of the interval is the whole
interval biproduct. -/
private theorem intervalTailSubobject_local_eq_top_of_le_left
    {a b p : ℤ} (J : Set.Icc a b → 𝒜) (hp : p ≤ a) :
    intervalTailSubobject_local (J := J) p = ⊤ := by
  -- Proof comment: every index in `[a, b]` satisfies `p ≤ i.1`, so the tail inclusion is an
  -- isomorphism with inverse the corresponding subtype projection.
  letI := intervalTailSubobject_local_splitMono (J := J) p
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
    intervalTailSubobject_local (J := J) p = ⊥ := by
  -- Proof comment: no index in `[a, b]` survives beyond the right endpoint, so the tail
  -- inclusion is the zero morphism and hence defines the bottom subobject.
  letI := intervalTailSubobject_local_splitMono (J := J) p
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
       filtration := intervalTailFiltration_local (J := J) } : FilteredObject 𝒜).IsFinite := by
  refine ⟨a, b + 1, ?_, ?_⟩
  · -- Proof comment: the left endpoint already contains every interval summand.
    simpa [intervalTailFiltration_local] using
      intervalTailSubobject_local_eq_top_of_le_left (J := J) (p := a) le_rfl
  · -- Proof comment: the stage immediately to the right of the window is the empty tail.
    simpa [intervalTailFiltration_local] using
      intervalTailSubobject_local_eq_bot_of_right_lt (J := J) (p := b + 1) (by omega)

/-- Helper for Lemma 13.26.5: the finite filtered object built from the interval-indexed injective
targets with the tail filtration. -/
@[reducible] private noncomputable def intervalSplitFilteredObject_local
    (a b : ℤ) (J : Set.Icc a b → 𝒜) :
    FilF :=
  ⟨{ obj := ⨁ J
     filtration := intervalTailFiltration_local (J := J) },
    intervalSplitFilteredObject_local_isFinite (J := J)⟩

/-- Helper for Lemma 13.26.5: the `p`-th stage of the local interval-tail object is canonically
isomorphic to the expected tail biproduct, and under this identification its arrow is the canonical
tail inclusion. -/
private theorem intervalSplitFilteredObject_stage_arrow_eq_fromSubtype_local
    (a b p : ℤ) (J : Set.Icc a b → 𝒜) :
    ∃ e :
      (((intervalSplitFilteredObject_local a b J).obj.filtration.obj p : Subobject _ ) : 𝒜) ≅
        (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1),
      e.hom ≫ biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
        ((intervalSplitFilteredObject_local a b J).obj.filtration.obj p).arrow := by
  -- Proof comment: the `p`-th stage is definitionally the local tail subobject, so we can reuse
  -- the canonical tail-carrier identification instead of rebuilding it ad hoc.
  letI := intervalTailSubobject_local_splitMono (J := J) p
  refine ⟨intervalTailSubobject_local_iso_subtype_biproduct (J := J) p, ?_⟩
  simpa [intervalSplitFilteredObject_local, intervalTailFiltration_local] using
    intervalTailSubobject_local_iso_subtype_biproduct_hom_comp_fromSubtype
      (J := J) (p := p)

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
    (A.obj.filtration.obj p).arrow ≫ quotientPresentationUnderlyingHom_local P ≫
        biproduct.π (fun j : Set.Icc a b ↦ (P j).J) i =
      0 := by
  -- Proof comment: after projecting the biproduct lift to the `i`-th summand, this is the
  -- previously established componentwise vanishing statement.
  calc
    (A.obj.filtration.obj p).arrow ≫ quotientPresentationUnderlyingHom_local P ≫
        biproduct.π (fun j : Set.Icc a b ↦ (P j).J) i
        =
          (A.obj.filtration.obj p).arrow ≫ quotient_presentation_component P i := by
            simp [Category.assoc, quotientPresentationUnderlyingHom_local_π]
    _ = 0 := quotient_presentation_component_stage_zero_of_lt P i hip

-- Proof sketch: choose a finite interval `[a, b]` supporting the filtration of `A`, embed each
-- quotient `A/F^(n + 1)A` into an injective object, assemble these component maps into an
-- interval-split filtered object, detect monicity on the top quotient, and prove strictness from
-- the induced-filtration criterion.
/-- Lemma 13.26.5: every object of `Fil^f(𝒜)` admits a strict monomorphism into a filtered
injective object. -/
theorem exists_strictMono_to_filteredInjective
    (A : Fil^f(𝒜)) :
    ∃ (I : 𝓘^f(𝒜)) (u : A ⟶ I.obj), Mono u ∧ Strict u.hom := by
  classical
  rcases ordered_window_of_isFinite (A := A) with ⟨a, b, hab, ha, hb⟩
  let P : ∀ i : Set.Icc a b, InjectivePresentation (stage_quotient A.obj (i.1 + 1)) :=
    fun i ↦ Classical.choice (EnoughInjectives.presentation (stage_quotient A.obj (i.1 + 1)))
  let J : Set.Icc a b → 𝒜 := fun i ↦ (P i).J
  have hJ : ∀ i, Injective (J i) := by
    intro i
    dsimp [J]
    exact (P i).injective
  let I₀ : FilF := intervalSplitFilteredObject_local a b J
  let u₀ : A.obj.obj ⟶ I₀.obj.obj := quotientPresentationUnderlyingHom_local P
  -- Route correction: the public interval-split owner route from `Lemma_13_26_2` and the Chapter
  -- 12 strictness owner route from `Lemma_12_19_7` both force `lake lean` through broken upstream
  -- modules in this workspace, so the remaining work must stay entirely local to this file.
  -- TODO: the carrier-level transport problem is now resolved by
  -- `intervalTailSubobject_local_iso_subtype_biproduct`,
  -- `intervalTailSubobject_local_factor_of_le`, and the rewritten stage-arrow API; the
  -- remaining work is to package `u₀` as a filtered morphism, prove `IsFilteredInjective I₀`,
  -- detect monicity on the top
  -- component using `hb`, and finish
  -- strictness from the pullback criterion `strict_iff_induced_filtration_of_mono`.
  sorry

end

end CategoryTheory
