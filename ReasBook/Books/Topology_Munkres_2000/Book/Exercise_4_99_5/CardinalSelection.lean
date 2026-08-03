module

public import Mathlib.SetTheory.Cardinal.Continuum

public section

open Set

/-- Helper for Exercise 4.99.5: a family of full-cardinality sets indexed by at most the
carrier has distinct representatives. -/
lemma existsInjective_mem_of_cardinalMk_le
    {I K : Type u} (A : I → Set K) (hI : Cardinal.mk I ≤ Cardinal.mk K)
    (hA : ∀ i, Cardinal.mk K ≤ Cardinal.mk (A i)) :
    ∃ f : I → K, Function.Injective f ∧ ∀ i, f i ∈ A i := by
  classical
  -- Embed the index set into the initial ordinal of the carrier cardinal.
  have hI' : Cardinal.mk I ≤ Cardinal.mk (Cardinal.mk K).ord.ToType := by
    simpa only [Cardinal.mk_ord_toType] using hI
  obtain ⟨e⟩ := (Cardinal.le_def I (Cardinal.mk K).ord.ToType).mp hI'
  let r : I → I → Prop := fun i j ↦ e i < e j
  have hrwf : WellFounded r := by
    exact WellFounded.onFun (f := e)
      (inferInstance : WellFoundedLT (Cardinal.mk K).ord.ToType).wf
  -- At each stage, all earlier choices form a set smaller than the next candidate set.
  have hFresh (i : I)
      (previous : ∀ j : I, r j i → K) :
      (A i \ Set.range (fun j : {j // r j i} ↦ previous j j.property)).Nonempty := by
    apply Cardinal.sdiff_nonempty_of_mk_lt_mk
    refine (Cardinal.mk_range_le.trans ?_).trans_lt
      ((Cardinal.mk_Iio_lt (e i) (by
        rw [Cardinal.mk_ord_toType, Ordinal.type_toType])).trans_le
          ((Cardinal.mk_ord_toType _).le.trans (hA i)))
    exact Cardinal.mk_le_of_injective (f := fun j : {j // r j i} ↦
      ⟨e j, j.property⟩) (fun j k hjk ↦
        Subtype.ext (e.injective (congrArg Subtype.val hjk)))
  let step : ∀ i : I, (∀ j : I, r j i → K) → K :=
    fun i previous ↦ Classical.choose (hFresh i previous)
  let f : I → K :=
    WellFounded.fix hrwf step
  have hf_eq (i : I) :
      f i = step i (fun j _ ↦ f j) := by
    exact WellFounded.fix_eq hrwf step i
  have hf_mem (i : I) : f i ∈ A i := by
    rw [hf_eq]
    exact (Classical.choose_spec (hFresh i (fun j _ ↦ f j))).1
  refine ⟨f, ?_, hf_mem⟩
  intro i j hij
  rcases lt_trichotomy (e i) (e j) with hijOrder | hijEq | hjiOrder
  · have hnot : f j ∉ Set.range
        (fun k : {k // r k j} ↦ f k) := by
      rw [hf_eq]
      exact (Classical.choose_spec (hFresh j (fun k _ ↦ f k))).2
    exact False.elim (hnot ⟨⟨i, hijOrder⟩, hij⟩)
  · exact e.injective hijEq
  · have hnot : f i ∉ Set.range
        (fun k : {k // r k i} ↦ f k) := by
      rw [hf_eq]
      exact (Classical.choose_spec (hFresh i (fun k _ ↦ f k))).2
    exact False.elim (hnot ⟨⟨j, hjiOrder⟩, hij.symm⟩)
