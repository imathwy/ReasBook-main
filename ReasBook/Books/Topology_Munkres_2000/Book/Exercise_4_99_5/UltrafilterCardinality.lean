module

public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Topology.Compactification.StoneCech

public section

open Function Filter Set

/-- Helper for Exercise 4.99.5: finite trace codes realizing Boolean patterns of subsets of `ℕ`. -/
private abbrev FiniteTraceCode := Σ s : Finset ℕ, Set (Set s)

/-- Helper for Exercise 4.99.5: restrict a subset of `ℕ` to finitely many coordinates. -/
private def finiteTrace (A : Set ℕ) (s : Finset ℕ) : Set s :=
  {n | (n : ℕ) ∈ A}

/-- Helper for Exercise 4.99.5: codes accepting a given subset's finite trace. -/
private def independentTraceSet (A : Set ℕ) : Set FiniteTraceCode :=
  {c | finiteTrace A c.1 ∈ c.2}

/-- Helper for Exercise 4.99.5: a trace set with the sign prescribed by an indexing family. -/
private noncomputable def signedTraceSet (R : Set (Set ℕ)) (A : Set ℕ) :
    Set FiniteTraceCode :=
  @ite (Set FiniteTraceCode) (A ∈ R) (Classical.propDecidable _)
    (independentTraceSet A) (independentTraceSet A)ᶜ

/-- Helper for Exercise 4.99.5: finitely many subsets of `ℕ` are separated on finite coordinates. -/
private lemma existsFiniteTraceInjOn (F : Finset (Set ℕ)) :
    ∃ s : Finset ℕ, Set.InjOn (fun A : Set ℕ ↦ finiteTrace A s) F := by
  classical
  -- Choose one coordinate witnessing each unequal ordered pair in the family.
  have hDifferent (A B : Set ℕ) (hAB : A ≠ B) :
      ∃ n : ℕ, (n ∈ A) ≠ (n ∈ B) := by
    by_contra h
    push Not at h
    exact hAB (Set.ext fun n ↦ iff_of_eq (h n))
  let witness (A B : Set ℕ) : ℕ :=
    if hAB : A = B then 0 else Classical.choose (hDifferent A B hAB)
  have hwitness {A B : Set ℕ} (hAB : A ≠ B) :
      (witness A B ∈ A) ≠ (witness A B ∈ B) := by
    simp only [witness, dif_neg hAB]
    exact Classical.choose_spec (hDifferent A B hAB)
  let s : Finset ℕ := (F ×ˢ F).image (fun p ↦ witness p.1 p.2)
  refine ⟨s, fun A hAF B hBF htrace ↦ ?_⟩
  by_contra hAB
  have hwmem : witness A B ∈ s := by
    exact Finset.mem_image.mpr ⟨(A, B), Finset.mem_product.mpr ⟨hAF, hBF⟩, rfl⟩
  have hsame : (witness A B ∈ A) ↔ (witness A B ∈ B) := by
    have := Set.ext_iff.mp htrace ⟨witness A B, hwmem⟩
    exact this
  exact hwitness hAB (propext hsame)

/-- Helper for Exercise 4.99.5: one finite trace code realizes any finite Boolean pattern. -/
private lemma signedTraceSets_finiteInter_nonempty (R : Set (Set ℕ))
    (F : Finset (Set ℕ)) :
    ∃ c : FiniteTraceCode, ∀ A ∈ F,
      c ∈ signedTraceSet R A := by
  classical
  -- Separate the indices, then accept exactly the traces carrying a positive sign.
  obtain ⟨s, hs⟩ := existsFiniteTraceInjOn F
  let accepted : Set (Set s) :=
    {t | ∃ A ∈ F, A ∈ R ∧ finiteTrace A s = t}
  refine ⟨⟨s, accepted⟩, fun A hAF ↦ ?_⟩
  by_cases hAR : A ∈ R
  · simp only [signedTraceSet, if_pos hAR, independentTraceSet, Set.mem_setOf_eq]
    exact ⟨A, hAF, hAR, rfl⟩
  · simp only [signedTraceSet, if_neg hAR, Set.mem_compl_iff,
      independentTraceSet, Set.mem_setOf_eq]
    rintro ⟨B, hBF, hBR, htrace⟩
    have hAB : A = B := hs hAF hBF htrace.symm
    exact hAR (hAB.symm ▸ hBR)

/-- Helper for Exercise 4.99.5: every sign choice on the trace family extends to an ultrafilter. -/
private lemma exists_ultrafilter_signedTraceSets (R : Set (Set ℕ)) :
    ∃ F : Ultrafilter FiniteTraceCode, ∀ A : Set ℕ,
      signedTraceSet R A ∈ F := by
  classical
  -- The finite-pattern lemma gives the finite-intersection property needed for extension.
  let signed : Set ℕ → Set FiniteTraceCode := fun A ↦
    signedTraceSet R A
  obtain ⟨F, hF⟩ := Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty
      (Set.range signed) (fun T hT ↦ by
        let index (V : T) : Set ℕ := Classical.choose (hT V.property)
        have hindex (V : T) : signed (index V) = V :=
          Classical.choose_spec (hT V.property)
        let I : Finset (Set ℕ) := T.attach.image index
        obtain ⟨c, hc⟩ := signedTraceSets_finiteInter_nonempty R I
        refine ⟨c, Set.mem_sInter.mpr (fun V hVT ↦ ?_)⟩
        have hindexMem : index ⟨V, hVT⟩ ∈ I :=
          Finset.mem_image.mpr ⟨⟨V, hVT⟩, Finset.mem_attach _ _, rfl⟩
        have hmem := hc _ hindexMem
        change c ∈ signed (index ⟨V, hVT⟩) at hmem
        rw [hindex ⟨V, hVT⟩] at hmem
        exact hmem)
  refine ⟨F, fun A ↦ hF ?_⟩
  exact ⟨A, rfl⟩

/-- Helper for Exercise 4.99.5: the trace ultrafilter's sign pattern recovers its indexing set. -/
private lemma signedTraceUltrafilter_injective :
    ∃ f : Set (Set ℕ) → Ultrafilter FiniteTraceCode, Function.Injective f := by
  classical
  -- Choose one extension per sign pattern and recover each sign from set membership.
  let f : Set (Set ℕ) → Ultrafilter FiniteTraceCode := fun R ↦
    Classical.choose (exists_ultrafilter_signedTraceSets R)
  have hf (R : Set (Set ℕ)) (A : Set ℕ) :
      signedTraceSet R A ∈ f R :=
    Classical.choose_spec (exists_ultrafilter_signedTraceSets R) A
  refine ⟨f, fun R S hRS ↦ ?_⟩
  ext A
  constructor
  · intro hAR
    by_contra hAS
    have hpos : independentTraceSet A ∈ f R := by
      simpa only [signedTraceSet, if_pos hAR] using hf R A
    have hneg : (independentTraceSet A)ᶜ ∈ f S := by
      simpa only [signedTraceSet, if_neg hAS] using hf S A
    rw [← hRS] at hneg
    exact (Ultrafilter.compl_mem_iff_notMem.mp hneg) hpos
  · intro hAS
    by_contra hAR
    have hneg : (independentTraceSet A)ᶜ ∈ f R := by
      simpa only [signedTraceSet, if_neg hAR] using hf R A
    have hpos : independentTraceSet A ∈ f S := by
      simpa only [signedTraceSet, if_pos hAS] using hf S A
    rw [hRS] at hneg
    exact (Ultrafilter.compl_mem_iff_notMem.mp hneg) hpos

/-- Helper for Exercise 4.99.5: mapping ultrafilters along an injection is injective. -/
private lemma Ultrafilter.map_injective_of_injective {X Y : Type*} {e : X → Y}
    (he : Function.Injective e) :
    Function.Injective (Ultrafilter.map e) := by
  -- Test equality on images, whose preimages are unchanged by injectivity.
  intro F G hFG
  apply Ultrafilter.ext
  intro A
  have hpreimage : e ⁻¹' (e '' A) = A := Set.preimage_image_eq A he
  rw [← hpreimage, ← Ultrafilter.mem_map, hFG, Ultrafilter.mem_map]

/-- Helper for Exercise 4.99.5: ultrafilters on `ℕ` have cardinality `2 ^ continuum`. -/
lemma cardinalMk_ultrafilterNat :
    Cardinal.mk (Ultrafilter ℕ) = 2 ^ Cardinal.continuum := by
  classical
  -- The set-of-sets representation is the upper bound; trace ultrafilters give the lower bound.
  apply le_antisymm
  · calc
      Cardinal.mk (Ultrafilter ℕ) ≤ Cardinal.mk (Set (Set ℕ)) := by
        exact Cardinal.mk_le_of_injective (f := fun F : Ultrafilter ℕ ↦ F.sets)
          (fun F G h ↦ Ultrafilter.ext (Set.ext_iff.mp h))
      _ = 2 ^ Cardinal.continuum := by
        rw [Cardinal.mk_set, Cardinal.mk_set_nat]
  · obtain ⟨f, hf⟩ := signedTraceUltrafilter_injective
    obtain ⟨encode, hencode⟩ := exists_injective_nat FiniteTraceCode
    have hmap : Function.Injective (Ultrafilter.map encode) :=
      Ultrafilter.map_injective_of_injective hencode
    calc
      2 ^ Cardinal.continuum = Cardinal.mk (Set (Set ℕ)) := by
        rw [Cardinal.mk_set, Cardinal.mk_set_nat]
      _ ≤ Cardinal.mk (Ultrafilter ℕ) :=
        Cardinal.mk_le_of_injective (hmap.comp hf)
