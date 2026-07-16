import Mathlib.Tactic
import StacksProject_2024.stacks_project.Chap20.«20_23_6_1»
import StacksProject_2024.stacks_project.Chap20.Definition_20_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

attribute [local instance] Classical.decEq Classical.propDecidable

section SemiOrdered

variable [PartialOrder ι]

/- Domain-style sampling for Item 20.23.6.2:
- primary domain: the explicit second homotopy on semi-ordered Čech cochains indexed by weakly
  increasing tuples, together with the canonical bridge between the semi-ordered and ordered Čech
  complexes;
- sampled owner API:
  `SemiOrderedCechTuple`,
  `semiOrderedCechTerm`,
  `semiOrderedCechComplex`,
  `semiOrderedCechProjection`,
  `orderedToSemiOrderedCech`,
  `cechDuplicateTransport`,
  `Monotone.strictMono_iff_injective`,
  `Fin.orderHom_injective_iff`;
- best owner abstraction: the source-facing owner layer here is the semi-ordered Čech complex
  itself; the public API is the degreewise second-homotopy formula together with the canonical
  projection/inclusion bridge to `orderedCechComplex 𝒰 F`, while the repeated-entry transport
  reuses `cechDuplicateTransport` from `20_23_6_1`.

Source/core/bridge triage:
- `source-facing`: `SemiOrderedCechTuple`, `semiOrderedCechTerm`,
  `semiOrderedCechComplex`, `semiOrderedCechSecondHomotopyToFun`;
- `core/canonical`: `cechDuplicateTransport` from `20_23_6_1`, together with
  `Monotone.strictMono_iff_injective` and `Fin.orderHom_injective_iff` from mathlib;
- `bridge/view`: `semiOrderedCechProjection`, `orderedToSemiOrderedCech`, and the tuple omission
  map `σ.comp (Fin.predAboveOrderHom a.succ)` at the first repeated adjacent index.

Primitive data versus derived API:
- primitive data: semi-ordered tuples, their Čech terms and differential, and the explicit second
  homotopy formula on weakly increasing tuples;
- derived API: the canonical least adjacent repeated index in a non-strict tuple, together with
  the semi-ordered/ordered bridge morphisms and the strict-mono and adjacent-repeat evaluation
  lemmas. -/

/-- A degree-`p` semi-ordered Čech tuple, i.e. a weakly increasing tuple of indices. -/
abbrev SemiOrderedCechTuple (p : ℕ) :=
  Fin (p + 1) →o ι

/-- The degree-`p` term of the semi-ordered Čech complex. -/
abbrev semiOrderedCechTerm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of
    ((σ : SemiOrderedCechTuple p) → F.obj (op (cechIntersection 𝒰 σ)))

/-- Delete the `j`th entry of a semi-ordered tuple. -/
private abbrev semiOrderedDeleteTuple {p : ℕ} (σ : Fin (p + 2) →o ι)
    (j : Fin (p + 2)) : Fin (p + 1) →o ι :=
  { toFun := σ ∘ j.succAboveEmb
    monotone' := fun a b hab ↦
      σ.monotone <| by
        rcases lt_or_eq_of_le hab with hab' | rfl
        · exact le_of_lt (Fin.strictMono_succAbove j hab')
        · rfl }

@[simp] private theorem semiOrderedDeleteTuple_coe {p : ℕ} (σ : Fin (p + 2) →o ι)
    (j : Fin (p + 2)) :
    ⇑(semiOrderedDeleteTuple σ j) = σ ∘ j.succAboveEmb :=
  rfl

/-- The underlying function of the degree-`p` semi-ordered Čech differential. -/
private def semiOrderedCechDifferentialToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    semiOrderedCechTerm 𝒰 F p → semiOrderedCechTerm 𝒰 F (p + 1) :=
  fun s σ ↦
    ∑ j : Fin (p + 2),
      (-1 : ℤ) ^ (j : ℕ) •
        cechRestriction 𝒰 F σ j (s (semiOrderedDeleteTuple σ j))

/-- The semi-ordered Čech differential is additive on cochains. -/
private theorem semiOrderedCechDifferentialToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : semiOrderedCechTerm 𝒰 F p) :
    semiOrderedCechDifferentialToFun 𝒰 F p (s + t) =
      semiOrderedCechDifferentialToFun 𝒰 F p s +
        semiOrderedCechDifferentialToFun 𝒰 F p t := by
  sorry

/-- The degree-`p` differential in the semi-ordered Čech complex. -/
private abbrev semiOrderedCechDifferential (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    semiOrderedCechTerm 𝒰 F p ⟶ semiOrderedCechTerm 𝒰 F (p + 1) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (semiOrderedCechDifferentialToFun 𝒰 F p)
      (semiOrderedCechDifferentialToFun_map_add 𝒰 F p))

/-- Two successive semi-ordered Čech differentials compose to zero. -/
private def semiOrderedToCechCochain (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    semiOrderedCechTerm 𝒰 F p → cechTerm 𝒰 F p :=
  fun s τ ↦
    if hτ : Monotone τ then
      s ⟨τ, hτ⟩
    else
      0

/-- On a weakly increasing tuple, the ordinary Čech differential of the zero extension agrees with
the semi-ordered Čech differential. -/
private theorem cechDifferentialToFun_apply_semiOrderedToCechCochain (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : semiOrderedCechTerm 𝒰 F p) (σ : SemiOrderedCechTuple (p + 1)) :
    cechDifferentialToFun 𝒰 F p (semiOrderedToCechCochain 𝒰 F p s) σ =
      semiOrderedCechDifferentialToFun 𝒰 F p s σ := by
  sorry

/-- Two successive semi-ordered Čech differentials compose to zero. -/
private theorem semiOrderedCechDifferential_comp (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    semiOrderedCechDifferential 𝒰 F p ≫ semiOrderedCechDifferential 𝒰 F (p + 1) = 0 := by
  sorry

/-- The semi-ordered Čech complex indexed by weakly increasing tuples. -/
def semiOrderedCechComplex (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.of
    (semiOrderedCechTerm 𝒰 F)
    (semiOrderedCechDifferential 𝒰 F)
    (semiOrderedCechDifferential_comp 𝒰 F)

-- Proof sketch: for an order hom on `Fin (p + 1)`, failure of strict monotonicity is equivalent to
-- failure of injectivity, and mathlib's `Fin.orderHom_injective_iff` identifies that with an
-- adjacent equality.
/-- A weakly increasing finite tuple that is not strictly increasing has an adjacent repeated
value. -/
theorem exists_adjacent_eq_of_not_strictMono {p : ℕ} (σ : Fin (p + 1) →o ι)
    (hσ : ¬ StrictMono σ) :
    ∃ a : Fin p, σ a.castSucc = σ a.succ := by
  have hσ' : ¬ Function.Injective σ := by
    rwa [σ.monotone.strictMono_iff_injective] at hσ
  rw [Fin.orderHom_injective_iff] at hσ'
  push Not at hσ'
  exact hσ'

/-- The least adjacent repeated index in a weakly increasing tuple that is not strictly
increasing. -/
def firstRepeatedIndex {p : ℕ} (σ : Fin (p + 1) →o ι)
    (hσ : ¬ StrictMono σ) : Fin p :=
  (Finset.univ.filter fun a : Fin p ↦ σ a.castSucc = σ a.succ).min' <| by
    rcases exists_adjacent_eq_of_not_strictMono σ hσ with ⟨a, ha⟩
    exact ⟨a, by simp [ha]⟩

/-- The adjacent entries at the first repeated index coincide. -/
theorem firstRepeatedIndex_spec {p : ℕ} (σ : Fin (p + 1) →o ι)
    (hσ : ¬ StrictMono σ) :
    σ (firstRepeatedIndex σ hσ).castSucc = σ (firstRepeatedIndex σ hσ).succ := by
  have hnonempty :
      (Finset.univ.filter fun a : Fin p ↦ σ a.castSucc = σ a.succ).Nonempty := by
    rcases exists_adjacent_eq_of_not_strictMono σ hσ with ⟨a, ha⟩
    exact ⟨a, by simp [ha]⟩
  have hmem :
      firstRepeatedIndex σ hσ ∈
        Finset.univ.filter fun a : Fin p ↦ σ a.castSucc = σ a.succ := by
    simpa [firstRepeatedIndex] using
      (Finset.min'_mem
        (Finset.univ.filter fun a : Fin p ↦ σ a.castSucc = σ a.succ) hnonempty)
  exact (Finset.mem_filter.mp hmem).2

/-- No earlier adjacent entries coincide before the first repeated index. -/
theorem firstRepeatedIndex_min {p : ℕ} (σ : Fin (p + 1) →o ι)
    (hσ : ¬ StrictMono σ) :
    ∀ ⦃b : Fin p⦄, b < firstRepeatedIndex σ hσ → σ b.castSucc ≠ σ b.succ := by
  intro b hb hEq
  have hle : firstRepeatedIndex σ hσ ≤ b := by
    simpa [firstRepeatedIndex] using
      (Finset.min'_le
        (Finset.univ.filter fun a : Fin p ↦ σ a.castSucc = σ a.succ)
        b (by simp [hEq]))
  exact (not_le_of_gt hb) hle

/-- A repeated adjacent index is the first repeated index precisely when no earlier adjacent
entries agree. -/
theorem firstRepeatedIndex_eq {p : ℕ} (σ : Fin (p + 1) →o ι)
    (hσ : ¬ StrictMono σ) (a : Fin p) (ha : σ a.castSucc = σ a.succ)
    (hfirst : ∀ ⦃b : Fin p⦄, b < a → σ b.castSucc ≠ σ b.succ) :
    firstRepeatedIndex σ hσ = a := by
  apply le_antisymm
  · simpa [firstRepeatedIndex] using
      (Finset.min'_le
        (Finset.univ.filter fun b : Fin p ↦ σ b.castSucc = σ b.succ)
        a (by simp [ha]))
  · exact le_of_not_gt fun hlt ↦ (hfirst hlt) (firstRepeatedIndex_spec σ hσ)

/-- 20.23.6.2: the degree-`p` component of the second homotopy on the semi-ordered Čech complex
vanishes on strictly increasing tuples and otherwise inserts one extra copy of the first repeated
adjacent index with sign `(-1)^a`. -/
@[stacks 01FO]
def semiOrderedCechSecondHomotopyToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    semiOrderedCechTerm 𝒰 F (p + 1) → semiOrderedCechTerm 𝒰 F p :=
  fun s σ ↦
    if hσ : StrictMono σ then
      0
    else
      let a := firstRepeatedIndex σ hσ
      (-1 : ℤ) ^ (a : ℕ) •
        cechDuplicateTransport 𝒰 F σ a.succ
          (s (σ.comp (Fin.predAboveOrderHom a.succ)))

/-- On a non-strict weakly increasing tuple, the second semi-ordered Čech homotopy is given by the
first repeated adjacent index. -/
theorem semiOrderedCechSecondHomotopyToFun_apply_of_not_strictMono (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : semiOrderedCechTerm 𝒰 F (p + 1))
    (σ : SemiOrderedCechTuple p) (hσ : ¬ StrictMono σ) :
    semiOrderedCechSecondHomotopyToFun 𝒰 F p s σ =
      (-1 : ℤ) ^ (firstRepeatedIndex σ hσ : ℕ) •
        cechDuplicateTransport 𝒰 F σ (firstRepeatedIndex σ hσ).succ
          (s (σ.comp (Fin.predAboveOrderHom (firstRepeatedIndex σ hσ).succ))) := by
  simp [semiOrderedCechSecondHomotopyToFun, hσ]

-- Proof sketch: unfold `semiOrderedCechSecondHomotopyToFun`; the strict-increasing branch is the
-- first clause of the defining case split.
/-- The second semi-ordered Čech homotopy vanishes on strictly increasing tuples. -/
@[simp] theorem semiOrderedCechSecondHomotopyToFun_apply_of_strictMono (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : semiOrderedCechTerm 𝒰 F (p + 1))
    (σ : SemiOrderedCechTuple p) (hσ : StrictMono σ) :
    semiOrderedCechSecondHomotopyToFun 𝒰 F p s σ = 0 := by
  simp [semiOrderedCechSecondHomotopyToFun, hσ]

/-- If a weakly increasing tuple is strictly increasing before an adjacent repeat at `a`, then the
second semi-ordered Čech homotopy inserts one extra copy of that repeated index with sign
`(-1)^a`. -/
theorem semiOrderedCechSecondHomotopyToFun_apply_of_adjacent_eq (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : semiOrderedCechTerm 𝒰 F (p + 1))
    (σ : SemiOrderedCechTuple p) (a : Fin p)
    (ha : σ a.castSucc = σ a.succ)
    (hfirst : ∀ ⦃b : Fin p⦄, b < a → σ b.castSucc ≠ σ b.succ) :
    semiOrderedCechSecondHomotopyToFun 𝒰 F p s σ =
      (-1 : ℤ) ^ (a : ℕ) •
        cechDuplicateTransport 𝒰 F σ a.succ
          (s (σ.comp (Fin.predAboveOrderHom a.succ))) := by
  have hσ : ¬ StrictMono σ := by
    intro hstrict
    have hlt : σ a.castSucc < σ a.succ := hstrict Fin.castSucc_lt_succ
    rw [ha] at hlt
    exact lt_irrefl _ hlt
  rw [semiOrderedCechSecondHomotopyToFun_apply_of_not_strictMono 𝒰 F p s σ hσ]
  have hindex : firstRepeatedIndex σ hσ = a := firstRepeatedIndex_eq σ hσ a ha hfirst
  rw [hindex]

/-- The second semi-ordered Čech homotopy is additive on cochains. -/
private theorem semiOrderedCechSecondHomotopyToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : (semiOrderedCechComplex 𝒰 F).X (p + 1)) :
    semiOrderedCechSecondHomotopyToFun 𝒰 F p (s + t) =
      semiOrderedCechSecondHomotopyToFun 𝒰 F p s +
        semiOrderedCechSecondHomotopyToFun 𝒰 F p t := by
  sorry

/-- The degree-`p` component of the second semi-ordered Čech homotopy as a morphism of
semi-ordered Čech terms. -/
def semiOrderedCechSecondHomotopyComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (semiOrderedCechComplex 𝒰 F).X (p + 1) ⟶ (semiOrderedCechComplex 𝒰 F).X p :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (semiOrderedCechSecondHomotopyToFun 𝒰 F p)
      (semiOrderedCechSecondHomotopyToFun_map_add 𝒰 F p))

@[simp] theorem semiOrderedCechSecondHomotopyComponent_f_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (semiOrderedCechComplex 𝒰 F).X (p + 1)) (σ : SemiOrderedCechTuple p) :
    semiOrderedCechSecondHomotopyComponent 𝒰 F p s σ =
      semiOrderedCechSecondHomotopyToFun 𝒰 F p s σ := rfl

end SemiOrdered

section OrderedBridge

variable [LinearOrder ι]

/-- Deleting either entry of an adjacent equal pair gives the same semi-ordered tuple. -/
private theorem semiOrderedDeleteTuple_castSucc_eq_succ {p : ℕ} (σ : Fin (p + 2) →o ι)
    (a : Fin (p + 1)) (ha : σ a.castSucc = σ a.succ) :
    semiOrderedDeleteTuple σ a.castSucc = semiOrderedDeleteTuple σ a.succ := by
  ext k
  by_cases hk : k < a
  · have hk1 : k.castSucc < a.castSucc := by
      simpa [Fin.castSucc_lt_castSucc_iff] using hk
    have hk2 : k.castSucc < a.succ := Fin.castSucc_lt_succ_iff.mpr (le_of_lt hk)
    simp [Fin.succAbove, hk1, hk2]
  · rcases lt_or_eq_of_le (le_of_not_gt hk) with hka | rfl
    · have hk1 : ¬ k.castSucc < a.castSucc := by
        simpa [Fin.castSucc_lt_castSucc_iff] using not_lt_of_ge (le_of_lt hka)
      have hk2 : ¬ k.castSucc < a.succ := by
        intro hlt
        exact (not_le_of_gt hka) (Fin.castSucc_lt_succ_iff.mp hlt)
      simp [Fin.succAbove, hk1, hk2]
    · have hk2 : a.castSucc < a.succ := Fin.castSucc_lt_succ_iff.mpr le_rfl
      simp [Fin.succAbove, hk2, ha]

/-- The degree-`p` projection from semi-ordered to ordered Čech cochains. -/
private abbrev semiOrderedCechProjectionComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (semiOrderedCechComplex 𝒰 F).X p ⟶ (orderedCechComplex 𝒰 F).X p :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (fun s σ ↦ s σ.toOrderHom)
      (by
        intro s t
        rfl))

/-- The semi-ordered-to-ordered projection commutes with the Čech differential. -/
private theorem semiOrderedCechProjectionComponent_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    semiOrderedCechProjectionComponent 𝒰 F p ≫ (orderedCechComplex 𝒰 F).d p (p + 1) =
      semiOrderedCechDifferential 𝒰 F p ≫
        semiOrderedCechProjectionComponent 𝒰 F (p + 1) := by
  sorry

/-- Restrict a semi-ordered Čech cochain to the strictly increasing tuples. -/
def semiOrderedCechProjection (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    semiOrderedCechComplex 𝒰 F ⟶ orderedCechComplex 𝒰 F :=
  HomologicalComplex.Hom.mk
    (semiOrderedCechProjectionComponent 𝒰 F)
    (fun i j hij ↦ by
      rcases hij with rfl
      simpa [semiOrderedCechComplex] using semiOrderedCechProjectionComponent_comm 𝒰 F i)

@[simp] theorem semiOrderedCechProjection_f_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (semiOrderedCechComplex 𝒰 F).X p) (σ : StrictCechTuple p) :
    (semiOrderedCechProjection 𝒰 F).f p s σ = s σ.toOrderHom := by
  rfl

/-- The degree-`p` inclusion of ordered Čech cochains into semi-ordered Čech cochains. -/
private def orderedToSemiOrderedCechToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplex 𝒰 F).X p → (semiOrderedCechComplex 𝒰 F).X p :=
  fun s σ ↦
    if hσ : StrictMono σ then
      s (OrderEmbedding.ofStrictMono σ hσ)
    else
      0

/-- The ordered-to-semi-ordered extension is additive on cochains. -/
private theorem orderedToSemiOrderedCechToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : (orderedCechComplex 𝒰 F).X p) :
    orderedToSemiOrderedCechToFun 𝒰 F p (s + t) =
      orderedToSemiOrderedCechToFun 𝒰 F p s +
        orderedToSemiOrderedCechToFun 𝒰 F p t := by
  sorry

/-- The degree-`p` ordered-to-semi-ordered comparison component. -/
private abbrev orderedToSemiOrderedCechComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplex 𝒰 F).X p ⟶ (semiOrderedCechComplex 𝒰 F).X p :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (orderedToSemiOrderedCechToFun 𝒰 F p)
      (orderedToSemiOrderedCechToFun_map_add 𝒰 F p))

/-- The ordered-to-semi-ordered comparison commutes with the Čech differential. -/
private theorem semiOrderedDeleteTuple_not_strictMono_of_lt {p : ℕ} (σ : Fin (p + 2) →o ι)
    (a : Fin (p + 1)) (ha : σ a.castSucc = σ a.succ) {j : Fin (p + 2)}
    (hj : j < a.castSucc) :
    ¬ StrictMono (semiOrderedDeleteTuple σ j) := by
  have ha0 : a ≠ 0 := by
    intro h
    subst h
    simpa using hj
  let b : Fin p := a.pred ha0
  have hb :
      (semiOrderedDeleteTuple σ j) b.castSucc = (semiOrderedDeleteTuple σ j) b.succ := by
    have hlt1 : ¬ (a.pred ha0).castSucc.castSucc < j := by
      rw [Fin.lt_def] at hj ⊢
      simp [Fin.val_pred] at *
      omega
    have hlt2 : ¬ a.castSucc < j := not_lt_of_ge (le_of_lt hj)
    have hsucc : (a.pred ha0).succ = a := Fin.succ_pred a ha0
    simp [b, Fin.succAbove, hlt1, hlt2,
      Fin.succ_castSucc, hsucc, ha]
  intro hstrict
  have hlt : (semiOrderedDeleteTuple σ j) b.castSucc < (semiOrderedDeleteTuple σ j) b.succ :=
    hstrict Fin.castSucc_lt_succ
  rw [hb] at hlt
  exact lt_irrefl _ hlt

private theorem semiOrderedDeleteTuple_not_strictMono_of_gt {p : ℕ} (σ : Fin (p + 2) →o ι)
    (a : Fin (p + 1)) (ha : σ a.castSucc = σ a.succ) {j : Fin (p + 2)}
    (hj : a.succ < j) :
    ¬ StrictMono (semiOrderedDeleteTuple σ j) := by
  sorry

private theorem orderedToSemiOrderedCechToFun_apply_delete_eq_zero (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p) (σ : SemiOrderedCechTuple (p + 1))
    (hσ : ¬ StrictMono σ) {j : Fin (p + 2)}
    (hj₁ : j ≠ (firstRepeatedIndex σ hσ).castSucc)
    (hj₂ : j ≠ (firstRepeatedIndex σ hσ).succ) :
    orderedToSemiOrderedCechToFun 𝒰 F p s (semiOrderedDeleteTuple σ j) = 0 := by
  sorry

private theorem orderedToSemiOrderedCech_pair_eq (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p) (σ : SemiOrderedCechTuple (p + 1))
    (a : Fin (p + 1)) (ha : σ a.castSucc = σ a.succ) :
    cechRestriction 𝒰 F σ a.castSucc
        (orderedToSemiOrderedCechToFun 𝒰 F p s (semiOrderedDeleteTuple σ a.castSucc)) =
      cechRestriction 𝒰 F σ a.succ
        (orderedToSemiOrderedCechToFun 𝒰 F p s (semiOrderedDeleteTuple σ a.succ)) := by
  sorry

private theorem semiOrderedCechDifferential_apply_orderedToSemiOrdered_of_strictMono
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p) (σ : SemiOrderedCechTuple (p + 1))
    (hσ : StrictMono σ) :
    semiOrderedCechDifferentialToFun 𝒰 F p (orderedToSemiOrderedCechToFun 𝒰 F p s) σ =
      (orderedCechComplex 𝒰 F).d p (p + 1) s (OrderEmbedding.ofStrictMono σ hσ) := by
  sorry

private theorem semiOrderedCechDifferential_apply_orderedToSemiOrdered_of_not_strictMono
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p) (σ : SemiOrderedCechTuple (p + 1))
    (hσ : ¬ StrictMono σ) :
    semiOrderedCechDifferentialToFun 𝒰 F p (orderedToSemiOrderedCechToFun 𝒰 F p s) σ = 0 := by
  sorry

private theorem orderedToSemiOrderedCechComponent_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedToSemiOrderedCechComponent 𝒰 F p ≫ semiOrderedCechDifferential 𝒰 F p =
      (orderedCechComplex 𝒰 F).d p (p + 1) ≫
        orderedToSemiOrderedCechComponent 𝒰 F (p + 1) := by
  sorry

/-- Extend an ordered Čech cochain by zero on the non-strict semi-ordered tuples. -/
def orderedToSemiOrderedCech (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    orderedCechComplex 𝒰 F ⟶ semiOrderedCechComplex 𝒰 F :=
  HomologicalComplex.Hom.mk
    (orderedToSemiOrderedCechComponent 𝒰 F)
    (fun i j hij ↦ by
      rcases hij with rfl
      simpa [semiOrderedCechComplex] using orderedToSemiOrderedCechComponent_comm 𝒰 F i)

@[simp] theorem orderedToSemiOrderedCech_f_apply_of_strictMono (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p)
    (σ : SemiOrderedCechTuple p) (hσ : StrictMono σ) :
    (orderedToSemiOrderedCech 𝒰 F).f p s σ = s (OrderEmbedding.ofStrictMono σ hσ) := by
  sorry

@[simp] theorem orderedToSemiOrderedCech_f_apply_of_not_strictMono (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p)
    (σ : SemiOrderedCechTuple p) (hσ : ¬ StrictMono σ) :
    (orderedToSemiOrderedCech 𝒰 F).f p s σ = 0 := by
  sorry

end OrderedBridge
