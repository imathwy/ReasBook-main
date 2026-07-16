import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.CategoryTheory.Subobject.HasCardinalLT
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.SetTheory.Cardinal.Ordinal
import StacksProject_2024.stacks_project.Chap19.Definition_19_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]
variable {U X : C}

/- Domain-style sampling for Lemma 19.11.1:
- primary domain: the ordered type `Subobject X` in an abelian category, with size controlled by a
  separator `U` through the hom-set `U ⟶ X`;
- core/canonical owners: `Subobject X`, `IsSeparator U`, the bridge `Subobject.factorSet U`,
  and the canonical size owner `HasCardinalLT (Subobject X) κ`;
- primitive data: the objects `U` and `X`, the generator hypothesis `IsSeparator U`, and the
  canonical cardinal comparison involving `Cardinal.mk (U ⟶ X)`;
- derived API: the source-facing prohibitions on strict chains, the stabilization of monotone or
  antitone ordinal-indexed chains, and the cardinal bound on `Subobject X`;
- companion owner declarations in the same domain: `IsNoetherianObject X`,
  `IsArtinianObject X`, and `wellPowered_of_isSeparator`, which package weaker chain or smallness
  consequences without the explicit Stacks-project cardinal estimate.

Source/core/bridge triage:
- `source-facing`: the five lemmas below are the Stacks-project cardinal consequences for
  subobject chains;
- `core/canonical`: the underlying owner abstractions are `Subobject X`, `IsSeparator U`,
  `Subobject.factorSet U`, and the companion size owner `HasCardinalLT (Subobject X) κ`;
- `bridge/view`: `Subobject.factorSet U` embeds `Subobject X` into `Set (U ⟶ X)`; part (5) is the
  resulting source-facing cardinal bound, and parts (1)–(4) are the corresponding chain
  consequences for strict subset chains and their complements.
-/

namespace Subobject

/-- The subset of `U ⟶ X` consisting of morphisms that factor through a fixed subobject of `X`. -/
def factorSet (A : Subobject X) (U : C) : Set (U ⟶ X) :=
  { f | A.Factors f }

@[simp]
theorem mem_factorSet (U : C) (A : Subobject X) (f : U ⟶ X) :
    f ∈ factorSet A U ↔ A.Factors f :=
  Iff.rfl

theorem monotone_factorSet (U : C) : Monotone fun A : Subobject X ↦ factorSet A U := by
  -- Factorization through a smaller subobject automatically factors through any larger one.
  intro A B hAB f hf
  exact Subobject.factors_of_le f hAB hf

end Subobject

variable [Abelian C]

namespace Subobject

theorem factorSet_injective (hU : IsSeparator U) :
    Function.Injective fun A : Subobject X ↦ factorSet A U := by
  -- We prove each inequality separately by separating a proper pullback subobject.
  have hle :
      ∀ {A B : Subobject X}, factorSet A U = factorSet B U → A ≤ B := by
    intro A B hEq
    by_contra hAB
    let P : Subobject (A : C) := (Subobject.pullback A.arrow).obj B
    have hP_ne_top : P ≠ ⊤ := by
      intro hP_top
      have hP_id : P.Factors (𝟙 (A : C)) := by
        simpa [P, hP_top] using (Subobject.top_factors (𝟙 (A : C)))
      have hB_arrow : B.Factors A.arrow := by
        simpa using
          (CategoryTheory.Limits.pullback_factors_iff (f := A.arrow) (y := B) (h := 𝟙 (A : C))).1
            hP_id
      exact hAB (Subobject.le_of_factors hB_arrow)
    obtain ⟨g, hg⟩ :=
      (isSeparator_iff_exists_not_factors_subobject C U).mp hU P hP_ne_top
    let f : U ⟶ X := g ≫ A.arrow
    have hfA : f ∈ factorSet A U := by
      exact (mem_factorSet U A f).2 (Subobject.factors_comp_arrow g)
    have hfB : f ∉ factorSet B U := by
      intro hfB
      have hPg : P.Factors g := by
        exact
          (CategoryTheory.Limits.pullback_factors_iff (f := A.arrow) (y := B) (h := g)).2
            ((mem_factorSet U B f).1 hfB)
      exact hg hPg
    have : f ∈ factorSet B U := by
      simpa [hEq] using hfA
    exact hfB this
  exact fun A B hEq ↦ le_antisymm (hle hEq) (hle hEq.symm)

/-- Helper for Lemma 19.11.1: an ordinal-indexed strictly increasing chain of subsets containing a
common element injects into the ambient type. -/
lemma no_strictly_increasing_subset_chain_of_lt_card_ord
    {T : Type v} {o : Ordinal.{v}} {z : T} (hκ : Cardinal.mk T < o.card) :
    ¬ ∃ S : o.ToType → Set T, StrictMono S ∧ ∀ i, z ∈ S i := by
  rintro ⟨S, hS, hz⟩
  classical
  let witness : o.ToType → T := fun i =>
    if hi : IsMax i then z
    else Classical.choose <| Set.not_subset.mp (hS (Order.lt_succ_of_not_isMax hi)).not_ge
  have witness_mem_next :
      ∀ i : o.ToType, ∀ hi : ¬ IsMax i, witness i ∈ S (Order.succ i) := by
    intro i hi
    simp only [witness, dif_neg hi]
    exact (Classical.choose_spec
      (Set.not_subset.mp (hS (Order.lt_succ_of_not_isMax hi)).not_ge)).1
  have witness_not_mem :
      ∀ i : o.ToType, ∀ hi : ¬ IsMax i, witness i ∉ S i := by
    intro i hi
    simp only [witness, dif_neg hi]
    exact (Classical.choose_spec
      (Set.not_subset.mp (hS (Order.lt_succ_of_not_isMax hi)).not_ge)).2
  have witness_ne_of_lt :
      ∀ {i j : o.ToType}, i < j → witness i ≠ witness j := by
    intro i j hij
    have hi : ¬ IsMax i := not_isMax_of_lt hij
    by_cases hj : IsMax j
    · intro hEq
      have hzj : witness j = z := by simp [witness, hj]
      have hzi : z ∈ S i := hz i
      have hwi : witness i ∉ S i := witness_not_mem i hi
      exact hwi (by simpa [hEq, hzj] using hzi)
    · intro hEq
      have hwi_mem : witness i ∈ S j := by
        exact (StrictMono.monotone hS (Order.succ_le_of_lt hij)) (witness_mem_next i hi)
      exact (witness_not_mem j hj) (by simpa [hEq] using hwi_mem)
  have hw_injective : Function.Injective witness := by
    intro i j hEq
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · exact (witness_ne_of_lt hij') hEq
    · exact (witness_ne_of_lt hij') hEq.symm
  have hcard : o.card ≤ Cardinal.mk T := by
    calc
      o.card = Cardinal.mk o.ToType := by
        symm
        simpa [Ordinal.type_toType] using (Ordinal.card_type (α := o.ToType) (r := (· < ·)))
      _ ≤ Cardinal.mk T := Cardinal.mk_le_of_injective hw_injective
  exact (not_le_of_gt hκ) hcard

/-- Helper for Lemma 19.11.1: an ordinal-indexed strictly decreasing chain of subsets containing a
common element injects into the ambient type. -/
lemma no_strictly_decreasing_subset_chain_of_lt_card_ord
    {T : Type v} {o : Ordinal.{v}} {z : T} (hκ : Cardinal.mk T < o.card) :
    ¬ ∃ S : o.ToType → Set T, StrictAnti S ∧ ∀ i, z ∈ S i := by
  rintro ⟨S, hS, hz⟩
  classical
  let witness : o.ToType → T := fun i =>
    if hi : IsMax i then z
    else Classical.choose <| Set.not_subset.mp (hS (Order.lt_succ_of_not_isMax hi)).not_ge
  have witness_mem_self :
      ∀ i : o.ToType, ∀ hi : ¬ IsMax i, witness i ∈ S i := by
    intro i hi
    simp only [witness, dif_neg hi]
    exact (Classical.choose_spec
      (Set.not_subset.mp (hS (Order.lt_succ_of_not_isMax hi)).not_ge)).1
  have witness_not_mem_next :
      ∀ i : o.ToType, ∀ hi : ¬ IsMax i, witness i ∉ S (Order.succ i) := by
    intro i hi
    simp only [witness, dif_neg hi]
    exact (Classical.choose_spec
      (Set.not_subset.mp (hS (Order.lt_succ_of_not_isMax hi)).not_ge)).2
  have witness_ne_of_lt :
      ∀ {i j : o.ToType}, i < j → witness i ≠ witness j := by
    intro i j hij
    have hi : ¬ IsMax i := not_isMax_of_lt hij
    by_cases hj : IsMax j
    · intro hEq
      have hzj : witness j = z := by simp [witness, hj]
      have hzi : z ∈ S (Order.succ i) := hz (Order.succ i)
      have hwi : witness i ∉ S (Order.succ i) := witness_not_mem_next i hi
      exact hwi (by simpa [hEq, hzj] using hzi)
    · intro hEq
      have hwj_mem : witness j ∈ S (Order.succ i) := by
        exact (StrictAnti.antitone hS (Order.succ_le_of_lt hij)) (witness_mem_self j hj)
      exact (witness_not_mem_next i hi) (by simpa [hEq] using hwj_mem)
  have hw_injective : Function.Injective witness := by
    intro i j hEq
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · exact (witness_ne_of_lt hij') hEq
    · exact (witness_ne_of_lt hij') hEq.symm
  have hcard : o.card ≤ Cardinal.mk T := by
    calc
      o.card = Cardinal.mk o.ToType := by
        symm
        simpa [Ordinal.type_toType] using (Ordinal.card_type (α := o.ToType) (r := (· < ·)))
      _ ≤ Cardinal.mk T := Cardinal.mk_le_of_injective hw_injective
  exact (not_le_of_gt hκ) hcard

/-- Helper for Lemma 19.11.1: transport the ordinal subset-chain contradiction to an arbitrary
well-ordered index type. -/
lemma no_strictly_increasing_subset_chain_of_lt_card
    {ι : Type v} [LinearOrder ι] [WellFoundedLT ι] {T : Type v} {z : T}
    (hκ : Cardinal.mk T < Cardinal.mk ι) :
    ¬ ∃ S : ι → Set T, StrictMono S ∧ ∀ i, z ∈ S i := by
  rintro ⟨S, hS, hz⟩
  let o : Ordinal := Ordinal.type (α := ι) LT.lt
  let e : o.ToType → ι := fun i =>
    Ordinal.enum (α := ι) (r := (· < · : ι → ι → Prop)) (Ordinal.ToType.mk.symm i)
  have he : StrictMono e := by
    intro i j hij
    exact
      (Ordinal.enum_lt_enum (r := (· < · : ι → ι → Prop))).2
        (show Ordinal.ToType.mk.symm i < Ordinal.ToType.mk.symm j from
          (Ordinal.ToType.mk (o := o)).symm.strictMono hij)
  let S' : o.ToType → Set T := fun i => S (e i)
  have hS' : StrictMono S' := hS.comp he
  have hz' : ∀ i, z ∈ S' i := fun i ↦ hz (e i)
  have hκ' : Cardinal.mk T < o.card := by
    simpa [o, Ordinal.card_type] using hκ
  exact Subobject.no_strictly_increasing_subset_chain_of_lt_card_ord hκ' ⟨S', hS', hz'⟩

/-- Helper for Lemma 19.11.1: transport the decreasing ordinal subset-chain contradiction to an
arbitrary well-ordered index type. -/
lemma no_strictly_decreasing_subset_chain_of_lt_card
    {ι : Type v} [LinearOrder ι] [WellFoundedLT ι] {T : Type v} {z : T}
    (hκ : Cardinal.mk T < Cardinal.mk ι) :
    ¬ ∃ S : ι → Set T, StrictAnti S ∧ ∀ i, z ∈ S i := by
  rintro ⟨S, hS, hz⟩
  let o : Ordinal := Ordinal.type (α := ι) LT.lt
  let e : o.ToType → ι := fun i =>
    Ordinal.enum (α := ι) (r := (· < · : ι → ι → Prop)) (Ordinal.ToType.mk.symm i)
  have he : StrictMono e := by
    intro i j hij
    exact
      (Ordinal.enum_lt_enum (r := (· < · : ι → ι → Prop))).2
        (show Ordinal.ToType.mk.symm i < Ordinal.ToType.mk.symm j from
          (Ordinal.ToType.mk (o := o)).symm.strictMono hij)
  let S' : o.ToType → Set T := fun i => S (e i)
  have hS' : StrictAnti S' := by
    intro i j hij
    exact hS (he hij)
  have hz' : ∀ i, z ∈ S' i := fun i ↦ hz (e i)
  have hκ' : Cardinal.mk T < o.card := by
    simpa [o, Ordinal.card_type] using hκ
  exact Subobject.no_strictly_decreasing_subset_chain_of_lt_card_ord hκ' ⟨S', hS', hz'⟩

end Subobject

/-- Lemma 19.11.1 (1): if `U` is a generator of the abelian category and
`#(U ⟶ X) < κ'`, then there is no strictly increasing chain of subobjects of `X`
indexed by `κ'`. -/
-- Proof sketch: send a subobject `A ≤ X` to `Subobject.factorSet A U ⊆ Hom(U, X)`. The
-- separator hypothesis implies that the map `A ↦ Subobject.factorSet A U` is injective, hence a
-- strict increasing chain of subobjects yields a strict increasing chain of subsets of
-- `Hom(U, X)`. Picking one fresh element at each strict subset step then contradicts
-- `#(U ⟶ X) < κ'`.
lemma no_strictly_increasing_subobject_chain_of_gt_hom_card
    (hU : IsSeparator U) (κ' : Cardinal.{v}) (hκ' : Cardinal.mk (U ⟶ X) < κ') :
    ¬ ∃ A : κ'.ord.ToType → Subobject X, StrictMono A := by
  rintro ⟨A, hA⟩
  let S : κ'.ord.ToType → Set (U ⟶ X) := fun i => Subobject.factorSet (A i) U
  have hS : StrictMono S := by
    -- The factor-set map is monotone, and separator-injectivity upgrades monotonicity to strictness.
    intro i j hij
    have hle : S i ≤ S j :=
      (Subobject.monotone_factorSet U) (hA.monotone hij.le)
    have hne : S i ≠ S j := by
      intro hEq
      exact hij.ne (hA.injective ((Subobject.factorSet_injective (U := U) (X := X) hU) hEq))
    exact lt_of_le_of_ne hle hne
  have hz : ∀ i, (0 : U ⟶ X) ∈ S i := by
    -- Every factor set contains the zero morphism.
    intro i
    exact (Subobject.mem_factorSet U (A i) 0).2 Subobject.factors_zero
  have hκ : Cardinal.mk (U ⟶ X) < (κ'.ord).card := by
    simpa using hκ'
  exact Subobject.no_strictly_increasing_subset_chain_of_lt_card_ord hκ ⟨S, hS, hz⟩

/-- Lemma 19.11.1 (2): if `U` is a generator of the abelian category and
`#(U ⟶ X) < κ'`, then there is no strictly decreasing chain of subobjects of `X`
indexed by `κ'`. -/
-- Proof sketch: a strict decreasing subobject chain gives a strict decreasing chain of factor
-- sets in `Set (U ⟶ X)`. Passing to complements turns this into a strict increasing chain of
-- subsets of `Hom(U, X)`, so the same fresh-element argument as in part (1) applies without any
-- incorrect opposite-category separator bridge.
lemma no_strictly_decreasing_subobject_chain_of_gt_hom_card
    (hU : IsSeparator U) (κ' : Cardinal.{v}) (hκ' : Cardinal.mk (U ⟶ X) < κ') :
    ¬ ∃ A : κ'.ord.ToType → Subobject X, StrictAnti A := by
  rintro ⟨A, hA⟩
  let S : κ'.ord.ToType → Set (U ⟶ X) := fun i => Subobject.factorSet (A i) U
  have hS : StrictAnti S := by
    -- The same factor-set bridge transfers strict antitone subobject chains to subset chains.
    intro i j hij
    have hle : S j ≤ S i :=
      (Subobject.monotone_factorSet U) ((hA hij).le)
    have hne : S i ≠ S j := by
      intro hEq
      exact hij.ne (hA.injective ((Subobject.factorSet_injective (U := U) (X := X) hU) hEq))
    exact lt_of_le_of_ne hle hne.symm
  have hz : ∀ i, (0 : U ⟶ X) ∈ S i := by
    -- Every factor set contains the zero morphism.
    intro i
    exact (Subobject.mem_factorSet U (A i) 0).2 Subobject.factors_zero
  have hκ : Cardinal.mk (U ⟶ X) < (κ'.ord).card := by
    simpa using hκ'
  exact Subobject.no_strictly_decreasing_subset_chain_of_lt_card_ord hκ ⟨S, hS, hz⟩

/-- Lemma 19.11.1 (3): if `U` is a generator of the abelian category,
and `α` has cofinality greater than `#(U ⟶ X)`, then every increasing
`α`-indexed sequence of subobjects of `X` is eventually constant. -/
-- Proof sketch: if the sequence were not eventually constant, one extracts a cofinal strictly
-- increasing subsequence of factor sets in `Set (U ⟶ X)` indexed by a set of cardinality at most
-- `α.cof`, contradicting part (1) when `#(U ⟶ X) < α.cof`.
lemma monotone_subobject_sequence_eventually_constant_of_cof_gt_hom_card
    (hU : IsSeparator U) (α : Ordinal.{v}) (hα : Cardinal.mk (U ⟶ X) < α.cof)
    (A : α.ToType → Subobject X) (hA : Monotone A) :
    ∃ a₀ : α.ToType, ∀ b : α.ToType, a₀ ≤ b → A b = A a₀ := by
  classical
  let J : Set α.ToType := { a | ∀ b : α.ToType, b < a → A b < A a }
  by_contra hEventual
  have hJ_cofinal : IsCofinal J := by
    -- If the jump indices were bounded, monotonicity would force the tail to be constant.
    intro a
    by_contra hnot
    push Not at hnot
    have htail : ∀ b : α.ToType, a ≤ b → A b = A a := by
      intro b
      induction b using WellFoundedLT.induction with
      | ind b IH =>
          intro hab
          by_cases hbJ : b ∈ J
          · exact False.elim ((hnot b hbJ).not_ge hab)
          · have h_not_lt : ∃ c : α.ToType, c < b ∧ ¬ A c < A b := by
              simpa [J] using hbJ
            rcases h_not_lt with ⟨c, hcb, hAcb⟩
            have hcb_le : A c ≤ A b := hA hcb.le
            have hbc_le : A b ≤ A c := by
              by_contra hbc_le
              exact hAcb (lt_of_le_of_ne hcb_le fun hEq => hbc_le hEq.ge)
            have hEqcb : A c = A b := le_antisymm hcb_le hbc_le
            by_cases hac : a ≤ c
            · calc
                A b = A c := hEqcb.symm
                _ = A a := IH c hcb hac
            · have hca : c < a := lt_of_not_ge hac
              have hca_le : A c ≤ A a := hA hca.le
              have haa_le : A a ≤ A c := by
                simpa [hEqcb] using hA hab
              calc
                A b = A c := hEqcb.symm
                _ = A a := le_antisymm hca_le haa_le
    exact hEventual ⟨a, htail⟩
  have hJ_card : Cardinal.mk (U ⟶ X) < Cardinal.mk J := by
    -- A cofinal subset of `α.ToType` has cardinality at least `α.cof`.
    have hcof_le : α.cof ≤ Cardinal.mk J := by
      rw [← Ordinal.cof_toType α]
      exact Order.cof_le hJ_cofinal
    exact lt_of_lt_of_le hα hcof_le
  have hJ_strict : StrictMono fun j : J => A j := by
    -- By definition, each jump index is the first occurrence of its value.
    intro i j hij
    exact j.2 i hij
  let S : J → Set (U ⟶ X) := fun j => Subobject.factorSet (A j) U
  have hS : StrictMono S := by
    -- The factor-set embedding preserves the strictness of the jump subsequence.
    intro i j hij
    have hle : S i ≤ S j :=
      (Subobject.monotone_factorSet U) ((hJ_strict hij).le)
    have hne : S i ≠ S j := by
      intro hEq
      exact hij.ne (hJ_strict.injective ((Subobject.factorSet_injective (U := U) (X := X) hU) hEq))
    exact lt_of_le_of_ne hle hne
  have hz : ∀ j, (0 : U ⟶ X) ∈ S j := by
    -- Zero still factors through every subobject along the jump subsequence.
    intro j
    exact (Subobject.mem_factorSet U (A j) 0).2 Subobject.factors_zero
  exact Subobject.no_strictly_increasing_subset_chain_of_lt_card hJ_card ⟨S, hS, hz⟩

/-- Lemma 19.11.1 (4): if `U` is a generator of the abelian category,
and `α` has cofinality greater than `#(U ⟶ X)`, then every decreasing
`α`-indexed sequence of subobjects of `X` is eventually constant. -/
-- Proof sketch: send the antitone subobject sequence to the monotone sequence of complements of
-- its factor sets inside `Set (U ⟶ X)`. If the original sequence were not eventually constant,
-- these complements would yield a cofinal strictly increasing subsequence of subsets of
-- `Hom(U, X)`, contradicting part (2).
lemma antitone_subobject_sequence_eventually_constant_of_cof_gt_hom_card
    (hU : IsSeparator U) (α : Ordinal.{v}) (hα : Cardinal.mk (U ⟶ X) < α.cof)
    (A : α.ToType → Subobject X) (hA : Antitone A) :
    ∃ a₀ : α.ToType, ∀ b : α.ToType, a₀ ≤ b → A b = A a₀ := by
  classical
  let J : Set α.ToType := { a | ∀ b : α.ToType, b < a → A a < A b }
  by_contra hEventual
  have hJ_cofinal : IsCofinal J := by
    -- For an antitone family, bounded jump indices would again force eventual constancy.
    intro a
    by_contra hnot
    push Not at hnot
    have htail : ∀ b : α.ToType, a ≤ b → A b = A a := by
      intro b
      induction b using WellFoundedLT.induction with
      | ind b IH =>
          intro hab
          by_cases hbJ : b ∈ J
          · exact False.elim ((hnot b hbJ).not_ge hab)
          · have h_not_lt : ∃ c : α.ToType, c < b ∧ ¬ A b < A c := by
              simpa [J] using hbJ
            rcases h_not_lt with ⟨c, hcb, hAbc⟩
            have hbc_le : A b ≤ A c := hA hcb.le
            have hcb_le : A c ≤ A b := by
              by_contra hcb_le
              exact hAbc (lt_of_le_of_ne hbc_le fun hEq => hcb_le hEq.ge)
            have hEqcb : A b = A c := le_antisymm hbc_le hcb_le
            by_cases hac : a ≤ c
            · calc
                A b = A c := hEqcb
                _ = A a := IH c hcb hac
            · have hca : c < a := lt_of_not_ge hac
              have hca_le : A a ≤ A c := hA hca.le
              have haa_le : A c ≤ A a := by
                simpa [hEqcb] using hA hab
              calc
                A b = A c := hEqcb
                _ = A a := le_antisymm haa_le hca_le
    exact hEventual ⟨a, htail⟩
  have hJ_card : Cardinal.mk (U ⟶ X) < Cardinal.mk J := by
    -- A cofinal subset of `α.ToType` has cardinality at least `α.cof`.
    have hcof_le : α.cof ≤ Cardinal.mk J := by
      rw [← Ordinal.cof_toType α]
      exact Order.cof_le hJ_cofinal
    exact lt_of_lt_of_le hα hcof_le
  have hJ_strict : StrictAnti fun j : J => A j := by
    -- By definition, each jump index is the first occurrence of a strictly smaller value.
    intro i j hij
    exact j.2 i hij
  let S : J → Set (U ⟶ X) := fun j => Subobject.factorSet (A j) U
  have hS : StrictAnti S := by
    -- The factor-set embedding preserves strict antitonicity on the jump subsequence.
    intro i j hij
    have hle : S j ≤ S i :=
      (Subobject.monotone_factorSet U) ((hJ_strict hij).le)
    have hne : S i ≠ S j := by
      intro hEq
      exact hij.ne (hJ_strict.injective ((Subobject.factorSet_injective (U := U) (X := X) hU) hEq))
    exact lt_of_le_of_ne hle hne.symm
  have hz : ∀ j, (0 : U ⟶ X) ∈ S j := by
    -- Zero still factors through every subobject along the jump subsequence.
    intro j
    exact (Subobject.mem_factorSet U (A j) 0).2 Subobject.factors_zero
  exact Subobject.no_strictly_decreasing_subset_chain_of_lt_card hJ_card ⟨S, hS, hz⟩

/-- Lemma 19.11.1 (5): if `U` is a generator of the abelian category, then the set of
subobjects of `X` has cardinality at most `2 ^ #(U ⟶ X)`. -/
-- Proof sketch: the map `A ↦ Subobject.factorSet A U` from `Subobject X` to `Set (U ⟶ X)` is
-- injective by the separator criterion, so `Subobject X` embeds into the power set of `Hom(U, X)`.
lemma mk_subobject_le_two_pow_lift_hom_card
    (hU : IsSeparator U) :
    Cardinal.mk (Subobject X) ≤ 2 ^ Cardinal.lift (Cardinal.mk (U ⟶ X)) := by
  -- The factor-set map embeds subobjects into the powerset of `Hom(U, X)`.
  have hEmb :
      Nonempty (Subobject X ↪ Set (U ⟶ X)) := by
    refine ⟨⟨fun A => Subobject.factorSet A U, ?_⟩⟩
    exact Subobject.factorSet_injective (U := U) (X := X) hU
  have hle' :
      Cardinal.lift.{v, max u v} (Cardinal.mk (Subobject X)) ≤
        Cardinal.lift.{max u v, v} (Cardinal.mk (Set (U ⟶ X))) :=
    Cardinal.lift_mk_le'.2 hEmb
  calc
    Cardinal.mk (Subobject X) =
        Cardinal.lift.{v, max u v} (Cardinal.mk (Subobject X)) := by
      symm
      exact Cardinal.lift_id' (Cardinal.mk (Subobject X))
    _ ≤ Cardinal.lift.{max u v, v} (Cardinal.mk (Set (U ⟶ X))) := hle'
    _ = 2 ^ Cardinal.lift.{max u v, v} (Cardinal.mk (U ⟶ X)) := by
      simp [Cardinal.mk_set, Cardinal.lift_power]
    _ = 2 ^ Cardinal.lift.{u, v} (Cardinal.mk (U ⟶ X)) := by
      rw [Cardinal.lift_umax.{v, u}]
