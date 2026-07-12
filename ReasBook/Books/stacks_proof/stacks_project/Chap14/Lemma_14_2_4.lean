import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

namespace SimplexCategoryGenRel

open CategoryTheory

/- 
Domain-style sampling for Lemma 14.2.4:
- primary domain: simplicial-category presentations and equivalences of categories
- declarations inspected in the owner domain:
  `SimplexCategoryGenRel.toSimplexCategory`,
  `SimplexCategoryGenRel.exists_P_σ_P_δ_factorization`,
  `SimplexCategoryGenRel.exists_normal_form_P_σ`,
  `SimplexCategory.morphismProperty_eq_top`,
  `CategoryTheory.Functor.IsEquivalence`
- best owner abstraction: the owner predicate `toSimplexCategory.IsEquivalence`
- primitive data: the canonical functor `toSimplexCategory`
- derived API: downstream functor-category equivalences obtained from this theorem-instance via the
  generic `Functor.IsEquivalence` infrastructure, for example whiskering on the left
- source/core/bridge triage:
  `source-facing`: the textbook lemma that the canonical presentation functor is an equivalence,
  formalized as a named theorem-instance;
  `core/canonical`: the owner predicate `toSimplexCategory.IsEquivalence`;
  `bridge/view`: downstream whiskering-left equivalence instances induced from this theorem.
- layer target: `source-facing` theorem stated directly in the canonical owner form
  `toSimplexCategory.IsEquivalence`.
-/

-- Proof sketch: essential surjectivity is immediate on objects since both categories are indexed
-- by natural numbers. Fullness comes from `SimplexCategory.morphismProperty_eq_top`, which reduces
-- every simplex morphism to compositions of `δ` and `σ`, hence to images of generators in
-- `SimplexCategoryGenRel`. Faithfulness is reduced to comparing `P_σ`-then-`P_δ` factorizations in
-- `SimplexCategoryGenRel`, whose images are split epi / split mono factorizations in
-- `SimplexCategory`. Then `Functor.IsEquivalence.mk'` applies.
/-- Helper for Lemma 14.2.4: in an admissible list, the head is strictly smaller than every later
entry. -/
lemma head_lt_of_mem_tail_of_isAdmissible {m a : ℕ} {L : List ℕ}
    (hL : IsAdmissible m (a :: L)) {j : ℕ} (hj : j ∈ L) :
    a < j := by
  -- The admissibility constructors make the next entry larger than the head, and the tail stays
  -- admissible after shifting the base parameter.
  cases hL with
  | singleton ha =>
      simpa using hj
  | cons_cons hab htail ha =>
      rw [List.mem_cons] at hj
      rcases hj with rfl | hj
      · simpa using hab
      · exact lt_trans hab (head_lt_of_mem_tail_of_isAdmissible htail hj)

/-- Helper for Lemma 14.2.4: admissible lists are strictly increasing. -/
lemma pairwise_lt_of_isAdmissible {m : ℕ} {L : List ℕ} (hL : IsAdmissible m L) :
    L.Pairwise (· < ·) := by
  -- Repeatedly use the previous head-versus-tail lemma to build the pairwise comparison data.
  induction hL with
  | nil =>
      exact List.Pairwise.nil
  | singleton ha =>
      refine List.pairwise_cons.2 ?_
      constructor
      · intro j hj
        simpa using hj
      · exact List.Pairwise.nil
  | cons_cons hab htail ha ih =>
      refine List.pairwise_cons.2 ?_
      constructor
      · intro j hj
        exact head_lt_of_mem_tail_of_isAdmissible (IsAdmissible.cons_cons hab htail ha) hj
      · exact ih

/-- Helper for Lemma 14.2.4: admissible `σ`-normal forms are determined by their image in the
simplex category. -/
lemma admissible_list_eq_of_standardσ_map_eq {m m₁ : ℕ} {L₁ L₂ : List ℕ}
    (hL₁ : IsAdmissible m L₁) (hL₂ : IsAdmissible m L₂)
    (hk₁ : m + L₁.length = m₁) (hk₂ : m + L₂.length = m₁)
    (hmap : toSimplexCategory.map (standardσ L₁ hk₁) =
      toSimplexCategory.map (standardσ L₂ hk₂)) :
    L₁ = L₂ := by
  -- Equal morphisms in `SimplexCategory` have equal underlying order homomorphisms, so the two
  -- admissible lists have the same support set detected by `simplicialEvalσ`.
  have hOrder :
      SimplexCategory.Hom.toOrderHom (toSimplexCategory.map (standardσ L₁ hk₁)) =
        SimplexCategory.Hom.toOrderHom (toSimplexCategory.map (standardσ L₂ hk₂)) := by
    exact congrArg SimplexCategory.Hom.toOrderHom hmap
  have hmem : ∀ j : ℕ, j ∈ L₁ ↔ j ∈ L₂ := by
    intro j
    rw [mem_isAdmissible_iff L₁ hL₁ j, mem_isAdmissible_iff L₂ hL₂ j]
    constructor
    · rintro ⟨hj, hσ⟩
      have hj₁ : j < m₁ := by
        simpa [hk₁] using hj
      have hj₂ : j < m + L₂.length := by
        simpa [hk₂] using hj₁
      have hj_eval : j < m₁ + 1 := Nat.lt_succ_of_lt hj₁
      have hj_succ_eval : j + 1 < m₁ + 1 := Nat.succ_lt_succ hj₁
      let jj : Fin (m₁ + 1) := ⟨j, hj_eval⟩
      let jjSucc : Fin (m₁ + 1) := ⟨j + 1, hj_succ_eval⟩
      have hEvalj :
          simplicialEvalσ L₁ j = simplicialEvalσ L₂ j := by
        have hPointwise := congrArg Fin.val (congrArg (fun f => f jj) hOrder)
        calc
          simplicialEvalσ L₁ j =
              (SimplexCategory.Hom.toOrderHom (toSimplexCategory.map (standardσ L₁ hk₁))) jj := by
                symm
                simpa [jj] using simplicialEvalσ_of_isAdmissible L₁ m₁ m hL₁ hk₁ j hj_eval
          _ =
              (SimplexCategory.Hom.toOrderHom (toSimplexCategory.map (standardσ L₂ hk₂))) jj := hPointwise
          _ = simplicialEvalσ L₂ j := by
                simpa [jj] using simplicialEvalσ_of_isAdmissible L₂ m₁ m hL₂ hk₂ j hj_eval
      have hEvalSucc :
          simplicialEvalσ L₁ (j + 1) = simplicialEvalσ L₂ (j + 1) := by
        have hPointwise := congrArg Fin.val (congrArg (fun f => f jjSucc) hOrder)
        calc
          simplicialEvalσ L₁ (j + 1) =
              (SimplexCategory.Hom.toOrderHom (toSimplexCategory.map (standardσ L₁ hk₁))) jjSucc := by
                symm
                simpa [jjSucc] using
                  simplicialEvalσ_of_isAdmissible L₁ m₁ m hL₁ hk₁ (j + 1) hj_succ_eval
          _ =
              (SimplexCategory.Hom.toOrderHom (toSimplexCategory.map (standardσ L₂ hk₂))) jjSucc :=
                hPointwise
          _ = simplicialEvalσ L₂ (j + 1) := by
                simpa [jjSucc] using
                  simplicialEvalσ_of_isAdmissible L₂ m₁ m hL₂ hk₂ (j + 1) hj_succ_eval
      refine ⟨hj₂, ?_⟩
      calc
        simplicialEvalσ L₂ j = simplicialEvalσ L₁ j := hEvalj.symm
        _ = simplicialEvalσ L₁ (j + 1) := hσ
        _ = simplicialEvalσ L₂ (j + 1) := hEvalSucc
    · rintro ⟨hj, hσ⟩
      have hj₂ : j < m₁ := by
        simpa [hk₂] using hj
      have hj₁ : j < m + L₁.length := by
        simpa [hk₁] using hj₂
      have hj_eval : j < m₁ + 1 := Nat.lt_succ_of_lt hj₂
      have hj_succ_eval : j + 1 < m₁ + 1 := Nat.succ_lt_succ hj₂
      let jj : Fin (m₁ + 1) := ⟨j, hj_eval⟩
      let jjSucc : Fin (m₁ + 1) := ⟨j + 1, hj_succ_eval⟩
      have hEvalj :
          simplicialEvalσ L₁ j = simplicialEvalσ L₂ j := by
        have hPointwise := congrArg Fin.val (congrArg (fun f => f jj) hOrder)
        calc
          simplicialEvalσ L₁ j =
              (SimplexCategory.Hom.toOrderHom (toSimplexCategory.map (standardσ L₁ hk₁))) jj := by
                symm
                simpa [jj] using simplicialEvalσ_of_isAdmissible L₁ m₁ m hL₁ hk₁ j hj_eval
          _ =
              (SimplexCategory.Hom.toOrderHom (toSimplexCategory.map (standardσ L₂ hk₂))) jj := hPointwise
          _ = simplicialEvalσ L₂ j := by
                simpa [jj] using simplicialEvalσ_of_isAdmissible L₂ m₁ m hL₂ hk₂ j hj_eval
      have hEvalSucc :
          simplicialEvalσ L₁ (j + 1) = simplicialEvalσ L₂ (j + 1) := by
        have hPointwise := congrArg Fin.val (congrArg (fun f => f jjSucc) hOrder)
        calc
          simplicialEvalσ L₁ (j + 1) =
              (SimplexCategory.Hom.toOrderHom (toSimplexCategory.map (standardσ L₁ hk₁))) jjSucc := by
                symm
                simpa [jjSucc] using
                  simplicialEvalσ_of_isAdmissible L₁ m₁ m hL₁ hk₁ (j + 1) hj_succ_eval
          _ =
              (SimplexCategory.Hom.toOrderHom (toSimplexCategory.map (standardσ L₂ hk₂))) jjSucc :=
                hPointwise
          _ = simplicialEvalσ L₂ (j + 1) := by
                simpa [jjSucc] using
                  simplicialEvalσ_of_isAdmissible L₂ m₁ m hL₂ hk₂ (j + 1) hj_succ_eval
      refine ⟨hj₁, ?_⟩
      calc
        simplicialEvalσ L₁ j = simplicialEvalσ L₂ j := hEvalj
        _ = simplicialEvalσ L₂ (j + 1) := hσ
        _ = simplicialEvalσ L₁ (j + 1) := hEvalSucc.symm
  have hPair₁ : L₁.Pairwise (· < ·) := pairwise_lt_of_isAdmissible hL₁
  have hPair₂ : L₂.Pairwise (· < ·) := pairwise_lt_of_isAdmissible hL₂
  have hNodup₁ : L₁.Nodup := hPair₁.nodup
  have hNodup₂ : L₂.Nodup := hPair₂.nodup
  have hPerm : L₁.Perm L₂ := by
    refine (List.perm_iff_count.2 ?_)
    intro j
    by_cases hj₁ : j ∈ L₁
    · have hj₂ : j ∈ L₂ := (hmem j).1 hj₁
      rw [List.count_eq_one_of_mem hNodup₁ hj₁, List.count_eq_one_of_mem hNodup₂ hj₂]
    · have hj₂ : j ∉ L₂ := fun hj₂ ↦ hj₁ ((hmem j).2 hj₂)
      rw [List.count_eq_zero_of_not_mem hj₁, List.count_eq_zero_of_not_mem hj₂]
  -- Strictly increasing lists are determined by their underlying multiset of entries.
  refine hPerm.eq_of_pairwise ?_ hPair₁ hPair₂
  intro a b ha hb hab hba
  exact (Nat.lt_asymm hab hba).elim

/-- Helper for Lemma 14.2.4: the presentation functor is injective on morphisms that are pure
compositions of degeneracies. -/
lemma toSimplexCategory_map_injective_of_P_σ {x y : SimplexCategoryGenRel} {e₁ e₂ : x ⟶ y}
    (he₁ : P_σ e₁) (he₂ : P_σ e₂) (hmap : toSimplexCategory.map e₁ = toSimplexCategory.map e₂) :
    e₁ = e₂ := by
  -- Put both source morphisms into the imported admissible `σ`-normal form.
  obtain ⟨L₁, m₁, b₁, hy₁, hx₁, hlen₁, hL₁, heq₁⟩ := exists_normal_form_P_σ e₁ he₁
  obtain ⟨L₂, m₂, b₂, hy₂, hx₂, hlen₂, hL₂, heq₂⟩ := exists_normal_form_P_σ e₂ he₂
  have hm₁ : m₁ = y.len := by
    simpa using congrArg len hy₁
  have hm₂ : m₂ = y.len := by
    simpa using congrArg len hy₂
  subst hm₁
  subst hm₂
  cases hy₁
  cases hy₂
  have hxlen₁ : x.len = y.len + b₁ := by
    simpa using congrArg len hx₁
  have hxlen₂ : x.len = y.len + b₂ := by
    simpa using congrArg len hx₂
  have hb : b₁ = b₂ := by
    exact Nat.add_left_cancel (hxlen₁.symm.trans hxlen₂)
  subst hb
  have hk₁ : y.len + L₁.length = x.len := by
    rw [hlen₁, hxlen₁.symm]
  have hk₂ : y.len + L₂.length = x.len := by
    rw [hlen₂, hxlen₂.symm]
  have hstandard :
      toSimplexCategory.map (standardσ L₁ hk₁) =
        toSimplexCategory.map (standardσ L₂ hk₂) := by
    simpa [heq₁, heq₂] using hmap
  -- Equality of the target maps recovers equality of the admissible index lists.
  have hL : L₁ = L₂ := admissible_list_eq_of_standardσ_map_eq hL₁ hL₂ hk₁ hk₂ hstandard
  subst hL
  simpa [heq₁, heq₂]

/-- Helper for Lemma 14.2.4: `standardδ` is the canonical face-word normal form, so an admissible
list `[i₀, ..., i_r]` represents the composite `δ i₀ ≫ ⋯ ≫ δ i_r`. -/
def standardδ (L : List ℕ) {m₁ m₂ : ℕ} (h : m₁ + L.length = m₂) : mk m₁ ⟶ mk m₂ :=
  match L with
  | .nil => eqToHom (by grind)
  | .cons a t => δ (Fin.ofNat _ a) ≫ standardδ (m₁ := m₁ + 1) (m₂ := m₂) t (by grind)

/-- Helper for Lemma 14.2.4: the empty face word gives the identity morphism. -/
@[simp]
lemma standardδ_nil (m : ℕ) : standardδ (m₁ := m) (m₂ := m) .nil rfl = 𝟙 (mk m) := by
  -- With no face map to compose, `standardδ` reduces to the identity.
  simp [standardδ]

/-- Helper for Lemma 14.2.4: unfolding `standardδ` on a nonempty list peels off the first face map
in the encoded word. -/
@[simp, reassoc]
lemma standardδ_cons (L : List ℕ) (a : ℕ) {m₁ m₂ : ℕ} (h : m₁ + (a :: L).length = m₂) :
    standardδ (m₁ := m₁) (m₂ := m₂) (L.cons a) h =
      δ (Fin.ofNat _ a) ≫ standardδ (m₁ := m₁ + 1) (m₂ := m₂) L (by grind) := rfl

/-- Helper for Lemma 14.2.4: when the target length is definitionally `m + (a :: L).length`, the
length bookkeeping in `standardδ_cons` becomes completely transparent. -/
@[simp, reassoc]
lemma standardδ_cons_rfl (L : List ℕ) (a m : ℕ) :
    standardδ (m₁ := m) (m₂ := m + (a :: L).length) (a :: L) rfl =
      δ (Fin.ofNat _ a) ≫
        standardδ (m₁ := m + 1) (m₂ := m + L.length + 1) L (by omega) := by
  -- In this normalized length bookkeeping, the recursive tail proof uses definitional equality.
  simp [standardδ]

/-- Helper for Lemma 14.2.4: a singleton face word is exactly the corresponding generating face
map. -/
@[simp]
lemma standardδ_singleton (m a : ℕ) :
    standardδ (m₁ := m) (m₂ := m + 1) [a] (by simp) = δ (Fin.ofNat _ a) := by
  -- Route correction: the face-side normal-form package starts by fixing the one-face base case
  -- before attempting the insertion recursion.
  simpa using standardδ_cons_rfl [] a m

/-- Helper for Lemma 14.2.4: `Fin.ofNat` fixes the value of an already-bounded simplex index. -/
@[simp]
lemma fin_ofNat_val_eq {n : ℕ} [NeZero n] (i : Fin n) : Fin.ofNat n i.1 = i := by
  apply Fin.ext
  simpa [Fin.ofNat] using Nat.mod_eq_of_lt i.2

/-- Helper for Lemma 14.2.4: the singleton `standardδ` word maps to the matching simplex coface. -/
@[simp]
lemma toSimplexCategory_map_standardδ_singleton {n : ℕ} (i : Fin (n + 2)) :
    toSimplexCategory.map (standardδ (m₁ := n) (m₂ := n + 1) [i.1] (by simp)) =
      SimplexCategory.δ i := by
  -- Rewriting the singleton normal form reduces the claim to the functorial image of one `δ`.
  simpa using
    congrArg toSimplexCategory.map (standardδ_singleton n i.1)

/-- Helper for Lemma 14.2.4: a two-term face word expands to the expected composite of two face
maps in the same left-to-right order as the list. -/
@[simp]
lemma standardδ_pair (m a b : ℕ) :
    standardδ (m₁ := m) (m₂ := m + 2) [a, b] (by simp) =
      δ (Fin.ofNat _ a) ≫ δ (Fin.ofNat _ b) := by
  -- Unfolding twice shows exactly how the recursive normal form follows the list order.
  simp

/-- Helper for Lemma 14.2.4: every simplex morphism lifts through the presentation functor. -/
lemma simplex_hom_lift_exists {Δ₁ Δ₂ : SimplexCategory} (θ : Δ₁ ⟶ Δ₂) :
    ∃ f : SimplexCategoryGenRel.mk Δ₁.len ⟶ SimplexCategoryGenRel.mk Δ₂.len,
      toSimplexCategory.map f = θ := by
  let W : MorphismProperty SimplexCategory := fun X Y φ =>
    ∃ f : SimplexCategoryGenRel.mk X.len ⟶ SimplexCategoryGenRel.mk Y.len,
      toSimplexCategory.map f = φ
  have hWmul : W.IsMultiplicative := by
    refine { id_mem := ?_, comp_mem := ?_ }
    · intro X
      refine ⟨𝟙 _, ?_⟩
      simp
    · intro X Y Z f g hf hg
      rcases hf with ⟨f', hf'⟩
      rcases hg with ⟨g', hg'⟩
      refine ⟨f' ≫ g', ?_⟩
      simp [hf', hg']
  letI : W.IsMultiplicative := hWmul
  have hWtop : W = ⊤ := by
    refine SimplexCategory.morphismProperty_eq_top W ?_ ?_
    · intro n i
      refine ⟨δ i, ?_⟩
      simp
    · intro n i
      refine ⟨σ i, ?_⟩
      simp
  have hθ : W θ := by
    rw [hWtop]
    trivial
  exact hθ

/-- Helper for Lemma 14.2.4: a pure face-word endomorphism must be the identity. -/
lemma p_delta_endomorphism_eq_id {x : SimplexCategoryGenRel} {m : x ⟶ x} (hm : P_δ m) :
    m = 𝟙 x := by
  -- A non-identity `P_δ` morphism strictly raises simplex length, so an endomorphism cannot be
  -- anything but the identity transport.
  rcases eq_or_len_le_of_P_δ hm with ⟨h, hmEq⟩ | hlt
  · cases h
    simpa using hmEq
  · exact (Nat.lt_irrefl x.len hlt).elim

/-- Helper for Lemma 14.2.4: a pure degeneracy endomorphism must be the identity. -/
lemma p_sigma_endomorphism_eq_id {x : SimplexCategoryGenRel} {e : x ⟶ x} (he : P_σ e) :
    e = 𝟙 x := by
  -- The imported `σ`-normal form records an endomorphism by a list of length `b` with
  -- `x.len = x.len + b`, so the list must be empty.
  obtain ⟨L, m, b, h₁, h₂, h, hL, heq⟩ := exists_normal_form_P_σ e he
  have hm : m = x.len := by
    simpa using congrArg len h₁
  have hmb : m = m + b := by
    calc
      m = x.len := hm
      _ = m + b := by
        simpa [hm] using congrArg len h₂
  have hb : b = 0 := by
    omega
  subst hb
  have hnil : L = [] := by
    cases L with
    | nil =>
        rfl
    | cons a t =>
        simp at h
  subst hnil
  cases h₁
  cases h₂
  simpa [standardσ_nil] using heq

/-- Helper for Lemma 14.2.4: if an endomorphism maps to the identity simplex morphism, then the
endomorphism was already equal to the identity in the presentation. -/
lemma toSimplexCategory_map_eq_id_of_endomorphism {x : SimplexCategoryGenRel} {u : x ⟶ x}
    (hmap : toSimplexCategory.map u = 𝟙 (toSimplexCategory.obj x)) :
    u = 𝟙 x := by
  -- Factor the endomorphism as a pure degeneracy followed by a pure face map.
  obtain ⟨z, e, m, he, hm, hfac⟩ := exists_P_σ_P_δ_factorization u
  have hem :
      toSimplexCategory.map e ≫ toSimplexCategory.map m =
        𝟙 (toSimplexCategory.obj x) := by
    simpa [hfac] using hmap
  letI : IsSplitEpi (toSimplexCategory.map e) :=
    isSplitEpi_toSimplexCategory_map_of_P_σ he
  have hme :
      toSimplexCategory.map m ≫ toSimplexCategory.map e =
        𝟙 (toSimplexCategory.obj z) := by
    -- Cancel the common split epi to show the two factors are inverse in `SimplexCategory`.
    apply (CategoryTheory.cancel_epi (toSimplexCategory.map e)).1
    calc
      toSimplexCategory.map e ≫ toSimplexCategory.map m ≫ toSimplexCategory.map e
          = (toSimplexCategory.map e ≫ toSimplexCategory.map m) ≫ toSimplexCategory.map e := by
              simp [Category.assoc]
      _ = 𝟙 (toSimplexCategory.obj x) ≫ toSimplexCategory.map e := by rw [hem]
      _ = toSimplexCategory.map e := by simp
      _ = toSimplexCategory.map e ≫ 𝟙 (toSimplexCategory.obj z) := by simp
  have hIso : IsIso (toSimplexCategory.map m) := by
    exact CategoryTheory.IsIso.mk ⟨toSimplexCategory.map e, hme, hem⟩
  have hzObj :
      toSimplexCategory.obj z = toSimplexCategory.obj x := by
    exact SimplexCategory.skeletal ⟨CategoryTheory.asIso (toSimplexCategory.map m)⟩
  have hzLen : z.len = x.len := by
    simpa using congrArg SimplexCategory.len hzObj
  have hz : z = x := SimplexCategoryGenRel.ext hzLen
  subst z
  -- Once the middle object is identified with `x`, both factors are endomorphisms and hence
  -- individually trivial by the two previous lemmas.
  have heId : e = 𝟙 x := p_sigma_endomorphism_eq_id he
  have hmId : m = 𝟙 x := p_delta_endomorphism_eq_id hm
  simpa [hfac, heId, hmId]

/-- Helper for Lemma 14.2.4: every `P_δ` morphism admits a retraction in the presentation
category. -/
lemma pDeltaRetract {x y : SimplexCategoryGenRel} {m : x ⟶ y} (hm : P_δ m) :
    ∃ r : y ⟶ x, m ≫ r = 𝟙 x := by
  -- A `P_δ` morphism is split mono, so we can use its chosen retraction directly.
  letI : IsSplitMono m := isSplitMono_P_δ hm
  refine ⟨CategoryTheory.retraction m, ?_⟩
  simpa using CategoryTheory.IsSplitMono.id m

/-- Helper for Lemma 14.2.4: a `P_δ` morphism between consecutive simplex lengths is a single face
map. -/
lemma pDelta_eq_delta_of_target_succ {n : ℕ} {m : mk n ⟶ mk (n + 1)} (hm : P_δ m) :
    ∃ i : Fin (n + 2), m = δ i := by
  -- A nontrivial `P_δ` word landing one step higher cannot contain more than one face map.
  cases hm with
  | of x hx =>
      cases hx with
      | δ i =>
          exact ⟨i, rfl⟩
  | comp_of f g hf hg =>
      cases hg with
      | δ i =>
          have hfId : f = 𝟙 (mk n) := p_delta_endomorphism_eq_id hf
          subst hfId
          exact ⟨i, by simp⟩

/-- Helper for Lemma 14.2.4: a `P_σ` morphism whose simplex-category image is monic is just the
identity transport along the induced object equality. -/
lemma pSigma_eq_eqToHom_of_mono_map {x z : SimplexCategoryGenRel} {e : x ⟶ z} (he : P_σ e)
    [Mono (toSimplexCategory.map e)] :
    ∃ h : x = z, e = eqToHom h := by
  -- A split epi that is also mono becomes an isomorphism, so the `P_σ` morphism is an
  -- endomorphism and hence trivial.
  letI : IsSplitEpi (toSimplexCategory.map e) := isSplitEpi_toSimplexCategory_map_of_P_σ he
  have hIso : IsIso (toSimplexCategory.map e) := CategoryTheory.isIso_of_mono_of_isSplitEpi _
  have hzObj :
      toSimplexCategory.obj x = toSimplexCategory.obj z := by
    exact SimplexCategory.skeletal ⟨CategoryTheory.asIso (toSimplexCategory.map e)⟩
  have hzLen : x.len = z.len := by
    simpa using congrArg SimplexCategory.len hzObj
  have hz : x = z := SimplexCategoryGenRel.ext hzLen
  refine ⟨hz, ?_⟩
  subst hz
  simpa using p_sigma_endomorphism_eq_id he

/-- Helper for Lemma 14.2.4: the presentation functor is injective on pure compositions of face
maps. -/
lemma toSimplexCategory_map_injective_of_P_δ {x y : SimplexCategoryGenRel} {m₁ m₂ : x ⟶ y}
    (hm₁ : P_δ m₁) (hm₂ : P_δ m₂) (hmap : toSimplexCategory.map m₁ = toSimplexCategory.map m₂) :
    m₁ = m₂ := by
  -- Route correction: the split-mono route proves that `m₁` and `m₂` share a retraction, but a
  -- common retraction does not determine a `P_δ` morphism uniquely.
  -- TODO: prove that equal simplex images force the same final omitted value, strip the common
  -- final `δ`, and recurse on the shorter `P_δ` words using the two helpers above.
  sorry

/-- Helper for Lemma 14.2.4: the presentation functor is faithful. -/
lemma toSimplexCategory_map_injective {x y : SimplexCategoryGenRel} {f g : x ⟶ y}
    (hmap : toSimplexCategory.map f = toSimplexCategory.map g) :
    f = g := by
  -- Factor both morphisms into their `P_σ` and `P_δ` parts.
  obtain ⟨z₁, e₁, m₁, he₁, hm₁, hf⟩ := exists_P_σ_P_δ_factorization f
  obtain ⟨z₂, e₂, m₂, he₂, hm₂, hg⟩ := exists_P_σ_P_δ_factorization g
  let φ := toSimplexCategory.map f
  have hfac₁ : toSimplexCategory.map e₁ ≫ toSimplexCategory.map m₁ = φ := by
    simpa [φ, hf]
  have hfac₂ : toSimplexCategory.map e₂ ≫ toSimplexCategory.map m₂ = φ := by
    simpa [φ, hg] using hmap.symm
  letI : IsSplitEpi (toSimplexCategory.map e₁) :=
    isSplitEpi_toSimplexCategory_map_of_P_σ he₁
  letI : IsSplitEpi (toSimplexCategory.map e₂) :=
    isSplitEpi_toSimplexCategory_map_of_P_σ he₂
  letI : IsSplitMono (toSimplexCategory.map m₁) :=
    isSplitMono_toSimplexCategory_map_of_P_δ hm₁
  letI : IsSplitMono (toSimplexCategory.map m₂) :=
    isSplitMono_toSimplexCategory_map_of_P_δ hm₂
  letI : Epi (toSimplexCategory.map e₁) := by infer_instance
  letI : Epi (toSimplexCategory.map e₂) := by infer_instance
  letI : Mono (toSimplexCategory.map m₁) := by infer_instance
  letI : Mono (toSimplexCategory.map m₂) := by infer_instance
  -- The simplex-category image of the common map identifies the two intermediate objects.
  have hzObj :
      toSimplexCategory.obj z₁ = toSimplexCategory.obj z₂ := by
    exact (SimplexCategory.image_eq hfac₁).symm.trans (SimplexCategory.image_eq hfac₂)
  have hzLen : z₁.len = z₂.len := by
    simpa using congrArg SimplexCategory.len hzObj
  have hz : z₁ = z₂ := SimplexCategoryGenRel.ext hzLen
  subst z₂
  have himg : toSimplexCategory.obj z₁ = Limits.image φ := by
    exact (SimplexCategory.image_eq hfac₁).symm
  -- Route correction: transport both factorizations to the actual image object before invoking the
  -- simplex-category image API, then cancel the transport isomorphisms.
  let e₁' : toSimplexCategory.obj x ⟶ Limits.image φ :=
    toSimplexCategory.map e₁ ≫ eqToHom himg
  let e₂' : toSimplexCategory.obj x ⟶ Limits.image φ :=
    toSimplexCategory.map e₂ ≫ eqToHom himg
  let m₁' : Limits.image φ ⟶ toSimplexCategory.obj y :=
    eqToHom himg.symm ≫ toSimplexCategory.map m₁
  let m₂' : Limits.image φ ⟶ toSimplexCategory.obj y :=
    eqToHom himg.symm ≫ toSimplexCategory.map m₂
  have hfac₁' : e₁' ≫ m₁' = φ := by
    dsimp [e₁', m₁']
    simpa [Category.assoc] using hfac₁
  have hfac₂' : e₂' ≫ m₂' = φ := by
    dsimp [e₂', m₂']
    simpa [Category.assoc] using hfac₂
  have heMap' : e₁' = e₂' := by
    calc
      e₁' = Limits.factorThruImage φ := by
        symm
        exact SimplexCategory.factorThruImage_eq hfac₁'
      _ = e₂' := SimplexCategory.factorThruImage_eq hfac₂'
  have hmMap' : m₁' = m₂' := by
    calc
      m₁' = Limits.image.ι φ := by
        symm
        exact SimplexCategory.image_ι_eq hfac₁'
      _ = m₂' := SimplexCategory.image_ι_eq hfac₂'
  have heMap : toSimplexCategory.map e₁ = toSimplexCategory.map e₂ := by
    apply (CategoryTheory.cancel_mono (eqToHom himg)).1
    simpa [e₁', e₂'] using heMap'
  have hmMap : toSimplexCategory.map m₁ = toSimplexCategory.map m₂ := by
    apply (CategoryTheory.cancel_epi (eqToHom himg.symm)).1
    simpa [m₁', m₂', Category.assoc] using hmMap'
  have heqE : e₁ = e₂ := toSimplexCategory_map_injective_of_P_σ he₁ he₂ heMap
  have heqM : m₁ = m₂ := toSimplexCategory_map_injective_of_P_δ hm₁ hm₂ hmMap
  simpa [hf, hg, heqE, heqM]

/-- Lemma 14.2.4: the category `Δ` is the universal category generated by the objects `[n]`,
the coface maps `δ`, and the codegeneracy maps `σ` subject only to the simplicial identities; in
Lean, this is expressed by saying that the canonical functor from the generators-and-relations
presentation `SimplexCategoryGenRel` to `SimplexCategory` is an equivalence. -/
@[stacks 0168, instance]
theorem toSimplexCategory_isEquivalence :
    toSimplexCategory.IsEquivalence := by
  -- Faithfulness is reduced to the injectivity lemma proved above.
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_⟩
    intro x y f g hfg
    exact toSimplexCategory_map_injective hfg
  · refine ⟨?_⟩
    intro x y θ
    let a := x.len
    let b := y.len
    have hx : x = SimplexCategoryGenRel.mk a := by
      exact (SimplexCategoryGenRel.ext rfl).symm
    have hy : y = SimplexCategoryGenRel.mk b := by
      exact (SimplexCategoryGenRel.ext rfl).symm
    cases hx
    cases hy
    simpa [a, b] using simplex_hom_lift_exists θ
  · refine ⟨?_⟩
    intro Δ
    refine ⟨SimplexCategoryGenRel.mk Δ.len, ?_⟩
    refine ⟨eqToIso (SimplexCategory.mk_len Δ)⟩

end SimplexCategoryGenRel
