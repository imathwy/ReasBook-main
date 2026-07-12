import Mathlib

universe u v

section

variable {K : Type u} [Field K] {A : Type v} [Nonempty A]

/-
Domain triage:
* primary domain: linear algebra over subfields and directed intersections of subfields;
* sampled owner declarations:
  - `Subfield.mem_iInf`,
  - `Submodule.restrictScalars`,
  - `Submodule.pi`,
  - `Subalgebra.mem_bot`;
* best owner abstraction: for a subfield `k ≤ K`, the vectors of `K^n` with all coordinates in `k`
  are the canonical `k`-submodule `k.vectorSubmodule n`;
* primitive data: the family of subfields `Kα` and the `K`-subspace `V`;
* derived API: existence of a nonzero vector in `V` whose coordinates lie in a given subfield;
* layer triage:
  - `source-facing`: the existence criterion of Lemma `15.46.3`;
  - `core/canonical`: `Submodule.restrictScalars`, `Submodule.pi`, and `Subfield.mem_iInf`;
  - `bridge/view`: `Subfield.vectorSubmodule`, the coordinatewise copy of `k` in `K^n`.
-/

namespace Subfield

/-- The coordinatewise copy of `k` inside `K^n`, viewed as a `k`-submodule of `K^n`. -/
abbrev vectorSubmodule (k : Subfield K) (n : ℕ) : Submodule k (Fin n → K) :=
  Submodule.pi Set.univ (fun _ : Fin n ↦ (⊥ : Subalgebra k K).toSubmodule)

/-- Helper for Lemma 15.46.3: a vector belongs to the coordinatewise copy of a subfield exactly
when each coordinate belongs to that subfield. -/
lemma mem_vectorSubmodule_iff (k : Subfield K) {n : ℕ} {v : Fin n → K} :
    v ∈ k.vectorSubmodule n ↔ ∀ i, v i ∈ k := by
  constructor
  · intro hv
    have hv' : ∀ i, v i ∈ (⊥ : Subalgebra k K) := by
      simpa [vectorSubmodule] using hv
    intro i
    rcases hv' i with ⟨x, hx⟩
    have hxk : ((algebraMap k K x) : K) ∈ k := by
      change ((x : K)) ∈ k
      exact x.2
    exact hx ▸ hxk
  · intro hv
    have hv' : ∀ i, v i ∈ (⊥ : Subalgebra k K) := by
      intro i
      exact ⟨⟨v i, hv i⟩, rfl⟩
    simpa [vectorSubmodule] using hv'

/-- Helper for Lemma 15.46.3: subfield inclusion transports coordinatewise membership upward. -/
lemma mem_vectorSubmodule_of_le {k k' : Subfield K} (hkk' : k ≤ k') {n : ℕ} {v : Fin n → K}
    (hv : v ∈ k.vectorSubmodule n) :
    v ∈ k'.vectorSubmodule n := by
  rw [mem_vectorSubmodule_iff] at hv ⊢
  intro i
  exact hkk' (hv i)

end Subfield

/-- Helper for Lemma 15.46.3: prepend a zero coordinate to a function on `Fin n`. -/
abbrev cons_zero_fun {n : ℕ} (t : Fin n → K) : Fin (n + 1) → K :=
  fun i ↦ Fin.cases 0 t i

/-- Helper for Lemma 15.46.3: drop the first coordinate of a function on `Fin (n + 1)`. -/
abbrev tail_fun {n : ℕ} (v : Fin (n + 1) → K) : Fin n → K :=
  fun i ↦ v i.succ

/-- Helper for Lemma 15.46.3: `cons_zero_fun` is additive. -/
lemma cons_zero_fun_add {n : ℕ} (x y : Fin n → K) :
    cons_zero_fun (x + y) = cons_zero_fun x + cons_zero_fun y := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [cons_zero_fun]
  · intro j
    simp [cons_zero_fun]

/-- Helper for Lemma 15.46.3: `cons_zero_fun` commutes with scalar multiplication. -/
lemma cons_zero_fun_smul {n : ℕ} (a : K) (x : Fin n → K) :
    cons_zero_fun (a • x) = a • cons_zero_fun x := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [cons_zero_fun]
  · intro j
    simp [cons_zero_fun]

/-- Helper for Lemma 15.46.3: prepending a zero coordinate is a linear map. -/
abbrev cons_zero_linear (n : ℕ) : (Fin n → K) →ₗ[K] (Fin (n + 1) → K) where
  toFun := cons_zero_fun
  map_add' := cons_zero_fun_add
  map_smul' := cons_zero_fun_smul

/-- Helper for Lemma 15.46.3: prepending zero preserves coordinatewise subfield membership. -/
lemma mem_vectorSubmodule_cons_zero_iff {L : Subfield K} {n : ℕ} {t : Fin n → K} :
    cons_zero_fun t ∈ L.vectorSubmodule (n + 1) ↔ t ∈ L.vectorSubmodule n := by
  rw [Subfield.mem_vectorSubmodule_iff, Subfield.mem_vectorSubmodule_iff]
  constructor
  · intro ht i
    simpa using ht i.succ
  · intro ht i
    refine Fin.cases ?_ ?_ i
    · simpa [cons_zero_fun] using L.zero_mem
    · intro j
      simpa [cons_zero_fun] using ht j

/-- Helper for Lemma 15.46.3: a tail vector in the comap produces a head-zero vector upstairs. -/
lemma cons_zero_mem_of_tail {L : Subfield K} {n : ℕ}
    (V : Submodule K (Fin (n + 1) → K)) {t : Fin n → K}
    (ht : t ∈ (V.comap (cons_zero_linear n)).restrictScalars L ⊓ L.vectorSubmodule n) :
    cons_zero_fun t ∈ V.restrictScalars L ⊓ L.vectorSubmodule (n + 1) := by
  constructor
  · exact ht.1
  · exact (mem_vectorSubmodule_cons_zero_iff).2 ht.2

/-- Helper for Lemma 15.46.3: if the head coordinate is zero, the tail lies in the tail comap. -/
lemma tail_mem_of_head_zero {L : Subfield K} {n : ℕ}
    (V : Submodule K (Fin (n + 1) → K)) {v : Fin (n + 1) → K}
    (hv : v ∈ V.restrictScalars L ⊓ L.vectorSubmodule (n + 1)) (h0 : v 0 = 0) :
    tail_fun v ∈ (V.comap (cons_zero_linear n)).restrictScalars L ⊓ L.vectorSubmodule n := by
  constructor
  · change cons_zero_fun (tail_fun v) ∈ V
    have hcons : cons_zero_fun (tail_fun v) = v := by
      ext i
      refine Fin.cases ?_ ?_ i
      · simpa [cons_zero_fun] using h0.symm
      · intro j
        simp [cons_zero_fun, tail_fun]
    simpa [hcons] using hv.1
  · have hvL : v ∈ L.vectorSubmodule (n + 1) := hv.2
    change tail_fun v ∈ L.vectorSubmodule n
    rw [Subfield.mem_vectorSubmodule_iff] at hvL ⊢
    intro i
    simpa [tail_fun] using hvL i.succ

/-- Helper for Lemma 15.46.3: if there are no nonzero tail vectors over `L`, then a head-zero
vector in `V ∩ L^(n+1)` must vanish. -/
lemma eq_zero_of_head_zero_of_no_tail_vector {L : Subfield K} {n : ℕ}
    (V : Submodule K (Fin (n + 1) → K))
    (h_no_tail :
      ¬ ∃ t ∈ (V.comap (cons_zero_linear n)).restrictScalars L ⊓ L.vectorSubmodule n, t ≠ 0)
    {v : Fin (n + 1) → K}
    (hv : v ∈ V.restrictScalars L ⊓ L.vectorSubmodule (n + 1)) (h0 : v 0 = 0) :
    v = 0 := by
  by_contra hv_ne
  have htail : tail_fun v ∈ (V.comap (cons_zero_linear n)).restrictScalars L ⊓
      L.vectorSubmodule n := tail_mem_of_head_zero V hv h0
  have htail_ne : tail_fun v ≠ 0 := by
    intro htail_zero
    apply hv_ne
    have hcons : cons_zero_fun (tail_fun v) = v := by
      ext i
      refine Fin.cases ?_ ?_ i
      · simpa [cons_zero_fun] using h0.symm
      · intro j
        simp [cons_zero_fun, tail_fun]
    calc
      v = cons_zero_fun (tail_fun v) := hcons.symm
      _ = 0 := by
        ext i
        refine Fin.cases ?_ ?_ i
        · simp [cons_zero_fun]
        · intro j
          have hj := congrArg (fun f : Fin n → K ↦ f j) htail_zero
          simpa [cons_zero_fun, tail_fun] using hj
  exact h_no_tail ⟨tail_fun v, htail, htail_ne⟩

/-- Helper for Lemma 15.46.3: under trivial tail intersection, a normalized vector is unique. -/
lemma eq_of_head_one_of_no_tail_vector {L : Subfield K} {n : ℕ}
    (V : Submodule K (Fin (n + 1) → K))
    (h_no_tail :
      ¬ ∃ t ∈ (V.comap (cons_zero_linear n)).restrictScalars L ⊓ L.vectorSubmodule n, t ≠ 0)
    {u w : Fin (n + 1) → K}
    (hu : u ∈ V.restrictScalars L ⊓ L.vectorSubmodule (n + 1))
    (hw : w ∈ V.restrictScalars L ⊓ L.vectorSubmodule (n + 1))
    (hu0 : u 0 = 1) (hw0 : w 0 = 1) :
    u = w := by
  -- Subtract the two normalized vectors and use triviality of the tail intersection.
  have hsub : u - w ∈ V.restrictScalars L ⊓ L.vectorSubmodule (n + 1) := by
    exact sub_mem hu hw
  have hsub0 : (u - w) 0 = 0 := by
    simp [hu0, hw0]
  have hzero := eq_zero_of_head_zero_of_no_tail_vector V h_no_tail hsub hsub0
  exact sub_eq_zero.mp hzero

/-- Helper for Lemma 15.46.3: a nonzero vector over `L` can be normalized to have head
coordinate `1`. -/
lemma exists_normalized_vector {L : Subfield K} {n : ℕ}
    (V : Submodule K (Fin (n + 1) → K)) {v : Fin (n + 1) → K}
    (hv : v ∈ V.restrictScalars L ⊓ L.vectorSubmodule (n + 1)) (hv0 : v 0 ≠ 0) :
    ∃ w ∈ V.restrictScalars L ⊓ L.vectorSubmodule (n + 1), w 0 = 1 := by
  let c : L := ⟨(v 0)⁻¹, L.inv_mem ((Subfield.mem_vectorSubmodule_iff L).1 hv.2 0)⟩
  refine ⟨c • v, ?_, ?_⟩
  · exact (V.restrictScalars L ⊓ L.vectorSubmodule (n + 1)).smul_mem c hv
  · change ((c : K) * v 0) = 1
    simp [c, hv0]

/-- Helper for Lemma 15.46.3: membership in every family vector submodule descends to the
intersection subfield. -/
lemma mem_base_vectorSubmodule_of_mem_all_family
    (k : Subfield K) (Kα : A → Subfield K) (h_inter : k = ⨅ α, Kα α)
    {m : ℕ} {v : Fin m → K}
    (hv : ∀ α, v ∈ (Kα α).vectorSubmodule m) :
    v ∈ k.vectorSubmodule m := by
  rw [Subfield.mem_vectorSubmodule_iff]
  intro i
  have hcoord : v i ∈ ⨅ α, Kα α := by
    rw [Subfield.mem_iInf]
    intro α
    exact (Subfield.mem_vectorSubmodule_iff (Kα α)).1 (hv α) i
  simpa [h_inter] using hcoord

-- Proof sketch: for `n = 0`, the coordinatewise submodule `k.vectorSubmodule 0` is trivial, so
-- both
-- sides are false. For `n = 1`, the claim is exactly the statement that membership in
-- `k = ⨅ α, Kα α` is equivalent to membership in every `Kα α` via `Subfield.mem_iInf`; the
-- nonemptiness hypothesis rules out the degenerate empty intersection `⨅ α, Kα α = ⊤`. For the
-- inductive step, first study the intersection of `V` with the last `n - 1` coordinates, then
-- choose an index `α` for which this smaller intersection over `Kα α` is trivial. A nonzero
-- vector in `V` with coordinates in `Kα α` can then be normalized so that its first coordinate is
-- `1`, forcing every other `Kα α`-rational vector in `V` to be a scalar multiple of it. The
-- downward directedness of the family and the hypothesis `k = ⨅ α, Kα α` then show that the
-- remaining coordinates already lie in `k`.
/-- Lemma 15.46.3: for a nonempty downward directed family of subfields of `K` whose intersection
is `k`, a `K`-subspace of `K^n` contains a nonzero vector with all coordinates in `k` if and only
if it contains such a vector over every subfield in the family. -/
@[stacks 07P3]
theorem exists_nonzero_vector_in_base_subfield_iff_forall_exists_nonzero_vector_in_family
    (k : Subfield K) (Kα : A → Subfield K) (h_inter : k = ⨅ α, Kα α)
    (h_directed : Directed (· ≥ ·) Kα) {n : ℕ} (V : Submodule K (Fin n → K)) :
    (∃ v ∈ V.restrictScalars k ⊓ k.vectorSubmodule n, v ≠ 0) ↔
      ∀ α, ∃ v ∈ V.restrictScalars (Kα α) ⊓ (Kα α).vectorSubmodule n, v ≠ 0 := by
  classical
  constructor
  · intro hv α
    -- Descend from the intersection field `k` to each family member by monotonicity.
    obtain ⟨v, hv, hv_ne⟩ := hv
    have hk_le : k ≤ Kα α := by
      intro x hx
      have hx' : x ∈ ⨅ β, Kα β := by
        simpa [h_inter] using hx
      exact (Subfield.mem_iInf.1 hx') α
    refine ⟨v, ?_, hv_ne⟩
    constructor
    · exact hv.1
    · exact Subfield.mem_vectorSubmodule_of_le hk_le hv.2
  · intro hfamily
    -- Prove the reverse implication by induction on the length of the coordinate vector.
    have hreverse :
        ∀ {m : ℕ} (W : Submodule K (Fin m → K)),
          (∀ α, ∃ v ∈ W.restrictScalars (Kα α) ⊓ (Kα α).vectorSubmodule m, v ≠ 0) →
            ∃ v ∈ W.restrictScalars k ⊓ k.vectorSubmodule m, v ≠ 0 := by
      intro m
      induction m with
      | zero =>
          intro W hW
          let α0 : A := Classical.choice ‹Nonempty A›
          obtain ⟨v, hv, hv_ne⟩ := hW α0
          have hv_zero : v = 0 := by
            ext i
            exact Fin.elim0 i
          exact False.elim (hv_ne hv_zero)
      | succ m ih =>
          intro W hW
          by_cases h_tail :
              ∀ α, ∃ t ∈ (W.comap (cons_zero_linear m)).restrictScalars (Kα α) ⊓
                  (Kα α).vectorSubmodule m, t ≠ 0
          · -- If every family member has a nonzero tail vector, apply the induction hypothesis.
            obtain ⟨t, ht, ht_ne⟩ := ih (W.comap (cons_zero_linear m)) h_tail
            refine ⟨cons_zero_fun t, ?_, ?_⟩
            · exact cons_zero_mem_of_tail W ht
            · intro hzero
              apply ht_ne
              ext i
              have hi := congrArg (fun f : Fin (m + 1) → K ↦ f i.succ) hzero
              simpa [cons_zero_fun] using hi
          · -- Otherwise choose a family member with trivial tail intersection and normalize there.
            obtain ⟨α0, hα0⟩ := not_forall.1 h_tail
            obtain ⟨v0, hv0, hv0_ne⟩ := hW α0
            have hv0_head : v0 0 ≠ 0 := by
              intro hv0_head_zero
              have hv0_zero :=
                eq_zero_of_head_zero_of_no_tail_vector (L := Kα α0) W hα0 hv0 hv0_head_zero
              exact hv0_ne hv0_zero
            obtain ⟨u, hu, hu0⟩ := exists_normalized_vector W hv0 hv0_head
            have hu_family : ∀ β, u ∈ (Kα β).vectorSubmodule (m + 1) := by
              intro β
              -- Directedness supplies a smaller field where both normalized vectors agree.
              obtain ⟨γ, hαγ, hβγ⟩ := h_directed α0 β
              have hγ_no_tail :
                  ¬ ∃ t ∈ (W.comap (cons_zero_linear m)).restrictScalars (Kα γ) ⊓
                      (Kα γ).vectorSubmodule m, t ≠ 0 := by
                intro ht
                rcases ht with ⟨t, ht, ht_ne⟩
                apply hα0
                refine ⟨t, ?_, ht_ne⟩
                constructor
                · exact ht.1
                · exact Subfield.mem_vectorSubmodule_of_le hαγ ht.2
              obtain ⟨vγ, hvγ, hvγ_ne⟩ := hW γ
              have hvγ_head : vγ 0 ≠ 0 := by
                intro hvγ_head_zero
                have hvγ_zero :=
                  eq_zero_of_head_zero_of_no_tail_vector (L := Kα γ) W hγ_no_tail hvγ
                    hvγ_head_zero
                exact hvγ_ne hvγ_zero
              obtain ⟨wγ, hwγ, hwγ0⟩ := exists_normalized_vector W hvγ hvγ_head
              have hwγα0 : wγ ∈ W.restrictScalars (Kα α0) ⊓ (Kα α0).vectorSubmodule (m + 1) := by
                constructor
                · exact hwγ.1
                · exact Subfield.mem_vectorSubmodule_of_le hαγ hwγ.2
              have hwγ_eq_u : wγ = u := by
                exact eq_of_head_one_of_no_tail_vector (L := Kα α0) W hα0 hwγα0 hu hwγ0 hu0
              have hwγβ : wγ ∈ (Kα β).vectorSubmodule (m + 1) := by
                exact Subfield.mem_vectorSubmodule_of_le hβγ hwγ.2
              simpa [hwγ_eq_u] using hwγβ
            have hu_base : u ∈ k.vectorSubmodule (m + 1) := by
              exact mem_base_vectorSubmodule_of_mem_all_family k Kα h_inter hu_family
            have hu_ne : u ≠ 0 := by
              intro hu_zero
              have hu_head_zero : u 0 = 0 := by
                simpa [hu_zero]
              simpa [hu0] using hu_head_zero
            refine ⟨u, ?_, hu_ne⟩
            constructor
            · exact hu.1
            · exact hu_base
    exact hreverse V hfamily

end
