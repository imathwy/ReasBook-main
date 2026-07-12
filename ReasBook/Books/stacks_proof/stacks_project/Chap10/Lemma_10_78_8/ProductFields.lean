import Mathlib

universe u v w

section

/-- Helper for Lemma 10.78.8: the product-fields model splits into its head coordinate and tail. -/
theorem prod_fields_head_tail_left_inv
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ}
    (y : ∀ i, Fin (n + 1) → K i) :
    (fun i ↦ Fin.cons (y i 0) (Fin.tail (y i))) = y := by
  -- Reassembling the head and tail of a tuple gives back the original tuple.
  funext i
  exact Fin.cons_self_tail (y i)

/-- Helper for Lemma 10.78.8: the head coordinate of a recombined head-tail pair is unchanged. -/
theorem prod_fields_head_tail_head
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ}
    (p : ((∀ i, K i) × (∀ i, Fin n → K i))) :
    ((fun i ↦ ((Fin.cons (p.1 i) (p.2 i) : Fin (n + 1) → K i) 0) : ∀ i, K i)) = p.1 := by
  -- Recombining a pair preserves its head entry.
  funext i
  simp

/-- Helper for Lemma 10.78.8: the tail coordinates of a recombined head-tail pair are unchanged. -/
theorem prod_fields_head_tail_tail
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ}
    (p : ((∀ i, K i) × (∀ i, Fin n → K i))) :
    ((fun i j ↦ (Fin.tail (Fin.cons (p.1 i) (p.2 i) : Fin (n + 1) → K i)) j : ∀ i, Fin n → K i))
      = p.2 := by
  -- Recombining a pair also preserves its tail coordinates.
  funext i j
  simp

/-- Helper for Lemma 10.78.8: the head-tail split preserves addition. -/
theorem prod_fields_head_tail_map_add
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ}
    (y z : ∀ i, Fin (n + 1) → K i) :
    (fun i ↦ (y + z) i 0, fun i ↦ Fin.tail ((y + z) i)) =
      (fun i ↦ y i 0, fun i ↦ Fin.tail (y i)) + (fun i ↦ z i 0, fun i ↦ Fin.tail (z i)) := by
  -- Both head and tail are computed coordinatewise.
  ext i
  · rfl
  · rfl

/-- Helper for Lemma 10.78.8: the head-tail split preserves scalar multiplication. -/
theorem prod_fields_head_tail_map_smul
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ}
    (a : ∀ i, K i) (y : ∀ i, Fin (n + 1) → K i) :
    (fun i ↦ (a • y) i 0, fun i ↦ Fin.tail ((a • y) i)) =
      a • (fun i ↦ y i 0, fun i ↦ Fin.tail (y i)) := by
  -- Scalar multiplication is also coordinatewise in the product-fields model.
  ext i
  · rfl
  · rfl

/-- Helper for Lemma 10.78.8: the product-fields model splits into its head coordinate and tail. -/
def prod_fields_head_tail_linear_equiv
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ} :
    (∀ i, Fin (n + 1) → K i) ≃ₗ[(∀ i, K i)] ((∀ i, K i) × (∀ i, Fin n → K i)) :=
  { toFun := fun y => (fun i ↦ y i 0, fun i ↦ Fin.tail (y i))
    invFun := fun p i ↦ Fin.cons (p.1 i) (p.2 i)
    left_inv := prod_fields_head_tail_left_inv
    right_inv := fun p => Prod.ext (prod_fields_head_tail_head p) (prod_fields_head_tail_tail p)
    map_add' := prod_fields_head_tail_map_add
    map_smul' := prod_fields_head_tail_map_smul }

/-- Helper for Lemma 10.78.8: the head-tail normalization map on `K × K^n` is inverse to the
stated reconstruction map on the left. -/
theorem prod_field_head_tail_normalize_left_inv
    {K : Type w} [Field K] {n : ℕ}
    (a : K) (ha : a ≠ 0) (w : Fin n → K) :
    Function.LeftInverse
      (fun p : K × (Fin n → K) ↦ (a⁻¹ * p.1, p.2 - (a⁻¹ * p.1) • w))
      (fun p : K × (Fin n → K) ↦ (a * p.1, p.2 + p.1 • w)) := by
  -- After rescaling the head and subtracting the transported tail, both coordinates recover.
  intro p
  ext
  · simp [mul_assoc, ha]
  · simp [mul_assoc, ha]

/-- Helper for Lemma 10.78.8: the head-tail normalization map on `K × K^n` is inverse to the
stated reconstruction map on the right. -/
theorem prod_field_head_tail_normalize_right_inv
    {K : Type w} [Field K] {n : ℕ}
    (a : K) (ha : a ≠ 0) (w : Fin n → K) :
    Function.RightInverse
      (fun p : K × (Fin n → K) ↦ (a⁻¹ * p.1, p.2 - (a⁻¹ * p.1) • w))
      (fun p : K × (Fin n → K) ↦ (a * p.1, p.2 + p.1 • w)) := by
  -- The same triangular algebra also shows the other composite is the identity.
  intro p
  ext
  · simp [mul_assoc, ha]
  · simp [mul_assoc, ha]

/-- Helper for Lemma 10.78.8: the head-tail normalization map is additive. -/
theorem prod_field_head_tail_normalize_map_add
    {K : Type w} [Field K] {n : ℕ}
    (a : K) (ha : a ≠ 0) (w : Fin n → K) :
    ∀ p q : K × (Fin n → K),
      (a⁻¹ * (p + q).1, (p + q).2 - (a⁻¹ * (p + q).1) • w) =
        (a⁻¹ * p.1, p.2 - (a⁻¹ * p.1) • w) +
          (a⁻¹ * q.1, q.2 - (a⁻¹ * q.1) • w) := by
  -- Everything is computed coordinatewise, and distributivity handles the tail correction.
  intro p q
  ext
  · simp [mul_add]
  · simp [sub_eq_add_neg, add_smul, mul_add, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 10.78.8: the head-tail normalization map respects scalar multiplication. -/
theorem prod_field_head_tail_normalize_map_smul
    {K : Type w} [Field K] {n : ℕ}
    (a : K) (ha : a ≠ 0) (w : Fin n → K) :
    ∀ (c : K) (p : K × (Fin n → K)),
      (a⁻¹ * (c • p).1, (c • p).2 - (a⁻¹ * (c • p).1) • w) =
        c • (a⁻¹ * p.1, p.2 - (a⁻¹ * p.1) • w) := by
  -- Commutativity of the field lets the scalar pass through the head rescaling.
  intro c p
  ext
  · simp [mul_assoc, mul_left_comm, mul_comm]
  · simp [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 10.78.8: once the head coordinate is nonzero, a triangular head-tail
automorphism rescales it to `1` and kills the tail. -/
def prod_field_head_tail_normalize_linear_equiv
    {K : Type w} [Field K] {n : ℕ}
    (a : K) (ha : a ≠ 0) (w : Fin n → K) :
    (K × (Fin n → K)) ≃ₗ[K] (K × (Fin n → K)) :=
  { toFun := fun p ↦ (a⁻¹ * p.1, p.2 - (a⁻¹ * p.1) • w)
    invFun := fun p ↦ (a * p.1, p.2 + p.1 • w)
    left_inv := prod_field_head_tail_normalize_right_inv a ha w
    right_inv := prod_field_head_tail_normalize_left_inv a ha w
    map_add' := prod_field_head_tail_normalize_map_add a ha w
    map_smul' := prod_field_head_tail_normalize_map_smul a ha w }

/-- Helper for Lemma 10.78.8: over one field, a nonzero vector in `K^(n + 1)` can be normalized to
the standard head vector by a linear automorphism. -/
theorem prod_field_linear_equiv_send_nonzero_to_head
    {K : Type w} [Field K] {n : ℕ}
    (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    ∃ e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K), e v = Fin.cons 1 0 := by
  classical
  let s : Set (Fin (n + 1) → K) := {v}
  have hs : LinearIndepOn K id s := by
    -- Proof comment: a singleton is linearly independent exactly when its element is nonzero.
    simpa [s] using (linearIndepOn_singleton_iff (R := K) (v := id) (i := v)).2 hv
  let b : Module.Basis (hs.extend (Set.subset_univ s)) K (Fin (n + 1) → K) :=
    Module.Basis.extend hs
  let i0 : hs.extend (Set.subset_univ s) :=
    ⟨v, hs.subset_extend (Set.subset_univ s) (by simp [s])⟩
  letI : Fintype (hs.extend (Set.subset_univ s)) := Fintype.ofFinite (hs.extend (Set.subset_univ s))
  have hcard : Fintype.card (hs.extend (Set.subset_univ s)) = n + 1 := by
    -- Proof comment: any basis of `K^(n + 1)` has exactly `n + 1` vectors.
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e0 : hs.extend (Set.subset_univ s) ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hcard
  let eidx : hs.extend (Set.subset_univ s) ≃ Fin (n + 1) :=
    e0.trans (Equiv.swap (e0 i0) 0)
  let c : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K) := b.reindex eidx
  have heidx_zero : eidx i0 = 0 := by
    -- Proof comment: the final swap reindexes the distinguished basis vector to the head.
    simp [eidx]
  have heidx_symm_zero : eidx.symm 0 = i0 := by
    exact eidx.symm_apply_eq.mpr heidx_zero.symm
  have hc_zero : c 0 = v := by
    -- Proof comment: after reindexing, the `0`th basis vector is exactly the original `v`.
    calc
      c 0 = b (eidx.symm 0) := by simp [c]
      _ = b i0 := by rw [heidx_symm_zero]
      _ = v := by
        simpa [b, i0] using Module.Basis.extend_apply_self hs i0
  refine ⟨c.equiv (Pi.basisFun K (Fin (n + 1))) (Equiv.refl _), ?_⟩
  -- Proof comment: the linear equivalence sending the reindexed basis `c` to the standard basis
  -- sends the distinguished vector `v = c 0` to the standard head vector.
  calc
    c.equiv (Pi.basisFun K (Fin (n + 1))) (Equiv.refl _) v
        = c.equiv (Pi.basisFun K (Fin (n + 1))) (Equiv.refl _) (c 0) := by rw [hc_zero]
    _ = Pi.basisFun K (Fin (n + 1)) 0 := by simp
    _ = Fin.cons 1 0 := by
      funext i
      rw [Pi.basisFun_apply]
      cases' Fin.eq_zero_or_eq_succ i with hi hi
      · subst hi
        simp
      · rcases hi with ⟨j, rfl⟩
        simp

/-- Helper for Lemma 10.78.8: a vector whose image in each field factor is nonzero can be
normalized simultaneously to the standard head vector by a product-linear automorphism. -/
def prod_fields_componentwise_linear_equiv
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ}
    (e : ∀ i, (Fin (n + 1) → K i) ≃ₗ[K i] (Fin (n + 1) → K i)) :
    (∀ i, Fin (n + 1) → K i) ≃ₗ[(∀ i, K i)] (∀ i, Fin (n + 1) → K i) :=
  { toFun := fun z i ↦ e i (z i)
    invFun := fun z i ↦ (e i).symm (z i)
    left_inv := by
      intro z
      funext i
      exact (e i).left_inv (z i)
    right_inv := by
      intro z
      funext i
      exact (e i).right_inv (z i)
    map_add' := by
      intro z z'
      funext i
      exact map_add (e i) (z i) (z' i)
    map_smul' := by
      intro a z
      funext i
      exact map_smul (e i) (a i) (z i) }

/-- Helper for Lemma 10.78.8: a vector whose image in each field factor is nonzero can be
normalized simultaneously to the standard head vector by a product-linear automorphism. -/
theorem prod_fields_normalize_nonzero_vector
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ}
    (y : ∀ i, Fin (n + 1) → K i) (hy : ∀ i, y i ≠ 0) :
    ∃ e : (∀ i, Fin (n + 1) → K i) ≃ₗ[(∀ i, K i)] (∀ i, Fin (n + 1) → K i),
      e y = fun i ↦ Fin.cons 1 0 := by
  classical
  choose e he using fun i ↦
    prod_field_linear_equiv_send_nonzero_to_head (K := K i) (n := n) (y i) (hy i)
  refine ⟨prod_fields_componentwise_linear_equiv (K := K) (n := n) e, ?_⟩
  -- Proof comment: the product automorphism acts componentwise, so it sends `y` to the family of
  -- standard head vectors exactly when each factorwise automorphism does.
  funext i
  simpa [prod_fields_componentwise_linear_equiv] using he i

/-- Helper for Lemma 10.78.8: if the image of `N` spans the product-fields model over the product
ring, then each field-valued factor projection already spans its full factor. -/
theorem factor_span_eq_top_of_span_eq_top_prod_fields
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)]
    {n : ℕ}
    (N : Submodule k (∀ i, Fin n → K i))
    (hN : Submodule.span (∀ i, K i) (N : Set (∀ i, Fin n → K i)) = ⊤) :
    ∀ i, Submodule.span (K i) ((fun y : (∀ i, Fin n → K i) ↦ y i) '' (N : Set _)) = ⊤ := by
  classical
  intro i
  let evali : (∀ j, K j) →+* K i := Pi.evalRingHom (fun j ↦ K j) i
  letI : RingHomSurjective evali := by
    refine ⟨?_⟩
    intro x
    refine ⟨Pi.single i x, ?_⟩
    simp [evali]
  let proji : (∀ j, Fin n → K j) →ₛₗ[evali] (Fin n → K i) :=
    { toFun := fun y ↦ y i
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine top_unique ?_
  intro x hx
  have hsingle :
      Pi.single i x ∈ Submodule.span (∀ j, K j) (N : Set (∀ j, Fin n → K j)) := by
    rw [hN]
    exact Submodule.mem_top
  have hxspan :
      proji (Pi.single i x) ∈ Submodule.span (K i) (proji '' (N : Set (∀ j, Fin n → K j))) :=
    Submodule.apply_mem_span_image_of_mem_span proji hsingle
  simpa [proji] using hxspan

/-- Helper for Lemma 10.78.8: if the `i`-th factor projection of a `k`-subspace spans the whole
`i`-th field-vector-space factor, then some element of the subspace has nonzero `i`-th component. -/
theorem exists_mem_nonzero_at_factor_of_factor_span_eq_top_prod_fields
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)]
    {n : ℕ}
    (N : Submodule k (∀ i, Fin (n + 1) → K i))
    (hN : ∀ i, Submodule.span (K i) ((fun y : (∀ i, Fin (n + 1) → K i) ↦ y i) '' (N : Set _)) = ⊤)
    (i : ι) :
    ∃ y ∈ N, y i ≠ 0 := by
  by_contra h
  push Not at h
  have hspan_eq_bot :
      Submodule.span (K i) ((fun y : (∀ i, Fin (n + 1) → K i) ↦ y i) '' (N : Set _)) = ⊥ := by
    -- If every projected vector is zero, then the projected span is zero.
    refine le_antisymm ?_ bot_le
    rw [Submodule.span_le]
    rintro _ ⟨y, hyN, rfl⟩
    exact h y hyN
  have htop_eq_bot : (⊤ : Submodule (K i) (Fin (n + 1) → K i)) = ⊥ := by
    simpa [hN i] using hspan_eq_bot
  exact top_ne_bot htop_eq_bot

/-- Helper for Lemma 10.78.8: over a finite product of fields, if each factor projection of a
`k`-subspace spans the whole factor, then one vector is nonzero in every factor. -/
theorem exists_mem_nonzero_in_each_factor_of_factor_span_eq_top_prod_fields
    {k : Type u} [Field k] [Infinite k]
    {ι : Type v} {K : ι → Type w}
    [Fintype ι] [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)]
    {n : ℕ}
    (N : Submodule k (∀ i, Fin (n + 1) → K i))
    (hN : ∀ i, Submodule.span (K i) ((fun y : (∀ i, Fin (n + 1) → K i) ↦ y i) '' (N : Set _)) = ⊤) :
    ∃ y ∈ N, ∀ i, y i ≠ 0 := by
  classical
  let projₖ : (i : ι) → (∀ i, Fin (n + 1) → K i) →ₗ[k] (Fin (n + 1) → K i) := fun i ↦
    { toFun := fun y ↦ y i
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let p : ι → Submodule k N := fun i ↦
    LinearMap.ker ((projₖ i).comp N.subtype)
  have hp : ∀ i, p i ≠ ⊤ := by
    intro i hpi
    obtain ⟨y, hyN, hyi⟩ :=
      exists_mem_nonzero_at_factor_of_factor_span_eq_top_prod_fields N hN i
    have hyker : (⟨y, hyN⟩ : N) ∈ p i := by
      simpa [p, hpi]
    have : y i = 0 := by
      simpa [p] using hyker
    exact hyi this
  obtain ⟨y, hy⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨y, y.2, ?_⟩
  intro i hyi
  apply hy i
  -- Being zero in the `i`-th factor is exactly membership in the corresponding kernel.
  simpa [p, hyi]

end
