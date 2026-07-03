import Mathlib
import StacksProject_2024.Chap10.Lemma_10_15_4_Chinese_remainder
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open IsLocalRing

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)]
variable [CommRing S] [Algebra R S] [Finite (MaximalSpectrum S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Free S M] [Module.Finite S M]

open scoped TensorProduct

/-- Helper for Lemma 10.78.8: a spanning family in `N` with exactly `Module.finrank S M` vectors is
already a basis of `M`. -/
private theorem exists_basis_of_fin_generators_mem_submodule
    (N : Submodule R M)
    (v : Fin (Module.finrank S M) → M)
    (hvN : ∀ i, v i ∈ N)
    (hvspan : Submodule.span S (Set.range v) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank S M)) S M, ∀ i, b i ∈ N := by
  let b : Module.Basis (Fin (Module.finrank S M)) S M :=
    basisOfTopLeSpanOfCardEqFinrank (R := S) (M := M) v hvspan.ge (by simp)
  refine ⟨b, ?_⟩
  intro i
  simpa [b] using hvN i

/-- Helper for Lemma 10.78.8: once the Jacobson-quotient images of elements of `N` form a basis,
they can be lifted to a basis of `M` contained in `N`. -/
private theorem exists_basis_of_jacobson_quotient_basis_mem_submodule
    (N : Submodule R M)
    (b : Module.Basis (Fin (Module.finrank S M)) (S ⧸ Ring.jacobson S)
      (M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))))
    (hb : ∀ i,
      b i ∈ (Ring.jacobson S • (⊤ : Submodule S M)).mkQ '' (N : Set M)) :
    ∃ b' : Module.Basis (Fin (Module.finrank S M)) S M, ∀ i, b' i ∈ N := by
  classical
  let J : Ideal S := Ring.jacobson S
  let q : M →ₗ[S] M ⧸ (J • (⊤ : Submodule S M)) := (J • (⊤ : Submodule S M)).mkQ
  choose v hvN hvq using hb
  have hq : q ∘ v = b := by
    funext i
    exact hvq i
  -- The lifted family still spans after quotienting.
  have hspan_quotient : Submodule.span (S ⧸ J) (Set.range (q ∘ v)) = ⊤ := by
    simpa [hq] using b.span_eq
  -- Restrict scalars along `S → S ⧸ J` to compare with the `S`-linear quotient map.
  have hspan_quotient_S : Submodule.span S (Set.range (q ∘ v)) = ⊤ := by
    have hrestrict :
        (Submodule.span (S ⧸ J) (Set.range (q ∘ v))).restrictScalars S = ⊤ := by
      simpa [hspan_quotient]
    rw [Submodule.restrictScalars_span (R := S) (A := S ⧸ J) Ideal.Quotient.mk_surjective] at hrestrict
    exact hrestrict
  -- Route correction: instead of rebuilding the quotient map API, use the quotient span to show
  -- that the lifts span modulo `J`, and then apply the Jacobson-radical form of Nakayama.
  have hmap_top : Submodule.map q (Submodule.span S (Set.range v)) = ⊤ := by
    rw [Submodule.map_span]
    simpa [q, Set.range_comp] using hspan_quotient_S
  have hsup : Submodule.span S (Set.range v) ⊔ J • (⊤ : Submodule S M) = ⊤ := by
    rw [Submodule.map_mkQ_eq_top] at hmap_top
    simpa [sup_comm] using hmap_top
  have hvspan : Submodule.span S (Set.range v) = ⊤ := by
    exact eq_top_of_sup_eq_top_of_le_ring_jacobson J (Submodule.span S (Set.range v))
      (⊤ : Submodule S M) Module.Finite.fg_top hsup le_rfl
  exact exists_basis_of_fin_generators_mem_submodule N v hvN hvspan

/-- Helper for Lemma 10.78.8: if the Jacobson radical of a semilocal ring vanishes, then the ring
is canonically the product of its maximal residue fields. -/
private noncomputable def jacobson_quotient_ring_equiv_pi_maximal_quotients
    (A : Type v) [CommRing A] [Finite (MaximalSpectrum A)]
    (hjac : Ring.jacobson A = ⊥) :
    A ≃+* ∀ x : MaximalSpectrum A, A ⧸ x.asIdeal := by
  classical
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite (MaximalSpectrum A)
  let I : MaximalSpectrum A → Ideal A := fun x ↦ x.asIdeal
  have hI : Pairwise fun x y => IsCoprime (I x) (I y) := by
    -- Distinct maximal ideals are comaximal, so the Chinese remainder theorem applies.
    intro x y hxy
    simpa [I] using Ideal.isCoprime_of_isMaximal (MaximalSpectrum.ext_iff.ne.mp hxy)
  have hiInf : (⨅ x : MaximalSpectrum A, x.asIdeal) = Ring.jacobson A := by
    rw [Ring.jacobson_eq_sInf_isMaximal]
    simpa using
      (show sInf (Set.range (fun x : MaximalSpectrum A ↦ x.asIdeal)) =
          sInf {I : Ideal A | I.IsMaximal} by
        rw [MaximalSpectrum.range_asIdeal])
  have hprod : ∏ x, I x = ⊥ := by
    -- For finitely many maximal ideals, the product agrees with the infimum, hence with `jacobson`.
    calc
      ∏ x, I x = ⨅ x, I x := chinese_remainder_prod_eq_iInf I hI
      _ = Ring.jacobson A := by
        simpa [I] using hiInf
      _ = ⊥ := hjac
  -- Identify `A` with the quotient by the product ideal and then apply the Chinese remainder map.
  exact (RingEquiv.quotientBot A).symm.trans <|
    (Ideal.quotEquivOfEq hprod.symm).trans (chinese_remainder_quotient_pi_ring_equiv I hI)

/-- Helper for Lemma 10.78.8: the product-fields model splits into its head coordinate and tail. -/
private theorem prod_fields_head_tail_left_inv
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ}
    (y : ∀ i, Fin (n + 1) → K i) :
    (fun i ↦ Fin.cons (y i 0) (Fin.tail (y i))) = y := by
  -- Reassembling the head and tail of a tuple gives back the original tuple.
  funext i
  exact Fin.cons_self_tail (y i)

/-- Helper for Lemma 10.78.8: the head coordinate of a recombined head-tail pair is unchanged. -/
private theorem prod_fields_head_tail_head
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ}
    (p : ((∀ i, K i) × (∀ i, Fin n → K i))) :
    ((fun i ↦ ((Fin.cons (p.1 i) (p.2 i) : Fin (n + 1) → K i) 0) : ∀ i, K i)) = p.1 := by
  -- Recombining a pair preserves its head entry.
  funext i
  simp

/-- Helper for Lemma 10.78.8: the tail coordinates of a recombined head-tail pair are unchanged. -/
private theorem prod_fields_head_tail_tail
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] {n : ℕ}
    (p : ((∀ i, K i) × (∀ i, Fin n → K i))) :
    ((fun i j ↦ (Fin.tail (Fin.cons (p.1 i) (p.2 i) : Fin (n + 1) → K i)) j : ∀ i, Fin n → K i))
      = p.2 := by
  -- Recombining a pair also preserves its tail coordinates.
  funext i j
  simp

/-- Helper for Lemma 10.78.8: the head-tail split preserves addition. -/
private theorem prod_fields_head_tail_map_add
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
private theorem prod_fields_head_tail_map_smul
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
private def prod_fields_head_tail_linear_equiv
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
private theorem prod_field_head_tail_normalize_left_inv
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
private theorem prod_field_head_tail_normalize_right_inv
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
private theorem prod_field_head_tail_normalize_map_add
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
private theorem prod_field_head_tail_normalize_map_smul
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
private def prod_field_head_tail_normalize_linear_equiv
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
private theorem prod_field_linear_equiv_send_nonzero_to_head
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
private def prod_fields_componentwise_linear_equiv
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
private theorem prod_fields_normalize_nonzero_vector
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
private theorem factor_span_eq_top_of_span_eq_top_prod_fields
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
private theorem exists_mem_nonzero_at_factor_of_factor_span_eq_top_prod_fields
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
private theorem exists_mem_nonzero_in_each_factor_of_factor_span_eq_top_prod_fields
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

/-- Helper for Lemma 10.78.8: if `N` spans `M`, then its image still spans the Jacobson quotient of
`M`. This is the first reduction step in the source proof. -/
private theorem jacobson_quotient_span_eq_top_of_span_eq_top
    (N : Submodule R M)
    (hN : Submodule.span S (N : Set M) = ⊤) :
    Submodule.span (S ⧸ Ring.jacobson S)
      ((Ring.jacobson S • (⊤ : Submodule S M)).mkQ '' (N : Set M)) = ⊤ := by
  let J : Ideal S := Ring.jacobson S
  let q : M →ₗ[S] M ⧸ (J • (⊤ : Submodule S M)) := (J • (⊤ : Submodule S M)).mkQ
  have hspan_S :
      Submodule.span S (q '' (N : Set M)) = ⊤ := by
    -- Push the spanning hypothesis through the quotient map over `S`.
    calc
      Submodule.span S (q '' (N : Set M)) = Submodule.map q (Submodule.span S (N : Set M)) := by
        rw [Submodule.map_span]
      _ = ⊤ := by
        rw [hN, Submodule.map_top]
        exact LinearMap.range_eq_top.2 (Submodule.mkQ_surjective _)
  have hrestrict :
      (Submodule.span (S ⧸ J) (q '' (N : Set M))).restrictScalars S = ⊤ := by
    -- Then compare the quotient-ring span with the restricted `S`-span.
    rw [Submodule.restrictScalars_span (R := S) (A := S ⧸ J) Ideal.Quotient.mk_surjective]
    simpa using hspan_S
  rw [Submodule.restrictScalars_eq_top_iff] at hrestrict
  simpa [J, q] using hrestrict

/-- Helper for Lemma 10.78.8: the Jacobson-quotient image of `N` is the range of the descended
`R`-linear map from `N` into the quotient module. -/
private abbrev jacobson_quotient_submodule_map
    (N : Submodule R M) :
    N →ₗ[R] M ⧸ (Ring.jacobson S • (⊤ : Submodule S M)) :=
  (((Ring.jacobson S • (⊤ : Submodule S M)).mkQ).restrictScalars R).comp N.subtype

/-- Helper for Lemma 10.78.8: package the raw Jacobson-quotient image of `N` as an honest
`R`-submodule before transporting it to product coordinates. -/
private abbrev jacobson_quotient_image_submodule
    (N : Submodule R M) :
    Submodule R (M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))) :=
  LinearMap.range (jacobson_quotient_submodule_map (R := R) (S := S) (M := M) N)

/-- Helper for Lemma 10.78.8: membership in the packaged Jacobson-quotient image is equivalent to
coming from a literal element of `N`. -/
private theorem mem_jacobson_quotient_image_submodule_iff
    (N : Submodule R M)
    (x : M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))) :
    x ∈ jacobson_quotient_image_submodule (R := R) (S := S) (M := M) N ↔
      ∃ n : N, (Ring.jacobson S • (⊤ : Submodule S M)).mkQ (n : M) = x := by
  -- Unfold the range description and read it as existence of a lift in `N`.
  change x ∈ LinearMap.range (jacobson_quotient_submodule_map (R := R) (S := S) (M := M) N) ↔
      ∃ n : N, (Ring.jacobson S • (⊤ : Submodule S M)).mkQ (n : M) = x
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [jacobson_quotient_submodule_map] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [jacobson_quotient_submodule_map] using hn

/-- Helper for Lemma 10.78.8: the packaged Jacobson-quotient image submodule still spans the whole
quotient over `S ⧸ Ring.jacobson S`. -/
private theorem jacobson_quotient_image_submodule_span_eq_top
    (N : Submodule R M)
    (hN : Submodule.span S (N : Set M) = ⊤) :
    Submodule.span (S ⧸ Ring.jacobson S)
      (jacobson_quotient_image_submodule (R := R) (S := S) (M := M) N : Set
        (M ⧸ (Ring.jacobson S • (⊤ : Submodule S M)))) = ⊤ := by
  have hraw :
      Submodule.span (S ⧸ Ring.jacobson S)
        ((Ring.jacobson S • (⊤ : Submodule S M)).mkQ '' (N : Set M)) = ⊤ := by
    -- First use the existing Jacobson-quotient span statement for the raw image set.
    simpa using jacobson_quotient_span_eq_top_of_span_eq_top (R := R) (S := S) (M := M) N hN
  have hset :
      (jacobson_quotient_image_submodule (R := R) (S := S) (M := M) N : Set
        (M ⧸ (Ring.jacobson S • (⊤ : Submodule S M)))) =
        (Ring.jacobson S • (⊤ : Submodule S M)).mkQ '' (N : Set M) := by
    -- The range description and the raw image description have the same elements.
    ext x
    constructor
    · intro hx
      rcases (mem_jacobson_quotient_image_submodule_iff
          (R := R) (S := S) (M := M) N x).1 hx with ⟨n, hn⟩
      exact ⟨n, n.2, hn⟩
    · rintro ⟨m, hm, hmq⟩
      exact (mem_jacobson_quotient_image_submodule_iff
        (R := R) (S := S) (M := M) N _).2 ⟨⟨m, hm⟩, hmq⟩
  rw [hset]
  exact hraw

/-- Helper for Lemma 10.78.8: after normalizing the chosen vector to the standard head vector,
the quotient by the rank-one summand `Sy` is modeled by the tail projection, whose image still
spans the full tail space. -/
private theorem tail_span_eq_top_of_head_mem_and_span_eq_top_prod_fields
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] {n : ℕ}
    (Npi : Submodule k (∀ i, Fin (n + 1) → K i))
    (hspan : Submodule.span (∀ i, K i) (Npi : Set (∀ i, Fin (n + 1) → K i)) = ⊤)
    (hhead : (fun i ↦ Fin.cons 1 0 : ∀ i, Fin (n + 1) → K i) ∈ Npi) :
    let tailMap :
        (∀ i, Fin (n + 1) → K i) →ₗ[(∀ i, K i)] (∀ i, Fin n → K i) :=
      (LinearMap.snd (∀ i, K i) (∀ i, K i) (∀ i, Fin n → K i)).comp
        (prod_fields_head_tail_linear_equiv (ι := ι) (K := K) (n := n)).toLinearMap
    Submodule.span (∀ i, K i) (tailMap '' (Npi : Set (∀ i, Fin (n + 1) → K i))) = ⊤ := by
  intro tailMap
  refine top_unique ?_
  intro x hx
  let y : ∀ i, Fin (n + 1) → K i :=
    (prod_fields_head_tail_linear_equiv (ι := ι) (K := K) (n := n)).symm (0, x)
  have hy_span : y ∈ Submodule.span (∀ i, K i) (Npi : Set (∀ i, Fin (n + 1) → K i)) := by
    rw [hspan]
    exact Submodule.mem_top
  have hx_span :
      tailMap y ∈ Submodule.span (∀ i, K i) (tailMap '' (Npi : Set (∀ i, Fin (n + 1) → K i))) :=
    Submodule.apply_mem_span_image_of_mem_span tailMap hy_span
  -- The split equivalence sends `(0, x)` back to a vector with tail exactly `x`.
  simpa [tailMap, y]
    using hx_span

/-- Helper for Lemma 10.78.8: the source induction recurses on the tail quotient as an honest
mapped `k`-submodule rather than on a raw set image. -/
private theorem tail_map_submodule_span_eq_top_of_head_mem_prod_fields
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] {n : ℕ}
    (Npi : Submodule k (∀ i, Fin (n + 1) → K i))
    (hspan : Submodule.span (∀ i, K i) (Npi : Set (∀ i, Fin (n + 1) → K i)) = ⊤)
    (hhead : (fun i ↦ Fin.cons 1 0 : ∀ i, Fin (n + 1) → K i) ∈ Npi) :
    let tailMap :
        (∀ i, Fin (n + 1) → K i) →ₗ[(∀ i, K i)] (∀ i, Fin n → K i) :=
      (LinearMap.snd (∀ i, K i) (∀ i, K i) (∀ i, Fin n → K i)).comp
        (prod_fields_head_tail_linear_equiv (ι := ι) (K := K) (n := n)).toLinearMap
    Submodule.span (∀ i, K i) (tailMap '' (Npi : Set (∀ i, Fin (n + 1) → K i))) = ⊤ := by
  exact tail_span_eq_top_of_head_mem_and_span_eq_top_prod_fields
    (k := k) (ι := ι) (K := K) (n := n) Npi hspan hhead

/-- Helper for Lemma 10.78.8: the triangular shear on a head-tail product module is inverted by
subtracting the same head correction. -/
private theorem head_tail_shear_left_inv
    {A : Type u} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    (φ : V →ₗ[A] A) :
    Function.LeftInverse
      (fun p : A × V ↦ (p.1 + φ p.2, p.2))
      (fun p : A × V ↦ (p.1 - φ p.2, p.2)) := by
  -- The head correction cancels, while the tail coordinate is unchanged.
  intro p
  ext
  · simp [sub_eq_add_neg, add_assoc]
  · rfl

/-- Helper for Lemma 10.78.8: the triangular shear on a head-tail product module is inverted by
adding back the same head correction. -/
private theorem head_tail_shear_right_inv
    {A : Type u} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    (φ : V →ₗ[A] A) :
    Function.RightInverse
      (fun p : A × V ↦ (p.1 + φ p.2, p.2))
      (fun p : A × V ↦ (p.1 - φ p.2, p.2)) := by
  -- The same cancellation works for the other composite.
  intro p
  ext
  · simp [sub_eq_add_neg, add_assoc]
  · rfl

/-- Helper for Lemma 10.78.8: the triangular shear is additive. -/
private theorem head_tail_shear_map_add
    {A : Type u} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    (φ : V →ₗ[A] A) :
    ∀ p q : A × V,
      (p + q).1 + φ (p + q).2 = (p.1 + φ p.2) + (q.1 + φ q.2) := by
  -- The shear only uses the linear functional `φ`, so distributivity is enough.
  intro p q
  simp [map_add, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 10.78.8: the triangular shear respects scalar multiplication. -/
private theorem head_tail_shear_map_smul
    {A : Type u} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    (φ : V →ₗ[A] A) :
    ∀ (a : A) (p : A × V),
      a • p.1 + φ (a • p.2) = a • (p.1 + φ p.2) := by
  -- The linearity of `φ` lets the head correction factor through the scalar.
  intro a p
  rw [map_smul]
  simp [left_distrib]

/-- Helper for Lemma 10.78.8: a linear functional on the tail defines a triangular shear on the
head-tail product module. -/
private def head_tail_shear_linear_equiv
    {A : Type u} [CommRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    (φ : V →ₗ[A] A) :
    (A × V) ≃ₗ[A] (A × V) :=
  { toFun := fun p ↦ (p.1 + φ p.2, p.2)
    invFun := fun p ↦ (p.1 - φ p.2, p.2)
    left_inv := head_tail_shear_right_inv φ
    right_inv := head_tail_shear_left_inv φ
    map_add' := by
      intro p q
      ext
      · exact head_tail_shear_map_add φ p q
      · rfl
    map_smul' := by
      intro a p
      ext
      · exact head_tail_shear_map_smul φ a p
      · rfl }

/-- Helper for Lemma 10.78.8: after choosing lifts of a tail basis, a shear in the head-tail
coordinates turns the standard product basis into a basis whose head vector is distinguished and
whose tail vectors are exactly the chosen lifts. -/
private theorem exists_sum_basis_of_head_and_tail_lifts_prod_fields
    {ι : Type v} {K : ι → Type w}
    [Fintype ι] [∀ i, Field (K i)] {n : ℕ}
    (btail : Module.Basis (Fin n) (∀ i, K i) (∀ i, Fin n → K i))
    (z : Fin n → ∀ i, Fin (n + 1) → K i)
    (hz :
      ∀ j,
        ((LinearMap.snd (∀ i, K i) (∀ i, K i) (∀ i, Fin n → K i)).comp
          (prod_fields_head_tail_linear_equiv (ι := ι) (K := K) (n := n)).toLinearMap) (z j) =
            btail j) :
    ∃ bsum : Module.Basis (Fin 1 ⊕ Fin n) (∀ i, K i) (∀ i, Fin (n + 1) → K i),
      (∀ i : Fin 1, bsum (Sum.inl i) = fun t ↦ Fin.cons 1 0) ∧
      ∀ j, bsum (Sum.inr j) = z j := by
  let A : Type _ := ∀ i, K i
  let V : Type _ := ∀ i, Fin n → K i
  let headTail := prod_fields_head_tail_linear_equiv (ι := ι) (K := K) (n := n)
  let bhead : Module.Basis (Fin 1) A A := Module.Basis.singleton (Fin 1) A
  let φ : V →ₗ[A] A := btail.constr A (fun j i ↦ (z j) i 0)
  let bprod : Module.Basis (Fin 1 ⊕ Fin n) A (A × V) := bhead.prod btail
  let bshear : Module.Basis (Fin 1 ⊕ Fin n) A (A × V) :=
    bprod.map (head_tail_shear_linear_equiv φ)
  let bsum : Module.Basis (Fin 1 ⊕ Fin n) A (∀ i, Fin (n + 1) → K i) :=
    bshear.map headTail.symm
  refine ⟨bsum, ?_, ?_⟩
  · intro i
    have hbprod :
        bprod (Sum.inl i) = (1, 0) := by
      ext t
      · simpa [bprod, bhead] using
          (Module.Basis.prod_apply_inl_fst (b := bhead) (b' := btail) i)
      · simpa [bprod] using
          (Module.Basis.prod_apply_inl_snd (b := bhead) (b' := btail) i)
    -- Proof comment: the shear fixes the standard head vector because its tail part is zero.
    calc
      bsum (Sum.inl i)
          = headTail.symm ((head_tail_shear_linear_equiv φ) (bprod (Sum.inl i))) := by
              simp [bsum, bshear, bprod, headTail]
      _ = headTail.symm (1, 0) := by simp [hbprod, head_tail_shear_linear_equiv, φ]
      _ = fun t ↦ Fin.cons 1 0 := by
            ext t j
            cases' Fin.eq_zero_or_eq_succ j with hj hj
            · subst hj
              simp [headTail, prod_fields_head_tail_linear_equiv]
            · rcases hj with ⟨j', rfl⟩
              simp [headTail, prod_fields_head_tail_linear_equiv]
  · intro j
    have hbprod :
        bprod (Sum.inr j) = (0, btail j) := by
      ext t
      · simpa [bprod] using
          (Module.Basis.prod_apply_inr_fst (b := bhead) (b' := btail) j)
      · simpa [bprod] using
          (Module.Basis.prod_apply_inr_snd (b := bhead) (b' := btail) j)
    have hφ :
        φ (btail j) = fun i ↦ (z j) i 0 := by
      -- Proof comment: `φ` was defined by prescribing these head coordinates on the tail basis.
      ext i
      simp [φ, Module.Basis.constr_apply]
    have hpair :
        (φ (btail j), btail j) = headTail (z j) := by
      refine Prod.ext hφ ?_
      -- Proof comment: the hypothesis `hz` says exactly that the tail of `z j` is `btail j`.
      simpa [headTail, prod_fields_head_tail_linear_equiv] using (hz j).symm
    -- Proof comment: the shear inserts the desired head coordinates, and `headTail.symm` then
    -- reconstructs the original lifted vector.
    calc
      bsum (Sum.inr j)
          = headTail.symm ((head_tail_shear_linear_equiv φ) (bprod (Sum.inr j))) := by
              simp [bsum, bshear, bprod, headTail]
      _ = headTail.symm (φ (btail j), btail j) := by
            simp [hbprod, head_tail_shear_linear_equiv]
      _ = headTail.symm (headTail (z j)) := by rw [hpair]
      _ = z j := by simp [headTail]

/-- Helper for Lemma 10.78.8: in the concrete product-of-fields coordinate model, a `k`-subspace
whose `A`-span is the whole ambient free `A`-module already contains an `A`-basis. -/
private theorem basis_pullback_mem_of_mem_map
    {k : Type u} {A : Type v} {V : Type w} {W : Type*} {ι : Type*}
    [Field k] [CommRing A]
    [AddCommGroup V] [Module A V] [Module k V]
    [AddCommGroup W] [Module A W]
    (N0 : Submodule k V)
    (e : V ≃ₗ[A] W)
    (b : Module.Basis ι A W)
    (hb : ∀ i, b i ∈ e '' (N0 : Set V)) :
    ∀ i, (b.map e.symm) i ∈ N0 := by
  intro i
  rcases hb i with ⟨x, hx, hxeq⟩
  -- Proof comment: once a basis vector is written literally as `e x` with `x ∈ N0`, pulling the
  -- basis back along `e.symm` recovers exactly that witness.
  have hpreimage : e.symm (b i) = x := by
    rw [← hxeq]
    simp
  rw [Module.Basis.map_apply, hpreimage]
  exact hx

/-- Helper for Lemma 10.78.8: an `A`-linear map between modules in a scalar tower is also
`k`-linear after forgetting from `A` to `k`. -/
private theorem linearMap_map_smul_of_tower
    {k : Type u} {A : Type v} {V : Type w} {W : Type*}
    [Field k] [CommRing A] [Algebra k A]
    [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]
    [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]
    (f : V →ₗ[A] W) (c : k) (x : V) :
    f (c • x) = c • f x := by
  -- Proof comment: the forgotten `k`-action is the `A`-action through `algebraMap k A`, so the
  -- original `A`-linearity of `f` already gives the desired `k`-linearity.
  simpa using f.map_smul (algebraMap k A c) x

/-- Helper for Lemma 10.78.8: forget scalars on an `A`-linear map along a scalar tower without
relying on `CompatibleSMul` typeclass search. -/
private def linearMap_restrictScalars_of_tower
    {k : Type u} {A : Type v} {V : Type w} {W : Type*}
    [Field k] [CommRing A] [Algebra k A]
    [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]
    [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]
    (f : V →ₗ[A] W) : V →ₗ[k] W :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := linearMap_map_smul_of_tower f }

/-- Helper for Lemma 10.78.8: forget scalars on an `A`-linear equivalence along a scalar tower
without relying on `CompatibleSMul` typeclass search. -/
private def linearEquiv_restrictScalars_of_tower
    {k : Type u} {A : Type v} {V : Type w} {W : Type*}
    [Field k] [CommRing A] [Algebra k A]
    [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]
    [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]
    (e : V ≃ₗ[A] W) : V ≃ₗ[k] W :=
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := linearMap_map_smul_of_tower e.toLinearMap }

/-- Helper for Lemma 10.78.8: componentwise scalar towers on the field factors induce the scalar
tower needed to restrict the product-coordinate maps from `∏ Kᵢ` to the residue field `k`. -/
private instance prod_fields_pi_isScalarTower
    {k : Type u} [Field k] {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] {n : ℕ} :
    IsScalarTower k (∀ i, K i) (∀ i, Fin n → K i) where
  smul_assoc a b x := by
    -- Proof comment: every scalar action is computed pointwise, so the tower law reduces to the
    -- corresponding componentwise tower law on each field factor.
    funext i j
    simp [smul_assoc]

/-- Helper for Lemma 10.78.8: forget scalars on the product-fields normalization equivalence so the
source induction can map `k`-submodules through the same underlying automorphism. -/
private def prod_fields_normalization_linearEquiv_to_residue_linear
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] {n : ℕ}
    (e : (∀ i, Fin (n + 1) → K i) ≃ₗ[(∀ i, K i)] (∀ i, Fin (n + 1) → K i)) :
    (∀ i, Fin (n + 1) → K i) ≃ₗ[k] (∀ i, Fin (n + 1) → K i) := sorry

/-- Helper for Lemma 10.78.8: the forgotten normalization equivalence has the same underlying
carrier map as the original product-ring linear equivalence. -/
private theorem prod_fields_normalization_linearEquiv_to_residue_linear_apply
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] {n : ℕ}
    (e : (∀ i, Fin (n + 1) → K i) ≃ₗ[(∀ i, K i)] (∀ i, Fin (n + 1) → K i))
    (x : ∀ i, Fin (n + 1) → K i) :
    prod_fields_normalization_linearEquiv_to_residue_linear
        (k := k) (ι := ι) (K := K) (n := n) e x =
      e x := by
  sorry

/-- Helper for Lemma 10.78.8: the inverse of the forgotten normalization equivalence has the same
underlying carrier map as the original inverse equivalence. -/
private theorem prod_fields_normalization_linearEquiv_to_residue_linear_symm_apply
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] {n : ℕ}
    (e : (∀ i, Fin (n + 1) → K i) ≃ₗ[(∀ i, K i)] (∀ i, Fin (n + 1) → K i))
    (x : ∀ i, Fin (n + 1) → K i) :
    (prod_fields_normalization_linearEquiv_to_residue_linear
        (k := k) (ι := ι) (K := K) (n := n) e).symm x =
      e.symm x := by
  sorry

/-- Helper for Lemma 10.78.8: forget scalars on the tail projection so the source induction can
recurse on the mapped `k`-submodule instead of a raw set image. -/
private def prod_fields_tail_projection_to_residue_linear
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] {n : ℕ}
    (tailMap : (∀ i, Fin (n + 1) → K i) →ₗ[(∀ i, K i)] (∀ i, Fin n → K i)) :
    (∀ i, Fin (n + 1) → K i) →ₗ[k] (∀ i, Fin n → K i) := sorry

/-- Helper for Lemma 10.78.8: the forgotten tail projection has the same carrier map as the
original product-ring linear tail projection. -/
private theorem prod_fields_tail_projection_to_residue_linear_apply
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] {n : ℕ}
    (tailMap : (∀ i, Fin (n + 1) → K i) →ₗ[(∀ i, K i)] (∀ i, Fin n → K i))
    (x : ∀ i, Fin (n + 1) → K i) :
    prod_fields_tail_projection_to_residue_linear
        (k := k) (ι := ι) (K := K) (n := n) tailMap x =
      tailMap x := by
  sorry

/-- Helper for Lemma 10.78.8: in the concrete product-of-fields coordinate model, a `k`-subspace
whose `A`-span is the whole ambient free `A`-module already contains an `A`-basis. -/
private theorem exists_basis_mem_submodule_of_span_eq_top_prod_fields_succ
    {k : Type u} [Field k] [Infinite k]
    {ι : Type v} {K : ι → Type w}
    [Fintype ι] [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)]
    (n : ℕ)
    (Npi : Submodule k (∀ i, Fin (n + 1) → K i))
    (ih :
      ∀ Ntail : Submodule k (∀ i, Fin n → K i),
        Submodule.span (∀ i, K i) (Ntail : Set (∀ i, Fin n → K i)) = ⊤ →
        ∃ b : Module.Basis (Fin n) (∀ i, K i) (∀ i, Fin n → K i), ∀ j, b j ∈ Ntail)
    (hspan : Submodule.span (∀ i, K i) (Npi : Set (∀ i, Fin (n + 1) → K i)) = ⊤) :
    ∃ b : Module.Basis (Fin (n + 1)) (∀ i, K i) (∀ i, Fin (n + 1) → K i), ∀ j, b j ∈ Npi := by
  -- TODO: finish the successor step by transporting `Npi` through the normalization equivalence,
  -- recursing on the mapped tail submodule, and pulling the glued basis back through the inverse
  -- equivalence. The remaining blocker is the same carrier-level transport between the forgotten
  -- `k`-linear tail map and the original product-ring tail map.
  sorry

/-- Helper for Lemma 10.78.8: in the concrete product-of-fields coordinate model, a `k`-subspace
whose `A`-span is the whole ambient free `A`-module already contains an `A`-basis. -/
private theorem exists_basis_mem_submodule_of_span_eq_top_prod_fields
    {k : Type u} [Field k] [Infinite k]
    {ι : Type v} {K : ι → Type w}
    [Fintype ι] [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] :
    ∀ n : ℕ,
      ∀ Npi : Submodule k (∀ i, Fin n → K i),
        Submodule.span (∀ i, K i) (Npi : Set (∀ i, Fin n → K i)) = ⊤ →
        ∃ b : Module.Basis (Fin n) (∀ i, K i) (∀ i, Fin n → K i), ∀ j, b j ∈ Npi
  | 0, Npi, hspan => by
      let e : (∀ i, Fin 0 → K i) ≃ₗ[(∀ i, K i)] Fin 0 → (∀ i, K i) :=
        LinearEquiv.ofSubsingleton _ _
      -- In rank zero the ambient module is trivial, so the unique basis works.
      refine ⟨Module.Basis.ofEquivFun e, ?_⟩
      intro j
      exact Fin.elim0 j
  | n + 1, Npi, hspan => by
      -- Proof comment: dispatch the successor case to the dedicated normalization-tail-gluing
      -- theorem so the recursive proof stays flat and follows the source induction.
      exact exists_basis_mem_submodule_of_span_eq_top_prod_fields_succ
        (k := k) (ι := ι) (K := K) n Npi
        (fun Ntail htail ↦ exists_basis_mem_submodule_of_span_eq_top_prod_fields n Ntail htail)
        hspan

/-- Helper for Lemma 10.78.8: before any `Fin`-reindexing, the Jacobson quotient inherits the
canonical base-change basis indexed by `Module.Free.ChooseBasisIndex S M`. -/
private noncomputable def jacobson_quotient_tensor_basis :
    Module.Basis (Module.Free.ChooseBasisIndex S M) (S ⧸ Ring.jacobson S)
      (M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))) :=
  -- Proof comment: base-change the chosen free `S`-basis of `M`, then identify the tensor product
  -- with the Jacobson quotient via the standard tensor-quotient equivalence.
  ((Module.Free.chooseBasis S M).baseChange (S ⧸ Ring.jacobson S)).map
    ((TensorProduct.quotTensorEquivQuotSMul M (Ring.jacobson S)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective)

/-- Helper for Lemma 10.78.8: reindex the canonical Jacobson-quotient basis by `Fin` using the
finite rank of `M` in the nontrivial branch where `StrongRankCondition` is available. -/
private noncomputable def jacobson_quotient_chooseBasis_nontrivial [Nontrivial S] :
    Module.Basis (Fin (Module.finrank S M)) (S ⧸ Ring.jacobson S)
      (M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))) :=
  -- Proof comment: the canonical quotient basis is already available; only the `Fin`-reindexing
  -- along `Module.finrank_eq_card_chooseBasisIndex` remains.
  jacobson_quotient_tensor_basis (S := S) (M := M) |>.reindex
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_chooseBasisIndex (R := S) (M := M)).symm)

/-- Helper for Lemma 10.78.8: the maximal spectrum of the Jacobson quotient is finite because it
injects into the maximal spectrum of the original semilocal ring. -/
private theorem finite_maximalSpectrum_jacobson_quotient :
    Finite (MaximalSpectrum (S ⧸ Ring.jacobson S)) := by
  classical
  let A : Type v := S ⧸ Ring.jacobson S
  let f : MaximalSpectrum A → MaximalSpectrum S := fun x ↦
    ⟨Ideal.comap (Ideal.Quotient.mk (Ring.jacobson S)) x.asIdeal,
      Ideal.comap_isMaximal_of_surjective
        (Ideal.Quotient.mk (Ring.jacobson S)) Ideal.Quotient.mk_surjective (K := x.asIdeal)⟩
  -- Proof comment: surjectivity of the quotient map makes comap on ideals injective, so maximal
  -- ideals of the quotient can be viewed as distinct maximal ideals of the original ring.
  exact Finite.of_injective f (by
    intro x y hxy
    apply MaximalSpectrum.ext
    exact Ideal.comap_injective_of_surjective
      (Ideal.Quotient.mk (Ring.jacobson S)) Ideal.Quotient.mk_surjective
      (by simpa using congrArg MaximalSpectrum.asIdeal hxy))

/-- Helper for Lemma 10.78.8: curry the free module `Fin n → ∀ i, K i` into the product-fields
model `∀ i, Fin n → K i` without changing the ambient product-ring linear structure. -/
private noncomputable def fin_pi_curry_linear_equiv
    {ι : Type v} {K : ι → Type w}
    [Fintype ι] [∀ i, Field (K i)] (n : ℕ) :
    (Fin n → ∀ i, K i) ≃ₗ[(∀ i, K i)] ∀ i, Fin n → K i :=
  { toFun := fun f i j ↦ f j i
    invFun := fun f j i ↦ f i j
    left_inv := by
      intro f
      funext j i
      rfl
    right_inv := by
      intro f
      funext i j
      rfl
    map_add' := by
      intro f g
      funext i j
      rfl
    map_smul' := by
      intro a f
      funext i j
      rfl }

/-- Helper for Lemma 10.78.8: changing coefficients along a ring equivalence agrees with the module
structure obtained by restricting scalars along the inverse equivalence. -/
private theorem ringEquiv_apply_smul_eq_original
    {A : Type u} {P : Type v} {V : Type w}
    [CommSemiring A] [CommSemiring P] [AddCommMonoid V] [Module A V]
    (e : A ≃+* P) :
    letI : Module P V := Module.compHom V (e.symm : P →+* A)
    ∀ c : A, ∀ x : V, e c • x = c • x := by
  intro c x
  -- Proof comment: after changing scalars via `Module.compHom`, the action of `e c` is
  -- definitionally the original action of `e.symm (e c) = c`.
  change e.symm (e c) • x = c • x
  simpa using congrArg (fun d : A ↦ d • x) (e.left_inv c)

/-- Helper for Lemma 10.78.8: transporting scalars back along the inverse ring equivalence recovers
the current module action. -/
private theorem ringEquiv_symm_apply_smul_eq_original
    {A : Type u} {P : Type v} {V : Type w}
    [CommSemiring A] [CommSemiring P] [AddCommMonoid V] [Module P V]
    (e : A ≃+* P) :
    letI : Module A V := Module.compHom V (e : A →+* P)
    ∀ c : P, ∀ x : V, e.symm c • x = c • x := by
  intro c x
  -- Proof comment: this is the same definitional scalar-transport identity, now written for the
  -- inverse equivalence so that `Basis.mapCoeffs` can return from the product ring to the quotient.
  change e (e.symm c) • x = c • x
  simpa using congrArg (fun d : P ↦ d • x) (e.right_inv c)

/-- Helper for Lemma 10.78.8: the quotient-coordinate adapter is now reduced to reindexing the
canonical quotient basis and then changing coefficients along the semisimple ring equivalence. -/
private noncomputable def jacobson_quotient_prod_fields_linear_equiv [Nontrivial S] :
    let A : Type v := S ⧸ Ring.jacobson S
  let K : MaximalSpectrum A → Type v := fun x ↦ A ⧸ x.asIdeal
  let P : Type v := ∀ x : MaximalSpectrum A, K x
  let Mbar : Type w := M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))
  letI : Finite (MaximalSpectrum A) := finite_maximalSpectrum_jacobson_quotient (S := S)
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite (MaximalSpectrum A)
  letI (x : MaximalSpectrum A) : Field (K x) := Ideal.Quotient.field x.asIdeal
  let eA : A ≃+* P := jacobson_quotient_ring_equiv_pi_maximal_quotients
    A (Ring.jacobson_quotient_jacobson (R := S))
  letI : Module P Mbar := Module.compHom Mbar (eA.symm : P →+* A)
  Mbar ≃ₗ[P] (∀ x, Fin (Module.finrank S M) → K x) := by
  classical
  let A : Type v := S ⧸ Ring.jacobson S
  let K : MaximalSpectrum A → Type v := fun x ↦ A ⧸ x.asIdeal
  let P : Type v := ∀ x : MaximalSpectrum A, K x
  let Mbar : Type w := M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))
  letI : Finite (MaximalSpectrum A) := finite_maximalSpectrum_jacobson_quotient (S := S)
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite (MaximalSpectrum A)
  letI (x : MaximalSpectrum A) : Field (K x) := Ideal.Quotient.field x.asIdeal
  let eA : A ≃+* P := jacobson_quotient_ring_equiv_pi_maximal_quotients
    A (Ring.jacobson_quotient_jacobson (R := S))
  letI : Module P Mbar := Module.compHom Mbar (eA.symm : P →+* A)
  let bP : Module.Basis (Fin (Module.finrank S M)) P Mbar :=
    (jacobson_quotient_chooseBasis_nontrivial (S := S) (M := M)).mapCoeffs eA
      (ringEquiv_apply_smul_eq_original (V := Mbar) eA)
  -- Proof comment: first rewrite the quotient module in `Fin`-coordinates over the semisimple
  -- product ring, then curry those coordinates into the factorwise product-fields model.
  exact (bP.equivFun).trans
    (fin_pi_curry_linear_equiv (ι := MaximalSpectrum A) (K := K) (Module.finrank S M))

/-- Helper for Lemma 10.78.8: zero belongs to the literal Jacobson-quotient image of `N`. -/
private theorem zero_mem_jacobson_quotient_image_residue_carrier
    (N : Submodule R M) :
    let J : Ideal S := Ring.jacobson S
    let Mbar : Type w := M ⧸ (J • (⊤ : Submodule S M))
    (0 : Mbar) ∈ (J • (⊤ : Submodule S M)).mkQ '' (N : Set M) := by
  intro J Mbar
  -- Proof comment: the zero class comes from the zero vector of the submodule.
  refine ⟨0, N.zero_mem, ?_⟩
  rfl

/-- Helper for Lemma 10.78.8: the literal Jacobson-quotient image of `N` is closed under
addition. -/
private theorem add_mem_jacobson_quotient_image_residue_carrier
    (N : Submodule R M) :
    let J : Ideal S := Ring.jacobson S
    let Mbar : Type w := M ⧸ (J • (⊤ : Submodule S M))
    ∀ {x y : Mbar},
      x ∈ (J • (⊤ : Submodule S M)).mkQ '' (N : Set M) →
      y ∈ (J • (⊤ : Submodule S M)).mkQ '' (N : Set M) →
      x + y ∈ (J • (⊤ : Submodule S M)).mkQ '' (N : Set M) := by
  intro J Mbar x y hx hy
  rcases hx with ⟨m, hm, rfl⟩
  rcases hy with ⟨n, hn, rfl⟩
  -- Proof comment: the quotient map is additive, so the sum comes from `m + n ∈ N`.
  refine ⟨m + n, N.add_mem hm hn, ?_⟩
  simp

/-- Helper for Lemma 10.78.8: the literal Jacobson-quotient image of `N` is closed under the
residue-field scalars coming from `R`. -/
private theorem smul_mem_jacobson_quotient_image_residue_carrier
    (N : Submodule R M)
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S)
    (c : IsLocalRing.ResidueField R)
    {x : M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))}
    (hx : x ∈ (Ring.jacobson S • (⊤ : Submodule S M)).mkQ '' (N : Set M)) :
    let k := IsLocalRing.ResidueField R
    let J : Ideal S := Ring.jacobson S
    let A : Type v := S ⧸ J
    let Mbar : Type w := M ⧸ (J • (⊤ : Submodule S M))
    letI : Algebra k A := Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp hmj)
    letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
    c • x ∈ (J • (⊤ : Submodule S M)).mkQ '' (N : Set M) := by
  let k := IsLocalRing.ResidueField R
  let J : Ideal S := Ring.jacobson S
  let A : Type v := S ⧸ J
  let Mbar : Type w := M ⧸ (J • (⊤ : Submodule S M))
  letI : Algebra k A := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp hmj)
  letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) c
  rcases hx with ⟨m, hm, rfl⟩
  -- Proof comment: lift the residue-field scalar to `R`, act on the witness in `N`, and descend
  -- that action through the quotient map.
  refine ⟨(algebraMap R S r) • m, ?_, ?_⟩
  · simpa using N.smul_mem r hm
  · change
      (algebraMap R (S ⧸ Ring.jacobson S) r) •
          ((Ring.jacobson S • (⊤ : Submodule S M)).mkQ m) =
        (algebraMap (IsLocalRing.ResidueField R) (S ⧸ Ring.jacobson S)
            (IsLocalRing.residue R r)) •
          ((Ring.jacobson S • (⊤ : Submodule S M)).mkQ m)
    rfl

/-- Helper for Lemma 10.78.8: the literal Jacobson-quotient image of `N` is stable under the
residue-field scalars coming from `R`. -/
private noncomputable def jacobson_quotient_image_residue_submodule
    (N : Submodule R M)
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S) :
    let k := IsLocalRing.ResidueField R
    let J : Ideal S := Ring.jacobson S
    let A : Type v := S ⧸ J
    let Mbar : Type w := M ⧸ (J • (⊤ : Submodule S M))
    letI : Algebra k A := Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp hmj)
    letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
    Submodule k Mbar :=
  let k := IsLocalRing.ResidueField R
  let J : Ideal S := Ring.jacobson S
  let A : Type v := S ⧸ J
  let Mbar : Type w := M ⧸ (J • (⊤ : Submodule S M))
  letI : Algebra k A := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp hmj)
  letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
  -- Proof comment: package the literal image set as a residue-field submodule using the closure
  -- lemmas above, so later pullbacks end with a single carrier rewrite.
  { carrier := (J • (⊤ : Submodule S M)).mkQ '' (N : Set M)
    zero_mem' := zero_mem_jacobson_quotient_image_residue_carrier (R := R) (S := S) (M := M) N
    add_mem' := add_mem_jacobson_quotient_image_residue_carrier (R := R) (S := S) (M := M) N
    smul_mem' := fun c x hx ↦ smul_mem_jacobson_quotient_image_residue_carrier
      (R := R) (S := S) (M := M) N hmj c (x := x) hx }

/-- Helper for Lemma 10.78.8: membership in the residue-field Jacobson-quotient image is exactly
membership in the literal quotient image of `N`. -/
private theorem mem_jacobson_quotient_image_residue_submodule_iff
    (N : Submodule R M)
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S)
    (x : M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))) :
    let k := IsLocalRing.ResidueField R
    let J : Ideal S := Ring.jacobson S
    let A : Type v := S ⧸ J
    let Mbar : Type w := M ⧸ (J • (⊤ : Submodule S M))
    letI : Algebra k A := Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp hmj)
    letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
    x ∈ jacobson_quotient_image_residue_submodule (R := R) (S := S) (M := M) N hmj ↔
      x ∈ (Ring.jacobson S • (⊤ : Submodule S M)).mkQ '' (N : Set M) := by
  -- Proof comment: the residue-field submodule was defined with this literal carrier, so the
  -- membership statement is just the carrier rewrite.
  dsimp [jacobson_quotient_image_residue_submodule]
  rfl

/-- Helper for Lemma 10.78.8: the residue-field Jacobson-quotient image of `N` still spans the
whole quotient over `S ⧸ Ring.jacobson S`. -/
private theorem jacobson_quotient_image_residue_submodule_span_eq_top
    (N : Submodule R M)
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S)
    (hN : Submodule.span S (N : Set M) = ⊤) :
    let k := IsLocalRing.ResidueField R
    let J : Ideal S := Ring.jacobson S
    let A : Type v := S ⧸ J
    let Mbar : Type w := M ⧸ (J • (⊤ : Submodule S M))
    letI : Algebra k A := Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp hmj)
    letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
    Submodule.span A
      (jacobson_quotient_image_residue_submodule (R := R) (S := S) (M := M) N hmj : Set Mbar) = ⊤ := by
  -- Proof comment: rewrite the packaged residue-field submodule back to the literal quotient image
  -- and invoke the already-proved Jacobson-quotient spanning statement.
  dsimp [jacobson_quotient_image_residue_submodule]
  exact jacobson_quotient_span_eq_top_of_span_eq_top (R := R) (S := S) (M := M) N hN

/-- Helper for Lemma 10.78.8: transport the Jacobson quotient into the product-of-residue-fields
coordinates as a genuine residue-field-linear map. -/
private noncomputable def jacobson_quotient_coordinate_map_linear
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S)
    [Nontrivial S] :
    let k := IsLocalRing.ResidueField R
    let J : Ideal S := Ring.jacobson S
    let A : Type v := S ⧸ J
    let K : MaximalSpectrum A → Type v := fun x ↦ A ⧸ x.asIdeal
    let P : Type v := ∀ x : MaximalSpectrum A, K x
    let Mbar : Type w := M ⧸ (J • (⊤ : Submodule S M))
    letI : Algebra k A := Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp hmj)
    letI : Finite (MaximalSpectrum A) := finite_maximalSpectrum_jacobson_quotient (S := S)
    letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite (MaximalSpectrum A)
    letI (x : MaximalSpectrum A) : Field (K x) := Ideal.Quotient.field x.asIdeal
    letI : Algebra k P := ((jacobson_quotient_ring_equiv_pi_maximal_quotients
      A (Ring.jacobson_quotient_jacobson (R := S))).toRingHom.comp (algebraMap k A)).toAlgebra
    let eA : A ≃+* P := jacobson_quotient_ring_equiv_pi_maximal_quotients
      A (Ring.jacobson_quotient_jacobson (R := S))
    letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
    letI : Module P Mbar := Module.compHom Mbar (eA.symm : P →+* A)
    Mbar →ₗ[k] (∀ x, Fin (Module.finrank S M) → K x) := sorry

private theorem exists_jacobson_quotient_basis_mem_submodule
    (N : Submodule R M)
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S)
    (hN : Submodule.span S (N : Set M) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank S M)) (S ⧸ Ring.jacobson S)
      (M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))),
      ∀ i, b i ∈ (Ring.jacobson S • (⊤ : Submodule S M)).mkQ '' (N : Set M) := by
  -- TODO: finish the Jacobson-quotient closing step by packaging the product-of-residue-fields
  -- coordinates as a genuine `k`-submodule `Npi`, proving its `P`-span is top via the semisimple
  -- ring equivalence, and then pulling the resulting basis back through the quotient coordinate map.
  -- The remaining blocker is a stable `k`-module API on `∀ x, Fin (finrank S M) → (A ⧸ x.asIdeal)`
  -- that avoids the current scalar-transport/elaboration failures.
  sorry

/-- Lemma 10.78.8: if `R` is a local ring with infinite residue field, `S` is a semilocal
`R`-algebra such that the extension of the maximal ideal of `R` is contained in the Jacobson
radical of `S`, `M` is a finite free `S`-module, and the `R`-submodule `N` generates `M` as an
`S`-module, then `N` contains an `S`-basis of `M`. -/
-- Proof sketch: reduce modulo the Jacobson radical of `S` using Nakayama's lemma, so that `S`
-- becomes a finite product of fields. Then choose an element of `N` with nonzero component in each
-- factor by using the infinitude of the residue field of `R`; this generates a free direct summand.
-- Quotient by that summand and argue by induction on the rank of the free module.
theorem exists_basis_mem_submodule_of_span_eq_top
    (N : Submodule R M)
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S)
    (hN : Submodule.span S (N : Set M) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank S M)) S M, ∀ i, b i ∈ N := by
  -- Reduce the theorem to finding a basis in the Jacobson quotient coming from `N`.
  obtain ⟨b, hb⟩ := exists_jacobson_quotient_basis_mem_submodule N hmj hN
  -- Once the quotient basis is available, Nakayama lifts it back to a basis of `M`.
  exact exists_basis_of_jacobson_quotient_basis_mem_submodule N b hb

end
