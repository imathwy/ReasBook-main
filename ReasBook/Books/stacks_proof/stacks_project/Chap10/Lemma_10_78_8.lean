import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_15_4_Chinese_remainder
import stacks_proof.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import stacks_proof.stacks_project.Chap10.Lemma_10_78_8.Index

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

omit [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)] [Algebra R S]
  [Finite (MaximalSpectrum S)] [IsScalarTower R S M] [Module.Free S M]
  [Module.Finite S M] in
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

omit [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)] [Algebra R S]
  [Finite (MaximalSpectrum S)] [IsScalarTower R S M] [Module.Free S M] in
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

omit [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)] [Algebra R S]
  [Finite (MaximalSpectrum S)] [IsScalarTower R S M] [Module.Free S M]
  [Module.Finite S M] in
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

omit [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)] [Finite (MaximalSpectrum S)]
  [Module.Free S M] [Module.Finite S M] in
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

omit [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)] [Finite (MaximalSpectrum S)]
  [Module.Free S M] [Module.Finite S M] in
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
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)]
    [∀ i, IsScalarTower k (K i) (K i)] {n : ℕ}
    (Npi : Submodule k (∀ i, Fin (n + 1) → K i))
    (hspan : Submodule.span (∀ i, K i) (Npi : Set (∀ i, Fin (n + 1) → K i)) = ⊤)
    (_hhead : (fun _ ↦ Fin.cons 1 0 : ∀ i, Fin (n + 1) → K i) ∈ Npi) :
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
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)]
    [∀ i, IsScalarTower k (K i) (K i)] {n : ℕ}
    (Npi : Submodule k (∀ i, Fin (n + 1) → K i))
    (hspan : Submodule.span (∀ i, K i) (Npi : Set (∀ i, Fin (n + 1) → K i)) = ⊤)
    (hhead : (fun _ ↦ Fin.cons 1 0 : ∀ i, Fin (n + 1) → K i) ∈ Npi) :
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
    [Finite ι] [∀ i, Field (K i)] {n : ℕ}
    (btail : Module.Basis (Fin n) (∀ i, K i) (∀ i, Fin n → K i))
    (z : Fin n → ∀ i, Fin (n + 1) → K i)
    (hz :
      ∀ j,
        ((LinearMap.snd (∀ i, K i) (∀ i, K i) (∀ i, Fin n → K i)).comp
          (prod_fields_head_tail_linear_equiv (ι := ι) (K := K) (n := n)).toLinearMap) (z j) =
            btail j) :
    ∃ bsum : Module.Basis (Fin 1 ⊕ Fin n) (∀ i, K i) (∀ i, Fin (n + 1) → K i),
      (∀ i : Fin 1, bsum (Sum.inl i) = fun _ ↦ Fin.cons 1 0) ∧
      ∀ j, bsum (Sum.inr j) = z j := by
  letI : Fintype ι := Fintype.ofFinite ι
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
      _ = fun _ ↦ Fin.cons 1 0 := by
            ext t j
            rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', rfl⟩
            · subst hj
              simp [headTail, prod_fields_head_tail_linear_equiv]
            ·
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
      simp [φ]
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
    (hb : ∀ i, b i ∈ (e.toLinearMap : V → W) '' (N0 : Set V)) :
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

/-- Helper for Lemma 10.78.8: cache the inverse-after-forward identity for a linear equivalence
so later transport proofs do not unfold a large concrete equivalence. -/
private theorem linearEquiv_symm_apply_apply_cached
    {A : Type u} {V : Type v} {W : Type w}
    [Semiring A] [AddCommMonoid V] [AddCommMonoid W] [Module A V] [Module A W]
    (e : V ≃ₗ[A] W) (x : V) :
    e.symm (e x) = x := by
  -- Proof comment: isolate the standard inverse law behind a small theorem with a fresh budget.
  exact LinearEquiv.symm_apply_apply e x

/-- Helper for Lemma 10.78.8: an `A`-linear map between modules in a scalar tower is also
`k`-linear after forgetting from `A` to `k`. -/
private theorem linearMap_map_smul_of_tower
    {k : Type u} {A : Type*} {V : Type*} {W : Type*}
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
    {k : Type u} {A : Type*} {V : Type*} {W : Type*}
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
    {k : Type u} {A : Type*} {V : Type*} {W : Type*}
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
    simp

/-- Helper for Lemma 10.78.8: an `∏ Kᵢ`-linear map between product-field coordinate modules is
linear over the residue field `k` after forgetting scalars. -/
private theorem prod_fields_linearMap_map_smul_to_residue
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] {n m : ℕ}
    (f : (∀ i, Fin n → K i) →ₗ[(∀ i, K i)] (∀ i, Fin m → K i))
    (c : k) (x : ∀ i, Fin n → K i) :
    f (c • x) = c • f x := by
  have h := f.map_smul (algebraMap k (∀ i, K i) c) x
  -- Proof comment: compare the forgotten `k`-action with product-ring scalar multiplication
  -- pointwise, then use the original product-ring linearity.
  convert h
  · ext i j
    simp [Algebra.smul_def]
  · ext i j
    simp [Algebra.smul_def]

/-- Helper for Lemma 10.78.8: the product-fields scalar compatibility in the exact
`LinearMap.map_smul'` normal form for a `k`-linear structure. -/
private theorem prod_fields_linearMap_map_smul_to_residue_id
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] [∀ i, Module k (K i)] {n m : ℕ}
    (f : (∀ i, Fin n → K i) →ₗ[(∀ i, K i)] (∀ i, Fin m → K i))
    (c : k) (x : ∀ i, Fin n → K i) :
    f (c • x) = (RingHom.id k) c • f x := by
  -- Proof comment: this is only a normal-form adapter for the structure field; the mathematics is
  -- the pointwise product-fields scalar compatibility proved above.
  simpa using prod_fields_linearMap_map_smul_to_residue (k := k) (ι := ι) (K := K) f c x

/-- Helper for Lemma 10.78.8: the product-fields normalization equivalence can be made
`k`-linear with the same forward and inverse carrier maps. -/
private theorem exists_prod_fields_normalization_linearEquiv_to_residue_linear
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] {n : ℕ}
    (e : (∀ i, Fin (n + 1) → K i) ≃ₗ[(∀ i, K i)] (∀ i, Fin (n + 1) → K i)) :
    ∃ ek : (∀ i, Fin (n + 1) → K i) ≃ₗ[k] (∀ i, Fin (n + 1) → K i),
      (∀ x, ek x = e x) ∧ ∀ x, ek.symm x = e.symm x := by
  -- Proof comment: construct the forgotten-scalar equivalence directly so the `map_smul'` goal
  -- uses Lean's chosen `k`-module action, then compare it pointwise with product-ring linearity.
  refine ⟨?ek, ?_, ?_⟩
  · refine
      { toFun := fun x ↦ e x
        invFun := fun x ↦ e.symm x
        left_inv := e.left_inv
        right_inv := e.right_inv
        map_add' := e.map_add
        map_smul' := ?_ }
    intro c x
    letI : SMul k ((i : ι) → Fin (n + 1) → K i) :=
      (inferInstance : DistribMulAction k ((i : ι) → Fin (n + 1) → K i)).toDistribSMul.toSMul
    calc
      e (c • x) = e ((algebraMap k (∀ i, K i) c) • x) := by
        congr 1
        funext i j
        simpa [Algebra.smul_def] using (algebraMap_smul (K i) c (x i j)).symm
      _ = (algebraMap k (∀ i, K i) c) • e x := e.map_smul _ _
      _ = (RingHom.id k) c • e x := by
        funext i j
        simpa [Algebra.smul_def] using algebraMap_smul (K i) c ((e x) i j)
  · intro x
    rfl
  · intro x
    rfl

/-- Helper for Lemma 10.78.8: forget scalars on the product-fields normalization equivalence so the
source induction can map `k`-submodules through the same underlying automorphism. -/
private noncomputable def prod_fields_normalization_linearEquiv_to_residue_linear
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] {n : ℕ}
    (e : (∀ i, Fin (n + 1) → K i) ≃ₗ[(∀ i, K i)] (∀ i, Fin (n + 1) → K i)) :
    (∀ i, Fin (n + 1) → K i) ≃ₗ[k] (∀ i, Fin (n + 1) → K i) :=
  Classical.choose (exists_prod_fields_normalization_linearEquiv_to_residue_linear
    (k := k) (ι := ι) (K := K) (n := n) e)

/-- Helper for Lemma 10.78.8: the forgotten normalization equivalence has the same underlying
carrier map as the original product-ring linear equivalence. -/
private theorem prod_fields_normalization_linearEquiv_to_residue_linear_apply
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] {n : ℕ}
    (e : (∀ i, Fin (n + 1) → K i) ≃ₗ[(∀ i, K i)] (∀ i, Fin (n + 1) → K i))
    (x : ∀ i, Fin (n + 1) → K i) :
    prod_fields_normalization_linearEquiv_to_residue_linear
        (k := k) (ι := ι) (K := K) (n := n) e x =
      e x := by
  -- Proof comment: the manual adapter was built with exactly the original carrier map.
  exact (Classical.choose_spec (exists_prod_fields_normalization_linearEquiv_to_residue_linear
    (k := k) (ι := ι) (K := K) (n := n) e)).1 x

/-- Helper for Lemma 10.78.8: the inverse of the forgotten normalization equivalence has the same
underlying carrier map as the original inverse equivalence. -/
private theorem prod_fields_normalization_linearEquiv_to_residue_linear_symm_apply
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] {n : ℕ}
    (e : (∀ i, Fin (n + 1) → K i) ≃ₗ[(∀ i, K i)] (∀ i, Fin (n + 1) → K i))
    (x : ∀ i, Fin (n + 1) → K i) :
    (prod_fields_normalization_linearEquiv_to_residue_linear
        (k := k) (ι := ι) (K := K) (n := n) e).symm x =
      e.symm x := by
  -- Proof comment: the inverse carrier of the manual adapter is the original inverse map.
  exact (Classical.choose_spec (exists_prod_fields_normalization_linearEquiv_to_residue_linear
    (k := k) (ι := ι) (K := K) (n := n) e)).2 x

/-- Helper for Lemma 10.78.8: the product-fields tail projection can be made `k`-linear with the
same carrier map. -/
private theorem exists_prod_fields_tail_projection_to_residue_linear
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] {n : ℕ}
    (tailMap : (∀ i, Fin (n + 1) → K i) →ₗ[(∀ i, K i)] (∀ i, Fin n → K i)) :
    ∃ tailk : (∀ i, Fin (n + 1) → K i) →ₗ[k] (∀ i, Fin n → K i),
      ∀ x, tailk x = tailMap x := by
  -- Proof comment: as for normalization, prove scalar compatibility in the exact structure-field
  -- goal and compare the two scalar actions componentwise.
  refine ⟨?tailk, ?_⟩
  · refine
      { toFun := fun x ↦ tailMap x
        map_add' := tailMap.map_add
        map_smul' := ?_ }
    intro c x
    letI : SMul k ((i : ι) → Fin (n + 1) → K i) :=
      (inferInstance : DistribMulAction k ((i : ι) → Fin (n + 1) → K i)).toDistribSMul.toSMul
    letI : SMul k ((i : ι) → Fin n → K i) :=
      (inferInstance : DistribMulAction k ((i : ι) → Fin n → K i)).toDistribSMul.toSMul
    calc
      tailMap (c • x) = tailMap ((algebraMap k (∀ i, K i) c) • x) := by
        congr 1
        funext i j
        simpa [Algebra.smul_def] using (algebraMap_smul (K i) c (x i j)).symm
      _ = (algebraMap k (∀ i, K i) c) • tailMap x := tailMap.map_smul _ _
      _ = (RingHom.id k) c • tailMap x := by
        funext i j
        simpa [Algebra.smul_def] using algebraMap_smul (K i) c ((tailMap x) i j)
  · intro x
    rfl

/-- Helper for Lemma 10.78.8: forget scalars on the tail projection so the source induction can
recurse on the mapped `k`-submodule instead of a raw set image. -/
private noncomputable def prod_fields_tail_projection_to_residue_linear
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] {n : ℕ}
    (tailMap : (∀ i, Fin (n + 1) → K i) →ₗ[(∀ i, K i)] (∀ i, Fin n → K i)) :
    (∀ i, Fin (n + 1) → K i) →ₗ[k] (∀ i, Fin n → K i) :=
  Classical.choose (exists_prod_fields_tail_projection_to_residue_linear
    (k := k) (ι := ι) (K := K) (n := n) tailMap)

/-- Helper for Lemma 10.78.8: the forgotten tail projection has the same carrier map as the
original product-ring linear tail projection. -/
private theorem prod_fields_tail_projection_to_residue_linear_apply
    {k : Type u} [Field k]
    {ι : Type v} {K : ι → Type w}
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)] {n : ℕ}
    (tailMap : (∀ i, Fin (n + 1) → K i) →ₗ[(∀ i, K i)] (∀ i, Fin n → K i))
    (x : ∀ i, Fin (n + 1) → K i) :
    prod_fields_tail_projection_to_residue_linear
        (k := k) (ι := ι) (K := K) (n := n) tailMap x =
      tailMap x := by
  -- Proof comment: the forgotten tail projection keeps the original carrier map.
  exact Classical.choose_spec (exists_prod_fields_tail_projection_to_residue_linear
    (k := k) (ι := ι) (K := K) (n := n) tailMap) x

/-- Helper for Lemma 10.78.8: in the concrete product-of-fields coordinate model, a `k`-subspace
whose `A`-span is the whole ambient free `A`-module already contains an `A`-basis. -/
private theorem exists_basis_mem_submodule_of_span_eq_top_prod_fields_succ
    {k : Type u} [Field k] [Infinite k]
    {ι : Type v} {K : ι → Type w}
    [Finite ι] [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (n : ℕ)
    (Npi : Submodule k (∀ i, Fin (n + 1) → K i))
    (ih :
      ∀ Ntail : Submodule k (∀ i, Fin n → K i),
        Submodule.span (∀ i, K i) (Ntail : Set (∀ i, Fin n → K i)) = ⊤ →
        ∃ b : Module.Basis (Fin n) (∀ i, K i) (∀ i, Fin n → K i), ∀ j, b j ∈ Ntail)
    (hspan : Submodule.span (∀ i, K i) (Npi : Set (∀ i, Fin (n + 1) → K i)) = ⊤) :
    ∃ b : Module.Basis (Fin (n + 1)) (∀ i, K i) (∀ i, Fin (n + 1) → K i), ∀ j, b j ∈ Npi := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let V := ∀ i, Fin (n + 1) → K i
  let W := ∀ i, Fin n → K i
  have hfactor :
      ∀ i, Submodule.span (K i) ((fun y : V ↦ y i) '' (Npi : Set V)) = ⊤ :=
    factor_span_eq_top_of_span_eq_top_prod_fields (k := k) (ι := ι) (K := K) Npi hspan
  obtain ⟨y, hyN, hyne⟩ :=
    exists_mem_nonzero_in_each_factor_of_factor_span_eq_top_prod_fields
      (k := k) (ι := ι) (K := K) Npi hfactor
  obtain ⟨e, hey⟩ := prod_fields_normalize_nonzero_vector (K := K) y hyne
  let ek := prod_fields_normalization_linearEquiv_to_residue_linear
    (k := k) (ι := ι) (K := K) (n := n) e
  let Nnorm : Submodule k V := Npi.map ek.toLinearMap
  have hNnorm_set : (Nnorm : Set V) = (e.toLinearMap : V → V) '' (Npi : Set V) := by
    ext x
    constructor
    · rintro ⟨z, hzN, rfl⟩
      refine ⟨z, hzN, ?_⟩
      exact (prod_fields_normalization_linearEquiv_to_residue_linear_apply
        (k := k) (ι := ι) (K := K) (n := n) e z).symm
    · rintro ⟨z, hzN, rfl⟩
      refine ⟨z, hzN, ?_⟩
      exact prod_fields_normalization_linearEquiv_to_residue_linear_apply
        (k := k) (ι := ι) (K := K) (n := n) e z
  have hNnorm_span : Submodule.span (∀ i, K i) (Nnorm : Set V) = ⊤ := by
    rw [hNnorm_set]
    calc
      Submodule.span (∀ i, K i) ((e.toLinearMap : V → V) '' (Npi : Set V)) =
          Submodule.map e.toLinearMap (Submodule.span (∀ i, K i) (Npi : Set V)) := by
            rw [Submodule.map_span]
      _ = ⊤ := by
            rw [hspan, Submodule.map_top]
            exact LinearMap.range_eq_top.2 e.surjective
  have hhead : (fun i ↦ Fin.cons 1 0 : V) ∈ Nnorm := by
    refine ⟨y, hyN, ?_⟩
    calc
      ek y = e y := prod_fields_normalization_linearEquiv_to_residue_linear_apply
        (k := k) (ι := ι) (K := K) (n := n) e y
      _ = (fun i ↦ Fin.cons 1 0 : V) := hey
  let tailMap : V →ₗ[(∀ i, K i)] W :=
    (LinearMap.snd (∀ i, K i) (∀ i, K i) W).comp
      (prod_fields_head_tail_linear_equiv (ι := ι) (K := K) (n := n)).toLinearMap
  let tailk := prod_fields_tail_projection_to_residue_linear
    (k := k) (ι := ι) (K := K) (n := n) tailMap
  let Ntail : Submodule k W := Nnorm.map tailk
  have hNtail_set : (Ntail : Set W) = (tailMap : V → W) '' (Nnorm : Set V) := by
    ext x
    constructor
    · rintro ⟨z, hzN, rfl⟩
      refine ⟨z, hzN, ?_⟩
      exact (prod_fields_tail_projection_to_residue_linear_apply
        (k := k) (ι := ι) (K := K) (n := n) tailMap z).symm
    · rintro ⟨z, hzN, rfl⟩
      refine ⟨z, hzN, ?_⟩
      exact prod_fields_tail_projection_to_residue_linear_apply
        (k := k) (ι := ι) (K := K) (n := n) tailMap z
  have htail_span : Submodule.span (∀ i, K i) (Ntail : Set W) = ⊤ := by
    rw [hNtail_set]
    exact tail_map_submodule_span_eq_top_of_head_mem_prod_fields
      (k := k) (ι := ι) (K := K) (n := n) Nnorm hNnorm_span hhead
  obtain ⟨btail, hbtail⟩ := ih Ntail htail_span
  have hbtail_image : ∀ j, btail j ∈ (tailMap : V → W) '' (Nnorm : Set V) := by
    intro j
    have h := hbtail j
    change btail j ∈ (Ntail : Set W) at h
    rw [hNtail_set] at h
    exact h
  choose z hzNnorm hztail using hbtail_image
  have hz_tail : ∀ j, tailMap (z j) = btail j := by
    intro j
    exact hztail j
  obtain ⟨bsum, hbsum_head, hbsum_tail⟩ :=
    exists_sum_basis_of_head_and_tail_lifts_prod_fields
      (ι := ι) (K := K) (n := n) btail z hz_tail
  let eidx : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
    finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
  let bnorm : Module.Basis (Fin (n + 1)) (∀ i, K i) V := bsum.reindex eidx
  have hbnorm : ∀ j, bnorm j ∈ Nnorm := by
    intro j
    rw [Module.Basis.reindex_apply]
    cases eidx.symm j with
    | inl i =>
        simpa [hbsum_head i] using hhead
    | inr j =>
        simpa [hbsum_tail j] using hzNnorm j
  have hbimage : ∀ j, bnorm j ∈ (e.toLinearMap : V → V) '' (Npi : Set V) := by
    intro j
    have h := hbnorm j
    change bnorm j ∈ (Nnorm : Set V) at h
    rw [hNnorm_set] at h
    exact h
  refine ⟨bnorm.map e.symm, ?_⟩
  -- Proof comment: the normalized basis is in the image of `Npi`; pulling it back through the
  -- inverse normalization equivalence gives the required basis in the original submodule.
  exact basis_pullback_mem_of_mem_map (k := k) (A := (∀ i, K i)) (N0 := Npi) e bnorm hbimage

/-- Helper for Lemma 10.78.8: in the concrete product-of-fields coordinate model, a `k`-subspace
whose `A`-span is the whole ambient free `A`-module already contains an `A`-basis. -/
private theorem exists_basis_mem_submodule_of_span_eq_top_prod_fields
    {k : Type u} [Field k] [Infinite k]
    {ι : Type v} {K : ι → Type w}
    [Finite ι] [∀ i, Field (K i)] [∀ i, Algebra k (K i)] :
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

/-- Helper for Lemma 10.78.8: after transporting an `A`-module structure to `P` along a ring
equivalence, scalar multiplication by `c : P` is multiplication by `e.symm c` in the original
module. -/
private theorem ringEquiv_compHom_symm_smul_eq_original
    {A : Type u} {P : Type v} {V : Type w}
    [CommSemiring A] [CommSemiring P] [AddCommMonoid V] [Module A V]
    (e : A ≃+* P) :
    letI : Module P V := Module.compHom V (e.symm : P →+* A)
    ∀ c : P, ∀ x : V, e.symm c • x = c • x := by
  intro c x
  -- Proof comment: the transported `P`-action is defined by first applying `e.symm`.
  rfl

/-- Helper for Lemma 10.78.8: a set spanning over a ring also spans after transporting the module
structure across a ring equivalence. -/
private theorem span_top_of_span_top_ringEquiv_compHom
    {A : Type u} {P : Type v} {V : Type w}
    [CommSemiring A] [CommSemiring P] [AddCommMonoid V] [Module A V]
    (e : A ≃+* P) (T : Set V) :
    letI : Module P V := Module.compHom V (e.symm : P →+* A)
    Submodule.span A T = ⊤ → Submodule.span P T = ⊤ := by
  intro hspan
  letI : Module P V := Module.compHom V (e.symm : P →+* A)
  -- Proof comment: every `A`-linear span step is also a `P`-linear span step after replacing
  -- scalar `a` by `e a`.
  apply eq_top_iff.mpr
  intro v hv
  have hvA : v ∈ Submodule.span A T := by
    simpa [hspan]
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hvA
  · intro x hx
    exact Submodule.subset_span hx
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    have hpx : e a • x ∈ Submodule.span P T := Submodule.smul_mem _ (e a) hx
    simpa [ringEquiv_apply_smul_eq_original (V := V) e a x] using hpx

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

/-- Helper for Lemma 10.78.8: applying the inverse product-coordinate equivalence after the
forward equivalence gives back the original Jacobson-quotient vector. -/
private theorem jacobson_quotient_prod_fields_linear_equiv_symm_apply_apply [Nontrivial S] :
    ∀ x : M ⧸ (Ring.jacobson S • (⊤ : Submodule S M)),
      (jacobson_quotient_prod_fields_linear_equiv (S := S) (M := M)).symm
        (jacobson_quotient_prod_fields_linear_equiv (S := S) (M := M) x) = x := by
  classical
  intro z
  -- Proof comment: cache the inverse law for the concrete coordinate equivalence in its own
  -- declaration, avoiding repeated unfolding in the final basis transport.
  exact (jacobson_quotient_prod_fields_linear_equiv (S := S) (M := M)).symm_apply_apply z

omit [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)] [Algebra R S]
  [Finite (MaximalSpectrum S)] [IsScalarTower R S M] [Module.Free S M]
  [Module.Finite S M] in
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

omit [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)] [Algebra R S]
  [Finite (MaximalSpectrum S)] [IsScalarTower R S M] [Module.Free S M]
  [Module.Finite S M] in
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

omit [Infinite (IsLocalRing.ResidueField R)] [Finite (MaximalSpectrum S)]
  [Module.Free S M] [Module.Finite S M] in
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

omit [Infinite (IsLocalRing.ResidueField R)] [Finite (MaximalSpectrum S)]
  [Module.Free S M] [Module.Finite S M] in
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

omit [Infinite (IsLocalRing.ResidueField R)] [Finite (MaximalSpectrum S)]
  [Module.Free S M] [Module.Finite S M] in
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

omit [Infinite (IsLocalRing.ResidueField R)] [Module R M] [IsScalarTower R S M] in
/-- Helper for Lemma 10.78.8: the product-coordinate equivalence on the Jacobson quotient can be
viewed as a residue-field-linear map without changing its carrier map. -/
private theorem exists_jacobson_quotient_coordinate_map_linear
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
    letI (x : MaximalSpectrum A) : Algebra k (K x) :=
      ((Ideal.Quotient.mk x.asIdeal).comp (algebraMap k A)).toAlgebra
    letI : Algebra k P := ((jacobson_quotient_ring_equiv_pi_maximal_quotients
      A (Ring.jacobson_quotient_jacobson (R := S))).toRingHom.comp (algebraMap k A)).toAlgebra
    let eA : A ≃+* P := jacobson_quotient_ring_equiv_pi_maximal_quotients
      A (Ring.jacobson_quotient_jacobson (R := S))
    letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
    letI : Module P Mbar := Module.compHom Mbar (eA.symm : P →+* A)
    letI : Module k (∀ x, Fin (Module.finrank S M) → K x) :=
      Module.compHom (∀ x, Fin (Module.finrank S M) → K x) (algebraMap k P)
    ∃ f : Mbar →ₗ[k] (∀ x, Fin (Module.finrank S M) → K x),
      ∀ x, f x = jacobson_quotient_prod_fields_linear_equiv (S := S) (M := M) x := by
  classical
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
  letI (x : MaximalSpectrum A) : Algebra k (K x) :=
    ((Ideal.Quotient.mk x.asIdeal).comp (algebraMap k A)).toAlgebra
  letI : Algebra k P := ((jacobson_quotient_ring_equiv_pi_maximal_quotients
    A (Ring.jacobson_quotient_jacobson (R := S))).toRingHom.comp (algebraMap k A)).toAlgebra
  let eA : A ≃+* P := jacobson_quotient_ring_equiv_pi_maximal_quotients
    A (Ring.jacobson_quotient_jacobson (R := S))
  letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
  letI : Module P Mbar := Module.compHom Mbar (eA.symm : P →+* A)
  letI : Module k (∀ x, Fin (Module.finrank S M) → K x) :=
    Module.compHom (∀ x, Fin (Module.finrank S M) → K x) (algebraMap k P)
  let e : Mbar ≃ₗ[P] (∀ x, Fin (Module.finrank S M) → K x) :=
    jacobson_quotient_prod_fields_linear_equiv (S := S) (M := M)
  -- Proof comment: package the existing `P`-linear coordinate equivalence as a `k`-linear map;
  -- only scalar compatibility needs transport through the quotient-ring equivalence.
  refine ⟨?f, ?_⟩
  · refine
      { toFun := fun x ↦ e x
        map_add' := e.map_add
        map_smul' := ?_ }
    intro c x
    let p : P := eA (algebraMap k A c)
    let psmulx : Mbar := (eA.symm p) • x
    calc
      e (c • x) = e psmulx := by
        congr 1
        have hp : eA.symm p = algebraMap k A c := by
          dsimp [p]
          exact eA.left_inv (algebraMap k A c)
        calc
          c • x = (algebraMap k A c) • x := rfl
          _ = (eA.symm p) • x := by rw [hp]
          _ = psmulx := rfl
      _ = p • e x := by
        exact e.map_smul p x
      _ = c • e x := by
        have hpP : p = algebraMap k P c := rfl
        rw [hpP]
        rfl
  · intro x
    rfl

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
    letI (x : MaximalSpectrum A) : Algebra k (K x) :=
      ((Ideal.Quotient.mk x.asIdeal).comp (algebraMap k A)).toAlgebra
    letI : Algebra k P := ((jacobson_quotient_ring_equiv_pi_maximal_quotients
      A (Ring.jacobson_quotient_jacobson (R := S))).toRingHom.comp (algebraMap k A)).toAlgebra
    let eA : A ≃+* P := jacobson_quotient_ring_equiv_pi_maximal_quotients
      A (Ring.jacobson_quotient_jacobson (R := S))
    letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
    letI : Module P Mbar := Module.compHom Mbar (eA.symm : P →+* A)
    letI : Module k (∀ x, Fin (Module.finrank S M) → K x) :=
      Module.compHom (∀ x, Fin (Module.finrank S M) → K x) (algebraMap k P)
    Mbar →ₗ[k] (∀ x, Fin (Module.finrank S M) → K x) :=
  Classical.choose (exists_jacobson_quotient_coordinate_map_linear
    (R := R) (S := S) (M := M) hmj)

omit [Infinite (IsLocalRing.ResidueField R)] [Module R M] [IsScalarTower R S M] in
/-- Helper for Lemma 10.78.8: the residue-field-linear coordinate map has the same carrier as the
product-coordinate equivalence. -/
private theorem jacobson_quotient_coordinate_map_linear_apply
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S)
    [Nontrivial S]
    (x : M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))) :
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
    letI (x : MaximalSpectrum A) : Algebra k (K x) :=
      ((Ideal.Quotient.mk x.asIdeal).comp (algebraMap k A)).toAlgebra
    letI : Algebra k P := ((jacobson_quotient_ring_equiv_pi_maximal_quotients
      A (Ring.jacobson_quotient_jacobson (R := S))).toRingHom.comp (algebraMap k A)).toAlgebra
    let eA : A ≃+* P := jacobson_quotient_ring_equiv_pi_maximal_quotients
      A (Ring.jacobson_quotient_jacobson (R := S))
    letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
    letI : Module P Mbar := Module.compHom Mbar (eA.symm : P →+* A)
    letI : Module k (∀ x, Fin (Module.finrank S M) → K x) :=
      Module.compHom (∀ x, Fin (Module.finrank S M) → K x) (algebraMap k P)
    jacobson_quotient_coordinate_map_linear (R := R) (S := S) (M := M) hmj x =
      jacobson_quotient_prod_fields_linear_equiv (S := S) (M := M) x := by
  -- Proof comment: the definition is a `Classical.choose`, and the existence theorem records the
  -- intended carrier equality for every quotient vector.
  exact (Classical.choose_spec (exists_jacobson_quotient_coordinate_map_linear
    (R := R) (S := S) (M := M) hmj)) x

/-- Helper for Lemma 10.78.8: the same product-coordinate basis pullback, stated only for a set of
Jacobson-quotient vectors so applying it does not involve residue-field submodule instances. -/
private theorem jacobson_quotient_product_basis_pullback_mem_set [Nontrivial S] :
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
    ∀ (T : Set Mbar)
      (bP : Module.Basis (Fin (Module.finrank S M)) P
        (∀ x, Fin (Module.finrank S M) → K x)),
      (∀ i, bP i ∈
        ((jacobson_quotient_prod_fields_linear_equiv (S := S) (M := M)).toLinearMap :
          Mbar → (∀ x, Fin (Module.finrank S M) → K x)) '' T) →
      ∀ i,
        (bP.map (jacobson_quotient_prod_fields_linear_equiv (S := S) (M := M)).symm) i ∈
          T := by
  classical
  dsimp
  intro T bP hbimage i
  rcases hbimage i with ⟨x, hx, hxeq⟩
  have hpre :
      (jacobson_quotient_prod_fields_linear_equiv (S := S) (M := M)).symm (bP i) = x := by
    rw [← hxeq]
    exact jacobson_quotient_prod_fields_linear_equiv_symm_apply_apply (S := S) (M := M) x
  -- Proof comment: this is the set-level form consumed by the final theorem; no submodule
  -- structure participates in the inverse-equivalence rewrite.
  simpa [Module.Basis.map_apply, hpre] using hx

/-- Chap10 Lemma 10 78 8: the Jacobson quotient contains a quotient basis whose vectors come
from the image of `N`. -/
private theorem exists_jacobson_quotient_basis_mem_submodule
    (N : Submodule R M)
    (hmj : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S)
    (hN : Submodule.span S (N : Set M) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank S M)) (S ⧸ Ring.jacobson S)
      (M ⧸ (Ring.jacobson S • (⊤ : Submodule S M))),
      ∀ i, b i ∈ (Ring.jacobson S • (⊤ : Submodule S M)).mkQ '' (N : Set M) := by
  classical
  by_cases hS : Nontrivial S
  · letI : Nontrivial S := hS
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
    letI (x : MaximalSpectrum A) : Algebra k (K x) :=
      ((Ideal.Quotient.mk x.asIdeal).comp (algebraMap k A)).toAlgebra
    letI : Algebra k P := ((jacobson_quotient_ring_equiv_pi_maximal_quotients
      A (Ring.jacobson_quotient_jacobson (R := S))).toRingHom.comp (algebraMap k A)).toAlgebra
    let eA : A ≃+* P := jacobson_quotient_ring_equiv_pi_maximal_quotients
      A (Ring.jacobson_quotient_jacobson (R := S))
    letI : Module k Mbar := Module.compHom Mbar (algebraMap k A)
    letI : Module P Mbar := Module.compHom Mbar (eA.symm : P →+* A)
    letI : Module k (∀ x, Fin (Module.finrank S M) → K x) :=
      Module.compHom (∀ x, Fin (Module.finrank S M) → K x) (algebraMap k P)
    let Nres : Submodule k Mbar :=
      jacobson_quotient_image_residue_submodule (R := R) (S := S) (M := M) N hmj
    let f : Mbar →ₗ[k] (∀ x, Fin (Module.finrank S M) → K x) :=
      jacobson_quotient_coordinate_map_linear (R := R) (S := S) (M := M) hmj
    let eP : Mbar ≃ₗ[P] (∀ x, Fin (Module.finrank S M) → K x) :=
      jacobson_quotient_prod_fields_linear_equiv (S := S) (M := M)
    let Npi : Submodule k (∀ x, Fin (Module.finrank S M) → K x) := Nres.map f
    have hNresA : Submodule.span A (Nres : Set Mbar) = ⊤ := by
      simpa [Nres] using jacobson_quotient_image_residue_submodule_span_eq_top
        (R := R) (S := S) (M := M) N hmj hN
    have hNresP : Submodule.span P (Nres : Set Mbar) = ⊤ := by
      exact span_top_of_span_top_ringEquiv_compHom (V := Mbar) eA (Nres : Set Mbar) hNresA
    have hNpi_set :
        (Npi : Set (∀ x, Fin (Module.finrank S M) → K x)) =
          (eP.toLinearMap : Mbar → (∀ x, Fin (Module.finrank S M) → K x)) ''
            (Nres : Set Mbar) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x, hx, ?_⟩
        -- Proof comment: the residue-field coordinate map has the same carrier as the local
        -- product-coordinate equivalence `eP`.
        simpa [f, eP] using (jacobson_quotient_coordinate_map_linear_apply
          (R := R) (S := S) (M := M) hmj x).symm
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x, hx, ?_⟩
        -- Proof comment: the reverse inclusion uses the same carrier equality in the forward
        -- direction to identify the two image descriptions.
        simpa [f, eP] using jacobson_quotient_coordinate_map_linear_apply
          (R := R) (S := S) (M := M) hmj x
    have hNpi_span :
        Submodule.span P (Npi : Set (∀ x, Fin (Module.finrank S M) → K x)) = ⊤ := by
      rw [hNpi_set]
      calc
        Submodule.span P
            ((eP.toLinearMap :
              Mbar → (∀ x, Fin (Module.finrank S M) → K x)) '' (Nres : Set Mbar)) =
            Submodule.map
              eP.toLinearMap
              (Submodule.span P (Nres : Set Mbar)) := by
              rw [Submodule.map_span]
        _ = ⊤ := by
              rw [hNresP, Submodule.map_top]
              exact LinearMap.range_eq_top.2 eP.surjective
    obtain ⟨bP, hbP⟩ :=
      exists_basis_mem_submodule_of_span_eq_top_prod_fields
        (k := k) (ι := MaximalSpectrum A) (K := K) (Module.finrank S M) Npi hNpi_span
    have hbMbarNres : ∀ i, (bP.map eP.symm) i ∈ Nres := by
      have hbimage :
          ∀ i, bP i ∈
            (eP.toLinearMap : Mbar → (∀ x, Fin (Module.finrank S M) → K x)) ''
              (Nres : Set Mbar) := by
        intro i
        have hmem := hbP i
        change bP i ∈ (Npi : Set (∀ x, Fin (Module.finrank S M) → K x)) at hmem
        rwa [hNpi_set] at hmem
      -- Route correction: avoid the earlier Jacobson-specific pullback helper, whose global
      -- equivalence spelling caused transport matching failure; stay in the local `eP` normal
      -- form and recover each witness by applying the inverse equivalence.
      intro i
      rcases hbimage i with ⟨x, hx, hxeq⟩
      have hpre : eP.symm (bP i) = x := by
        exact (congrArg eP.symm hxeq.symm).trans
          (by
            simpa [eP] using
              jacobson_quotient_prod_fields_linear_equiv_symm_apply_apply (S := S) (M := M) x)
      rw [Module.Basis.map_apply, hpre]
      exact hx
    let bA : Module.Basis (Fin (Module.finrank S M)) A Mbar :=
      (bP.map eP.symm).mapCoeffs eA.symm
        (ringEquiv_compHom_symm_smul_eq_original (V := Mbar) eA)
    refine ⟨bA, ?_⟩
    intro i
    have hiNres : (bP.map eP.symm) i ∈ Nres := hbMbarNres i
    have hiraw :
        (bP.map eP.symm) i ∈ (Ring.jacobson S • (⊤ : Submodule S M)).mkQ ''
          (N : Set M) := by
      exact (mem_jacobson_quotient_image_residue_submodule_iff
        (R := R) (S := S) (M := M) N hmj ((bP.map eP.symm) i)).mp hiNres
    simpa [bA] using hiraw
  · letI : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    let J : Ideal S := Ring.jacobson S
    let A : Type v := S ⧸ J
    let Mbar : Type w := M ⧸ (J • (⊤ : Submodule S M))
    haveI : Subsingleton M := by
      refine ⟨fun x y ↦ ?_⟩
      have hx0 : x = 0 := by
        calc
          x = (1 : S) • x := by simp
          _ = (0 : S) • x := by rw [Subsingleton.elim (1 : S) 0]
          _ = 0 := by simp
      have hy0 : y = 0 := by
        calc
          y = (1 : S) • y := by simp
          _ = (0 : S) • y := by rw [Subsingleton.elim (1 : S) 0]
          _ = 0 := by simp
      exact hx0.trans hy0.symm
    letI : Subsingleton Mbar := inferInstance
    let e : Mbar ≃ₗ[A] (Fin (Module.finrank S M) → A) := LinearEquiv.ofSubsingleton _ _
    let b : Module.Basis (Fin (Module.finrank S M)) A Mbar := Module.Basis.ofEquivFun e
    refine ⟨b, ?_⟩
    intro i
    have hzero : (0 : Mbar) ∈ (J • (⊤ : Submodule S M)).mkQ '' (N : Set M) :=
      zero_mem_jacobson_quotient_image_residue_carrier (R := R) (S := S) (M := M) N
    simpa [J, Mbar, Subsingleton.elim (b i) 0] using hzero

/-- Consequence of Chap10 Lemma 10 78 8: if `R` is a local ring with infinite residue field, `S` is a semilocal
`R`-algebra such that the extension of the maximal ideal of `R` is contained in the Jacobson
radical of `S`, `M` is a finite free `S`-module, and the `R`-submodule `N` generates `M` as an
`S`-module, then `N` contains an `S`-basis of `M`. -/
-- Proof sketch: reduce modulo the Jacobson radical of `S` using Nakayama's lemma, so that `S`
-- becomes a finite product of fields. Then choose an element of `N` with nonzero component in each
-- factor by using the infinitude of the residue field of `R`; this generates a free direct summand.
-- Quotient by that summand and argue by induction on the rank of the free module.
@[stacks 03C1]
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
