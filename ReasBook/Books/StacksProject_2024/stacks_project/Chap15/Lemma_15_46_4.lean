import StacksProject_2024.Chap15.Definition_15_46_1
import StacksProject_2024.Chap09.Lemma_9_14_5
import StacksProject_2024.Chap15.Lemma_15_46_2
import StacksProject_2024.Chap15.Lemma_15_46_3

-- Declarations for this item will be appended below by the statement pipeline.

open KaehlerDifferential
open scoped FrobeniusSubfield TensorProduct IntermediateField

universe u v w

section

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]

local instance : Algebra (ZMod p) K := ZMod.algebra K p

variable {A : Type v} (Kα : A → Subfield K)

private instance instSMulSubfield (k : Subfield K) : SMul (ZMod p) k :=
  (inferInstance : Algebra (ZMod p) k).toSMul

private theorem coe_algebraMap_zmod_subfield (k : Subfield K) (x : ZMod p) :
    (((algebraMap (ZMod p) k) x : k) : K) = algebraMap (ZMod p) K x :=
  congrArg (fun f : ZMod p →+* K ↦ f x)
    (RingHom.ext_zmod ((algebraMap k K).comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) K))

private theorem coe_zmod_smul_subfield (k : Subfield K) (x : ZMod p) (y : k) :
    ((x • y : k) : K) = x • (y : K) := by
  simpa [Algebra.smul_def] using
    congrArg (fun z : K ↦ z * (y : K)) (coe_algebraMap_zmod_subfield k x)

private instance instIsScalarTowerSubfield (k : Subfield K) : IsScalarTower (ZMod p) k K where
  smul_assoc x y z := by
    change (((x • y : k) : K) * z) = x • y • z
    rw [coe_zmod_smul_subfield k x y]
    exact smul_mul_assoc x (y : K) z

local notation "kaehlerDifferentialMapTo" α =>
  @KaehlerDifferential.map (ZMod p) (Kα α) _ _
    (inferInstance : Algebra (ZMod p) (Kα α)) K K _ _
    (inferInstance : Algebra (ZMod p) K) (inferInstance : Algebra K K)
    (inferInstance : Algebra (Kα α) K) (inferInstance : Algebra (ZMod p) K)
    (inferInstance : IsScalarTower (ZMod p) K K) (instIsScalarTowerSubfield (Kα α))
    (inferInstance : SMulCommClass (Kα α) K K)

local notation "kaehlerDifferentialMapBaseChangeFrom" α =>
  @KaehlerDifferential.mapBaseChange (ZMod p) _ (Kα α) K _ _
    (inferInstance : Algebra (ZMod p) (Kα α))
    (inferInstance : Algebra (Kα α) K)
    (inferInstance : Algebra (ZMod p) K)
    (instIsScalarTowerSubfield (Kα α))

/-
Domain triage:
* primary domain: fields of characteristic `p`, Frobenius subfields, and the canonical
  Kähler-differential maps induced by `𝔽_p ⊆ K_α ⊆ K`, together with the chapter owner
  `pPowerCompositum` for the compositum `L^p K_α`;
* sampled owner declarations:
  - `frobeniusSubfield`,
  - `pPowerCompositum`,
  - `KaehlerDifferential.map`,
  - `Subfield.map`,
  - `Subfield.mem_iInf`;
* best owner abstraction: the primitive owner data are the family of subfields `Kα` and the
  canonical owner map `KaehlerDifferential.map (ZMod p) k K K`; the
  intersection-of-kernels and
  Frobenius-compositum statements are derived API, with the latter expressed through
  `pPowerCompositum` rather than a parallel raw `⊔`/`Subfield.map` spelling;
* layer triage:
  - `source-facing`: the two clauses of Lemma `15.46.4`;
  - `core/canonical`: `K^[p]`, `pPowerCompositum`, `KaehlerDifferential.map`, and the
    lattice operations on subfields;
  - `bridge/view`: no extra bridge owner is needed beyond the reusable comparison-map owner
  above; the source-facing statements use it together with `pPowerCompositum`.
-/

/-- Helper for Lemma 15.46.4: an element lies in the intersection of the differential kernels
exactly when every canonical map sends it to zero. -/
lemma mem_iInf_ker_kaehlerDifferentialMapTo_iff {ω : Ω[K⁄(ZMod p)]} :
    ω ∈ (⨅ α, LinearMap.ker (kaehlerDifferentialMapTo α)) ↔
      ∀ α : A, (kaehlerDifferentialMapTo α) ω = 0 := by
  -- Unpack the lattice-theoretic intersection into the pointwise kernel condition.
  constructor
  · intro hω α
    rw [Submodule.mem_iInf] at hω
    exact LinearMap.mem_ker.mp (hω α)
  · intro hω
    rw [Submodule.mem_iInf]
    intro α
    exact LinearMap.mem_ker.mpr (hω α)

/-- Helper for Lemma 15.46.4: every Kähler differential over `𝔽_p` has a finite coordinate
expansion along the differentials of a chosen `p`-basis. -/
lemma pbasis_differential_coordinates {ι : Type*} (x : ι → K)
    (hx : IsPBasis p (ZMod p) K x) (ω : Ω[K⁄(ZMod p)]) :
    ∃ (T : Finset Ω[K⁄(ZMod p)]) (c : T →₀ K),
      ↑T ⊆ Set.range (D (ZMod p) K ∘ x) ∧
        c.sum (fun t a ↦ a • (t : Ω[K⁄(ZMod p)])) = ω := by
  classical
  -- The `p`-basis criterion identifies the chosen differentials as a spanning family.
  have hform :=
    (isPBasis_iff_differentials_formBasis (p := p) (k := ZMod p) (K := K) x).1 hx
  have hωspan : ω ∈ Submodule.span K (Set.range (D (ZMod p) K ∘ x)) := by
    rw [hform.2]
    exact Submodule.mem_top
  -- Shrink the infinite spanning family to a finite support and record its coefficients.
  obtain ⟨T, hTsub, hTmem⟩ := Submodule.mem_span_finite_of_mem_span hωspan
  have hTmem' :
      ω ∈ Submodule.span K (Set.range fun t : T ↦ (t : Ω[K⁄(ZMod p)])) := by
    simpa using hTmem
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hTmem'
  refine ⟨T, c, hTsub, ?_⟩
  simpa [Finsupp.sum] using hc

/-- Helper for Lemma 15.46.4: reindex a finite differential coordinate expansion along a
chosen `p`-basis by `Fin n`, so the remaining descent argument no longer has to transport through
`Finset` subtypes. -/
lemma reindex_pbasis_coordinate_support {ι : Type*} (x : ι → K)
    (hx : IsPBasis p (ZMod p) K x) {ω : Ω[K⁄(ZMod p)]} (hω : ω ≠ 0) :
    ∃ (n : ℕ) (y : Fin n → ι) (c : Fin n → K),
      Function.Injective y ∧
        c ≠ 0 ∧
        ω = ∑ i, c i • D (ZMod p) K (x (y i)) ∧
        LinearIndependent K (fun i ↦ D (ZMod p) K (x (y i))) := by
  classical
  obtain ⟨T, cT, hTsub, hcω⟩ :=
    pbasis_differential_coordinates (p := p) (K := K) x hx ω
  have hform :=
    (isPBasis_iff_differentials_formBasis (p := p) (k := ZMod p) (K := K) x).1 hx
  have hcT_ne : cT ≠ 0 := by
    -- A zero coefficient family would force the displayed differential to vanish.
    intro hcT_zero
    apply hω
    rw [← hcω, hcT_zero]
    simp
  have hy_exists : ∀ t : T, ∃ i, D (ZMod p) K (x i) = (t : Ω[K⁄(ZMod p)]) := by
    intro t
    have ht_range :
        ((t : T) : Ω[K⁄(ZMod p)]) ∈ Set.range (D (ZMod p) K ∘ x) :=
      hTsub t.2
    simpa [Function.comp] using ht_range
  choose yT hyT using hy_exists
  have hyT_injective : Function.Injective yT := by
    -- Distinct subtype coordinates cannot share the same chosen preimage because the preimage
    -- equations recover the original differential exactly.
    intro t₁ t₂ hyt
    apply Subtype.ext
    calc
      ((t₁ : T) : Ω[K⁄(ZMod p)]) = D (ZMod p) K (x (yT t₁)) := by
        symm
        exact hyT t₁
      _ = D (ZMod p) K (x (yT t₂)) := by simpa [hyt]
      _ = ((t₂ : T) : Ω[K⁄(ZMod p)]) := hyT t₂
  let e : T ≃ Fin T.card := Finset.equivFin T
  let y : Fin T.card → ι := fun i ↦ yT (e.symm i)
  let c : Fin T.card → K := fun i ↦ cT (e.symm i)
  have hy_injective : Function.Injective y := by
    -- The `Fin` reindexing preserves injectivity because `e.symm` and the chosen preimages do.
    intro i j hij
    apply e.symm.injective
    exact hyT_injective hij
  have hc_ne : c ≠ 0 := by
    -- Reindexing the coefficient function does not create the zero vector.
    intro hc_zero
    apply hcT_ne
    ext t
    have hct := congrFun hc_zero (e t)
    simpa [c] using hct
  have hω_coords : ω = ∑ i, c i • D (ZMod p) K (x (y i)) := by
    -- First rewrite the `Finsupp` sum as an honest sum over the finite subtype `T`, then
    -- transport that finite sum along the equivalence `T ≃ Fin T.card`.
    calc
      ω = cT.sum (fun t a ↦ a • (t : Ω[K⁄(ZMod p)])) := by simpa using hcω.symm
      _ = ∑ t : T, cT t • (t : Ω[K⁄(ZMod p)]) := by
        exact Finsupp.sum_fintype cT
          (fun t a ↦ a • (t : Ω[K⁄(ZMod p)])) (by intro t; simp)
      _ = ∑ i : Fin T.card, c i • D (ZMod p) K (x (y i)) := by
        exact Fintype.sum_equiv e
          (fun t : T ↦ cT t • (t : Ω[K⁄(ZMod p)]))
          (fun i : Fin T.card ↦ c i • D (ZMod p) K (x (y i)))
          (by
            intro t
            simp [c, y, hyT])
  have hlin : LinearIndependent K (fun i ↦ D (ZMod p) K (x (y i))) := by
    -- The global differential independence from the `p`-basis survives restriction to this
    -- finite injective subfamily.
    simpa [y, Function.comp] using hform.1.comp y hy_injective
  exact ⟨T.card, y, c, hy_injective, hc_ne, hω_coords, hlin⟩

/-- Helper for Lemma 15.46.4: a differential that vanishes after base change to `K / K_α`
comes from a tensor preimage under the left map of the field Jacobi-Zariski sequence. -/
lemma kernel_exactness_preimage (α : A) {ω : Ω[K⁄(ZMod p)]}
    (hω : (kaehlerDifferentialMapTo α) ω = 0) :
    ∃ z, (kaehlerDifferentialMapBaseChangeFrom α) z = ω := by
  -- Freeze the owner exactness theorem with all scalar towers fixed, then read off a preimage.
  exact ((@KaehlerDifferential.exact_mapBaseChange_map (ZMod p) _ (Kα α) K _ _
      (inferInstance : Algebra (ZMod p) (Kα α))
      (inferInstance : Algebra (Kα α) K)
      (inferInstance : Algebra (ZMod p) K)
      (instIsScalarTowerSubfield (Kα α)) ω).mp hω)

/-- Helper for Lemma 15.46.4: every tensor preimage can be normalized to a finite sum of simple
tensors before any coefficient descent is attempted. -/
lemma exact_preimage_sum_tmul (α : A)
    (z : K ⊗[(Kα α)] Ω[(Kα α)⁄(ZMod p)]) :
    ∃ (m : ℕ) (a : Fin m → K) (η : Fin m → Ω[(Kα α)⁄(ZMod p)]),
      z = ∑ j, a j ⊗ₜ[(Kα α)] η j := by
  -- Expand the tensor witness once so later lemmas can work with a visible finite sum.
  obtain ⟨m, a, η, hz⟩ := TensorProduct.exists_sum_tmul_eq z
  exact ⟨m, a, η, hz⟩

/-- Helper for Lemma 15.46.4: the base-change map distributes over a finite sum of pure tensors. -/
lemma mapBaseChange_sum_tmul (α : A) :
    ∀ {m : ℕ} (a : Fin m → K) (η : Fin m → Ω[(Kα α)⁄(ZMod p)]),
      (kaehlerDifferentialMapBaseChangeFrom α) (∑ j, a j ⊗ₜ[(Kα α)] η j) =
        ∑ j, (kaehlerDifferentialMapBaseChangeFrom α) (a j ⊗ₜ[(Kα α)] η j) := by
  intro m
  induction m with
  | zero =>
      intro a η
      -- The empty sum case is the zero map applied to zero.
      simp
  | succ m ih =>
      intro a η
      -- Split the finite sum into its head term and tail, then use additivity of the map.
      rw [Fin.sum_univ_succ, map_add, ih (fun j => a j.succ) (fun j => η j.succ),
        Fin.sum_univ_succ]

/-- Helper for Lemma 15.46.4: a kernel element admits an exactness preimage already expanded as a
finite sum of simple tensors. -/
lemma kernel_exactness_preimage_sum_tmul (α : A) {ω : Ω[K⁄(ZMod p)]}
    (hω : (kaehlerDifferentialMapTo α) ω = 0) :
    ∃ (m : ℕ) (a : Fin m → K) (η : Fin m → Ω[(Kα α)⁄(ZMod p)]),
      ω = ∑ j, (kaehlerDifferentialMapBaseChangeFrom α) (a j ⊗ₜ[(Kα α)] η j) := by
  obtain ⟨z, hz⟩ := kernel_exactness_preimage (Kα := Kα) α hω
  obtain ⟨m, a, η, hzsum⟩ := exact_preimage_sum_tmul (Kα := Kα) α z
  refine ⟨m, a, η, ?_⟩
  -- Rewrite the exactness witness through the finite pure-tensor expansion of its preimage.
  calc
    ω = (kaehlerDifferentialMapBaseChangeFrom α) z := hz.symm
    _ = ∑ j, (kaehlerDifferentialMapBaseChangeFrom α) (a j ⊗ₜ[(Kα α)] η j) := by
      rw [hzsum]
      exact mapBaseChange_sum_tmul (Kα := Kα) α a η

/-- Helper for Lemma 15.46.4: every Kähler differential over a subfield `K_α` is already a
finite sum of universal differentials `D(b)` with coefficients in `K_α`. -/
lemma subfield_kaehlerDifferential_finite_sum_D (α : A)
    (η : Ω[(Kα α)⁄(ZMod p)]) :
    ∃ (m : ℕ) (r : Fin m → Kα α) (b : Fin m → Kα α),
      η = ∑ j, r j • D (ZMod p) (Kα α) (b j) := by
  classical
  -- Use the owner span theorem for `Ω[(K_α)⁄𝔽_p]`, then shrink to a finite support.
  have hηspan : η ∈ Submodule.span (Kα α) (Set.range (D (ZMod p) (Kα α))) := by
    rw [KaehlerDifferential.span_range_derivation (ZMod p) (Kα α)]
    exact Submodule.mem_top
  obtain ⟨T, hTsub, hTmem⟩ := Submodule.mem_span_finite_of_mem_span hηspan
  have hTmem' :
      η ∈ Submodule.span (Kα α) (Set.range fun t : T ↦ (t : Ω[(Kα α)⁄(ZMod p)])) := by
    simpa using hTmem
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hTmem'
  have hb_exists : ∀ t : T, ∃ b : Kα α, D (ZMod p) (Kα α) b = (t : Ω[(Kα α)⁄(ZMod p)]) := by
    intro t
    have ht_range :
        ((t : T) : Ω[(Kα α)⁄(ZMod p)]) ∈ Set.range (D (ZMod p) (Kα α)) :=
      hTsub t.2
    simpa using ht_range
  choose bT hbT using hb_exists
  let e : T ≃ Fin T.card := Finset.equivFin T
  let r : Fin T.card → Kα α := fun i ↦ c (e.symm i)
  let b : Fin T.card → Kα α := fun i ↦ bT (e.symm i)
  refine ⟨T.card, r, b, ?_⟩
  -- Reindex the finite subtype support by `Fin T.card` so later transport lemmas stay flat.
  calc
    η = c.sum (fun t a ↦ a • (t : Ω[(Kα α)⁄(ZMod p)])) := by
      simpa [Finsupp.sum] using hc.symm
    _ = ∑ t : T, c t • (t : Ω[(Kα α)⁄(ZMod p)]) := by
      exact Finsupp.sum_fintype c
        (fun t a ↦ a • (t : Ω[(Kα α)⁄(ZMod p)])) (by intro t; simp)
    _ = ∑ i : Fin T.card, r i • D (ZMod p) (Kα α) (b i) := by
      exact Fintype.sum_equiv e
        (fun t : T ↦ c t • (t : Ω[(Kα α)⁄(ZMod p)]))
        (fun i : Fin T.card ↦ r i • D (ZMod p) (Kα α) (b i))
        (by
          intro t
          simp [r, b, hbT])

/-- Helper for Lemma 15.46.4: once a subfield differential is expanded as a finite sum of
`D(b)` terms, the base-change map rewrites a pure tensor preimage into the corresponding finite
sum inside `Ω[K⁄𝔽_p]`. -/
lemma mapBaseChange_tmul_subfield_differential_sum (α : A) {m : ℕ}
    (a : K) (r : Fin m → Kα α) (b : Fin m → Kα α) :
    (kaehlerDifferentialMapBaseChangeFrom α)
        (a ⊗ₜ[(Kα α)] (∑ j, r j • D (ZMod p) (Kα α) (b j))) =
      ∑ j, (a * (r j : K)) • D (ZMod p) K (b j) := by
  -- Rewrite the pure tensor by `mapBaseChange_tmul` first, so no tensor-side transport remains.
  rw [KaehlerDifferential.mapBaseChange_tmul, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  -- The owner formulas `map_smul` and `map_D` reduce the term to a scalar-combination identity.
  rw [map_smul, KaehlerDifferential.map_D]
  change a • ((r j : K) • D (ZMod p) K (b j)) = (a * (r j : K)) • D (ZMod p) K (b j)
  rw [smul_smul]

/-- Helper for Lemma 15.46.4: if a differential lies in every kernel, then each family member
admits a concrete tensor preimage under the base-change map. -/
lemma kernel_exactness_preimage_family {ω : Ω[K⁄(ZMod p)]}
    (hω : ∀ α : A, (kaehlerDifferentialMapTo α) ω = 0) :
    ∀ α : A, ∃ z, (kaehlerDifferentialMapBaseChangeFrom α) z = ω := by
  intro α
  -- Package the pointwise kernel hypothesis through the single-index preimage extractor.
  exact kernel_exactness_preimage (Kα := Kα) α (hω α)

/-- Helper for Lemma 15.46.4: if a subfield already contains `K^[p]`, then adjoining `K^[p]`
over that base contributes nothing. -/
lemma pPowerCompositum_eq_bot_of_frobeniusSubfield_le (k : Subfield K)
    (hk : K^[p] ≤ k) :
    pPowerCompositum p k K = ⊥ := by
  -- The mixed compositum is the adjoin of `K^[p]`, so it collapses to the base field image once
  -- `K^[p]` is already contained in the chosen subfield.
  refine le_antisymm ?_ bot_le
  rw [show pPowerCompositum p k K = IntermediateField.adjoin k (K^[p] : Set K) by rfl]
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  change x ∈ ((⊥ : IntermediateField k K).toSubfield : Set K)
  exact ⟨⟨x, hk hx⟩, rfl⟩

/-- Helper for Lemma 15.46.4: every `p`th power of `K` belongs to the mixed compositum over
`𝔽_p`. -/
lemma mem_pPowerCompositum_zmod_of_mem_frobeniusSubfield {x : K} (hx : x ∈ K^[p]) :
    x ∈ (pPowerCompositum p (ZMod p) K).toSubfield := by
  -- By definition the mixed compositum adjoins `K^[p]` to the prime field.
  exact IntermediateField.subset_adjoin (ZMod p) (K^[p] : Set K) hx

/-- Helper for Lemma 15.46.4: if a finite differential combination dies after base change to
`K / K_α`, then the underlying family is not `p`-independent over `K_α`. -/
lemma not_pIndependent_of_kaehler_map_zero_on_finite_support
    (α : A) {n : ℕ} (u : Fin n → K) (c : Fin n → K) (hc : c ≠ 0)
    (hzero :
      (kaehlerDifferentialMapTo α) (∑ i, c i • D (ZMod p) K (u i)) = 0) :
    ¬ PIndependent p (Kα α) K u := by
  intro hu
  have hlin : LinearIndependent K (D (Kα α) K ∘ u) :=
    (pIndependent_iff_linearIndependent_differentials
      (p := p) (k := Kα α) (K := K) u).1 hu
  have hsum : ∑ i, c i • D (Kα α) K (u i) = 0 := by
    -- Rewrite the vanished image as the same coefficient combination in `Ω[K⁄K_α]`.
    simpa [map_sum, map_smul, KaehlerDifferential.map_D] using hzero
  have hc_zero : ∀ i, c i = 0 := by
    -- Finite linear independence forces every coefficient in the vanished combination to vanish.
    rw [Fintype.linearIndependent_iff] at hlin
    exact hlin c hsum
  apply hc
  ext i
  exact hc_zero i

/-- Helper for Lemma 15.46.4: once `k` already contains `K^[p]`, every element of the mixed
compositum `k(K^p)` already lies in `k`. -/
lemma mem_base_of_mem_pPowerCompositum {k : Subfield K} (hk : K^[p] ≤ k) {x : K}
    (hx : x ∈ (pPowerCompositum p k K).toSubfield) :
    x ∈ k := by
  -- Collapse the mixed compositum to the base field and read the resulting membership there.
  rw [pPowerCompositum_eq_bot_of_frobeniusSubfield_le (p := p) (K := K) (k := k) hk] at hx
  change x ∈ ((⊥ : IntermediateField k K).toSubfield : Set K) at hx
  rcases hx with ⟨y, rfl⟩
  exact y.2

/-- Helper for Lemma 15.46.4: the fixed finite relation space of the `p`-restricted monomials of
`u`, reindexed by `e : (Fin n →₀ Fin p) ≃ Fin m`. -/
abbrev monomial_relation_submodule {n m : ℕ} (u : Fin n → K)
    (e : (Fin n →₀ Fin p) ≃ Fin m) : Submodule K (Fin m → K) :=
  (Fintype.linearCombination K (fun i : Fin m ↦ pMonomial p u (e.symm i))).ker

/-- Helper for Lemma 15.46.4: non-`p`-independence over a subfield containing `K^[p]`
produces a nonzero vector in the fixed finite monomial relation space whose coordinates lie in
that subfield. -/
lemma exists_nonzero_relation_vector_of_not_pIndependent
    {n m : ℕ} (u : Fin n → K) (e : (Fin n →₀ Fin p) ≃ Fin m)
    (k : Subfield K) (hk : K^[p] ≤ k) (hnot : ¬ PIndependent p k K u) :
    ∃ v ∈ ((monomial_relation_submodule (K := K) (p := p) u e).restrictScalars k ⊓
      k.vectorSubmodule m), v ≠ 0 := by
  classical
  -- Turn the failure of `p`-independence into a nontrivial finite monomial relation.
  change ¬ LinearIndependent (pPowerCompositum p k K) (pMonomial p u) at hnot
  rw [linearIndependent_iff] at hnot
  push_neg at hnot
  obtain ⟨l, hlrel, hlne⟩ := hnot
  let v : Fin m → K := fun i ↦ l (e.symm i)
  have hv_rel :
      (Fintype.linearCombination K (fun i : Fin m ↦ pMonomial p u (e.symm i))) v = 0 := by
    -- Reindex the relation from the monomial exponent type to `Fin m`.
    rw [Fintype.linearCombination_apply]
    calc
      ∑ i : Fin m, v i • pMonomial p u (e.symm i)
          = ∑ j : (Fin n →₀ Fin p), (l j : K) • pMonomial p u j := by
              exact Fintype.sum_equiv e.symm
                (fun i : Fin m ↦ v i • pMonomial p u (e.symm i))
                (fun j : Fin n →₀ Fin p ↦ (l j : K) • pMonomial p u j)
                (by intro i; simp [v])
      _ = l.sum (fun j a ↦ (a : K) • pMonomial p u j) := by
            symm
            exact Finsupp.sum_fintype l
              (fun j a ↦ (a : K) • pMonomial p u j) (by intro j; simp)
      _ = 0 := by
            simpa [Finsupp.linearCombination] using hlrel
  have hv_base : v ∈ k.vectorSubmodule m := by
    -- Each coefficient lies in `k` because `k(K^p) = k` under the standing hypothesis.
    rw [Subfield.mem_vectorSubmodule_iff]
    intro i
    exact mem_base_of_mem_pPowerCompositum (p := p) (K := K) (k := k) hk <| by
      simpa [v] using (l (e.symm i)).2
  have hv_ne : v ≠ 0 := by
    -- Reindexing the nonzero relation vector along `e` preserves nontriviality.
    intro hv_zero
    apply hlne
    ext j
    simpa [v] using congrFun hv_zero (e j)
  refine ⟨v, ?_, hv_ne⟩
  constructor
  · exact hv_rel
  · exact hv_base

-- Proof sketch: choose a `p`-basis of `K` over `𝔽_p` using Lemma `15.46.2`, identify an element of
-- the intersection of all kernels with a finite linear relation over every `K_α`, and apply the
-- directed-intersection criterion of Lemma `15.46.3` to force the coefficients into `K^p`, where
-- Lemma `15.46.2` rules out any nontrivial relation.
/-- Lemma 15.46.4 (1): if the subfields `K_α` intersect in `K^p` and are downward directed as a
nonempty family, then the intersection of the kernels of the canonical maps
`Ω[K⁄𝔽_p] → Ω[K⁄K_α]` is zero. -/
theorem iInf_ker_kaehlerDifferentialMap_eq_bot
    (h_nonempty : Nonempty A) (h_inter : K^[p] = ⨅ α, Kα α) (h_directed : Directed (· ≥ ·) Kα) :
    (⨅ α, LinearMap.ker (kaehlerDifferentialMapTo α)) = ⊥ := by
  classical
  letI : Nonempty A := h_nonempty
  rw [Submodule.eq_bot_iff]
  intro ω hω
  by_contra hω_ne
  obtain ⟨ι, x, hx⟩ := exists_isPBasis (p := p) (k := ZMod p) (K := K)
  obtain ⟨n, y, c, -, hc_ne, hω_coords, hlin⟩ :=
    reindex_pbasis_coordinate_support (p := p) (K := K) x hx hω_ne
  let u : Fin n → K := fun i ↦ x (y i)
  have hω_zero : ∀ α : A, (kaehlerDifferentialMapTo α) ω = 0 :=
    (mem_iInf_ker_kaehlerDifferentialMapTo_iff (Kα := Kα) (p := p) (K := K)).1 hω
  have hu_pIndependent : PIndependent p (ZMod p) K u := by
    -- The chosen `p`-basis subfamily stays `p`-independent over `𝔽_p`.
    exact (pIndependent_iff_linearIndependent_differentials
      (p := p) (k := ZMod p) (K := K) u).2 <| by
        simpa [u, Function.comp] using hlin
  let m : ℕ := Fintype.card (Fin n →₀ Fin p)
  let e : (Fin n →₀ Fin p) ≃ Fin m := Fintype.equivFin (Fin n →₀ Fin p)
  let relationMap : (Fin m → K) →ₗ[K] K :=
    Fintype.linearCombination K (fun i : Fin m ↦ pMonomial p u (e.symm i))
  let V : Submodule K (Fin m → K) := LinearMap.ker relationMap
  have hfamily :
      ∀ α,
        ∃ v ∈ V.restrictScalars (Kα α) ⊓ (Kα α).vectorSubmodule m, v ≠ 0 := by
    intro α
    have hkα : K^[p] ≤ Kα α := by
      intro z hz
      have hz' : z ∈ ⨅ β, Kα β := by
        simpa [h_inter] using hz
      exact (Subfield.mem_iInf.1 hz') α
    have hmap_zero :
        (kaehlerDifferentialMapTo α) (∑ i, c i • D (ZMod p) K (u i)) = 0 := by
      -- Rewrite the original kernel condition through the chosen finite support coordinates.
      simpa [u, hω_coords] using hω_zero α
    have hu_not :
        ¬ PIndependent p (Kα α) K u :=
      not_pIndependent_of_kaehler_map_zero_on_finite_support
        (Kα := Kα) (p := p) (K := K) α u c hc_ne hmap_zero
    simpa [V, relationMap, m, e] using
      exists_nonzero_relation_vector_of_not_pIndependent
        (K := K) (p := p) u e (Kα α) hkα hu_not
  obtain ⟨v, hv, hv_ne⟩ :=
    (exists_nonzero_vector_in_base_subfield_iff_forall_exists_nonzero_vector_in_family
      (k := K^[p]) (Kα := Kα) h_inter h_directed V).2 hfamily
  let l0 : Fin m → pPowerCompositum p (ZMod p) K := fun i ↦
    ⟨v i,
      mem_pPowerCompositum_zmod_of_mem_frobeniusSubfield (p := p) (K := K) <|
        (Subfield.mem_vectorSubmodule_iff (K^[p])).1 hv.2 i⟩
  have hl0_rel :
      ∑ i : Fin m, (l0 i : K) • pMonomial p u (e.symm i) = 0 := by
    -- The descended vector remains in the fixed relation kernel over `K`.
    simpa [relationMap, V, l0, Fintype.linearCombination_apply] using hv.1
  have hu_fin :
      LinearIndependent (pPowerCompositum p (ZMod p) K)
        (fun i : Fin m ↦ pMonomial p u (e.symm i)) := by
    -- Reindex the monomial family so the finite relation criterion can be applied directly.
    exact hu_pIndependent.comp e.symm e.symm.injective
  have hl0_zero : ∀ i, l0 i = 0 := by
    rw [Fintype.linearIndependent_iff] at hu_fin
    exact hu_fin l0 hl0_rel
  apply hv_ne
  ext i
  -- Coerce the vanished coefficients back to `K` to contradict nontriviality of `v`.
  show v i = 0
  have hi := congrArg (fun z : pPowerCompositum p (ZMod p) K ↦ (z : K)) (hl0_zero i)
  simpa [l0] using hi

/-- Helper for Lemma 15.46.4: the initial stage in a finite `p`-root tower is the base field. -/
private theorem finiteGeneratorStage_zero_eq_bot
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (α : Fin n → E) :
    finiteGeneratorStage F α (0 : Fin (n + 1)) = ⊥ := by
  -- At stage `0` the prefix is empty, so no new generators have been adjoined.
  ext x
  simp [finiteGeneratorStage, finiteGeneratorPrefix]

/-- Helper for Lemma 15.46.4: a successor stage in the finite `p`-root tower is obtained by
adjoining the new chosen generator to the previous stage. -/
private theorem finiteGeneratorStage_succ_eq_adjoin
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (α : Fin n → E) (i : Fin n) :
    finiteGeneratorStage F α (Fin.succ i) =
      (IntermediateField.adjoin (finiteGeneratorStage F α (Fin.castSucc i))
        ({α i} : Set E)).restrictScalars F := by
  have hprefix :
      finiteGeneratorPrefix α (Fin.succ i) =
        Set.insert (α i) (finiteGeneratorPrefix α (Fin.castSucc i)) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      by_cases hji : j = i
      · left
        simpa [hji]
      · right
        exact ⟨j, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) fun h => hji (Fin.ext h), rfl⟩
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨i, Nat.lt_succ_self i.1, rfl⟩
      · rcases hx with ⟨j, hj, rfl⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
  have hprev :
      finiteGeneratorStage F α (Fin.castSucc i) ≤ finiteGeneratorStage F α (Fin.succ i) := by
    -- The previous stage is generated by a subset of the successor-stage generators.
    rw [finiteGeneratorStage, finiteGeneratorStage, hprefix]
    refine IntermediateField.adjoin_le_iff.2 ?_
    intro x hx
    exact IntermediateField.subset_adjoin F
      (Set.insert (α i) (finiteGeneratorPrefix α (Fin.castSucc i))) (Or.inr hx)
  apply le_antisymm
  · intro x hx
    rw [finiteGeneratorStage, hprefix] at hx
    change x ∈ IntermediateField.adjoin (finiteGeneratorStage F α (Fin.castSucc i))
      ({α i} : Set E)
    -- Generate the successor stage from the base field and the inserted prefix, then move the
    -- old-prefix generators into the previous stage.
    refine IntermediateField.adjoin_induction (F := F)
        (s := Set.insert (α i) (finiteGeneratorPrefix α (Fin.castSucc i)))
        (p := fun y _ ↦
          y ∈ IntermediateField.adjoin (finiteGeneratorStage F α (Fin.castSucc i))
            ({α i} : Set E)) ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl | hy
      · exact IntermediateField.mem_adjoin_simple_self (finiteGeneratorStage F α (Fin.castSucc i))
          (α i)
      · have hy_prev : y ∈ finiteGeneratorStage F α (Fin.castSucc i) :=
          IntermediateField.subset_adjoin F (finiteGeneratorPrefix α (Fin.castSucc i)) hy
        exact IntermediateField.algebraMap_mem
          (IntermediateField.adjoin (finiteGeneratorStage F α (Fin.castSucc i)) ({α i} : Set E))
          ⟨y, hy_prev⟩
    · intro a
      have ha_prev : algebraMap F E a ∈ finiteGeneratorStage F α (Fin.castSucc i) :=
        IntermediateField.algebraMap_mem (finiteGeneratorStage F α (Fin.castSucc i)) a
      exact IntermediateField.algebraMap_mem
        (IntermediateField.adjoin (finiteGeneratorStage F α (Fin.castSucc i)) ({α i} : Set E))
        ⟨algebraMap F E a, ha_prev⟩
    · intro y z _ _ hy hz
      exact IntermediateField.add_mem _ hy hz
    · intro y _ hy
      exact IntermediateField.inv_mem _ hy
    · intro y z _ _ hy hz
      exact IntermediateField.mul_mem _ hy hz
  · intro x hx
    change x ∈ IntermediateField.adjoin (finiteGeneratorStage F α (Fin.castSucc i))
      ({α i} : Set E) at hx
    rw [finiteGeneratorStage, hprefix]
    -- Conversely, adjoin over the previous stage stays inside the field generated by the inserted
    -- prefix because that field already contains both the previous stage and the new generator.
    refine IntermediateField.adjoin_induction
        (F := finiteGeneratorStage F α (Fin.castSucc i)) (s := ({α i} : Set E))
        (p := fun y _ ↦
          y ∈ IntermediateField.adjoin F
            (Set.insert (α i) (finiteGeneratorPrefix α (Fin.castSucc i)))) ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact IntermediateField.subset_adjoin F
        (Set.insert (α i) (finiteGeneratorPrefix α (Fin.castSucc i))) (Or.inl <| by
          simpa using hy)
    · intro a
      simpa [finiteGeneratorStage, hprefix] using hprev a.2
    · intro y z _ _ hy hz
      exact IntermediateField.add_mem _ hy hz
    · intro y _ hy
      exact IntermediateField.inv_mem _ hy
    · intro y z _ _ hy hz
      exact IntermediateField.mul_mem _ hy hz

-- Proof sketch: reduce along intermediate fields to the primitive-extension case, then treat the
-- separable and purely inseparable degree-`p` cases separately. In each case, a basis of `L` over
-- `K` adapted to a primitive generator shows that intersecting the composita `L^p K_α` recovers
-- exactly `L^p` because the coefficients intersect back to `K^p`.
section FiniteExtension

variable {L : Type w} [Field L] [Algebra K L] [FiniteDimensional K L] [CharP L p]

omit [CharP K p] [FiniteDimensional K L] in
/-- Helper for Lemma 15.46.4: the Frobenius subfield `L^[p]` is contained in each mixed
compositum `L^[p] K_α`. -/
lemma frobeniusSubfield_le_pPowerCompositum_toSubfield (α : A) :
    L^[p] ≤ (pPowerCompositum p ((Kα α).map (algebraMap K L)) L).toSubfield := by
  intro x hx
  -- The mixed compositum is an adjunction over the base field `(K_α)_L`, so it already contains
  -- every `p`th power from `L`.
  change x ∈ pPowerCompositum p ((Kα α).map (algebraMap K L)) L
  exact IntermediateField.subset_adjoin ((Kα α).map (algebraMap K L)) (L^[p] : Set L) hx

omit [CharP K p] [FiniteDimensional K L] in
/-- Helper for Lemma 15.46.4: in a simple extension `K⟮θ⟯`, taking `p`th powers replaces the
generator `θ` by `θ ^ p`. -/
lemma pow_mem_adjoin_simple_pth_power {θ y : L}
    (hy : y ∈ (K⟮θ⟯ : IntermediateField K L)) :
    y ^ p ∈ (K⟮θ ^ p⟯ : IntermediateField K L) := by
  -- Follow the source proof literally: `K(θ)` is built from `K` and `θ`, and Frobenius respects
  -- the field operations in characteristic `p`.
  refine IntermediateField.adjoin_induction (F := K) (s := ({θ} : Set L))
      (p := fun z _ ↦ z ^ p ∈ (K⟮θ ^ p⟯ : IntermediateField K L)) ?_ ?_ ?_ ?_ ?_ hy
  · intro z hz
    have hz' : z = θ := by simpa using hz
    simpa [hz'] using (IntermediateField.mem_adjoin_simple_self K (θ ^ p))
  · intro a
    simpa using (IntermediateField.algebraMap_mem (K⟮θ ^ p⟯ : IntermediateField K L) (a ^ p))
  · intro x y _ _ hx hy
    simpa [add_pow_char] using
      IntermediateField.add_mem (K⟮θ ^ p⟯ : IntermediateField K L) hx hy
  · intro x _ hx
    simpa [inv_pow] using
      IntermediateField.inv_mem (K⟮θ ^ p⟯ : IntermediateField K L) hx
  · intro x y _ _ hx hy
    simpa [mul_pow] using
      IntermediateField.mul_mem (K⟮θ ^ p⟯ : IntermediateField K L) hx hy

omit [CharP K p] [FiniteDimensional K L] in
/-- Helper for Lemma 15.46.4: if `θ` already generates `L / K`, then every `p`th power in `L`
lies in the simple extension generated by `θ ^ p`. -/
lemma frobeniusSubfield_le_adjoin_pth_power_of_generator_eq_top {θ : L}
    (hθ : (K⟮θ⟯ : IntermediateField K L) = ⊤) :
    L^[p] ≤ (K⟮θ ^ p⟯ : IntermediateField K L).toSubfield := by
  -- First express an arbitrary element of `L^[p]` as `y ^ p`, then apply the simple-extension
  -- Frobenius descent just proved.
  intro x hx
  rcases hx with ⟨y, rfl⟩
  have hy : y ∈ (K⟮θ⟯ : IntermediateField K L) := by
    simpa [hθ] using (show y ∈ (⊤ : IntermediateField K L) from by simp)
  exact pow_mem_adjoin_simple_pth_power (p := p) (K := K) (L := L) hy

/-- Helper for Lemma 15.46.4: for any family of base subfields, the Frobenius subfield of the
ambient extension lies in the intersection of the corresponding mixed composita. -/
lemma frobeniusSubfield_le_iInf_pPowerCompositum_toSubfield
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E] [CharP E p]
    {B : Type*} (Fα : B → Subfield F) :
    E^[p] ≤ ⨅ α, (pPowerCompositum p ((Fα α).map (algebraMap F E)) E).toSubfield := by
  intro x hx
  rw [Subfield.mem_iInf]
  intro α
  -- Read the intersection pointwise and then use the standard inclusion of `E^[p]` into each
  -- mixed compositum.
  exact frobeniusSubfield_le_pPowerCompositum_toSubfield
    (Kα := Fα) (p := p) (K := F) (L := E) α hx

/-- Helper for Lemma 15.46.4: in a simple extension generated by a `p`th root, every `p`th power
already lies in the base field. -/
lemma frobeniusSubfield_le_bot_of_adjoin_simple_pth_power_mem
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E] [CharP E p]
    {θ : E} (hθpow : θ ^ p ∈ (⊥ : IntermediateField F E))
    (hθtop : (F⟮θ⟯ : IntermediateField F E) = ⊤) :
    E^[p] ≤ (⊥ : IntermediateField F E).toSubfield := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  have hy : y ∈ (F⟮θ⟯ : IntermediateField F E) := by
    simpa [hθtop] using (show y ∈ (⊤ : IntermediateField F E) from by simp)
  have hypow :
      y ^ p ∈ (F⟮θ ^ p⟯ : IntermediateField F E) :=
    pow_mem_adjoin_simple_pth_power (p := p) (K := F) (L := E) hy
  have hbase : (F⟮θ ^ p⟯ : IntermediateField F E) = ⊥ := by
    -- Once the `p`th power of the generator is already in the base, adjoining it changes nothing.
    refine le_antisymm ?_ bot_le
    exact (IntermediateField.adjoin_simple_le_iff).2 hθpow
  simpa [hbase] using hypow

/-- Helper for Lemma 15.46.4: in a finite separable extension, the `p`th power of a primitive
generator still generates the whole extension over the base field. -/
lemma adjoin_pth_power_of_separable_powerBasis_eq_top [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) :
    K⟮pb.gen ^ p⟯ = ⊤ := by
  -- First show that the `p`th-power subfield lies in the simple extension generated by `pb.gen^p`.
  have hgen_top : (K⟮pb.gen⟯ : IntermediateField K L) = ⊤ := by
    exact IntermediateField.adjoin_eq_top_of_algebra (F := K) (S := ({pb.gen} : Set L))
      pb.adjoin_gen_eq_top
  have hpow :
      L^[p] ≤ (K⟮pb.gen ^ p⟯ : IntermediateField K L).toSubfield :=
    frobeniusSubfield_le_adjoin_pth_power_of_generator_eq_top
      (p := p) (K := K) (L := L) (θ := pb.gen) hgen_top
  -- Then separability collapses the extension once all `p`th powers already lie in the base.
  exact top_of_isSeparableOver_of_frobeniusSubfield_le
    (p := p) (k := K) (K := L) (K⟮pb.gen ^ p⟯) hpow

/-- Helper for Lemma 15.46.4: a finite separable extension admits a power basis whose generator
already lies in the Frobenius subfield. -/
lemma exists_powerBasis_generator_mem_frobeniusSubfield_of_separable
    {M : Type*} [Field M] [Algebra K M] [FiniteDimensional K M] [CharP M p]
    [Algebra.IsSeparable K M] :
    ∃ pb : PowerBasis K M, pb.gen ∈ M^[p] := by
  let pb₀ : PowerBasis K M := Field.powerBasisOfFiniteOfSeparable K M
  let θ : M := pb₀.gen ^ p
  have hθtop : K⟮θ⟯ = ⊤ := by
    -- Replace the original primitive generator by its `p`th power, which still generates the
    -- whole separable extension by the source normalization step just proved.
    simpa [θ, pb₀] using
      adjoin_pth_power_of_separable_powerBasis_eq_top
        (p := p) (K := K) (L := M) pb₀
  let pb₁ : PowerBasis K K⟮θ⟯ :=
    IntermediateField.adjoin.powerBasis (IsIntegral.of_finite K θ)
  let e : K⟮θ⟯ ≃ₐ[K] M := (IntermediateField.equivOfEq hθtop).trans IntermediateField.topEquiv
  let pb : PowerBasis K M := pb₁.map e
  refine ⟨pb, ?_⟩
  -- The transported generator is exactly `θ = pb₀.gen ^ p`, hence it lies in `M^[p]`.
  change e pb₁.gen ∈ M^[p]
  simpa [pb₁, e, θ] using (show θ ∈ M^[p] from ⟨pb₀.gen, rfl⟩)

omit [CharP K p] [FiniteDimensional K L] in
/-- Helper for Lemma 15.46.4: if a power basis over `K` has the same length as the
`K₀`-dimension of the extension, then every `K`-coordinate of an element already lies in the
smaller subfield `K₀`. -/
lemma powerBasis_repr_mem_subfield_of_finrank_eq
    {K₀ : Subfield K} (pb : PowerBasis K L)
    (hfinrank : Module.finrank K₀ L = pb.dim) (x : L) (i : Fin pb.dim) :
    pb.basis.repr x i ∈ K₀ := by
  -- The powers of the generator are a `K`-basis, so they remain linearly independent after
  -- restricting scalars to `K₀`.
  let hK : LinearIndependent K (fun j : Fin pb.dim ↦ pb.gen ^ (j : ℕ)) := by
    simpa [pb.basis_eq_pow] using pb.basis.linearIndependent
  have hK₀_injective : Function.Injective (fun r : K₀ ↦ r • (1 : K)) := by
    intro a b h
    exact Subtype.ext (by simpa using h)
  let hK₀ : LinearIndependent K₀ (fun j : Fin pb.dim ↦ pb.gen ^ (j : ℕ)) :=
    LinearIndependent.restrict_scalars (K := K) (R := K₀) hK₀_injective hK
  haveI : Nonempty (Fin pb.dim) := ⟨⟨0, pb.dim_pos⟩⟩
  have hspan : Submodule.span K₀ (Set.range (fun j : Fin pb.dim ↦ pb.gen ^ (j : ℕ))) = ⊤ := by
    -- Equal cardinality with the smaller-base finrank upgrades linear independence to spanning.
    refine LinearIndependent.span_eq_top_of_card_eq_finrank hK₀ ?_
    simpa [hfinrank]
  have hxspan : x ∈ Submodule.span K₀ (Set.range (fun j : Fin pb.dim ↦ pb.gen ^ (j : ℕ))) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K₀).1 hxspan
  have hc_basis : ∑ j, (((c j : K₀) : K)) • pb.basis j = x := by
    -- Rewrite the smaller-base expansion in the ambient power basis.
    simpa [pb.basis_eq_pow] using hc
  have hrepr : pb.basis.repr x i = ((c i : K₀) : K) := by
    -- Read the `i`-th basis coordinate of that expansion.
    rw [← hc_basis]
    simpa using congrFun (pb.basis.repr_sum_self (fun j ↦ ((c j : K₀) : K))) i
  -- The recovered coordinate is visibly the image of an element of the smaller subfield.
  rw [hrepr]
  exact (c i).2

omit [CharP K p] [Algebra K L] [FiniteDimensional K L] in
/-- Helper for Lemma 15.46.4: after a tower `K ⟶ M ⟶ L`, the mixed compositum built from the
image of `M^[p]K_α` has the same underlying subfield of `L` as the mixed compositum built
directly from the image of `K_α`. -/
lemma pPowerCompositum_map_pPowerCompositum_toSubfield_eq (α : A)
    {M : Type*} [Field M] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [CharP M p] :
    (pPowerCompositum p
        (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map (algebraMap M L))
        L).toSubfield =
      (pPowerCompositum p ((Kα α).map (algebraMap K L)) L).toSubfield := by
  -- Compare the two carriers directly. The left base field is the image of
  -- `M^[p]K_α` in `L`, so every one of its generators already lies in the right compositum.
  -- Conversely, the direct image of `K_α` in `L` already lands in the mapped base on the left.
  ext x
  constructor
  · intro hx
    change x ∈ pPowerCompositum p ((Kα α).map (algebraMap K L)) L
    have hbase :
        (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map
            (algebraMap M L)) ≤
          (pPowerCompositum p ((Kα α).map (algebraMap K L)) L).toSubfield := by
      intro y hy
      rcases Subfield.mem_map.mp hy with ⟨z, hz, rfl⟩
      change algebraMap M L z ∈ pPowerCompositum p ((Kα α).map (algebraMap K L)) L
      -- Descend membership in `M^[p]K_α` to the generators `M^[p]` and `(K_α)_M`.
      refine IntermediateField.adjoin_induction (F := (Kα α).map (algebraMap K M))
          (s := (M^[p] : Set M))
          (p := fun w _ ↦
            algebraMap M L w ∈ pPowerCompositum p ((Kα α).map (algebraMap K L)) L) ?_ ?_ ?_ ?_ ?_
          hz
      · intro w hw
        rcases hw with ⟨u, rfl⟩
        exact IntermediateField.subset_adjoin ((Kα α).map (algebraMap K L)) (L^[p] : Set L) <| by
          refine ⟨algebraMap M L u, ?_⟩
          simpa using (RingHom.map_frobenius (algebraMap M L) p u).symm
      · intro w
        rcases Subfield.mem_map.mp w.2 with ⟨u, hu, hw⟩
        have huL : algebraMap K L u ∈ (Kα α).map (algebraMap K L) :=
          Subfield.mem_map.mpr ⟨u, hu, rfl⟩
        have huMem : algebraMap K L u ∈ pPowerCompositum p ((Kα α).map (algebraMap K L)) L :=
          IntermediateField.algebraMap_mem
            (pPowerCompositum p ((Kα α).map (algebraMap K L)) L)
            ⟨algebraMap K L u, huL⟩
        simpa [hw, IsScalarTower.algebraMap_eq K M L] using huMem
      · intro w₁ w₂ _ _ hw₁ hw₂
        simpa using IntermediateField.add_mem
          (pPowerCompositum p ((Kα α).map (algebraMap K L)) L) hw₁ hw₂
      · intro w _ hw
        simpa using IntermediateField.inv_mem
          (pPowerCompositum p ((Kα α).map (algebraMap K L)) L) hw
      · intro w₁ w₂ _ _ hw₁ hw₂
        simpa using IntermediateField.mul_mem
          (pPowerCompositum p ((Kα α).map (algebraMap K L)) L) hw₁ hw₂
    -- Now run the final induction on the left-hand compositum in `L`.
    refine IntermediateField.adjoin_induction
        (F := (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map
          (algebraMap M L)))
        (s := (L^[p] : Set L))
        (p := fun y _ ↦ y ∈ pPowerCompositum p ((Kα α).map (algebraMap K L)) L) ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact IntermediateField.subset_adjoin ((Kα α).map (algebraMap K L)) (L^[p] : Set L) hy
    · intro y
      exact hbase y.2
    · intro y₁ y₂ _ _ hy₁ hy₂
      exact IntermediateField.add_mem _ hy₁ hy₂
    · intro y _ hy
      exact IntermediateField.inv_mem _ hy
    · intro y₁ y₂ _ _ hy₁ hy₂
      exact IntermediateField.mul_mem _ hy₁ hy₂
  · intro hx
    change x ∈ pPowerCompositum p
      (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map (algebraMap M L))
      L
    have hbase :
        (Kα α).map (algebraMap K L) ≤
          (pPowerCompositum p
            (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map
              (algebraMap M L))
            L).toSubfield := by
      intro y hy
      rcases Subfield.mem_map.mp hy with ⟨u, hu, rfl⟩
      have huBase :
          algebraMap K L u ∈
            (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map
              (algebraMap M L)) := by
        refine Subfield.mem_map.mpr ?_
        refine ⟨algebraMap K M u, ?_, by simp [IsScalarTower.algebraMap_eq K M L]⟩
        have huM : algebraMap K M u ∈ pPowerCompositum p ((Kα α).map (algebraMap K M)) M :=
          IntermediateField.algebraMap_mem
            (pPowerCompositum p ((Kα α).map (algebraMap K M)) M)
            ⟨algebraMap K M u, Subfield.mem_map.mpr ⟨u, hu, rfl⟩⟩
        simpa using huM
      simpa using IntermediateField.algebraMap_mem
        (pPowerCompositum p
          (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map
            (algebraMap M L))
          L)
        ⟨algebraMap K L u, huBase⟩
    -- The right-hand compositum is generated by `(K_α)_L` and `L^[p]`, and both already lie on
    -- the left after the base-field inclusion above.
    refine IntermediateField.adjoin_induction (F := (Kα α).map (algebraMap K L))
        (s := (L^[p] : Set L))
        (p := fun y _ ↦
          y ∈ pPowerCompositum p
            (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map
              (algebraMap M L))
            L) ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact IntermediateField.subset_adjoin
        (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map
          (algebraMap M L))
        (L^[p] : Set L) hy
    · intro y
      exact hbase y.2
    · intro y₁ y₂ _ _ hy₁ hy₂
      exact IntermediateField.add_mem _ hy₁ hy₂
    · intro y _ hy
      exact IntermediateField.inv_mem _ hy
    · intro y₁ y₂ _ _ hy₁ hy₂
      exact IntermediateField.mul_mem _ hy₁ hy₂

/-- Helper for Lemma 15.46.4: once the induced tower family `M^[p]K_α` is used as the base for
`L / M`, the resulting intersection statement rewrites to the original family over `K`. -/
lemma frobeniusSubfield_eq_iInf_pPowerCompositum_of_tower
    {M : Type*} [Field M] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [CharP M p]
    (hL :
      L^[p] = ⨅ α,
        (pPowerCompositum p
          (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map
            (algebraMap M L))
          L).toSubfield) :
    L^[p] = ⨅ α, (pPowerCompositum p ((Kα α).map (algebraMap K L)) L).toSubfield := by
  -- Rewrite the tower family pointwise using the carrier equality just proved.
  have hrewrite :
      ∀ α : A,
        (pPowerCompositum p
          (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map
            (algebraMap M L))
          L).toSubfield =
          (pPowerCompositum p ((Kα α).map (algebraMap K L)) L).toSubfield := by
    intro α
    exact pPowerCompositum_map_pPowerCompositum_toSubfield_eq
      (Kα := Kα) (p := p) (K := K) (L := L) (M := M) α
  calc
    L^[p] = ⨅ α,
        (pPowerCompositum p
          (((pPowerCompositum p ((Kα α).map (algebraMap K M)) M).toSubfield).map
            (algebraMap M L))
          L).toSubfield := hL
    _ = ⨅ α, (pPowerCompositum p ((Kα α).map (algebraMap K L)) L).toSubfield := by
      ext x
      rw [Subfield.mem_iInf, Subfield.mem_iInf]
      constructor
      · intro hx α
        rw [← hrewrite α]
        exact hx α
      · intro hx α
        rw [hrewrite α]
        exact hx α

/-- Lemma 15.46.4 (2): for every finite extension `L / K` over a field `K` of characteristic `p`,
the `p`-th-power subfield `L^p` is the
intersection of the composita `L^p K_α` inside `L` for a downward directed family `(K_α)` with
intersection `K^p`. -/
theorem frobeniusSubfield_eq_iInf_pPowerCompositum_of_finiteExtension
    (h_inter : K^[p] = ⨅ α, Kα α) (h_directed : Directed (· ≥ ·) Kα) :
    L^[p] = ⨅ α, (pPowerCompositum p ((Kα α).map (algebraMap K L)) L).toSubfield := by
  apply le_antisymm
  · intro x hx
    rw [Subfield.mem_iInf]
    intro α
    exact frobeniusSubfield_le_pPowerCompositum_toSubfield (Kα := Kα) (p := p) (K := K)
      (L := L) α hx
  · -- Route correction: the reverse inclusion is the coefficient-descent part of the source proof.
    letI : Algebra K ↥(separableClosure K L) := inferInstance
    letI : Algebra ↥(separableClosure K L) L := inferInstance
    letI : IsScalarTower K ↥(separableClosure K L) L := inferInstance
    letI : FiniteDimensional K ↥(separableClosure K L) :=
      IntermediateField.finiteDimensional_left (separableClosure K L)
    letI : Module.Finite ↥(separableClosure K L) L :=
      FiniteDimensional.right K ↥(separableClosure K L) L
    letI : FiniteDimensional ↥(separableClosure K L) L := by infer_instance
    let Mα : A → Subfield ↥(separableClosure K L) := fun α ↦
      (pPowerCompositum p ((Kα α).map (algebraMap K ↥(separableClosure K L)))
        ↥(separableClosure K L)).toSubfield
    have hM_sep : Algebra.IsSeparable K ↥(separableClosure K L) :=
      separableClosure.isSeparable K L
    have hML_pure : IsPurelyInseparable ↥(separableClosure K L) L :=
      separableClosure.isPurelyInseparable K L
    obtain ⟨n, β, hβ⟩ :=
      exists_pthRoot_tower_of_finite_purelyInseparable
        (F := ↥(separableClosure K L)) (E := L) p
    have hM_inter :
        (↥(separableClosure K L))^[p] = ⨅ α, Mα α := by
      refine le_antisymm ?_ ?_
      · -- The easy inclusion is the universal one: every `p`th power lies in every mixed
        -- compositum by construction.
        simpa [Mα] using
          (frobeniusSubfield_le_iInf_pPowerCompositum_toSubfield
            (p := p) (F := K) (E := ↥(separableClosure K L)) Kα)
      · -- TODO: prove the reverse inclusion by choosing a power basis of `M / K` whose generator
        -- lies in `M^[p]`, rewriting each `Mα α` as a simple adjoin over `(Kα α).map _`, and
        -- descending the fixed coordinates of an element of `⋂ α, Mα α` through `h_inter`.
        sorry
    have hL_over_M :
        L^[p] = ⨅ α,
          (pPowerCompositum p (((Mα α).map
            (algebraMap ↥(separableClosure K L) L))) L).toSubfield := by
      refine le_antisymm ?_ ?_
      · -- Again the forward inclusion is the formal inclusion of `L^[p]` into each mixed
        -- compositum over the stagewise base fields `Mα α`.
        simpa using
          (frobeniusSubfield_le_iInf_pPowerCompositum_toSubfield
            (p := p) (F := ↥(separableClosure K L)) (E := L) Mα)
      · -- TODO: iterate the prime-step source argument along the finite `p`-root tower `β`.
        -- The new helper `frobeniusSubfield_le_bot_of_adjoin_simple_pth_power_mem` packages the
        -- source fact that each successor stage has no new `p`th powers beyond the previous one;
        -- what still remains is the stagewise reverse inclusion against the family `Mα`.
        sorry
    -- Rewrite the tower family back to the original family once the two source-faithful stages
    -- above are available.
    intro x hx
    -- Consume the tower rewrite as an equality of subfields, then read the desired membership
    -- from the rewritten intersection statement.
    have hrewrite :=
      frobeniusSubfield_eq_iInf_pPowerCompositum_of_tower
        (Kα := Kα) (p := p) (K := K) (L := L) (M := ↥(separableClosure K L)) hL_over_M
    rw [← hrewrite] at hx
    exact hx

end FiniteExtension

end
