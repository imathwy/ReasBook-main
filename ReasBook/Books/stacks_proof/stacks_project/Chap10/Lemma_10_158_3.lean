import StacksProject_2024.Chap10.Lemma_10_158_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: purely inseparable finite field extensions in characteristic `p`, measured by the
  canonical universal derivation on Kähler differentials;
- sampled owner declarations:
  `KaehlerDifferential.D`,
  `kaehlerDifferential_eq_zero_iff_exists_pth_root`,
  `IntermediateField.adjoin`,
  `IntermediateField.relfinrank`;
- best owner abstraction: the source-facing generated intermediate field
  `IntermediateField.adjoin k (Set.range roots)`, together with the owner derivation
  `KaehlerDifferential.D (ZMod p) k`;
- primitive data: the family `a : Fin n → k`, the chosen roots `roots : Fin n → K`, and the
  equations `roots i ^ p = algebraMap k K (a i)`;
- derived API: the degree computation for the generated extension under linear independence of the
  differentials.

Source/core/bridge triage:
- `source-facing`: `relfinrank_adjoin_pthRoots_eq_pow`;
- `core/canonical`: `KaehlerDifferential.D (ZMod p) k`, `IntermediateField.adjoin`, and
  `IntermediateField.relfinrank`;
- `bridge/view`: Lemma `10.158.2`, which converts vanishing of a differential into existence of a
  `p`th root and is the canonical chapter input for the inductive degree-counting argument.
-/

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p n : ℕ} [Fact p.Prime] [CharP k p]
variable [Algebra (ZMod p) k]

/-- Helper for Lemma 10.158.3: restricting an independent family of differentials to the prefix
indexed by `Fin n` preserves linear independence. -/
lemma linearIndependent_differentials_castSucc
    {a : Fin (n + 1) → k}
    (hd : LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    LinearIndependent k
      (fun i : Fin n ↦ KaehlerDifferential.D (ZMod p) k (a i.castSucc)) := by
  -- The prefix family is obtained by composing with the canonical embedding `Fin n ↪ Fin (n + 1)`.
  simpa using hd.comp Fin.castSuccEmb Fin.castSuccEmb.injective

/-- Helper for Lemma 10.158.3: the differential of the last element in an independent family is
not in the span of the earlier differentials. -/
lemma last_differential_not_mem_span_prefix
    (a : Fin (n + 1) → k)
    (hd : LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    KaehlerDifferential.D (ZMod p) k (a (Fin.last n)) ∉
      Submodule.span k
        (Set.range fun i : Fin n ↦ KaehlerDifferential.D (ZMod p) k (a i.castSucc)) := by
  have himage :
      (fun i : Fin (n + 1) ↦ KaehlerDifferential.D (ZMod p) k (a i)) ''
          {i : Fin (n + 1) | ↑i < n} =
        Set.range fun i : Fin n ↦ KaehlerDifferential.D (ZMod p) k (a i.castSucc) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, i.is_lt, rfl⟩
  have hlast : (Fin.last n : Fin (n + 1)) ∉ {i : Fin (n + 1) | ↑i < n} := by
    simp
  -- Apply the standard span-exclusion criterion to the last index.
  rw [← himage]
  exact hd.notMem_span_image (s := {i : Fin (n + 1) | ↑i < n}) hlast

/-- Helper for Lemma 10.158.3: adjoining the last chosen root after the prefix field is the same
as adjoining the whole `Fin.snoc` family at once over `k`. -/
lemma adjoin_range_succ_eq_restrictScalars_adjoin_singleton
    (roots₀ : Fin n → K) (β : K) :
    IntermediateField.adjoin k (Set.range (Fin.snoc roots₀ β)) =
      (IntermediateField.adjoin (IntermediateField.adjoin k (Set.range roots₀))
        ({β} : Set K)).restrictScalars k := by
  -- Rewrite the `Fin.snoc` range as the union of the prefix range with the last root.
  rw [Fin.range_snoc]
  calc
    IntermediateField.adjoin k (insert β (Set.range roots₀)) =
        IntermediateField.adjoin k ((Set.range roots₀) ∪ ({β} : Set K)) := by
          congr 1
          ext x
          simp [Set.mem_insert_iff]
    _ = IntermediateField.adjoin k (Set.range roots₀) ⊔ IntermediateField.adjoin k ({β} : Set K) := by
          rw [IntermediateField.adjoin_union]
    _ =
        (IntermediateField.adjoin (IntermediateField.adjoin k (Set.range roots₀))
          ({β} : Set K)).restrictScalars k := by
            symm
            simpa using
              (IntermediateField.restrictScalars_adjoin_eq_sup (F := k) (E := K)
                (IntermediateField.adjoin k (Set.range roots₀)) ({β} : Set K))

/-- Helper for Lemma 10.158.3: adjoining one chosen `p`th root over a field where the base element
is not already a `p`th power gives relative degree `p`. -/
lemma finrank_adjoin_singleton_eq_prime
    (L : IntermediateField k K) (β : K) (a : L)
    (hβ : β ^ p = algebraMap L K a)
    (hnot : ¬ ∃ b : L, b ^ p = a) :
    Module.finrank L (IntermediateField.adjoin L ({β} : Set K)) = p := by
  have hβ_integral_pow : IsIntegral L (β ^ p) := by
    rw [hβ]
    exact isIntegral_algebraMap
  have hβ_integral : IsIntegral L β :=
    IsIntegral.of_pow (show 0 < p by exact (Fact.out : Nat.Prime p).pos) hβ_integral_pow
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C a) := by
    -- The nonexistence of a `p`th root in `L` is exactly the irreducibility criterion.
    refine X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p) ?_
    intro b hb
    exact hnot ⟨b, hb⟩
  have hroot : Polynomial.aeval β (Polynomial.X ^ p - Polynomial.C a) = 0 := by
    -- The chosen generator `β` is a root of `X ^ p - a`.
    calc
      Polynomial.aeval β (Polynomial.X ^ p - Polynomial.C a) =
          β ^ p - algebraMap L K a := by
            simp [Polynomial.aeval_def]
      _ = 0 := by rw [hβ, sub_self]
  have hmin :
      minpoly L β = Polynomial.X ^ p - Polynomial.C a := by
    -- The minimal polynomial agrees with the irreducible polynomial having `β` as a root.
    refine (minpoly.eq_of_irreducible_of_monic hirr hroot ?_).symm
    exact Polynomial.monic_X_pow_sub_C a (Nat.Prime.ne_zero (Fact.out : p.Prime))
  -- The simple-adjunction degree is the degree of the minimal polynomial.
  rw [IntermediateField.adjoin.finrank hβ_integral, hmin]
  simp

/-- Helper for Lemma 10.158.3: linear independence of the differentials produces a derivation on
`k` that kills the prefix elements but not the last one. -/
lemma exists_separator_derivation_kills_prefix_not_last
    (a : Fin (n + 1) → k)
    (hd : LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    ∃ δ : Derivation (ZMod p) k k,
      (∀ i : Fin n, δ (a i.castSucc) = 0) ∧
      δ (a (Fin.last n)) ≠ 0 := by
  let W : Submodule k (KaehlerDifferential (ZMod p) k) :=
    Submodule.span k
      (Set.range fun i : Fin n ↦ KaehlerDifferential.D (ZMod p) k (a i.castSucc))
  have hnot :
      KaehlerDifferential.D (ZMod p) k (a (Fin.last n)) ∉ W := by
    -- The last differential lies outside the span of the prefix differentials.
    simpa [W] using last_differential_not_mem_span_prefix (k := k) (p := p) a hd
  rcases Submodule.exists_le_ker_of_notMem (p := W) hnot with ⟨φ, hφlast, hWker⟩
  refine ⟨LinearMap.compDer φ (KaehlerDifferential.D (ZMod p) k), ?_⟩
  constructor
  · intro i
    -- The separating functional vanishes on the prefix span, hence on each prefix differential.
    have hi :
        KaehlerDifferential.D (ZMod p) k (a i.castSucc) ∈ W :=
      Submodule.subset_span ⟨i, rfl⟩
    have hzero :
        φ (KaehlerDifferential.D (ZMod p) k (a i.castSucc)) = 0 :=
      hWker hi
    simpa using hzero
  · -- The last differential was chosen outside the kernel, so the induced derivation sees it.
    simpa using hφlast

/-- Helper for Lemma 10.158.3: a `ZMod p`-derivation kills every element that becomes a `p`th
power in its target field. -/
lemma derivation_apply_algebraMap_eq_zero_of_exists_pth_root
    {L : Type v} [Field L] [Algebra k L] [Algebra (ZMod p) L] [CharP L p]
    (D : Derivation (ZMod p) L L) {a : k} {b : L}
    (hb : b ^ p = algebraMap k L a) :
    D (algebraMap k L a) = 0 := by
  -- Differentiate the displayed `p`th-power relation in characteristic `p`.
  calc
    D (algebraMap k L a) = D (b ^ p) := by rw [hb]
    _ = 0 := by
      rw [Derivation.leibniz_pow]
      simp

/-- Helper for Lemma 10.158.3: the `p`th power of an element in the prefix root field lands back
in the intermediate field of `k` generated by Frobenius images and the prefix coefficients. -/
lemma pth_power_mem_separator_closure_of_mem_prefix_adjoin
    (a : Fin (n + 1) → k) (roots₀ : Fin n → K)
    (hroots₀ : ∀ i, roots₀ i ^ p = algebraMap k K (a i.castSucc))
    {x : K}
    (hx : x ∈ IntermediateField.adjoin k (Set.range roots₀)) :
    ∃ c : k,
      c ∈ IntermediateField.adjoin (ZMod p)
        (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun i : Fin n ↦ a i.castSucc)) ∧
      x ^ p = algebraMap k K c := by
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  let M : IntermediateField (ZMod p) k :=
    IntermediateField.adjoin (ZMod p)
      (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun i : Fin n ↦ a i.castSucc))
  have hprefix_mem : ∀ i : Fin n, a i.castSucc ∈ M := by
    intro i
    -- Each prefix coefficient is one of the explicit generators of `M`.
    exact IntermediateField.subset_adjoin (F := ZMod p)
      (S := (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun j : Fin n ↦ a j.castSucc)))
      (by exact Or.inr ⟨i, rfl⟩)
  have hfrobenius_mem : ∀ r : k, r ^ p ∈ M := by
    intro r
    -- Every `p`th power lies in the Frobenius range, hence among the generators of `M`.
    exact IntermediateField.subset_adjoin (F := ZMod p)
      (S := (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun j : Fin n ↦ a j.castSucc)))
      (by
        left
        simpa [frobenius_def] using RingHom.mem_fieldRange_self (frobenius k p) r)
  -- The controlled invariant is exactly the source proof's claim about `p`th powers in the
  -- prefix root field.
  refine IntermediateField.adjoin_induction (F := k) (s := Set.range roots₀)
    (p := fun y _ ↦ ∃ c : k, c ∈ M ∧ y ^ p = algebraMap k K c)
    ?_ ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    -- A generator root has `p`th power equal to the corresponding base coefficient.
    exact ⟨a i.castSucc, hprefix_mem i, hroots₀ i⟩
  · intro r
    -- Scalars contribute Frobenius generators.
    exact ⟨r ^ p, hfrobenius_mem r, by simpa using (map_pow (algebraMap k K) r p).symm⟩
  · intro y z hy hz ⟨cy, hcyM, hcy⟩ ⟨cz, hczM, hcz⟩
    -- The characteristic-`p` Frobenius turns addition into addition of `p`th powers.
    refine ⟨cy + cz, M.add_mem hcyM hczM, ?_⟩
    calc
      (y + z) ^ p = y ^ p + z ^ p := by simpa using (add_pow_char (p := p) y z)
      _ = algebraMap k K cy + algebraMap k K cz := by rw [hcy, hcz]
      _ = algebraMap k K (cy + cz) := by rw [map_add]
  · intro y hy ⟨cy, hcyM, hcy⟩
    -- Inversion stays inside the intermediate field, and `p`th powers commute with inversion.
    refine ⟨cy⁻¹, M.inv_mem hcyM, ?_⟩
    calc
      (y⁻¹) ^ p = (y ^ p)⁻¹ := by rw [inv_pow]
      _ = (algebraMap k K cy)⁻¹ := by rw [hcy]
      _ = algebraMap k K (cy⁻¹) := by rw [map_inv₀]
  · intro y z hy hz ⟨cy, hcyM, hcy⟩ ⟨cz, hczM, hcz⟩
    -- Multiplication stays compatible with the `p`th-power invariant.
    refine ⟨cy * cz, M.mul_mem hcyM hczM, ?_⟩
    calc
      (y * z) ^ p = y ^ p * z ^ p := by rw [mul_pow]
      _ = algebraMap k K cy * algebraMap k K cz := by rw [hcy, hcz]
      _ = algebraMap k K (cy * cz) := by rw [map_mul]

/-- Helper for Lemma 10.158.3: a separator derivation kills the intermediate field of `k`
generated by Frobenius images and the prefix coefficients. -/
lemma separator_derivation_eq_zero_on_separator_closure
    (a : Fin (n + 1) → k) (δ : Derivation (ZMod p) k k)
    (hδprefix : ∀ i : Fin n, δ (a i.castSucc) = 0)
    {x : k}
    (hx : x ∈ IntermediateField.adjoin (ZMod p)
      (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun i : Fin n ↦ a i.castSucc))) :
    δ x = 0 := by
  -- The source proof differentiates only inside `k`, so we keep the derivation on the
  -- Frobenius-plus-prefix closure there.
  refine IntermediateField.adjoin_induction (F := ZMod p)
    (s := (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun i : Fin n ↦ a i.castSucc)))
    (p := fun y _ ↦ δ y = 0)
    ?_ ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · rcases RingHom.mem_fieldRange.mp hy with ⟨z, rfl⟩
      -- Frobenius generators are `p`th powers, and derivations kill those in characteristic `p`.
      rw [frobenius_def, Derivation.leibniz_pow]
      simp
    · rcases hy with ⟨i, rfl⟩
      -- The separator derivation was chosen to vanish on each prefix coefficient.
      exact hδprefix i
  · intro r
    -- Derivations vanish on the scalar image of the prime field.
    simpa using δ.map_algebraMap r
  · intro y z hy hz hδy hδz
    -- Zero is preserved under addition.
    rw [δ.map_add, hδy, hδz, add_zero]
  · intro y hy hδy
    -- Zero is preserved under inversion inside the field.
    rw [δ.leibniz_inv, hδy]
    simp
  · intro y z hy hz hδy hδz
    -- Zero is preserved under multiplication.
    rw [δ.leibniz, hδy, hδz]
    simp

/-- Helper for Lemma 10.158.3: in the successor step, the last base element does not become a
`p`th power in the prefix field generated by the earlier chosen roots. -/
lemma last_root_not_pth_power_in_prefix
    (a : Fin (n + 1) → k) (roots₀ : Fin n → K)
    (hroots₀ : ∀ i, roots₀ i ^ p = algebraMap k K (a i.castSucc))
    (hd : LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    ¬ ∃ b : IntermediateField.adjoin k (Set.range roots₀),
      b ^ p =
        algebraMap k (IntermediateField.adjoin k (Set.range roots₀)) (a (Fin.last n)) := by
  rcases exists_separator_derivation_kills_prefix_not_last (k := k) (p := p) a hd with
    ⟨δ, hδprefix, hδlast⟩
  let M : IntermediateField (ZMod p) k :=
    IntermediateField.adjoin (ZMod p)
      (((frobenius k p).fieldRange : Set k) ∪ Set.range (fun i : Fin n ↦ a i.castSucc))
  intro hb
  rcases hb with ⟨b, hb⟩
  have hbK : (b : K) ^ p = algebraMap k K (a (Fin.last n)) := by
    -- Coerce the hypothetical `p`th-root witness from the prefix field to the ambient field.
    exact congrArg Subtype.val hb
  obtain ⟨c, hcM, hcpow⟩ :=
    pth_power_mem_separator_closure_of_mem_prefix_adjoin
      (k := k) (K := K) (p := p) a roots₀ hroots₀ b.2
  have hlast_mem : a (Fin.last n) ∈ M := by
    -- The source contradiction comes from pushing the witness back into the controlled subfield
    -- of `k`, where the separator derivation is already defined.
    have hmap_eq : algebraMap k K c = algebraMap k K (a (Fin.last n)) := by
      rw [← hcpow, hbK]
    exact hmap_eq |> (algebraMap k K).injective |> fun h => h ▸ hcM
  have hδzero :
      δ (a (Fin.last n)) = 0 :=
    separator_derivation_eq_zero_on_separator_closure
      (k := k) (p := p) a δ hδprefix hlast_mem
  -- Route correction: instead of extending `δ` to the prefix field, we keep it on `k` and use the
  -- Frobenius-closure argument from the source proof to force `a_last` into the kernel.
  exact hδlast hδzero

-- Proof sketch: argue by induction on `n`. For the induction step, compare
-- `k(a_1^(1/p), ..., a_(n-1)^(1/p))` with the field obtained by adjoining one more chosen root of
-- `a_n`. If `a_n` became a `p`th power in the smaller field, Lemma `10.158.2` would force
-- `KaehlerDifferential.D (ZMod p) k (a n)` to lie in the `k`-span of the earlier differentials,
-- contradicting linear independence. Hence each step multiplies the relative degree by `p`.
/-- Lemma 10.158.3: if `da₁, ..., daₙ` are linearly independent in `Ω[k⁄ZMod p]`, then adjoining
chosen `p`th roots of the `aᵢ` gives an extension of degree `p ^ n` over `k`. -/
@[stacks 07DZ]
theorem relfinrank_adjoin_pthRoots_eq_pow
    (a : Fin n → k) (roots : Fin n → K)
    (hroots : ∀ i, roots i ^ p = algebraMap k K (a i))
    (hd :
      LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i))) :
    (⊥ : IntermediateField k K).relfinrank (IntermediateField.adjoin k (Set.range roots)) =
      p ^ n := by
  induction n with
  | zero =>
      -- The empty family adjoins nothing, so the relative degree is `1 = p ^ 0`.
      simp
  | succ n ih =>
      let a₀ : Fin n → k := fun i ↦ a i.castSucc
      let roots₀ : Fin n → K := fun i ↦ roots i.castSucc
      let a_last : k := a (Fin.last n)
      let root_last : K := roots (Fin.last n)
      let L : IntermediateField k K := IntermediateField.adjoin k (Set.range roots₀)
      have hroots₀ : ∀ i, roots₀ i ^ p = algebraMap k K (a₀ i) := by
        intro i
        exact hroots i.castSucc
      have hd₀ :
          LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a₀ i)) := by
        -- Restrict the independent differential family to the prefix indices.
        simpa [a₀] using linearIndependent_differentials_castSucc (k := k) (p := p) hd
      have hprefix : (⊥ : IntermediateField k K).relfinrank L = p ^ n := by
        -- Apply the induction hypothesis to the prefix family.
        simpa [L, a₀, roots₀] using ih a₀ roots₀ hroots₀ hd₀
      have hnot :
          ¬ ∃ b : L, b ^ p = algebraMap k L a_last := by
        -- The last source element cannot already be a `p`th power over the prefix field.
        simpa [L, a₀, roots₀, a_last] using
          last_root_not_pth_power_in_prefix
            (k := k) (K := K) (p := p) a roots₀ hroots₀ hd
      have hsimple :
          Module.finrank L (IntermediateField.adjoin L ({root_last} : Set K)) = p := by
        -- The last chosen root gives a simple purely inseparable step of degree `p`.
        have hroot_last : root_last ^ p = algebraMap L K (algebraMap k L a_last) := by
          -- Rewrite the original root equation through the prefix-field tower.
          rw [show algebraMap L K (algebraMap k L a_last) = algebraMap k K a_last by rfl]
          simpa [root_last, a_last] using hroots (Fin.last n)
        exact
          finrank_adjoin_singleton_eq_prime (k := k) (K := K) (p := p) L root_last
            (algebraMap k L a_last) hroot_last hnot
      have hsnoc : Fin.snoc roots₀ root_last = roots := by
        ext i
        rcases Fin.eq_castSucc_or_eq_last i with (⟨j, rfl⟩ | rfl)
        · simp [roots₀]
        · simp [root_last]
      have hrewrite :
          IntermediateField.adjoin k (Set.range roots) =
            (IntermediateField.adjoin L ({root_last} : Set K)).restrictScalars k := by
        -- Normalize the successor stage as a simple adjunction over the prefix field.
        simpa [hsnoc, L, roots₀, root_last] using
          adjoin_range_succ_eq_restrictScalars_adjoin_singleton
            (k := k) (n := n) roots₀ root_last
      have hle :
          L ≤ IntermediateField.adjoin k (Set.range roots) := by
        -- The prefix field embeds into the full field generated by all chosen roots.
        intro x hx
        rw [hrewrite]
        exact
          IntermediateField.adjoin_contains_field_as_subfield
            (F := L.toSubfield) (S := ({root_last} : Set K)) hx
      have hstep :
          L.relfinrank (IntermediateField.adjoin k (Set.range roots)) = p := by
        have hext :
            IntermediateField.extendScalars hle =
              IntermediateField.adjoin L ({root_last} : Set K) := by
          apply IntermediateField.restrictScalars_injective k
          rw [IntermediateField.extendScalars_restrictScalars, hrewrite]
        -- Convert the simple-adjunction finrank into the relative degree in the original tower.
        rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext]
        exact hsimple
      -- Multiply the prefix degree and the last simple degree.
      calc
        (⊥ : IntermediateField k K).relfinrank (IntermediateField.adjoin k (Set.range roots)) =
            (⊥ : IntermediateField k K).relfinrank L *
              L.relfinrank (IntermediateField.adjoin k (Set.range roots)) := by
                symm
                exact IntermediateField.relfinrank_mul_relfinrank
                  (show (⊥ : IntermediateField k K) ≤ L from bot_le) hle
        _ = p * p ^ n := by rw [hprefix, hstep, Nat.mul_comm]
        _ = p ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

end
