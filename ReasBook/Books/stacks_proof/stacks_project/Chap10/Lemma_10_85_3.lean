import stacks_proof.stacks_project.Chap10.Lemma_10_85_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {P : Type v}
variable [CommRing R] [IsLocalRing R]
variable [AddCommGroup P] [Module R P] [Module.Projective R P]

/- Domain triage: this file lies in commutative algebra of projective modules over local rings
and free direct summands.
Sampled declarations in this domain:
* `Module.Projective.iff_split`
* `Module.Projective.of_split`
* `Complementeds (Submodule R P)`
* `Module.HasFiniteFreeComplementSummandProperty R P`
The numbered item is `source-facing`: it says a given element lies in a free direct summand.
The best downstream owner abstraction is `Module.HasFiniteFreeComplementSummandProperty R P` from
Lemma `10.85.2`.
Primitive data are only the ambient projective module `P`; the complemented free submodule
containing a chosen element is derived output. -/

/-- Helper for Lemma 10.85.3: in a local ring, adding a nonunit perturbation to a unit stays a
unit. -/
lemma isUnit_add_of_isUnit_of_mem_nonunits {a b : R} (ha : IsUnit a) (hb : b ∈ nonunits R) :
    IsUnit (a + b) := by
  obtain ⟨u, rfl⟩ := ha
  -- Rewrite the sum as a unit times `1 - c`, where `c` is still a nonunit.
  have hneg : -(((↑u⁻¹ : Units R) : R) * b) ∈ nonunits R := by
    simpa [neg_mul] using (mul_mem_nonunits_right (a := -(((↑u⁻¹ : Units R) : R))) hb)
  have hone : IsUnit (1 + (((↑u⁻¹ : Units R) : R) * b)) := by
    -- The local-ring criterion applies to `c = -u⁻¹ * b`.
    simpa [sub_eq_add_neg] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
        (-((((↑u⁻¹ : Units R) : R) * b))) hneg
  have hrewrite : ((↑u : Units R) : R) + b = (((↑u : Units R) : R) * (1 + (((↑u⁻¹ : Units R) : R) * b))) := by
    -- Expand and cancel `u * u⁻¹`.
    simp [mul_add, add_comm]
  exact hrewrite.symm ▸ u.isUnit.mul hone

/-- Helper for Lemma 10.85.3: a finite sum of nonunits in a local ring is again a nonunit. -/
lemma sum_mem_nonunits {ι : Type*} (s : Finset ι) (f : ι → R)
    (h : ∀ i ∈ s, f i ∈ nonunits R) :
    s.sum f ∈ nonunits R := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using (zero_mem_nonunits (α := R)).2 (zero_ne_one : (0 : R) ≠ 1)
  · intro a t hat h_ind h
    have ha : f a ∈ nonunits R := h a (Finset.mem_insert_self a t)
    have ht : ∀ i ∈ t, f i ∈ nonunits R := fun i hi => h i (Finset.mem_insert_of_mem hi)
    -- Closure of nonunits under addition is the defining local-ring property.
    simpa [Finset.sum_insert hat, add_comm] using IsLocalRing.nonunits_add ha (h_ind ht)

/-- Helper for Lemma 10.85.3: a finite sum is a unit once one summand is a unit and every other
summand is a nonunit. -/
lemma isUnit_sum_of_isUnit_of_mem_nonunits {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → R) {i : ι} (hi : i ∈ s) (hi_unit : IsUnit (f i))
    (hrest : ∀ j ∈ s.erase i, f j ∈ nonunits R) :
    IsUnit (s.sum f) := by
  -- Split off the distinguished unit term and absorb the rest into one nonunit tail.
  rw [← Finset.sum_erase_add _ _ hi, add_comm]
  exact isUnit_add_of_isUnit_of_mem_nonunits hi_unit (sum_mem_nonunits (s.erase i) f hrest)

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: equality of two finite linear combinations in a basis gives the
column relations for the corresponding coefficients. -/
lemma projected_block_coordinate_relation {ι : Type*} [Fintype ι]
    {M : Type*} [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (a : ι → R) (y : ι → M)
    (hxy : (∑ i, a i • b i) = ∑ i, a i • y i) :
    ∀ j, a j = ∑ i, a i * b.repr (y i) j := by
  intro j
  -- Apply the `j`-th basis coordinate to both sides to compare coefficients.
  have hrepr : b.repr (∑ i, a i • b i) j = b.repr (∑ i, a i • y i) j := by
    exact congrArg (fun z ↦ b.repr z j) hxy
  have hleft : b.repr (∑ i, a i • b i) j = a j := by
    simpa using congrArg (fun f ↦ f j) (Module.Basis.repr_sum_self b a)
  have hright : b.repr (∑ i, a i • y i) j = ∑ i, a i * b.repr (y i) j := by
    simp [smul_eq_mul]
  -- The chosen basis identifies the left side with `a j`.
  calc
    a j = b.repr (∑ i, a i • b i) j := by simpa using hleft.symm
    _ = b.repr (∑ i, a i • y i) j := hrepr
    _ = ∑ i, a i * b.repr (y i) j := hright

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: any vector in a free module is supported on a finite left block of a
reindexed basis. -/
lemma exists_support_fin_block_representation
    {F : Type w} [AddCommMonoid F] [Module R F] [Module.Free R F] (z : F) :
    ∃ n : ℕ, ∃ κ : Type w, ∃ B : Module.Basis (Fin n ⊕ κ) R F, ∃ a : Fin n → R,
      z = ∑ j, a j • B (Sum.inl j) := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex R F) R F := Module.Free.chooseBasis R F
  let c : Module.Free.ChooseBasisIndex R F →₀ R := b.repr z
  let s : Finset (Module.Free.ChooseBasisIndex R F) := c.support
  let efin : s ≃ Fin s.card := Fintype.equivFinOfCardEq (Fintype.card_coe s)
  let e :
      Module.Free.ChooseBasisIndex R F ≃
        (Fin s.card ⊕ {i // i ∉ (↑s : Set (Module.Free.ChooseBasisIndex R F))}) :=
    (Equiv.sumCompl fun i : Module.Free.ChooseBasisIndex R F ↦ i ∈ (↑s : Set _)).symm.trans
      (Equiv.sumCongr efin (Equiv.refl _))
  let B : Module.Basis
      (Fin s.card ⊕ {i // i ∉ (↑s : Set (Module.Free.ChooseBasisIndex R F))}) R F :=
    b.reindex e
  let a : Fin s.card → R := fun j ↦ c (efin.symm j)
  refine
    ⟨s.card, {i // i ∉ (↑s : Set (Module.Free.ChooseBasisIndex R F))}, B, a, ?_⟩
  have hz_support : z = s.sum (fun i ↦ c i • b i) := by
    -- The basis-coordinate representation of `z` only uses the finitely many support indices.
    calc
      z = Finsupp.linearCombination R b c := by
        simpa [b, c] using (b.repr_symm_apply c).symm
      _ = s.sum (fun i ↦ c i • b i) := by
        rw [Finsupp.linearCombination_apply]
        rfl
  have hz_subtype : z = ∑ i : s, c i • b i := by
    -- Rewrite the support sum as a sum over the subtype of supporting indices.
    simpa [s] using hz_support.trans (Finset.sum_attach s (fun i ↦ c i • b i)).symm
  calc
    z = ∑ i : s, c i • b i := hz_subtype
    _ = ∑ j : Fin s.card, c (efin.symm j) • b (efin.symm j) := by
      -- Reindex the finite support once to a `Fin` block.
      simpa [efin] using (efin.symm.sum_comp fun i : s ↦ c i • b i).symm
    _ = ∑ j : Fin s.card, a j • B (Sum.inl j) := by
      -- The new left block is exactly the old support block, now indexed by `Fin`.
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [a, B, b, e, efin]

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: every nonidentity Leibniz term picks up an off-diagonal nonunit
factor. -/
lemma nonidentity_permutation_product_mem_nonunits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι R) (hoff : ∀ i j, i ≠ j → B i j ∈ nonunits R)
    {σ : Equiv.Perm ι} (hσ : σ ≠ Equiv.refl ι) :
    (Equiv.Perm.sign σ • ∏ i, B (σ i) i) ∈ nonunits R := by
  classical
  have hmove : ∃ i, σ i ≠ i := by
    by_contra hmove
    apply hσ
    ext i
    exact by
      have hfixed : ¬ σ i ≠ i := by
        exact fun hi ↦ hmove ⟨i, hi⟩
      exact not_not.mp hfixed
  obtain ⟨i, hi⟩ := hmove
  have hfactor : B (σ i) i ∈ nonunits R := hoff (σ i) i hi
  have hprod : (∏ k, B (σ k) k) ∈ nonunits R := by
    -- Isolate the off-diagonal factor and use ideal closure of `nonunits`.
    rw [← Finset.prod_erase_mul _ (fun k ↦ B (σ k) k) (Finset.mem_univ i)]
    exact mul_mem_nonunits_right hfactor
  -- The sign factor only multiplies this nonunit product by a unit scalar.
  simpa [Units.smul_def, smul_eq_mul] using
    (mul_mem_nonunits_right (a := (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R)) hprod)

/-- Helper for Lemma 10.85.3: a matrix over a local ring with unit diagonal and nonunit
off-diagonal entries has unit determinant. -/
lemma isUnit_det_of_isUnit_diag_of_mem_nonunits_offDiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι R) (hdiag : ∀ i, IsUnit (B i i))
    (hoff : ∀ i j, i ≠ j → B i j ∈ nonunits R) :
    IsUnit B.det := by
  classical
  let term : Equiv.Perm ι → R := fun σ ↦ Equiv.Perm.sign σ • ∏ i, B (σ i) i
  have hdiag_prod : IsUnit (∏ i, B i i) := by
    -- A finite product of units is a unit.
    refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
    · simp
    · intro i s hi hs
      simpa [Finset.prod_insert hi] using (hdiag i).mul hs
  have hterm_refl : IsUnit (term (Equiv.refl ι)) := by
    -- The identity permutation contributes the diagonal product.
    simpa [term] using hdiag_prod
  have hterm_rest :
      ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)).erase (Equiv.refl ι), term σ ∈ nonunits R := by
    intro σ hσ
    exact nonidentity_permutation_product_mem_nonunits B hoff (Finset.mem_erase.mp hσ).1
  -- Isolate the identity term in the Leibniz expansion of the determinant.
  rw [Matrix.det_apply]
  exact isUnit_sum_of_isUnit_of_mem_nonunits (Finset.univ : Finset (Equiv.Perm ι)) term
    (Finset.mem_univ _) hterm_refl hterm_rest

/-- Helper for Lemma 10.85.3: the textbook minimal-support relation forces the diagonal
coefficient-complement and every off-diagonal coefficient to be nonunits. -/
lemma minimal_support_column_nonunit_zero_diag {n : ℕ} (a : Fin n → R)
    (hmin : ∀ j (d : Fin n → R), d j = 0 → a j ≠ ∑ i, a i * d i)
    {j : Fin n} {c : Fin n → R} (hrel : a j = ∑ i, a i * c i) :
    (1 - c j) ∈ nonunits R ∧ ∀ i, i ≠ j → c i ∈ nonunits R := by
  classical
  constructor
  · rw [mem_nonunits_iff]
    intro hunit
    obtain ⟨u, hu⟩ := hunit
    let d : Fin n → R := fun i ↦ if i = j then 0 else c i * ↑u⁻¹
    have hdj : d j = 0 := by
      -- The comparison vector is zero at the distinguished index, matching `hmin`.
      simp [d]
    have hsplit :
        (∑ i, a i * c i) = a j * c j + Finset.sum (Finset.univ.erase j) (fun i ↦ a i * c i) := by
      -- Split the coefficient relation into the `j`-term and the remaining support.
      rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ j)]
    have hrest :
        Finset.sum (Finset.univ.erase j) (fun i ↦ a i * c i) = a j * (1 - c j) := by
      -- Rearranging the split relation isolates the off-diagonal tail.
      have hsum :
          a j * c j + Finset.sum (Finset.univ.erase j) (fun i ↦ a i * c i) = a j := by
        calc
          a j * c j + Finset.sum (Finset.univ.erase j) (fun i ↦ a i * c i) = ∑ i, a i * c i := by
            simpa using hsplit.symm
          _ = a j := hrel.symm
      calc
        Finset.sum (Finset.univ.erase j) (fun i ↦ a i * c i) = a j - a j * c j := by
          refine (eq_sub_iff_add_eq).2 ?_
          simpa [add_comm] using hsum
        _ = a j * (1 - c j) := by ring
    have hrepr : a j = ∑ i, a i * d i := by
      -- Multiply the tail relation by the inverse of `1 - c j` to solve for `a j`.
      calc
        a j = (a j * ↑u) * ↑u⁻¹ := by
          simp [mul_assoc]
        _ = (a j * (1 - c j)) * ↑u⁻¹ := by rw [hu]
        _ = Finset.sum (Finset.univ.erase j) (fun i ↦ a i * c i) * ↑u⁻¹ := by rw [hrest]
        _ = Finset.sum (Finset.univ.erase j) (fun i ↦ (a i * c i) * ↑u⁻¹) := by
          rw [Finset.sum_mul]
        _ = Finset.sum (Finset.univ.erase j) (fun i ↦ a i * d i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hij : i ≠ j := (Finset.mem_erase.mp hi).1
          simp [d, hij, mul_assoc]
        _ = ∑ i, a i * d i := by
          rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ j)]
          simp [d]
    exact hmin j d hdj hrepr
  · intro i hij
    rw [mem_nonunits_iff]
    intro hunit
    obtain ⟨u, hu⟩ := hunit
    let d : Fin n → R := fun k ↦
      if hk : k = i then 0 else ((if k = j then (1 : R) else 0) - c k) * ↑u⁻¹
    have hdi : d i = 0 := by
      -- The contradiction vector now vanishes at the off-diagonal index `i`.
      simp [d]
    have hsingle :
        Finset.sum (Finset.univ.erase i) (fun k ↦ a k * (if k = j then (1 : R) else 0)) = a j := by
      -- Only the `j`-term survives because `j ∈ univ.erase i`.
      have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
      rw [← (Finset.univ.erase i).add_sum_erase _ hj_mem]
      simp
    have hsplit :
        (∑ k, a k * c k) = a i * ↑u + Finset.sum (Finset.univ.erase i) (fun k ↦ a k * c k) := by
      -- Split the given column relation at the off-diagonal unit coefficient.
      rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ i)]
      simp [hu]
    have hsolve :
        a j - Finset.sum (Finset.univ.erase i) (fun k ↦ a k * c k) = a i * ↑u := by
      -- Solving for `a i` uses the invertibility of `c i = u`.
      have hsum :
          a i * ↑u + Finset.sum (Finset.univ.erase i) (fun k ↦ a k * c k) = a j := by
        calc
          a i * ↑u + Finset.sum (Finset.univ.erase i) (fun k ↦ a k * c k) =
              a i * c i + Finset.sum (Finset.univ.erase i) (fun k ↦ a k * c k) := by
            rw [hu]
          _ = ∑ k, a k * c k := by
            simpa using hsplit.symm
          _ = a j := hrel.symm
      exact (sub_eq_iff_eq_add).2 <| by
        simpa [add_comm] using hsum.symm
    have hrepr : a i = ∑ k, a k * d k := by
      -- Repackage the solved expression so that `hmin` applies at index `i`.
      calc
        a i = (a j - Finset.sum (Finset.univ.erase i) (fun k ↦ a k * c k)) * ↑u⁻¹ := by
          rw [hsolve]
          simp [mul_assoc]
        _ = (Finset.sum (Finset.univ.erase i) (fun k ↦ a k * (if k = j then (1 : R) else 0)) -
              Finset.sum (Finset.univ.erase i) (fun k ↦ a k * c k)) * ↑u⁻¹ := by rw [hsingle]
        _ = (Finset.sum (Finset.univ.erase i)
              (fun k ↦ a k * (if k = j then (1 : R) else 0) - a k * c k)) * ↑u⁻¹ := by
          rw [Finset.sum_sub_distrib]
        _ = (Finset.sum (Finset.univ.erase i)
              (fun k ↦ a k * (((if k = j then (1 : R) else 0) - c k)))) * ↑u⁻¹ := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
        _ = Finset.sum (Finset.univ.erase i)
              (fun k ↦ (a k * (((if k = j then (1 : R) else 0) - c k))) * ↑u⁻¹) := by
          rw [Finset.sum_mul]
        _ = Finset.sum (Finset.univ.erase i) (fun k ↦ a k * d k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hki : k ≠ i := (Finset.mem_erase.mp hk).1
          simp [d, hki, mul_assoc]
        _ = ∑ k, a k * d k := by
          rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ i)]
          simp [d]
    exact hmin i d hdi hrepr

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: among all finite left-block presentations of a vector in a free
module, there is one with minimal block size. -/
lemma support_minimal_fin_block_exists_from_seed
    {F : Type w} [AddCommMonoid F] [Module R F] [Module.Free R F] (z : F) :
    ∃ n : ℕ, ∃ κ : Type w, ∃ B : Module.Basis (Fin n ⊕ κ) R F, ∃ a : Fin n → R,
      z = ∑ j, a j • B (Sum.inl j) ∧
      ∀ ⦃m : ℕ⦄ ⦃κ' : Type w⦄ (B' : Module.Basis (Fin m ⊕ κ') R F) (a' : Fin m → R),
        z = ∑ j, a' j • B' (Sum.inl j) → n ≤ m := by
  classical
  let FinBlockRep : ℕ → Prop := fun n ↦
    ∃ κ : Type w, ∃ B : Module.Basis (Fin n ⊕ κ) R F, ∃ a : Fin n → R,
      z = ∑ j, a j • B (Sum.inl j)
  obtain ⟨n₀, κ₀, B₀, a₀, hz₀⟩ :=
    exists_support_fin_block_representation (R := R) (F := F) z
  have hexists : ∃ n : ℕ, FinBlockRep n := by
    -- The existing finite-support presentation supplies a nonempty search space for `Nat.find`.
    exact ⟨n₀, κ₀, B₀, a₀, hz₀⟩
  let n := Nat.find hexists
  have hn : FinBlockRep n := Nat.find_spec hexists
  rcases hn with ⟨κ, B, a, hza⟩
  refine ⟨n, κ, B, a, hza, ?_⟩
  intro m κ' B' a' hz'
  -- Minimality is exactly the universal property of `Nat.find`.
  exact Nat.find_min' hexists ⟨κ', B', a', hz'⟩

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: if one coefficient in a `Fin (m + 1)` left block is zero, then the
corresponding basis vector can be moved into the right block by the explicit `succAbove`
reindexing. -/
lemma delete_zero_coeff_fin_block_succAbove
    {F : Type w} [AddCommMonoid F] [Module R F]
    {m : ℕ} {κ : Type w} {z : F}
    (B : Module.Basis (Fin (m + 1) ⊕ κ) R F) (j : Fin (m + 1)) (a : Fin (m + 1) → R)
    (hrep : z = ∑ i, a i • B (Sum.inl i)) (hzj : a j = 0) :
    ∃ B' : Module.Basis (Fin m ⊕ (Unit ⊕ κ)) R F, ∃ a' : Fin m → R,
      z = ∑ i, a' i • B' (Sum.inl i) := by
  classical
  let toE : (Fin (m + 1) ⊕ κ) → (Fin m ⊕ (Unit ⊕ κ)) :=
    Sum.elim
      (fun i ↦
        if h : i = j then
          Sum.inr (Sum.inl ())
        else
          Sum.inl ((finSuccAboveEquiv j).symm ⟨i, h⟩))
      (fun t ↦ Sum.inr (Sum.inr t))
  let invE : (Fin m ⊕ (Unit ⊕ κ)) → (Fin (m + 1) ⊕ κ) :=
    Sum.elim
      (fun i ↦ Sum.inl (j.succAbove i))
      (Sum.elim (fun _ ↦ Sum.inl j) (fun t ↦ Sum.inr t))
  have hleft : Function.LeftInverse invE toE := by
    intro x
    refine Sum.rec ?_ ?_ x
    · intro i
      by_cases h : i = j
      · -- The deleted slot is sent to the distinguished right-block basis vector.
        simp [toE, invE, h]
      · -- Every other left basis vector is recovered through `succAbove`/`predAbove`.
        have hsucc :
            j.succAbove ((finSuccAboveEquiv j).symm ⟨i, h⟩) = i := by
          exact Subtype.ext_iff.mp (Equiv.apply_symm_apply (finSuccAboveEquiv j) ⟨i, h⟩)
        simp [toE, invE, h, hsucc]
    · intro t
      -- The original right block stays fixed.
      simp [toE, invE]
  have hright : Function.RightInverse invE toE := by
    intro x
    refine Sum.rec ?_ ?_ x
    · intro i
      -- Re-entering through the left block reuses the same `succAbove` index.
      have hsymm :
          (finSuccAboveEquiv j).symm ⟨j.succAbove i, j.succAbove_ne i⟩ = i := by
        exact Equiv.symm_apply_apply (finSuccAboveEquiv j) i
      simp [toE, invE, Fin.succAbove_ne, hsymm]
    · intro x
      refine Sum.rec ?_ ?_ x
      · intro u
        -- The isolated deleted slot maps back to `j`.
        simp [toE, invE]
      · intro t
        -- The untouched ambient right block remains untouched.
        simp [toE, invE]
  let e : (Fin (m + 1) ⊕ κ) ≃ (Fin m ⊕ (Unit ⊕ κ)) :=
    Equiv.mk toE invE hleft hright
  refine ⟨B.reindex e, fun i ↦ a (j.succAbove i), ?_⟩
  -- Split off the zero coefficient at `j`, then rewrite the remaining block through `e`.
  calc
    z = ∑ i : Fin (m + 1), a i • B (Sum.inl i) := hrep
    _ = a j • B (Sum.inl j) + ∑ i : Fin m, a (j.succAbove i) • B (Sum.inl (j.succAbove i)) := by
      simpa using (Fin.sum_univ_succAbove (fun i : Fin (m + 1) ↦ a i • B (Sum.inl i)) j)
    _ = ∑ i : Fin m, a (j.succAbove i) • B (Sum.inl (j.succAbove i)) := by
      rw [hzj, zero_smul, zero_add]
    _ = ∑ i : Fin m, (fun i ↦ a (j.succAbove i)) i • (B.reindex e) (Sum.inl i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [Module.Basis.reindex_apply, e, invE]

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: a minimal finite left block cannot contain a zero coefficient,
because the zero slot can be deleted and moved into the right block. -/
lemma minimal_fin_block_coeff_ne_zero
    {F : Type w} [AddCommMonoid F] [Module R F]
    {n : ℕ} {κ : Type w} {z : F}
    (B : Module.Basis (Fin n ⊕ κ) R F) (a : Fin n → R)
    (hrep : z = ∑ j, a j • B (Sum.inl j))
    (hminimal : ∀ ⦃m : ℕ⦄ ⦃κ' : Type w⦄ (B' : Module.Basis (Fin m ⊕ κ') R F) (a' : Fin m → R),
        z = ∑ j, a' j • B' (Sum.inl j) → n ≤ m) :
    ∀ j, a j ≠ 0 := by
  classical
  cases n with
  | zero =>
      intro j
      exact Fin.elim0 j
  | succ m =>
      intro j hzj
      -- Route correction: the deletion half of the source contradiction is now explicit, so a
      -- zero coefficient immediately contradicts cardinality minimality.
      obtain ⟨B', a', hz'⟩ := delete_zero_coeff_fin_block_succAbove
        (B := B) (j := j) (a := a) hrep hzj
      have hle : m.succ ≤ m := hminimal B' a' hz'
      exact Nat.not_succ_le_self m hle

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: once a chosen left-block coefficient is zero, the corresponding
basis vector can be removed from the finite sum and only the erased support remains. -/
lemma fin_block_sum_eq_sum_erase_of_coeff_eq_zero
    {F : Type w} [AddCommGroup F] [Module R F]
    {n : ℕ} {κ : Type w}
    (B : Module.Basis (Fin n ⊕ κ) R F) (a : Fin n → R) (j : Fin n) (hzj : a j = 0) :
    (∑ i, a i • B (Sum.inl i)) =
      Finset.sum (Finset.univ.erase j) (fun i ↦ a i • B (Sum.inl i)) := by
  -- Splitting off the `j`-summand and using `a j = 0` collapses the left block to the erase-sum.
  rw [← Finset.univ.add_sum_erase (fun i : Fin n ↦ a i • B (Sum.inl i)) (Finset.mem_univ j)]
  simp [hzj]

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: shearing the finite left block by multiples of one chosen basis
vector still gives a basis of the ambient free module, while the right block stays fixed. -/
lemma sheared_left_block_basis
    {F : Type w} [AddCommGroup F] [Module R F]
    {m : ℕ} {κ : Type w}
    (B : Module.Basis (Fin (m + 1) ⊕ κ) R F) (j : Fin (m + 1)) (d : Fin (m + 1) → R)
    (hdj : d j = 0) :
    ∃ Bshear : Module.Basis (Fin (m + 1) ⊕ κ) R F,
      (∀ i, Bshear (Sum.inl i) = B (Sum.inl i) + d i • B (Sum.inl j)) ∧
      (∀ t, Bshear (Sum.inr t) = B (Sum.inr t)) := by
  classical
  let shear : (Fin (m + 1) →₀ R) ≃ₗ[R] (Fin (m + 1) →₀ R) :=
    Finsupp.addSingleEquiv (R := R) (i := j) d hdj
  let split :
      ((Fin (m + 1) ⊕ κ) →₀ R) ≃ₗ[R] (Fin (m + 1) →₀ R) × (κ →₀ R) :=
    Finsupp.sumFinsuppLEquivProdFinsupp R
  let coord :
      ((Fin (m + 1) ⊕ κ) →₀ R) ≃ₗ[R] ((Fin (m + 1) ⊕ κ) →₀ R) :=
    split.trans ((shear.symm.prodCongr (LinearEquiv.refl R (κ →₀ R))).trans split.symm)
  let Bshear : Module.Basis (Fin (m + 1) ⊕ κ) R F := Module.Basis.ofRepr (B.repr.trans coord)
  refine ⟨Bshear, ?_, ?_⟩
  · intro i
    -- Route correction: package the same-size shear as a coordinate automorphism of the full
    -- left-plus-right block, so the deletion step can consume a genuine basis immediately.
    have hcoord :
        coord.symm (Finsupp.single (Sum.inl i) 1) =
          Finsupp.single (Sum.inl i) 1 + d i • Finsupp.single (Sum.inl j) 1 := by
      have hshear :
          shear (Finsupp.single i 1) = Finsupp.single i 1 + Finsupp.single j (d i) := by
        simp [shear, Finsupp.addSingleEquiv]
      apply split.injective
      calc
        split (coord.symm (Finsupp.single (Sum.inl i) 1)) = (shear (Finsupp.single i 1), 0) := by
          simp [coord, split, LinearEquiv.prodCongr_apply, LinearEquiv.prodCongr_symm]
        _ = (Finsupp.single i 1 + Finsupp.single j (d i), 0) := by rw [hshear]
        _ = split (Finsupp.single (Sum.inl i) 1 + d i • Finsupp.single (Sum.inl j) 1) := by
          apply Prod.ext
          · ext a
            simp [split, Finsupp.single_apply]
          · ext a
            simp [split]
    calc
      Bshear (Sum.inl i) = B.repr.symm (coord.symm (Finsupp.single (Sum.inl i) 1)) := by
        simp [Bshear]
      _ = B.repr.symm
            (Finsupp.single (Sum.inl i) 1 + d i • Finsupp.single (Sum.inl j) 1) := by
          rw [hcoord]
      _ = B (Sum.inl i) + d i • B (Sum.inl j) := by
          simp [LinearEquiv.map_add]
  · intro t
    -- The right block is untouched by the shear automorphism.
    have hcoord :
        coord.symm (Finsupp.single (Sum.inr t) 1) = Finsupp.single (Sum.inr t) 1 := by
      apply split.injective
      calc
        split (coord.symm (Finsupp.single (Sum.inr t) 1)) = (0, Finsupp.single t 1) := by
          simp [coord, split, LinearEquiv.prodCongr_apply, LinearEquiv.prodCongr_symm]
        _ = split (Finsupp.single (Sum.inr t) 1) := by
          apply Prod.ext
          · ext a
            simp [split]
          · ext a
            simp [split]
    calc
      Bshear (Sum.inr t) = B.repr.symm (coord.symm (Finsupp.single (Sum.inr t) 1)) := by
        simp [Bshear]
      _ = B.repr.symm (Finsupp.single (Sum.inr t) 1) := by rw [hcoord]
      _ = B (Sum.inr t) := by simp

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: a forbidden coefficient relation on a minimal `Fin (m + 1)` left
block shears one slot to zero and then deletes that slot, producing a strictly smaller
presentation. -/
lemma minimal_relation_shortens_after_shear_and_delete
    {F : Type w} [AddCommGroup F] [Module R F]
    {m : ℕ} {κ : Type w} {z : F}
    (B : Module.Basis (Fin (m + 1) ⊕ κ) R F) (a : Fin (m + 1) → R)
    (hrep : z = ∑ i, a i • B (Sum.inl i)) (j : Fin (m + 1)) (d : Fin (m + 1) → R)
    (hdj : d j = 0) (hrel : a j = ∑ i, a i * d i) :
    ∃ κ' : Type w, ∃ B' : Module.Basis (Fin m ⊕ κ') R F, ∃ a' : Fin m → R,
      z = ∑ i, a' i • B' (Sum.inl i) := by
  classical
  obtain ⟨Bshear, hleft, hright⟩ := sheared_left_block_basis (B := B) (j := j) (d := d) hdj
  let a₀ : Fin (m + 1) → R := fun i ↦ if i = j then 0 else a i
  have ha₀j : a₀ j = 0 := by
    simp [a₀]
  have hsum_left :
      ∑ i, a₀ i • B (Sum.inl i) =
        Finset.sum (Finset.univ.erase j) (fun i ↦ a i • B (Sum.inl i)) := by
    calc
      ∑ i, a₀ i • B (Sum.inl i) =
          Finset.sum (Finset.univ.erase j) (fun i ↦ a₀ i • B (Sum.inl i)) := by
            exact fin_block_sum_eq_sum_erase_of_coeff_eq_zero (B := B) (a := a₀) (j := j) ha₀j
      _ = Finset.sum (Finset.univ.erase j) (fun i ↦ a i • B (Sum.inl i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hij : i ≠ j := (Finset.mem_erase.mp hi).1
            simp [a₀, hij]
  have hcoeff :
      (∑ i, a₀ i * d i) = a j := by
    calc
      ∑ i, a₀ i * d i = ∑ i, a i * d i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hij : i = j
        · subst hij
          simp [a₀, hdj]
        · simp [a₀, hij]
      _ = a j := hrel.symm
  have hrep_shear :
      z = ∑ i, a₀ i • Bshear (Sum.inl i) := by
    -- Expand the sheared basis vectors and use the given relation to recover the missing slot.
    calc
      z = ∑ i, a i • B (Sum.inl i) := hrep
      _ = a j • B (Sum.inl j) +
            Finset.sum (Finset.univ.erase j) (fun i ↦ a i • B (Sum.inl i)) := by
              simpa using
                (Finset.univ.add_sum_erase (fun i : Fin (m + 1) ↦ a i • B (Sum.inl i))
                  (Finset.mem_univ j)).symm
      _ = (∑ i, a₀ i * d i) • B (Sum.inl j) +
            Finset.sum (Finset.univ.erase j) (fun i ↦ a i • B (Sum.inl i)) := by
              rw [hcoeff]
      _ = ∑ i, a₀ i • B (Sum.inl i) + (∑ i, a₀ i * d i) • B (Sum.inl j) := by
              rw [hsum_left, add_comm]
      _ = ∑ i, a₀ i • B (Sum.inl i) + ∑ i, a₀ i • (d i • B (Sum.inl j)) := by
              congr 1
              calc
                (∑ i, a₀ i * d i) • B (Sum.inl j) =
                    ∑ i, (a₀ i * d i) • B (Sum.inl j) := by
                      rw [Finset.sum_smul]
                _ = ∑ i, a₀ i • (d i • B (Sum.inl j)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      rw [smul_smul]
      _ = ∑ i, (a₀ i • B (Sum.inl i) + a₀ i • (d i • B (Sum.inl j))) := by
              symm
              rw [Finset.sum_add_distrib]
      _ = ∑ i, a₀ i • (B (Sum.inl i) + d i • B (Sum.inl j)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [smul_add]
      _ = ∑ i, a₀ i • Bshear (Sum.inl i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hleft]
  -- Delete the now-zero coefficient from the sheared basis block.
  obtain ⟨B', a', hz'⟩ := delete_zero_coeff_fin_block_succAbove
    (B := Bshear) (j := j) (a := a₀) hrep_shear ha₀j
  exact ⟨Unit ⊕ κ, B', a', hz'⟩

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: cardinality minimality rules out the textbook shortening relation on
the coefficients of the chosen `Fin n` block. -/
lemma minimal_fin_block_forbids_shortening_relation
    {F : Type w} [AddCommGroup F] [Module R F]
    {n : ℕ} {κ : Type w} {z : F}
    (B : Module.Basis (Fin n ⊕ κ) R F) (a : Fin n → R)
    (hrep : z = ∑ j, a j • B (Sum.inl j))
    (hminimal : ∀ ⦃m : ℕ⦄ ⦃κ' : Type w⦄ (B' : Module.Basis (Fin m ⊕ κ') R F) (a' : Fin m → R),
        z = ∑ j, a' j • B' (Sum.inl j) → n ≤ m) :
    ∀ j (d : Fin n → R), d j = 0 → a j ≠ ∑ i, a i * d i := by
  classical
  cases n with
  | zero =>
      intro j
      exact Fin.elim0 j
  | succ m =>
      intro j d hdj hrel
      -- Route correction: combine the source shear and delete moves into one contradiction object
      -- before invoking the minimality hypothesis.
      obtain ⟨κ', B', a', hz'⟩ := minimal_relation_shortens_after_shear_and_delete
        (B := B) (a := a) hrep j d hdj hrel
      have hle : m.succ ≤ m := hminimal B' a' hz'
      exact Nat.not_succ_le_self m hle

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: an invertible projected left block can be completed to an ambient
basis while keeping the original right block fixed. -/
lemma projected_left_block_basis_of_unit_det
    {F : Type w} [AddCommGroup F] [Module R F]
    {n : ℕ} {κ : Type w}
    (B : Module.Basis (Fin n ⊕ κ) R F) (y : Fin n → F)
    (C : Matrix (Fin n) (Fin n) R)
    (hC : ∀ i j, B.repr (y j) (Sum.inl i) = C i j)
    (hdet : IsUnit C.det) :
    ∃ Btilde : Module.Basis (Fin n ⊕ κ) R F,
      (∀ j, Btilde (Sum.inl j) = y j) ∧
      (∀ t, Btilde (Sum.inr t) = B (Sum.inr t)) := by
  classical
  let split :
      ((Fin n ⊕ κ) →₀ R) ≃ₗ[R] (Fin n →₀ R) × (κ →₀ R) :=
    Finsupp.sumFinsuppLEquivProdFinsupp R
  let leftBlock :
      (Fin n →₀ R) ≃ₗ[R] (Fin n →₀ R) :=
    Matrix.toLinearEquiv (Finsupp.basisSingleOne : Module.Basis (Fin n) R (Fin n →₀ R)) C hdet
  let tail : Fin n → (κ →₀ R) := fun j ↦ (split (B.repr (y j))).2
  let tailMap : (Fin n →₀ R) →ₗ[R] (κ →₀ R) :=
    (Finsupp.basisSingleOne : Module.Basis (Fin n) R (Fin n →₀ R)).constr R tail
  have hshear_add :
      ∀ u v : (Fin n →₀ R) × (κ →₀ R),
        (u + v).1 = u.1 + v.1 ∧
          ((u + v).2 - tailMap ((u + v).1)) =
            (u.2 - tailMap u.1) + (v.2 - tailMap v.1) := by
    intro u v
    constructor
    · rfl
    · ext t
      rw [Prod.snd_add, Prod.fst_add, map_add]
      abel_nf
  have hshear_smul :
      ∀ (a : R) (u : (Fin n →₀ R) × (κ →₀ R)),
        (a • u).1 = a • u.1 ∧
          ((a • u).2 - tailMap ((a • u).1)) = a • (u.2 - tailMap u.1) := by
    intro a u
    constructor
    · rfl
    · ext t
      change (a • u.2 - tailMap (a • u.1)) t = (a • (u.2 - tailMap u.1)) t
      have hmap : tailMap (a • u.1) t = a * tailMap u.1 t := by
        simpa using congrArg (fun f : κ →₀ R ↦ f t) (tailMap.map_smul a u.1)
      change a * u.2 t - (tailMap (a • u.1)) t = a * (u.2 t - tailMap u.1 t)
      rw [hmap]
      ring
  have hshear_left_inv :
      Function.LeftInverse
        (fun u : (Fin n →₀ R) × (κ →₀ R) ↦ (u.1, u.2 + tailMap u.1))
        (fun u : (Fin n →₀ R) × (κ →₀ R) ↦ (u.1, u.2 - tailMap u.1)) := by
    intro u
    apply Prod.ext
    · rfl
    · ext t
      simp [sub_eq_add_neg, add_assoc]
  have hshear_right_inv :
      Function.RightInverse
        (fun u : (Fin n →₀ R) × (κ →₀ R) ↦ (u.1, u.2 + tailMap u.1))
        (fun u : (Fin n →₀ R) × (κ →₀ R) ↦ (u.1, u.2 - tailMap u.1)) := by
    intro u
    apply Prod.ext
    · rfl
    · ext t
      simp [sub_eq_add_neg, add_assoc]
  let tailShear :
      ((Fin n →₀ R) × (κ →₀ R)) ≃ₗ[R] ((Fin n →₀ R) × (κ →₀ R)) :=
    { toFun := fun u ↦ (u.1, u.2 - tailMap u.1)
      invFun := fun u ↦ (u.1, u.2 + tailMap u.1)
      left_inv := hshear_left_inv
      right_inv := hshear_right_inv
      map_add' := by
        intro u v
        apply Prod.ext
        · simp
        · ext t
          exact congrArg (fun f : κ →₀ R ↦ f t) (hshear_add u v).2
      map_smul' := by
        intro a u
        apply Prod.ext
        · simp
        · ext t
          exact congrArg (fun f : κ →₀ R ↦ f t) (hshear_smul a u).2 }
  let coord :
      ((Fin n ⊕ κ) →₀ R) ≃ₗ[R] ((Fin n ⊕ κ) →₀ R) :=
    split.trans
      (((leftBlock.symm.prodCongr (LinearEquiv.refl R (κ →₀ R))).trans tailShear).trans split.symm)
  let Btilde : Module.Basis (Fin n ⊕ κ) R F := Module.Basis.ofRepr (B.repr.trans coord)
  refine ⟨Btilde, ?_, ?_⟩
  · intro j
    -- Normalize the left coordinates by `C⁻¹`, then add back the right tail recorded by `y j`.
    have hcoord :
        coord.symm (Finsupp.single (Sum.inl j) 1) = B.repr (y j) := by
      apply split.injective
      calc
        split (coord.symm (Finsupp.single (Sum.inl j) 1)) =
            (leftBlock (Finsupp.single j 1), tailMap (Finsupp.single j 1)) := by
              simp [coord, split, tailShear, LinearEquiv.prodCongr_apply,
                LinearEquiv.prodCongr_symm]
        _ = ((split (B.repr (y j))).1, (split (B.repr (y j))).2) := by
              apply Prod.ext
              · ext i
                calc
                  leftBlock (Finsupp.single j 1) i =
                      ((Matrix.toLin
                        (Finsupp.basisSingleOne : Module.Basis (Fin n) R (Fin n →₀ R))
                        (Finsupp.basisSingleOne : Module.Basis (Fin n) R (Fin n →₀ R)) C)
                        (Finsupp.single j 1)) i := by
                          rfl
                  _ = C i j := by
                        have hself :=
                          congrArg (fun f : Fin n →₀ R ↦ f i)
                            (Matrix.toLin_self
                              (v₁ := (Finsupp.basisSingleOne :
                                Module.Basis (Fin n) R (Fin n →₀ R)))
                              (v₂ := (Finsupp.basisSingleOne :
                                Module.Basis (Fin n) R (Fin n →₀ R)))
                              C j)
                        simpa [Finsupp.single_apply] using hself
                  _ = (split (B.repr (y j))).1 i := by
                        simp [split, hC]
              · simpa [tailMap, tail] using
                  (Module.Basis.constr_basis
                    (b := (Finsupp.basisSingleOne : Module.Basis (Fin n) R (Fin n →₀ R)))
                    (S := R) (f := tail) j)
        _ = split (B.repr (y j)) := by
              cases hsplit : split (B.repr (y j))
              rfl
    calc
      Btilde (Sum.inl j) = B.repr.symm (coord.symm (Finsupp.single (Sum.inl j) 1)) := by
        simp [Btilde]
      _ = B.repr.symm (B.repr (y j)) := by rw [hcoord]
      _ = y j := by simp
  · intro t
    -- The right block is fixed because the coordinate shear only changes the tail of left vectors.
    have hcoord :
        coord.symm (Finsupp.single (Sum.inr t) 1) = Finsupp.single (Sum.inr t) 1 := by
      apply split.injective
      calc
        split (coord.symm (Finsupp.single (Sum.inr t) 1)) = (0, Finsupp.single t 1) := by
          simp [coord, split, tailShear, LinearEquiv.prodCongr_apply, LinearEquiv.prodCongr_symm]
        _ = split (Finsupp.single (Sum.inr t) 1) := by
          apply Prod.ext
          · ext i
            simp [split]
          · ext s
            simp [split]
    calc
      Btilde (Sum.inr t) = B.repr.symm (coord.symm (Finsupp.single (Sum.inr t) 1)) := by
        simp [Btilde]
      _ = B.repr.symm (Finsupp.single (Sum.inr t) 1) := by rw [hcoord]
      _ = B (Sum.inr t) := by simp

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: the projected left block inherits linear independence from the
ambient replacement basis. -/
lemma projected_family_linearIndependent
    {F : Type w} [AddCommGroup F] [Module R F]
    {n : ℕ} {κ : Type w}
    (i : P →ₗ[R] F) (π : F →ₗ[R] P) (hπi : π.comp i = LinearMap.id)
    (p : Fin n → P) (Btilde : Module.Basis (Fin n ⊕ κ) R F)
    (hleft : ∀ j, Btilde (Sum.inl j) = i (p j)) :
    LinearIndependent R p := by
  have hi_inj : Function.Injective i := by
    intro u v huv
    have hu : π (i u) = u := by
      simpa [LinearMap.comp_apply] using DFunLike.congr_fun hπi u
    have hv : π (i v) = v := by
      simpa [LinearMap.comp_apply] using DFunLike.congr_fun hπi v
    calc
      u = π (i u) := hu.symm
      _ = π (i v) := congrArg π huv
      _ = v := hv
  have hi_injOn : Set.InjOn i (Submodule.span R (Set.range p)) := fun _ _ _ _ hxy ↦ hi_inj hxy
  have hleft_ind :
      LinearIndependent R (fun j : Fin n ↦ Btilde (Sum.inl j)) := by
    exact Btilde.linearIndependent.comp Sum.inl Sum.inl_injective
  have hp_map : LinearIndependent R (i ∘ p) := by
    simpa [Function.comp_def, hleft] using hleft_ind
  exact (i.linearIndependent_iff_of_injOn (v := p) hi_injOn).mp hp_map

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: a split submodule is complementary to the kernel of its
retraction. -/
lemma subtype_isCompl_ker_of_split
    (N : Submodule R P) (ρ : P →ₗ[R] N)
    (hρ : ρ.comp N.subtype = LinearMap.id) :
    IsCompl N (LinearMap.ker ρ) := by
  let e : P →ₗ[R] P := N.subtype.comp ρ
  have he : IsIdempotentElem e := by
    -- The endomorphism `N.subtype ∘ ρ` is idempotent because `ρ` is a left inverse to `N.subtype`.
    change e * e = e
    ext x
    change N.subtype (ρ (N.subtype (ρ x))) = N.subtype (ρ x)
    have hsec : ρ (N.subtype (ρ x)) = ρ x := by
      simpa using congrArg (fun f : N →ₗ[R] N ↦ f (ρ x)) hρ
    rw [hsec]
  have hrange : LinearMap.range e = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (ρ y).2
    · intro hx
      refine ⟨x, ?_⟩
      have hsec : ρ (N.subtype ⟨x, hx⟩) = ⟨x, hx⟩ := by
        simpa using congrArg (fun f : N →ₗ[R] N ↦ f ⟨x, hx⟩) hρ
      exact congrArg Subtype.val hsec
  have hker : LinearMap.ker e = LinearMap.ker ρ := by
    ext x
    constructor
    · intro hx
      change N.subtype (ρ x) = 0 at hx
      have hsx : ρ (N.subtype (ρ x)) = 0 := by
        simpa using congrArg ρ hx
      have hsec : ρ (N.subtype (ρ x)) = ρ x := by
        simpa using congrArg (fun f : N →ₗ[R] N ↦ f (ρ x)) hρ
      rw [hsec] at hsx
      exact hsx
    · intro hx
      change N.subtype (ρ x) = 0
      simpa using congrArg N.subtype hx
  -- Transport the standard range/kernel complement for an idempotent endomorphism.
  simpa [hrange, hker] using LinearMap.IsIdempotentElem.isCompl (f := e) he

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: the ambient left-block projector descends to an idempotent
endomorphism of `P` whose range is the span of the projected family. -/
lemma projected_span_projector_range
    {F : Type w} [AddCommGroup F] [Module R F]
    {n : ℕ} {κ : Type w}
    (i : P →ₗ[R] F) (π : F →ₗ[R] P) (hπi : π.comp i = LinearMap.id)
    (p : Fin n → P) (Btilde : Module.Basis (Fin n ⊕ κ) R F)
    (hleft : ∀ j, Btilde (Sum.inl j) = i (p j)) :
    ∃ e : P →ₗ[R] P, e.comp e = e ∧
      LinearMap.range e = Submodule.span R (Set.range p) ∧
      (∀ j, e (p j) = p j) := by
  classical
  let prLeftF : F →ₗ[R] F :=
    Btilde.constr R (Sum.elim (fun j ↦ Btilde (Sum.inl j)) fun _ ↦ (0 : F))
  let e : P →ₗ[R] P := π.comp (prLeftF.comp i)
  have hpr_left : ∀ j, prLeftF (Btilde (Sum.inl j)) = Btilde (Sum.inl j) := by
    intro j
    simp [prLeftF]
  have hpr_range :
      LinearMap.range prLeftF =
        Submodule.span R
          (Set.range
            (Sum.elim (fun j : Fin n ↦ Btilde (Sum.inl j)) (fun _ : κ ↦ (0 : F))
              : Fin n ⊕ κ → F)) := by
    -- `Basis.constr_range` identifies the projector image with the span of its chosen basis images.
    simpa [prLeftF] using
      (Btilde.constr_range (S := R)
        (f := (Sum.elim (fun j : Fin n ↦ Btilde (Sum.inl j)) (fun _ : κ ↦ (0 : F))
          : Fin n ⊕ κ → F)))
  have hpr_span_le :
      Submodule.span R
          (Set.range
            (Sum.elim (fun j : Fin n ↦ Btilde (Sum.inl j)) (fun _ : κ ↦ (0 : F))
              : Fin n ⊕ κ → F)) ≤
        Submodule.span R (Set.range fun j : Fin n ↦ Btilde (Sum.inl j)) := by
    refine Submodule.span_le.2 ?_
    intro z hz
    rcases hz with ⟨s, rfl⟩
    cases s with
    | inl j =>
        exact Submodule.subset_span ⟨j, rfl⟩
    | inr t =>
        simp
  have hpr_mem_left :
      ∀ x, prLeftF x ∈ Submodule.span R (Set.range fun j : Fin n ↦ Btilde (Sum.inl j)) := by
    intro x
    have hx : prLeftF x ∈ LinearMap.range prLeftF := ⟨x, rfl⟩
    rw [hpr_range] at hx
    exact hpr_span_le hx
  have he_left : ∀ j, e (p j) = p j := by
    intro j
    -- The descended projector fixes each projected left-block basis vector.
    calc
      e (p j) = π (prLeftF (i (p j))) := by
        rfl
      _ = π (prLeftF (Btilde (Sum.inl j))) := by
        rw [hleft]
      _ = π (Btilde (Sum.inl j)) := by
        rw [hpr_left]
      _ = π (i (p j)) := by
        rw [hleft]
      _ = p j := by
        simpa [LinearMap.comp_apply] using DFunLike.congr_fun hπi (p j)
  have hmap_left :
      Submodule.map π (Submodule.span R (Set.range fun j : Fin n ↦ Btilde (Sum.inl j))) =
        Submodule.span R (Set.range p) := by
    -- Mapping the ambient left block through `π` recovers exactly the projected family `p`.
    have himage :
        Set.image π (Set.range fun j : Fin n ↦ Btilde (Sum.inl j)) = Set.range p := by
      ext x
      constructor
      · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
        refine ⟨j, ?_⟩
        simpa [hleft, LinearMap.comp_apply] using (DFunLike.congr_fun hπi (p j)).symm
      · rintro ⟨j, rfl⟩
        refine ⟨Btilde (Sum.inl j), ⟨j, rfl⟩, ?_⟩
        simpa [hleft, LinearMap.comp_apply] using DFunLike.congr_fun hπi (p j)
    rw [Submodule.map_span, himage]
  have hrange_le : LinearMap.range e ≤ Submodule.span R (Set.range p) := by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    have hx :
        prLeftF (i x) ∈ Submodule.span R (Set.range fun j : Fin n ↦ Btilde (Sum.inl j)) :=
      hpr_mem_left (i x)
    have hmap_mem :
        π (prLeftF (i x)) ∈
          Submodule.map π (Submodule.span R (Set.range fun j : Fin n ↦ Btilde (Sum.inl j))) := by
      exact ⟨prLeftF (i x), hx, rfl⟩
    rw [hmap_left] at hmap_mem
    simpa [e, LinearMap.comp_apply] using hmap_mem
  have hspan_le_range : Submodule.span R (Set.range p) ≤ LinearMap.range e := by
    refine Submodule.span_le.2 ?_
    intro z hz
    rcases hz with ⟨j, rfl⟩
    exact ⟨p j, he_left j⟩
  have hrange :
      LinearMap.range e = Submodule.span R (Set.range p) :=
    le_antisymm hrange_le hspan_le_range
  have hfix_span :
      ∀ z ∈ Submodule.span R (Set.range p), e z = z := by
    intro z hz
    -- Once the projector fixes each generator, it fixes the entire projected span.
    refine Submodule.span_induction (p := fun z _ ↦ e z = z) ?_ ?_ ?_ ?_ hz
    · intro y hy
      rcases hy with ⟨j, rfl⟩
      exact he_left j
    · simp [e]
    · intro u v hu hv hu' hv'
      simpa [map_add, hu', hv']
    · intro a u hu hu'
      simpa [map_smul, hu']
  have hidem : e.comp e = e := by
    ext z
    have hz : e z ∈ LinearMap.range e := ⟨z, rfl⟩
    rw [hrange] at hz
    simpa [LinearMap.comp_apply] using hfix_span (e z) hz
  exact ⟨e, hidem, hrange, he_left⟩

omit [IsLocalRing R] in
/-- Helper for Lemma 10.85.3: the span of the projected left block is a complemented free
submodule of `P`, and any coefficient expression in that family lands inside it. -/
lemma ambient_left_block_basis_descends_to_split_submodule
    {F : Type w} [AddCommGroup F] [Module R F]
    {n : ℕ} {κ : Type w}
    (i : P →ₗ[R] F) (π : F →ₗ[R] P) (hπi : π.comp i = LinearMap.id)
    (p : Fin n → P) (Btilde : Module.Basis (Fin n ⊕ κ) R F)
    (hleft : ∀ j, Btilde (Sum.inl j) = i (p j))
    (x : P) (a : Fin n → R) (hx : x = ∑ j, a j • p j) :
    ∃ N : Complementeds (Submodule R P), x ∈ (N : Submodule R P) ∧
      Module.Free R (N : Submodule R P) := by
  classical
  obtain ⟨e, heidem, hrange, _⟩ :=
    projected_span_projector_range (i := i) (π := π) hπi p Btilde hleft
  let N : Submodule R P := Submodule.span R (Set.range p)
  have hsplit :
      e.rangeRestrict.comp (LinearMap.range e).subtype = LinearMap.id := by
    -- The range-restricted endomorphism is a retraction because `e` is idempotent on its own image.
    ext y
    change e ↑y = ↑y
    rcases y.2 with ⟨z, hz⟩
    rw [← hz]
    simpa [LinearMap.comp_apply] using DFunLike.congr_fun heidem z
  have hcompl_range :
      IsCompl (LinearMap.range e) (LinearMap.ker e.rangeRestrict) := by
    exact subtype_isCompl_ker_of_split (N := LinearMap.range e) (ρ := e.rangeRestrict) hsplit
  have hcomplN : IsCompl N (LinearMap.ker e.rangeRestrict) := by
    simpa [N, hrange] using hcompl_range
  have hp_lin :
      LinearIndependent R p :=
    projected_family_linearIndependent (i := i) (π := π) hπi p Btilde hleft
  have hfreeN : Module.Free R N := by
    -- The projected family is linearly independent, so its span carries the induced basis.
    dsimp [N]
    exact Module.Free.of_basis (Module.Basis.span hp_lin)
  have hxN : x ∈ N := by
    -- The given coefficient presentation of `x` already lives in the span of the projected family.
    rw [hx]
    refine Submodule.sum_mem _ ?_
    intro j hj
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine ⟨⟨N, ⟨LinearMap.ker e.rangeRestrict, hcomplN⟩⟩, ?_, hfreeN⟩
  simpa [N] using hxN

-- Proof sketch: realize `P` as a direct summand of a free module using
-- `Module.Projective.iff_split`, choose a minimal finite support expression for `x` in a basis of
-- the ambient free module, project the supporting basis vectors to `P`, and use the local-ring
-- determinant argument from the textbook to show these projected vectors span a free complemented
-- submodule containing `x`.
/-- Lemma 10.85.3: if `P` is a projective module over a local ring `R`, then every element of `P`
is contained in a free direct summand of `P`. -/
@[stacks 0592]
theorem exists_free_directSummand_submodule_containing
    (x : P) :
    ∃ N : Complementeds (Submodule R P), x ∈ (N : Submodule R P) ∧
      Module.Free R (N : Submodule R P) :=
  by
  classical
  -- Route correction: the determinant endgame is already isolated in the helpers above.
  -- The remaining source-faithful work is to build the minimal-support finite block in a split
  -- free ambient module and then apply those helpers to the projected block matrix.
  obtain ⟨F, _instAddCommGroupF, _instModuleF, _instFreeF, i, π, hπi⟩ :=
    Module.Projective.iff_split.mp (inferInstance : Module.Projective R P)
  letI := _instAddCommGroupF
  letI := _instModuleF
  letI := _instFreeF
  letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R (M := F)
  obtain ⟨n, κ, B, a, hxB, hminimal⟩ :=
    support_minimal_fin_block_exists_from_seed (R := R) (F := F) (i x)
  have hnonzero : ∀ j, a j ≠ 0 :=
    minimal_fin_block_coeff_ne_zero (B := B) (a := a) hxB hminimal
  let p : Fin n → P := fun j ↦ π (B (Sum.inl j))
  let y : Fin n → F := fun j ↦ i (p j)
  let C : Matrix (Fin n) (Fin n) R := fun i j ↦ B.repr (y j) (Sum.inl i)
  have hxP : x = ∑ j, a j • p j := by
    -- Applying the retraction to the ambient basis expression recovers the projected family in `P`.
    calc
      x = π (i x) := by
            simpa [LinearMap.comp_apply] using (DFunLike.congr_fun hπi x).symm
      _ = π (∑ j, a j • B (Sum.inl j)) := by rw [hxB]
      _ = ∑ j, a j • p j := by
            simp [p, map_sum]
  have hxy : i x = ∑ j, a j • y j := by
    -- Re-embedding the projected expression gives the left block used in the source proof.
    calc
      i x = i (∑ j, a j • p j) := by rw [hxP]
      _ = ∑ j, a j • y j := by
            simp [y, map_sum]
  have hcoord :
      ∀ j : Fin n, a j = ∑ i, a i * C j i := by
    -- Compare the `Sum.inl j` coordinate under `B.repr` on the original and projected expressions.
    intro j
    have hleftcoord : B.repr (i x) (Sum.inl j) = a j := by
      rw [hxB]
      -- Apply `B.repr` to the finite left-block sum and then read off the `Sum.inl j` coordinate.
      have hrepr_sum :
          B.repr (∑ i, a i • B (Sum.inl i)) =
            ∑ i, a i • (Finsupp.single (α := Fin n ⊕ κ) (Sum.inl i) (1 : R)) := by
        simp
      have hcoord_sum :
          B.repr (∑ i, a i • B (Sum.inl i)) (Sum.inl j) =
            (∑ i, a i • (Finsupp.single (α := Fin n ⊕ κ) (Sum.inl i) (1 : R))) (Sum.inl j) := by
        exact congrArg (fun f : (Fin n ⊕ κ →₀ R) ↦ f (Sum.inl j)) hrepr_sum
      rw [hcoord_sum]
      simp [Finsupp.single_apply]
    calc
      a j = B.repr (i x) (Sum.inl j) := hleftcoord.symm
      _ = B.repr (∑ i, a i • y i) (Sum.inl j) := by
            rw [hxy]
      _ = ∑ i, a i * C j i := by
            simp [C, smul_eq_mul]
  have hshort :
      ∀ j (d : Fin n → R), d j = 0 → a j ≠ ∑ i, a i * d i :=
    minimal_fin_block_forbids_shortening_relation (R := R) (F := F) (B := B) (a := a) hxB hminimal
  have hdiag : ∀ j, IsUnit (C j j) := by
    intro j
    obtain ⟨hdiag_nonunit, _⟩ :=
      minimal_support_column_nonunit_zero_diag (a := a) (hmin := hshort) (hrel := hcoord j)
    simpa [sub_eq_add_neg, add_assoc] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (1 - C j j) hdiag_nonunit
  have hoff : ∀ i j, i ≠ j → C i j ∈ nonunits R := by
    intro i j hij
    obtain ⟨_, hoffj⟩ :=
      minimal_support_column_nonunit_zero_diag (a := a) (hmin := hshort) (hrel := hcoord i)
    exact hoffj j hij.symm
  have hdetC : IsUnit C.det :=
    isUnit_det_of_isUnit_diag_of_mem_nonunits_offDiag C hdiag hoff
  have hC : ∀ i j, B.repr (y j) (Sum.inl i) = C i j := by
    intro i j
    rfl
  obtain ⟨Btilde, hBleft, hBright⟩ :=
    projected_left_block_basis_of_unit_det (B := B) (y := y) (C := C) hC hdetC
  exact ambient_left_block_basis_descends_to_split_submodule
    (i := i) (π := π) hπi p Btilde hBleft x a hxP

namespace Module

-- Proof sketch: given a decomposition `P = N ⊕ N'` with `N'` finite free, the summand `N` is
-- projective by `Module.Projective.of_split`; apply Lemma `10.85.3` to each `x : N`.
/-- Canonical owner-form companion to Lemma 10.85.3 for the chapter abstraction used in
Lemma `10.85.2`. -/
theorem hasFiniteFreeComplementSummandProperty_of_projective_of_isLocalRing :
    HasFiniteFreeComplementSummandProperty R P := by
  intro N N' hNN' _ _
  -- The complementary summand `N` is projective because the ambient projective module `P` splits
  -- along the inclusion/projection pair coming from `hNN'`.
  letI : Module.Projective R N :=
    Module.Projective.of_split N.subtype (N.linearProjOfIsCompl N' hNN')
      (Submodule.linearProjOfIsCompl_comp_subtype hNN')
  intro x
  -- Apply Lemma 10.85.3 inside the summand `N`, then unpack the complemented witness.
  obtain ⟨F, hxF, hfreeF⟩ := exists_free_directSummand_submodule_containing (R := R) (P := N) x
  obtain ⟨F', hFF'⟩ := F.2
  exact ⟨F, F', hxF, hfreeF, hFF'⟩

end Module

end
