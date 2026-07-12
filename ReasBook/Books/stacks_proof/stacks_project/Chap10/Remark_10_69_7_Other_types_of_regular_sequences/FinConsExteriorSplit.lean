import StacksProject_2024.Chap10.Remark_10_69_7_Other_types_of_regular_sequences.HeadTailExactness

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Set
open scoped Pointwise TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): if a subset of `Fin (m + 2)` of
cardinality `n + 1` contains the head index `0`, then erasing `0` leaves a subset of
cardinality `n`. -/
theorem fin_cons_powersetCard_erase_zero_card {m n : ℕ}
    (s : Set.powersetCard (Fin (m + 2)) (n + 1)) (h0 : (0 : Fin (m + 2)) ∈ s) :
    ((s : Finset (Fin (m + 2))).erase 0).card = n := by
  -- Proof comment: removing a present head element drops the cardinality by exactly one.
  have hcard :
      ((s : Finset (Fin (m + 2))).erase 0).card + 1 = n + 1 := by
    simpa [Set.powersetCard.card_eq s] using Finset.card_erase_add_one h0
  omega

/-- Helper for Remark 10.69.7 (Other types of regular sequences): if a subset of `Fin (m + 2)` of
cardinality `n + 1` avoids the head index `0`, then erasing `0` does not change its cardinality. -/
theorem fin_cons_powersetCard_erase_zero_card_of_not_mem {m n : ℕ}
    (s : Set.powersetCard (Fin (m + 2)) (n + 1)) (h0 : (0 : Fin (m + 2)) ∉ s) :
    ((s : Finset (Fin (m + 2))).erase 0).card = n + 1 := by
  -- Proof comment: erasing a missing head element leaves the subset unchanged.
  have h0' : (0 : Fin (m + 2)) ∉ (s : Finset (Fin (m + 2))) := by
    simpa using h0
  have herase : ((s : Finset (Fin (m + 2))).erase 0) = (s : Finset (Fin (m + 2))) := by
    exact Finset.erase_eq_self.mpr h0'
  rw [herase]
  exact Set.powersetCard.card_eq s

/- The source-faithful combinatorics is cleaner on ordered embeddings than on subsets: an
embedding into `Fin (m + 2)` either misses `0` entirely or hits it at the unique first position. -/
/-- Helper for Remark 10.69.7 (Other types of regular sequences): if an ordered embedding into
`Fin (m + 2)` does not send `0` to `0`, then none of its values is `0`. -/
theorem fin_cons_orderEmb_ne_zero_of_head_ne_zero {m n : ℕ}
    {f : Fin (n + 1) ↪o Fin (m + 2)} (h0 : f 0 ≠ 0) (i : Fin (n + 1)) :
    f i ≠ 0 := by
  -- Proof comment: monotonicity forces `f 0 ≤ f i`; if `f i = 0`, then also `f 0 = 0`.
  intro hi
  have hle : f 0 ≤ f i := f.monotone (Fin.zero_le i)
  rw [hi] at hle
  exact h0 (le_antisymm hle (Fin.zero_le _))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): after deleting the initial `0`
from a `0`-avoiding ordered embedding, the resulting `pred` map is still strictly monotone. -/
theorem fin_cons_orderEmb_pred_strictMono_of_head_ne_zero {m n : ℕ}
    {f : Fin (n + 1) ↪o Fin (m + 2)} (h0 : f 0 ≠ 0) :
    StrictMono (fun i : Fin (n + 1) ↦ (f i).pred (fin_cons_orderEmb_ne_zero_of_head_ne_zero h0 i)) :=
    by
  intro i j hij
  -- Proof comment: `pred` preserves the strict order on positive elements of `Fin`.
  rw [Fin.lt_pred_iff (fin_cons_orderEmb_ne_zero_of_head_ne_zero h0 j)]
  simpa [Fin.succ_pred (f i) (fin_cons_orderEmb_ne_zero_of_head_ne_zero h0 i)] using
    f.strictMono hij

/-- Helper for Remark 10.69.7 (Other types of regular sequences): deleting the initial `0` from a
`0`-avoiding ordered embedding into `Fin (m + 2)` produces an ordered embedding into
`Fin (m + 1)`. -/
noncomputable def fin_cons_orderEmb_drop_zero {m n : ℕ}
    {f : Fin (n + 1) ↪o Fin (m + 2)} (h0 : f 0 ≠ 0) :
    Fin (n + 1) ↪o Fin (m + 1) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (f i).pred (fin_cons_orderEmb_ne_zero_of_head_ne_zero h0 i))
    (fin_cons_orderEmb_pred_strictMono_of_head_ne_zero h0)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): if an ordered embedding into
`Fin (m + 2)` hits `0` at the head, then every successor-domain value is positive. -/
theorem fin_cons_orderEmb_succ_ne_zero_of_head_zero {m n : ℕ}
    {f : Fin (n + 1) ↪o Fin (m + 2)} (h0 : f 0 = 0) (i : Fin n) :
    f i.succ ≠ 0 := by
  -- Proof comment: strict monotonicity forces the successor-domain values to lie strictly above
  -- the head value `0`.
  have hlt : 0 < f i.succ := by
    have hdom : (0 : Fin (n + 1)) < i.succ := by
      simp
    simpa [h0] using f.strictMono hdom
  exact ne_of_gt hlt

/-- Helper for Remark 10.69.7 (Other types of regular sequences): after removing the head domain
and codomain positions from a `0`-hitting ordered embedding, the resulting `pred` map is still
strictly monotone. -/
theorem fin_cons_orderEmb_tail_strictMono_of_head_zero {m n : ℕ}
    {f : Fin (n + 1) ↪o Fin (m + 2)} (h0 : f 0 = 0) :
    StrictMono
      (fun i : Fin n ↦ (f i.succ).pred (fin_cons_orderEmb_succ_ne_zero_of_head_zero h0 i)) := by
  intro i j hij
  -- Proof comment: on the successor branch, the same positive-element `pred` argument transports
  -- strict monotonicity to the smaller `Fin`.
  rw [Fin.lt_pred_iff (fin_cons_orderEmb_succ_ne_zero_of_head_zero h0 j)]
  simpa [Fin.succ_pred (f i.succ) (fin_cons_orderEmb_succ_ne_zero_of_head_zero h0 i)] using
    f.strictMono (show i.succ < j.succ by simpa using hij)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): if an ordered embedding into
`Fin (m + 2)` sends `0` to `0`, then deleting the head domain and codomain slots yields an ordered
embedding `Fin n ↪o Fin (m + 1)`. -/
noncomputable def fin_cons_orderEmb_drop_head {m n : ℕ}
    {f : Fin (n + 1) ↪o Fin (m + 2)} (h0 : f 0 = 0) :
    Fin n ↪o Fin (m + 1) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (f i.succ).pred (fin_cons_orderEmb_succ_ne_zero_of_head_zero h0 i))
    (fin_cons_orderEmb_tail_strictMono_of_head_zero h0)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): adjoining a head value `0` and
shifting the tail by `Fin.succ` defines a strictly monotone map. -/
theorem fin_cons_orderEmb_cons_zero_strictMono {m n : ℕ} (g : Fin n ↪o Fin (m + 1)) :
    StrictMono (Fin.cons (0 : Fin (m + 2)) (fun i ↦ (g i).succ)) := by
  intro i j hij
  -- Proof comment: compare the four `Fin.cons` cases explicitly; only the successor-successor
  -- branch uses the tail embedding.
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          exact (lt_irrefl _ hij).elim
      | succ j =>
          simpa using Fin.zero_lt_succ j
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          exact (Fin.not_lt_zero _ hij).elim
      | succ j =>
          have hij' : i < j := by
            simpa using hij
          simpa using (show (g i).succ < (g j).succ by simpa using g.strictMono hij')

/-- Helper for Remark 10.69.7 (Other types of regular sequences): adjoining the head value `0` to
an ordered tail embedding gives an ordered embedding into the larger `Fin`. -/
noncomputable def fin_cons_orderEmb_cons_zero {m n : ℕ} (g : Fin n ↪o Fin (m + 1)) :
    Fin (n + 1) ↪o Fin (m + 2) :=
  OrderEmbedding.ofStrictMono
    (Fin.cons (0 : Fin (m + 2)) (fun i ↦ (g i).succ))
    (fin_cons_orderEmb_cons_zero_strictMono g)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the forward branch of the
ordered-embedding split sends a `Fin (n + 1) ↪o Fin (m + 2)` either to the `0`-avoiding branch or
to the `0`-hitting branch. -/
noncomputable def fin_cons_orderEmb_sum_toFun (m n : ℕ) :
    (Fin (n + 1) ↪o Fin (m + 2)) →
      (Fin (n + 1) ↪o Fin (m + 1)) ⊕ (Fin n ↪o Fin (m + 1)) :=
  fun f ↦
    if h0 : f 0 = 0 then
      Sum.inr (fin_cons_orderEmb_drop_head h0)
    else
      Sum.inl (fin_cons_orderEmb_drop_zero h0)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the inverse branch of the
ordered-embedding split reinserts the deleted head `0`. -/
noncomputable def fin_cons_orderEmb_sum_invFun (m n : ℕ) :
    (Fin (n + 1) ↪o Fin (m + 1)) ⊕ (Fin n ↪o Fin (m + 1)) →
      (Fin (n + 1) ↪o Fin (m + 2)) :=
  Sum.elim
    (fun g ↦ g.trans (Fin.succOrderEmb (m + 1)))
    fin_cons_orderEmb_cons_zero

/-- Helper for Remark 10.69.7 (Other types of regular sequences): deleting and then reinserting
the head `0` recovers the original ordered embedding. -/
theorem fin_cons_orderEmb_sum_left_inv (m n : ℕ) :
    Function.LeftInverse (fin_cons_orderEmb_sum_invFun m n) (fin_cons_orderEmb_sum_toFun m n) := by
  intro f
  -- Proof comment: split according to whether `f` hits `0` at the head and then simplify the
  -- `pred`/`succ` cancellation on each branch.
  by_cases h0 : f 0 = 0
  · dsimp [fin_cons_orderEmb_sum_toFun, fin_cons_orderEmb_sum_invFun]
    rw [dif_pos h0]
    ext i
    cases i using Fin.cases with
    | zero =>
        simpa [fin_cons_orderEmb_cons_zero] using congrArg Fin.val h0.symm
    | succ j =>
        simpa [fin_cons_orderEmb_cons_zero, fin_cons_orderEmb_drop_head] using
          (Fin.succ_pred (f j.succ) (fin_cons_orderEmb_succ_ne_zero_of_head_zero h0 j))
  · dsimp [fin_cons_orderEmb_sum_toFun, fin_cons_orderEmb_sum_invFun]
    rw [dif_neg h0]
    ext i
    simpa [fin_cons_orderEmb_drop_zero] using
      (Fin.succ_pred (f i) (fin_cons_orderEmb_ne_zero_of_head_ne_zero h0 i))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): reinserting and then deleting
the head `0` recovers the chosen sum-branch embedding. -/
theorem fin_cons_orderEmb_sum_right_inv (m n : ℕ) :
    Function.RightInverse (fin_cons_orderEmb_sum_invFun m n) (fin_cons_orderEmb_sum_toFun m n) := by
  intro x
  cases x with
  | inl g =>
      -- Proof comment: the `0`-avoiding branch is exactly the shifted embedding.
      have h0 : (g.trans (Fin.succOrderEmb (m + 1))) 0 ≠ 0 := by
        simp
      simp [fin_cons_orderEmb_sum_toFun, fin_cons_orderEmb_sum_invFun, h0]
      ext i
      simpa [fin_cons_orderEmb_drop_zero] using
        (Fin.pred_succ (g i))
  | inr g =>
      -- Proof comment: the `0`-hitting branch is exactly the embedding built by adjoining the
      -- head value `0`.
      simp [fin_cons_orderEmb_sum_toFun, fin_cons_orderEmb_sum_invFun]
      apply congrArg Sum.inr
      ext i
      simpa [fin_cons_orderEmb_cons_zero, fin_cons_orderEmb_drop_head] using
        (Fin.pred_succ (g i))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): ordered embeddings into
`Fin (m + 2)` split according to whether they hit the head value `0`. -/
noncomputable def fin_cons_orderEmb_sum_equiv (m n : ℕ) :
    (Fin (n + 1) ↪o Fin (m + 2)) ≃ (Fin (n + 1) ↪o Fin (m + 1)) ⊕ (Fin n ↪o Fin (m + 1)) :=
  { toFun := fin_cons_orderEmb_sum_toFun m n
    invFun := fin_cons_orderEmb_sum_invFun m n
    left_inv := fin_cons_orderEmb_sum_left_inv m n
    right_inv := fin_cons_orderEmb_sum_right_inv m n }

/- The next helper is the remaining combinatorial object from the source proof: positive-degree
subsets of `Fin (m + 2)` should split according to whether they contain the head index `0`. -/
/-- Helper for Remark 10.69.7 (Other types of regular sequences): subsets of `Fin (m + 2)` of
cardinality `n + 1` split into those avoiding `0` and those containing `0`, where the latter are
identified with subsets of `Fin (m + 1)` of cardinality `n`. -/
noncomputable def fin_cons_powersetCard_succ_sum_equiv (m n : ℕ) :
    Set.powersetCard (Fin (m + 2)) (n + 1) ≃
      Set.powersetCard (Fin (m + 1)) (n + 1) ⊕ Set.powersetCard (Fin (m + 1)) n :=
  (Set.powersetCard.ofFinEmbEquiv (I := Fin (m + 2)) (n := n + 1)).symm.trans
    ((fin_cons_orderEmb_sum_equiv m n).trans
      (Equiv.sumCongr
        (Set.powersetCard.ofFinEmbEquiv (I := Fin (m + 1)) (n := n + 1))
        (Set.powersetCard.ofFinEmbEquiv (I := Fin (m + 1)) (n := n))))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in positive degree, the
`Fin.cons` Koszul term splits by whether the chosen exterior-power basis element uses the head
index `0`, giving a product of the two adjacent tail terms. -/
noncomputable def fin_cons_koszul_succ_term_prod_linearEquiv {A : Type u} [CommRing A]
    {m : ℕ} {r : A} (g : Fin (m + 1) → A) (n : ℕ) :
    ((koszulComplexOn (R := A) (Fin.cons r g)).X (n + 1)) ≃ₗ[A]
      (((koszulComplexOn (R := A) g).X (n + 1)) × ((koszulComplexOn (R := A) g).X n)) :=
  let bcons : Module.Basis (Fin (m + 2)) A (Fin (m + 2) → A) := Pi.basisFun A (Fin (m + 2))
  let btail : Module.Basis (Fin (m + 1)) A (Fin (m + 1) → A) := Pi.basisFun A (Fin (m + 1))
  -- Proof comment: reindex the exterior-power basis by the head/non-head subset split, then
  -- identify the resulting sum-indexed basis with the product basis on the two tail terms.
  (((bcons.exteriorPower (n + 1)).reindex
      (fin_cons_powersetCard_succ_sum_equiv m n)).equivFun).trans
    (((btail.exteriorPower (n + 1)).prod (btail.exteriorPower n)).equivFun.symm)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the head/tail term equivalence
sends the reindexed exterior-power basis to the corresponding product-basis branch. -/
theorem fin_cons_koszul_succ_term_prod_linearEquiv_apply_reindex_basis
    {A : Type u} [CommRing A] {m : ℕ} {r : A} (g : Fin (m + 1) → A) (n : ℕ)
    (x :
      Set.powersetCard (Fin (m + 1)) (n + 1) ⊕ Set.powersetCard (Fin (m + 1)) n) :
    let bcons : Module.Basis (Fin (m + 2)) A (Fin (m + 2) → A) := Pi.basisFun A (Fin (m + 2))
    let btail : Module.Basis (Fin (m + 1)) A (Fin (m + 1) → A) := Pi.basisFun A (Fin (m + 1))
    fin_cons_koszul_succ_term_prod_linearEquiv (r := r) g n
      (((bcons.exteriorPower (n + 1)).reindex (fin_cons_powersetCard_succ_sum_equiv m n)) x) =
        Sum.elim
          (fun s ↦ ((btail.exteriorPower (n + 1)) s, 0))
          (fun t ↦ (0, (btail.exteriorPower n) t))
          x := by
  classical
  let breindex :
      Module.Basis
        (Set.powersetCard (Fin (m + 1)) (n + 1) ⊕ Set.powersetCard (Fin (m + 1)) n)
        A ((koszulComplexOn (R := A) (Fin.cons r g)).X (n + 1)) :=
    ((Pi.basisFun A (Fin (m + 2))).exteriorPower (n + 1)).reindex
      (fin_cons_powersetCard_succ_sum_equiv m n)
  let bprod :
      Module.Basis
        (Set.powersetCard (Fin (m + 1)) (n + 1) ⊕ Set.powersetCard (Fin (m + 1)) n)
        A (((koszulComplexOn (R := A) g).X (n + 1)) × ((koszulComplexOn (R := A) g).X n)) :=
    ((Pi.basisFun A (Fin (m + 1))).exteriorPower (n + 1)).prod
      ((Pi.basisFun A (Fin (m + 1))).exteriorPower n)
  -- Proof comment: the reindexed basis vector is sent by `equivFun` to the delta function at
  -- `x`, and the inverse product-basis coordinate equivalence reconstructs the corresponding
  -- product-basis vector.
  dsimp [fin_cons_koszul_succ_term_prod_linearEquiv, breindex, bprod]
  -- Proof comment: only the `x`-summand survives in the basis expansion of the delta function.
  cases x with
  | inl s =>
      have hbreindex :
          breindex.equivFun (breindex (Sum.inl s)) = Pi.single (Sum.inl s) 1 := by
        -- Proof comment: the coordinate function of a basis vector is the corresponding delta
        -- function.
        ext y
        simpa [Pi.single_apply, eq_comm] using
          (Module.Basis.equivFun_self breindex (Sum.inl s) y)
      have hbprod :
          bprod.equivFun.symm (Pi.single (Sum.inl s) 1) = bprod (Sum.inl s) := by
        -- Proof comment: the inverse coordinate equivalence reconstructs the matching product
        -- basis vector from the same delta function.
        simpa using Basis.equivFun_symm_single bprod (Sum.inl s)
      calc
        (breindex.equivFun.trans bprod.equivFun.symm) (breindex (Sum.inl s))
            = bprod.equivFun.symm (breindex.equivFun (breindex (Sum.inl s))) := by
                rfl
        _ = bprod.equivFun.symm (Pi.single (Sum.inl s) 1) := by rw [hbreindex]
        _ = bprod (Sum.inl s) := hbprod
        _ = Sum.elim
              (fun s ↦ ((Module.Basis.exteriorPower (n + 1) (Pi.basisFun A (Fin (m + 1)))) s, 0))
              (fun t ↦ (0, (Module.Basis.exteriorPower n (Pi.basisFun A (Fin (m + 1)))) t))
              (Sum.inl s) := by
              -- Proof comment: the product basis sends the left branch to `(tail basis, 0)`.
              ext
              · exact Module.Basis.prod_apply_inl_fst
                  (b := (Pi.basisFun A (Fin (m + 1))).exteriorPower (n + 1))
                  (b' := (Pi.basisFun A (Fin (m + 1))).exteriorPower n) s
              · exact Module.Basis.prod_apply_inl_snd
                  (b := (Pi.basisFun A (Fin (m + 1))).exteriorPower (n + 1))
                  (b' := (Pi.basisFun A (Fin (m + 1))).exteriorPower n) s
  | inr t =>
      have hbreindex :
          breindex.equivFun (breindex (Sum.inr t)) = Pi.single (Sum.inr t) 1 := by
        -- Proof comment: the right branch is the same delta-function computation on the
        -- reindexed basis.
        ext y
        simpa [Pi.single_apply, eq_comm] using
          (Module.Basis.equivFun_self breindex (Sum.inr t) y)
      have hbprod :
          bprod.equivFun.symm (Pi.single (Sum.inr t) 1) = bprod (Sum.inr t) := by
        -- Proof comment: again, the inverse coordinate equivalence reconstructs the matching
        -- product-basis vector.
        simpa using Basis.equivFun_symm_single bprod (Sum.inr t)
      calc
        (breindex.equivFun.trans bprod.equivFun.symm) (breindex (Sum.inr t))
            = bprod.equivFun.symm (breindex.equivFun (breindex (Sum.inr t))) := by
                rfl
        _ = bprod.equivFun.symm (Pi.single (Sum.inr t) 1) := by rw [hbreindex]
        _ = bprod (Sum.inr t) := hbprod
        _ = Sum.elim
              (fun s ↦ ((Module.Basis.exteriorPower (n + 1) (Pi.basisFun A (Fin (m + 1)))) s, 0))
              (fun t ↦ (0, (Module.Basis.exteriorPower n (Pi.basisFun A (Fin (m + 1)))) t))
              (Sum.inr t) := by
              -- Proof comment: the product basis sends the right branch to `(0, tail basis)`.
              ext
              · exact Module.Basis.prod_apply_inr_fst
                  (b := (Pi.basisFun A (Fin (m + 1))).exteriorPower (n + 1))
                  (b' := (Pi.basisFun A (Fin (m + 1))).exteriorPower n) t
              · exact Module.Basis.prod_apply_inr_snd
                  (b := (Pi.basisFun A (Fin (m + 1))).exteriorPower (n + 1))
                  (b' := (Pi.basisFun A (Fin (m + 1))).exteriorPower n) t

/-- Helper for Remark 10.69.7 (Other types of regular sequences): after tensoring the
`Fin.cons` Koszul complex with `single₀ M`, every positive term splits as the product of the two
adjacent tail terms. -/
noncomputable def fin_cons_tensor_term_iso_tail_prod {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {m : ℕ} {r : A}
    (g : Fin (m + 1) → A) (n : ℕ) :
    ((HomologicalComplex.tensorObj (koszulComplexOn (Fin.cons r g))
      ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X (n + 1)) ≅
      ModuleCat.of A
        (↑((HomologicalComplex.tensorObj (koszulComplexOn g)
            ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X (n + 1)) ×
          ↑((HomologicalComplex.tensorObj (koszulComplexOn g)
            ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X n)) := by
  let econs := tensor_single₀_X_iso_tensorRight
    (K := koszulComplexOn (Fin.cons r g)) (M := M) (n + 1)
  let etail_succ := tensor_single₀_X_iso_tensorRight (K := koszulComplexOn g) (M := M) (n + 1)
  let etail := tensor_single₀_X_iso_tensorRight (K := koszulComplexOn g) (M := M) n
  let esplit :
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj
        ((koszulComplexOn (Fin.cons r g)).X (n + 1))) ≅
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (↑((koszulComplexOn g).X (n + 1)) × ↑((koszulComplexOn g).X n)))) :=
    (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).mapIso
      ((fin_cons_koszul_succ_term_prod_linearEquiv (r := r) g n).toModuleIso))
  let eprod :
      (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (↑((koszulComplexOn g).X (n + 1)) × ↑((koszulComplexOn g).X n)))) ≅
      ModuleCat.of A
        (↑(((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj
            ((koszulComplexOn g).X (n + 1))) ×
          ↑(((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj
            ((koszulComplexOn g).X n))) :=
    (TensorProduct.prodLeft A A ((koszulComplexOn g).X (n + 1)) ((koszulComplexOn g).X n) M).toModuleIso
  let etail_prod :
      ModuleCat.of A
        (↑(((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj
            ((koszulComplexOn g).X (n + 1))) ×
          ↑(((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj
            ((koszulComplexOn g).X n))) ≅
      ModuleCat.of A
        (↑((HomologicalComplex.tensorObj (koszulComplexOn g)
            ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X (n + 1)) ×
          ↑((HomologicalComplex.tensorObj (koszulComplexOn g)
            ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X n)) :=
    (etail_succ.symm.toLinearEquiv.prodCongr etail.symm.toLinearEquiv).toModuleIso
  -- Proof comment: first collapse the tensor term to termwise right tensoring, then split the
  -- `Fin.cons` exterior-power term, commute tensoring with the finite product, and finally undo
  -- the tail term collapses in each factor.
  exact econs ≪≫ esplit ≪≫ eprod ≪≫ etail_prod

end RingTheory.Sequence
