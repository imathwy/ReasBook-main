import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanSmithRange
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.SmithInvariantFactors

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation

universe u

namespace Representation

section PPrimaryCyclicProductUniqueness

variable {ι : Type u}

private def addEquivNsmulKerEquiv {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (m : ℕ) :
    (nsmulAddMonoidHom (α := A) m).ker ≃
      (nsmulAddMonoidHom (α := B) m).ker where
  toFun x :=
    ⟨e x.1, by
      have hx : m • (x : A) = 0 := by simp [x.2]
      simpa [hx] using (map_nsmul e.toAddMonoidHom m (x : A)).symm⟩
  invFun y :=
    ⟨e.symm y.1, by
      have hy : m • (y : B) = 0 := by simp [y.2]
      simpa [hy] using (map_nsmul e.symm m (y : B)).symm⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp

private def piZModNsmulKerEquiv [Fintype ι] (n : ι → ℕ) (m : ℕ) :
    (nsmulAddMonoidHom (α := ((i : ι) → ZMod (n i))) m).ker ≃
      ((i : ι) → (nsmulAddMonoidHom (α := ZMod (n i)) m).ker) where
  toFun x := fun i =>
    ⟨(x : (i : ι) → ZMod (n i)) i, by
      have hx : m • (x : (i : ι) → ZMod (n i)) = 0 := by simp [x.2]
      exact congrFun hx i⟩
  invFun x :=
    ⟨(fun i => (x i : ZMod (n i))), by
      ext i
      exact (x i).2⟩
  left_inv x := by
    ext i
    rfl
  right_inv x := by
    ext i
    rfl

private theorem nat_card_pi_zmod [Fintype ι] (n : ι → ℕ) :
    Nat.card ((i : ι) → ZMod (n i)) = ∏ i, n i := by
  classical
  rw [Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => Nat.card_zmod (n i)

private theorem nat_card_piZMod_nsmul_ker [Fintype ι] (n : ι → ℕ)
    [∀ i, NeZero (n i)] (m : ℕ) :
    Nat.card (nsmulAddMonoidHom (α := ((i : ι) → ZMod (n i))) m).ker =
      ∏ i, Nat.gcd (n i) m := by
  classical
  calc
    Nat.card (nsmulAddMonoidHom (α := ((i : ι) → ZMod (n i))) m).ker =
        Nat.card ((i : ι) → (nsmulAddMonoidHom (α := ZMod (n i)) m).ker) :=
      Nat.card_congr (piZModNsmulKerEquiv n m)
    _ = ∏ i, Nat.card (nsmulAddMonoidHom (α := ZMod (n i)) m).ker := by
      rw [Nat.card_pi]
    _ = ∏ i, Nat.gcd (n i) m := by
      exact Finset.prod_congr rfl fun i _ => by
        rw [IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod (n i)) m, Nat.card_zmod]

private theorem nat_gcd_prime_pow_pow (p e r : ℕ) :
    Nat.gcd (p ^ e) (p ^ r) = p ^ min e r := by
  by_cases h : e ≤ r
  · rw [Nat.gcd_eq_left (pow_dvd_pow p h), Nat.min_eq_left h]
  · have hr : r ≤ e := le_of_not_ge h
    rw [Nat.gcd_eq_right (pow_dvd_pow p hr), Nat.min_eq_right hr]

private theorem sum_min_succ_eq_sum_min_add_card_lt [Fintype ι] (e : ι → ℕ) (r : ℕ) :
    (∑ i, min (e i) (r + 1)) =
      (∑ i, min (e i) r) + Fintype.card {i : ι // r < e i} := by
  classical
  have hpoint : ∀ i : ι,
      min (e i) (r + 1) = min (e i) r + (if r < e i then 1 else 0) := by
    intro i
    by_cases h : r < e i
    · have hsucc : r + 1 ≤ e i := Nat.succ_le_of_lt h
      have hright : min (e i) r = r := Nat.min_eq_right (le_of_lt h)
      have hsucc_right : min (e i) (r + 1) = r + 1 := Nat.min_eq_right hsucc
      calc
        min (e i) (r + 1) = r + 1 := hsucc_right
        _ = min (e i) r + 1 := by rw [hright]
        _ = min (e i) r + (if r < e i then 1 else 0) := by simp [h]
    · have hle : e i ≤ r := le_of_not_gt h
      have hsucc_le : e i ≤ r + 1 := le_trans hle (Nat.le_succ r)
      have hleft : min (e i) r = e i := Nat.min_eq_left hle
      have hsucc_left : min (e i) (r + 1) = e i := Nat.min_eq_left hsucc_le
      simp [h, hleft, hsucc_left]
  calc
    (∑ i, min (e i) (r + 1)) =
        ∑ i, (min (e i) r + (if r < e i then 1 else 0)) := by
      exact Finset.sum_congr rfl fun i _ => hpoint i
    _ = (∑ i, min (e i) r) + ∑ i, (if r < e i then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i, min (e i) r) + Fintype.card {i : ι // r < e i} := by
      rw [Fintype.card_subtype, Finset.card_filter]

private theorem card_eq_fiber_of_card_lt_eq [Fintype ι] (e f : ι → ℕ)
    (h : ∀ r, Fintype.card {i : ι // r < e i} =
      Fintype.card {i : ι // r < f i}) :
    ∀ n, Fintype.card {i : ι // e i = n} =
      Fintype.card {i : ι // f i = n}
  | 0 => by
      classical
      have hpos : (Finset.univ.filter fun i : ι => 0 < e i).card =
          (Finset.univ.filter fun i : ι => 0 < f i).card := by
        simpa [Fintype.card_subtype] using h 0
      have hepart :=
        Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset ι)) (p := fun i : ι => 0 < e i)
      have hfpart :=
        Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset ι)) (p := fun i : ι => 0 < f i)
      have hezero :
          (Finset.univ.filter fun i : ι => e i = 0) =
            (Finset.univ.filter fun i : ι => ¬ 0 < e i) := by
        ext i
        simp
      have hfzero :
          (Finset.univ.filter fun i : ι => f i = 0) =
            (Finset.univ.filter fun i : ι => ¬ 0 < f i) := by
        ext i
        simp
      rw [Fintype.card_subtype, Fintype.card_subtype, hezero, hfzero]
      omega
  | n + 1 => by
      classical
      have hlt_n : (Finset.univ.filter fun i : ι => n < e i).card =
          (Finset.univ.filter fun i : ι => n < f i).card := by
        simpa [Fintype.card_subtype] using h n
      have hlt_succ : (Finset.univ.filter fun i : ι => n + 1 < e i).card =
          (Finset.univ.filter fun i : ι => n + 1 < f i).card := by
        simpa [Fintype.card_subtype] using h (n + 1)
      have hepart :=
        Finset.card_filter_add_card_filter_not
          (s := (Finset.univ.filter fun i : ι => n < e i))
          (p := fun i : ι => n + 1 < e i)
      have hfpart :=
        Finset.card_filter_add_card_filter_not
          (s := (Finset.univ.filter fun i : ι => n < f i))
          (p := fun i : ι => n + 1 < f i)
      have he_gt :
          ((Finset.univ.filter fun i : ι => n < e i).filter
              fun i : ι => n + 1 < e i) =
            (Finset.univ.filter fun i : ι => n + 1 < e i) := by
        ext i
        simp
        omega
      have hf_gt :
          ((Finset.univ.filter fun i : ι => n < f i).filter
              fun i : ι => n + 1 < f i) =
            (Finset.univ.filter fun i : ι => n + 1 < f i) := by
        ext i
        simp
        omega
      have he_eq :
          ((Finset.univ.filter fun i : ι => n < e i).filter
              fun i : ι => ¬ n + 1 < e i) =
            (Finset.univ.filter fun i : ι => e i = n + 1) := by
        ext i
        simp
        omega
      have hf_eq :
          ((Finset.univ.filter fun i : ι => n < f i).filter
              fun i : ι => ¬ n + 1 < f i) =
            (Finset.univ.filter fun i : ι => f i = n + 1) := by
        ext i
        simp
        omega
      rw [Fintype.card_subtype, Fintype.card_subtype]
      rw [← he_eq, ← hf_eq]
      rw [he_gt] at hepart
      rw [hf_gt] at hfpart
      omega

private theorem exists_equiv_of_sum_min_eq [Fintype ι] (e f : ι → ℕ)
    (h : ∀ r, (∑ i, min (e i) r) = ∑ i, min (f i) r) :
    ∃ σ : ι ≃ ι, ∀ i, f i = e (σ i) := by
  classical
  have hlt : ∀ r, Fintype.card {i : ι // r < e i} =
      Fintype.card {i : ι // r < f i} := by
    intro r
    have he := sum_min_succ_eq_sum_min_add_card_lt (ι := ι) e r
    have hf := sum_min_succ_eq_sum_min_add_card_lt (ι := ι) f r
    have h0 := h r
    have h1 := h (r + 1)
    omega
  have hfiber : ∀ n, Fintype.card {i : ι // f i = n} =
      Fintype.card {i : ι // e i = n} := fun n =>
    (card_eq_fiber_of_card_lt_eq (ι := ι) e f hlt n).symm
  let fiberEquiv : ∀ n, {i : ι // f i = n} ≃ {i : ι // e i = n} :=
    fun n => Fintype.equivOfCardEq (hfiber n)
  let σ : ι ≃ ι := Equiv.ofFiberEquiv fiberEquiv
  exact ⟨σ, fun i => (Equiv.ofFiberEquiv_map fiberEquiv i).symm⟩

private theorem pPrimaryCyclicProductUniqueness [Fintype ι] [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (d : ι → ℕ)
    (hd : ∀ i, d i ≠ 0) (hdpow : ∀ i, ∃ e, d i = p ^ e) :
    ∀ a : ι → ℕ,
      Nonempty (((i : ι) → ZMod (d i)) ≃+ ((i : ι) → ZMod (a i))) →
        ∃ σ : ι ≃ ι, ∀ i, a i = d (σ i) := by
  classical
  let ed : ι → ℕ := fun i => Classical.choose (hdpow i)
  have hd_eq : ∀ i, d i = p ^ ed i := fun i => Classical.choose_spec (hdpow i)
  intro a h
  rcases h with ⟨φ⟩
  have hcard : (∏ i, d i) = ∏ i, a i := by
    calc
      (∏ i, d i) = Nat.card ((i : ι) → ZMod (d i)) :=
        (nat_card_pi_zmod (ι := ι) d).symm
      _ = Nat.card ((i : ι) → ZMod (a i)) :=
        Nat.card_congr φ.toEquiv
      _ = ∏ i, a i :=
        nat_card_pi_zmod (ι := ι) a
  have hdprod_ne : (∏ i, d i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact hd i
  have haprod_ne : (∏ i, a i) ≠ 0 := by
    intro hzero
    exact hdprod_ne (hcard.trans hzero)
  have ha : ∀ i, a i ≠ 0 := by
    intro i hi
    exact haprod_ne ((Finset.prod_eq_zero_iff).2 ⟨i, Finset.mem_univ i, hi⟩)
  have hprodDpow : (∏ i, d i) = p ^ (∑ i, ed i) := by
    calc
      (∏ i, d i) = ∏ i, p ^ ed i := by
        exact Finset.prod_congr rfl fun i _ => hd_eq i
      _ = p ^ (∑ i, ed i) := by
        rw [Finset.prod_pow_eq_pow_sum]
  have haPow : ∀ i, ∃ e, a i = p ^ e := by
    intro i
    have hdiv : a i ∣ p ^ (∑ i, ed i) := by
      rw [← hprodDpow, hcard]
      exact Finset.dvd_prod_of_mem a (Finset.mem_univ i)
    rcases (Nat.dvd_prime_pow hp).mp hdiv with ⟨e, _he, heq⟩
    exact ⟨e, heq⟩
  let ea : ι → ℕ := fun i => Classical.choose (haPow i)
  have ha_eq : ∀ i, a i = p ^ ea i := fun i => Classical.choose_spec (haPow i)
  have hker :
      ∀ r, (∏ i, Nat.gcd (d i) (p ^ r)) = ∏ i, Nat.gcd (a i) (p ^ r) := by
    intro r
    letI : ∀ i, NeZero (d i) := fun i => ⟨hd i⟩
    letI : ∀ i, NeZero (a i) := fun i => ⟨ha i⟩
    calc
      (∏ i, Nat.gcd (d i) (p ^ r)) =
          Nat.card
            (nsmulAddMonoidHom (α := ((i : ι) → ZMod (d i))) (p ^ r)).ker :=
        (nat_card_piZMod_nsmul_ker (ι := ι) d (p ^ r)).symm
      _ =
          Nat.card
            (nsmulAddMonoidHom (α := ((i : ι) → ZMod (a i))) (p ^ r)).ker :=
        Nat.card_congr (addEquivNsmulKerEquiv φ (p ^ r))
      _ = ∏ i, Nat.gcd (a i) (p ^ r) :=
        nat_card_piZMod_nsmul_ker (ι := ι) a (p ^ r)
  have hsum : ∀ r, (∑ i, min (ed i) r) = ∑ i, min (ea i) r := by
    intro r
    have hpow :
        p ^ (∑ i, min (ed i) r) = p ^ (∑ i, min (ea i) r) := by
      calc
        p ^ (∑ i, min (ed i) r) = ∏ i, p ^ min (ed i) r := by
          rw [Finset.prod_pow_eq_pow_sum]
        _ = ∏ i, Nat.gcd (d i) (p ^ r) := by
          exact (Finset.prod_congr rfl fun i _ => by
            rw [hd_eq i, nat_gcd_prime_pow_pow]).symm
        _ = ∏ i, Nat.gcd (a i) (p ^ r) := hker r
        _ = ∏ i, p ^ min (ea i) r := by
          exact Finset.prod_congr rfl fun i _ => by
            rw [ha_eq i, nat_gcd_prime_pow_pow]
        _ = p ^ (∑ i, min (ea i) r) := by
          rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_right_injective hp.two_le hpow
  rcases exists_equiv_of_sum_min_eq (ι := ι) ed ea hsum with ⟨σ, hσ⟩
  exact
    ⟨σ, fun i => by
      calc
        a i = p ^ ea i := ha_eq i
        _ = p ^ ed (σ i) := by rw [hσ i]
        _ = d (σ i) := (hd_eq (σ i)).symm⟩

end PPrimaryCyclicProductUniqueness

section CartanCokernelSmith

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanCokernelSmithFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanCokernelSmithDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The cyclic modulus attached to a `p`-regular class is nonzero. -/
theorem centralizerPPart_pRegular_ne_zero
    (c : PRegularConjClass G p) :
    ConjClasses.centralizerPPart p c.1 ≠ 0 := by
  obtain ⟨g, hg⟩ := ConjClasses.mk_surjective c.1
  rw [← hg, ConjClasses.centralizerPPart_mk]
  exact pow_ne_zero _ (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))

/-- The centralizer `p`-part attached to a `p`-regular class is a power of `p`. -/
theorem centralizerPPart_pRegular_eq_prime_pow
    (c : PRegularConjClass G p) :
    ∃ e, ConjClasses.centralizerPPart p c.1 = p ^ e := by
  obtain ⟨g, hg⟩ := ConjClasses.mk_surjective c.1
  refine ⟨(Nat.card (Subgroup.centralizer ({g} : Set G))).factorization p, ?_⟩
  rw [← hg, ConjClasses.centralizerPPart_mk]
  rfl

/-- The product of cyclic groups with centralizer `p`-part moduli has the expected uniqueness
certificate when every cyclic-product presentation of it has the same moduli up to permutation.

This is only a naming wrapper for the finite-abelian-group uniqueness input; it keeps the Cartan
Smith adapter's hypotheses source-facing. -/
def cartanCokernelCentralizerPPartProductUniqueness : Prop :=
  ∀ a : PRegularConjClass G p → ℕ,
    Nonempty
      (((c : PRegularConjClass G p) → ZMod (ConjClasses.centralizerPPart p c.1)) ≃+
        ((c : PRegularConjClass G p) → ZMod (a c))) →
      ∃ σ : PRegularConjClass G p ≃ PRegularConjClass G p,
        ∀ c, a c = ConjClasses.centralizerPPart p (σ c).1

/-- The finite-abelian uniqueness certificate for the centralizer `p`-part cyclic product. -/
theorem cartanCokernelCentralizerPPartProductUniqueness_holds :
    cartanCokernelCentralizerPPartProductUniqueness (p := p) (G := G) := by
  exact
    pPrimaryCyclicProductUniqueness
      (ι := PRegularConjClass G p)
      (p := p)
      (Fact.out : Nat.Prime p)
      (fun c : PRegularConjClass G p => ConjClasses.centralizerPPart p c.1)
      (centralizerPPart_pRegular_ne_zero (p := p) (G := G))
      (centralizerPPart_pRegular_eq_prime_pow (p := p) (G := G))

/-- Source-faithful Smith adapter for Exercise 18-18.3-2.

If Serre's projective-character argument supplies the cokernel product
`coker(c) ≃ Π_s ℤ / |C_G(s)|_p ℤ`, and the corresponding finite-abelian-group uniqueness theorem
identifies these factors as the invariant factors up to permutation, then the Cartan image has
the desired diagonal coordinate description. -/
theorem existsCartanRangeCoordinateEquiv_of_cokernelProduct_and_invariantFactorUniqueness
    (hCokernel :
      Nonempty
        (cartanCokernel k G ≃+
          ((c : PRegularConjClass G p) → ZMod (ConjClasses.centralizerPPart p c.1))))
    (hunique :
      cartanCokernelCentralizerPPartProductUniqueness (p := p) (G := G)) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  classical
  let hbasis : Nonempty (Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G))) :=
    ⟨Classical.choose (simple_basis_on_pRegular_classes_ring_owner (p := p) (k := k) (G := G))⟩
  have hquot :
      Nonempty
        (R₀[k](G) ⧸ (cartanHom k G).range ≃+
          ((c : PRegularConjClass G p) → ZMod (ConjClasses.centralizerPPart p c.1))) := by
    simpa [cartanCokernel] using hCokernel
  have hSmith :
      ∃ (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
        (hfull :
          Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
            Module.finrank ℤ (R₀[k](G)))
        (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
        ∀ c : PRegularConjClass G p,
          Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := (cartanHom k G).range.toIntSubmodule) b hfull c) =
            ConjClasses.centralizerPPart p (σ c).1 := by
    exact
      addSubgroup_exists_smith_coeffs_natAbs_perm_of_quotientEquivPiZMod
        (N := (cartanHom k G).range)
        (hbasis := hbasis)
        (d := fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
        (hd := centralizerPPart_pRegular_ne_zero (p := p) (G := G))
        (hquot := hquot)
        (hunique := hunique)
  exact
    existsCartanRangeCoordinateEquiv_of_exists_smith_coeffs_perm
      (p := p) (k := k) (G := G) hSmith

/-- Source-faithful Smith adapter using the intrinsic `p`-primary uniqueness of the displayed
centralizer product. -/
theorem existsCartanRangeCoordinateEquiv_of_cokernelProduct
    (hCokernel :
      Nonempty
        (cartanCokernel k G ≃+
          ((c : PRegularConjClass G p) → ZMod (ConjClasses.centralizerPPart p c.1)))) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_cokernelProduct_and_invariantFactorUniqueness
    (p := p) (k := k) (G := G)
    hCokernel
    (cartanCokernelCentralizerPPartProductUniqueness_holds (p := p) (G := G))

end CartanCokernelSmith

end Representation
