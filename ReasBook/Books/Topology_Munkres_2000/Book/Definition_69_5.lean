module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Projection

public section

universe uG uι uκ

/- Definition 69.5 (1). The torsion subgroup of an abelian group is the canonical
additive subgroup consisting exactly of the elements of finite order. -/
#check AddCommGroup.torsion
#check AddCommGroup.mem_torsion

/- Definition 69.5 (2). The Betti number of a finitely generated abelian group is
its canonical free rank, equivalently the rank of its quotient by the torsion subgroup. -/
#check AddCommGroup.freeRank
#check AddCommGroup.freeRank_def

/-- Helper for Definition 69.5: the additive-group rank of a finitely generated free
abelian group equals the cardinality of any finite basis. -/
lemma AddGroup.rank_eq_card_basis
    {A : Type uG} [AddCommGroup A] [AddGroup.FG A]
    {ι : Type uι} [Fintype ι] (basis : Module.Basis ι ℤ A) :
    AddGroup.rank A = Fintype.card ι := by
  classical
  -- The basis itself supplies a finite additive generating set.
  let basisFinset : Finset A := Finset.univ.image basis
  have basisFinset_card : basisFinset.card = Fintype.card ι := by
    simpa [basisFinset] using Finset.card_image_of_injective Finset.univ basis.injective
  apply le_antisymm
  · rw [← basisFinset_card]
    apply AddGroup.rank_le
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    have basis_span : Submodule.span ℤ (basisFinset : Set A) = ⊤ := by
      simpa [basisFinset, Set.image_univ] using basis.span_eq
    exact congrArg Submodule.toAddSubgroup basis_span
  · -- A rank-minimizing additive generating set spans the underlying `ℤ`-module.
    obtain ⟨generators, hcard, hclosure⟩ := AddGroup.rank_spec A
    rw [← hcard, ← Module.finrank_eq_card_basis basis]
    have hspan : Submodule.span ℤ (generators : Set A) = ⊤ := by
      apply Submodule.toAddSubgroup_injective
      rw [Submodule.span_int_eq_addSubgroupClosure, hclosure]
      rfl
    rw [← finrank_top ℤ A, ← hspan]
    exact finrank_span_finset_le_card generators

/-- If a subgroup complementary to the torsion subgroup has a finite basis, then
its cardinality is the free rank of the ambient finitely generated abelian group. -/
theorem freeRank_eq_of_isCompl_torsion
    {G : Type uG} [AddCommGroup G] [AddGroup.FG G]
    {H : AddSubgroup G} {ι : Type uι} [Fintype ι]
    (basis : Module.Basis ι ℤ H)
    (hcompl : IsCompl H (AddCommGroup.torsion G)) :
    AddCommGroup.freeRank G = Fintype.card ι := by
  -- The finite basis gives the complement the finite-generation instance needed by rank.
  letI : Module.Finite ℤ H := Module.Finite.of_basis basis
  letI : AddGroup.FG H := Module.Finite.iff_addGroup_fg.mp inferInstance
  rw [AddCommGroup.freeRank_def]
  -- Complementarity identifies the quotient by torsion with the chosen free summand.
  have hcomplModules :
      IsCompl (AddCommGroup.torsion G).toIntSubmodule H.toIntSubmodule := by
    exact ((AddSubgroup.toIntSubmodule : AddSubgroup G ≃o Submodule ℤ G).isCompl_iff).mp
      hcompl.symm
  let quotientEquiv : (G ⧸ AddCommGroup.torsion G) ≃+ H :=
    (Submodule.quotientEquivOfIsCompl
      (AddCommGroup.torsion G).toIntSubmodule H.toIntSubmodule hcomplModules).toAddEquiv
  calc
    AddGroup.rank (G ⧸ AddCommGroup.torsion G) = AddGroup.rank H :=
      AddGroup.rank_congr quotientEquiv
    _ = Fintype.card ι := AddGroup.rank_eq_card_basis basis

/-- Helper for Definition 69.5: additive equivalences preserve the cardinality of the
kernel of multiplication by a natural number. -/
lemma natCard_nsmulKer_eq_of_addEquiv
    {A : Type uι} {B : Type uκ} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (d : ℕ) :
    Nat.card (nsmulAddMonoidHom (α := A) d).ker =
      Nat.card (nsmulAddMonoidHom (α := B) d).ker := by
  -- The equivalence restricts to the kernels because it commutes with `d`-fold addition.
  have ker_mem_iff (a : A) :
      a ∈ (nsmulAddMonoidHom (α := A) d).ker ↔
        e a ∈ (nsmulAddMonoidHom (α := B) d).ker := by
    simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
    constructor
    · intro ha
      calc
        d • e a = e (d • a) := (map_nsmul e d a).symm
        _ = e 0 := congrArg e ha
        _ = 0 := map_zero e
    · intro ha
      apply e.injective
      calc
        e (d • a) = d • e a := map_nsmul e d a
        _ = 0 := ha
        _ = e 0 := (map_zero e).symm
  let kerEquiv : (nsmulAddMonoidHom (α := A) d).ker ≃
      (nsmulAddMonoidHom (α := B) d).ker := e.toEquiv.subtypeEquiv ker_mem_iff
  exact Nat.card_congr kerEquiv

/-- Helper for Definition 69.5: the kernel of pointwise multiplication by `d` is the
product of the coordinate kernels. -/
lemma natCard_nsmulKer_pi
    {ι : Type uι} [Fintype ι] (A : ι → Type uG) [∀ i, AddCommGroup (A i)] (d : ℕ) :
    Nat.card (nsmulAddMonoidHom (α := (i : ι) → A i) d).ker =
      ∏ i, Nat.card (nsmulAddMonoidHom (α := A i) d).ker := by
  -- Membership in the product kernel is exactly coordinatewise kernel membership.
  have mem_ker_iff (f : (i : ι) → A i) :
      f ∈ (nsmulAddMonoidHom (α := (i : ι) → A i) d).ker ↔
        ∀ i, f i ∈ (nsmulAddMonoidHom (α := A i) d).ker := by
    simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, Pi.zero_apply,
      Pi.smul_apply, funext_iff]
  let pointwiseEquiv : (nsmulAddMonoidHom (α := (i : ι) → A i) d).ker ≃
      {f : (i : ι) → A i // ∀ i, f i ∈ (nsmulAddMonoidHom (α := A i) d).ker} :=
    (Equiv.refl _).subtypeEquiv mem_ker_iff
  calc
    Nat.card (nsmulAddMonoidHom (α := (i : ι) → A i) d).ker =
        Nat.card {f : (i : ι) → A i // ∀ i, f i ∈
          (nsmulAddMonoidHom (α := A i) d).ker} := Nat.card_congr pointwiseEquiv
    _ = Nat.card ((i : ι) → (nsmulAddMonoidHom (α := A i) d).ker) :=
      Nat.card_congr Equiv.subtypePiEquivPi
    _ = ∏ i, Nat.card (nsmulAddMonoidHom (α := A i) d).ker := Nat.card_pi

/-- Helper for Definition 69.5: multiplication by `d` on a finite direct sum of
nontrivial cyclic groups has kernel cardinality `∏ i, Nat.gcd (m i) d`. -/
lemma natCard_nsmulKer_directSum_zmod
    {ι : Type uι} [Fintype ι] (m : ι → ℕ) (hm : ∀ i, m i ≠ 0) (d : ℕ) :
    Nat.card (nsmulAddMonoidHom (α := DirectSum ι (fun i ↦ ZMod (m i))) d).ker =
      ∏ i, Nat.gcd (m i) d := by
  letI (i : ι) : NeZero (m i) := ⟨hm i⟩
  -- Move to the finite product, then use the cyclic kernel formula coordinatewise.
  calc
    Nat.card (nsmulAddMonoidHom (α := DirectSum ι (fun i ↦ ZMod (m i))) d).ker =
        Nat.card (nsmulAddMonoidHom (α := (i : ι) → ZMod (m i)) d).ker :=
      natCard_nsmulKer_eq_of_addEquiv (DirectSum.addEquivProd fun i ↦ ZMod (m i)) d
    _ = ∏ i, Nat.card (nsmulAddMonoidHom (α := ZMod (m i)) d).ker :=
      natCard_nsmulKer_pi (fun i ↦ ZMod (m i)) d
    _ = ∏ i, Nat.gcd (m i) d := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod]

/-- Helper for Definition 69.5: factorization at a prime converts a finite product
of gcds with a prime power into a sum of truncated factorization exponents. -/
private lemma factorization_gcdProduct_primePow
    {ι : Type uι} [Fintype ι] (a : ι → ℕ) (ha : ∀ i, a i ≠ 0)
    {p k : ℕ} (hp : p.Prime) :
    (∏ i, Nat.gcd (a i) (p ^ k)).factorization p =
      ∑ i, min ((a i).factorization p) k := by
  classical
  -- Factor the product first, then compute each gcd coordinate at `p`.
  rw [Nat.factorization_prod_apply]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.factorization_gcd (ha i) (pow_ne_zero k hp.ne_zero)]
    simp only [Finsupp.inf_apply, hp.factorization_pow, Finsupp.single_eq_same]
  · intro i hi
    exact Nat.gcd_ne_zero_left (ha i)

/-- Helper for Definition 69.5: the first finite difference of a sum of truncated
natural numbers counts the entries above the truncation threshold. -/
private lemma sum_min_succ_eq_add_card_gt
    {ι : Type uι} [Fintype ι] (a : ι → ℕ) (k : ℕ) :
    (∑ i, min (a i) (k + 1)) =
      (∑ i, min (a i) k) + Fintype.card {i // k < a i} := by
  classical
  -- Rewrite the subtype cardinality as a Boolean sum and compare pointwise.
  have hcard : Fintype.card {i // k < a i} =
      ∑ i, if k < a i then 1 else 0 := by
    rw [Fintype.card_subtype]
    exact (Finset.sum_boole (R := ℕ) (fun i ↦ k < a i) Finset.univ).symm
  rw [hcard, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hki : k < a i
  · simp only [hki, if_true]
    omega
  · simp only [hki, if_false, add_zero]
    omega

/-- Helper for Definition 69.5: equality of all truncated-sum profiles gives
equality of the cardinalities above every threshold. -/
private lemma card_gt_eq_of_sum_min_eq
    {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (hsum : ∀ k, ∑ i, min (a i) k = ∑ j, min (b j) k) (k : ℕ) :
    Fintype.card {i // k < a i} = Fintype.card {j // k < b j} := by
  -- Compare successive profiles and cancel their common value at `k`.
  have hsucc := hsum (k + 1)
  rw [sum_min_succ_eq_add_card_gt a k, sum_min_succ_eq_add_card_gt b k,
    hsum k] at hsucc
  exact Nat.add_left_cancel hsucc

/-- Helper for Definition 69.5: equality of all strict-threshold counts gives
equality of the multiplicity of every positive natural value. -/
private lemma card_eq_succ_of_card_gt_eq
    {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    (a : ι → ℕ) (b : κ → ℕ)
    (hgt : ∀ k, Fintype.card {i // k < a i} = Fintype.card {j // k < b j})
    (k : ℕ) :
    Fintype.card {i // a i = k + 1} = Fintype.card {j // b j = k + 1} := by
  classical
  -- Split each threshold fiber into the exact next value and the higher threshold.
  have thresholdCard (c : ι → ℕ) :
      Fintype.card {i // k < c i} =
        Fintype.card {i // c i = k + 1} + Fintype.card {i // k + 1 < c i} := by
    calc
      Fintype.card {i // k < c i} =
          Fintype.card {i // c i = k + 1 ∨ k + 1 < c i} := by
        have hpred (i : ι) : k < c i ↔ c i = k + 1 ∨ k + 1 < c i := by
          omega
        apply Fintype.card_congr
        exact (Equiv.refl ι).subtypeEquiv hpred
      _ = Fintype.card {i // c i = k + 1} + Fintype.card {i // k + 1 < c i} := by
        apply Fintype.card_subtype_or_disjoint
        exact Set.disjoint_left.2 (fun i hi hj ↦ by
          change c i = k + 1 at hi
          change k + 1 < c i at hj
          rw [hi] at hj
          exact (Nat.lt_irrefl _ hj))
  have thresholdCard' (c : κ → ℕ) :
      Fintype.card {j // k < c j} =
        Fintype.card {j // c j = k + 1} + Fintype.card {j // k + 1 < c j} := by
    calc
      Fintype.card {j // k < c j} =
          Fintype.card {j // c j = k + 1 ∨ k + 1 < c j} := by
        have hpred (j : κ) : k < c j ↔ c j = k + 1 ∨ k + 1 < c j := by
          omega
        apply Fintype.card_congr
        exact (Equiv.refl κ).subtypeEquiv hpred
      _ = Fintype.card {j // c j = k + 1} + Fintype.card {j // k + 1 < c j} := by
        apply Fintype.card_subtype_or_disjoint
        exact Set.disjoint_left.2 (fun j hj hl ↦ by
          change c j = k + 1 at hj
          change k + 1 < c j at hl
          rw [hj] at hl
          exact (Nat.lt_irrefl _ hl))
  have hthreshold := hgt k
  rw [thresholdCard a, thresholdCard' b, hgt (k + 1)] at hthreshold
  exact Nat.add_right_cancel hthreshold

/-- Helper for Definition 69.5: two prime powers with the same positive
factorization exponent at the second one's least prime factor are equal. -/
private lemma primePower_eq_of_factorization_minFac_eq
    {a q : ℕ} (ha : IsPrimePow a) (hq : IsPrimePow q)
    (hfactor : a.factorization q.minFac = q.factorization q.minFac) : a = q := by
  -- Expand both prime powers; positivity rules out distinct prime bases.
  obtain ⟨p, r, hp, hr, rfl⟩ := ha
  obtain ⟨s, t, hs, ht, rfl⟩ := hq
  rw [← Nat.prime_iff] at hp hs
  rw [hs.pow_minFac ht.ne', hp.factorization_pow, hs.factorization_pow] at hfactor
  simp only [Finsupp.single_apply] at hfactor
  by_cases hps : p = s
  · subst s
    simp only [if_true] at hfactor
    subst t
    rfl
  · simp only [hps, if_false, if_true] at hfactor
    omega

/-- Helper for Definition 69.5: equal gcd-product profiles give equal cardinalities
for every prime-power-valued fiber. -/
private lemma primePowerFiber_card_eq_of_gcdProducts_eq
    {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    (m : ι → ℕ) (n : κ → ℕ)
    (hm : ∀ i, IsPrimePow (m i)) (hn : ∀ j, IsPrimePow (n j))
    (hprofile : ∀ d, ∏ i, Nat.gcd (m i) d = ∏ j, Nat.gcd (n j) d)
    {q : ℕ} (hq : IsPrimePow q) :
    Fintype.card {i // m i = q} = Fintype.card {j // n j = q} := by
  classical
  let p := q.minFac
  let e := q.factorization p
  have hp : p.Prime := by
    exact Nat.minFac_prime (hq.ne_one)
  have he : e ≠ 0 := by
    exact Nat.factorization_minFac_ne_zero hq.one_lt
  -- Specialize the profile to `p ^ k` and take the `p`-factorization coordinate.
  have hsum (k : ℕ) :
      ∑ i, min ((m i).factorization p) k =
        ∑ j, min ((n j).factorization p) k := by
    have hfactor := congrArg (fun x : ℕ ↦ x.factorization p) (hprofile (p ^ k))
    rw [factorization_gcdProduct_primePow m (fun i ↦ (hm i).ne_zero) hp,
      factorization_gcdProduct_primePow n (fun j ↦ (hn j).ne_zero) hp] at hfactor
    exact hfactor
  have hgt (k : ℕ) :
      Fintype.card {i // k < (m i).factorization p} =
        Fintype.card {j // k < (n j).factorization p} := by
    exact card_gt_eq_of_sum_min_eq
      (fun i ↦ (m i).factorization p) (fun j ↦ (n j).factorization p) hsum k
  have hexact :
      Fintype.card {i // (m i).factorization p = e} =
        Fintype.card {j // (n j).factorization p = e} := by
    have h := card_eq_succ_of_card_gt_eq
      (fun i ↦ (m i).factorization p) (fun j ↦ (n j).factorization p) hgt (e - 1)
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)] using h
  -- Prime-power uniqueness identifies the exact exponent fibers with the order fibers.
  calc
    Fintype.card {i // m i = q} =
        Fintype.card {i // (m i).factorization p = e} := by
      have hpred (i : ι) : m i = q ↔ (m i).factorization p = e := by
        constructor
        · intro hi
          simpa [p, e] using congrArg (fun x : ℕ ↦ x.factorization q.minFac) hi
        · intro hi
          exact primePower_eq_of_factorization_minFac_eq (hm i) hq (by simpa [p, e] using hi)
      apply Fintype.card_congr
      exact (Equiv.refl ι).subtypeEquiv hpred
    _ = Fintype.card {j // (n j).factorization p = e} := hexact
    _ = Fintype.card {j // n j = q} := by
      have hpred (j : κ) : (n j).factorization p = e ↔ n j = q := by
        constructor
        · intro hj
          exact primePower_eq_of_factorization_minFac_eq (hn j) hq (by simpa [p, e] using hj)
        · intro hj
          simpa [p, e] using congrArg (fun x : ℕ ↦ x.factorization q.minFac) hj
      apply Fintype.card_congr
      exact (Equiv.refl κ).subtypeEquiv hpred

/-- Helper for Definition 69.5: equal multiplication-kernel profiles determine finite
families of positive prime powers up to reindexing. -/
lemma equivOf_primePower_gcdProducts_eq
    {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    (m : ι → ℕ) (n : κ → ℕ)
    (hm : ∀ i, IsPrimePow (m i)) (hn : ∀ j, IsPrimePow (n j))
    (hprofile : ∀ d, ∏ i, Nat.gcd (m i) d = ∏ j, Nat.gcd (n j) d) :
    ∃ σ : ι ≃ κ, ∀ i, m i = n (σ i) := by
  classical
  -- Match each value fiber, using the arithmetic reconstruction on prime powers.
  have fiberEquiv (q : ℕ) : {i // m i = q} ≃ {j // n j = q} := by
    by_cases hq : IsPrimePow q
    · exact Fintype.equivOfCardEq
        (primePowerFiber_card_eq_of_gcdProducts_eq m n hm hn hprofile hq)
    · have leftEmpty : IsEmpty {i // m i = q} :=
        ⟨fun i ↦ hq (i.property ▸ hm i)⟩
      have rightEmpty : IsEmpty {j // n j = q} :=
        ⟨fun j ↦ hq (j.property ▸ hn j)⟩
      exact Fintype.equivOfCardEq (by simp)
  let σ : ι ≃ κ := Equiv.ofFiberEquiv fiberEquiv
  refine ⟨σ, fun i ↦ ?_⟩
  -- The assembled equivalence preserves the family value by construction.
  exact (Equiv.ofFiberEquiv_map fiberEquiv i).symm

/-- Definition 69.5 (3). Two decompositions of the torsion subgroup into cyclic
groups of prime-power order have the same factor orders up to reindexing. -/
theorem elementaryDivisors_unique
    {G : Type uG} {ι : Type uι} {κ : Type uκ}
    [AddCommGroup G] [Finite ι] [Finite κ]
    (m : ι → ℕ) (n : κ → ℕ)
    (hm : ∀ i, IsPrimePow (m i)) (hn : ∀ j, IsPrimePow (n j))
    (decompM : AddCommGroup.torsion G ≃+ DirectSum ι (fun i ↦ ZMod (m i)))
    (decompN : AddCommGroup.torsion G ≃+ DirectSum κ (fun j ↦ ZMod (n j))) :
    ∃ σ : ι ≃ κ, ∀ i, m i = n (σ i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  -- The two decompositions give identical multiplication-kernel profiles.
  have hprofile (d : ℕ) :
      ∏ i, Nat.gcd (m i) d = ∏ j, Nat.gcd (n j) d := by
    calc
      ∏ i, Nat.gcd (m i) d =
          Nat.card (nsmulAddMonoidHom
            (α := DirectSum ι (fun i ↦ ZMod (m i))) d).ker :=
        (natCard_nsmulKer_directSum_zmod m (fun i ↦ (hm i).ne_zero) d).symm
      _ = Nat.card (nsmulAddMonoidHom (α := AddCommGroup.torsion G) d).ker :=
        natCard_nsmulKer_eq_of_addEquiv decompM.symm d
      _ = Nat.card (nsmulAddMonoidHom
          (α := DirectSum κ (fun j ↦ ZMod (n j))) d).ker :=
        natCard_nsmulKer_eq_of_addEquiv decompN d
      _ = ∏ j, Nat.gcd (n j) d :=
        natCard_nsmulKer_directSum_zmod n (fun j ↦ (hn j).ne_zero) d
  -- The arithmetic reconstruction of prime-power fibers finishes the reindexing.
  exact equivOf_primePower_gcdProducts_eq m n hm hn hprofile
