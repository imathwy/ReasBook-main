import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Data.Finset.Card
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open HomogeneousIdeal

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Domain triage:
* source-facing: a homogeneous ideal inside the irrelevant ideal contains a positive-degree
  homogeneous element avoiding finitely many homogeneous prime ideals.
* core/canonical owner: `ProjectiveSpectrum 𝒜`.
* bridge/view: the private theorem works at the owner level, and the public theorem upgrades a
  finite family of homogeneous prime ideals to points of `Proj` by deriving relevance from
  `I ≤ 𝒜₊` and `¬ I ≤ p i`.
-/

/-- Helper for Lemma 10.57.6: the finite product of homogeneous ideals is homogeneous. -/
private lemma family_product_isHomogeneous {ι : Type*}
    (p : ι → HomogeneousIdeal 𝒜) (s : Finset ι) :
    (s.prod fun i ↦ (p i).toIdeal).IsHomogeneous 𝒜 := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      -- The empty product is `⊤`, which is homogeneous.
      simpa using (Ideal.IsHomogeneous.top (𝒜 := 𝒜))
  | @cons i s hi hs =>
      -- Insert one factor and use closure of homogeneous ideals under multiplication.
      simpa [Finset.prod_insert hi] using
        Ideal.IsHomogeneous.mul (𝒜 := 𝒜) (p i).isHomogeneous hs

/-- Helper for Lemma 10.57.6: the product ideal associated to a finite family of homogeneous
prime ideals. -/
private def familyProduct {ι : Type*} [DecidableEq ι]
    (p : ι → HomogeneousIdeal 𝒜) (s : Finset ι) : HomogeneousIdeal 𝒜 :=
  ⟨s.prod fun i ↦ (p i).toIdeal, family_product_isHomogeneous 𝒜 p s⟩

/-- Helper for Lemma 10.57.6: inserting a new factor multiplies the family product by that factor.
-/
private lemma familyProduct_insert {ι : Type*} [DecidableEq ι]
    (p : ι → HomogeneousIdeal 𝒜) {i : ι} {s : Finset ι} (hi : i ∉ s) :
    familyProduct 𝒜 p (insert i s) = p i * familyProduct 𝒜 p s := by
  -- Both sides have the same underlying ideal product.
  apply HomogeneousIdeal.ext
  simp [familyProduct, hi, Finset.prod_insert, HomogeneousIdeal.toIdeal_mul]

/-- Helper for Lemma 10.57.6: the family product is contained in each factor that appears in the
finite family. -/
private lemma familyProduct_le_of_mem {ι : Type*} [DecidableEq ι]
    (p : ι → HomogeneousIdeal 𝒜) {s : Finset ι} {i : ι} (hi : i ∈ s) :
    familyProduct 𝒜 p s ≤ p i := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      cases hi
  | @cons j s hj hs =>
      simp only [Finset.mem_cons] at hi
      have hcons : familyProduct 𝒜 p (Finset.cons j s hj) = p j * familyProduct 𝒜 p s := by
        simpa [Finset.cons_eq_insert] using (familyProduct_insert 𝒜 p hj)
      rw [hcons]
      rcases hi with rfl | hi
      · -- The factor indexed by `j` contains the whole product.
        change (p i).toIdeal * (familyProduct 𝒜 p s).toIdeal ≤ (p i).toIdeal
        simpa [HomogeneousIdeal.toIdeal_mul] using
          (Ideal.mul_le_right : (p i).toIdeal * (familyProduct 𝒜 p s).toIdeal ≤ (p i).toIdeal)
      · -- Otherwise the product is first contained in the tail product, then in the target factor.
        exact le_trans
          (by
            change (p j).toIdeal * (familyProduct 𝒜 p s).toIdeal ≤
                (familyProduct 𝒜 p s).toIdeal
            simpa [HomogeneousIdeal.toIdeal_mul] using
              (Ideal.mul_le_left :
                (p j).toIdeal * (familyProduct 𝒜 p s).toIdeal ≤
                  (familyProduct 𝒜 p s).toIdeal))
          (hs hi)

/-- Helper for Lemma 10.57.6: if a prime homogeneous ideal contains the product of a finite family,
then it contains one of the factors. -/
private lemma family_product_not_le_of_forall_factor_not_le {ι : Type*} [DecidableEq ι]
    (p : ι → HomogeneousIdeal 𝒜) (s : Finset ι) (q : HomogeneousIdeal 𝒜)
    (hq : q.toIdeal.IsPrime) (havoid : ∀ i ∈ s, ¬ p i ≤ q) :
    ¬ familyProduct 𝒜 p s ≤ q := by
  intro hle
  -- Prime containment of a finite product forces containment of one factor.
  rcases (Ideal.IsPrime.prod_le (s := s) (f := fun i ↦ (p i).toIdeal) hq).1
      (by simpa [familyProduct] using (show (familyProduct 𝒜 p s).toIdeal ≤ q.toIdeal from hle)) with
    ⟨i, hi, hip⟩
  exact havoid i hi hip

/-- Helper for Lemma 10.57.6: a homogeneous ideal not contained in a homogeneous prime contains a
positive-degree homogeneous element outside that prime once it lies in the irrelevant ideal. -/
private lemma exists_pos_degree_mem_and_not_mem_of_not_le_prime
    (I P : HomogeneousIdeal 𝒜) (hI_irrelevant : I ≤ 𝒜₊) (havoid : ¬ I ≤ P) :
    ∃ x ∈ I, ∃ d > 0, x ∈ 𝒜 d ∧ x ∉ P := by
  classical
  by_cases hex : ∃ z, z ∈ I ∧ z ∉ P
  · obtain ⟨z, hzI, hzP⟩ := hex
    have hzI_decomp : ∀ d, (DirectSum.decompose 𝒜 z d : A) ∈ I :=
      (Ideal.IsHomogeneous.mem_iff (𝒜 := 𝒜) I.isHomogeneous).1 hzI
    have hnotall : ¬ ∀ d, (DirectSum.decompose 𝒜 z d : A) ∈ P := by
      intro hall
      exact hzP <| (Ideal.IsHomogeneous.mem_iff (𝒜 := 𝒜) P.isHomogeneous).2 hall
    obtain ⟨d, hdP⟩ := not_forall.mp hnotall
    let x : A := DirectSum.decompose 𝒜 z d
    have hxI : x ∈ I := hzI_decomp d
    have hxd : x ∈ 𝒜 d := SetLike.coe_mem _
    have hxP : x ∉ P := hdP
    have hx0 : x ≠ 0 := fun hx ↦ hxP (hx ▸ P.zero_mem)
    -- The irrelevant-ideal hypothesis rules out degree `0` for a nonzero homogeneous witness.
    have hdpos : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
      have hxirr0 : GradedRing.proj 𝒜 0 x = 0 := by
        simpa [HomogeneousIdeal.mem_irrelevant_iff] using hI_irrelevant hxI
      have hproj0 : GradedRing.proj 𝒜 0 x = x := by
        simpa [GradedRing.proj_apply, hd0] using
          (DirectSum.decompose_of_mem_same 𝒜 (hd0 ▸ hxd))
      exact hx0 <| by
        rw [← hproj0, hxirr0]
    exact ⟨x, hxI, d, hdpos, hxd, hxP⟩
  · exfalso
    apply havoid
    intro z hzI
    by_contra hzP
    exact hex ⟨z, hzI, hzP⟩

/-- Helper for Lemma 10.57.6: two powers of homogeneous elements with swapped exponents have the
same degree, so their sum is homogeneous. -/
private lemma pow_swap_add_mem_mul_degree {x y : A} {dx dy : ℕ}
    (hx : x ∈ 𝒜 dx) (hy : y ∈ 𝒜 dy) :
    x ^ dy + y ^ dx ∈ 𝒜 (dx * dy) := by
  -- Each summand lands in degree `dx * dy`, so the sum stays in that degree.
  have hxpow : x ^ dy ∈ 𝒜 (dx * dy) := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded dy hx
  have hypow : y ^ dx ∈ 𝒜 (dx * dy) := by
    simpa [nsmul_eq_mul] using SetLike.pow_mem_graded dx hy
  exact add_mem hxpow hypow

/-- Helper for Lemma 10.57.6: finite homogeneous-prime avoidance for an arbitrary finite index set.
-/
private theorem exists_pos_degree_mem_avoid_homogeneous_primes_finset
    {ι : Type*} (s : Finset ι) (I : HomogeneousIdeal 𝒜)
    (p : ι → HomogeneousIdeal 𝒜) (hprime : ∀ i ∈ s, (p i).toIdeal.IsPrime)
    (hI_irrelevant : I ≤ 𝒜₊) (havoid : ∀ i ∈ s, ¬ I ≤ p i) :
    ∃ x ∈ I, ∃ d > 0, x ∈ 𝒜 d ∧ ∀ i ∈ s, x ∉ p i := by
  classical
  -- Route correction: prove the positive-degree theorem directly by finite-set induction; the
  -- owner-level `Proj` statement will then be derived from it by multiplying with `𝒜₊`.
  revert hprime havoid
  refine s.strongInductionOn ?_
  intro s ih hprime havoid
  by_cases hs : s.Nonempty
  · obtain ⟨i₀, hi₀, hmin⟩ := s.exists_minimalFor p hs
    let t := s.erase i₀
    by_cases ht : t.Nonempty
    · have htss : t ⊂ s := by
        simpa [t] using Finset.erase_ssubset hi₀
      have hprime_t : ∀ i ∈ t, (p i).toIdeal.IsPrime := by
        intro i hi
        exact hprime i (by simpa [t] using Finset.mem_of_mem_erase hi)
      have havoid_t : ∀ i ∈ t, ¬ I ≤ p i := by
        intro i hi
        exact havoid i (by simpa [t] using Finset.mem_of_mem_erase hi)
      obtain ⟨x, hxI, dx, hdxpos, hxd, hxavoid_t⟩ :=
        ih t htss hprime_t havoid_t
      by_cases hxPi₀ : x ∈ p i₀
      · have hfactor_avoid : ∀ i ∈ t, ¬ p i ≤ p i₀ := by
          intro i hi hle
          have hi_s : i ∈ s := by
            simpa [t] using Finset.mem_of_mem_erase hi
          have hi₀le : p i₀ ≤ p i := hmin hi_s hle
          exact hxavoid_t i hi (hi₀le hxPi₀)
        have hfamily_not_le : ¬ familyProduct 𝒜 p t ≤ p i₀ :=
          family_product_not_le_of_forall_factor_not_le 𝒜 p t (p i₀) (hprime i₀ hi₀) hfactor_avoid
        have hprod_le_I : I * familyProduct 𝒜 p t ≤ I := by
          change I.toIdeal * (familyProduct 𝒜 p t).toIdeal ≤ I.toIdeal
          simpa [HomogeneousIdeal.toIdeal_mul] using
            (Ideal.mul_le_right : I.toIdeal * (familyProduct 𝒜 p t).toIdeal ≤ I.toIdeal)
        have hprod_irrelevant : I * familyProduct 𝒜 p t ≤ 𝒜₊ := hprod_le_I.trans hI_irrelevant
        have hprod_not_le : ¬ I * familyProduct 𝒜 p t ≤ p i₀ := by
          intro hle
          rcases (Ideal.IsPrime.mul_le (P := (p i₀).toIdeal) (hprime i₀ hi₀)).1
              (by simpa [HomogeneousIdeal.toIdeal_mul] using
                (show (I * familyProduct 𝒜 p t).toIdeal ≤ (p i₀).toIdeal from hle)) with
            hIle | hFle
          · exact havoid i₀ hi₀ hIle
          · exact hfamily_not_le hFle
        obtain ⟨y, hyProd, dy, hdypos, hyd, hyPi₀⟩ :=
          exists_pos_degree_mem_and_not_mem_of_not_le_prime 𝒜
            (I * familyProduct 𝒜 p t) (p i₀) hprod_irrelevant hprod_not_le
        have hyI : y ∈ I := hprod_le_I hyProd
        have hxPowI : x ^ dy ∈ I := I.toIdeal.pow_mem_of_mem hxI dy hdypos
        have hyPowI : y ^ dx ∈ I := I.toIdeal.pow_mem_of_mem hyI dx hdxpos
        have hzI : x ^ dy + y ^ dx ∈ I := I.add_mem hxPowI hyPowI
        have hzPi₀ : x ^ dy + y ^ dx ∉ p i₀ := by
          intro hzmem
          have hxPowPi₀ : x ^ dy ∈ p i₀ := (p i₀).toIdeal.pow_mem_of_mem hxPi₀ dy hdypos
          have hyPowPi₀ : y ^ dx ∈ p i₀ := by
            have : x ^ dy + y ^ dx - x ^ dy ∈ p i₀ := (p i₀).toIdeal.sub_mem hzmem hxPowPi₀
            simpa [add_comm, add_left_comm, add_assoc] using this
          exact hyPi₀ <| ((hprime i₀ hi₀).pow_mem_iff_mem dx hdxpos).1 hyPowPi₀
        have hzavoid_t : ∀ i ∈ t, x ^ dy + y ^ dx ∉ p i := by
          intro i hi hzmem
          have hyFamily : y ∈ familyProduct 𝒜 p t := by
            have hprod_le_family : (I * familyProduct 𝒜 p t).toIdeal ≤ (familyProduct 𝒜 p t).toIdeal := by
              simpa [HomogeneousIdeal.toIdeal_mul] using
                (Ideal.mul_le_left :
                  I.toIdeal * (familyProduct 𝒜 p t).toIdeal ≤ (familyProduct 𝒜 p t).toIdeal)
            exact hprod_le_family hyProd
          have hyPi : y ∈ p i := familyProduct_le_of_mem 𝒜 p hi hyFamily
          have hyPowPi : y ^ dx ∈ p i := (p i).toIdeal.pow_mem_of_mem hyPi dx hdxpos
          have hxPowPi : x ^ dy ∈ p i := by
            have : x ^ dy + y ^ dx - y ^ dx ∈ p i := (p i).toIdeal.sub_mem hzmem hyPowPi
            simpa [add_comm, add_left_comm, add_assoc] using this
          exact hxavoid_t i hi <| ((hprime_t i hi).pow_mem_iff_mem dy hdypos).1 hxPowPi
        exact ⟨x ^ dy + y ^ dx, hzI, dx * dy, Nat.mul_pos hdxpos hdypos,
          pow_swap_add_mem_mul_degree 𝒜 hxd hyd, by
            intro i hi
            by_cases hii₀ : i = i₀
            · simpa [hii₀] using hzPi₀
            · have hit : i ∈ t := by
                simpa [t, hii₀] using hi
              exact hzavoid_t i hit⟩
      · exact ⟨x, hxI, dx, hdxpos, hxd, by
          intro i hi
          by_cases hii₀ : i = i₀
          · simpa [hii₀] using hxPi₀
          · have hit : i ∈ t := by
              simpa [t, hii₀] using hi
            exact hxavoid_t i hit⟩
    · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      obtain ⟨x, hxI, d, hdpos, hxd, hxPi₀⟩ :=
        exists_pos_degree_mem_and_not_mem_of_not_le_prime 𝒜
          I (p i₀) hI_irrelevant (havoid i₀ hi₀)
      exact ⟨x, hxI, d, hdpos, hxd, by
        intro i hi
        have hii₀ : i = i₀ := by
          by_contra hii₀
          have : i ∈ t := by
            simpa [t, hii₀] using hi
          simpa [ht0] using this
        simpa [hii₀] using hxPi₀⟩
  · -- For the empty family, the zero element is a vacuous witness of positive degree.
    refine ⟨0, I.zero_mem, 1, zero_lt_one, ?_, ?_⟩
    · simpa using (show (0 : A) ∈ 𝒜 1 from ZeroMemClass.coe_zero)
    · intro i hi
      have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have : False := by
        simpa [hs0] using hi
      exact this.elim

/-- Lemma 10.57.6: if a homogeneous ideal `I` is contained in the irrelevant ideal and is not
contained in any of finitely many homogeneous prime ideals, then `I` contains a homogeneous element
of positive degree that avoids all of those prime ideals. -/
@[stacks 00JS]
theorem exists_pos_degree_mem_avoid_homogeneous_primes
    {r : ℕ} (I : HomogeneousIdeal 𝒜) (p : Fin r → HomogeneousIdeal 𝒜)
    (hprime : ∀ i, (p i).toIdeal.IsPrime) (hI_irrelevant : I ≤ 𝒜₊) (havoid : ∀ i, ¬ I ≤ p i) :
    ∃ x ∈ I, ∃ d > 0, x ∈ 𝒜 d ∧ ∀ i, x ∉ p i := by
  -- Specialize the finite-set theorem to `Finset.univ`.
  simpa using exists_pos_degree_mem_avoid_homogeneous_primes_finset 𝒜
    (Finset.univ : Finset (Fin r)) I p (fun i _ ↦ hprime i) hI_irrelevant (fun i _ ↦ havoid i)

/-- Internal owner-level bridge: a homogeneous ideal contains a homogeneous element avoiding
finitely many relevant homogeneous primes as soon as it is not contained in any of them. -/
private theorem exists_isHomogeneousElem_mem_and_avoid
    {r : ℕ} (I : HomogeneousIdeal 𝒜) (p : Fin r → ProjectiveSpectrum 𝒜)
    (havoid : ∀ i, ¬ I ≤ (p i).asHomogeneousIdeal) :
    ∃ x ∈ I, SetLike.IsHomogeneousElem 𝒜 x ∧ ∀ i, x ∉ (p i).asHomogeneousIdeal := by
  -- Multiply by the irrelevant ideal to force positive degree, then forget the degree afterwards.
  have hprod_le_I : I * 𝒜₊ ≤ I := by
    change I.toIdeal * (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal ≤ I.toIdeal
    simpa [HomogeneousIdeal.toIdeal_mul] using
      (Ideal.mul_le_right : I.toIdeal * (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal ≤ I.toIdeal)
  have hprod_irrelevant : I * 𝒜₊ ≤ 𝒜₊ := by
    change I.toIdeal * (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal ≤
        (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal
    simpa [HomogeneousIdeal.toIdeal_mul] using
      (Ideal.mul_le_left : I.toIdeal * (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal ≤
        (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
  have hprod_avoid : ∀ i, ¬ I * 𝒜₊ ≤ (p i).asHomogeneousIdeal := by
    intro i hle
    rcases (Ideal.IsPrime.mul_le (P := (p i).asHomogeneousIdeal.toIdeal) (p i).isPrime).1
        (by simpa [HomogeneousIdeal.toIdeal_mul] using
          (show (I * 𝒜₊).toIdeal ≤ (p i).asHomogeneousIdeal.toIdeal from hle)) with
      hIle | hIrr
    · exact havoid i hIle
    · exact (p i).not_irrelevant_le hIrr
  obtain ⟨x, hxProd, d, hdpos, hxd, hxavoid⟩ :=
    exists_pos_degree_mem_avoid_homogeneous_primes 𝒜 (I * 𝒜₊)
      (fun i ↦ (p i).asHomogeneousIdeal) (fun i ↦ (p i).isPrime) hprod_irrelevant hprod_avoid
  exact ⟨x, hprod_le_I hxProd, ⟨d, hxd⟩, hxavoid⟩

end
