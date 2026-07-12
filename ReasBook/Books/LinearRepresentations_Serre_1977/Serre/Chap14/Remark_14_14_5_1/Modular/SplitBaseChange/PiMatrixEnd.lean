import Mathlib

noncomputable section
universe u
open scoped TensorProduct

namespace Serre.SplitBaseChange

theorem finrank_end_eq_one_pi_matrix
    {k : Type u} [Field k] {ι : Type u} [Fintype ι] (d : ι → ℕ)
    (S : Type u) [AddCommGroup S]
    [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S]
    [Module k S] [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S]
    [Module.Finite k S]
    (hS : IsSimpleModule (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S) :
    Module.finrank k (Module.End (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S) = 1 := by
  classical
  haveI : Nontrivial S := IsSimpleModule.nontrivial (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S
  -- We use `R` to denote the product ring throughout the comments.
  -- f-independent component: identify the supporting matrix factor `j`.
  -- Commutativity / idempotence of the central idempotents `Pi.single i 1`.
  have hcomm : ∀ (i : ι) (r : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)),
      (Pi.single i 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) * r = r * Pi.single i 1 := by
    intro i r
    funext i'
    by_cases h : i' = i
    · subst h; simp
    · simp [h]
  have hidem : ∀ (i : ι),
      (Pi.single i 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) * Pi.single i 1
        = Pi.single i 1 := by
    intro i
    funext i'
    by_cases h : i' = i
    · subst h; simp
    · simp [h]
  -- The endomorphism `x ↦ (Pi.single i 1) • x`.
  let P : ι → (S →ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) k] S) := fun i =>
    { toFun := fun x => Pi.single i 1 • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        rw [← mul_smul, ← mul_smul, hcomm i r] }
  have hP : ∀ i (x : S),
      P i x = (Pi.single i 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) • x := by
    intro i x; simp only [P, LinearMap.coe_mk, AddHom.coe_mk]
  have hPbt : ∀ i, LinearMap.range (P i) = ⊥ ∨ LinearMap.range (P i) = ⊤ :=
    fun i => eq_bot_or_eq_top _
  -- Some factor acts by the identity.
  have hexj : ∃ j, LinearMap.range (P j) = ⊤ := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ i (x : S),
        (Pi.single i 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) • x = 0 := by
      intro i x
      have hr : LinearMap.range (P i) = ⊥ := (hPbt i).resolve_right (hcon i)
      have hx : P i x ∈ LinearMap.range (P i) := LinearMap.mem_range_self _ x
      rw [hr, Submodule.mem_bot] at hx
      rw [hP] at hx
      exact hx
    obtain ⟨x, hx0⟩ := exists_ne (0 : S)
    apply hx0
    have hone : (∑ i, (Pi.single i 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k))) = 1 := by
      have h := Finset.univ_sum_single (1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k))
      simpa using h
    calc x = (1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) • x := (one_smul _ x).symm
      _ = (∑ i, (Pi.single i 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k))) • x := by rw [hone]
      _ = ∑ i, (Pi.single i 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) • x := Finset.sum_smul
      _ = 0 := by simp [hall]
  obtain ⟨j, hjtop⟩ := hexj
  have hPj_surj : Function.Surjective (P j) := LinearMap.range_eq_top.mp hjtop
  have hej : ∀ x : S,
      (Pi.single j 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) • x = x := by
    intro x
    obtain ⟨y, hy⟩ := hPj_surj x
    have hy' : (Pi.single j 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) • y = x := by
      rw [← hP]; exact hy
    calc (Pi.single j 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) • x
        = (Pi.single j 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) •
            ((Pi.single j 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) • y) := by rw [hy']
      _ = ((Pi.single j 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) * Pi.single j 1) • y :=
          (mul_smul _ _ _).symm
      _ = (Pi.single j 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) • y := by rw [hidem j]
      _ = x := hy'
  -- Matrix unit computations inside the factor `j`.
  have hsm : ∀ (A B : Matrix (Fin (d j)) (Fin (d j)) k)
      (r : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)),
      (Pi.single j A : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) * r * Pi.single j B
        = Pi.single j (A * r j * B) := by
    intro A B r
    funext i'
    by_cases h : i' = j
    · subst h; simp
    · simp [h]
  have hss : ∀ (A B : Matrix (Fin (d j)) (Fin (d j)) k),
      (Pi.single j A : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) * Pi.single j B
        = Pi.single j (A * B) := by
    intro A B
    funext i'
    by_cases h : i' = j
    · subst h; simp
    · simp [h]
  have hsingle_sum : ∀ (M : Fin (d j) → Matrix (Fin (d j)) (Fin (d j)) k),
      (∑ a, (Pi.single j (M a) : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)))
        = Pi.single j (∑ a, M a) := by
    intro M
    funext i'
    by_cases h : i' = j
    · subst h; simp [Finset.sum_apply]
    · simp [h, Finset.sum_apply]
  -- The matrix units.
  obtain ⟨u, hu⟩ : ∃ u : Fin (d j) → Fin (d j) → (Π i, Matrix (Fin (d i)) (Fin (d i)) k),
      ∀ a b, u a b = Pi.single j (Matrix.single a b (1 : k)) := ⟨_, fun _ _ => rfl⟩
  have hmulu : ∀ (p q r : Fin (d j)), u p q * u q r = u p r := by
    intro p q r
    rw [hu, hu, hu, hss, Matrix.single_mul_single_same, mul_one]
  have hcompose : ∀ (p q r : Fin (d j)) (y : S), u p q • (u q r • y) = u p r • y := by
    intro p q r y
    rw [← mul_smul, hmulu]
  have hCORNER : ∀ (a : Fin (d j)) (r : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)),
      u a a * r * u a a = (r j a a) • u a a := by
    intro a r
    rw [hu, hsm, Matrix.single_mul_mul_single, one_mul, mul_one, ← Pi.single_smul,
      Matrix.smul_single, smul_eq_mul, mul_one]
  have hUsum : (∑ a : Fin (d j), u a a)
      = (Pi.single j 1 : (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) := by
    simp only [hu]
    rw [hsingle_sum, Matrix.sum_single_one]
  -- Line lemma: a nonzero vector fixed by `u a a` generates `u a a • S` over `k`.
  have hline : ∀ (a : Fin (d j)) (z w : S), z ≠ 0 → u a a • z = z → u a a • w = w →
      ∃ t : k, w = t • z := by
    intro a z w hz hzl hwl
    have htop : Submodule.span (Π i, Matrix (Fin (d i)) (Fin (d i)) k) {z} = ⊤ := by
      rcases eq_bot_or_eq_top
          (Submodule.span (Π i, Matrix (Fin (d i)) (Fin (d i)) k) {z}) with hb | ht
      · exfalso; apply hz
        have hmem : z ∈ Submodule.span (Π i, Matrix (Fin (d i)) (Fin (d i)) k) {z} :=
          Submodule.mem_span_singleton_self z
        rw [hb] at hmem; simpa using hmem
      · exact ht
    have hwmem : w ∈ Submodule.span (Π i, Matrix (Fin (d i)) (Fin (d i)) k) {z} := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hwmem
    refine ⟨(r j) a a, ?_⟩
    have hw2 : w = (u a a * r * u a a) • z := by
      rw [mul_smul, mul_smul, hzl, hr, hwl]
    have key2 : (u a a * r * u a a) • z = (r j a a) • z := by
      rw [hCORNER a r, smul_assoc, hzl]
    rw [hw2]; exact key2
  -- f-linearity over `k` (the action factors through the central `algebraMap`).
  have hfk : ∀ (f : Module.End (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S) (t : k) (x : S),
      f (t • x) = t • f x := by
    intro f t x
    have h1 : (t • x : S)
        = (algebraMap k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) t) • x :=
      (algebraMap_smul _ t x).symm
    have h2 : (t • f x : S)
        = (algebraMap k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) t) • f x :=
      (algebraMap_smul _ t (f x)).symm
    rw [h1, h2, map_smul]
  -- A nonzero generator for each line.
  obtain ⟨s, hs0⟩ := exists_ne (0 : S)
  have hsum_s : ∑ a, u a a • s = s := by
    rw [← Finset.sum_smul, hUsum, hej]
  have hexa : ∃ a, u a a • s ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hs0
    rw [← hsum_s]
    exact Finset.sum_eq_zero (fun a _ => hcon a)
  obtain ⟨a₀, ha₀⟩ := hexa
  have hgline : ∀ a, u a a • (u a a₀ • s) = u a a₀ • s := fun a => hcompose a a a₀ s
  have hgne : ∀ a, u a a₀ • s ≠ 0 := by
    intro a hcontra
    apply ha₀
    have hcollapse : u a₀ a • (u a a₀ • s) = u a₀ a₀ • s := hcompose a₀ a a₀ s
    rw [hcontra, smul_zero] at hcollapse
    exact hcollapse.symm
  -- The key claim: every `R`-endomorphism is a `k`-scalar.
  have key : ∀ f : Module.End (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S,
      ∃ c : k, ∀ x, f x = c • x := by
    intro f
    have hscal : ∀ a, ∃ c : k, f (u a a₀ • s) = c • (u a a₀ • s) := by
      intro a
      have hpres : u a a • (f (u a a₀ • s)) = f (u a a₀ • s) := by
        have h := map_smul f (u a a) (u a a₀ • s)
        rw [hgline a] at h
        exact h.symm
      exact hline a (u a a₀ • s) (f (u a a₀ • s)) (hgne a) (hgline a) hpres
    choose c hc using hscal
    have hfz0 : f (u a₀ a₀ • s) = c a₀ • (u a₀ a₀ • s) := hc a₀
    have hlinescal : ∀ a w, u a a • w = w → f w = c a • w := by
      intro a w hw
      obtain ⟨t, ht⟩ := hline a (u a a₀ • s) w (hgne a) (hgline a) hw
      rw [ht, hfk, hc a, smul_comm]
    have hceq : ∀ a, c a = c a₀ := by
      intro a
      have h2 : f (u a a₀ • s) = c a₀ • (u a a₀ • s) := by
        have hge : u a a₀ • s = u a a₀ • (u a₀ a₀ • s) :=
          (hcompose a a₀ a₀ s).symm
        rw [hge, map_smul, hfz0]
        exact (smul_comm (c a₀) (u a a₀) (u a₀ a₀ • s)).symm
      have h3 : c a • (u a a₀ • s) = c a₀ • (u a a₀ • s) := by rw [← hc a, h2]
      exact smul_left_injective k (hgne a) h3
    refine ⟨c a₀, ?_⟩
    intro x
    have hxsum : (∑ a, u a a • x) = x := by
      rw [← Finset.sum_smul, hUsum, hej]
    calc f x = f (∑ a, u a a • x) := by rw [hxsum]
      _ = ∑ a, f (u a a • x) := map_sum f _ _
      _ = ∑ a, c a₀ • (u a a • x) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hlinescal a (u a a • x) (hcompose a a a x), hceq a]
      _ = c a₀ • (∑ a, u a a • x) := by rw [Finset.smul_sum]
      _ = c a₀ • x := by rw [hxsum]
  -- Assemble: `algebraMap k (End R S)` is bijective.
  have hsurj : Function.Surjective
      (algebraMap k (Module.End (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S)) := by
    intro f
    obtain ⟨c, hc⟩ := key f
    refine ⟨c, ?_⟩
    ext x
    rw [Module.algebraMap_end_apply]
    exact (hc x).symm
  haveI : Nontrivial (Module.End (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S) := by
    obtain ⟨x, hx⟩ := exists_ne (0 : S)
    refine ⟨1, 0, fun h => hx ?_⟩
    have := LinearMap.congr_fun h x
    simpa using this
  have hinj : Function.Injective
      (algebraMap k (Module.End (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S)) :=
    RingHom.injective _
  have e : k ≃ₗ[k] Module.End (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S :=
    LinearEquiv.ofBijective
      (Algebra.linearMap k (Module.End (Π i, Matrix (Fin (d i)) (Fin (d i)) k) S))
      ⟨hinj, hsurj⟩
  rw [← e.finrank_eq]
  exact CommSemiring.finrank_self k

end Serre.SplitBaseChange
