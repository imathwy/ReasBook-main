import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap07.Exercise_7_7_2_4
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_5_2.SemisimpleEquivTransport

/-!
# Classification of the irreducible `S₃`-representations in characteristic `2` (support for 18.5.2)

Over an algebraically closed field `k` of characteristic `2`, the symmetric group `S₃` has exactly
two irreducible representations: the trivial one (degree `1`) and the natural/augmentation module
(degree `2`).  This is the modular-representation-theory heart of the characteristic-`2` branch of
Exercise 18.5.2.

The proof restricts to the cyclic subgroup `C₃ = ⟨(0 1 2)⟩` (order `3`, coprime to `2`, hence
semisimple on restriction): the `3`-cycle acts diagonalizably with eigenvalues among the cube roots
of unity `{1, ω, ω²}`, and the transposition `(0 1)` conjugates the `3`-cycle to its inverse, hence
swaps the `ω`- and `ω²`-eigenlines.  Irreducibility then forces either the trivial module
(`C₃` acts trivially) or the `2`-dimensional natural module.
-/

attribute [-instance] Field.henselian

noncomputable section
open Polynomial Module
namespace Representation
section
local notation "S3" => Equiv.Perm (Fin 3)
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V]

private def cc : S3 := finRotate 3
private def tt : S3 := Equiv.swap (0 : Fin 3) 1

private theorem words_univ (g : S3) :
    g ∈ ({1, cc, cc*cc, tt, cc*tt, cc*cc*tt} : Finset S3) := by
  have heq : ({1, cc, cc*cc, tt, cc*tt, cc*cc*tt} : Finset S3) = Finset.univ := by decide
  rw [heq]; exact Finset.mem_univ g

private theorem cc_tt : (cc : S3) * tt = tt * (cc * cc) := by decide
private theorem tt_tt : (tt : S3) * tt = 1 := by decide
private theorem cc3 : (cc : S3) * cc * cc = 1 := by decide

-- stability under cc and tt ⟹ stability under all g
omit [IsAlgClosed k] in
private theorem stab_all (σ : Representation k S3 V) (W : Submodule k V)
    (hc : ∀ x ∈ W, σ cc x ∈ W) (ht : ∀ x ∈ W, σ tt x ∈ W) :
    ∀ (g : S3), ∀ x ∈ W, σ g x ∈ W := by
  intro g x hx
  have hg := words_univ g
  fin_cases hg
  · simpa using hx
  · exact hc x hx
  · rw [map_mul, Module.End.mul_apply]; exact hc _ (hc x hx)
  · exact ht x hx
  · rw [map_mul, Module.End.mul_apply]; exact hc _ (ht x hx)
  · rw [map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply]
    exact hc _ (hc _ (ht x hx))

-- σ cc = 1 and σ tt = 1 ⟹ σ g = 1
omit [IsAlgClosed k] in
private theorem all_one (σ : Representation k S3 V) (hc : σ cc = 1) (ht : σ tt = 1) :
    ∀ g : S3, σ g = 1 := by
  intro g
  have hg := words_univ g
  fin_cases hg <;> simp [map_mul, map_one, hc, ht]

-- intertwining on cc and tt extends to all g
omit [IsAlgClosed k] in
private theorem intertwine_all {W : Type u} [AddCommGroup W] [Module k W]
    (σ : Representation k S3 V) (τ : Representation k S3 W) (e : V →ₗ[k] W)
    (hc : e ∘ₗ σ cc = τ cc ∘ₗ e) (ht : e ∘ₗ σ tt = τ tt ∘ₗ e) :
    ∀ g : S3, e ∘ₗ σ g = τ g ∘ₗ e := by
  have key : ∀ a b : S3, e ∘ₗ σ a = τ a ∘ₗ e → e ∘ₗ σ b = τ b ∘ₗ e →
      e ∘ₗ σ (a*b) = τ (a*b) ∘ₗ e := by
    intro a b ha hb
    rw [map_mul, map_mul]
    calc e ∘ₗ (σ a * σ b) = (e ∘ₗ σ a) ∘ₗ σ b := by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc]
      _ = (τ a ∘ₗ e) ∘ₗ σ b := by rw [ha]
      _ = τ a ∘ₗ (e ∘ₗ σ b) := by rw [LinearMap.comp_assoc]
      _ = τ a ∘ₗ (τ b ∘ₗ e) := by rw [hb]
      _ = (τ a * τ b) ∘ₗ e := by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  have h1 : e ∘ₗ σ (1:S3) = τ 1 ∘ₗ e := by rw [map_one, map_one]; ext x; simp
  intro g
  have hg := words_univ g
  fin_cases hg
  · exact h1
  · exact hc
  · exact key _ _ hc hc
  · exact ht
  · exact key _ _ hc ht
  · exact key _ _ (key _ _ hc hc) ht


omit [IsAlgClosed k] in
private theorem swap_eig {W' : Type u} [AddCommGroup W'] [Module k W']
    (ρ : Representation k S3 W') (μ : k) (v : W') (hv : ρ cc v = μ • v) :
    ρ cc (ρ tt v) = (μ*μ) • (ρ tt v) := by
  have hmap : ρ cc * ρ tt = ρ tt * (ρ cc * ρ cc) := by
    rw [← map_mul, ← map_mul, ← map_mul, cc_tt]
  have happ : ρ cc (ρ tt v) = ρ tt (ρ cc (ρ cc v)) := by
    have := congrArg (fun m : Module.End k W' => m v) hmap
    simpa [Module.End.mul_apply] using this
  rw [happ, hv, map_smul, hv, smul_smul, map_smul]

omit [IsAlgClosed k] in
private theorem rho_tt_ne_zero {W' : Type u} [AddCommGroup W'] [Module k W']
    (ρ : Representation k S3 W') (v : W') (hv0 : v ≠ 0) : ρ tt v ≠ 0 := by
  intro h
  apply hv0
  have key : ρ tt (ρ tt v) = v := by
    have := congrArg (fun m : Module.End k W' => m v)
      (show ρ tt * ρ tt = 1 by rw [← map_mul, tt_tt, map_one])
    simpa [Module.End.mul_apply] using this
  rw [h, map_zero] at key
  exact key.symm

omit [IsAlgClosed k] in
private theorem pair_indep {W' : Type u} [AddCommGroup W'] [Module k W']
    (Tl : Module.End k W') (v w : W') (μ ν : k) (hμν : μ ≠ ν)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hev : Tl v = μ • v) (hew : Tl w = ν • w) :
    LinearIndependent k ![v, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h2 : (s*μ) • v + (t*ν) • w = 0 := by
    have := congrArg Tl hst
    simpa [map_add, map_smul, hev, hew, smul_smul, map_zero] using this
  have h3 : (t*(ν - μ)) • w = 0 := by
    have e1 : ((s*μ) • v + (t*ν) • w) - μ • (s•v + t•w) = (t*(ν-μ)) • w := by module
    calc (t*(ν-μ)) • w = ((s*μ) • v + (t*ν) • w) - μ • (s•v + t•w) := e1.symm
      _ = 0 - μ • 0 := by rw [h2, hst]
      _ = 0 := by simp
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp (by
      rcases smul_eq_zero.mp h3 with h|h
      · exact h
      · exact absurd h hw0) with h|h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hμν
  refine ⟨?_, ht0⟩
  rw [ht0, zero_smul, add_zero] at hst
  rcases smul_eq_zero.mp hst with h|h
  · exact h
  · exact absurd h hv0


omit [IsAlgClosed k] in
private theorem case_one (h2 : (2 : k) = 0) (σ : Representation k S3 V) [σ.IsIrreducible]
    [FiniteDimensional k V] (hV1 : LinearMap.ker (σ cc - 1) ≠ ⊥) :
    Nonempty (σ.Equiv (Representation.trivial k S3 k)) := by
  -- helper: membership in ker(σ cc - 1) means fixed by σ cc
  have fixc : ∀ x, x ∈ LinearMap.ker (σ cc - 1) → σ cc x = x := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    exact hx
  -- Build subrep U1 = ker(σ cc - 1)
  have hc1 : ∀ x ∈ LinearMap.ker (σ cc - 1), σ cc x ∈ LinearMap.ker (σ cc - 1) := by
    intro x hx; rw [fixc x hx]; exact hx
  have ht1 : ∀ x ∈ LinearMap.ker (σ cc - 1), σ tt x ∈ LinearMap.ker (σ cc - 1) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have hmap : σ cc * σ tt = σ tt * (σ cc * σ cc) := by
      rw [← map_mul, ← map_mul, ← map_mul, cc_tt]
    have happ : σ cc (σ tt x) = σ tt (σ cc (σ cc x)) := by
      have := congrArg (fun m : Module.End k V => m x) hmap
      simpa [Module.End.mul_apply] using this
    rw [happ, fixc x hx, fixc x hx]
  let U1 : Subrepresentation σ :=
    { toSubmodule := LinearMap.ker (σ cc - 1)
      apply_mem_toSubmodule := fun g x hx => stab_all σ _ hc1 ht1 g x hx }
  have hU1ne : U1 ≠ ⊥ := fun h => hV1 (congrArg Subrepresentation.toSubmodule h)
  have hU1top : U1 = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U1).resolve_left hU1ne
  have hkertop : LinearMap.ker (σ cc - 1) = ⊤ := congrArg Subrepresentation.toSubmodule hU1top
  have hccone : σ cc = 1 := sub_eq_zero.mp (LinearMap.ker_eq_top.mp hkertop)
  -- Now nilpotent argument for σ tt
  have htt2 : σ tt * σ tt = 1 := by rw [← map_mul, tt_tt, map_one]
  have hnil : (σ tt - 1)^2 = 0 := by
    have expand : (σ tt - 1)^2 = σ tt * σ tt - (σ tt + σ tt) + 1 := by noncomm_ring
    rw [expand, htt2]
    have ha : σ tt + σ tt = 0 := by rw [← two_smul k (σ tt), h2, zero_smul]
    have hb : (1 : Module.End k V) + 1 = 0 := by rw [← two_smul k (1:Module.End k V), h2, zero_smul]
    rw [ha, sub_zero]; exact hb
  -- Nontrivial V
  haveI hNT : Nontrivial V := by
    rcases subsingleton_or_nontrivial V with hs | hn
    · exfalso
      have : (⊥ : Subrepresentation σ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        exact Subsingleton.elim _ _
      exact bot_ne_top this
    · exact hn
  have hker_t : LinearMap.ker (σ tt - 1) ≠ ⊥ := by
    intro hbot
    have hinj := LinearMap.ker_eq_bot.mp hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hz : (((σ tt - 1 : Module.End k V))^2) x = 0 := by rw [hnil]; simp
    rw [sq, Module.End.mul_apply] at hz
    have h1 : (σ tt - 1) x = 0 := hinj (by rw [hz, map_zero])
    exact hx (hinj (by rw [h1, map_zero]))
  -- Build subrep U2 = ker(σ tt - 1)
  have fixt : ∀ x, x ∈ LinearMap.ker (σ tt - 1) → σ tt x = x := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    exact hx
  have hc2 : ∀ x ∈ LinearMap.ker (σ tt - 1), σ cc x ∈ LinearMap.ker (σ tt - 1) := by
    intro x hx; rw [hccone, Module.End.one_apply]; exact hx
  have ht2 : ∀ x ∈ LinearMap.ker (σ tt - 1), σ tt x ∈ LinearMap.ker (σ tt - 1) := by
    intro x hx; rw [fixt x hx]; exact hx
  let U2 : Subrepresentation σ :=
    { toSubmodule := LinearMap.ker (σ tt - 1)
      apply_mem_toSubmodule := fun g x hx => stab_all σ _ hc2 ht2 g x hx }
  have hU2ne : U2 ≠ ⊥ := fun h => hker_t (congrArg Subrepresentation.toSubmodule h)
  have hU2top : U2 = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U2).resolve_left hU2ne
  have hkertop2 : LinearMap.ker (σ tt - 1) = ⊤ := congrArg Subrepresentation.toSubmodule hU2top
  have httone : σ tt = 1 := sub_eq_zero.mp (LinearMap.ker_eq_top.mp hkertop2)
  have hall : ∀ g : S3, σ g = 1 := all_one σ hccone httone
  -- Build the equivalence with the trivial representation
  obtain ⟨v, hv0⟩ := exists_ne (0 : V)
  have hc3 : ∀ x ∈ Submodule.span k {v}, σ cc x ∈ Submodule.span k {v} := by
    intro x hx; rw [hccone, Module.End.one_apply]; exact hx
  have ht3 : ∀ x ∈ Submodule.span k {v}, σ tt x ∈ Submodule.span k {v} := by
    intro x hx; rw [httone, Module.End.one_apply]; exact hx
  let U3 : Subrepresentation σ :=
    { toSubmodule := Submodule.span k {v}
      apply_mem_toSubmodule := fun g x hx => stab_all σ _ hc3 ht3 g x hx }
  have hU3ne : U3 ≠ ⊥ := by
    intro h
    have hs : Submodule.span k {v} = ⊥ := congrArg Subrepresentation.toSubmodule h
    rw [Submodule.span_singleton_eq_bot] at hs
    exact hv0 hs
  have hU3top : U3 = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U3).resolve_left hU3ne
  have hspan : Submodule.span k {v} = ⊤ := congrArg Subrepresentation.toSubmodule hU3top
  let e0 : k ≃ₗ[k] V := (LinearEquiv.toSpanNonzeroSingleton k V v hv0).trans
    ((LinearEquiv.ofEq _ _ hspan).trans (Submodule.topEquiv))
  refine ⟨Representation.Equiv.mk e0.symm (fun g => ?_)⟩
  ext x
  simp [hall g, Module.End.one_apply, LinearMap.comp_apply, Representation.trivial]


omit [AddCommGroup V] [Module k V] in
private theorem exists_omega (h2 : (2:k) = 0) :
    ∃ ω : k, ω^2 + ω + 1 = 0 ∧ ω ≠ 1 ∧ ω^3 = 1 ∧ ω ≠ 0 ∧ ω*ω ≠ ω := by
  have h3 : (3 : k) ≠ 0 := by
    have h31 : (3:k) = 1 := by
      have : (3:k) = 2 + 1 := by norm_num
      rw [this, h2]; ring
    rw [h31]; exact one_ne_zero
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (k := k) (X^2 + X + 1) (by
    have : (X^2 + X + 1 : k[X]).degree = 2 := by compute_degree!
    rw [this]; decide)
  rw [Polynomial.IsRoot.def] at hω
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at hω
  have hne1 : ω ≠ 1 := by
    intro h; rw [h] at hω; norm_num at hω; exact h3 (by linear_combination hω)
  have hcube : ω^3 = 1 := by
    have hfac : (ω - 1) * (ω^2 + ω + 1) = ω^3 - 1 := by ring
    rw [hω, mul_zero] at hfac
    linear_combination -hfac
  have hne0 : ω ≠ 0 := by
    intro h; rw [h] at hω; norm_num at hω
  have hsq : ω * ω ≠ ω := by
    intro h
    apply hne1
    have hz : ω * (ω - 1) = 0 := by ring_nf; linear_combination h
    rcases mul_eq_zero.mp hz with h0 | h1
    · exact absurd h0 hne0
    · linear_combination h1
  exact ⟨ω, hω, hne1, hcube, hne0, hsq⟩


private def wfull (ω : k) : Fin 3 →₀ k :=
  Finsupp.single 0 1 + Finsupp.single 1 (ω^2) + Finsupp.single 2 ω

omit [IsAlgClosed k] in
private theorem ofMulAction_wfull (ω : k) (hcube : ω^3 = 1) :
    ofMulAction k S3 (Fin 3) cc (wfull ω) = ω • wfull ω := by
  conv_lhs => rw [wfull]
  simp only [map_add, ofMulAction_single]
  rw [show cc • (0:Fin 3) = 1 from by decide, show cc • (1:Fin 3) = 2 from by decide,
      show cc • (2:Fin 3) = 0 from by decide]
  rw [wfull, smul_add, smul_add, Finsupp.smul_single, Finsupp.smul_single, Finsupp.smul_single]
  simp only [smul_eq_mul, mul_one]
  rw [show ω * ω^2 = 1 from by rw [show ω*ω^2 = ω^3 from by ring, hcube],
      show ω * ω = ω^2 from by ring]
  abel

omit [IsAlgClosed k] in
private theorem wfull_mem (ω : k) (hquad : ω^2 + ω + 1 = 0) :
    wfull ω ∈ (permutationAugmentationSubrepresentation k S3 (Fin 3)).toSubmodule := by
  show permutationAugmentationLinearMap k (Fin 3) (wfull ω) = 0
  rw [wfull]
  simp only [permutationAugmentationLinearMap, map_add, Finsupp.lsum_single, LinearMap.id_coe, id_eq]
  linear_combination hquad

omit [IsAlgClosed k] in
private theorem tau_val (g : S3)
    (x : (permutationAugmentationSubrepresentation k S3 (Fin 3)).toSubmodule) :
    ((permutationAugmentationRepresentation k S3 (Fin 3) g x : Fin 3 →₀ k))
      = ofMulAction k S3 (Fin 3) g (x : Fin 3 →₀ k) := rfl

omit [IsAlgClosed k] in
private theorem carrier_finrank :
    finrank k ((permutationAugmentationSubrepresentation k S3 (Fin 3)).toSubmodule) = 2 := by
  have hsurj : Function.Surjective (permutationAugmentationLinearMap k (Fin 3)) := by
    intro z
    refine ⟨Finsupp.single 0 z, ?_⟩
    simp only [permutationAugmentationLinearMap, Finsupp.lsum_single, LinearMap.id_coe, id_eq]
  have hrange : LinearMap.range (permutationAugmentationLinearMap k (Fin 3)) = ⊤ :=
    LinearMap.range_eq_top.2 hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker (permutationAugmentationLinearMap k (Fin 3))
  rw [hrange] at hrn
  have h3 : finrank k (Fin 3 →₀ k) = 3 := by rw [Module.finrank_finsupp_self]; rfl
  rw [h3] at hrn
  have htop : finrank k (⊤ : Submodule k k) = 1 := by rw [finrank_top]; exact finrank_self k
  rw [htop] at hrn
  show finrank k (LinearMap.ker (permutationAugmentationLinearMap k (Fin 3))) = 2
  omega

private theorem case_two (h2 : (2 : k) = 0) (σ : Representation k S3 V) [σ.IsIrreducible]
    [FiniteDimensional k V] (hV1 : LinearMap.ker (σ cc - 1) = ⊥) :
    Nonempty (σ.Equiv (permutationAugmentationRepresentation k S3 (Fin 3))) := by
  haveI hNT : Nontrivial V := by
    rcases subsingleton_or_nontrivial V with hs | hn
    · exfalso
      have : (⊥ : Subrepresentation σ) = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        exact Subsingleton.elim _ _
      exact bot_ne_top this
    · exact hn
  obtain ⟨ω, hquad, hne1, hcube, hne0, hsqne⟩ := exists_omega (k := k) h2
  -- T^3 = 1 and the quadratic operator relation
  have hT3 : (σ cc)^3 = 1 := by
    rw [← map_pow, show (cc:S3)^3 = 1 from by decide, map_one]
  have hquadop : (1 : Module.End k V) + σ cc + (σ cc)^2 = 0 := by
    have hmulfac : (σ cc - 1) * (1 + σ cc + (σ cc)^2) = (σ cc)^3 - 1 := by noncomm_ring
    rw [hT3, sub_self] at hmulfac
    ext x
    have hx : ((1 : Module.End k V) + σ cc + (σ cc)^2) x ∈ LinearMap.ker (σ cc - 1) := by
      rw [LinearMap.mem_ker]
      have := congrArg (fun m : Module.End k V => m x) hmulfac
      simpa [Module.End.mul_apply] using this
    rw [hV1, Submodule.mem_bot] at hx
    simpa using hx
  -- scalar facts
  have hsum : ω^2 + ω = 1 := by linear_combination hquad - h2
  -- the factorization pointwise: (σcc - ω)(σcc - ω²) = 0
  have hfac : ∀ x : V, (σ cc - ω • 1) ((σ cc - ω^2 • 1) x) = 0 := by
    intro x
    have hxq : ((1 : Module.End k V) + σ cc + (σ cc)^2) x = 0 := by rw [hquadop]; simp
    have hxq' : σ cc (σ cc x) + σ cc x + x = 0 := by
      simpa [Module.End.pow_apply, add_comm, add_left_comm, add_assoc] using hxq
    have lhs_eq : (σ cc - ω • 1) ((σ cc - ω^2 • 1) x)
        = σ cc (σ cc x) - (ω^2 + ω) • σ cc x + (ω * ω^2) • x := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
      module
    rw [lhs_eq, hsum, show ω * ω^2 = 1 from by rw [show ω*ω^2 = ω^3 from by ring, hcube]]
    -- goal: σ cc (σ cc x) - 1 • σ cc x + 1 • x = 0
    rw [one_smul, one_smul]
    -- char two: subtraction = addition
    have hbb : σ cc x + σ cc x = 0 := by rw [← two_smul k (σ cc x), h2, zero_smul]
    calc σ cc (σ cc x) - σ cc x + x
        = (σ cc (σ cc x) + σ cc x + x) - (σ cc x + σ cc x) := by abel
      _ = 0 - 0 := by rw [hxq', hbb]
      _ = 0 := by simp
  -- obtain a nonzero ω-eigenvector
  obtain ⟨v, hv0, hveig⟩ : ∃ v : V, v ≠ 0 ∧ σ cc v = ω • v := by
    obtain ⟨u, hu0⟩ := exists_ne (0:V)
    by_cases hpz : (σ cc - ω^2 • 1) u = 0
    · refine ⟨σ tt u, rho_tt_ne_zero σ u hu0, ?_⟩
      have hu_eig : σ cc u = ω^2 • u := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hpz
        exact hpz
      have hsw := swap_eig σ (ω^2) u hu_eig
      rwa [show ω^2 * ω^2 = ω from by rw [show ω^2*ω^2 = ω^3*ω from by ring, hcube, one_mul]] at hsw
    · refine ⟨(σ cc - ω^2 • 1) u, hpz, ?_⟩
      have := hfac u
      rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  -- w := σ tt v
  set w := σ tt v with hwdef
  have hw_eig : σ cc w = (ω*ω) • w := swap_eig σ ω v hveig
  have hw0 : w ≠ 0 := rho_tt_ne_zero σ v hv0
  have hsw : σ tt w = v := by
    have h := congrArg (fun m : Module.End k V => m v)
      (show σ tt * σ tt = 1 by rw [← map_mul, tt_tt, map_one])
    simpa [Module.End.mul_apply] using h
  -- linear independence
  have hLI : LinearIndependent k ![v, w] :=
    pair_indep (σ cc) v w ω (ω*ω) (Ne.symm hsqne) hv0 hw0 hveig hw_eig
  -- span {v, w} = ⊤
  have hc : ∀ x ∈ Submodule.span k ({v, w} : Set V), σ cc x ∈ Submodule.span k ({v,w}:Set V) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · rw [hveig]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
        · rw [hw_eig]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  have ht : ∀ x ∈ Submodule.span k ({v, w} : Set V), σ tt x ∈ Submodule.span k ({v,w}:Set V) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · rw [← hwdef]; exact Submodule.subset_span (by simp)
        · rw [hsw]; exact Submodule.subset_span (by simp)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  let Uv : Subrepresentation σ :=
    { toSubmodule := Submodule.span k ({v, w} : Set V)
      apply_mem_toSubmodule := fun g x hx => stab_all σ _ hc ht g x hx }
  have hUvne : Uv ≠ ⊥ := by
    intro h
    have hs : Submodule.span k ({v,w}:Set V) = ⊥ := congrArg Subrepresentation.toSubmodule h
    have : v ∈ (⊥ : Submodule k V) := by rw [← hs]; exact Submodule.subset_span (by simp)
    rw [Submodule.mem_bot] at this; exact hv0 this
  have hUvtop : Uv = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top Uv).resolve_left hUvne
  have hspan : Submodule.span k ({v,w}:Set V) = ⊤ := congrArg Subrepresentation.toSubmodule hUvtop
  have hrange : (Set.range ![v, w]) = {v, w} := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hspan2 : Submodule.span k (Set.range ![v, w]) = ⊤ := by rw [hrange]; exact hspan
  let bV : Basis (Fin 2) k V := Basis.mk hLI hspan2.ge
  have hbV0 : bV 0 = v := by simp [bV, Basis.mk_apply]
  have hbV1 : bV 1 = w := by simp [bV, Basis.mk_apply]
  -- τ side
  have hwmem : wfull ω ∈ (permutationAugmentationSubrepresentation k S3 (Fin 3)).toSubmodule :=
    wfull_mem ω hquad
  set wv : (permutationAugmentationSubrepresentation k S3 (Fin 3)).toSubmodule :=
    ⟨wfull ω, hwmem⟩ with hwvdef
  have hwv_eig : permutationAugmentationRepresentation k S3 (Fin 3) cc wv = ω • wv := by
    apply Subtype.ext
    rw [tau_val cc wv, Submodule.coe_smul]
    exact ofMulAction_wfull ω hcube
  set wv' := permutationAugmentationRepresentation k S3 (Fin 3) tt wv with hwv'def
  have hwv'_eig : permutationAugmentationRepresentation k S3 (Fin 3) cc wv' = (ω*ω) • wv' :=
    swap_eig (permutationAugmentationRepresentation k S3 (Fin 3)) ω wv hwv_eig
  have hwv0 : wv ≠ 0 := by
    intro h
    have hval : wfull ω = 0 := by
      have := congrArg (Subtype.val) h; simpa [hwvdef] using this
    have hc0 : (wfull ω) 0 = 1 := by simp [wfull]
    rw [hval] at hc0; simp at hc0
  have hwv'0 : wv' ≠ 0 :=
    rho_tt_ne_zero (permutationAugmentationRepresentation k S3 (Fin 3)) wv hwv0
  have hsw' : permutationAugmentationRepresentation k S3 (Fin 3) tt wv' = wv := by
    have h := congrArg (fun m : Module.End k _ => m wv)
      (show permutationAugmentationRepresentation k S3 (Fin 3) tt
            * permutationAugmentationRepresentation k S3 (Fin 3) tt = 1 by
        rw [← map_mul, tt_tt, map_one])
    simpa [Module.End.mul_apply, hwv'def] using h
  have hτLI : LinearIndependent k ![wv, wv'] :=
    pair_indep (permutationAugmentationRepresentation k S3 (Fin 3) cc) wv wv' ω (ω*ω)
      (Ne.symm hsqne) hwv0 hwv'0 hwv_eig hwv'_eig
  have hcard : Fintype.card (Fin 2)
      = finrank k ((permutationAugmentationSubrepresentation k S3 (Fin 3)).toSubmodule) := by
    rw [carrier_finrank]; rfl
  let bτ : Basis (Fin 2) k ((permutationAugmentationSubrepresentation k S3 (Fin 3)).toSubmodule) :=
    basisOfLinearIndependentOfCardEqFinrank hτLI hcard
  have hbτ0 : bτ 0 = wv := by
    simp only [bτ, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero]
  have hbτ1 : bτ 1 = wv' := by
    simp only [bτ, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_one,
      Matrix.cons_val_zero]
  let e : V ≃ₗ[k] _ := bV.equiv bτ (_root_.Equiv.refl (Fin 2))
  have heq : ∀ i, e (bV i) = bτ i := by
    intro i
    show (bV.equiv bτ (_root_.Equiv.refl (Fin 2))) (bV i) = bτ i
    rw [Basis.equiv_apply]; rfl
  -- eigen / swap facts expressed through the basis vectors
  have hcc0 : σ cc (bV 0) = ω • bV 0 := by rw [hbV0]; exact hveig
  have hcc1 : σ cc (bV 1) = (ω*ω) • bV 1 := by rw [hbV1]; exact hw_eig
  have htt0 : σ tt (bV 0) = bV 1 := by rw [hbV0, hbV1, hwdef]
  have htt1 : σ tt (bV 1) = bV 0 := by rw [hbV0, hbV1]; exact hsw
  refine ⟨Representation.Equiv.mk e
    (intertwine_all σ (permutationAugmentationRepresentation k S3 (Fin 3)) e.toLinearMap ?_ ?_)⟩
  · refine Basis.ext bV (fun i => ?_)
    fin_cases i
    · show e (σ cc (bV 0)) = permutationAugmentationRepresentation k S3 (Fin 3) cc (e (bV 0))
      simp only [hcc0, map_smul, heq, hbτ0, hwv_eig]
    · show e (σ cc (bV 1)) = permutationAugmentationRepresentation k S3 (Fin 3) cc (e (bV 1))
      simp only [hcc1, map_smul, heq, hbτ1, hwv'_eig]
  · refine Basis.ext bV (fun i => ?_)
    fin_cases i
    · show e (σ tt (bV 0)) = permutationAugmentationRepresentation k S3 (Fin 3) tt (e (bV 0))
      simp only [htt0, heq, hbτ0, hbτ1, hwv'def]
    · show e (σ tt (bV 1)) = permutationAugmentationRepresentation k S3 (Fin 3) tt (e (bV 1))
      simp only [htt1, heq, hbτ0, hbτ1, hsw']

/-- **Classification of irreducible `S₃`-representations in characteristic `2`.**  Over an
algebraically closed field of characteristic `2`, every irreducible `S₃`-representation is
equivalent to either the trivial representation or the natural (augmentation) `2`-dimensional
module. -/
theorem s3_char_two_irreducible_dichotomy
    (h2 : (2 : k) = 0) (σ : Representation k S3 V) [σ.IsIrreducible] :
    Nonempty (σ.Equiv (Representation.trivial k S3 k)) ∨
      Nonempty (σ.Equiv (permutationAugmentationRepresentation k S3 (Fin 3))) := by
  haveI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite σ
  by_cases hV1 : LinearMap.ker (σ cc - 1) = ⊥
  · exact Or.inr (case_two h2 σ hV1)
  · exact Or.inl (case_one h2 σ hV1)

end
end Representation
