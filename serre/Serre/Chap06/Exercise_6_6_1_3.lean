import Mathlib.Algebra.CharP.Defs
import Mathlib.RepresentationTheory.Maschke

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra

universe u v

section

variable {k : Type u} {G : Type v} {p : ℕ}
variable [Field k] [CharP k p] [Group G] [Finite G]

/-
Domain-style sampling for this item:
* `MonoidAlgebra.Submodule.instIsSemisimpleRing` in mathlib is the owner-level Maschke instance on
  `k[G]`, with primitive input `[NeZero (Nat.card G : k)]`.
* `NeZero.of_not_dvd` in `Mathlib.Algebra.CharP.Defs` is the canonical bridge from `CharP k p` and
  `¬ p ∣ Nat.card G` to that primitive owner input.
* `Serre.Chap06.Proposition_6_6_1_1` already treats the characteristic-zero case as a direct
  recall of the same owner instance.
* `Serre.Chap06.Corollary_6_6_1_2` reuses the same owner style for the Wedderburn-Artin
  consequence.

This exercise therefore stays at the `source-facing` layer as the divisibility criterion, while
reusing the Maschke owner `IsSemisimpleRing k[G]` rather than introducing any parallel wrapper.
-/

-- Proof sketch:
-- For the forward implication, if `p ∣ Nat.card G`, the augmentation ideal in `k[G]` is not a
-- direct summand of the regular module, so `k[G]` cannot be semisimple. For the reverse
-- implication, `¬ p ∣ Nat.card G` gives `[NeZero (Nat.card G : k)]` via `NeZero.of_not_dvd`,
-- and Maschke's theorem yields `IsSemisimpleRing k[G]`.
/-- Source-facing Maschke bridge: if the characteristic of `k` does not divide `|G|`, then the
canonical Maschke owner instance makes `k[G]` semisimple. -/
theorem group_algebra_isSemisimpleRing_of_char_not_dvd_group_order
    (h : ¬ p ∣ Nat.card G) : IsSemisimpleRing k[G] := by
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k h
  infer_instance

/-- Source-facing converse to Maschke's criterion: semisimplicity of `k[G]` forces the
characteristic of `k` not to divide `|G|`. -/
theorem char_not_dvd_group_order_of_group_algebra_isSemisimpleRing
    (h : IsSemisimpleRing k[G]) : ¬ p ∣ Nat.card G := by
  let _ : IsSemisimpleRing k[G] := h
  letI : Fintype G := Fintype.ofFinite G
  intro hdiv
  let ε : k[G] →ₐ[k] k := MonoidAlgebra.lift k k G (1 : G →* k)
  let I : Ideal k[G] := RingHom.ker ε.toRingHom
  let Ω : k[G] := Finset.univ.sum fun s : G => MonoidAlgebra.single s (1 : k)
  obtain ⟨J, hIJ⟩ : ∃ J : Submodule k[G] k[G], IsCompl I J := exists_isCompl I
  -- The formal group sum has coefficient `1` at every group element.
  have hOmegaEq : ((Ω : k[G]) : G → k) = fun _ : G => (1 : k) := by
    classical
    have happly :
        (((Finset.univ.sum fun s : G => MonoidAlgebra.single s (1 : k)) : k[G]) : G → k) =
          ∑ i : G, Pi.single i (1 : k) := by
      calc
        (((Finset.univ.sum fun s : G => MonoidAlgebra.single s (1 : k)) : k[G]) : G → k)
            = ∑ i : G, ⇑(MonoidAlgebra.single i (1 : k)) := Finsupp.coe_finset_sum _ _
        _ = ∑ i : G, Pi.single i (1 : k) := by
          simp_rw [Finsupp.single_eq_pi_single]
    simpa [Ω] using happly.trans (Finset.univ_sum_single (fun _ : G => (1 : k)))
  -- Any complement of the augmentation ideal is fixed by left translation.
  have hleft : ∀ ⦃x : k[G]⦄, x ∈ J → ∀ g : G, MonoidAlgebra.single g (1 : k) * x = x := by
    intro x hx g
    have hyJ : MonoidAlgebra.single g (1 : k) * x - x ∈ J := by
      refine J.sub_mem ?_ hx
      simpa using J.smul_mem (MonoidAlgebra.single g (1 : k)) hx
    have hyI : MonoidAlgebra.single g (1 : k) * x - x ∈ I := by
      rw [RingHom.mem_ker]
      simp [ε]
    have hyBot : MonoidAlgebra.single g (1 : k) * x - x ∈ (⊥ : Submodule k[G] k[G]) := by
      rw [← hIJ.disjoint.eq_bot, Submodule.mem_inf]
      exact ⟨hyI, hyJ⟩
    exact sub_eq_zero.mp ((Submodule.mem_bot (k[G])).1 hyBot)
  -- A left-invariant vector in the regular module is a scalar multiple of `Ω`.
  have hscalar : ∀ ⦃x : k[G]⦄, x ∈ J → x = x 1 • Ω := by
    intro x hx
    ext g
    have hcoeff := congrArg (fun y : k[G] => y g) (hleft hx g)
    have hconst : x g = x 1 := by
      simpa [MonoidAlgebra.single_mul_apply] using hcoeff.symm
    have hOmegaCoeff : Ω g = 1 := by
      simpa using congrFun hOmegaEq g
    simp [hconst, hOmegaCoeff]
  -- In characteristic `p`, divisibility `p ∣ |G|` puts the formal group sum in the kernel.
  have hOmegaI : Ω ∈ I := by
    rw [RingHom.mem_ker]
    have hcardzero : (Nat.card G : k) = 0 := by
      simpa using (CharP.cast_eq_zero_iff (R := k) p (Nat.card G)).2 hdiv
    calc
      ε Ω = Finset.univ.sum fun s : G => ε (MonoidAlgebra.single s (1 : k)) := by
        simp [Ω]
      _ = Finset.univ.sum fun _ : G => (1 : k) := by
        simp [ε]
      _ = (Fintype.card G : k) := by
        simp
      _ = (Nat.card G : k) := by
        simp [Nat.card_eq_fintype_card]
      _ = 0 := hcardzero
  -- Therefore the complement is contained in the augmentation ideal, forcing it to be trivial.
  have hJI : J ≤ I := by
    intro x hx
    have hxEq : x = (algebraMap k k[G] (x 1)) * Ω := by
      calc
        x = x 1 • Ω := hscalar hx
        _ = (algebraMap k k[G] (x 1)) * Ω := Algebra.smul_def _ _
    rw [hxEq]
    exact I.mul_mem_left _ hOmegaI
  have hJbot : J = ⊥ := by
    apply bot_unique
    intro x hx
    have hxBot : x ∈ (I ⊓ J : Submodule k[G] k[G]) := ⟨hJI hx, hx⟩
    rw [hIJ.disjoint.eq_bot] at hxBot
    simpa using hxBot
  -- But then codisjointness would force the augmentation ideal to be all of `k[G]`,
  -- contradicting that `1` has augmentation `1`.
  have hItop : I = ⊤ := by
    simpa [hJbot] using hIJ.codisjoint.eq_top
  have hOneNotMem : (1 : k[G]) ∉ I := by
    rw [RingHom.mem_ker]
    simp [ε]
  have hOneMem : (1 : k[G]) ∈ I := by
    simp [hItop]
  exact hOneNotMem hOneMem

/-- Exercise 6-6.1-3: for a field `k` of characteristic `p` and a finite group `G`, the
group algebra `k[G]` is semisimple if and only if `p` does not divide the order of `G`.

Layer triage:
* source-facing: the divisibility criterion `¬ p ∣ Nat.card G`
* core/canonical: the owner `IsSemisimpleRing k[G]`
* bridge/view: `NeZero.of_not_dvd` converts `¬ p ∣ Nat.card G` into the primitive Maschke input
  `[NeZero (Nat.card G : k)]`. -/
theorem group_algebra_isSemisimpleRing_iff_char_not_dvd_group_order :
    IsSemisimpleRing k[G] ↔ ¬ p ∣ Nat.card G := by
  constructor
  · exact char_not_dvd_group_order_of_group_algebra_isSemisimpleRing
  · exact group_algebra_isSemisimpleRing_of_char_not_dvd_group_order

end
