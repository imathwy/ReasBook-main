import Mathlib

universe u v

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R] [Fintype G]

local notation "RFix" => FixedPoints.subring R G

/-- Lemma 15.111.3: if `x` lies in the extension of an ideal `J` of the fixed subring `R^G`, then
every nonleading coefficient of `∏ σ : G, (T - σ(x))` belongs to `J`. -/
-- Proof sketch: induct on an expression of `x` as a finite sum of elements of the extended ideal
-- `JR`. Replacing `x` by `y - f b` changes the orbit polynomial by a sum of terms divisible by
-- powers of `f ∈ J`, and the symmetric coefficient expressions remain fixed by the action, hence
-- define elements of the fixed subring lying in `J`.
theorem coeff_charpoly_mem_fixed_ideal_of_mem_ideal_map
    (J : Ideal RFix) {x : R}
    (hx : x ∈ Ideal.map (FixedPoints.subring R G).subtype J)
    (i : Fin (Fintype.card G)) :
    ⟨(MulSemiringAction.charpoly G x).coeff i,
      fun g ↦ MulSemiringAction.smul_coeff_charpoly x i g⟩ ∈ J := sorry

end
