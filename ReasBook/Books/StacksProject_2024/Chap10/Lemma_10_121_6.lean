import StacksProject_2024.Chap10.Definition_10_121_5
import StacksProject_2024.Chap10.Lemma_10_121_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Ring.KrullDimLE 1 R]
variable [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

namespace Submodule

variable (M M' : Submodule R V)

/-- Helper for Lemma 10.121.6: under the ambient `KrullDim ≤ 1` hypothesis, a non-field local
domain has Krull dimension exactly `1`. -/
lemma ringKrullDim_eq_one_of_not_isField (hR : ¬ IsField R) :
    ringKrullDim R = 1 := by
  -- The ambient typeclass gives the upper bound `dim R ≤ 1`.
  have hle : ringKrullDim R ≤ 1 :=
    Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 R)
  -- Dimension `0` would force `R` to be a field, contradicting the hypothesis.
  have hnotle_zero : ¬ ringKrullDim R ≤ 0 := by
    intro hzero
    let _ : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr hzero
    exact hR Ring.KrullDimLE.isField_of_isDomain
  have hge : 1 ≤ ringKrullDim R :=
    Order.succ_le_of_lt (lt_of_not_ge hnotle_zero)
  exact le_antisymm hle hge

/-- Helper for Lemma 10.121.6: if the base ring is already a field, then any lattice is the whole
ambient vector space. -/
lemma eq_top_of_isField_of_isLattice [IsLattice K M] (hfield : IsField R) :
    M = ⊤ := by
  classical
  -- Surjectivity of `R → K` lets us rewrite every finite `K`-linear combination with
  -- coefficients coming from `R`, so the `K`-span condition forces `M = ⊤`.
  have hsurj : Function.Surjective (algebraMap R K) :=
    (IsFractionRing.surjective_iff_isField (R := R) (K := K)).mpr hfield
  have hspan : Submodule.span K (M : Set V) = ⊤ :=
    Submodule.IsLattice.span_eq_top (A := K) (M := M)
  apply eq_top_iff.mpr
  intro x hx
  have hxspan : x ∈ Submodule.span K (M : Set V) := by
    simpa [hspan] using hx
  obtain ⟨T, hTM, hxT⟩ := Submodule.mem_span_finite_of_mem_span hxspan
  rw [Submodule.mem_span_finset] at hxT
  obtain ⟨f, hf, hsum⟩ := hxT
  rw [← hsum]
  refine Submodule.sum_mem M fun a ha ↦ ?_
  have haM : a ∈ M := hTM ha
  obtain ⟨r, hr⟩ := hsurj (f a)
  rw [← hr]
  simpa using Submodule.smul_mem M r haM

/-- Helper for Lemma 10.121.6: in the field case, every lattice distance is zero because both
lattices are equal to `⊤`. -/
lemma latticeDistance_eq_zero_of_isField [IsLattice K M] [IsLattice K M'] (hfield : IsField R) :
    latticeDistance M M' = 0 := by
  -- Collapse both lattices to `⊤` and then simplify the defining quotient lengths.
  rw [eq_top_of_isField_of_isLattice (M := M) hfield, eq_top_of_isField_of_isLattice (M := M') hfield]
  rw [Submodule.latticeDistance_def]
  simp

-- Proof sketch: unfold `latticeDistance`; both quotient-length terms are identical when the two
-- lattices agree, so the integer difference is zero.
/-- The distance from a lattice to itself is zero. -/
theorem latticeDistance_self [IsLattice K M] :
    latticeDistance M M = 0 := by
  -- Unfold the distance and simplify the quotient by the full submodule.
  rw [Submodule.latticeDistance_def]
  simp

variable (M'' : Submodule R V)

-- Proof sketch: choose a lattice contained in all three lattices, rewrite each distance as the
-- difference of two finite lengths relative to that common sublattice, and use additivity of
-- module length in short exact sequences to telescope the resulting expression.
/-- Lemma 10.121.6: for lattices `M`, `M'`, and `M''` in a finite-dimensional `K`-vector space
over a one-dimensional Noetherian local domain `R`, the lattice distance is additive:
`d(M, M'') = d(M, M') + d(M', M'')`. The canonical ambient hypothesis is
`[Ring.KrullDimLE 1 R]`. -/
theorem latticeDistance_add [IsLattice K M] [IsLattice K M'] [IsLattice K M'']
    : latticeDistance M M'' = latticeDistance M M' + latticeDistance M' M'' := by
  by_cases hfield : IsField R
  · -- In the field case every lattice is `⊤`, so all three distances vanish.
    rw [latticeDistance_eq_zero_of_isField (M := M) (M' := M'') hfield]
    rw [latticeDistance_eq_zero_of_isField (M := M) (M' := M') hfield]
    rw [latticeDistance_eq_zero_of_isField (M := M') (M' := M'') hfield]
    simp
  · -- In the genuine dimension-one case, compare all three distances through one common lattice.
    let N : Submodule R V := M ⊓ M' ⊓ M''
    have hdim : ringKrullDim R = 1 :=
      ringKrullDim_eq_one_of_not_isField (R := R) hfield
    have hMM' : IsLattice K (M ⊓ M') :=
      Submodule.IsLattice.inf_of_isNoetherianRing (K := K) (M := M) (M' := M')
    letI : IsLattice K N := by
      simpa [N] using
        (Submodule.IsLattice.inf_of_isNoetherianRing (K := K) (M := M ⊓ M') (M' := M'')
          : IsLattice K ((M ⊓ M') ⊓ M''))
    have hNleM : N ≤ M := by
      exact inf_le_left.trans inf_le_left
    have hNleM' : N ≤ M' := by
      exact inf_le_left.trans inf_le_right
    have hNleM'' : N ≤ M'' := by
      exact inf_le_right
    have hNleMM'' : N ≤ M ⊓ M'' := by
      exact le_inf hNleM hNleM''
    have hNleMM' : N ≤ M ⊓ M' := by
      exact le_inf hNleM hNleM'
    have hNleM'M'' : N ≤ M' ⊓ M'' := by
      exact le_inf hNleM' hNleM''
    have hMM'' :
        latticeDistance M M'' =
          ((Module.length R (M ⧸ N.submoduleOf M)).toNat : ℤ) -
            ((Module.length R (M'' ⧸ N.submoduleOf M'')).toNat : ℤ) := by
      -- Rewrite the first distance using the common controlling lattice `N`.
      rw [Submodule.latticeDistance_def]
      exact length_difference_inf_eq_length_difference_of_le_inf
        (R := R) (K := K) (V := V) (M := M) (M' := M'') (N := N) hdim hNleMM''
    have hMM' :
        latticeDistance M M' =
          ((Module.length R (M ⧸ N.submoduleOf M)).toNat : ℤ) -
            ((Module.length R (M' ⧸ N.submoduleOf M')).toNat : ℤ) := by
      -- Rewrite the second distance through the same lattice `N`.
      rw [Submodule.latticeDistance_def]
      exact length_difference_inf_eq_length_difference_of_le_inf
        (R := R) (K := K) (V := V) (M := M) (M' := M') (N := N) hdim hNleMM'
    have hM'M'' :
        latticeDistance M' M'' =
          ((Module.length R (M' ⧸ N.submoduleOf M')).toNat : ℤ) -
            ((Module.length R (M'' ⧸ N.submoduleOf M'')).toNat : ℤ) := by
      -- Rewrite the third distance through the same lattice `N`.
      rw [Submodule.latticeDistance_def]
      exact length_difference_inf_eq_length_difference_of_le_inf
        (R := R) (K := K) (V := V) (M := M') (M' := M'') (N := N) hdim hNleM'M''
    rw [hMM'', hMM', hM'M'']
    ring

-- Proof sketch: unfold `latticeDistance`; swapping `M` and `M'` exchanges the two quotient-length
-- terms, so the defining integer difference changes sign.
/-- Swapping the two lattices negates the lattice distance. -/
theorem latticeDistance_neg_swap [IsLattice K M] [IsLattice K M'] :
    latticeDistance M M' = - latticeDistance M' M := by
  -- Apply additivity to the triangle `M → M' → M` and isolate the skew-symmetry relation.
  have hadd :
      latticeDistance M M = latticeDistance M M' + latticeDistance M' M :=
    latticeDistance_add (M := M) (M' := M') (M'' := M)
  have hself : latticeDistance M M = 0 := latticeDistance_self (M := M)
  linarith

end Submodule

end
