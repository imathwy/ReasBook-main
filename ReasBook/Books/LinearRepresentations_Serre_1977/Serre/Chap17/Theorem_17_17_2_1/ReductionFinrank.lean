import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_2_1

/-!
# Dimension of the reduction of a stable lattice

For a discrete valuation ring `A` with fraction field `K` and residue field `k = ResidueField A`,
and a finite-dimensional `K`-representation `E` of `G` with a `G`-stable `A`-lattice `L`, the
residue-field dimension of the reduction `L / 𝔪·L` equals the `K`-dimension of `E`.

This is the standard fact that reduction modulo the maximal ideal preserves dimension (the lattice
is `A`-free of rank `dim_K E`, and a free basis descends to a `k`-basis of the reduction by
Nakayama).  It is the keystone for showing that Serre's decomposition homomorphism sends the unit
class to the unit class (`decompositionHom 1 = 1`), used in Theorem 17-17.2-1.

The proof is deliberately built on a free `A`-basis of `L` (Nakayama route) rather than on
`TensorProduct.quotTensorEquivQuotSMul`, because the latter forces the `ResidueField A` vs
`A ⧸ 𝔪` module-instance presentation of the reduction, which clashes with the bespoke
`Module (ResidueField A) L.reduction` instance from `Definition 15-15.2-1`.
-/

noncomputable section

universe u v w

open Representation

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type v} [AddCommGroup E] [Module K E] [Module A E] [IsScalarTower A K E]
  [FiniteDimensional K E]

/-- The reduction of a `G`-stable `A`-lattice `L` in a finite-dimensional `K`-representation `E`
has residue-field dimension equal to `dim_K E`. -/
theorem finrank_reduction_eq (ρ : Representation K G E) (L : StableLattice A ρ) :
    Module.finrank (IsLocalRing.ResidueField A) L.reduction = Module.finrank K E := by
  classical
  haveI hlat : Submodule.IsLattice K L.toSubmodule := L.isLattice
  -- A free `A`-basis of the lattice.
  let b : Module.Basis (Module.Free.ChooseBasisIndex A L.toSubmodule) A L.toSubmodule :=
    Module.Free.chooseBasis A L.toSubmodule
  haveI : Fintype (Module.Free.ChooseBasisIndex A L.toSubmodule) :=
    Module.Free.ChooseBasisIndex.fintype A L.toSubmodule
  -- The candidate residue-field basis of the reduction: the classes of the lattice basis vectors.
  let c : (Module.Free.ChooseBasisIndex A L.toSubmodule) → L.reduction :=
    fun i => Submodule.Quotient.mk (b i)
  have rsmul : ∀ (a : A) (y : L.toSubmodule),
      (IsLocalRing.residue A a) • (Submodule.Quotient.mk y : L.reduction)
        = Submodule.Quotient.mk (a • y) :=
    fun a y => StableLattice.reduction_smul_mk L a y
  -- The classes span the reduction over the residue field.
  have hsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField A) (Set.range c) := by
    rintro z -
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hx : (Submodule.Quotient.mk x : L.reduction)
        = ∑ i, (IsLocalRing.residue A (b.repr x i)) • c i := by
      conv_lhs => rw [← b.sum_repr x]
      rw [← Submodule.mkQ_apply, map_sum]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [Submodule.mkQ_apply]; exact (rsmul (b.repr x i) (b i)).symm)
    rw [hx]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- The classes are residue-field linearly independent (Nakayama).
  have hli : LinearIndependent (IsLocalRing.ResidueField A) c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    choose a ha using fun i => Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal A) (g i)
    have hmem : (∑ i, a i • b i) ∈
        (IsLocalRing.maximalIdeal A) • Submodule.span A (Set.range b) := by
      rw [b.span_eq, ← Submodule.Quotient.mk_eq_zero]
      have hsum : (Submodule.Quotient.mk (∑ i, a i • b i) : L.reduction) = ∑ i, g i • c i := by
        rw [← Submodule.mkQ_apply, map_sum]
        exact Finset.sum_congr rfl (fun i _ => by
          rw [Submodule.mkQ_apply, ← ha i]; exact (rsmul (a i) (b i)).symm)
      rw [hsum, hg]
    rw [Submodule.mem_ideal_smul_span_iff_exists_sum] at hmem
    obtain ⟨d, hd, hdeq⟩ := hmem
    rw [Finsupp.sum_fintype _ _ (fun i => by simp)] at hdeq
    have hb := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hb
    have heq : ∑ i, (a i - d i) • b i = 0 := by
      simp only [sub_smul]
      rw [Finset.sum_sub_distrib, hdeq, sub_self]
    intro i
    rw [← ha i, sub_eq_zero.mp (hb (fun i => a i - d i) heq i)]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hd i)
  -- Hence the reduction has a residue-field basis indexed by the same set as the lattice basis.
  let bk : Module.Basis (Module.Free.ChooseBasisIndex A L.toSubmodule)
      (IsLocalRing.ResidueField A) L.reduction := Module.Basis.mk hli hsp
  have h1 : Module.finrank (IsLocalRing.ResidueField A) L.reduction
      = Fintype.card (Module.Free.ChooseBasisIndex A L.toSubmodule) :=
    Module.finrank_eq_card_basis bk
  have h2 : Module.finrank A L.toSubmodule
      = Fintype.card (Module.Free.ChooseBasisIndex A L.toSubmodule) :=
    Module.finrank_eq_card_basis b
  have h3 : Module.finrank A L.toSubmodule = Module.finrank K E :=
    congrArg Cardinal.toNat (Submodule.IsLattice.rank' (R := A) (K := K) (V := E) L.toSubmodule)
  rw [h1, ← h2]; exact h3
