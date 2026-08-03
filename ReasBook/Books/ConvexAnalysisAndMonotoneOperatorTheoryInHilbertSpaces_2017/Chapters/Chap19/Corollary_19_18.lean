import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap19.Definition_19_11
import BauschkeLean.Chap19.Proposition_19_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open Set

universe u v

namespace ERealFunction

section ParametricDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/- Source/core/bridge triage:
- `source-facing`: Corollary 19.18 characterizes a dual minimizer by equality between one
  Lagrangian fiber infimum and the supremum of all such infima.
- `core/canonical`: the owner abstractions are `Argmin`, `perturbationDualObjective F`, and the
  Lagrangian owner `ℒ[F]`.
- `bridge/view`: the corollary is obtained by transporting the canonical `Argmin` criterion through
  Proposition 19.17(iv), so the public theorem should stay a thin bridge rather than introducing a
  second owner for the dual value function.
-/

-- Proof sketch: rewrite `v ∈ Argmin (perturbationDualObjective F)` as minimization of the dual
-- objective. Then apply Proposition 19.17(iv) pointwise to identify each fiber infimum
-- `inf_x ℒ[F] x w` with `-F^*(0, w)`, and convert minimizing `F^*(0, ·)` into maximizing the
-- Lagrangian fiber-infimum map.
/-- Helper for Corollary 19.18: in `EReal`, the infimum of pointwise negatives is the negative of
the corresponding supremum. -/
private theorem iInf_neg_eq_neg_iSup_ereal
    {ι : Sort*} (φ : ι → EReal) :
    (⨅ i, -φ i) = -(⨆ i, φ i) := by
  -- Negation is an order isomorphism, so it carries the infimum to the supremum.
  have hmap : -(⨅ i, -φ i) = ⨆ i, -(-φ i) := by
    exact OrderIso.map_iInf EReal.negOrderIso (fun i : ι ↦ -φ i)
  have hmap' : -(⨅ i, -φ i) = (⨆ i, φ i) := by
    simpa using hmap
  rw [← hmap']
  simp

/-- Helper for Corollary 19.18: in `EReal`, the supremum of pointwise negatives is the negative of
the corresponding infimum. -/
private theorem iSup_neg_eq_neg_iInf_ereal
    {ι : Sort*} (φ : ι → EReal) :
    (⨆ i, -φ i) = -(⨅ i, φ i) := by
  -- Dualize the previous infimum identity by applying it to `-φ`.
  have hdual : (⨅ i, φ i) = -(⨆ i, -φ i) := by
    simpa using (iInf_neg_eq_neg_iSup_ereal (fun i : ι ↦ -φ i))
  have hneg := congrArg Neg.neg hdual
  simpa using hneg.symm

/-- Helper for Corollary 19.18: the infimum of the fixed-`v` Lagrangian fiber equals the negated
dual perturbation objective at `v`. -/
private theorem lagrangianFiberInf_eq_neg_perturbationDualObjective
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    sInf (Set.range fun x : H ↦ ℒ[F] x v) = -perturbationDualObjective F v := by
  -- Flatten the two-stage infimum to a product infimum and rewrite each term as a negative.
  calc
    sInf (Set.range fun x : H ↦ ℒ[F] x v) =
        ⨅ p : H × K, (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal) := by
          rw [sInf_range]
          calc
            (⨅ x : H, ℒ[F] x v) =
                ⨅ x : H, ⨅ y : K, (F (x, y) : EReal) - (⟪y, v⟫_ℝ : EReal) := by
                  simp [lagrangian_apply]
            _ = ⨅ p : H × K, (F p : EReal) - (⟪p.2, v⟫_ℝ : EReal) := by
                  rw [iInf_prod]
    _ = ⨅ p : H × K, -((((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal))) := by
          refine iInf_congr fun p ↦ ?_
          simpa [sub_eq_add_neg, add_comm] using
            (EReal.neg_sub
              (x := (((⟪p.2, v⟫_ℝ : ℝ) : EReal)))
              (y := (F p : EReal))
              (.inl (EReal.coe_ne_bot _))
              (.inl (EReal.coe_ne_top _))).symm
    _ = -(⨆ p : H × K, (((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal))) := by
          let ψ : H × K → EReal := fun p : H × K ↦
            (((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal))
          simpa [ψ] using iInf_neg_eq_neg_iSup_ereal ψ
    _ = -perturbationDualObjective F v := by
          rw [perturbationDualObjective_apply]

/-- Helper for Corollary 19.18: the supremum over multipliers of the Lagrangian fiber infima is
the negated infimum of the dual perturbation objective. -/
private theorem lagrangianFiberInfSup_eq_neg_sInf_perturbationDualObjective
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    sSup (Set.range fun w : K ↦ sInf (Set.range fun x : H ↦ ℒ[F] x w)) =
      -sInf (Set.range (perturbationDualObjective F)) := by
  -- Rewrite each fiber infimum by the previous bridge and collapse the supremum of negatives.
  rw [sSup_range, sInf_range]
  simp_rw [lagrangianFiberInf_eq_neg_perturbationDualObjective]
  simpa using iSup_neg_eq_neg_iInf_ereal (fun w : K ↦ perturbationDualObjective F w)

/-- Corollary 19.18: a point `v` minimizes the dual objective exactly when the infimum of the
Lagrangian fiber `x ↦ ℒ[F] x v` equals the supremum over `w` of the infima of the fibers
`x ↦ ℒ[F] x w`. -/
theorem mem_argmin_perturbationDualObjective_iff_lagrangian_sInf_eq_sSup
    (F : H × K → Set.Ioi (⊥ : EReal)) (v : K) :
    v ∈ Argmin (perturbationDualObjective F) ↔
      sInf (Set.range fun x : H ↦ ℒ[F] x v) =
        sSup (Set.range fun w : K ↦ sInf (Set.range fun x : H ↦ ℒ[F] x w)) := by
  constructor
  · intro hv
    -- Convert the `Argmin` statement into the canonical dual-objective infimum equality.
    have hvEq :
        perturbationDualObjective F v = sInf (Set.range (perturbationDualObjective F)) :=
      mem_argmin_iff_eq_sInf.mp hv
    have hneg :
        -perturbationDualObjective F v = -sInf (Set.range (perturbationDualObjective F)) := by
      exact congrArg Neg.neg hvEq
    -- Transport that equality through the Lagrangian-fiber normalization.
    calc
      sInf (Set.range fun x : H ↦ ℒ[F] x v) = -perturbationDualObjective F v := by
            exact lagrangianFiberInf_eq_neg_perturbationDualObjective F v
      _ = -sInf (Set.range (perturbationDualObjective F)) := hneg
      _ = sSup (Set.range fun w : K ↦ sInf (Set.range fun x : H ↦ ℒ[F] x w)) := by
            symm
            exact lagrangianFiberInfSup_eq_neg_sInf_perturbationDualObjective F
  · intro hLag
    -- Route correction: recover the dual-objective infimum equality by negating the normalized
    -- Lagrangian identity instead of trying to use the stronger imported Proposition 19.17 API.
    have hneg :
        -perturbationDualObjective F v = -sInf (Set.range (perturbationDualObjective F)) := by
      calc
        -perturbationDualObjective F v = sInf (Set.range fun x : H ↦ ℒ[F] x v) := by
              symm
              exact lagrangianFiberInf_eq_neg_perturbationDualObjective F v
        _ = sSup (Set.range fun w : K ↦ sInf (Set.range fun x : H ↦ ℒ[F] x w)) := hLag
        _ = -sInf (Set.range (perturbationDualObjective F)) := by
              exact lagrangianFiberInfSup_eq_neg_sInf_perturbationDualObjective F
    have hvEq :
        perturbationDualObjective F v = sInf (Set.range (perturbationDualObjective F)) := by
      -- Negating both sides removes the bridge sign and returns the `Argmin` criterion.
      simpa using congrArg Neg.neg hneg
    exact mem_argmin_iff_eq_sInf.mpr hvEq

end ParametricDuality

end ERealFunction
