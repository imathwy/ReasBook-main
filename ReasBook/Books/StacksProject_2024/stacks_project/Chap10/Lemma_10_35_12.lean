import StacksProject_2024.stacks_project.Chap10.Theorem_10_35_11

-- Declarations for this item will be appended below by the statement pipeline.

open Cardinal
open Algebra.TensorProduct
open scoped TensorProduct

universe u v w

section

variable {k : Type u} {S : Type v} {K : Type w}
variable [Field k] [CommRing S] [Algebra k S] [Field K] [Algebra k K]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (includeRight : S →ₐ[k] S_K)

private theorem adjoin_range_includeRight_eq_top :
    Algebra.adjoin K (Set.range iSK) = ⊤ := by
  simpa [Set.image_univ] using
    adjoin_one_tmul_image_eq_top (Set.univ : Set S) (Algebra.adjoin_univ k S)

private theorem lift_mk_range_includeRight_lt
    (hcard :
      Cardinal.lift.{max w v, v} #S <
        Cardinal.lift.{max w v, w} #K) :
    Cardinal.lift.{max v w, max v w}
        #(Set.range iSK) <
      Cardinal.lift.{max v w, w} #K := by
  have hle :
      Cardinal.lift.{v, max v w}
          #(Set.range iSK) ≤
        Cardinal.lift.{max v w, v} #S := by
    exact Cardinal.mk_range_le_lift
  have hsmall :
      Cardinal.lift.{v, max v w}
          #(Set.range iSK) <
        Cardinal.lift.{max v w, w} #K := by
    exact lt_of_le_of_lt hle <| by simpa [max_comm] using hcard
  rw [Cardinal.lift_id'.{v, w}] at hsmall
  simpa [Cardinal.lift_id] using hsmall

/-- Lemma 10.35.12 (1): if `K/k` is a field extension with `#S < #K`, then for every maximal ideal
`m` of the scalar extension `K ⊗[k] S`, the residue field `m.ResidueField` is algebraic over
`K`. -/
theorem isAlgebraic_residueField_of_maximal_scalarExtension_of_cardinalMk_lt
    (_hcard :
      Cardinal.lift.{max w v, v} #S <
        Cardinal.lift.{max w v, w} #K)
    (m : Ideal S_K) [m.IsMaximal] :
    Algebra.IsAlgebraic K m.ResidueField := by
  simpa using
    isAlgebraic_residueField_of_maximal_of_adjoin_eq_top_of_cardinalMk_lt m

/-- Lemma 10.35.12 (2): if `K/k` is a field extension with `#S < #K`, then the scalar extension
`K ⊗[k] S` is a Jacobson ring. -/
theorem isJacobsonRing_scalarExtension_of_cardinalMk_lt
    (_hcard :
      Cardinal.lift.{max w v, v} #S <
        Cardinal.lift.{max w v, w} #K) :
    IsJacobsonRing S_K := by
  simpa using
    isJacobsonRing_of_adjoin_eq_top_of_cardinalMk_lt

end
