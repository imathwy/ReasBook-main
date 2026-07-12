import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

open QuotientGroup
open Subgroup

section

variable (H : Subgroup G) [H.Normal]

/- Source part (a) is the quotient specialization of the canonical
surjectivity theorem `Sylow.mapSurjective_surjective`. -/
#check (Sylow.mapSurjective_surjective (mk'_surjective H) p :
  Function.Surjective
    (Sylow.mapSurjective (mk'_surjective H) : Sylow p G → Sylow p (G ⧸ H)))

-- Proof sketch: if `H` is a `p`-group, then `P ∩ H` and `Q ∩ H` exhaust the entire `p`-part of
-- the kernel of the quotient map. Compare the cardinalities of two Sylow lifts with their common
-- quotient image to conclude that the quotient-image map on Sylow subgroups is injective.
/-- Exercise 8-8.4-3 (1): source part (b) in owner form. If the normal subgroup `H` is a
`p`-group, then the quotient-image map on Sylow `p`-subgroups is injective. -/
theorem sylow_mapSurjective_injective_of_normal_isPGroup
    (hH : IsPGroup p H) :
    Function.Injective
      (Sylow.mapSurjective (mk'_surjective H) : Sylow p G → Sylow p (G ⧸ H)) :=
  by
    let q : G →* G ⧸ H := mk' H
    intro P Q hPQ
    have hHP : H ≤ (P : Subgroup G) := by
      exact sup_eq_left.mp (P.is_maximal' (P.isPGroup'.to_sup_of_normal_right hH) le_sup_left)
    have hHQ : H ≤ (Q : Subgroup G) := by
      exact sup_eq_left.mp (Q.is_maximal' (Q.isPGroup'.to_sup_of_normal_right hH) le_sup_left)
    have hkerP : q.ker ≤ (P : Subgroup G) := by simpa [q, QuotientGroup.ker_mk'] using hHP
    have hkerQ : q.ker ≤ (Q : Subgroup G) := by simpa [q, QuotientGroup.ker_mk'] using hHQ
    apply Sylow.ext
    have hmap : (P : Subgroup G).map q = (Q : Subgroup G).map q := by
      simpa using congrArg (fun R : Sylow p (G ⧸ H) ↦ (R : Subgroup (G ⧸ H))) hPQ
    simpa [q, QuotientGroup.ker_mk'] using
      (Subgroup.map_injective_of_ker_le q hkerP hkerQ hmap)

-- Proof sketch: reduce to the case where `H` has order prime to `p`; when `H` is central, the
-- quotient lifts differ by a homomorphism from the common quotient-image Sylow subgroup into `H`,
-- and that homomorphism is trivial, so the quotient-image map is injective.
/-- Exercise 8-8.4-3 (2): source part (b), expressed intrinsically on subgroups. If the subgroup
`H` is central, then a Sylow `p`-subgroup is determined by its join with `H`. -/
theorem sylow_subgroup_unique_of_le_center
    (H : Subgroup G) (hH : H ≤ center G) {P Q : Sylow p G}
    (hPQ : H ⊔ (P : Subgroup G) = H ⊔ (Q : Subgroup G)) :
    P = Q := by
  let K : Subgroup G := H ⊔ (P : Subgroup G)
  have hsup : K = H ⊔ (Q : Subgroup G) := by simpa [K] using hPQ
  have hPK : (P : Subgroup G) ≤ K := le_sup_right
  have hQK : (Q : Subgroup G) ≤ K := by
    rw [hsup]
    exact le_sup_right
  have hH_normalizer : H ≤ normalizer (P : Set G) :=
    hH.trans (center_le_normalizer (P : Set G))
  haveI : (P.subtype hPK).Normal := by
    show ((P.subtype hPK : Sylow p K) : Subgroup K).Normal
    simpa [K, Sylow.coe_subtype, sup_comm] using
      normal_subgroupOf_sup_of_le_normalizer hH_normalizer
  let P' : Sylow p K := P.subtype hPK
  let Q' : Sylow p K := Q.subtype hQK
  haveI : Finite (Sylow p K) := P'.finite_of_finiteIndex
  letI := Sylow.unique_of_normal P' (show P'.Normal from inferInstance)
  exact P.subtype_injective (Subsingleton.elim P' Q')

section

variable (H : Subgroup G)

local instance normalOfLeCenter (hH : H ≤ center G) : H.Normal := by
  refine ⟨?_⟩
  intro a ha b
  change b * a * b⁻¹ ∈ H
  have hconj : b * a * b⁻¹ = a := by
    calc
      b * a * b⁻¹ = b * (a * b⁻¹) := by rw [mul_assoc]
      _ = b * (b⁻¹ * a) := by rw [Subgroup.mem_center_iff.mp (hH ha) b⁻¹]
      _ = a := by simp
  simpa [hconj] using ha

/-- Exercise 8-8.4-3 (2): owner-level quotient formulation. If the subgroup `H` is central, then
the quotient-image map on Sylow `p`-subgroups is injective. -/
theorem sylow_mapSurjective_injective_of_le_center (hH : H ≤ center G) :
    letI : H.Normal := normalOfLeCenter H hH
    Function.Injective
      (Sylow.mapSurjective (mk'_surjective H) : Sylow p G → Sylow p (G ⧸ H)) := by
  letI : H.Normal := normalOfLeCenter H hH
  let q : G →* G ⧸ H := mk' H
  intro P Q hPQ
  apply sylow_subgroup_unique_of_le_center H hH
  exact Subgroup.map_injective_of_ker_le q
    (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
    (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
    (by
      have hmap : (P : Subgroup G).map q = (Q : Subgroup G).map q := by
        simpa [Sylow.coe_mapSurjective] using
          congrArg (fun R : Sylow p (G ⧸ H) ↦ (R : Subgroup (G ⧸ H))) hPQ
      calc
        (H ⊔ (P : Subgroup G)).map q
            = H.map q ⊔ (P : Subgroup G).map q := by
                rw [Subgroup.map_sup]
        _ = H.map q ⊔ (Q : Subgroup G).map q := by rw [hmap]
        _ = (H ⊔ (Q : Subgroup G)).map q := by rw [Subgroup.map_sup])

end

end

end
