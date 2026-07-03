import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section Group

variable {G : Type u} [Group G]
variable {p : ℕ}

local notation "C(" x ")" => Subgroup.centralizer ({x} : Set G)

namespace IsPElementaryDecomposition

-- Proof sketch: the decomposition hypothesis makes the image of `P` in `G` a `p`-subgroup of the
-- centralizer of `x`, because every element of `P` commutes with the cyclic factor `C` and `x`
-- generates `C`. Reconstruct `Fact p.Prime` from `hH.prime`, then enlarge that `p`-subgroup to a
-- Sylow subgroup `Q ≤ C_G(x)` using `IsPGroup.exists_le_sylow`; then the decomposition
-- `H = C ⋅ P` maps to the inclusion `H ≤ associatedPElementarySubgroup p x Q`.
/-- Exercise 10-10.1-5: if the cyclic factor in a `p`-elementary decomposition of `H` is `⟨x⟩`,
then `H` is contained in the associated subgroup of `G` attached to `x`; its `p`-elementarity is
the canonical content of `associatedPElementarySubgroup_isPElementary`. -/
theorem exists_le_associatedPElementarySubgroup {H : Subgroup G} {x : H} {P : Subgroup H}
    (hH : IsPElementaryDecomposition p (Subgroup.zpowers x) P) :
    ∃ Q : Sylow p C((x : G)),
      H ≤ associatedPElementarySubgroup p (x : G) Q := by
  letI : Fact p.Prime := ⟨hH.prime⟩
  let CGx : Subgroup G := C((x : G))
  let P' : Subgroup G := P.map H.subtype
  have hxC : x ∈ Subgroup.zpowers x :=
    Subgroup.mem_zpowers x
  have hP'_le_centralizer : P' ≤ CGx := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hH.commute ⟨x, hxC⟩ ⟨y, hy⟩).map H.subtype).symm.eq
  have hP' : IsPGroup p P' :=
    hH.isPGroup.of_surjective (H.subtype.subgroupMap P) (H.subtype.subgroupMap_surjective P)
  have hP'_centralizer : IsPGroup p (P'.subgroupOf CGx) :=
    hP'.of_equiv (Subgroup.subgroupOfEquivOfLe hP'_le_centralizer).symm
  obtain ⟨Q, hPQ⟩ := hP'_centralizer.exists_le_sylow
  have hP'_le_Qmap : P' ≤ Subgroup.map CGx.subtype (Q : Subgroup CGx) := by
    calc
      P' = Subgroup.map CGx.subtype (P'.subgroupOf CGx) := by
        symm
        exact Subgroup.map_subgroupOf_eq_of_le hP'_le_centralizer
      _ ≤ Subgroup.map CGx.subtype (Q : Subgroup CGx) := Subgroup.map_mono hPQ
  have hH_eq :
      H = Subgroup.zpowers (x : G) ⊔ P' := by
    calc
      H = (⊤ : Subgroup H).map H.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (Subgroup.zpowers x ⊔ P).map H.subtype := by rw [← hH.isComplement.sup_eq_top]
      _ = Subgroup.zpowers (H.subtype x) ⊔ P' := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      _ = Subgroup.zpowers (x : G) ⊔ P.map H.subtype := by rfl
  refine ⟨Q, ?_⟩
  calc
    H = Subgroup.zpowers (x : G) ⊔ P' := hH_eq
    _ ≤ Subgroup.zpowers (x : G) ⊔ Subgroup.map CGx.subtype (Q : Subgroup CGx) :=
      sup_le_sup le_rfl hP'_le_Qmap
    _ = associatedPElementarySubgroup p (x : G) Q := by
      simp [associatedPElementarySubgroup, CGx]

end IsPElementaryDecomposition

end Group
