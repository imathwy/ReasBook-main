import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_4_1 (from Items/Chap01) -/
universe u v

noncomputable section

section

variable {F : Type u} [Group F] {X : Type v}

namespace FreeGroupBasis

/-- The `(T1)` inversion automorphism relative to `basis`. -/
private def invertElementaryNielsenEndomorphism
    (basis : FreeGroupBasis X F) (x : X) : F →* F :=
  letI : DecidableEq X := Classical.decEq X
  basis.lift fun z ↦ if z = x then (basis x)⁻¹ else basis z

@[simp] private theorem invertElementaryNielsenEndomorphism_apply_self
    (basis : FreeGroupBasis X F) (x : X) :
    invertElementaryNielsenEndomorphism basis x (basis x) = (basis x)⁻¹ := by
  letI : DecidableEq X := Classical.decEq X
  simp [invertElementaryNielsenEndomorphism]

@[simp] private theorem invertElementaryNielsenEndomorphism_apply_of_ne
    (basis : FreeGroupBasis X F) {x z : X} (hz : z ≠ x) :
    invertElementaryNielsenEndomorphism basis x (basis z) = basis z := by
  letI : DecidableEq X := Classical.decEq X
  simp [invertElementaryNielsenEndomorphism, hz]

/-- The `(T1)` inversion automorphism relative to `basis`. -/
def elementaryNielsenInversion
    (basis : FreeGroupBasis X F) (x : X) : MulAut F :=
  MonoidHom.toMulEquiv
    (invertElementaryNielsenEndomorphism basis x)
    (invertElementaryNielsenEndomorphism basis x)
    (by
      apply basis.ext_hom
      intro z
      by_cases hz : z = x
      · subst hz
        simp
      · simp [MonoidHom.comp_apply, hz])
    (by
      apply basis.ext_hom
      intro z
      by_cases hz : z = x
      · subst hz
        simp
      · simp [MonoidHom.comp_apply, hz])

/-- The inversion automorphism sends the chosen basis element `basis x` to its inverse. -/
@[simp] theorem elementaryNielsenInversion_apply_self
    (basis : FreeGroupBasis X F) (x : X) :
    elementaryNielsenInversion basis x (basis x) = (basis x)⁻¹ := by
  simp [elementaryNielsenInversion]

/-- The inversion automorphism fixes every basis element other than `basis x`. -/
@[simp] theorem elementaryNielsenInversion_apply_of_ne
    (basis : FreeGroupBasis X F) {x z : X} (hz : z ≠ x) :
    elementaryNielsenInversion basis x (basis z) = basis z := by
  simp [elementaryNielsenInversion, hz]

/-- The `(T2)` transvection endomorphism relative to `basis`. -/
private def multiplyElementaryNielsenEndomorphism
    (basis : FreeGroupBasis X F) (x y : X) : F →* F :=
  letI : DecidableEq X := Classical.decEq X
  basis.lift fun z ↦ if z = x then basis x * basis y else basis z

/-- The inverse endomorphism for the `(T2)` transvection relative to `basis`. -/
private def multiplyElementaryNielsenEndomorphismInv
    (basis : FreeGroupBasis X F) (x y : X) : F →* F :=
  letI : DecidableEq X := Classical.decEq X
  basis.lift fun z ↦ if z = x then basis x * (basis y)⁻¹ else basis z

@[simp] private theorem multiplyElementaryNielsenEndomorphism_apply_fst
    (basis : FreeGroupBasis X F) (x y : X) :
    multiplyElementaryNielsenEndomorphism basis x y (basis x) = basis x * basis y := by
  letI : DecidableEq X := Classical.decEq X
  simp [multiplyElementaryNielsenEndomorphism]

@[simp] private theorem multiplyElementaryNielsenEndomorphism_apply_of_ne
    (basis : FreeGroupBasis X F) (x y : X) {z : X} (hz : z ≠ x) :
    multiplyElementaryNielsenEndomorphism basis x y (basis z) = basis z := by
  letI : DecidableEq X := Classical.decEq X
  simp [multiplyElementaryNielsenEndomorphism, hz]

@[simp] private theorem multiplyElementaryNielsenEndomorphismInv_apply_fst
    (basis : FreeGroupBasis X F) (x y : X) :
    multiplyElementaryNielsenEndomorphismInv basis x y (basis x) =
      basis x * (basis y)⁻¹ := by
  letI : DecidableEq X := Classical.decEq X
  simp [multiplyElementaryNielsenEndomorphismInv]

@[simp] private theorem multiplyElementaryNielsenEndomorphismInv_apply_of_ne
    (basis : FreeGroupBasis X F) (x y : X) {z : X} (hz : z ≠ x) :
    multiplyElementaryNielsenEndomorphismInv basis x y (basis z) = basis z := by
  letI : DecidableEq X := Classical.decEq X
  simp [multiplyElementaryNielsenEndomorphismInv, hz]

/-- The `(T2)` transvection automorphism relative to `basis`. -/
def elementaryNielsenTransvection
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) : MulAut F :=
  MonoidHom.toMulEquiv
    (multiplyElementaryNielsenEndomorphism basis x y)
    (multiplyElementaryNielsenEndomorphismInv basis x y)
    (by
      apply basis.ext_hom
      intro z
      by_cases hz : z = x
      · subst z
        rw [MonoidHom.comp_apply, multiplyElementaryNielsenEndomorphism_apply_fst, map_mul,
          multiplyElementaryNielsenEndomorphismInv_apply_fst,
          multiplyElementaryNielsenEndomorphismInv_apply_of_ne basis x y hxy.symm]
        simp
      · rw [MonoidHom.comp_apply,
          multiplyElementaryNielsenEndomorphism_apply_of_ne basis x y hz,
          multiplyElementaryNielsenEndomorphismInv_apply_of_ne basis x y hz]
        simp)
    (by
      apply basis.ext_hom
      intro z
      by_cases hz : z = x
      · subst z
        rw [MonoidHom.comp_apply, multiplyElementaryNielsenEndomorphismInv_apply_fst, map_mul,
          map_inv, multiplyElementaryNielsenEndomorphism_apply_fst,
          multiplyElementaryNielsenEndomorphism_apply_of_ne basis x y hxy.symm]
        simp
      · rw [MonoidHom.comp_apply,
          multiplyElementaryNielsenEndomorphismInv_apply_of_ne basis x y hz,
          multiplyElementaryNielsenEndomorphism_apply_of_ne basis x y hz]
        simp)

/-- The transvection sends the moved basis element to its product with the companion basis
element. -/
@[simp] theorem elementaryNielsenTransvection_apply_fst
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) :
    elementaryNielsenTransvection basis x y hxy (basis x) = basis x * basis y := by
  simp [elementaryNielsenTransvection]

/-- The transvection fixes every basis element other than the moved one. -/
@[simp] theorem elementaryNielsenTransvection_apply_of_ne
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) {z : X} (hz : z ≠ x) :
    elementaryNielsenTransvection basis x y hxy (basis z) = basis z := by
  simp [elementaryNielsenTransvection, hz]

/-- The inverse transvection sends the moved basis element to its product with the inverse of the
companion basis element. -/
@[simp] theorem elementaryNielsenTransvection_inv_apply_fst
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) :
    (elementaryNielsenTransvection basis x y hxy)⁻¹ (basis x) =
      basis x * (basis y)⁻¹ := by
  simp [elementaryNielsenTransvection]

/-- The inverse transvection fixes every basis element other than the moved one. -/
@[simp] theorem elementaryNielsenTransvection_inv_apply_of_ne
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) {z : X} (hz : z ≠ x) :
    (elementaryNielsenTransvection basis x y hxy)⁻¹ (basis z) = basis z := by
  simp [elementaryNielsenTransvection, hz]

/-- The subgroup `Aut_f(F)` generated by the elementary Nielsen automorphisms relative to the
chosen basis `basis`. -/
def elementaryNielsenAutomorphismSubgroup (basis : FreeGroupBasis X F) : Subgroup (MulAut F) :=
  Subgroup.closure
    (Set.range (basis.elementaryNielsenInversion) ∪
      Set.range fun xy : {p : X × X // p.1 ≠ p.2} ↦
        basis.elementaryNielsenTransvection xy.1.1 xy.1.2 xy.2)

/-- Each inversion generator belongs to the elementary Nielsen automorphism subgroup. -/
theorem elementaryNielsenInversion_mem_subgroup
    (basis : FreeGroupBasis X F) (x : X) :
    basis.elementaryNielsenInversion x ∈ basis.elementaryNielsenAutomorphismSubgroup := by
  exact Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)

/-- Each transvection generator belongs to the elementary Nielsen automorphism subgroup. -/
theorem elementaryNielsenTransvection_mem_subgroup
    (basis : FreeGroupBasis X F) (x y : X) (hxy : x ≠ y) :
    basis.elementaryNielsenTransvection x y hxy ∈ basis.elementaryNielsenAutomorphismSubgroup := by
  exact Subgroup.subset_closure (Or.inr ⟨⟨(x, y), hxy⟩, rfl⟩)

/-- Proposition 1-4-1: the subgroup generated by the elementary Nielsen automorphisms is dense in
`Aut(F)` for the pointwise topology on finite families, meaning that every automorphism can be
matched on any prescribed finite family of elements. -/
-- Layer triage:
-- `source-facing`: a free group `F` with basis `basis : FreeGroupBasis X F`, a finite family
-- `u : ι → F` indexed by an arbitrary finite type, and an automorphism `α : MulAut F`.
-- `core/canonical`: the automorphism group `MulAut F` together with the canonical basis owner
-- abstraction `FreeGroupBasis X F`, with generated subgroup owner `Subgroup.closure` and the
-- canonical finite-family interface `ι → F` under `[Finite ι]`.
-- `bridge/view`: the internal generator set is the concrete `(T1)` inversion and `(T2)`
-- transvection automorphism families relative to `basis`.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` in `Mathlib/GroupTheory/FreeGroup/IsFreeGroup` is the canonical owner
--    abstraction for a chosen free basis of `F`.
-- 2. `MulAut F` in `Mathlib/Algebra/Group/End` is the canonical automorphism group of `F`.
-- 3. `FreeGroupBasis.lift` provides the canonical basis-determined endomorphisms used to realize
--    the regular Nielsen generators as actual automorphisms.
-- 4. `FreeGroupBasis.ext_hom` shows that endomorphisms of a free group are determined by their
--    values on a basis, matching the source proof strategy and the inverse checks above.
-- Primitive/derived split:
-- the public owner object is only `basis.elementaryNielsenAutomorphismSubgroup`;
-- the finite family itself is primitive source data and should therefore stay at the canonical
-- owner level `ι → F` for arbitrary `[Fintype ι]`; the private generator families above are
-- implementation-level bridge data for the subgroup owner.
-- Proof sketch: reduce to the finite subfamily of basis elements needed to write the given finite
-- family `u`, apply Nielsen reduction to the corresponding finite tuple of basis images under
-- `α⁻¹`, and read the resulting regular Nielsen transformation as an element of the subgroup
-- generated by the elementary Nielsen automorphisms. The source calculation then shows that this
-- element agrees with `α` on the prescribed family.
theorem exists_elementaryNielsenAutomorphism_eq_on_finite_family
    (basis : FreeGroupBasis X F) {ι : Type*} [Finite ι] (u : ι → F) (α : MulAut F) :
    ∃ β ∈ basis.elementaryNielsenAutomorphismSubgroup, ∀ i, β (u i) = α (u i) := sorry

/-- If the chosen free basis is finite, then the subgroup generated by the elementary Nielsen
automorphisms is the whole automorphism group. -/
-- Proof sketch: apply the density theorem to the finite family consisting of all basis elements.
-- An automorphism of `F` is determined by its values on `basis`, so agreement on that finite
-- family forces equality. Hence every automorphism belongs to the generated subgroup.
theorem elementaryNielsenAutomorphismSubgroup_eq_top_of_finite
    (basis : FreeGroupBasis X F) [Finite X] :
    basis.elementaryNielsenAutomorphismSubgroup = ⊤ := sorry

end FreeGroupBasis

end

/-! ### Proposition_1_4_2 (from Items/Chap01) -/
universe u v

section

variable {F : Type u} [Group F] {X : Type v}

namespace FreeGroupBasis

/-- The set of basis indices moved by an automorphism. -/
def movedBasisSupport (basis : FreeGroupBasis X F) (α : MulAut F) : Set X :=
  {x | α (basis x) ≠ basis x}

private theorem finite_moved_one (basis : FreeGroupBasis X F) :
    (basis.movedBasisSupport (1 : MulAut F)).Finite := sorry

private theorem finite_moved_mul (basis : FreeGroupBasis X F) {α β : MulAut F}
    (hα : (basis.movedBasisSupport α).Finite)
    (hβ : (basis.movedBasisSupport β).Finite) :
    (basis.movedBasisSupport (α * β)).Finite := sorry

private theorem finite_moved_inv (basis : FreeGroupBasis X F) {α : MulAut F}
    (hα : (basis.movedBasisSupport α).Finite) :
    (basis.movedBasisSupport α⁻¹).Finite := sorry

/-- The automorphisms moving only finitely many elements of the chosen basis. -/
def finiteMovedSubgroup (basis : FreeGroupBasis X F) : Subgroup (MulAut F) where
  carrier := {α | (basis.movedBasisSupport α).Finite}
  one_mem' := finite_moved_one basis
  mul_mem' := fun hα hβ ↦ finite_moved_mul basis hα hβ
  inv_mem' := fun hα ↦ finite_moved_inv basis hα

@[simp] theorem mem_finiteMovedSubgroup (basis : FreeGroupBasis X F) (α : MulAut F) :
    α ∈ basis.finiteMovedSubgroup ↔ (basis.movedBasisSupport α).Finite :=
  Iff.rfl

end FreeGroupBasis

namespace FreeGroupBasis

/-- Proposition 1-4-2: the elementary Nielsen subgroup for `basis` is exactly the subgroup of
automorphisms moving only finitely many elements of that chosen basis. -/
-- Layer triage:
-- `bridge/view`: this proposition identifies the subgroup owner
-- `basis.elementaryNielsenAutomorphismSubgroup` from Proposition `1-4-1` with the basis-owned
-- finite-support subgroup `basis.finiteMovedSubgroup`.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the canonical owner object for a chosen free basis of `F`.
-- 2. `MulAut F` is the canonical automorphism group of `F`.
-- 3. `basis.elementaryNielsenAutomorphismSubgroup` from Proposition `1-4-1` is the project owner
--    for the subgroup `Aut_f(F)` attached to `basis`.
-- 4. `Subgroup (MulAut F)` is the canonical owner level for a subgroup of automorphisms, so the
--    finite-moved condition should be packaged as `basis.finiteMovedSubgroup` rather than exposed
--    through a parallel predicate wrapper.
-- Primitive/derived split:
-- the primitive owner declarations are the moved-index set `basis.movedBasisSupport` and the two
-- subgroups `basis.elementaryNielsenAutomorphismSubgroup` and `basis.finiteMovedSubgroup`;
-- the finite-support membership test is derived canonically from
-- `FreeGroupBasis.mem_finiteMovedSubgroup`.

theorem elementaryNielsenAutomorphismSubgroup_eq_finiteMovedSubgroup
    (basis : FreeGroupBasis X F) :
    basis.elementaryNielsenAutomorphismSubgroup = basis.finiteMovedSubgroup := sorry

/-- Membership in the elementary Nielsen subgroup is equivalent to moving only finitely many basis
elements. -/
theorem mem_elementaryNielsenAutomorphismSubgroup_iff
    (basis : FreeGroupBasis X F) (α : MulAut F) :
    α ∈ basis.elementaryNielsenAutomorphismSubgroup ↔ (basis.movedBasisSupport α).Finite := by
  rw [elementaryNielsenAutomorphismSubgroup_eq_finiteMovedSubgroup,
    FreeGroupBasis.mem_finiteMovedSubgroup]

end FreeGroupBasis

end

/-! ### Remark_1_4_3 (from Items/Chap01) -/
universe u v

open FreeGroup

noncomputable section

variable {F : Type u} [Group F] {X : Type v}

-- Layer triage:
-- `source-facing`: the contrast between the cardinalities of `Aut(F)` and the subgroup
-- `Aut_f(F)` attached to a countably infinite basis `basis : FreeGroupBasis X F`.
-- `core/canonical`: `MulAut F`, the chosen-basis owner `FreeGroupBasis X F`, and the basis-owned
-- finite-support subgroup `basis.finiteMovedSubgroup`.
-- `bridge/view`: Proposition `1-4-2` identifies `Aut_f(F)` with that owner subgroup, while
-- permutations of the basis index type transport through `basis.repr` into `MulAut F` for the
-- uncountability argument.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` in `Mathlib/GroupTheory/FreeGroup/IsFreeGroup` is the owner
--    abstraction for a chosen free basis of `F`.
-- 2. `MulAut F` is the canonical automorphism group of `F`.
-- 3. `FreeGroupBasis.finiteMovedSubgroup` from Proposition `1-4-2` is the chapter owner for the
--    finite-support subgroup on a chosen basis.
-- 4. `elementaryNielsenAutomorphismSubgroup_eq_finiteMovedSubgroup` is the source-to-owner bridge
--    identifying `Aut_f(F)` with that finite-support subgroup, and `basis.repr` together with
--    `freeGroupCongr` gives the canonical permutation action used below.
-- Primitive/derived split:
-- the primitive public data are the ambient group `F` and an explicit basis
-- `basis : FreeGroupBasis X F`; the finite-support subgroup `basis.finiteMovedSubgroup` and the
-- source-facing subgroup `basis.elementaryNielsenAutomorphismSubgroup` are derived owner-level
-- constructions, while infinitude and countability of `X` enter only in the cardinality theorems.

/-- Distinct permutations of the basis indices induce distinct automorphisms of `F`. -/
private theorem basisReindexMulAut_injective (basis : FreeGroupBasis X F) :
    Function.Injective
      (fun σ : Equiv.Perm X ↦ (basis.repr.trans (freeGroupCongr σ)).trans basis.repr.symm) := by
  -- Proof sketch: compare the induced automorphisms on the basis elements `basis x`; if the
  -- induced automorphisms agree, transport through `basis.repr` to conclude that the underlying
  -- permutations agree on every index.
  sorry

/-- The automorphism group of a free group with infinite basis `basis` is uncountable. -/
-- Proof sketch: the canonical map
-- `fun σ : Equiv.Perm X ↦ (basis.repr.trans (freeGroupCongr σ)).trans basis.repr.symm`
-- injects the symmetric group on the basis index type into `MulAut F`, and the permutation group
-- of an infinite set is uncountable.
theorem automorphismGroup_uncountable_of_infiniteBasis
    (basis : FreeGroupBasis X F) [Infinite X] :
    Uncountable (MulAut F) := sorry

section CountableBasis

variable [Countable X]

/-- The basis-owned finite-support subgroup is countable when the basis index type is countable. -/
-- Proof sketch: an element of `basis.finiteMovedSubgroup` is determined by a finite subset of the
-- countable basis index type together with a permutation on that finite support,
-- so the subgroup is a countable union of finite-symmetry data.
theorem finiteMovedSubgroup_countable (basis : FreeGroupBasis X F) :
    Countable ↥(basis.finiteMovedSubgroup) := sorry

/-- The subgroup `Aut_f(F)` attached to `basis` is countable when the basis index type is
countable. -/
theorem elementaryNielsenAutomorphismSubgroup_countable (basis : FreeGroupBasis X F) :
    Countable ↥(basis.elementaryNielsenAutomorphismSubgroup) := by
  have h : Countable ↥(basis.finiteMovedSubgroup) :=
    finiteMovedSubgroup_countable basis
  simpa [basis.elementaryNielsenAutomorphismSubgroup_eq_finiteMovedSubgroup] using h

/-- Remark 1-4-3: if a free group has a countably infinite basis, then its full automorphism group
is uncountable, while the subgroup `Aut_f(F)` attached to that basis is countable. -/
-- Proof sketch: embed the symmetric group on the basis index type into `MulAut F` to obtain
-- uncountability, and pass from the canonical finite-support subgroup
-- `basis.finiteMovedSubgroup` back to `Aut_f(F)` using Proposition `1-4-2`.
theorem automorphism_group_cardinality_contrast
    (basis : FreeGroupBasis X F) [Infinite X] :
    Uncountable (MulAut F) ∧
      Countable ↥(basis.elementaryNielsenAutomorphismSubgroup) := by
  exact ⟨automorphismGroup_uncountable_of_infiniteBasis basis,
    elementaryNielsenAutomorphismSubgroup_countable basis⟩

end CountableBasis

/-! ### Proposition_1_4_4 (from Items/Chap01) -/
universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]
variable [Group.FG F]

namespace MulAut

/-- Proposition 1-4-4: if `F` is a free group of finite rank greater than `1`, then `Aut(F)` is
complete, meaning that its center is trivial and every automorphism of `Aut(F)` is inner. -/
-- Layer triage:
-- `source-facing`: completeness of the automorphism group of a finitely generated free group of
-- rank `> 1`, expressed through the intrinsic chapter owner `Group.rank`.
-- `core/canonical`: the owner group `MulAut F`, its center `Subgroup.center (MulAut F)`, the
-- chapter owner subgroup `innerAutomorphismSubgroup (MulAut F)` of inner automorphisms of
-- `Aut(F)`, and `Group.rank`.
-- `bridge/view`: the textbook phrase “every automorphism is inner” is expressed by the owner
-- equality `innerAutomorphismSubgroup (MulAut F) = ⊤`.
-- Domain sampling:
-- 1. `innerAutomorphismSubgroup` in `Proposition_1_4_5` is the chapter owner for the subgroup
--    of inner automorphisms, already defined as the range of `MulAut.conj`.
-- 2. `MulAut.conj` in `Mathlib/Algebra/Group/End` remains the primitive canonical map behind
--    that owner subgroup.
-- 3. `Subgroup.center` in `Mathlib/GroupTheory/Subgroup/Center` is the canonical center
--    construction for a group.
-- 4. `eq_of_le_of_rank_ge_of_finiteIndex_subgroup` in `Proposition_1_3_17` shows the chapter
--    owner style for the hypothesis “rank greater than `1`”: use `1 < Group.rank F`.
-- Primitive vs. derived:
-- the primitive owner-side public content is split into the atomic statements
-- `Subgroup.center (MulAut F) = ⊥` and `innerAutomorphismSubgroup (MulAut F) = ⊤`, under
-- the intrinsic rank hypothesis `1 < Group.rank F`; the source-facing textbook completeness
-- statement is the conjunction of those two owner facts. The underlying range description in
-- terms of `MulAut.conj` is derived API and is omitted from the public surface.
-- Proof sketch: by Burnside's observation it is enough to show that the subgroup of inner
-- automorphisms of `F` is characteristic in `Aut(F)`. Dyer and Formanek prove this for finitely
-- generated free groups of rank `> 1`, from which triviality of the center and surjectivity of
-- the inner-automorphism map on `Aut(F)` follow.
theorem center_eq_bot_of_fg_and_rank_gt_one (h_rank : 1 < Group.rank F) :
    Subgroup.center (MulAut F) = ⊥ := sorry

/-- For a finitely generated free group of rank greater than `1`, every automorphism of `Aut(F)`
is inner. -/
theorem innerAutomorphismSubgroup_eq_top_of_fg_and_rank_gt_one
    (h_rank : 1 < Group.rank F) : innerAutomorphismSubgroup (MulAut F) = ⊤ := sorry

/-- Proposition 1-4-4: if `F` is a free group of finite rank greater than `1`, then `Aut(F)` is
complete, meaning that its center is trivial and every automorphism of `Aut(F)` is inner. -/
theorem complete_of_fg_and_rank_gt_one (h_rank : 1 < Group.rank F) :
    Subgroup.center (MulAut F) = ⊥ ∧ innerAutomorphismSubgroup (MulAut F) = ⊤ :=
  ⟨center_eq_bot_of_fg_and_rank_gt_one h_rank,
    innerAutomorphismSubgroup_eq_top_of_fg_and_rank_gt_one h_rank⟩

end MulAut

end

/-! ### Proposition_1_4_5 (from Items/Chap01) -/
universe u

noncomputable section

namespace MulAut

variable (F : Type u) [Group F]

/-- The action of an automorphism of `F` on the quotient by a characteristic subgroup. -/
def quotient (H : Subgroup F) [H.Characteristic] : MulAut F →* MulAut (F ⧸ H) where
  toFun σ :=
    QuotientGroup.congr H H σ (Subgroup.characteristic_iff_map_eq.mp inferInstance σ)
  map_one' := by
    ext ⟨x⟩
    rfl
  map_mul' σ τ := by
    ext ⟨x⟩
    rfl

/-- The natural homomorphism from automorphisms of `F` to automorphisms of its abelianization,
obtained by specializing the canonical quotient-action owner `MulAut.quotient` to the commutator
subgroup. -/
abbrev abelianization : MulAut F →* MulAut (Abelianization F) :=
  quotient F (commutator F)

/-- The subgroup of automorphisms acting trivially on the abelianization of `F`. -/
def IA : Subgroup (MulAut F) :=
  (abelianization F).ker

/-- The subgroup of inner automorphisms of `F`. -/
def innerAutomorphismSubgroup : Subgroup (MulAut F) :=
  (MulAut.conj : F →* MulAut F).range

/-- The subgroup of inner automorphisms is normal in the full automorphism group. -/
instance innerAutomorphismSubgroup_normal : (innerAutomorphismSubgroup F).Normal := by
  change ((MulAut.conj : F →* MulAut F).range).Normal
  refine ⟨?_⟩
  intro n hn σ
  rcases hn with ⟨a, rfl⟩
  exact ⟨σ a, by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  ⟩

end MulAut

macro "JA(" F:term ")" : term => `(MulAut.innerAutomorphismSubgroup $F)

section

variable {F : Type u} [Group F] [IsFreeGroup F] [Group.FG F]

/-- Proposition 1-4-5: for a finitely generated free group `F`, the natural map from `Aut(F)` to
the automorphism group of its abelianization is surjective. -/
-- Layer triage:
-- `source-facing`: the natural map from `MulAut F` to `MulAut (Abelianization F)`.
-- `core/canonical`: the quotient-action owner `MulAut.quotient F H`, whose specialization to
-- `H = commutator F` is definitionally the abelianization action; pointwise this is the induced
-- automorphism `σ.abelianizationCongr` on `Abelianization F`.
-- `bridge/view`: `MulAut.abelianization F` is just the source-facing abbreviation for that
-- specialization, while `MulAut.quotient F H` remains the broader owner for later
-- lower-central-series quotients. The textbook quotient `\overline{F}` is the canonical
-- abelianization `Abelianization F`, and `lowerCentralSeries_one` identifies it with the first
-- lower-central-series quotient.
-- Domain sampling:
-- 1. `MulAut.quotient F H` is the chapter owner action on quotients by characteristic subgroups.
-- 2. `MulEquiv.abelianizationCongr` in mathlib is the pointwise owner for the induced
--    automorphism on abelianizations.
-- 3. `QuotientGroup.congr` is the canonical equivalence induced on quotient groups by an
--    automorphism preserving the distinguished subgroup.
-- 4. `Subgroup.characteristic_iff_map_eq` is the owner criterion turning characteristicity into
--    the equality needed by `QuotientGroup.congr`.
-- 5. `lowerCentralSeries_one` identifies the first lower-central-series quotient with the
--    canonical abelianization.
-- 6. `[Group.FG F]` is the chapter's canonical finite-rank owner assumption for free groups.
-- Primitive vs. derived:
-- the primitive owner datum for the public action is the quotient owner `MulAut.quotient F H`;
-- its commutator specialization is the source-facing abbreviation `MulAut.abelianization F`,
-- used for kernel and surjectivity statements, while the subgroup of inner automorphisms is used
-- downstream through the owner declaration `MulAut.innerAutomorphismSubgroup F`. Pointwise the
-- action is still the canonical automorphism `σ.abelianizationCongr`. The textbook notation
-- `JA(F)` is rendered in later source-facing statements by this canonical inner-automorphism
-- owner rather than by a second subgroup declaration. The
-- representative quotient formulas are already supplied upstream by `QuotientGroup.congr_mk'`,
-- so this file keeps no parallel local wrapper lemmas for them.
-- Proof sketch: choose a finite free basis of `F` and identify `Abelianization F` with the free
-- abelian group on that basis. Elementary Nielsen automorphisms lift the standard generators of
-- the automorphism group of the free abelian group, so every automorphism of `Abelianization F`
-- comes from an automorphism of `F`.
theorem abelianization_surjective_of_fg :
    Function.Surjective (MulAut.abelianization F) := sorry

end

/-! ### Proposition_1_4_6 (from Items/Chap01) -/
universe u

noncomputable section

variable {F : Type u} [Group F] [IsFreeGroup F]

-- Primary domain: automorphisms of a rank-two free group and the induced action on its
-- abelianization.
-- Domain sampling:
-- 1. `MulAut F` is the canonical owner abstraction for `Aut(F)`.
-- 2. `MulAut.abelianization F` from Proposition `1-4-5` is the owner map to the automorphism
--    group of the abelianization.
-- 3. `MulAut.IA F` and `MulAut.innerAutomorphismSubgroup F` are the chapter owner subgroups for
--    the kernel and the inner automorphisms.
-- 4. `Group.rank` from `Mathlib/GroupTheory/Rank` is the intrinsic chapter owner for the source
--    phrase “free group of rank `2`”, while `FreeGroupBasis (Fin 2) F` is only auxiliary proof
--    data used to compare the abelianization with `GL (Fin 2) ℤ`.
-- Layer triage:
-- `source-facing`: the intrinsic rank-two hypothesis `Group.rank F = 2` and the textbook
-- statement that the kernel of the abelianization action equals the subgroup of inner
-- automorphisms.
-- `core/canonical`: `MulAut.abelianization F`, `MulAut.IA F`,
-- `MulAut.innerAutomorphismSubgroup F`, and the owner invariant `Group.rank`.
-- `bridge/view`: a chosen basis `basis : FreeGroupBasis (Fin 2) F` is internal bridge data used
-- to identify the abelianization with the free abelian group on `Fin 2`.
-- Primitive vs. derived:
-- the source-facing primitive datum is the rank hypothesis `Group.rank F = 2`; any chosen
-- `FreeGroupBasis (Fin 2) F` realizing that rank is derived bridge data and should not appear in
-- the public API.

/-- Core/canonical rank-two form of Proposition 1-4-6, expressed relative to a chosen basis so the
abelianization action can later be identified with `GL (Fin 2) ℤ`. -/
-- Proof sketch: use `basis` to identify `Abelianization F` with the free abelian group on
-- `Fin 2`. Proposition `1-4-5` gives surjectivity of `MulAut.abelianization F`, and Nielsen's
-- rank-two computation shows that its kernel is exactly the subgroup of inner automorphisms.
private theorem ia_eq_inner_of_basis (basis : FreeGroupBasis (Fin 2) F) :
    MulAut.IA F = MulAut.innerAutomorphismSubgroup F := sorry

section

variable [Group.FG F]

private theorem rank_freeGroup_eq_nat_card (α : Type u) [Finite α] :
    Group.rank (FreeGroup α) = Nat.card α := by
  letI : Fintype α := Fintype.ofFinite α
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq (FreeGroup α) := Classical.decEq _
  let basis : FreeGroupBasis α (FreeGroup α) := .ofFreeGroup α
  have hle : Group.rank (FreeGroup α) ≤ Fintype.card α := by
    calc
      Group.rank (FreeGroup α) ≤ (Finset.univ.image basis).card :=
        Group.rank_le <| by
          have hset :
              ((Finset.univ.image basis : Finset (FreeGroup α)) : Set (FreeGroup α)) =
                Set.range basis := by
            ext x
            simp
          have hrange : Set.range basis = Set.range (FreeGroup.of : α → FreeGroup α) := by
            ext x
            simp [basis]
          rw [hset]
          rw [hrange]
          exact FreeGroup.closure_range_of α
      _ = Fintype.card α := by
        rw [Finset.card_image_of_injOn]
        · simp
        · exact basis.injective.injOn
  have hge : Fintype.card α ≤ Group.rank (FreeGroup α) := by
    obtain ⟨S, hS, hgenS⟩ := Group.rank_spec (FreeGroup α)
    exact hS ▸ fintype_card_le_card_of_generating_finset basis S hgenS
  rw [Nat.card_eq_fintype_card]
  exact le_antisymm hle hge

private theorem rank_eq_nat_card_generators :
    Group.rank F = Nat.card (IsFreeGroup.Generators F) := by
  letI : Finite (IsFreeGroup.Generators F) := IsFreeGroup.finite_generators F
  calc
    Group.rank F = Group.rank (FreeGroup (IsFreeGroup.Generators F)) := by
      simpa using Group.rank_congr (IsFreeGroup.toFreeGroup F)
    _ = Nat.card (IsFreeGroup.Generators F) := rank_freeGroup_eq_nat_card (IsFreeGroup.Generators F)

/-- A rank-two finitely generated free group admits a basis indexed by `Fin 2`. This bridge
converts the intrinsic rank statement `Group.rank F = 2` into the basis owner used by the
chapter's basis-dependent automorphism results. -/
private theorem exists_basis_fin_two_of_rank_eq_two (h_rank : Group.rank F = 2) :
    Nonempty (FreeGroupBasis (Fin 2) F) := by
  letI : Finite (IsFreeGroup.Generators F) := IsFreeGroup.finite_generators F
  have hcard : Group.rank F = Nat.card (IsFreeGroup.Generators F) :=
    rank_eq_nat_card_generators
  exact ⟨(IsFreeGroup.basis F).reindex <| Finite.equivFinOfCardEq <| hcard.symm.trans h_rank⟩

/-- Proposition 1-4-6: if `F` is a free group of rank `2`, then the kernel of the natural map
from `Aut(F)` to the automorphism group of its abelianization is the subgroup of inner
automorphisms. Via a basis of `Abelianization F`, the target identifies with `GL(2, ℤ)`. -/
-- Proof sketch: convert the intrinsic rank hypothesis `Group.rank F = 2` to a private chosen
-- basis `FreeGroupBasis (Fin 2) F`, then apply the private bridge theorem
-- `ia_eq_inner_of_basis`.
theorem ia_eq_inner_of_rank_eq_two (h_rank : Group.rank F = 2) :
    MulAut.IA F = MulAut.innerAutomorphismSubgroup F := by
  rcases exists_basis_fin_two_of_rank_eq_two h_rank with ⟨basis⟩
  simpa using ia_eq_inner_of_basis basis

end

end

/-! ### Proposition_1_4_7 (from Items/Chap01) -/
universe u

noncomputable section

section

variable {F : Type u} [Group F] [IsFreeGroup F]

-- Primary domain: finite-order automorphisms and their conjugacy classes in a rank-two free group.
-- Domain sampling:
-- 1. `MulAut F` is the canonical owner abstraction for `Aut(F)`.
-- 2. `IsOfFinOrder α` is mathlib's owner predicate for finite-order automorphisms.
-- 3. `ConjClasses (MulAut F)` together with `ConjClasses.mk` is the owner abstraction for
--    conjugacy classes in `Aut(F)`.
-- 4. `Group.rank` is the intrinsic owner for the source phrase “rank-two free group”, while
--    `FreeGroupBasis (Fin 2) F` with `basis.toGL : MulAut F →* GL (Fin 2) ℤ` is auxiliary proof
--    data used internally for the matrix classification.
-- Layer triage:
-- `source-facing`: finite-order elements of `Aut(F)` and their conjugacy classes in a free group
-- of intrinsic rank `2`.
-- `core/canonical`: `FreeGroupBasis (Fin 2) F`, `Group.rank`, `MulAut F`, `IsOfFinOrder`,
-- `orderOf`, `ConjClasses (MulAut F)`, and `ConjClasses.mk`.
-- `bridge/view`: a chosen basis `basis : FreeGroupBasis (Fin 2) F` obtained from
-- `FreeGroupBasis.nonempty_of_rank_eq_two h_rank` is internal bridge data used to pass to
-- `basis.toGL`; the basis-relative classification lemmas below stay private because the public
-- textbook content is the intrinsic rank-two statement.

/-- Private basis-relative bridge for Proposition 1-4-7. -/
-- Proof sketch: transport the automorphism through `basis.toGL`, classify finite-order elements in
-- `GL (Fin 2) ℤ`, and use `basis.orderOf_toGL_eq` from Corollary `1-4-16` to bring the
-- order statement back to `MulAut F`.
private theorem orderOf_eq_one_or_two_or_three_or_four_of_finite_order_basis
    (basis : FreeGroupBasis (Fin 2) F)
    {α : MulAut F} (hα : IsOfFinOrder α) :
    orderOf α = 1 ∨ orderOf α = 2 ∨ orderOf α = 3 ∨ orderOf α = 4 := sorry

/-- Private basis-relative involution count bridge for Proposition 1-4-7. -/
-- Proof sketch: classify involutions in `GL (Fin 2) ℤ` up to conjugacy, then use the basis bridge
-- to lift those classes back to `Aut(F)`.
private theorem orderTwo_conjClasses_encard_basis (basis : FreeGroupBasis (Fin 2) F) :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 2 }).encard = 4 := sorry

/-- Private basis-relative order-`3` conjugacy-class count bridge for Proposition 1-4-7. -/
-- Proof sketch: classify order-`3` matrices in `GL (Fin 2) ℤ`, then transport the unique
-- conjugacy class back through `basis.toGL`.
private theorem orderThree_conjClasses_encard_basis (basis : FreeGroupBasis (Fin 2) F) :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 3 }).encard = 1 := sorry

/-- Private basis-relative order-`4` conjugacy-class count bridge for Proposition 1-4-7. -/
-- Proof sketch: as in the order-`3` case, classify order-`4` matrices in `GL (Fin 2) ℤ` and
-- transport the unique conjugacy class back through `basis.toGL`.
private theorem orderFour_conjClasses_encard_basis (basis : FreeGroupBasis (Fin 2) F) :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 4 }).encard = 1 := sorry

section

variable [Group.FG F]

variable (h_rank : Group.rank F = 2)

include h_rank

/-- Proposition 1-4-7: in the automorphism group of a rank-two free group, every finite-order
automorphism has order `1`, `2`, `3`, or `4`. -/
-- Proof sketch: use `FreeGroupBasis.nonempty_of_rank_eq_two` to obtain a basis
-- `FreeGroupBasis (Fin 2) F`, then apply the basis-dependent owner theorem above. Its proof uses
-- the canonical bridge `basis.toGL` from Corollary `1-4-16`.
theorem orderOf_eq_one_or_two_or_three_or_four_of_finite_order
    {α : MulAut F} (hα : IsOfFinOrder α) :
    orderOf α = 1 ∨ orderOf α = 2 ∨ orderOf α = 3 ∨ orderOf α = 4 := by
  rcases FreeGroupBasis.nonempty_of_rank_eq_two h_rank with ⟨basis⟩
  simpa using orderOf_eq_one_or_two_or_three_or_four_of_finite_order_basis basis hα

/-- The conjugacy classes in `Aut(F)` represented by involutions of a rank-two free group form a
four-element set. -/
-- Proof sketch: use `FreeGroupBasis.nonempty_of_rank_eq_two` and then apply the
-- basis-dependent count theorem, whose proof uses the canonical bridge `basis.toGL`.
theorem orderTwo_conjClasses_encard :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 2 }).encard = 4 := by
  rcases FreeGroupBasis.nonempty_of_rank_eq_two h_rank with ⟨basis⟩
  simpa using orderTwo_conjClasses_encard_basis basis

/-- The conjugacy classes in `Aut(F)` represented by elements of order `3` in a rank-two free
group form a singleton. -/
-- Proof sketch: use `FreeGroupBasis.nonempty_of_rank_eq_two` and then apply the
-- basis-dependent count theorem, whose proof uses the canonical bridge `basis.toGL`.
theorem orderThree_conjClasses_encard :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 3 }).encard = 1 := by
  rcases FreeGroupBasis.nonempty_of_rank_eq_two h_rank with ⟨basis⟩
  simpa using orderThree_conjClasses_encard_basis basis

/-- The conjugacy classes in `Aut(F)` represented by elements of order `4` in a rank-two free
group form a singleton. -/
-- Proof sketch: use `FreeGroupBasis.nonempty_of_rank_eq_two` and then apply the
-- basis-dependent count theorem, whose proof uses the canonical bridge `basis.toGL`.
theorem orderFour_conjClasses_encard :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 4 }).encard = 1 := by
  rcases FreeGroupBasis.nonempty_of_rank_eq_two h_rank with ⟨basis⟩
  simpa using orderFour_conjClasses_encard_basis basis

omit h_rank

end

end

/-! ### Lemma_1_4_8 (from Items/Chap01) -/
universe u v

noncomputable section

section

variable {F : Type u} [Group F] [IsFreeGroup F]

namespace FreeGroupBasis

/-- Lemma 1-4-8: if `α ∈ IA(F)` and some positive power of `α` is inner, then for every chosen
basis element `basis x` and every lower-central-series term `lowerCentralSeries F n`, there is
some `k` in that term such that `α (basis x)` is conjugate to `(basis x) * k`. -/
-- Layer triage:
-- `source-facing`: a free group `F`, a chosen basis `basis : FreeGroupBasis X F`, an
-- automorphism `α : MulAut F`, a basis element `x : X`, and a lower-central-series index `n`.
-- `core/canonical`: the owner basis object `FreeGroupBasis X F`, the owner homomorphisms
-- `MulAut.abelianization F` and `MulAut.quotient F H`, the lower-central-series owner
-- `lowerCentralSeries F n`, the conjugacy relation `IsConj`, and the inner automorphism owner
-- subgroup `MulAut.innerAutomorphismSubgroup F`.
-- `bridge/view`: the textbook notation `IA(F)` is expressed by `MulAut.IA F`, while the local
-- textbook hypothesis that a power of `α` lies in `JA(F)` is rendered here by the canonical inner
-- automorphism owner `MulAut.innerAutomorphismSubgroup F`.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` in mathlib is the canonical owner abstraction for a chosen free basis.
-- 2. `MulAut.quotient F H` in `Proposition_1_4_5` is the chapter owner action on quotients by a
--    characteristic subgroup.
-- 3. `MulAut.IA F` and `MulAut.innerAutomorphismSubgroup F` are the chapter owner subgroups used
--    for the source-facing `IA(F)` hypothesis and the local inner-power hypothesis.
-- 4. `lowerCentralSeries F n` in mathlib is the canonical descending central series, with each
--    term characteristic.
-- Primitive vs. derived:
-- the primitive data is the chosen basis element and the owner lower-central-series term
-- `lowerCentralSeries F n`; the witness should therefore live in that subgroup itself, while the
-- subgroup conditions are the derived API `MulAut.IA F` and
-- `MulAut.innerAutomorphismSubgroup F`.
-- Proof sketch: induct on `n`. For the induction step, use that `α ∈ IA(F)` makes `α` act
-- trivially on `F_n / F_{n+1}`, while `α ^ N` being inner gives the source-facing `JA(F)`
-- hypothesis used in the Baumslag-Taylor argument. Standard commutator-module structure of
-- `F_n / F_{n+1}` then improves the
-- lower-central-series error term from `F_n` to `F_{n+1}`.
theorem exists_isConj_basisElement_mul_of_mem_IA_of_pow_mem_inner
    {X : Type v} (basis : FreeGroupBasis X F) (α : MulAut F) (x : X) (n : ℕ) {N : ℕ}
    (hN : 0 < N)
    (hIA : α ∈ MulAut.IA F)
    (hInner : α ^ N ∈ JA(F)) :
    ∃ k : lowerCentralSeries F n, IsConj (α (basis x)) (basis x * k) := sorry

end FreeGroupBasis

end

/-! ### Proposition_1_4_9 (from Items/Chap01) -/
universe u

section

open QuotientGroup

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-4-9: if `u` and `v` are not conjugate in a free group `F`, then for every
prime `p` there is a finite `p`-group quotient of `F` in which the images of `u` and `v` are still
not conjugate. This is the quotient-owner form of the textbook surjective statement, recovered
canonically from the quotient-by-kernel presentation of a surjective homomorphism. -/
-- Layer triage:
-- `source-facing`: the ambient free group `F`, the two elements `u` and `v`, and a prime `p`.
-- `core/canonical`: the bundled owner `N : FiniteIndexNormalSubgroup F`, its underlying subgroup
-- `N.toSubgroup`, the quotient owner `F ⧸ N.toSubgroup`, the quotient-side coercions
-- `u : F ⧸ N.toSubgroup` and `v : F ⧸ N.toSubgroup`, and the quotient-side predicates
-- `IsPGroup p (F ⧸ N.toSubgroup)` and `IsConj`.
-- `bridge/view`: the textbook phrase “a surjective homomorphism onto a finite `p`-group” is the
-- quotient-by-kernel view of the owner datum `N.toSubgroup`, via
-- `QuotientGroup.quotientKerEquivOfSurjective`.
-- Domain sampling:
-- 1. `FiniteIndexNormalSubgroup` is the owner abstraction for normal subgroups of finite index.
-- 2. The quotient coercion `F → F ⧸ N.toSubgroup` is the canonical image map attached to a normal
--    subgroup.
-- 3. `QuotientGroup.quotientKerEquivOfSurjective` is the first-isomorphism owner bridge from an
--    arbitrary surjective homomorphism to its kernel quotient.
-- 4. `MonoidHom.map_isConj` is the canonical transport of conjugacy along homomorphisms.
-- 5. `IsPGroup.of_equiv` is the canonical way to move the `p`-group structure across the quotient
--    isomorphism induced by a surjection.
-- Primitive vs. derived:
-- the intrinsic primitive data is the finite-index normal subgroup owner `N`;
-- the quotient group, its quotient map, its `p`-group structure, and the source-facing surjective
-- homomorphism are derived API.
-- Proof sketch: argue by induction on the total reduced-word length after transporting `F` to its
-- canonical free-group model. If the images of `u` and `v` already differ in the abelianization,
-- reduce modulo a large `p`-power to separate them in a finite abelian `p`-group. Otherwise use
-- the Baumslag-Taylor reduction to pass to shorter nonconjugate words inside a suitable subgroup,
-- apply the induction hypothesis there, and then compose with the relevant finite `p`-group
-- quotient map back from `F`.
theorem exists_finite_pGroup_quotient_separating_nonconjugate
    (p : ℕ) [Fact p.Prime] (u v : F) (huv : ¬ IsConj u v) :
    ∃ N : FiniteIndexNormalSubgroup F,
      IsPGroup p (F ⧸ N.toSubgroup) ∧
        ¬ IsConj (u : F ⧸ N.toSubgroup) (v : F ⧸ N.toSubgroup) := sorry

end

/-! ### Proposition_1_4_10 (from Items/Chap01) -/
universe u

section

open QuotientGroup

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-4-10: if `u` and `v` are not conjugate in the free group `F`, then for some
index `n` their images in the quotient by the `n`th term of the lower central series are not
conjugate. -/
-- Layer triage:
-- this item is a `bridge/view` theorem: it keeps the textbook lower-central-series quotient
-- `F / F_n`, but its proof should pass through the quotient-owner theorem from Proposition 1-4-9.
-- `source-facing`: the free group `F`, elements `u v : F`, and the lower-central-series index
-- `n`.
-- `core/canonical`: `lowerCentralSeries F n`, the quotient map
-- `mk' (lowerCentralSeries F n) : F →* F ⧸ lowerCentralSeries F n`, and the quotient conjugacy
-- relation `IsConj`.
-- Domain sampling:
-- 1. `lowerCentralSeries F` in mathlib is the owner descending central series.
-- 2. `mk'` is the canonical quotient map attached to a normal subgroup, and the quotient-side
--    coercion `u : F ⧸ lowerCentralSeries F n` is its owner-derived view.
-- 3. `MonoidHom.map_isConj` is the owner transport for conjugacy along the factor map
--    `F ⧸ lowerCentralSeries F n →* F ⧸ N`.
-- 4. `IsPGroup.isNilpotent` and `nilpotent_iff_lowerCentralSeries` are the owner bridge from the
--    finite `p`-group quotient in Proposition 1-4-9 to a vanishing lower-central-series stage.
-- Primitive vs. derived:
-- the primitive datum is the canonical owner subgroup `lowerCentralSeries F n`; the quotient type
-- `F ⧸ lowerCentralSeries F n` and the induced quotient image `u : F ⧸ lowerCentralSeries F n`
-- are derived from it.
-- Proof sketch: apply Proposition 1-4-9 in its quotient-owner form to obtain a finite-index
-- normal subgroup owner `N` such that `F ⧸ N.toSubgroup` is a finite `p`-group and the images of
-- `u` and `v` in `F ⧸ N.toSubgroup` are not conjugate. Since finite `p`-groups are nilpotent,
-- some lower central term of `F ⧸ N.toSubgroup` is trivial; functoriality of the lower central
-- series for the canonical quotient map then shows `lowerCentralSeries F n ≤ N.toSubgroup`, so
-- the quotient map `F →* F ⧸ N.toSubgroup` factors through
-- `F ⧸ lowerCentralSeries F n`. If the images of `u` and `v` were conjugate in that lower-central
-- quotient, their further images in `F ⧸ N.toSubgroup` would also be conjugate.
theorem exists_lowerCentralSeries_quotient_separating_nonconjugate
    (u v : F) (huv : ¬ IsConj u v) :
    ∃ n : ℕ,
      ¬ IsConj ((u : F ⧸ lowerCentralSeries F n)) (v : F ⧸ lowerCentralSeries F n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNpq, huvN⟩ :=
    exists_finite_pGroup_quotient_separating_nonconjugate 2 u v huv
  letI : Group.IsNilpotent (F ⧸ N.toSubgroup) := hNpq.isNilpotent
  let n : ℕ := Group.nilpotencyClass (F ⧸ N.toSubgroup)
  have hle : lowerCentralSeries F n ≤ N.toSubgroup := by
    rw [← ker_mk' N.toSubgroup]
    exact (Subgroup.map_eq_bot_iff _).mp <| by
      apply eq_bot_iff.mpr
      calc
        Subgroup.map (mk' N.toSubgroup) (lowerCentralSeries F n) ≤
            lowerCentralSeries (F ⧸ N.toSubgroup) n :=
          lowerCentralSeries.map _ n
        _ = ⊥ := by
          dsimp [n]
          simp [lowerCentralSeries_nilpotencyClass]
  refine ⟨n, ?_⟩
  intro huvLower
  exact huvN <| by
    simpa using
      (QuotientGroup.map (lowerCentralSeries F n) N.toSubgroup (.id F) hle).map_isConj huvLower

end

/-! ### Lemma_1_4_11 (from Items/Chap01) -/
universe u v

section

open QuotientGroup

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Lemma 1-4-11: if `α ∈ IA(F)` and some positive power of `α` is inner, then `α` sends every
chosen basis element of `F` to a conjugate of itself. -/
-- Layer triage:
-- `source-facing`: a free group `F`, a chosen basis `basis : FreeGroupBasis X F`, an
-- automorphism `α : MulAut F`, and a basis element `x : X`.
-- `core/canonical`: the owner homomorphisms `MulAut.abelianization F` and
-- `MulAut.quotient F H`, the lower-central-series owner `lowerCentralSeries F`, the chosen
-- free-basis object `FreeGroupBasis X F`, the conjugacy relation `IsConj`, and the inner
-- automorphism owner subgroup `MulAut.innerAutomorphismSubgroup F`.
-- `bridge/view`: the textbook notation `IA(F)` is expressed by `MulAut.IA F`, while the local
-- inner-power hypothesis is rendered by `MulAut.innerAutomorphismSubgroup F`.
-- Domain sampling:
-- 1. `MulAut.IA F` and `MulAut.innerAutomorphismSubgroup F` in `Proposition_1_4_5` are the owner
--    subgroup declarations used in the surrounding section.
-- 2. `MulAut.quotient F H` in `Proposition_1_4_5` is the owner action on quotients by
--    characteristic subgroups.
-- 3. `lowerCentralSeries F n` in mathlib is the canonical lower-central-series owner, with each
--    term characteristic.
-- 4. `MonoidHom.map_isConj` in mathlib is the owner transport of conjugacy along quotient maps.
-- Primitive vs. derived:
-- the primitive data is the owner action `MulAut.quotient F H` on a quotient by a characteristic
-- subgroup `H`; the lower-central-series specialization and the subgroup conditions
-- `MulAut.IA F` and `MulAut.innerAutomorphismSubgroup F` are derived API.
-- Proof sketch: apply Lemma `1-4-8` to see that for every `n`, the element `α (basis x)` is
-- conjugate to `(basis x) * k` with `k ∈ lowerCentralSeries F n`. If `α (basis x)` were not
-- conjugate to `basis x`, Proposition `1-4-10` would separate their conjugacy classes in some
-- quotient `F ⧸ lowerCentralSeries F n`, contradicting the previous sentence because `k` dies in
-- that quotient.
theorem isConj_basisElement_of_mem_IA_of_pow_mem_inner
    {X : Type v} (basis : FreeGroupBasis X F) (α : MulAut F) (x : X) {N : ℕ}
    (hN : 0 < N)
    (hIA : α ∈ MulAut.IA F)
    (hInner : α ^ N ∈ JA(F)) :
    IsConj (α (basis x)) (basis x) := by
  by_contra hconj
  obtain ⟨n, hn⟩ :=
    exists_lowerCentralSeries_quotient_separating_nonconjugate (α (basis x)) (basis x) hconj
  obtain ⟨k, hkconj⟩ :=
    basis.exists_isConj_basisElement_mul_of_mem_IA_of_pow_mem_inner α x n hN hIA hInner
  exact hn <| by
    simpa [k.2] using (mk' (lowerCentralSeries F n)).map_isConj hkconj

end

/-! ### Proposition_1_4_12 (from Items/Chap01) -/
universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-4-12: for a free group `F`, if an automorphism `α` acts trivially on the
abelianization and some positive power of `α` is inner, then `α` is inner. Here the textbook
notation `JA(F)` is expressed by the canonical subgroup
`MulAut.innerAutomorphismSubgroup F`. -/
-- Layer triage:
-- `source-facing`: the free group `F`, an automorphism `α : MulAut F`, the IA-subgroup
-- condition, and the textbook conclusion that `α` lies in `JA(F)`, which in this proposition is
-- the subgroup of inner automorphisms.
-- `core/canonical`: `MulAut F`, the canonical IA-subgroup `MulAut.IA F`, the intrinsic primitive
-- element predicate `IsPrimitiveElement`, and the canonical inner automorphism subgroup
-- `MulAut.innerAutomorphismSubgroup F`.
-- `bridge/view`: Lemma `1-4-11` gives the basis-level conjugacy statement, while the textbook
-- symbol `JA(F)` is rendered by the chapter's owner declaration
-- `MulAut.innerAutomorphismSubgroup F`.
-- Domain sampling:
-- 1. `MulAut.IA F` in `Proposition_1_4_5` is the project's canonical subgroup of automorphisms
--    acting trivially on the abelianization.
-- 2. `MulAut.conj : F →* MulAut F` in mathlib is the canonical inner-automorphism map.
-- 3. `IsPrimitiveElement` in `CombinatorialGroupTheory_Magnus_2004.Basic` is the project's intrinsic owner
--    for elements belonging to some free basis.
-- 4. `MulAut.innerAutomorphismSubgroup F` is the chapter owner abstraction for the subgroup of
--    inner automorphisms.
-- Primitive vs. derived:
-- the primitive public inputs are only `α`, the positive integer `N : ℕ+`, and the membership
-- hypotheses in `MulAut.IA F` and the inner-automorphism subgroup; no chosen basis or rank data
-- belongs in the statement header.
-- Proof sketch: first upgrade Lemma `1-4-11` from basis elements to the intrinsic primitive
-- elements of `F`. The Baumslag-Taylor argument then compares primitive pairs to show that all of
-- these conjugacies are realized by one common group element, so `α` itself is conjugation by
-- that element.
private theorem isConj_primitive_of_mem_IA_of_pow_mem_inner
    (α : MulAut F) (N : ℕ+) {p : F} (hp : IsPrimitiveElement p)
    (hIA : α ∈ MulAut.IA F)
    (hInner : α ^ (N : ℕ) ∈ JA(F)) :
    IsConj (α p) p := by
  rcases hp with ⟨X, basis, x, rfl⟩
  simpa using isConj_basisElement_of_mem_IA_of_pow_mem_inner basis α x N.2 hIA hInner

private theorem mem_inner_of_maps_primitive_to_conjugates
    (α : MulAut F)
    (hprimitive : ∀ {p : F}, IsPrimitiveElement p → IsConj (α p) p) :
    α ∈ JA(F) := by
  sorry

theorem mem_inner_of_mem_IA_of_pow_mem_inner
    (α : MulAut F) (N : ℕ+)
    (hIA : α ∈ MulAut.IA F)
    (hInner : α ^ (N : ℕ) ∈ JA(F)) :
    α ∈ JA(F) := by
  refine mem_inner_of_maps_primitive_to_conjugates α fun hp ↦ ?_
  exact isConj_primitive_of_mem_IA_of_pow_mem_inner α N hp hIA hInner

end

/-! ### Corollary_1_4_13 (from Items/Chap01) -/
universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Corollary 1-4-13: for a free group `F`, the quotient of `IA(F)` by its inner automorphism
subgroup is torsion free. -/
-- Layer triage:
-- `source-facing`: the IA-subgroup `MulAut.IA F` of automorphisms acting trivially on the
-- abelianization, together with the quotient by inner automorphisms.
-- `core/canonical`: `MulAut.IA F`, the inner automorphism owner subgroup
-- `MulAut.innerAutomorphismSubgroup F`, the subgroup-in-subgroup construction
-- `Subgroup.subgroupOf`, and the torsion-free predicate `IsMulTorsionFree`.
-- `bridge/view`: the textbook quotient `IA(F) / JA(F)` is rendered as the quotient of the subgroup
-- `MulAut.IA F` by the inner automorphism subgroup viewed inside it via `Subgroup.subgroupOf`.
-- Domain sampling:
-- 1. `MulAut.IA F` from Proposition `1-4-5` is the project owner abstraction for automorphisms
--    acting trivially on the abelianization.
-- 2. `MulAut.innerAutomorphismSubgroup F` is the chapter owner abstraction for the subgroup of
--    inner automorphisms of `F`.
-- 3. `Subgroup.subgroupOf` is mathlib's owner API for viewing that subgroup inside `MulAut.IA F`.
-- 4. `IsMulTorsionFree` is the canonical torsion-free predicate on the resulting quotient group.
-- Primitive vs. derived:
-- the primitive public datum is only the ambient free group `F`; the subgroup quotient is the
-- canonical derived object attached to the IA-subgroup and the inner automorphism subgroup.
-- Proof sketch: let `q` be a finite-order element of the quotient and choose `α ∈ IA(F)`
-- representing it. Some positive power `α ^ N` lies in the inner automorphism subgroup, so
-- Proposition `1-4-12` implies that `α` itself is inner. Therefore `q` is trivial, and the
-- quotient is torsion free.
theorem ia_quotient_inner_isMulTorsionFree :
    IsMulTorsionFree
      (MulAut.IA F ⧸ (JA(F)).subgroupOf (MulAut.IA F)) :=
  sorry

end

/-! ### Corollary_1_4_14 (from Items/Chap01) -/
universe u

noncomputable section

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/- Corollary 1-4-14: if `F` is a free group, then the IA-subgroup `IA(F)` of `Aut(F)` is torsion
free. -/
-- Layer triage:
-- `source-facing`: the textbook subgroup `IA(F)` of automorphisms acting trivially on the
-- abelianization, together with the assertion that this group has no nontrivial finite-order
-- elements.
-- `core/canonical`: the subgroup `MulAut.IA F` and the finite-order predicate `IsOfFinOrder`.
-- `bridge/view`: Corollary `1-4-13` supplies the canonical quotient-owner statement that
-- `IA(F) / JA(F)` is torsion free, while the inner automorphism subgroup is the owner declaration
-- `MulAut.innerAutomorphismSubgroup F`.
-- Domain sampling:
-- 1. `MulAut.IA F` from Proposition `1-4-5` is the owner object for the subgroup `IA(F)`.
-- 2. `MulAut.innerAutomorphismSubgroup F` is the canonical subgroup of inner automorphisms used
--    in Corollary `1-4-13`.
-- 3. `IsOfFinOrder` is mathlib's canonical predicate for finite-order elements.
-- 4. `normalizer_zpowers_isCyclic` is the chapter owner theorem detecting when a nontrivial
--    central element would force the ambient free group to be cyclic.
-- Primitive vs. derived:
-- the only primitive datum is the free group `F`; the subgroup `MulAut.IA F` is the canonical
-- derived object attached to the abelianization action, and no basis or rank choice belongs in
-- the public header.
-- Proof sketch: first show privately that the inner automorphism subgroup is torsion free. If `F`
-- were cyclic, that subgroup would be trivial; otherwise any element in the kernel of
-- `MulAut.conj` would be a nontrivial central element, and Proposition `1-2-21` would force `F`
-- to be cyclic, a contradiction. Hence `MulAut.conj` is injective and its range inherits
-- torsion-freeness from `F`. For a finite-order element of `IA(F)`, Corollary `1-4-13` makes its
-- image in `IA(F) / JA(F)` trivial, so the element lies in the inner automorphism subgroup; the
-- private torsion-freeness result then forces the element itself to be trivial.
private theorem conj_eq_one_implies_eq_one_of_not_isCyclic
    (hnotcyc : ¬ IsCyclic F) {x : F} (hconj : MulAut.conj x = 1) : x = 1 := by
  by_contra hx
  have hx_center : x ∈ Subgroup.center F := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : x * y * x⁻¹ = y := by
      simpa [MulAut.conj_apply] using congrArg (fun σ : MulAut F ↦ σ y) hconj
    have hxy : x * y = y * x := by
      calc
        x * y = (x * y * x⁻¹) * x := by simp [mul_assoc]
        _ = y * x := by rw [hy]
    exact hxy.symm
  have hnormal : (Subgroup.zpowers x : Subgroup F).Normal := by
    refine ⟨?_⟩
    intro a ha b
    rcases Subgroup.mem_zpowers_iff.mp ha with ⟨n, rfl⟩
    have hbx : Commute b x := by
      exact (commute_iff_eq b x).2 (Subgroup.mem_center_iff.mp hx_center b)
    have hbxn : Commute b (x ^ n) := hbx.zpow_right n
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    simp [mul_assoc, hbxn.eq]
  let H : Subgroup F := Subgroup.zpowers x
  have hnormalizer_top : Subgroup.normalizer (Subgroup.zpowers x : Set F) = ⊤ := by
    letI : H.Normal := by
      simpa [H] using hnormal
    have htop : Subgroup.normalizer (H : Set F) = ⊤ := Subgroup.normalizer_eq_top H
    simpa [H] using htop
  have hcyc_top : IsCyclic (⊤ : Subgroup F) := by
    have hcyc_normalizer : IsCyclic ↥(Subgroup.normalizer (Subgroup.zpowers x : Set F)) :=
      normalizer_zpowers_isCyclic x hx
    rwa [hnormalizer_top] at hcyc_normalizer
  have hcyc : IsCyclic F :=
    isCyclic_of_surjective (⊤ : Subgroup F).subtype <| fun y ↦ ⟨⟨y, by simp⟩, rfl⟩
  exact hnotcyc hcyc

private instance innerAutomorphismSubgroup_isMulTorsionFree :
    IsMulTorsionFree (JA(F)) := by
  by_cases hcyc : IsCyclic F
  · letI : IsCyclic F := hcyc
    letI : Std.Commutative (· * · : F → F → F) := IsCyclic.commutative
    letI : Subsingleton ↥(JA(F)) := by
      refine ⟨fun α β ↦ ?_⟩
      apply Subtype.ext
      have hα : α.1 = 1 := by
        rcases α.2 with ⟨a, ha⟩
        calc
          α.1 = MulAut.conj a := ha.symm
          _ = 1 := by
            ext x
            calc
              (MulAut.conj a) x = a * (x * a⁻¹) := by
                simp [MulAut.conj_apply, mul_assoc]
              _ = (a * a⁻¹) * x := by ac_rfl
              _ = x := by simp
              _ = (1 : MulAut F) x := by rfl
      have hβ : β.1 = 1 := by
        rcases β.2 with ⟨b, hb⟩
        calc
          β.1 = MulAut.conj b := hb.symm
          _ = 1 := by
            ext x
            calc
              (MulAut.conj b) x = b * (x * b⁻¹) := by
                simp [MulAut.conj_apply, mul_assoc]
              _ = (b * b⁻¹) * x := by ac_rfl
              _ = x := by simp
              _ = (1 : MulAut F) x := by rfl
      exact hα.trans hβ.symm
    infer_instance
  · let e : F ≃* JA(F) :=
        MulEquiv.ofBijective
          ((MulAut.conj : F →* MulAut F).rangeRestrict)
          ⟨by
              intro g h hgh
              have hconj : MulAut.conj g = MulAut.conj h := congrArg Subtype.val hgh
              have hdiv : MulAut.conj (g * h⁻¹) = 1 := by
                calc
                  MulAut.conj (g * h⁻¹) = MulAut.conj g * (MulAut.conj h)⁻¹ := by simp
                  _ = 1 := by rw [hconj]; simp
              have hEq : g * h⁻¹ = 1 := conj_eq_one_implies_eq_one_of_not_isCyclic hcyc hdiv
              exact eq_of_mul_inv_eq_one hEq,
            (MulAut.conj : F →* MulAut F).rangeRestrict_surjective⟩
    exact Function.Injective.isMulTorsionFree e.symm.toMonoidHom e.symm.injective

private theorem ia_eq_one_of_isOfFinOrder_aux {α : MulAut.IA F} (hα_fin : IsOfFinOrder α) :
    α = 1 := by
  by_contra hα_ne
  let G := MulAut.IA F
  let N : Subgroup G :=
    (JA(F)).subgroupOf G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  letI : IsMulTorsionFree (G ⧸ N) := by
    simpa [N] using ia_quotient_inner_isMulTorsionFree
  have hq_eq : q α = 1 := IsOfFinOrder.eq_one' (q.isOfFinOrder hα_fin)
  have hN : α ∈ N := (QuotientGroup.eq_one_iff α).mp hq_eq
  let β : JA(F) := ⟨α.1, hN⟩
  have hβ_fin : IsOfFinOrder β := by
    rw [isOfFinOrder_iff_pow_eq_one] at hα_fin ⊢
    obtain ⟨n, hn, hpow⟩ := hα_fin
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val hpow
  have hβ_eq : β = 1 := IsOfFinOrder.eq_one' hβ_fin
  have hβ_val : α.1 = 1 := by
    simpa [β] using congrArg Subtype.val hβ_eq
  apply hα_ne
  apply Subtype.ext
  exact hβ_val

/-- Corollary 1-4-14: if `F` is a free group, then `IA(F)` is torsion free. -/
theorem ia_isMulTorsionFree : IsMulTorsionFree (MulAut.IA F) := by
  sorry

end

/-! ### Corollary_1_4_15 (from Items/Chap01) -/
universe u

noncomputable section

open LinearMap

section

variable {F : Type u} [Group F]
variable {n : ℕ}

-- Layer triage for Corollary 1-4-15:
-- `source-facing`: a basis `basis : FreeGroupBasis (Fin n) F` and a finite subgroup
-- `G ≤ MulAut F`.
-- `core/canonical`: the restricted homomorphism `basis.toGL.restrict G` and mathlib's owner
-- equivalence `MonoidHom.ofInjective` from an injective homomorphism to its range.
-- `bridge/view`: `FreeGroupBasis.toGL` from Corollary `1-4-16`.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.toGL` is the chapter owner map from `MulAut F` to `GL (Fin n) ℤ`.
-- 2. `Subgroup.orderOf_coe` is the canonical comparison between element orders in a subgroup and
--    in the ambient group.
-- 3. `MonoidHom.ofInjective` is the owner equivalence from a group to the range of an injective
--    homomorphism, with owner companion lemma `MonoidHom.ofInjective_apply`.
--
-- Primitive vs. derived:
-- the primitive source data are the chosen basis and the finite subgroup `G`; injectivity of the
-- restricted representation is the substantive theorem, while the isomorphism onto the image is
-- derived canonically from `MonoidHom.ofInjective`.

/-- The restriction of the canonical abelianization representation of `Aut(F)` to a finite
subgroup is injective. -/
-- Proof sketch: if `φ : G` maps to the identity matrix, then its underlying automorphism of `F`
-- acts trivially on the abelianization. Because `G` is finite, `φ` has finite order, so the
-- kernel-torsion theorem from Corollary `1-4-16` forces `φ = 1`.
theorem toGL_restrict_injective_of_finite_subgroup
    (basis : FreeGroupBasis (Fin n) F) (G : Subgroup (MulAut F)) [Finite G] :
    Function.Injective (basis.toGL.restrict G) := by
  intro φ ψ hφψ
  let δ : G := φ * ψ⁻¹
  have hδ_toGL : basis.toGL (δ : MulAut F) = 1 := by
    simpa [δ, MonoidHom.map_mul] using
      congrArg (fun g : GL (Fin n) ℤ ↦ g * (basis.toGL ψ)⁻¹) hφψ
  have hδ_fin : IsOfFinOrder δ := isTorsion_of_finite δ
  have hδ_fin' : IsOfFinOrder (δ : MulAut F) := by
    rw [← orderOf_pos_iff, Subgroup.orderOf_coe, orderOf_pos_iff]
    exact hδ_fin
  have hδ_order :
      orderOf (basis.toGL (δ : MulAut F)) = orderOf (δ : MulAut F) :=
    basis.orderOf_toGL_eq (δ : MulAut F) hδ_fin'
  have hδ_eq_one : (δ : MulAut F) = 1 := by
    rw [← orderOf_eq_one_iff, ← hδ_order]
    simp [hδ_toGL]
  exact Subtype.ext <| eq_of_mul_inv_eq_one <| by simpa [δ] using hδ_eq_one

/- Corollary 1-4-15: after choosing a rank-`n` basis of the free group `F`, the natural map from
`Aut(F)` to `GL (Fin n) ℤ` carries each finite subgroup of `Aut(F)` isomorphically onto its image
subgroup of `GL (Fin n) ℤ`, via the canonical owner equivalence
`MonoidHom.ofInjective (toGL_restrict_injective_of_finite_subgroup basis G)`. -/
#check
  (fun (basis : FreeGroupBasis (Fin n) F) (G : Subgroup (MulAut F)) [Finite G] ↦
    (MonoidHom.ofInjective (toGL_restrict_injective_of_finite_subgroup basis G) :
      G ≃* (basis.toGL.restrict G).range))

end

/-! ### Corollary_1_4_16 (from Items/Chap01) -/
universe u

noncomputable section

section

open LinearMap.GeneralLinearGroup Matrix.GeneralLinearGroup MulEquiv

variable {F : Type u} [Group F]
variable {n N : ℕ}

namespace FreeGroupBasis

/-- The canonical equivalence from automorphisms of `Abelianization F` to `GL (Fin n) ℤ`,
obtained by passing through additive automorphisms and then expressing the induced `ℤ`-linear
automorphism in the standard basis of the free abelian group of rank `n`. -/
private noncomputable def abelianizationToGL (basis : FreeGroupBasis (Fin n) F) :
    MulAut (Abelianization F) ≃* GL (Fin n) ℤ :=
  let addAutToGL :
      AddAut (Additive (Abelianization F)) ≃*
        LinearMap.GeneralLinearGroup ℤ (Additive (Abelianization F)) :=
    ({ toFun := fun φ ↦ φ.toIntLinearEquiv
       invFun := fun ψ ↦ ψ.toAddEquiv
       left_inv := by
         intro φ
         ext a
         rfl
       right_inv := by
         intro ψ
         ext a
         rfl
       map_mul' := by
         intro φ ψ
         ext a
         rfl } : AddAut (Additive (Abelianization F)) ≃*
         (Additive (Abelianization F) ≃ₗ[ℤ] Additive (Abelianization F))).trans
      (generalLinearEquiv ℤ (Additive (Abelianization F))).symm
  let reprAbAdd : Additive (Abelianization F) ≃+ FreeAbelianGroup (Fin n) :=
    toAdditive <| basis.repr.abelianizationCongr
  let reprAb : Additive (Abelianization F) ≃ₗ[ℤ] FreeAbelianGroup (Fin n) :=
    reprAbAdd.toIntLinearEquiv
  (AddAutAdditive (Abelianization F)).symm.trans
    (addAutToGL.trans <| (congrLinearEquiv reprAb).trans <|
      (toLin' (FreeAbelianGroup.basis (Fin n))).symm)

/-- The source-facing bridge from automorphisms of a free group of rank `n` to `GL (Fin n) ℤ`,
factored through the canonical owner map on abelianizations. -/
noncomputable def toGL (basis : FreeGroupBasis (Fin n) F) : MulAut F →* GL (Fin n) ℤ :=
  let abelianizationToGL := basis.abelianizationToGL
  abelianizationToGL.toMonoidHom.comp (MulAut.abelianization F)

/-- The canonical matrix attached to a finite-order automorphism of a rank-`n` free group has the
same order as the automorphism itself. -/
theorem orderOf_toGL_eq
    (basis : FreeGroupBasis (Fin n) F) (φ : MulAut F) (hφ : IsOfFinOrder φ) :
    orderOf (basis.toGL φ) = orderOf φ := by
  letI : IsFreeGroup F := basis.isFreeGroup
  let abelianizationToGL := basis.abelianizationToGL
  rw [orderOf_eq_orderOf_iff]
  intro k
  constructor
  · intro hk
    have hgl : basis.toGL (φ ^ k) = 1 := by
      simpa [MonoidHom.map_pow] using hk
    have hab : MulAut.abelianization F (φ ^ k) = 1 := by
      apply abelianizationToGL.injective
      simpa [toGL] using hgl
    have hIA : φ ^ k ∈ MulAut.IA F := hab
    let ψ : MulAut.IA F := ⟨φ ^ k, hIA⟩
    have hψfin : IsOfFinOrder ψ := by
      rw [isOfFinOrder_iff_pow_eq_one]
      obtain ⟨m, hm, hpow⟩ := (hφ.pow (n := k)).exists_pow_eq_one
      refine ⟨m, hm, ?_⟩
      apply Subtype.ext
      simpa [ψ] using hpow
    letI : IsMulTorsionFree (MulAut.IA F) := ia_isMulTorsionFree
    exact congrArg Subtype.val <| IsOfFinOrder.eq_one' hψfin
  · intro hk
    simpa [MonoidHom.map_pow] using congrArg basis.toGL hk

end FreeGroupBasis

/-- Corollary 1-4-16: if a free group of rank `n` has an automorphism of positive finite order
`N`, then `GL (Fin n) ℤ` has an element of order `N`. -/
-- Layer triage:
-- `source-facing`: a free group `F` equipped with `basis : FreeGroupBasis (Fin n) F`, an
-- automorphism of `F` of exact order `N`, and the resulting existence of an element of
-- `GL (Fin n) ℤ` of exact order `N`.
-- `core/canonical`: `MulAut F`, `MulAut.abelianization F`, the basis-induced linear equivalence
-- from `Additive (Abelianization F)` to `FreeAbelianGroup (Fin n)`, and the matrix owner group
-- `GL (Fin n) ℤ`.
-- `bridge/view`: `FreeGroupBasis.toGL` is the canonical passage from a rank-`n` free-group
-- automorphism to the corresponding integral matrix.
-- Domain sampling:
-- 1. `FreeGroupBasis (Fin n) F` is the chapter owner abstraction for “a free group of rank `n`”.
-- 2. `MulAut.abelianization F` is the owner map from automorphisms of `F` to automorphisms of its
--    abelianization.
-- 3. `FreeAbelianGroup.basis (Fin n)` is the canonical basis on the free abelian group of rank
--    `n`.
-- 4. `Matrix.GeneralLinearGroup.toLin'` is the owner equivalence between `GL (Fin n) ℤ` and the
--    `ℤ`-linear general linear group of a module with basis `Fin n`.
-- Primitive vs. derived:
-- the primitive source data is the basis `basis : FreeGroupBasis (Fin n) F` and the explicit
-- automorphism `φ : MulAut F`; the free-group structure is canonically derived from
-- `basis.isFreeGroup`; the matrix in `GL (Fin n) ℤ` is derived canonically via `basis.toGL`.
theorem exists_gl_element_of_order_of_free_group_automorphism
    (basis : FreeGroupBasis (Fin n) F)
    (hN : 0 < N)
    (hF : ∃ φ : MulAut F, orderOf φ = N) :
    ∃ g : GL (Fin n) ℤ, orderOf g = N := by
  obtain ⟨φ, hφ⟩ := hF
  have hφ_fin : IsOfFinOrder φ := orderOf_pos_iff.mp <| hφ ▸ hN
  exact ⟨basis.toGL φ, hφ ▸ basis.orderOf_toGL_eq φ hφ_fin⟩

end
