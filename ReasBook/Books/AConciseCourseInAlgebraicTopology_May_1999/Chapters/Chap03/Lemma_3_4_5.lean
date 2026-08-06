import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_4_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory
open QuotientGroup
open Subgroup

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/- We write the textbook notation `Aut_G(S)` as `Aut_ G S` in Lean. -/
notation "Aut_" G:arg S:arg => Aut (Action.ofMulAction G S)

/-- The concrete centralizer view of `Aut_G S` inside `Equiv.Perm S`. -/
abbrev gSetAut (G : Type u) (S : Type v) [Group G] [MulAction G S] : Subgroup (Equiv.Perm S) :=
  centralizer ((MulAction.toPermHom G S).range : Set (Equiv.Perm S))

/-- A permutation lies in `gSetAut G S` exactly when it commutes with the `G`-action. -/
theorem mem_gSetAut_iff (σ : Equiv.Perm S) :
    σ ∈ gSetAut G S ↔ ∀ g : G, ∀ x : S, σ (g • x) = g • σ x := by
  constructor
  · intro hσ g x
    have hcomm : (MulAction.toPermHom G S) g * σ = σ * (MulAction.toPermHom G S) g :=
      (Subgroup.mem_centralizer_iff.mp hσ) _ ⟨g, rfl⟩
    simpa using (congrArg (fun τ : Equiv.Perm S ↦ τ x) hcomm).symm
  · intro hσ
    rw [Subgroup.mem_centralizer_iff]
    intro τ hτ
    rcases hτ with ⟨g, rfl⟩
    ext x
    simpa using (hσ g x).symm

/-- An element of `gSetAut G S` acts equivariantly on `S`. -/
theorem gSetAut_apply_smul (σ : gSetAut G S) (g : G) (x : S) :
    σ.1 (g • x) = g • σ.1 x :=
  (mem_gSetAut_iff σ.1).mp σ.2 g x

private noncomputable def autToPerm (f : Aut_ G S) : Equiv.Perm S where
  toFun := f.hom.hom
  invFun := f.inv.hom
  left_inv x := by
    simpa using congrFun (Action.hom_inv_hom f) x
  right_inv x := by
    simpa using congrFun (Action.inv_hom_hom f) x

private noncomputable def autToGSetAut (f : Aut_ G S) : gSetAut G S :=
  ⟨autToPerm f, by
    intro τ hτ
    rcases hτ with ⟨g, rfl⟩
    ext x
    simpa [Action.ofMulAction_apply, autToPerm] using
      (congrFun (f.hom.comm g) x).symm⟩

private noncomputable def gSetAutToAut (σ : gSetAut G S) : Aut_ G S :=
  Action.mkIso σ.1.toIso fun g ↦ by
    ext x
    have hσ : (MulAction.toPermHom G S) g * σ.1 = σ.1 * (MulAction.toPermHom G S) g :=
      (show σ.1 ∈ centralizer ((MulAction.toPermHom G S).range : Set (Equiv.Perm S)) from σ.2)
        _ ⟨g, rfl⟩
    simpa [Action.ofMulAction_apply] using
      (congrArg (fun τ : Equiv.Perm S ↦ τ x) hσ).symm

/-- The intrinsic automorphism group `Aut_G S` is canonically equivalent to its concrete
centralizer view in `Equiv.Perm S`. -/
noncomputable def autMulEquivGSetAut (G : Type u) (S : Type v) [Group G] [MulAction G S] :
    Aut_ G S ≃* gSetAut G S where
  toFun := autToGSetAut
  invFun := gSetAutToAut
  left_inv f := by
    ext x
    rfl
  right_inv σ := by
    ext x
    rfl
  map_mul' f g := by
    ext x
    rfl

private noncomputable def permCongrMulEquiv {α : Type u} {β : Type v} (e : α ≃ β) :
    Equiv.Perm α ≃* Equiv.Perm β where
  toFun := e.permCongr
  invFun := e.symm.permCongr
  left_inv σ := by
    ext x
    simp [Equiv.permCongr_apply]
  right_inv σ := by
    ext x
    simp [Equiv.permCongr_apply]
  map_mul' σ τ := by
    ext x
    simp [Equiv.permCongr_apply]

private noncomputable abbrev normalizerInvOpHom (H : Subgroup G) :
    normalizer (H : Set G) →* (normalizer (H : Set G)).op where
  toFun n := ⟨MulOpposite.op ((n : G)⁻¹), by
    exact (n⁻¹).2⟩
  map_one' := by
    ext
    simp
  map_mul' := by
    intro x y
    ext
    simp

/-- Right translation by the normalizer induces permutations of `G ⧸ H`. -/
private noncomputable abbrev rightQuotientPermHom (H : Subgroup G) :
    normalizer (H : Set G) →* Equiv.Perm (G ⧸ H) :=
  (MulAction.toPermHom (normalizer (H : Set G)).op (G ⧸ H)).comp (normalizerInvOpHom H)

/-- The kernel of the right-translation action on `G ⧸ H` is the induced copy of `H` inside its
normalizer. -/
-- Proof sketch: a normalizer element acts trivially on `G ⧸ H` exactly when its right
-- translation fixes the identity coset, which is equivalent to lying in `H`.
private theorem rightQuotientPermHom_ker_eq (H : Subgroup G) :
    (rightQuotientPermHom H).ker = H.subgroupOf (normalizer (H : Set G)) := by
  ext n
  constructor
  · intro hn
    rw [MonoidHom.mem_ker] at hn
    -- Evaluate the trivial permutation at the identity coset to read off membership in `H`.
    have hfix := congrArg (fun σ : Equiv.Perm (G ⧸ H) ↦ σ (((1 : G) : G ⧸ H))) hn
    have hmem : (n : G) ∈ H := by
      simpa [rightQuotientPermHom, normalizerInvOpHom, QuotientGroup.eq] using hfix
    simpa [Subgroup.mem_subgroupOf] using hmem
  · intro hn
    rw [MonoidHom.mem_ker]
    have hn' : (n : G) ∈ H := by
      simpa [Subgroup.mem_subgroupOf] using hn
    -- An element of `H` acts trivially on every left coset by right translation.
    ext q
    refine Quotient.inductionOn' q fun g ↦ ?_
    simp [rightQuotientPermHom, normalizerInvOpHom, hn']

/-- Helper for Lemma 3.4.5: the image of the identity coset determines a unique normalizer
element producing the same quotient permutation. -/
private theorem gset_aut_eq_rightQuotientPermHom_of_apply_one (H : Subgroup G)
    (σ : gSetAut G (G ⧸ H)) :
    ∃ n : normalizer (H : Set G), rightQuotientPermHom H n = σ.1 := by
  let oneCoset : G ⧸ H := (((1 : G) : G) : G ⧸ H)
  let a : G := (σ.1 oneCoset).out
  have ha : (((a : G) : G) : G ⧸ H) = σ.1 oneCoset := QuotientGroup.out_eq' _
  have hfix_of_mem {h : G} (hh : h ∈ H) :
      h • (((a : G) : G) : G ⧸ H) = (((a : G) : G) : G ⧸ H) := by
    have h_oneCoset : h • oneCoset = oneCoset := by
      change (((h * 1 : G) : G) : G ⧸ H) = (((1 : G) : G) : G ⧸ H)
      simpa [QuotientGroup.eq] using hh
    calc
      h • (((a : G) : G) : G ⧸ H) = h • σ.1 oneCoset := by rw [ha]
      _ = σ.1 (h • oneCoset) := by
        symm
        exact gSetAut_apply_smul σ h oneCoset
      _ = σ.1 oneCoset := by rw [h_oneCoset]
      _ = (((a : G) : G) : G ⧸ H) := ha.symm
  have ha_inv_mem_normalizer : a⁻¹ ∈ normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hfix := hfix_of_mem hh
      change (((h * a : G) : G) : G ⧸ H) = (((a : G) : G) : G ⧸ H) at hfix
      have hmem : ((h * a : G)⁻¹ * a) ∈ H := QuotientGroup.eq.mp hfix
      simpa [mul_assoc] using H.inv_mem hmem
    · intro hh
      let σinv : gSetAut G (G ⧸ H) := ⟨σ.1.symm, by
        change σ.1⁻¹ ∈ gSetAut G (G ⧸ H)
        exact inv_mem σ.2⟩
      have hfix_a : h • (((a : G) : G) : G ⧸ H) = (((a : G) : G) : G ⧸ H) := by
        apply QuotientGroup.eq.mpr
        simpa [mul_assoc] using H.inv_mem hh
      have hσinv_a : σinv.1 (((a : G) : G) : G ⧸ H) = oneCoset := by
        change σ.1.symm ((((a : G) : G) : G ⧸ H)) = oneCoset
        rw [ha]
        exact σ.1.left_inv oneCoset
      have hfix_oneCoset : h • oneCoset = oneCoset := by
        calc
          h • oneCoset = h • σinv.1 (((a : G) : G) : G ⧸ H) := by rw [hσinv_a]
          _ = σinv.1 (h • (((a : G) : G) : G ⧸ H)) := by
            symm
            exact gSetAut_apply_smul σinv h _
          _ = σinv.1 (((a : G) : G) : G ⧸ H) := by rw [hfix_a]
          _ = oneCoset := hσinv_a
      change (((h * 1 : G) : G) : G ⧸ H) = (((1 : G) : G) : G ⧸ H) at hfix_oneCoset
      simpa [QuotientGroup.eq] using hfix_oneCoset
  let n : normalizer (H : Set G) := ⟨a⁻¹, ha_inv_mem_normalizer⟩
  refine ⟨n, ?_⟩
  ext q
  refine Quotient.inductionOn' q fun g ↦ ?_
  calc
    rightQuotientPermHom H n (((g : G) : G) : G ⧸ H) = g • (((a : G) : G) : G ⧸ H) := by
      simp [rightQuotientPermHom, normalizerInvOpHom, n]
    _ = σ.1 (g • oneCoset) := by rw [gSetAut_apply_smul σ g oneCoset, ← ha]
    _ = σ.1 (((g : G) : G) : G ⧸ H) := by
      simp [oneCoset]

/-- Every `G`-equivariant automorphism of `G ⧸ H` comes from right translation by the normalizer. -/
-- Proof sketch: an equivariant automorphism is determined by the image of the identity coset, and
-- that image must be a coset `nH` with `n` normalizing `H`; this gives the required range
-- description.
private theorem rightQuotientPermHom_range_eq (H : Subgroup G) :
    (rightQuotientPermHom H).range = gSetAut G (G ⧸ H) := by
  ext σ
  constructor
  · rintro ⟨n, rfl⟩
    rw [mem_gSetAut_iff]
    intro g q
    refine Quotient.inductionOn' q fun x ↦ ?_
    simp [rightQuotientPermHom, normalizerInvOpHom, mul_assoc]
  · intro hσ
    rcases gset_aut_eq_rightQuotientPermHom_of_apply_one H ⟨σ, hσ⟩ with ⟨n, rfl⟩
    exact ⟨n, rfl⟩

/-- The Weyl group `N_G(H) / H` in the concrete permutation-centralizer view of
`Aut_G (G ⧸ H)`. -/
noncomputable def weylGroupMulEquivQuotientGSetAut (H : Subgroup G) :
    Subgroup.weylGroup H ≃* gSetAut G (G ⧸ H) :=
  (QuotientGroup.quotientMulEquivOfEq (rightQuotientPermHom_ker_eq H)).symm.trans
    ((QuotientGroup.quotientKerEquivRange (rightQuotientPermHom H)).trans
      (MulEquiv.subgroupCongr (rightQuotientPermHom_range_eq H)))

/-- The Weyl group `N_G(H) / H` is canonically isomorphic to `Aut_G (G ⧸ H)`. -/
noncomputable def weylGroupMulEquivQuotientAut (H : Subgroup G) :
    Subgroup.weylGroup H ≃* Aut_ G(G ⧸ H) :=
  (weylGroupMulEquivQuotientGSetAut H).trans
    (autMulEquivGSetAut G (G ⧸ H)).symm

namespace Subgroup

/-- For a normal subgroup `H`, its Weyl group is canonically the quotient `G ⧸ H`. -/
noncomputable def weylGroupMulEquivQuotientOfNormal (H : Subgroup G) [H.Normal] :
    weylGroup H ≃* G ⧸ H :=
  let h_normalizer : normalizer (H : Set G) = ⊤ :=
    H.normalizer_eq_top
  let e₁ :
      normalizer H ⧸ H.subgroupOf (normalizer H) ≃*
        (⊤ : Subgroup G) ⧸ H.subgroupOf (⊤ : Subgroup G) :=
    QuotientGroup.equivQuotientSubgroupOfOfEq rfl h_normalizer
  let e₂ :
      (⊤ : Subgroup G) ⧸ H.subgroupOf (⊤ : Subgroup G) ≃* G ⧸ H :=
    QuotientGroup.congr
      (H.subgroupOf (⊤ : Subgroup G))
      H
      topEquiv
      (map_subgroupOf_eq_of_le le_top)
  e₁.trans e₂

end Subgroup

section QuotientStabilizer

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/-- Helper for Lemma 3.4.5: the inverse quotient-stabilizer equivalence is `G`-equivariant. -/
private theorem quotientStabilizerEquivOfIsPretransitive_symm_equivariant
    [MulAction.IsPretransitive G S] (s : S) (g : G) (x : S) :
    ((quotientStabilizerEquivOfIsPretransitive s : G ⧸ MulAction.stabilizer G s ≃ S).symm
        (g • x)) =
      g •
        ((quotientStabilizerEquivOfIsPretransitive s : G ⧸ MulAction.stabilizer G s ≃ S).symm
          x) := by
  apply (quotientStabilizerEquivOfIsPretransitive s).injective
  simpa using (quotientStabilizerEquivOfIsPretransitive_equivariant s g
    ((quotientStabilizerEquivOfIsPretransitive s).symm x)).symm

private noncomputable def quotientStabilizerGSetAutMulEquiv
    [MulAction.IsPretransitive G S] (s : S) :
    gSetAut G (G ⧸ MulAction.stabilizer G s) ≃* gSetAut G S where
  toFun σ :=
    let e : G ⧸ MulAction.stabilizer G s ≃ S := quotientStabilizerEquivOfIsPretransitive s
    ⟨permCongrMulEquiv e σ.1, by
      rw [mem_gSetAut_iff]
      intro g x
      have hσ := (mem_gSetAut_iff σ.1).mp σ.2
      calc
        e (σ.1 (e.symm (g • x))) = e (σ.1 (g • e.symm x)) := by
          rw [quotientStabilizerEquivOfIsPretransitive_symm_equivariant s g x]
        _ = e (g • σ.1 (e.symm x)) := by rw [hσ g (e.symm x)]
        _ = g • e (σ.1 (e.symm x)) := by
          simpa using quotientStabilizerEquivOfIsPretransitive_equivariant s g
            (σ.1 (e.symm x))⟩
  invFun τ :=
    let e : G ⧸ MulAction.stabilizer G s ≃ S := quotientStabilizerEquivOfIsPretransitive s
    ⟨(permCongrMulEquiv e).symm τ.1, by
      rw [mem_gSetAut_iff]
      intro g x
      have hτ := (mem_gSetAut_iff τ.1).mp τ.2
      calc
        e.symm (τ.1 (e (g • x))) = e.symm (τ.1 (g • e x)) := by
          rw [quotientStabilizerEquivOfIsPretransitive_equivariant s g x]
        _ = e.symm (g • τ.1 (e x)) := by rw [hτ g (e x)]
        _ = g • e.symm (τ.1 (e x)) := by
          exact quotientStabilizerEquivOfIsPretransitive_symm_equivariant s g (τ.1 (e x))⟩
  left_inv σ := by
    apply Subtype.ext
    ext x
    exact congrArg (fun π : Equiv.Perm (G ⧸ MulAction.stabilizer G s) ↦ π x)
      ((permCongrMulEquiv (quotientStabilizerEquivOfIsPretransitive s)).left_inv σ.1)
  right_inv τ := by
    apply Subtype.ext
    ext x
    exact congrArg (fun π : Equiv.Perm S ↦ π x)
      ((permCongrMulEquiv (quotientStabilizerEquivOfIsPretransitive s)).right_inv τ.1)
  map_mul' σ τ := by
    apply Subtype.ext
    ext x
    exact congrArg (fun π : Equiv.Perm S ↦ π x)
      ((permCongrMulEquiv (quotientStabilizerEquivOfIsPretransitive s)).map_mul σ.1 τ.1)

/-- Transport `Aut_G (G ⧸ G_s)` across the canonical quotient-stabilizer equivalence from
Lemma 3.4.3 to obtain `Aut_G S`. -/
noncomputable def quotientStabilizerAutMulEquiv [MulAction.IsPretransitive G S] (s : S) :
    Aut_ G(G ⧸ MulAction.stabilizer G s) ≃* Aut_ G S :=
  (autMulEquivGSetAut G (G ⧸ MulAction.stabilizer G s)).trans
    ((quotientStabilizerGSetAutMulEquiv s).trans (autMulEquivGSetAut G S).symm)

/-- Evaluating `quotientStabilizerAutMulEquiv s` means conjugating an automorphism of
`G ⧸ G_s` by the canonical quotient-stabilizer equivalence from Lemma 3.4.3. -/
theorem quotientStabilizerAutMulEquiv_apply [MulAction.IsPretransitive G S] (s : S)
    (φ : Aut_ G(G ⧸ MulAction.stabilizer G s)) :
    quotientStabilizerAutMulEquiv s φ =
      (autMulEquivGSetAut G S).symm
        (quotientStabilizerGSetAutMulEquiv s
          ((autMulEquivGSetAut G (G ⧸ MulAction.stabilizer G s)) φ)) := by
  rfl

/-- Pointwise, `quotientStabilizerAutMulEquiv s` conjugates an automorphism of `G ⧸ G_s` by the
canonical quotient-stabilizer equivalence from Lemma 3.4.3. -/
theorem quotientStabilizerAutMulEquiv_hom_apply [MulAction.IsPretransitive G S] (s : S)
    (φ : Aut_ G(G ⧸ MulAction.stabilizer G s)) (x : S) :
    (quotientStabilizerAutMulEquiv s φ).hom.hom x =
      quotientStabilizerEquivOfIsPretransitive s
        (φ.hom.hom ((quotientStabilizerEquivOfIsPretransitive s).symm x)) := by
  rfl

/-- Lemma 3.4.5: if `G` acts transitively on `S` and `H = G_s`, then the Weyl group
`N_G(H) / H` is canonically isomorphic to the automorphism group `Aut_G S` of the `G`-set `S`. -/
noncomputable def weylGroup_stabilizer_mulEquiv_aut [MulAction.IsPretransitive G S] (s : S) :
    Subgroup.weylGroup (MulAction.stabilizer G s) ≃* Aut_ G S :=
  (weylGroupMulEquivQuotientAut (MulAction.stabilizer G s)).trans
    (quotientStabilizerAutMulEquiv s)

/-- Evaluating the Weyl-group equivalence amounts to first identify the Weyl group with
`Aut_G (G ⧸ G_s)`, pass to the concrete centralizer model, and then transport along the
quotient-stabilizer equivariant equivalence with `S`. -/
theorem weylGroup_stabilizer_mulEquiv_aut_apply [MulAction.IsPretransitive G S] (s : S)
    (x : Subgroup.weylGroup (MulAction.stabilizer G s)) :
    weylGroup_stabilizer_mulEquiv_aut s x =
      quotientStabilizerAutMulEquiv s
        (weylGroupMulEquivQuotientAut (MulAction.stabilizer G s) x) := by
  rfl

/-- Pointwise, the Weyl-group automorphism of `S` is obtained by transporting the corresponding
automorphism of `G ⧸ G_s` across the quotient-stabilizer equivalence. -/
theorem weylGroup_stabilizer_mulEquiv_aut_hom_apply [MulAction.IsPretransitive G S] (s : S)
    (x : Subgroup.weylGroup (MulAction.stabilizer G s)) (y : S) :
    (weylGroup_stabilizer_mulEquiv_aut s x).hom.hom y =
      quotientStabilizerEquivOfIsPretransitive s
        ((weylGroupMulEquivQuotientAut (MulAction.stabilizer G s) x).hom.hom
          ((quotientStabilizerEquivOfIsPretransitive s).symm y)) := by
  rfl

end QuotientStabilizer
