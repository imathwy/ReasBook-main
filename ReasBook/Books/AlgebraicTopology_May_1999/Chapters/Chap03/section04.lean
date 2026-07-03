import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_4_1 (from Chap03) -/
universe u v

variable (G : Type u) (S : Type v) [Group G]

/- Definition 3.4.1: A left action of a group `G` on a set `S` is the canonical mathlib typeclass
`MulAction G S`, written using the action notation `g • s`, with axioms `1 • s = s` and
`(g' * g) • s = g' • (g • s)`. -/
#check (MulAction G S)

/-! ### Definition_3_4_2 (from Chap03) -/
universe u v

/- Definition 3.4.2: a free action of `G` on `S` is the canonical proposition
`IsCancelSMul G S`. -/
recall IsCancelSMul (G : Type u) (S : Type v) [SMul G S] : Prop

/- The canonical mathlib owner for the orbit condition in a transitive action is
`MulAction.IsPretransitive G S`. The source-facing transitivity notion additionally requires
`Nonempty S`; mathlib does not introduce a separate `MulAction.IsTransitive`. -/
recall MulAction.IsPretransitive (G : Type u) (S : Type v) [SMul G S] : Prop

namespace MulAction

/-- Definition 3.4.2: a transitive action of `G` on `S` is a nonempty pretransitive action,
equivalently `S` is a single orbit. -/
def IsTransitive (G : Type u) (S : Type v) [SMul G S] : Prop :=
  Nonempty S ∧ IsPretransitive G S

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/-- A `G`-action on `S` is transitive exactly when some orbit is all of `S`. -/
theorem isTransitive_iff_exists_orbit_eq_univ :
    IsTransitive G S ↔ ∃ s : S, orbit G s = Set.univ := by
  constructor
  · rintro ⟨hS, hG⟩
    letI : IsPretransitive G S := hG
    obtain ⟨s⟩ := hS
    exact ⟨s, orbit_eq_univ G s⟩
  · rintro ⟨s, hs⟩
    exact ⟨⟨s⟩, (isPretransitive_iff_orbit_eq_univ s).2 hs⟩

/-- The source-facing transitivity notion is equivalent to nonemptiness together with the
canonical mathlib owner for the orbit condition. -/
theorem isTransitive_iff_nonempty_pretransitive :
    IsTransitive G S ↔ Nonempty S ∧ IsPretransitive G S :=
  Iff.rfl

end MulAction

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/- For `s : S`, the isotropy group `G_s` is the canonical subgroup
`MulAction.stabilizer G s` of those elements `g : G` satisfying `g • s = s`. -/
recall MulAction.stabilizer (G : Type u) {S : Type v} [Group G] [MulAction G S] (s : S) :
    Subgroup G

/- Equivalently, a free action is one whose isotropy groups are all trivial. -/
recall isCancelSMul_iff_stabilizer_eq_bot :
    IsCancelSMul G S ↔ ∀ s : S, MulAction.stabilizer G s = ⊥

/- With a chosen basepoint `s`, the orbit condition underlying transitivity is equivalent to every
point of `S` being a translate of `s`. -/
recall MulAction.isPretransitive_iff_base (s : S) :
    MulAction.IsPretransitive G S ↔ ∀ t : S, ∃ g : G, g • s = t

/- With a chosen basepoint `s`, the orbit condition underlying transitivity is also equivalent to
the orbit of `s` being all of `S`. -/
recall MulAction.isPretransitive_iff_orbit_eq_univ (s : S) :
    MulAction.IsPretransitive G S ↔ MulAction.orbit G s = Set.univ

/-! ### Lemma_3_4_3 (from Chap03) -/
universe u v

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/-- The canonical equivalence from the quotient `G ⧸ G_s` to a transitive `G`-set `S`. -/
noncomputable def quotientStabilizerEquivOfIsPretransitive [MulAction.IsPretransitive G S] (s : S) :
    G ⧸ MulAction.stabilizer G s ≃ S :=
  (MulAction.orbitEquivQuotientStabilizer G s).symm.trans
    ((Equiv.setCongr (MulAction.orbit_eq_univ G s)).trans (Equiv.Set.univ S))

@[simp] theorem quotientStabilizerEquivOfIsPretransitive_apply
    [MulAction.IsPretransitive G S] (s : S) (x : G ⧸ MulAction.stabilizer G s) :
    quotientStabilizerEquivOfIsPretransitive s x = MulAction.ofQuotientStabilizer G s x := by
  refine Quotient.inductionOn' x fun g ↦ ?_
  rfl

/-- Lemma 3.4.3: if the action of `G` on `S` is transitive, then the canonical equivariant map
`G ⧸ G_s → S`, sending `gG_s` to `g • s`, is bijective, so `S` is isomorphic to the `G`-set
`G ⧸ MulAction.stabilizer G s`. -/
theorem ofQuotientStabilizer_bijective_of_isPretransitive [MulAction.IsPretransitive G S] (s : S) :
    Function.Bijective (MulAction.ofQuotientStabilizer G s) := by
  simpa [quotientStabilizerEquivOfIsPretransitive_apply] using
    (quotientStabilizerEquivOfIsPretransitive s).bijective

/-- The quotient-stabilizer equivalence is `G`-equivariant. -/
theorem quotientStabilizerEquivOfIsPretransitive_equivariant
    [MulAction.IsPretransitive G S] (s : S) (g : G)
    (x : G ⧸ MulAction.stabilizer G s) :
    quotientStabilizerEquivOfIsPretransitive s (g • x) =
      g • quotientStabilizerEquivOfIsPretransitive s x := by
  simp [quotientStabilizerEquivOfIsPretransitive_apply, MulAction.ofQuotientStabilizer_smul]

/-! ### Definition_3_4_4 (from Chap03) -/
universe u

namespace Subgroup

variable {G : Type u} [Group G]

/- Definition 3.4.4: for a subgroup `H` of `G`, its normalizer is the canonical subgroup
`Subgroup.normalizer H`. -/
#check (fun H : Subgroup G ↦ Subgroup.normalizer (H : Set G))

/-- Definition 3.4.4: the Weyl group of `H` is the quotient of its normalizer by `H`, viewed as a
subgroup of `normalizer H`. -/
abbrev weylGroup (H : Subgroup G) : Type u :=
  Subgroup.normalizer H ⧸ H.subgroupOf (Subgroup.normalizer H)

/-- The Weyl group is canonically the quotient of `normalizer H` by the induced copy of `H`. -/
-- Proof sketch: This is immediate from unfolding `weylGroup`.
theorem weylGroup_def (H : Subgroup G) :
    weylGroup H = (Subgroup.normalizer H ⧸ H.subgroupOf (Subgroup.normalizer H)) := by
  -- Unfold the abbreviation to identify the Weyl group with the stated quotient.
  rfl

end Subgroup

/-! ### Lemma_3_4_5 (from Chap03) -/
universe u v w

open CategoryTheory
open scoped Pointwise
open QuotientGroup
open Subgroup

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

/- We write the textbook notation `Aut_G(S)` as `Aut_ G S` in Lean. -/
notation "Aut_" G:arg S:arg => Aut (Action.ofMulAction G S)

/-- The concrete centralizer view of `Aut_G S` inside `Equiv.Perm S`. -/
abbrev gSetAut (G : Type u) (S : Type v) [Group G] [MulAction G S] : Subgroup (Equiv.Perm S) :=
  centralizer ((MulAction.toPermHom G S).range : Set (Equiv.Perm S))

private noncomputable def autToPerm (f : Aut_ G S) : Equiv.Perm S where
  toFun := f.hom.hom
  invFun := f.inv.hom
  left_inv x := by
    change (ConcreteCategory.hom f.inv.hom) ((ConcreteCategory.hom f.hom.hom) x) = x
    have h := ConcreteCategory.congr_hom (Action.hom_inv_hom f) x
    simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at h
    exact h
  right_inv x := by
    change (ConcreteCategory.hom f.hom.hom) ((ConcreteCategory.hom f.inv.hom) x) = x
    have h := ConcreteCategory.congr_hom (Action.inv_hom_hom f) x
    simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at h
    exact h

private noncomputable def autToGSetAut (f : Aut_ G S) : gSetAut G S :=
  ⟨autToPerm f, by
    intro τ hτ
    rcases hτ with ⟨g, rfl⟩
    ext x
    simpa [Action.ofMulAction_apply, autToPerm] using
      (ConcreteCategory.congr_hom (f.hom.comm g) x).symm⟩

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
    simp [rightQuotientPermHom, normalizerInvOpHom, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfix ⊢
    exact hfix
  · intro hn
    rw [MonoidHom.mem_ker]
    have hn' : (n : G) ∈ H := by
      simpa [Subgroup.mem_subgroupOf] using hn
    -- An element of `H` acts trivially on every left coset by right translation.
    ext q
    refine Quotient.inductionOn' q fun g ↦ ?_
    simp [rightQuotientPermHom, normalizerInvOpHom, hn']

/-- Helper for Lemma 3.4.5: a concrete `G`-set automorphism commutes with the left `G`-action. -/
private theorem gSetAut_apply_smul (σ : gSetAut G S) (g : G) (x : S) :
    σ.1 (g • x) = g • σ.1 x := by
  -- Centralizing the image of `toPermHom` is exactly equivariance.
  have hcomm : (MulAction.toPermHom G S) g * σ.1 = σ.1 * (MulAction.toPermHom G S) g :=
    (Subgroup.mem_centralizer_iff.mp σ.2) _ ⟨g, rfl⟩
  have happly := congrArg (fun τ : Equiv.Perm S ↦ τ x) hcomm
  simpa using happly.symm

/-- Helper for Lemma 3.4.5: the image of the identity coset determines a unique normalizer
element producing the same quotient permutation. -/
private theorem gset_aut_eq_rightQuotientPermHom_of_apply_one (H : Subgroup G)
    (σ : gSetAut G (G ⧸ H)) :
    ∃ n : normalizer (H : Set G), rightQuotientPermHom H n = σ.1 := by
  let q₀ : G ⧸ H := σ.1 (((1 : G) : G ⧸ H))
  let n : G := q₀.out
  have hσcomm : ∀ g : G, σ.1 ((g : G ⧸ H)) = g • q₀ := by
    intro g
    -- Equivariance lets us compute `σ` on every coset from its value at `1H`.
    simpa [q₀] using gSetAut_apply_smul (G := G) (S := G ⧸ H) σ g (((1 : G) : G ⧸ H))
  have hn_normalizer : n ∈ normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    constructor
    · intro hh
      -- If `h ∈ H`, then `h` fixes `1H`, so equivariance forces it to fix `q₀`.
      have hfix : h • q₀ = q₀ := by
        calc
          h • q₀ = σ.1 ((h : G) • (((1 : G) : G ⧸ H))) := by
            rw [gSetAut_apply_smul (G := G) (S := G ⧸ H) σ h (((1 : G) : G ⧸ H))]
          _ = σ.1 (((1 : G) : G ⧸ H)) := by simp [QuotientGroup.eq, hh]
          _ = q₀ := rfl
      have hquot : ((h * n : G) : G ⧸ H) = ((n : G) : G ⧸ H) := by
        calc
          ((h * n : G) : G ⧸ H) = h • ((n : G) : G ⧸ H) := by rfl
          _ = h • q₀ := by rw [QuotientGroup.out_eq' q₀]
          _ = q₀ := hfix
          _ = ((n : G) : G ⧸ H) := (QuotientGroup.out_eq' q₀).symm
      rw [QuotientGroup.eq] at hquot
      have hquot_inv : ((h * n)⁻¹ * n)⁻¹ ∈ H := H.inv_mem hquot
      simpa [n, mul_assoc] using hquot_inv
    · intro hh
      have hquot : ((h * n : G) : G ⧸ H) = ((n : G) : G ⧸ H) := by
        rw [QuotientGroup.eq]
        have hquot_inv : ((h * n)⁻¹ * n) ∈ H := by
          have hhinv : (n⁻¹ * h * n)⁻¹ ∈ H := H.inv_mem hh
          simpa [n, mul_assoc] using hhinv
        exact hquot_inv
      have hfix : h • q₀ = q₀ := by
        calc
          h • q₀ = h • ((n : G) : G ⧸ H) := by rw [QuotientGroup.out_eq' q₀]
          _ = ((h * n : G) : G ⧸ H) := by rfl
          _ = ((n : G) : G ⧸ H) := hquot
          _ = q₀ := QuotientGroup.out_eq' q₀
      -- Injectivity of `σ` brings the fixed-point condition back to the base coset.
      have hσeq : σ.1 ((h : G ⧸ H)) = σ.1 (((1 : G) : G ⧸ H)) := by
        calc
          σ.1 ((h : G ⧸ H)) = h • q₀ := hσcomm h
          _ = q₀ := hfix
          _ = σ.1 (((1 : G) : G ⧸ H)) := rfl
      have hbase : ((h : G) : G ⧸ H) = (((1 : G) : G) : G ⧸ H) := σ.1.injective hσeq
      simpa [QuotientGroup.eq] using hbase
  refine ⟨⟨n⁻¹, inv_mem hn_normalizer⟩, ?_⟩
  -- The chosen witness sends `1H` to `q₀`, so equivariance forces agreement on all cosets.
  ext q
  refine Quotient.inductionOn' q fun g ↦ ?_
  calc
    rightQuotientPermHom H ⟨n⁻¹, inv_mem hn_normalizer⟩ ((g : G ⧸ H)) = ((g * n : G) : G ⧸ H) := by
      simp [rightQuotientPermHom, normalizerInvOpHom]
    _ = g • q₀ := by
      rw [← QuotientGroup.out_eq' q₀]
      rfl
    _ = σ.1 ((g : G ⧸ H)) := by rw [hσcomm]

/-- Every `G`-equivariant automorphism of `G ⧸ H` comes from right translation by the normalizer. -/
-- Proof sketch: an equivariant automorphism is determined by the image of the identity coset, and
-- that image must be a coset `nH` with `n` normalizing `H`; this gives the required range
-- description.
private theorem rightQuotientPermHom_range_eq (H : Subgroup G) :
    (rightQuotientPermHom H).range = gSetAut G (G ⧸ H) := by
  ext σ
  constructor
  · intro hσ
    rcases hσ with ⟨n, rfl⟩
    -- Left multiplication commutes with right multiplication on cosets.
    rw [Subgroup.mem_centralizer_iff]
    intro τ hτ
    rcases hτ with ⟨g, rfl⟩
    ext q
    refine Quotient.inductionOn' q fun x ↦ ?_
    simp [rightQuotientPermHom, normalizerInvOpHom, mul_assoc]
  · intro hσ
    -- Reconstruct the normalizer element from the image of `1H`.
    rcases gset_aut_eq_rightQuotientPermHom_of_apply_one (G := G) H ⟨σ, hσ⟩ with ⟨n, hn⟩
    exact ⟨n, hn⟩

/-- The Weyl group `N_G(H) / H` in the concrete permutation-centralizer view of
`Aut_G (G ⧸ H)`. -/
noncomputable def weylGroupMulEquivQuotientGSetAut (H : Subgroup G) :
    Subgroup.weylGroup H ≃* gSetAut G (G ⧸ H) :=
  (QuotientGroup.quotientMulEquivOfEq (rightQuotientPermHom_ker_eq H)).symm.trans
    ((QuotientGroup.quotientKerEquivRange (rightQuotientPermHom H)).trans
      (MulEquiv.subgroupCongr (rightQuotientPermHom_range_eq H)))

/-- The Weyl group `N_G(H) / H` is canonically isomorphic to `Aut_G (G ⧸ H)`. -/
noncomputable def weylGroupMulEquivQuotientAut (H : Subgroup G) :
    Subgroup.weylGroup H ≃* Aut_ G (G ⧸ H) :=
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

/-- Helper for Lemma 3.4.5: the inverse quotient-stabilizer equivalence sends an element of `S`
to a quotient representative mapping back to it. -/
private theorem quotientStabilizerEquivOfIsPretransitive_symm_apply
    [MulAction.IsPretransitive G S] (s : S) (x : S) :
    MulAction.ofQuotientStabilizer G s
      ((quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s).symm x) = x := by
  have hx : quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
      ((quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s).symm x) = x :=
    (quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s).apply_symm_apply x
  rwa [quotientStabilizerEquivOfIsPretransitive_apply] at hx

/-- Helper for Lemma 3.4.5: the inverse quotient-stabilizer equivalence is `G`-equivariant. -/
private theorem quotientStabilizerEquivOfIsPretransitive_symm_equivariant
    [MulAction.IsPretransitive G S] (s : S) (g : G) (x : S) :
    (quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s).symm (g • x) =
      g • (quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s).symm x := by
  let e := quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
  -- Apply the forward equivariant equivalence to reduce the claim to the known equivariance law.
  apply e.injective
  calc
    e (e.symm (g • x)) = g • x := by simp [e]
    _ = MulAction.ofQuotientStabilizer G s (g • e.symm x) := by
          symm
          simpa [quotientStabilizerEquivOfIsPretransitive_apply, e] using
            quotientStabilizerEquivOfIsPretransitive_equivariant (G := G) (S := S) s g (e.symm x)
    _ = e (g • e.symm x) := by rfl

private noncomputable def quotientStabilizerGSetAutMulEquiv
    [MulAction.IsPretransitive G S] (s : S) :
    gSetAut G (G ⧸ MulAction.stabilizer G s) ≃* gSetAut G S where
  toFun σ :=
    let e := quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
    ⟨permCongrMulEquiv e σ.1, by
      -- Conjugating by an equivariant equivalence preserves commutation with the left action.
      rw [Subgroup.mem_centralizer_iff]
      intro τ hτ
      rcases hτ with ⟨g, rfl⟩
      ext x
      calc
        ((MulAction.toPermHom G S) g * permCongrMulEquiv e σ.1) x = g • e (σ.1 (e.symm x)) := by
          simp [permCongrMulEquiv, Equiv.permCongr_apply]
        _ = e (g • σ.1 (e.symm x)) := by
          simpa [quotientStabilizerEquivOfIsPretransitive_apply] using
            (quotientStabilizerEquivOfIsPretransitive_equivariant (G := G) (S := S) s g
              (σ.1 (e.symm x))).symm
        _ = e (σ.1 (e.symm (g • x))) := by
          rw [quotientStabilizerEquivOfIsPretransitive_symm_equivariant (G := G) (S := S),
            gSetAut_apply_smul (G := G) (S := G ⧸ MulAction.stabilizer G s)]
        _ = (permCongrMulEquiv e σ.1 * (MulAction.toPermHom G S) g) x := by
          simp [permCongrMulEquiv, Equiv.permCongr_apply]⟩
  invFun τ :=
    let e := quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
    ⟨(permCongrMulEquiv e).symm τ.1, by
      -- The same conjugation argument works in the reverse direction.
      rw [Subgroup.mem_centralizer_iff]
      intro ρ hρ
      rcases hρ with ⟨g, rfl⟩
      ext x
      calc
        ((MulAction.toPermHom G (G ⧸ MulAction.stabilizer G s)) g * (permCongrMulEquiv e).symm τ.1) x
            = g • e.symm (τ.1 (e x)) := by
              simp [permCongrMulEquiv]
        _ = e.symm (g • τ.1 (e x)) := by
              rw [← quotientStabilizerEquivOfIsPretransitive_symm_equivariant (G := G) (S := S)]
        _ = e.symm (τ.1 (g • e x)) := by
              rw [gSetAut_apply_smul (G := G) (S := S)]
        _ = e.symm (τ.1 (e (g • x))) := by
              rw [quotientStabilizerEquivOfIsPretransitive_equivariant (G := G) (S := S)]
        _ = ((permCongrMulEquiv e).symm τ.1 * (MulAction.toPermHom G (G ⧸ MulAction.stabilizer G s)) g) x := by
              simp [permCongrMulEquiv]⟩
  left_inv := by
    intro σ
    -- The forward and backward conjugations cancel pointwise.
    let e := quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
    ext x
    have hcancel : e.symm (e (σ.1 (e.symm (e x)))) = σ.1 x := by
      rw [e.symm_apply_apply, e.symm_apply_apply]
    simpa [permCongrMulEquiv, Equiv.permCongr_apply, e,
      quotientStabilizerEquivOfIsPretransitive_apply] using hcancel
  right_inv := by
    intro τ
    -- The same cancellation gives the inverse identity on `S`.
    let e := quotientStabilizerEquivOfIsPretransitive (G := G) (S := S) s
    ext x
    have hcancel : e (e.symm (τ.1 (e (e.symm x)))) = τ.1 x := by
      rw [e.apply_symm_apply, e.apply_symm_apply]
    simpa [permCongrMulEquiv, Equiv.permCongr_apply, e,
      quotientStabilizerEquivOfIsPretransitive_apply] using hcancel
  map_mul' := by
    intro σ τ
    -- Conjugation is multiplicative on permutations.
    ext x
    simp [permCongrMulEquiv, Equiv.permCongr_apply]

/-- Lemma 3.4.5: if `G` acts transitively on `S` and `H = G_s`, then the Weyl group
`N_G(H) / H` is canonically isomorphic to the automorphism group `Aut_G S` of the `G`-set `S`. -/
noncomputable def weylGroup_stabilizer_mulEquiv_aut [MulAction.IsPretransitive G S] (s : S) :
    Subgroup.weylGroup (MulAction.stabilizer G s) ≃* Aut_ G S :=
  (weylGroupMulEquivQuotientAut (MulAction.stabilizer G s)).trans
    ((autMulEquivGSetAut G (G ⧸ MulAction.stabilizer G s)).trans
      ((quotientStabilizerGSetAutMulEquiv s).trans (autMulEquivGSetAut G S).symm))

/-- Evaluating the Weyl-group equivalence amounts to first identify the Weyl group with
`Aut_G (G ⧸ G_s)`, pass to the concrete centralizer model, and then transport along the
quotient-stabilizer equivariant equivalence with `S`. -/
-- Proof sketch: unfold `weylGroup_stabilizer_mulEquiv_aut` and evaluate the composite
-- equivalence on the given quotient element.
theorem weylGroup_stabilizer_mulEquiv_aut_apply [MulAction.IsPretransitive G S] (s : S)
    (x : Subgroup.weylGroup (MulAction.stabilizer G s)) :
    weylGroup_stabilizer_mulEquiv_aut s x =
      (autMulEquivGSetAut G S).symm
        (quotientStabilizerGSetAutMulEquiv s
          ((autMulEquivGSetAut G (G ⧸ MulAction.stabilizer G s))
            (weylGroupMulEquivQuotientAut (MulAction.stabilizer G s) x))) := by
  -- This is exactly the value of the composite equivalence after unfolding the definition.
  rfl

end QuotientStabilizer

/-! ### Lemma_3_4_6 (from Chap03) -/
universe u

open scoped Pointwise
open QuotientGroup

variable {G : Type u} [Group G] {H K : Subgroup G}

/-- Lemma 3.4.6: a `G`-equivariant map `α : G ⧸ H → G ⧸ K` is determined by the image of the base
coset `eH`; if `α(eH) = γK`, then `α(gH) = gγK` for every `g : G`. -/
-- Proof sketch: every coset `gH` is `g • eH`, so equivariance gives
-- `α (gH) = g • α (eH) = g • γK`, and the quotient action identifies `g • γK` with `(g * γ)K`.
theorem quotient_mulActionHom_apply_coe_eq_coe_mul_of_apply_one
    (α : G ⧸ H →[G] G ⧸ K) (γ : G) (g : G)
    (hα : α ((1 : G) : G ⧸ H) = (γ : G ⧸ K)) :
    α (g : G ⧸ H) = ((g * γ : G) : G ⧸ K) := by
  -- Rewrite `gH` as `g • eH` and use equivariance to move `g` through `α`.
  calc
    α (g : G ⧸ H) = α (g • ((1 : G) : G ⧸ H)) := by simp
    _ = (g : G) • α ((1 : G) : G ⧸ H) := by
      simpa using α.map_smul g (((1 : G) : G ⧸ H))
    -- Substitute the prescribed value of `α(eH)` and simplify the quotient action.
    _ = ((g * γ : G) : G ⧸ K) := by
      simp [hα]

/-- Helper for Lemma 3.4.6: evaluating a `G`-equivariant map `G ⧸ H → G ⧸ K` at the identity
coset gives an `H`-fixed point of `G ⧸ K`. -/
theorem quotient_mulActionHom_apply_one_mem_fixedPoints (α : G ⧸ H →[G] G ⧸ K) :
    α ((1 : G) : G ⧸ H) ∈ MulAction.fixedPoints H (G ⧸ K) := by
  rw [MulAction.mem_fixedPoints]
  intro h
  -- The identity coset of `G ⧸ H` is fixed by every element of `H`.
  have hh : (h : G) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    simpa using
      (QuotientGroup.eq.mpr (show ((h : G)⁻¹ * 1) ∈ H by
        simp [H.inv_mem h.2]) : ((h : G) : G ⧸ H) = ((1 : G) : G ⧸ H))
  -- Transport that fixed-point relation across the equivariant map `α`.
  calc
    (h : G) • α ((1 : G) : G ⧸ H) = α ((h : G) • ((1 : G) : G ⧸ H)) := by
      symm
      simpa using α.map_smul (h : G) (((1 : G) : G ⧸ H))
    _ = α ((1 : G) : G ⧸ H) := by
      simp [hh]

/-- Helper for Lemma 3.4.6: if a `G`-equivariant map `G ⧸ H → G ⧸ K` sends `eH` to `γK`, then
`γ⁻¹ H γ` is contained in `K`. -/
-- Proof sketch: `α(eH)` is `H`-fixed by `quotient_mulActionHom_apply_one_mem_fixedPoints`.
-- Instantiating the fixed-point condition on the representative `γK` at `h⁻¹ ∈ H` yields
-- `(h⁻¹ * γ)K = γK`, and rewriting equality of left cosets gives `γ⁻¹ * h * γ ∈ K`.
theorem subgroup_map_conj_inv_le_of_quotient_mulActionHom_apply_one
    (α : G ⧸ H →[G] G ⧸ K) (γ : G)
    (hα : α ((1 : G) : G ⧸ H) = (γ : G ⧸ K)) :
    MulAut.conj γ⁻¹ • H ≤ K := by
  -- Replace `α(eH)` by `γK` in the fixed-point statement coming from equivariance.
  have hfixed : (γ : G ⧸ K) ∈ MulAction.fixedPoints H (G ⧸ K) := by
    simpa [hα] using quotient_mulActionHom_apply_one_mem_fixedPoints α
  rw [Subgroup.pointwise_smul_def]
  rintro _ ⟨h, hh, rfl⟩
  -- Apply fixedness to `h⁻¹ ∈ H` so that the resulting coset equality reads `(h⁻¹ * γ)K = γK`.
  have hq : (((h⁻¹ : G) * γ : G) : G ⧸ K) = (γ : G ⧸ K) := by
    simpa using (MulAction.mem_fixedPoints.1 hfixed ⟨h⁻¹, H.inv_mem hh⟩)
  -- Convert equality of left cosets into the desired conjugacy membership statement.
  simpa [MulAut.conj_apply, mul_assoc] using
    (show γ⁻¹ * h * γ ∈ K by
      simpa [mul_assoc] using (QuotientGroup.eq.mp hq))

/-! ### Definition_3_4_7 (from Chap03) -/
universe u

open CategoryTheory
open QuotientGroup

variable (G : Type u) [Group G]

/-- Definition 3.4.7: the orbit category `O(G)` has as objects the canonical transitive `G`-sets
`G ⧸ H`, encoded by subgroups `H ≤ G`. The owner is distinct from `Subgroup G`; the subgroup
encoding is a view of the objects, not the orbit category itself. -/
@[ext]
structure orbitCategory : Type u where
  toSubgroup : Subgroup G

notation "O(" G ")" => orbitCategory G

attribute [coe] orbitCategory.toSubgroup

namespace orbitCategory

instance : CoeTC (O(G)) (Subgroup G) := ⟨orbitCategory.toSubgroup⟩

instance : HasQuotient G (O(G)) := ⟨fun H ↦ G ⧸ (H : Subgroup G)⟩

instance (H : O(G)) : CoeTC G (G ⧸ H) :=
  show CoeTC G (G ⧸ (H : Subgroup G)) from inferInstance

instance (H : O(G)) : MulAction G (G ⧸ H) :=
  show MulAction G (G ⧸ (H : Subgroup G)) from inferInstance

instance instIsPretransitiveQuotient (H : O(G)) : MulAction.IsPretransitive G (G ⧸ H) :=
  show MulAction.IsPretransitive G (G ⧸ (H : Subgroup G)) from inferInstance

instance (H : O(G)) [TopologicalSpace G] : TopologicalSpace (G ⧸ H) :=
  show TopologicalSpace (G ⧸ (H : Subgroup G)) from inferInstance

theorem toSubgroup_injective : Function.Injective ((↑) : O(G) → Subgroup G)
  | ⟨_⟩, ⟨_⟩, rfl => rfl

instance : SetLike (O(G)) G where
  coe H := H.toSubgroup.carrier
  coe_injective' H K h := by
    apply toSubgroup_injective
    exact SetLike.ext' h

instance : SubgroupClass (O(G)) G where
  mul_mem {H} := H.toSubgroup.mul_mem
  one_mem H := H.toSubgroup.one_mem
  inv_mem {H} := H.toSubgroup.inv_mem

instance : PartialOrder (O(G)) := .ofSetLike (O(G)) G

end orbitCategory

/-- Morphisms in the orbit category are the `G`-equivariant maps between the quotient `G`-sets. -/
instance : Category (O(G)) where
  Hom H K := G ⧸ H →[G] G ⧸ K
  id H := MulActionHom.id G
  comp f g := MulActionHom.comp g f

/-- Every object of the orbit category is a transitive `G`-set. -/
theorem orbitCategory_obj_isTransitive (H : O(G)) :
    MulAction.IsTransitive G (G ⧸ H) :=
  ⟨⟨((1 : G) : G ⧸ H)⟩, inferInstance⟩

/-! ### Lemma_3_4_8 (from Chap03) -/
universe u

open CategoryTheory
open QuotientGroup
open scoped Pointwise

namespace Subgroup

variable {G : Type u} [Group G]

/-- A coset `γK` is `H`-fixed in `G ⧸ K` exactly when `γ⁻¹ H γ ≤ K`. -/
-- Proof sketch: rewrite the fixed-coset condition as `(h * γ)K = γK` for every `h ∈ H`, then use
-- the quotient-group criterion for equality of left cosets to identify this with
-- `γ⁻¹ * h * γ ∈ K`.
theorem mem_fixedPoints_iff_conj_le (H K : Subgroup G) (γ : G) :
    ((γ : G ⧸ K) ∈ MulAction.fixedPoints H (G ⧸ K)) ↔
      MulAut.conj γ⁻¹ • H ≤ K := by
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    rw [Subgroup.pointwise_smul_def]
    rintro _ ⟨h', hh', rfl⟩
    have hq : (((h'⁻¹ : G) * γ : G) : G ⧸ K) = (γ : G ⧸ K) := by
      simpa using h ⟨h'⁻¹, H.inv_mem hh'⟩
    simpa [MulAut.conj_apply, mul_assoc] using
      (show γ⁻¹ * h' * γ ∈ K by
        simpa [mul_assoc] using (QuotientGroup.eq.mp hq))
  · intro h h'
    rw [Subgroup.pointwise_smul_def] at h
    apply QuotientGroup.eq.mpr
    have hk : γ⁻¹ * ((h' : G)⁻¹) * γ ∈ K := by
      exact h ⟨(h' : G)⁻¹, H.inv_mem h'.2, by simp [mul_assoc]⟩
    simpa [mul_assoc] using hk

/-- Evaluation at the identity coset sends a morphism in the orbit category to its corresponding
`H`-fixed coset in `G ⧸ K`. -/
def orbitCategoryHomEvalOne (H K : O(G)) :
    (H ⟶ K) → MulAction.fixedPoints (H : Subgroup G) (G ⧸ K) :=
  fun α ↦ ⟨α.toFun ((1 : G) : G ⧸ H), quotient_mulActionHom_apply_one_mem_fixedPoints α⟩

/-- Helper for Lemma 3.4.8: an `H`-fixed coset has stabilizer containing `H`. -/
theorem fixed_points_le_stabilizer_quotient (H K : O(G))
    (x : MulAction.fixedPoints (H : Subgroup G) (G ⧸ K)) :
    (H : Subgroup G) ≤ MulAction.stabilizer G (x : G ⧸ K) := by
  -- Rewrite fixedness as a stabilizer condition for each element of `H`.
  intro h hh
  rw [MulAction.mem_stabilizer_iff]
  exact (MulAction.mem_fixedPoints.mp x.2) ⟨h, hh⟩

/-- Helper for Lemma 3.4.8: quotient maps induced by subgroup inclusions commute with the
ambient `G`-action on quotient sets. -/
theorem quotientMapOfLE_smul {H L : Subgroup G} (h : H ≤ L) (g : G) (q : G ⧸ H) :
    Subgroup.quotientMapOfLE h (g • q) = g • Subgroup.quotientMapOfLE h q := by
  -- Check the formula on representatives, where both sides are definitional.
  refine Quotient.inductionOn' q ?_
  intro a
  simp [Subgroup.quotientMapOfLE_apply_mk]

/-- Helper for Lemma 3.4.8: the orbit map attached to an `H`-fixed coset is `G`-equivariant. -/
theorem orbitCategoryHomOfFixedPoint_map_smul (H K : O(G))
    (x : MulAction.fixedPoints (H : Subgroup G) (G ⧸ K))
    (g : G) (q : G ⧸ H) :
    MulAction.ofQuotientStabilizer G (x : G ⧸ K)
      (Subgroup.quotientMapOfLE (fixed_points_le_stabilizer_quotient H K x) (g • q)) =
      g • MulAction.ofQuotientStabilizer G (x : G ⧸ K)
        (Subgroup.quotientMapOfLE (fixed_points_le_stabilizer_quotient H K x) q) := by
  -- Pass the action through the quotient map, then through the quotient-stabilizer map.
  rw [quotientMapOfLE_smul]
  simpa using
    (MulAction.ofQuotientStabilizer_smul G (x : G ⧸ K) g
      (Subgroup.quotientMapOfLE (fixed_points_le_stabilizer_quotient H K x) q))

/-- Helper for Lemma 3.4.8: an `H`-fixed coset determines the equivariant map `gH ↦ g • x`. -/
def orbitCategoryHomOfFixedPoint (H K : O(G)) :
    MulAction.fixedPoints (H : Subgroup G) (G ⧸ K) → (H ⟶ K) :=
  fun x ↦
    { toFun := fun q ↦
        MulAction.ofQuotientStabilizer G (x : G ⧸ K)
          (Subgroup.quotientMapOfLE (fixed_points_le_stabilizer_quotient H K x) q)
      map_smul' := orbitCategoryHomOfFixedPoint_map_smul H K x }

/-- Helper for Lemma 3.4.8: evaluating the orbit map built from a fixed coset recovers that
fixed coset. -/
theorem orbitCategoryHomEvalOne_orbitCategoryHomOfFixedPoint (H K : O(G))
    (x : MulAction.fixedPoints (H : Subgroup G) (G ⧸ K)) :
    orbitCategoryHomEvalOne H K (orbitCategoryHomOfFixedPoint H K x) = x := by
  -- Compare the underlying cosets at the identity representative.
  apply Subtype.ext
  simp [orbitCategoryHomEvalOne, orbitCategoryHomOfFixedPoint,
    Subgroup.quotientMapOfLE_apply_mk, MulAction.ofQuotientStabilizer_mk]

/-- Helper for Lemma 3.4.8: rebuilding a morphism from its value on the identity coset gives back
that morphism. -/
theorem orbitCategoryHomOfFixedPoint_orbitCategoryHomEvalOne (H K : O(G))
    (α : H ⟶ K) :
    orbitCategoryHomOfFixedPoint H K (orbitCategoryHomEvalOne H K α) = α := by
  -- Compare the two equivariant maps on quotient representatives.
  refine MulActionHom.ext ?_
  intro q
  refine Quotient.inductionOn' q ?_
  intro g
  calc
    (orbitCategoryHomOfFixedPoint H K (orbitCategoryHomEvalOne H K α)).toFun (g : G ⧸ H)
        = g • α.toFun ((1 : G) : G ⧸ H) := by
          simp [orbitCategoryHomOfFixedPoint, orbitCategoryHomEvalOne,
            Subgroup.quotientMapOfLE_apply_mk, MulAction.ofQuotientStabilizer_mk]
    -- Equivariance rewrites the original morphism on `gH` using its value on `1H`.
    _ = α.toFun (g • ((1 : G) : G ⧸ H)) := by
          exact (α.map_smul' g (((1 : G) : G ⧸ H))).symm
    _ = α.toFun (g : G ⧸ H) := by simp

/-- Evaluation at the identity coset gives a bijection from orbit-category morphisms to admissible
subconjugacy cosets, canonically realized as `H`-fixed cosets of `G ⧸ K`. -/
-- Proof sketch: injectivity is Lemma 3.4.6, which says an equivariant map is determined by the
-- image of the identity coset. Surjectivity sends an admissible coset `γK` to the unique map
-- `gH ↦ gγK`; the fixed-coset condition is exactly what makes this formula well defined.
theorem orbitCategoryHomEvalOne_bijective (H K : O(G)) :
    Function.Bijective (orbitCategoryHomEvalOne H K) := by
  constructor
  · intro α β hαβ
    -- Evaluation at `1H` determines the whole morphism, so compare both reconstructions.
    calc
      α = orbitCategoryHomOfFixedPoint H K (orbitCategoryHomEvalOne H K α) := by
        symm
        exact orbitCategoryHomOfFixedPoint_orbitCategoryHomEvalOne H K α
      _ = orbitCategoryHomOfFixedPoint H K (orbitCategoryHomEvalOne H K β) := by
        rw [hαβ]
      _ = β := orbitCategoryHomOfFixedPoint_orbitCategoryHomEvalOne H K β
  · intro x
    -- The canonical orbit map attached to `x` evaluates back to `x`.
    exact ⟨orbitCategoryHomOfFixedPoint H K x,
      orbitCategoryHomEvalOne_orbitCategoryHomOfFixedPoint H K x⟩

/-- Lemma 3.4.8: for subgroups `H, K ≤ G`, the morphisms in `O(G)` from `H` to `K` are exactly
the distinct subconjugacy relations `γ⁻¹ H γ ≤ K`, canonically encoded as `H`-fixed cosets
of `G ⧸ K`. -/
noncomputable def orbitCategoryHomEquivFixedPoints (H K : O(G)) :
    (H ⟶ K) ≃ MulAction.fixedPoints (H : Subgroup G) (G ⧸ K) :=
  Equiv.ofBijective (orbitCategoryHomEvalOne H K) (orbitCategoryHomEvalOne_bijective H K)

/-- Applying the equivalence of Lemma 3.4.8 is evaluation of an orbit-category morphism at the
identity coset. -/
-- Proof sketch: unfold `orbitCategoryHomEquivFixedPoints`; it was defined by applying
-- `Equiv.ofBijective` to `orbitCategoryHomEvalOne`.
theorem orbitCategoryHomEquivFixedPoints_apply (H K : O(G)) (α : H ⟶ K) :
    orbitCategoryHomEquivFixedPoints H K α = orbitCategoryHomEvalOne H K α := by
  -- The equivalence was defined with `orbitCategoryHomEvalOne` as its forward map.
  rfl

end Subgroup

/-! ### Definition_3_4_9 (from Chap03) -/
universe u v w

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

variable (B : Type u) [Groupoid.{v} B]

/- Definition 3.4.9: a functor from a small groupoid `B` to sets is the canonical functor type
`B ⥤ Type v`; this is the source-facing notion of an action of `B` on sets. -/
#check (B ⥤ Type w)

namespace CategoryTheory.Functor

variable {B : Type u} [Groupoid.{v} B]

/-- For a functor `T : B ⥤ Type v`, the source-facing vertex group `π(B, b)` acts on the fiber
`T.obj b`. Since `T` is covariant, the corresponding left action is given by inverse loops. -/
noncomputable abbrev vertexGroupAction (T : B ⥤ Type w) (b : B) :
    MulAction (b ⟶ b) (T.obj b) :=
  MulAction.ofEndHom
    { toFun := fun g : b ⟶ b => fun x ↦ T.map g⁻¹ x
      map_one' := by
        funext x
        simp [Function.End.one_def]
      map_mul' := by
        intro g h
        funext x
        simp [Function.End.mul_def] }

/-- The source-facing vertex-group action attached to `T` evaluates a loop by applying `T.map` to
its inverse. -/
@[simp] theorem vertexGroupAction_smul_eq_map_inv (T : B ⥤ Type w) (b : B)
    (g : b ⟶ b) (x : T.obj b) :
    letI := vertexGroupAction T b
    g • x = T.map g⁻¹ x := by
  rfl

/-- The implementation-level `End b`-action corresponding to `vertexGroupAction T b`. Since
`CategoryTheory.End b` reverses categorical multiplication, this bridge evaluates a loop directly
by `T.map`. -/
noncomputable abbrev vertexGroupMulAction (T : B ⥤ Type w) (b : B) :
    MulAction (CategoryTheory.End b) (T.obj b) :=
  MulAction.ofEndHom
    { toFun := fun g => (T.map g ·)
      map_one' := by
        funext x
        simp [Function.End.one_def]
      map_mul' := by
        intro g h
        funext x
        simp [Function.End.mul_def, T.map_comp] }

/-- The vertex-group action attached to `T` evaluates a loop by applying `T.map`. -/
@[simp] theorem vertexGroupMulAction_smul_eq_map (T : B ⥤ Type w) (b : B)
    (g : CategoryTheory.End b) (x : T.obj b) :
    letI := vertexGroupMulAction T b
    g • x = T.map g x := by
  change (vertexGroupMulAction T b).smul g x = T.map g x
  rfl

end CategoryTheory.Functor

/-! ### Definition_3_4_10 (from Chap03) -/
universe u v

open CategoryTheory

namespace CategoryTheory.Functor

variable {B : Type u} [Groupoid.{v} B]

/-- Definition 3.4.10: a functor `T : B ⥤ Type v` is transitive if, for every object `b : B`, the
source-facing vertex group `π(B,b)` acts transitively on the fiber `T.obj b`. -/
def IsTransitive (T : B ⥤ Type v) : Prop :=
  ∀ b : B,
    letI := vertexGroupAction T b
    MulAction.IsTransitive (b ⟶ b) (T.obj b)

noncomputable section

/-- Helper for Definition 3.4.10: the source-facing transitivity condition at a fixed object. -/
private abbrev VertexGroupActionTransitive (T : B ⥤ Type v) (b : B) : Prop :=
  letI := vertexGroupAction T b
  MulAction.IsTransitive (b ⟶ b) (T.obj b)

/-- Helper for Definition 3.4.10: the `End`-based transitivity condition at a fixed object. -/
private abbrev VertexGroupMulActionTransitive (T : B ⥤ Type v) (b : B) : Prop :=
  letI := vertexGroupMulAction T b
  MulAction.IsTransitive (End b) (T.obj b)

/-- Helper for Definition 3.4.10: an equivariant equivalence of acting groups and fibers carries a
transitive action to a transitive action. -/
private theorem isTransitive_of_equivariant_equiv
    {H : Type*} [Group H] {K : Type*} [Group K]
    {X : Type*} [MulAction H X] {Y : Type*} [MulAction K Y]
    (eH : H ≃* K) (eX : X ≃ Y)
    (hcompat : ∀ g x, eX (g • x) = eH g • eX x)
    (h : MulAction.IsTransitive H X) :
    MulAction.IsTransitive K Y := by
  rcases h with ⟨hX, hpre⟩
  let f : X →ₑ[eH] Y :=
    { toFun := eX
      map_smul' := hcompat }
  have hf : Function.Bijective f := eX.bijective
  -- Move the nonemptiness and orbit condition across the equivariant bijection.
  refine ⟨hX.map eX, ?_⟩
  exact (MulAction.isPretransitive_congr eH.surjective hf).mp hpre

/-- Helper for Definition 3.4.10: a witness for the inverse-loop action produces a witness for the
direct `End`-action by inverting the loop. -/
private theorem vertexGroupMulAction_exists_of_vertexGroupAction_exists
    (T : B ⥤ Type v) (b : B) (x y : T.obj b)
    (h : ∃ g : b ⟶ b, letI := vertexGroupAction T b; g • x = y) :
    ∃ g : End b, letI := vertexGroupMulAction T b; g • x = y := by
  rcases h with ⟨g, hg⟩
  refine ⟨((g⁻¹ : b ⟶ b) : End b), ?_⟩
  letI := vertexGroupAction T b
  letI := vertexGroupMulAction T b
  -- Rewrite the source-facing action through `T.map` and transport the inverse through `T`.
  have hg' : CategoryTheory.inv (T.map g) x = y := by
    simpa [vertexGroupAction_smul_eq_map_inv] using hg
  rw [vertexGroupMulAction_smul_eq_map]
  calc
    T.map (((g⁻¹ : b ⟶ b) : End b)) x = CategoryTheory.inv (T.map g) x := by
      simpa using congrArg (fun f : T.obj b ⟶ T.obj b => f x) (Functor.map_inv T g)
    _ = y := hg'

/-- Helper for Definition 3.4.10: a witness for the direct `End`-action produces a witness for the
source-facing inverse-loop action by inverting the endomorphism. -/
private theorem vertexGroupAction_exists_of_vertexGroupMulAction_exists
    (T : B ⥤ Type v) (b : B) (x y : T.obj b)
    (h : ∃ g : End b, letI := vertexGroupMulAction T b; g • x = y) :
    ∃ g : b ⟶ b, letI := vertexGroupAction T b; g • x = y := by
  rcases h with ⟨g, hg⟩
  refine ⟨(((g⁻¹ : End b) : b ⟶ b)), ?_⟩
  letI := vertexGroupAction T b
  letI := vertexGroupMulAction T b
  -- After inverting the `End`-witness, the source action reduces to the same `T.map g`.
  have hg' : T.map g x = y := by
    simpa [vertexGroupMulAction_smul_eq_map] using hg
  rw [vertexGroupAction_smul_eq_map_inv]
  calc
    T.map (g⁻¹⁻¹) x = CategoryTheory.inv (T.map g⁻¹) x := by
      simpa using congrArg (fun f : T.obj b ⟶ T.obj b => f x) (Functor.map_inv T (g⁻¹))
    _ = T.map g x := by
      symm
      simpa using congrArg (fun f : T.obj b ⟶ T.obj b => f x) (Functor.map_inv T (g⁻¹))
    _ = y := hg'

/-- Helper for Definition 3.4.10: at a fixed object, the source-facing loop action and the
auxiliary `End`-action have the same transitivity condition. -/
theorem vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive
    (T : B ⥤ Type v) (b : B) :
    VertexGroupActionTransitive T b ↔ VertexGroupMulActionTransitive T b := by
  constructor
  · intro h
    letI := vertexGroupAction T b
    letI := vertexGroupMulAction T b
    change MulAction.IsTransitive (b ⟶ b) (T.obj b) at h
    change MulAction.IsTransitive (End b) (T.obj b)
    rw [MulAction.isTransitive_iff_nonempty_pretransitive] at h
    rcases h with ⟨hx, hpre⟩
    refine ⟨hx, ?_⟩
    obtain ⟨x₀⟩ := hx
    -- Use a chosen basepoint in the fiber and translate the orbit witnesses.
    rw [MulAction.isPretransitive_iff_base x₀] at hpre ⊢
    intro y
    exact vertexGroupMulAction_exists_of_vertexGroupAction_exists T b x₀ y (hpre y)
  · intro h
    letI := vertexGroupAction T b
    letI := vertexGroupMulAction T b
    change MulAction.IsTransitive (End b) (T.obj b) at h
    change MulAction.IsTransitive (b ⟶ b) (T.obj b)
    rw [MulAction.isTransitive_iff_nonempty_pretransitive] at h
    rcases h with ⟨hx, hpre⟩
    refine ⟨hx, ?_⟩
    obtain ⟨x₀⟩ := hx
    -- Translate orbit witnesses back by inverting the chosen endomorphism.
    rw [MulAction.isPretransitive_iff_base x₀] at hpre ⊢
    intro y
    exact vertexGroupAction_exists_of_vertexGroupMulAction_exists T b x₀ y (hpre y)

/-- Helper for Definition 3.4.10: an isomorphism of objects transports transitivity of the
`End`-based vertex-group action between the two fibers. -/
theorem vertexGroupMulAction_isTransitive_iff_of_iso
    (T : B ⥤ Type v) {b b' : B} (i : b ≅ b') :
    VertexGroupMulActionTransitive T b ↔ VertexGroupMulActionTransitive T b' := by
  letI := vertexGroupMulAction T b
  letI := vertexGroupMulAction T b'
  constructor
  · intro h
    change MulAction.IsTransitive (End b') (T.obj b')
    -- Transport both loops and points along the isomorphism `i`.
    exact isTransitive_of_equivariant_equiv i.conj (T.mapIso i).toEquiv
      (fun g x ↦ by
        simp only [vertexGroupMulAction_smul_eq_map, Iso.conj_apply, Functor.mapIso_hom,
          Iso.toEquiv_fun, ← Functor.map_comp_apply]
        simp [Iso.hom_inv_id_assoc])
      h
  · intro h
    change MulAction.IsTransitive (End b) (T.obj b)
    -- Apply the same transport argument to the inverse isomorphism.
    exact isTransitive_of_equivariant_equiv i.symm.conj (T.mapIso i.symm).toEquiv
      (fun g x ↦ by
        simp only [vertexGroupMulAction_smul_eq_map, Iso.conj_apply,
          Iso.toEquiv_fun, Iso.symm_hom, Iso.symm_inv]
        change (ConcreteCategory.hom (T.map g ≫ (T.mapIso i).inv)) x =
               (ConcreteCategory.hom ((T.mapIso i).inv ≫ T.map (i.hom ≫ g ≫ i.inv))) x
        congr 1
        simp only [Functor.mapIso_inv, ← T.map_comp, Category.assoc, Iso.inv_hom_id_assoc])
      h

/-- Helper for Definition 3.4.10: in a connected groupoid, transitivity of the `End`-action at one
object propagates to every object. -/
theorem forall_vertexGroupMulAction_isTransitive_of_isConnected [CategoryTheory.IsConnected B]
    (T : B ⥤ Type v) (b₀ : B) :
    VertexGroupMulActionTransitive T b₀ →
    ∀ b : B,
      letI := vertexGroupMulAction T b
      MulAction.IsTransitive (End b) (T.obj b) := by
  intro hb₀ b
  classical
  -- Connectedness supplies a morphism from `b₀` to `b`, hence an isomorphism in the groupoid.
  let f : b₀ ⟶ b := Classical.choice (CategoryTheory.nonempty_hom_of_preconnected_groupoid b₀ b)
  let i : b₀ ≅ b := (Groupoid.isoEquivHom _ _).symm f
  exact (vertexGroupMulAction_isTransitive_iff_of_iso T i).mp hb₀

/-- The source-facing transitivity condition is equivalent to the same condition phrased through
the auxiliary `End`-based action `vertexGroupMulAction`. -/
theorem isTransitive_iff_forall_vertexGroupMulAction_isTransitive (T : B ⥤ Type v) :
    IsTransitive T ↔
      ∀ b : B,
        letI := vertexGroupMulAction T b
        MulAction.IsTransitive (End b) (T.obj b) := by
  constructor
  · intro hT b
    -- Rewrite the defining pointwise condition through the `End`-action bridge.
    exact (vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive T b).mp (hT b)
  · intro hT b
    -- Rewrite back objectwise to recover the original source-facing condition.
    exact (vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive T b).mpr (hT b)

/-- For a connected groupoid, transitivity of a functor can be checked at a single object via the
canonical vertex-group action on that fiber. -/
-- Proof sketch: use connectedness to choose a zigzag, hence an isomorphism in the groupoid,
-- from the chosen base object `b₀` to any `b`; transport points and the orbit condition along
-- `T.map` of that isomorphism to transfer transitivity between the two fibers.
theorem isTransitive_iff_at_object [CategoryTheory.IsConnected B]
    (T : B ⥤ Type v) (b₀ : B) :
    IsTransitive T ↔
      letI := vertexGroupAction T b₀
      MulAction.IsTransitive (b₀ ⟶ b₀) (T.obj b₀) := by
  constructor
  · intro hT
    -- Specialize the global transitivity condition to `b₀` after rewriting via `End b₀`.
    have hAll :
        ∀ b : B,
          letI := vertexGroupMulAction T b
          MulAction.IsTransitive (End b) (T.obj b) :=
      (isTransitive_iff_forall_vertexGroupMulAction_isTransitive T).mp hT
    exact (vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive T b₀).mpr
      (hAll b₀)
  · intro hb₀
    -- Convert the base-object hypothesis to the `End`-action and propagate it by connectedness.
    have hb₀' :
        letI := vertexGroupMulAction T b₀
        MulAction.IsTransitive (End b₀) (T.obj b₀) :=
      (vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive T b₀).mp hb₀
    have hAll :
        ∀ b : B,
          letI := vertexGroupMulAction T b
          MulAction.IsTransitive (End b) (T.obj b) :=
      forall_vertexGroupMulAction_isTransitive_of_isConnected T b₀ hb₀'
    exact (isTransitive_iff_forall_vertexGroupMulAction_isTransitive T).mpr hAll

end

end CategoryTheory.Functor

/-! ### Lemma_3_4_11 (from Chap03) -/
universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Helper for Lemma 3.4.11: a morphism upstairs carries the canonical point in one fiber to the
canonical point in the next fiber under the corresponding fiber translation downstairs. -/
lemma fiberTranslationMap_map_eq_of_hom (hp : Functor.IsCovering p) {x y : E} (g : x ⟶ y) :
    fiberTranslationMap hp (p.map g) (⟨x, rfl⟩ : p.Fiber (p.obj x)) = ⟨y, rfl⟩ := by
  apply Subtype.ext
  -- Compare the chosen lift of `p.map g` with the actual arrow `g`.
  have hstar : starLift hp (p.map g) ⟨x, rfl⟩ = Under.mk g := by
    apply (hp.star_bijective x).injective
    calc
      (Under.post p).obj (starLift hp (p.map g) ⟨x, rfl⟩) = Under.mk (p.map g) := by
        simpa using starLift_post_eq hp (p.map g) ⟨x, rfl⟩
      _ = (Under.post p).obj (Under.mk g) := by
        simp [Under.post]
  -- Equality of lifted under-objects identifies their endpoints.
  change (starLift hp (p.map g) ⟨x, rfl⟩).right = y
  simpa using congrArg Comma.right hstar

/-- Helper for Lemma 3.4.11: fiber translation along an `eqToHom` changes only the witness that
the chosen point lies in the relevant fiber. -/
lemma fiberTranslationMap_eqToHom_basepoint (hp : Functor.IsCovering p) {x : E} {b : B}
    (h : p.obj x = b) :
    fiberTranslationMap hp (eqToHom h) (⟨x, rfl⟩ : p.Fiber (p.obj x)) = ⟨x, h⟩ := by
  -- After reducing to the reflexive case, fiber translation along the identity is trivial.
  cases h
  exact congrArg (fun f ↦ f (⟨x, rfl⟩ : p.Fiber (p.obj x))) (fiberTranslationMap_id hp (p.obj x))

/-- Lemma 3.4.11 (1): if the total groupoid of a covering functor is connected, then the vertex
group at each base object acts transitively on the corresponding fiber by fiber translation. -/
-- Proof sketch: for points `x y` in the same fiber over `b`, connectedness of `E` gives a
-- morphism `g : x.1 ⟶ y.1`; its image under `p` is a loop at `b`, and lifting that loop from
-- `x` recovers `g`, so fiber translation sends `x` to `y`.
theorem fiberTranslationMulAction_isTransitive [CategoryTheory.IsConnected E]
    (hp : Functor.IsCovering p) (b : B) :
    fiberTranslationMulAction.IsTransitive hp b := by
  letI := fiberTranslationMulAction hp b
  change MulAction.IsTransitive (b ⟶ b) (p.Fiber b)
  rw [MulAction.isTransitive_iff_nonempty_pretransitive]
  obtain ⟨x, rfl⟩ := hp.obj_surjective b
  let x₀ : p.Fiber (p.obj x) := ⟨x, rfl⟩
  refine ⟨⟨x₀⟩, ?_⟩
  -- Use connectedness of `E` to reach every fiber point from the chosen basepoint upstairs.
  have hbase : ∀ y : p.Fiber (p.obj x), ∃ g : p.obj x ⟶ p.obj x, g • x₀ = y := by
    rintro ⟨y, hy⟩
    let g : x ⟶ y :=
      Classical.choice (CategoryTheory.nonempty_hom_of_preconnected_groupoid x y)
    let γ : p.obj x ⟶ p.obj x := eqToHom hy.symm ≫ p.map (CategoryTheory.Groupoid.inv g)
    refine ⟨γ, ?_⟩
    have hg : fiberTranslationMap hp (p.map g) x₀ = (⟨y, rfl⟩ : p.Fiber (p.obj y)) := by
      simpa [x₀] using (fiberTranslationMap_map_eq_of_hom (hp := hp) g)
    have htransport :
        fiberTranslationMap hp (eqToHom hy) (⟨y, rfl⟩ : p.Fiber (p.obj y)) = ⟨y, hy⟩ := by
      exact fiberTranslationMap_eqToHom_basepoint (hp := hp) hy
    have hcomp : fiberTranslationMap hp (p.map g ≫ eqToHom hy) x₀ = ⟨y, hy⟩ := by
      -- First follow the lifted arrow `g`, then transport the endpoint into the target fiber.
      rw [fiberTranslationMap_comp]
      simpa [Function.comp, hg] using htransport
    have hγinv : γ⁻¹ = p.map g ≫ eqToHom hy := by
      simp [γ]
    -- The action uses inverse loops, so the witness is the inverse of the image of `g`.
    calc
      γ • x₀ = fiberTranslationMap hp γ⁻¹ x₀ := by
        change (fiberTranslationFunctor hp).map γ⁻¹ x₀ = fiberTranslationMap hp γ⁻¹ x₀
        rfl
      _ = fiberTranslationMap hp (p.map g ≫ eqToHom hy) x₀ := by
        rw [hγinv]
      _ = ⟨y, hy⟩ := hcomp
  exact (MulAction.isPretransitive_iff_base x₀).2 hbase

/-- The transitive fiber-translation action is in particular pretransitive. -/
theorem fiberTranslationMulAction_isPretransitive [CategoryTheory.IsConnected E]
    (hp : Functor.IsCovering p) (b : B) :
    fiberTranslationMulAction.IsPretransitive hp b := by
  letI := fiberTranslationMulAction hp b
  change MulAction.IsPretransitive (b ⟶ b) (p.Fiber b)
  exact (fiberTranslationMulAction_isTransitive hp b).2

/-- Helper for Lemma 3.4.11: if a loop fixes the distinguished base fiber point, then it comes
from a loop in the vertex group upstairs. -/
private theorem mapVertexGroup_mem_of_fiberTranslation_inv_basepoint_fixed
    (hp : Functor.IsCovering p) (e : E) {γ : p.obj e ⟶ p.obj e}
    (hγ : fiberTranslationMap hp γ⁻¹ (⟨e, rfl⟩ : p.Fiber (p.obj e)) = ⟨e, rfl⟩) :
    γ ∈ (Functor.mapVertexGroup p e).range := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  let u := starLift hp γ⁻¹ x₀
  -- The fixed-point hypothesis forces the lifted arrow of `γ⁻¹` to end back at `e`.
  have hright : u.right = e := by
    exact congrArg Subtype.val hγ
  have hobj : starLift_obj hp γ⁻¹ x₀ = congrArg p.obj hright := by
    apply Subsingleton.elim
  have hloop : p.map (u.hom ≫ eqToHom hright) = γ⁻¹ := by
    -- Normalize the lift, then cancel the endpoint transport coming from `hright`.
    have hmap : p.map u.hom = γ⁻¹ ≫ eqToHom (congrArg p.obj hright).symm := by
      simpa [u, x₀, hobj] using starLift_hom_over hp γ⁻¹ x₀
    have hmapEqToHom : p.map (eqToHom hright) = eqToHom (congrArg p.obj hright) := by
      simpa using eqToHom_map p hright
    have hcancel :
        eqToHom (congrArg p.obj hright).symm ≫ p.map (eqToHom hright) = 𝟙 (p.obj e) := by
      rw [hmapEqToHom]
      simp
    calc
      p.map (u.hom ≫ eqToHom hright) = p.map u.hom ≫ p.map (eqToHom hright) := by
        simp
      _ = (γ⁻¹ ≫ eqToHom (congrArg p.obj hright).symm) ≫ p.map (eqToHom hright) := by
        exact congrArg (fun k ↦ k ≫ p.map (eqToHom hright)) hmap
      _ = γ⁻¹ ≫ (eqToHom (congrArg p.obj hright).symm ≫ p.map (eqToHom hright)) := by
        simp [Category.assoc]
      _ = γ⁻¹ := by
        rw [hcancel]
        simp
  have hmem_inv : γ⁻¹ ∈ (Functor.mapVertexGroup p e).range := by
    refine ⟨u.hom ≫ eqToHom hright, hloop⟩
  simpa using Subgroup.inv_mem (Functor.mapVertexGroup p e).range hmem_inv

/-- Lemma 3.4.11 (2): the stabilizer of the distinguished point `⟨e, rfl⟩` for the fiber
translation action is the image of the vertex group at `e` under the covering functor. -/
-- Proof sketch: a loop `γ` at `p.obj e` fixes `⟨e, rfl⟩` exactly when its chosen lift starting at
-- `e` ends again at `e`; this is equivalent to `γ` lying in the range of `Functor.mapVertexGroup
-- p e`.
theorem fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range
    (hp : Functor.IsCovering p) (e : E) :
    let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
    letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
      fiberTranslationMulAction hp (p.obj e)
    MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ =
      (Functor.mapVertexGroup p e).range := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  ext γ
  constructor
  · intro hγ
    rw [MulAction.mem_stabilizer_iff] at hγ
    change fiberTranslationMap hp γ⁻¹ x₀ = x₀ at hγ
    -- A stabilizing loop is exactly a loop whose chosen lift closes up at `e`.
    exact mapVertexGroup_mem_of_fiberTranslation_inv_basepoint_fixed hp e hγ
  · rintro ⟨δ, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change fiberTranslationMap hp (p.map δ)⁻¹ x₀ = x₀
    -- The inverse loop `δ⁻¹` upstairs lifts the base loop and returns to the basepoint.
    simpa [x₀] using
      (fiberTranslationMap_map_eq_of_hom (hp := hp) (x := e) (y := e) δ⁻¹)

end CategoryTheory.Functor.IsCovering

/-! ### Remark_3_4_12 (from Chap03) -/
universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- The regularity condition is equivalent to normality of the stabilizer of the distinguished
point in the fiber action. -/
-- Proof sketch: rewrite the stabilizer at `⟨e, rfl⟩` as the image of
-- `Functor.mapVertexGroup p e` using
-- `fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range`, then unfold
-- `Functor.IsRegularCovering`.
theorem isRegularCovering_iff_fiberTranslation_basepoint_stabilizer_normal
    (hp : Functor.IsCovering p) (e : E) :
    by
      letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
        fiberTranslationMulAction hp (p.obj e)
      let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
      exact Functor.IsRegularCovering p e ↔
        (MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀).Normal := by
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  constructor
  · intro hreg
    rw [fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e]
    exact hreg.2
  · intro hnormal
    exact ⟨hp, by
      rw [← fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e]
      exact hnormal⟩

/-- Helper for Remark 3.4.12: on a connected total groupoid, universality at `e` is equivalent
to freeness of the fiber-translation action over `p.obj e`. -/
private theorem isUniversalCovering_iff_fiberTranslation_isFree [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    Functor.IsUniversalCovering p e ↔ fiberTranslationMulAction.IsFree hp (p.obj e) := by
  have htrans : fiberTranslationMulAction.IsTransitive hp (p.obj e) :=
    fiberTranslationMulAction_isTransitive hp (p.obj e)
  -- Connectedness supplies the pretransitivity required by Lemma 3.3.12.
  exact isUniversalCovering_iff_fiberTranslation_isFree_of_isPretransitive hp e htrans.2

/-- For a connected total groupoid, universality is equivalent to the fiber translation action
being free and transitive. -/
-- Proof sketch:
-- connectedness supplies transitivity of the whole fiber action, and Lemma 3.3.12 upgrades
-- universality to freeness of the canonical fiber-translation action; pairing these gives the
-- free-transitive description.
theorem isUniversalCovering_iff_fiberTranslation_free_transitive [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    Functor.IsUniversalCovering p e ↔
      fiberTranslationMulAction.IsFree hp (p.obj e) ∧
        fiberTranslationMulAction.IsTransitive hp (p.obj e) := by
  have htrans : fiberTranslationMulAction.IsTransitive hp (p.obj e) :=
    fiberTranslationMulAction_isTransitive hp (p.obj e)
  -- First collapse universality to the freeness criterion specialized to the connected case.
  rw [isUniversalCovering_iff_fiberTranslation_isFree hp e]
  constructor
  · intro hfree
    -- The transitivity witness is global, so freeness is the only remaining datum.
    exact ⟨hfree, htrans⟩
  · rintro ⟨hfree, htrans⟩
    -- The backward direction only needs the freeness component; transitivity is automatic here.
    exact hfree

/-- Remark 3.4.12: regular coverings correspond to normal isotropy subgroups, while on a
connected total groupoid universal coverings correspond to free transitive fiber actions. -/
-- Proof sketch: combine the stabilizer description from Lemma 3.4.11 with the definitions of
-- regular and universal covering, and use connectedness to supply transitivity of the fiber
-- translation action in the universal case.
theorem regular_and_universal_covering_characterizations
    (hp : Functor.IsCovering p) (e : E) [IsConnected E] :
    (Functor.IsRegularCovering p e ↔
        letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
          fiberTranslationMulAction hp (p.obj e)
        let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
        (MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀).Normal) ∧
      (Functor.IsUniversalCovering p e ↔
        fiberTranslationMulAction.IsFree hp (p.obj e) ∧
          fiberTranslationMulAction.IsTransitive hp (p.obj e)) := by
  constructor
  · -- Regularity is exactly normality of the basepoint stabilizer.
    exact isRegularCovering_iff_fiberTranslation_basepoint_stabilizer_normal hp e
  · -- In the connected case, universality is freeness together with transitivity.
    exact isUniversalCovering_iff_fiberTranslation_free_transitive hp e

end CategoryTheory.Functor.IsCovering
