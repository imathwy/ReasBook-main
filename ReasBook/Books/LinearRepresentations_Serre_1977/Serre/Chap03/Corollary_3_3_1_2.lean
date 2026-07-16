import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Serre.Chap03.Lemma_3_3_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

section

open Rep
open Module.End
open scoped IsMulCommutative

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G]
variable (A : Subgroup G) [A.FiniteIndex] [IsMulCommutative A]

private def uliftRepresentation
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    Representation k G (ULift.{max u v} V) where
  toFun g :=
    { toFun := fun x ↦ ⟨ρ g x.down⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

private def uliftRepresentationEquiv
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    ρ.Equiv (uliftRepresentation ρ) :=
  Representation.Equiv.mk ULift.moduleEquiv.symm fun g ↦ by
    ext x
    rfl

omit [IsAlgClosed k] in
private theorem isIrreducible_uliftRepresentation
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsIrreducible] :
    (uliftRepresentation ρ).IsIrreducible := by
  exact isIrreducible_of_nonempty_equiv ⟨uliftRepresentationEquiv ρ⟩

-- Source/core/bridge triage:
-- * source-facing: the corollary is about an irreducible representation
--   `ρ : Representation k G V`.
-- * core/canonical: irreducibility is the owner predicate `ρ.IsIrreducible`.
-- * bridge/view: `Rep.of ρ` is used only internally, because subgroup induction and Frobenius
--   reciprocity live canonically in `Rep k G`.
--
-- Proof sketch: choose an irreducible `A`-subrepresentation `W` of the restriction `X|ₐ`.
-- Since `A` is commutative, the canonical owner theorem
-- `Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative` gives `dim W = 1`.
-- Frobenius reciprocity turns the inclusion `W ↪ X|ₐ` into the canonical morphism
-- `Ind_A^G(W) ⟶ X`; because `X` is irreducible and the image contains a nonzero vector of `W`,
-- this map is surjective. The induced representation is spanned by the generators indexed by the
-- right cosets of `A`, and each such generator is a scalar multiple of a fixed nonzero vector in
-- `W`; right cosets are in bijection with `G ⧸ A`, so the number of spanning vectors is `A.index`.
private theorem finrank_le_index_of_commutative_subgroup_rep
    (X : Rep.{max (max u v) w} k G) [FiniteDimensional k X] [X.ρ.IsIrreducible] :
    Module.finrank k X ≤ A.index := by
  let ρA : Representation k A X := (Rep.res A.subtype X).ρ
  letI : Nontrivial X := by
    by_contra hX
    letI : Subsingleton X := not_nontrivial_iff_subsingleton.mp hX
    have hbot : (⊥ : Subrepresentation X.ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (Subsingleton.elim x 0)
    exact bot_ne_top hbot
  let S : Set (Submodule k X) := {W | W ∈ ρA.invtSubmodule ∧ W ≠ ⊥}
  have hS_nonempty : S.Nonempty := by
    refine ⟨⊤, ?_, top_ne_bot⟩
    exact Representation.invtSubmodule.top_mem ρA
  obtain ⟨Wsub, hWsub, hWmin⟩ := IsArtinian.set_has_minimal S hS_nonempty
  have hWinv : Wsub ∈ ρA.invtSubmodule := hWsub.1
  have hW_ne_bot : Wsub ≠ ⊥ := hWsub.2
  have hWstable : ∀ a : A, ∀ x ∈ Wsub, ρA a x ∈ Wsub := by
    intro a x hx
    have hWa : Wsub ∈ Module.End.invtSubmodule (ρA a) := ρA.mem_invtSubmodule.mp hWinv a
    rw [mem_invtSubmodule_iff_forall_mem_of_mem] at hWa
    exact hWa x hx
  let W : Subrepresentation ρA :=
    { toSubmodule := Wsub
      apply_mem_toSubmodule := hWstable }
  have hWirr : W.toRepresentation.IsIrreducible := by
    letI : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hW_ne_bot
    letI : Nontrivial (Subrepresentation W.toRepresentation) := by
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro h
      exact bot_ne_top <| congrArg Subrepresentation.toSubmodule h
    refine IsSimpleOrder.of_forall_eq_top fun Y hY ↦ ?_
    have hY_mem : Y.toSubmodule.map W.toSubmodule.subtype ∈ ρA.invtSubmodule := by
      rw [Representation.mem_invtSubmodule]
      intro a
      rw [mem_invtSubmodule_iff_forall_mem_of_mem]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨W.toRepresentation a y, Y.apply_mem_toSubmodule a hy, rfl⟩
    have hY_toSubmodule_ne_bot : Y.toSubmodule ≠ ⊥ := by
      intro hY_bot
      exact hY <| Subrepresentation.toSubmodule_injective hY_bot
    have hY_ne_bot : Y.toSubmodule.map W.toSubmodule.subtype ≠ ⊥ := by
      obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hY_toSubmodule_ne_bot
      intro hY_bot
      have hy_mem : y.1 ∈ Y.toSubmodule.map W.toSubmodule.subtype := ⟨y, hy, rfl⟩
      rw [hY_bot] at hy_mem
      exact hy0 <| by simpa using hy_mem
    have hY_le : Y.toSubmodule.map W.toSubmodule.subtype ≤ Wsub :=
      Wsub.map_subtype_le Y.toSubmodule
    have hY_eq : Y.toSubmodule.map W.toSubmodule.subtype = Wsub := by
      refine le_antisymm hY_le ?_
      by_contra hlt
      exact hWmin _ ⟨hY_mem, hY_ne_bot⟩ (lt_of_le_of_ne hY_le fun hEq ↦ hlt <| by simp [hEq])
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro x _
    have hx : x.1 ∈ Y.toSubmodule.map W.toSubmodule.subtype := by simp [hY_eq]
    rcases hx with ⟨y, hy, hyx⟩
    exact Subtype.ext hyx ▸ hy
  have hW_dim : Module.finrank k W.toSubmodule = 1 := by
    letI : W.toRepresentation.IsIrreducible := hWirr
    simpa using Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative W.toRepresentation
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hW_ne_bot
  let Y : Rep k G := Rep.ind A.subtype (Rep.of W.toRepresentation)
  let f : Y ⟶ X := inducedFromSubrepresentationHom X.ρ A W
  have hf_mk (g : G) (x : W.toSubmodule) :
      f.hom (Representation.IndV.mk A.subtype W.toRepresentation g x) = X.ρ g⁻¹ x := by
    simpa [f] using inducedFromSubrepresentationHom_mk X.ρ A W g x
  have hf_range_top : f.hom.range = ⊤ := by
    have hw_range : w ∈ f.hom.range := by
      rw [Representation.IntertwiningMap.mem_range]
      refine ⟨Representation.IndV.mk A.subtype W.toRepresentation 1 ⟨w, hw⟩, ?_⟩
      simpa using hf_mk 1 ⟨w, hw⟩
    have hrange_ne_bot : f.hom.range ≠ ⊥ := by
      intro hbot
      have : w = 0 := by
        have hw_bot : w ∈ (⊥ : Subrepresentation X.ρ) := by simpa [hbot] using hw_range
        simpa using hw_bot
      exact hw0 this
    exact (IsSimpleOrder.eq_bot_or_eq_top f.hom.range).resolve_left hrange_ne_bot
  have hf_surj : Function.Surjective f.hom.toLinearMap := by
    intro x
    have hx : x ∈ f.hom.range := by
      simpa [hf_range_top] using (show x ∈ (⊤ : Subrepresentation X.ρ) by trivial)
    rw [Representation.IntertwiningMap.mem_range] at hx
    exact hx
  let ι := Quotient (QuotientGroup.rightRel A)
  letI : Fintype (G ⧸ A) := Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype ι := Fintype.ofEquiv (G ⧸ A)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel A).symm
  let v : ι → Y := fun q ↦ Representation.IndV.mk A.subtype W.toRepresentation q.out ⟨w, hw⟩
  let T : Submodule k Y := Submodule.span k (Set.range v)
  have hmk_mem (g : G) (x : W.toSubmodule) :
      Representation.IndV.mk A.subtype W.toRepresentation g x ∈ T := by
    let q : ι := Quotient.mk'' g
    have hrel : QuotientGroup.rightRel A q.out g := by
      apply Quotient.exact'
      simp [q]
    let a : A := ⟨g * q.out⁻¹, by simpa [QuotientGroup.rightRel_apply] using hrel⟩
    have ha : g = (a : G) * q.out := by
      dsimp [a]
      simp [mul_assoc]
    obtain ⟨c, hc⟩ :=
      (finrank_eq_one_iff_of_nonzero' (⟨w, hw⟩ : W.toSubmodule) (by simpa using hw0)).mp hW_dim
        (W.toRepresentation a⁻¹ x)
    have hx :
        Representation.IndV.mk A.subtype W.toRepresentation g x =
          c • Representation.IndV.mk A.subtype W.toRepresentation q.out ⟨w, hw⟩ := by
      calc
      Representation.IndV.mk A.subtype W.toRepresentation g x =
          Representation.IndV.mk A.subtype W.toRepresentation ((a : A) * q.out) x := by
            rw [ha]
      _ = Representation.IndV.mk A.subtype W.toRepresentation q.out (W.toRepresentation a⁻¹ x) := by
            simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]
      _ = c • Representation.IndV.mk A.subtype W.toRepresentation q.out ⟨w, hw⟩ := by
            rw [← hc, (Representation.IndV.mk A.subtype W.toRepresentation q.out).map_smul]
    rw [hx]
    exact Submodule.smul_mem T c (Submodule.subset_span ⟨q, rfl⟩)
  have hmkQ_zero :
      (Submodule.mkQ T : Y →ₗ[k] Y ⧸ T) = 0 := by
    apply Representation.IndV.hom_ext
    intro g
    ext x
    simpa [LinearMap.comp_apply] using (Submodule.Quotient.mk_eq_zero T).2 (hmk_mem g x)
  have hT_top : T = ⊤ := by
    apply top_unique
    intro y _
    have hy : (Submodule.mkQ T : Y →ₗ[k] Y ⧸ T) y = 0 := by
      simp [hmkQ_zero]
    exact (Submodule.Quotient.mk_eq_zero _).1 hy
  letI : FiniteDimensional k T := by
    dsimp [T]
    exact FiniteDimensional.span_of_finite k (Set.finite_range v)
  letI : FiniteDimensional k Y := (LinearEquiv.ofTop T hT_top).finiteDimensional
  calc
    Module.finrank k X ≤ Module.finrank k Y :=
      LinearMap.finrank_le_finrank_of_surjective hf_surj
    _ ≤ Fintype.card ι := by
      exact finrank_le_of_span_eq_top hT_top
    _ = Fintype.card (G ⧸ A) := by
      exact Fintype.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel A)
    _ = A.index := by
      rw [Subgroup.index, Nat.card_eq_fintype_card]

/-- Corollary 3-3.1-2: if `A` is an abelian subgroup of finite index in `G`, then every
irreducible finite-dimensional representation of `G` over an algebraically closed field has degree
at most the index of `A` in `G`. In particular, this applies to abelian subgroups of finite
groups. -/
theorem finrank_le_index_of_commutative_subgroup
    {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    [FiniteDimensional k V] [ρ.IsIrreducible] :
    Module.finrank k V ≤ A.index := by
  let ρ' := uliftRepresentation ρ
  let X : Rep.{max (max u v) w} k G := Rep.of ρ'
  letI : FiniteDimensional k X := by
    simpa [X, ρ'] using (inferInstance : FiniteDimensional k (ULift.{max u v} V))
  letI : X.ρ.IsIrreducible := by
    simpa [X, ρ'] using isIrreducible_uliftRepresentation ρ
  have hX : Module.finrank.{v, max (max u v) w} k (ULift.{max u v} V) ≤ A.index := by
    change Module.finrank.{v, max (max u v) w} k X ≤ A.index
    exact finrank_le_index_of_commutative_subgroup_rep A X
  rw [(ULift.moduleEquiv : ULift.{max u v} V ≃ₗ[k] V).finrank_eq] at hX
  simpa using hX

end

end Representation
