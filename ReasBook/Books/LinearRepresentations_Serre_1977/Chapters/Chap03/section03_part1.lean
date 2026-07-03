import Mathlib
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_3_3_1_2 (from Chap03) -/
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

/-! ### Exercise_3_3_1_3 (from Chap03) -/
-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's exercise says that an irreducible finite-dimensional complex
--   representation of an abelian group has degree `1`.
-- * core/canonical: this is exactly the mathlib owner theorem
--   `Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`.
-- * bridge/view: none is needed here, since the source statement is a direct specialization of the
--   canonical owner theorem rather than an additional construction.
--
-- Primitive data are only a representation `ρ`, its irreducibility, finite-dimensionality over an
-- algebraically closed field, and the commutativity hypothesis on the group. The degree-one
-- conclusion is derived directly from the owner theorem, so a pure `recall` item is the canonical
-- surface.
/- Exercise 3-3.1-3: a finite-dimensional irreducible complex representation of an abelian group
has degree `1`; this is the existing theorem
`Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`, which does not assume the group
is finite. -/
recall Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative

/-! ### Exercise_3_3_1_4 (from Chap03) -/
universe u v

namespace Representation

section

open scoped BigOperators
open IntertwiningMap

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]

-- Source/core/bridge triage: this item is `source-facing`. The primitive data are the
-- irreducible finite-dimensional representation `ρ` and the central element `s`. The owner
-- abstraction is the canonical intertwining endomorphism `centralMul ρ s hs`; Schur's lemma from
-- Chapter 2 is the `core/canonical` input, and forgetting the intertwining map back to the
-- underlying endomorphism is the only `bridge/view` step.
-- Proof sketch: `IntertwiningMap.centralMul s hs` is the canonical intertwining endomorphism
-- attached to the central action of `s`; then apply the Chapter 2 owner theorem
-- `Representation.intertwiningMap_eq_smul_id` and forget back to the underlying endomorphism.
/-- Exercise 3-3.1-4 (1): in an irreducible finite-dimensional representation over an
algebraically closed field, every central element acts by a homothety. -/
theorem exists_smul_id_of_mem_center (s : G) (hs : s ∈ Submonoid.center G) :
    ∃ z : k, ρ s = z • 1 := by
  obtain ⟨z, hz⟩ := intertwiningMap_eq_smul_id ρ (centralMul ρ s hs)
  exact ⟨z, by simpa using congrArg toLinearMap hz⟩

end

section

variable {G : Type u} [Monoid G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V) [ρ.IsIrreducible]

-- Source/core/bridge triage: this item is `source-facing`. The primitive data are again `ρ`, the
-- central finite-order element `s`, and its order hypothesis. The scalar-action owner remains
-- `centralMul ρ s hs` together with Chapter 2 Schur; `Representation.character` and
-- `Representation.char_one` provide the canonical character-level bridge from scalar action to the
-- stated norm identity.
-- Proof sketch: use `centralMul ρ s hs` and `intertwiningMap_eq_smul_id` to write
-- `ρ s = z • 1`; then `ρ.character s = z * Module.finrank ℂ V`. If `s` has finite order, then so
-- does `ρ s`, hence the scalar `z` has norm `1`; taking norms yields the claimed equality.
/-- Exercise 3-3.1-4 (2): if `s` is a central finite-order element, then the norm of the character
value `χ(s)` equals the degree of the irreducible representation. -/
theorem norm_character_eq_finrank_of_mem_center (s : G) (hs : s ∈ Submonoid.center G)
    (hsfin : IsOfFinOrder s) :
    ‖ρ.character s‖ = (Module.finrank ℂ V : ℝ) :=
  (character_norm_eq_char_one_iff_exists_smul_id ρ s hsfin).2 <|
    exists_smul_id_of_mem_center ρ s hs

end

section

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

-- Source/core/bridge triage: this item is `source-facing`. Its primitive data are the irreducible
-- complex representation `ρ`; the square bound is the textbook statement proved directly from
-- character orthogonality. The later Chapter 6 theorem `finrank_dvd_center_index` is a
-- complementary divisibility sharpening, but it does not replace this earlier square-inequality
-- statement.
-- Proof sketch: derive the finite-dimensionality of `V` from the owner theorem
-- `IsIrreducible.finiteDimensional_of_finite`, then start from the orthogonality relation
-- `Representation.card_inv_mul_sum_char_mul_char_eq_finrank` specialized to `ρ = σ`, so the sum
-- of `‖ρ.character s‖ ^ 2` over `G` is `Nat.card G`; then apply
-- `norm_character_eq_finrank_of_mem_center` to each central element using
-- `isOfFinOrder_of_finite s` and compare the contribution of the center with the canonical index
-- `(Subgroup.center G).index = [G : Z(G)]`.
/-- Exercise 3-3.1-4 (3): the square of the degree of an irreducible complex representation is at
most the index of the center. -/
theorem finrank_sq_le_center_index (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Module.finrank ℂ V ^ 2 ≤ (Subgroup.center G).index := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  have hsum :
      ∑ s : G, Complex.normSq (ρ.character s) = Nat.card G := by
    have hterm :
        Finset.univ.sum (fun s : G ↦ (Complex.normSq (ρ.character s) : ℂ)) =
          Finset.univ.sum (fun s : G ↦ ρ.character s * ρ.character s⁻¹) := by
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [ρ.char_inv_eq_star_of_isOfFinOrder s (isOfFinOrder_of_finite s)]
      simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj' (ρ.character s)).symm
    apply Complex.ofReal_injective
    calc
      ((∑ s : G, Complex.normSq (ρ.character s) : ℝ) : ℂ)
          = ∑ s : G, ρ.character s * ρ.character s⁻¹ := by
              simpa using hterm
      _ = Nat.card G := by
            have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
              exact_mod_cast Nat.card_pos.ne'
            letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
            have hortho :
                (Nat.card G : ℂ)⁻¹ * ∑ s : G, ρ.character s * ρ.character s⁻¹ = 1 := by
              rw [ρ.card_inv_mul_sum_char_mul_char_eq_finrank,
                Representation.IsIrreducible.finrank_intertwiningMap_self ρ]
              norm_num
            apply_fun (fun z : ℂ ↦ z * (Nat.card G : ℂ)) at hortho
            simpa [hcard_ne, mul_comm, mul_left_comm, mul_assoc] using hortho
  have hcenter_sum :
      ∑ s : Subgroup.center G, Complex.normSq (ρ.character s) =
        Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 := by
    have hcenter_term (s : Subgroup.center G) :
        Complex.normSq (ρ.character s) = Module.finrank ℂ V ^ 2 := by
      rw [Complex.normSq_eq_norm_sq,
        norm_character_eq_finrank_of_mem_center ρ s
          (show (s : G) ∈ Submonoid.center G from by
            simpa [Subgroup.center_toSubmonoid] using s.2)
          (show IsOfFinOrder (s : G) from by
            let t : G := s
            have ht : IsOfFinOrder t := isOfFinOrder_of_finite t
            simpa [t] using ht)]
    calc
      ∑ s : Subgroup.center G, Complex.normSq (ρ.character s)
          = ∑ _ : Subgroup.center G, Module.finrank ℂ V ^ 2 := by
              simp [hcenter_term]
      _ = Fintype.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 := by
            simp [mul_comm]
      _ = Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 := by
            rw [Nat.card_eq_fintype_card]
  have hcenter_le :
      (Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 : ℝ) ≤ Nat.card G := by
    have hnonneg :
        0 ≤ (Finset.univ.filter (fun s : G ↦ s ∉ Subgroup.center G)).sum
          (fun s ↦ Complex.normSq (ρ.character s)) := by
      exact Finset.sum_nonneg fun s _ ↦ Complex.normSq_nonneg (ρ.character s)
    calc
      (Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 : ℝ)
          = (Finset.univ.filter (fun s : G ↦ s ∈ Subgroup.center G)).sum
              (fun s ↦ Complex.normSq (ρ.character s)) := by
                rw [← Finset.sum_subtype_eq_sum_filter]
                simpa using hcenter_sum.symm
      _ ≤
          (Finset.univ.filter (fun s : G ↦ s ∈ Subgroup.center G)).sum
              (fun s ↦ Complex.normSq (ρ.character s)) +
            (Finset.univ.filter (fun s : G ↦ s ∉ Subgroup.center G)).sum
              (fun s ↦ Complex.normSq (ρ.character s)) := by
            exact le_add_of_nonneg_right hnonneg
      _ = ∑ s : G, Complex.normSq (ρ.character s) := by
            simpa using
              (Finset.univ.sum_filter_add_sum_filter_not
                (fun s : G ↦ s ∈ Subgroup.center G)
                (fun s ↦ Complex.normSq (ρ.character s)))
      _ = Nat.card G := hsum
  have hcenter_le_nat :
      Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 ≤ Nat.card G := by
    exact_mod_cast hcenter_le
  have hmul :
      Nat.card (Subgroup.center G) * Module.finrank ℂ V ^ 2 ≤
        Nat.card (Subgroup.center G) * (Subgroup.center G).index := by
    rw [Subgroup.card_mul_index]
    exact hcenter_le_nat
  exact Nat.le_of_mul_le_mul_left hmul Nat.card_pos

end

section

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]

-- Proof sketch: first derive `FiniteDimensional k V` from
-- `IsIrreducible.finiteDimensional_of_finite ρ`. For `s ∈ Subgroup.center G`,
-- `exists_smul_id_of_mem_center ρ s hs` writes `ρ s` as `z • 1`; faithfulness identifies `s` with
-- the scalar `z`, so `Subgroup.center G` injects into `kˣ`. The canonical owner theorem
-- `isCyclic_of_injective_ringHom` then implies that this finite subgroup of the unit group of the
-- commutative field `k` is cyclic.
/-- Exercise 3-3.1-4 (4): the center of a finite group admitting a faithful irreducible
representation over an algebraically closed field is cyclic. -/
theorem center_isCyclic_of_faithful (hfaithful : Function.Injective ρ) :
    IsCyclic (Subgroup.center G) := by
  classical
  by_cases hV : Subsingleton V
  · have hG : Subsingleton G := by
      refine ⟨fun g h ↦ hfaithful ?_⟩
      ext x
      exact hV.elim _ _
    infer_instance
  · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
    let v : V := Classical.choose (exists_ne (0 : V))
    have hv : v ≠ 0 := Classical.choose_spec (exists_ne (0 : V))
    have hsmul_injective : Function.Injective fun z : k ↦ z • (1 : Module.End k V) := by
      intro z w hzw
      have hvw : z • v = w • v := by
        simpa using congrArg (fun f : Module.End k V ↦ f v) hzw
      have hsub : (z - w) • v = 0 := by
        rw [sub_smul, hvw, sub_self]
      rcases smul_eq_zero.mp hsub with hzero | hzero
      · exact sub_eq_zero.mp hzero
      · exact (hv hzero).elim
    let scalar : Subgroup.center G → k := fun s ↦
      Classical.choose <|
        exists_smul_id_of_mem_center ρ (s : G)
          (show (s : G) ∈ Submonoid.center G from by
            simpa [Subgroup.center_toSubmonoid] using s.2)
    have hscalar (s : Subgroup.center G) :
        ρ (s : G) = scalar s • (1 : Module.End k V) := by
      simpa [scalar] using
        (Classical.choose_spec <|
          exists_smul_id_of_mem_center ρ (s : G)
            (show (s : G) ∈ Submonoid.center G from by
              simpa [Subgroup.center_toSubmonoid] using s.2))
    let φ : Subgroup.center G →* k :=
      { toFun := scalar
        map_one' := by
          apply hsmul_injective
          calc
            scalar 1 • (1 : Module.End k V) = ρ (1 : G) := (hscalar 1).symm
            _ = (1 : k) • (1 : Module.End k V) := by simp
        map_mul' := by
          intro s t
          apply hsmul_injective
          calc
            scalar (s * t) • (1 : Module.End k V) = ρ (s * t : G) := (hscalar (s * t)).symm
            _ = ρ (s : G) * ρ (t : G) := by simp
            _ = (scalar s * scalar t) • (1 : Module.End k V) := by
                  rw [hscalar s, hscalar t]
                  ext x
                  simp [smul_smul, mul_comm] }
    have hφ_injective : Function.Injective φ := by
      intro s t hst
      apply Subtype.ext
      apply hfaithful
      calc
        ρ (s : G) = scalar s • (1 : Module.End k V) := hscalar s
        _ = φ t • (1 : Module.End k V) := by simpa [hst]
        _ = ρ (t : G) := (hscalar t).symm
    exact isCyclic_of_injective_ringHom φ hφ_injective

end

end Representation

/-! ### Exercise_3_3_1_5 (from Chap03) -/
/-
Domain-style sampling:
* primary domain: Pontryagin duality for finite abelian groups via additive characters.
* sampled owner declarations in this domain:
  `AddChar.doubleDualEmb`,
  `AddChar.doubleDualEquiv`,
  `AddChar.doubleDualEmb_injective`,
  `AddChar.card_eq`.
* best owner abstraction: the existing `AddChar` double-dual API from mathlib, already reused by
  the chapter-level file `LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_1_5`.

Primitive data versus derived API:
* primitive owner data: the canonical evaluation morphism into the double dual.
* derived API: the finite-group double-dual equivalence, its injectivity consequence, and the
  cardinality equality for the dual group.

Source/core/bridge triage:
* `source-facing`: Exercise `3-3.1-5` as a recall of the canonical double-dual statements for
  finite abelian groups.
* `core/canonical`: the `AddChar` owner declarations listed above, as surfaced in
  `LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_1_5`.
* `bridge/view`: this item file is only a thin recall layer reusing the chapter-level owner file
  rather than restating the same recalls from scratch.
-/

/- The evaluation map `x ↦ (χ ↦ χ x)` into the dual of the dual is the canonical double-dual
embedding. -/
recall AddChar.doubleDualEmb

/- Exercise 3-3.1-5: using Theorem 3-3.1-1 to identify the irreducible complex characters of the
finite abelian group `G` with the complex characters `AddChar (Additive G) ℂ`, Pontryagin duality
gives the canonical double-dual isomorphism `Additive G ≃+ AddChar (AddChar (Additive G) ℂ) ℂ`. -/
recall AddChar.doubleDualEquiv

/- The canonical evaluation homomorphism into the double dual is injective. -/
recall AddChar.doubleDualEmb_injective

/- The dual group of a finite abelian group has the same cardinality as the group itself. -/
recall AddChar.card_eq

/-! ### Theorem_3_3_1_1 (from Chap03) -/
universe u v

namespace Representation

section

open CategoryTheory

private def uliftRepresentation
    {G k V : Type} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    Representation k G (ULift.{v} V) where
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
    {G k V : Type} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    ρ.Equiv (uliftRepresentation ρ) :=
  Representation.Equiv.mk ULift.moduleEquiv.symm fun g ↦ by
    ext x
    rfl

private theorem isIrreducible_uliftRepresentation
    {G k V : Type} [Monoid G] [Finite G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    (uliftRepresentation ρ).IsIrreducible := by
  exact isIrreducible_of_nonempty_equiv ⟨uliftRepresentationEquiv ρ⟩

variable {G : Type} [Group G] [Finite G]

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's criterion that a finite group is abelian exactly when all irreducible
--   complex representations have degree `1`, using the Chapter 1 owner
--   `Representation.IsIrreducible`.
-- * core/canonical: the complete-family arguments run through the bundled owner `FDRep ℂ G`,
--   where irreducibility is expressed by `Simple`, together with the Chapter 2 owner theorem
--   `isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card`.
-- * bridge/view: `FDRep.of` packages a finite-dimensional representation into the canonical
--   `FDRep` owner; the owner theorem `FDRep.isIrreducible_of_simple` moves back from a simple
--   bundled object to the source-facing irreducibility predicate.
--
-- Primitive data are only the finite group `G` and an irreducible representation
-- `ρ : Representation k G V`. The finite-dimensionality bridge is derived internally, at the
-- owner layer `Representation.IsIrreducible`, from the finite orbit of a nonzero vector; the
-- `FDRep`/`Simple` layer is used only internally when a complete irreducible family is chosen for
-- the reverse implication, and `Representation.Equiv.toFDRepIso` is the only bridge needed
-- between the source-facing and bundled owner layers.
-- Proof sketch: for the forward implication, apply
-- `Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative` after inserting the derived
-- finite-dimensionality instance for `ρ`. For the reverse implication, choose a complete family
-- of irreducible complex representations in `FDRep ℂ G`, transport their simplicity to
-- `Representation.IsIrreducible`, use Chapter 2's owner theorem
-- `isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card` to recover completeness from the
-- square-degree sum, then combine Chapter 2's formulas
-- `sum_sq_degree_eq_card_of_complete_irreducible_family` and
-- `card_eq_card_conjClasses_of_complete_irreducible_family`, rewrite the latter equality as
-- `commProb G = 1` via `commProb_def'`, and conclude with `commProb_eq_one_iff`.

/-- Theorem 3-3.1-1: a finite group `G` is abelian if and only if every irreducible complex
representation of `G` has degree `1`. -/
theorem isMulCommutative_iff_forall_irreducible_finrank_eq_one :
    IsMulCommutative G ↔
      ∀ {V : Type v} [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V) [ρ.IsIrreducible], Module.finrank ℂ V = 1 := by
  constructor
  · intro hG V _ _ ρ _
    letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
    letI : IsMulCommutative G := hG
    exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  · intro h
    classical
    let _ : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
    obtain ⟨ι, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
        ∃ (ι : Type) (_ : Fintype ι) (σ : ι → Subrepresentation (leftRegular ℂ G)),
          iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
            (⨆ i, (σ i).toSubmodule) = ⊤ ∧
            ∀ i, (σ i).toRepresentation.IsIrreducible :=
      exists_isInternal_irreducible_subrepresentations (leftRegular ℂ G)
    let _ : Finite ι := inferInstance
    let _ : Fintype ι := Fintype.ofFinite ι
    let π : ι → FDRep ℂ G := fun i ↦ FDRep.of (σ i).toRepresentation
    let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
    have hπ_finrank (i : ι) : Module.finrank ℂ (π i) = 1 := by
      letI : (uliftRepresentation (σ i).toRepresentation).IsIrreducible :=
        isIrreducible_uliftRepresentation (σ i).toRepresentation
      simpa [π, finrank_ulift] using h (uliftRepresentation (σ i).toRepresentation)
    have hσ_finrank (i : ι) : Module.finrank ℂ (σ i).toSubmodule = 1 := by
      simpa [π] using hπ_finrank i
    have hπ_pairwise : PairwiseNonisomorphic π := by
      intro i j hij hijIso
      have hmult :
          Nat.card { t // Nonempty ((σ t).toRepresentation.Equiv (σ i).toRepresentation) } = 1 := by
        letI : (σ i).toRepresentation.IsIrreducible := hσ_irr i
        calc
          Nat.card { t // Nonempty ((σ t).toRepresentation.Equiv (σ i).toRepresentation) } =
              Module.finrank ℂ (σ i).toSubmodule := by
                simpa using
                  leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr
                    (σ i).toRepresentation inferInstance
          _ = 1 := hσ_finrank i
      have hcard :
          Fintype.card { t // Nonempty ((σ t).toRepresentation.Equiv (σ i).toRepresentation) } =
            1 := by
        simpa [Nat.card_eq_fintype_card] using hmult
      rcases Fintype.card_eq_one_iff.mp hcard with ⟨a, ha⟩
      have hi :
          (⟨i, ⟨Representation.Equiv.refl (σ i).toRepresentation⟩⟩ :
            { t // Nonempty ((σ t).toRepresentation.Equiv (σ i).toRepresentation) }) = a := ha _
      have hjRep : Nonempty ((σ j).toRepresentation.Equiv (σ i).toRepresentation) := by
        rcases hijIso with ⟨e⟩
        exact ⟨(Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)).symm⟩
      have hj :
          (⟨j, hjRep⟩ :
            { t // Nonempty ((σ t).toRepresentation.Equiv (σ i).toRepresentation) }) = a := ha _
      exact hij <| by simpa using hi.trans hj.symm
    have hπ_simple (i : ι) : CategoryTheory.Simple (π i) := by
      letI : Representation.IsIrreducible (π i).ρ := by
        simpa [π] using hσ_irr i
      exact FDRep.simple_of_isIrreducible (π i)
    have hπ_sum :
        ∑ i : ι, Module.finrank ℂ (π i) ^ 2 = Nat.card G := by
      have hsum_dims : ∑ i : ι, Module.finrank ℂ (σ i).toSubmodule = Nat.card G := by
        letI := DirectSum.IsInternal.chooseDecomposition (fun i ↦ (σ i).toSubmodule) hinternal
        let e := (DirectSum.decomposeLinearEquiv (fun i ↦ (σ i).toSubmodule)).symm
        calc
          ∑ i : ι, Module.finrank ℂ (σ i).toSubmodule = Module.finrank ℂ (G →₀ ℂ) := by
            symm
            calc
              Module.finrank ℂ (G →₀ ℂ) =
                  Module.finrank ℂ (DirectSum ι fun i ↦ (σ i).toSubmodule) := by
                    exact e.finrank_eq.symm
              _ = ∑ i : ι, Module.finrank ℂ (σ i).toSubmodule := by
                    simp [Module.finrank_directSum]
          _ = Nat.card G := by
            let _ : Fintype G := Fintype.ofFinite G
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self ℂ
      calc
        ∑ i : ι, Module.finrank ℂ (π i) ^ 2 = ∑ i : ι, 1 := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hπ_finrank i]
          simp
        _ = ∑ i : ι, Module.finrank ℂ (σ i).toSubmodule := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact (hσ_finrank i).symm
        _ = Nat.card G := hsum_dims
    have hπ_complete : IsCompleteIrreducibleFamily π := by
      exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum
    have hcard_ι : Nat.card ι = Nat.card G := by
      calc
        Nat.card ι = Fintype.card ι := Nat.card_eq_fintype_card
        _ = ∑ i : ι, 1 := by simp
        _ = ∑ i : ι, Module.finrank ℂ (π i) ^ 2 := by
              symm
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [hπ_finrank i]
              simp
        _ = Nat.card G := hπ_sum
    have hconj : Nat.card (ConjClasses G) = Nat.card G := by
      calc
        Nat.card (ConjClasses G) = Nat.card ι := by
          symm
          exact
            card_eq_card_conjClasses_of_complete_irreducible_family
              π (fun i ↦ hπ_complete.isSimple i) hπ_pairwise
              (fun τ hτ ↦ hπ_complete.exists_iso τ hτ)
        _ = Nat.card G := hcard_ι
    have hcommProb : commProb G = 1 := by
      rw [commProb_def', hconj, div_self]
      exact_mod_cast Nat.card_pos.ne'
    exact (commProb_eq_one_iff).mp hcommProb

end

end Representation
