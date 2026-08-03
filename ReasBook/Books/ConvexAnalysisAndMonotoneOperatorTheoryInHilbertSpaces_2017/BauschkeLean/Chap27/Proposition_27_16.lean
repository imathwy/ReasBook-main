import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap06.Example_6_43
import BauschkeLean.Chap06.Proposition_6_19
import BauschkeLean.Chap17.Definition_17_1
import BauschkeLean.Chap27.Proposition_27_8

open Set
open scoped InnerProductSpace Pointwise SetValuedOperator

noncomputable section

universe u

namespace ERealFunction

section AffineConstraints

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall note: `lean_leansearch` only surfaced generic affine-subspace and orthogonal
-- projection owners. The verified project-facing surface for this proposition is the affine
-- translate `AffineSubspace.mk' z V` together with Proposition 27.8 and the affine normal-cone
-- identification from Example 6.43.

/- Source/core/bridge triage:
- `source-facing`: Proposition 27.16 studies minimization of `f` over the affine subspace
  `AffineSubspace.mk' z V`.
- `core/canonical`: Proposition 27.8 is the reusable constrained-minimization owner over a set
  `C`, together with the normal-cone computation for affine subspaces.
- `bridge/view`: `AffineSubspaceConstraintRegularity` is the source regularity hypothesis, and the
  companion theorem `AffineSubspaceConstraintRegularity.toSetConstraintRegularity` converts it to
  the Chapter 27 set-constraint regularity owner.
-/

/-- Helper for Proposition 27.16: a subgradient at `x` bounds every positive directional
increment quotient from below. -/
private theorem inner_le_incrementQuotient_of_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} {x u y : H}
    (hx : x ∈ effectiveDomain f) (hu : u ∈ (∂ f) x)
    {α : ℝ} (hα : 0 < α) :
    (⟪y, u⟫_ℝ : EReal) ≤
      (((f (x + α • y) : EReal) - (f x : EReal)) / α) := by
  have huα :
      (⟪α • y, u⟫_ℝ : EReal) + (f x : EReal) ≤
        (f (x + α • y) : EReal) := by
    -- Evaluate the subgradient inequality at the ray point `x + α • y`.
    simpa using (mem_subdifferential_iff f x u).1 hu (x + α • y)
  by_cases hxy : x + α • y ∈ effectiveDomain f
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hxy_top : (f (x + α • y) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hxy)
    have hxy_bot : (f (x + α • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x + α • y) : EReal) from
        (f (x + α • y)).2)
    have huα_real :
        α * ⟪y, u⟫_ℝ + (f x : EReal).toReal ≤
          (f (x + α • y) : EReal).toReal := by
      -- On the finite branch, rewrite the `EReal` inequality as a real inequality.
      have hcast :
          (((α * ⟪y, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) ≤
            (((f (x + α • y) : EReal).toReal : ℝ) : EReal) := by
        calc
          (((α * ⟪y, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal))
              = (⟪α • y, u⟫_ℝ : EReal) + (f x : EReal) := by
                  rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
                  simp [real_inner_smul_left, EReal.coe_mul]
          _ ≤ (f (x + α • y) : EReal) := huα
          _ = (((f (x + α • y) : EReal).toReal : ℝ) : EReal) := by
                exact (EReal.coe_toReal hxy_top hxy_bot).symm
      exact_mod_cast hcast
    have hquot_real :
        ⟪y, u⟫_ℝ ≤
          ((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α := by
      -- Divide the real inequality by the positive scalar `α`.
      refine (le_div_iff₀ hα).2 ?_
      linarith
    have hquot_cast :
        (⟪y, u⟫_ℝ : EReal) ≤
          ((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
      exact_mod_cast hquot_real
    have hquot_eq :
        (((f (x + α • y) : EReal) - (f x : EReal)) / α) =
          ((((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
      -- Once both endpoint values are finite, the quotient is the cast of the real quotient.
      rw [← EReal.coe_toReal hxy_top hxy_bot, ← EReal.coe_toReal hx_top hx_bot,
        ← EReal.coe_sub, ← EReal.coe_div]
      simp
    rw [hquot_eq]
    exact hquot_cast
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hxy_top : (f (x + α • y) : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hxy))
    have hαE_pos : (0 : EReal) < (α : EReal) := by
      exact_mod_cast hα
    have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top _
    -- Outside the effective domain, the quotient is `⊤`, so the lower bound is automatic.
    rw [hxy_top, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top hαE_pos hα_ne_top]
    exact le_top

/-- Helper for Proposition 27.16: a directional-derivative witness controls every subgradient on
the same direction. -/
private theorem inner_le_directionalWitness_of_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} {x u y : H} {ξ : EReal}
    (hu : u ∈ (∂ f) x) (hξ : HasDirectionalDerivativeAt f x y ξ) :
    (⟪y, u⟫_ℝ : EReal) ≤ ξ := by
  rcases hξ with ⟨hx, htendsto⟩
  have hpoint :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (⟪y, u⟫_ℝ : EReal) ≤
          (((f (x + α • y) : EReal) - (f x : EReal)) / α) := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact inner_le_incrementQuotient_of_mem_subdifferential hx hu hα
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htendsto hpoint

/-- The source regularity hypothesis in Proposition 27.16: the set
`V + cone ({z} - dom f)` is a closed linear subspace, encoded by requiring it to equal its linear
span and for that span to be closed. -/
def AffineSubspaceConstraintRegularity
    (f : H → Set.Ioi (⊥ : EReal)) (V : Submodule ℝ H) (z : H) : Prop :=
  let S : Set H := (V : Set H) + cone (({z} : Set H) - effectiveDomain f)
  S = (Submodule.span ℝ S : Set H) ∧
    IsClosed (((Submodule.span ℝ S : Submodule ℝ H) : Set H))

namespace AffineSubspaceConstraintRegularity

/-- Helper for Proposition 27.16: subtracting `effectiveDomain f` from the affine translate
`AffineSubspace.mk' z V` is the same as adding the translated effective domain `({z} - dom f)` to
the direction subspace `V`. -/
private theorem affineSubspace_sub_effectiveDomain_eq_direction_add_translatedDomain
    {f : H → Set.Ioi (⊥ : EReal)} {V : Submodule ℝ H} {z : H} :
    ((AffineSubspace.mk' z V : Set H) - effectiveDomain f) =
      (V : Set H) + (({z} : Set H) - effectiveDomain f) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_sub.mp hx with ⟨y, hy, w, hw, hxyw⟩
    refine Set.mem_add.mpr ⟨y - z, ?_, z - w, ?_, ?_⟩
    · -- Rewrite affine feasibility as membership in the direction subspace.
      simpa using hy
    · exact Set.mem_sub.mpr ⟨z, by simp, w, hw, rfl⟩
    · calc
        (y - z) + (z - w) = y - w := by abel_nf
        _ = x := hxyw
  · intro hx
    rcases Set.mem_add.mp hx with ⟨v, hv, u, hu, hvu⟩
    rcases Set.mem_sub.mp hu with ⟨z', hz', y, hy, hz'y⟩
    have hz'_eq : z' = z := by simpa using hz'
    subst z'
    refine Set.mem_sub.mpr ⟨v + z, ?_, y, hy, ?_⟩
    · -- Reassemble the affine point from its base point `z` and direction component `v`.
      simpa [AffineSubspace.mem_mk', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hv
    · calc
        (v + z) - y = v + (z - y) := by abel_nf
        _ = v + u := by simp [hz'y]
        _ = x := hvu

/-- Helper for Proposition 27.16: subtracting the translated domain `dom f - {z}` from `V`
normalizes to the same `V + ({z} - dom f)` form that appears in the textbook proof. -/
private theorem sub_translatedEffectiveDomain_eq_direction_add_translatedDomain
    {f : H → Set.Ioi (⊥ : EReal)} {V : Submodule ℝ H} {z : H} :
    (V : Set H) - (effectiveDomain f - ({z} : Set H)) =
      (V : Set H) + (({z} : Set H) - effectiveDomain f) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_sub.mp hx with ⟨v, hv, u, hu, hvu⟩
    rcases Set.mem_sub.mp hu with ⟨y, hy, z', hz', hyz'⟩
    have hz'_eq : z' = z := by simpa using hz'
    subst z'
    refine Set.mem_add.mpr ⟨v, hv, z - y, ?_, ?_⟩
    · exact Set.mem_sub.mpr ⟨z, by simp, y, hy, rfl⟩
    · calc
        v + (z - y) = v - (y - z) := by abel_nf
        _ = v - u := by simp [hyz']
        _ = x := hvu
  · intro hx
    rcases Set.mem_add.mp hx with ⟨v, hv, u, hu, hvu⟩
    rcases Set.mem_sub.mp hu with ⟨z', hz', y, hy, hz'y⟩
    have hz'_eq : z' = z := by simpa using hz'
    subst z'
    refine Set.mem_sub.mpr ⟨v, hv, y - z, ?_, ?_⟩
    · exact Set.mem_sub.mpr ⟨y, hy, z, by simp, rfl⟩
    · calc
        v - (y - z) = v + (z - y) := by abel_nf
        _ = v + u := by simp [hz'y]
        _ = x := hvu

/-- Helper for Proposition 27.16: reflecting the translated domain through the origin reflects its
cone. -/
private theorem cone_translatedDomain_eq_neg_cone_reverseTranslatedDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (z : H) :
    cone (({z} : Set H) - effectiveDomain f) =
      -cone (effectiveDomain f - ({z} : Set H)) := by
  let C : Set H := effectiveDomain f
  have hC_convex : Convex ℝ C := hf.2.convex_effectiveDomain
  have hleft_convex : Convex ℝ (({z} : Set H) - C) := (convex_singleton z).sub hC_convex
  have hright_convex : Convex ℝ (C - ({z} : Set H)) := hC_convex.sub (convex_singleton z)
  ext x
  constructor
  · intro hx
    rw [Set.mem_neg]
    rcases (mem_cone_iff_exists_pos_smul_mem hleft_convex).1 hx with ⟨a, ha, hxmem⟩
    rcases Set.mem_smul_set.mp hxmem with ⟨u, hu, rfl⟩
    rcases Set.mem_sub.mp hu with ⟨z', hz', y, hy, hz'y⟩
    have hz'_eq : z' = z := by simpa using hz'
    subst z'
    have hyz : y - z = -u := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hz'y
    refine (mem_cone_iff_exists_pos_smul_mem hright_convex).2 ⟨a, ha, ?_⟩
    refine Set.mem_smul_set.mpr ⟨y - z, ?_, ?_⟩
    · exact Set.mem_sub.mpr ⟨y, hy, z, by simp, rfl⟩
    · calc
        a • (y - z) = a • (-u) := by simp [hyz]
        _ = -(a • u) := by simp
  · intro hx
    rw [Set.mem_neg] at hx
    rcases (mem_cone_iff_exists_pos_smul_mem hright_convex).1 hx with ⟨a, ha, hxmem⟩
    rcases Set.mem_smul_set.mp hxmem with ⟨u, hu, hu_eq⟩
    rcases Set.mem_sub.mp hu with ⟨y, hy, z', hz', hyz'⟩
    have hz'_eq : z' = z := by simpa using hz'
    subst z'
    have hzy : z - y = -u := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hyz'
    refine (mem_cone_iff_exists_pos_smul_mem hleft_convex).2 ⟨a, ha, ?_⟩
    refine Set.mem_smul_set.mpr ⟨z - y, ?_, ?_⟩
    · exact Set.mem_sub.mpr ⟨z, by simp, y, hy, rfl⟩
    · calc
        a • (z - y) = a • (-u) := by simp [hzy]
        _ = -(a • u) := by simp
        _ = x := by simpa using congrArg Neg.neg hu_eq

/-- Helper for Proposition 27.16: the affine normal-cone witness from Proposition 27.8 is
equivalent to feasibility together with a subgradient orthogonal to `V`. -/
private theorem
    exists_mem_subdifferential_neg_normalCone_affine_iff
    {f : H → Set.Ioi (⊥ : EReal)} {V : Submodule ℝ H} {z xbar : H} :
    (∃ u : H, u ∈ (∂ f) xbar ∧ -u ∈ N[(AffineSubspace.mk' z V : Set H)] xbar) ↔
      xbar ∈ (AffineSubspace.mk' z V : Set H) ∧
        (((∂ f) xbar ∩ (Vᗮ : Set H)).Nonempty) := by
  constructor
  · rintro ⟨u, hu, hneg⟩
    by_cases hxC : xbar ∈ (AffineSubspace.mk' z V : Set H)
    · have hu_orth : u ∈ (Vᗮ : Set H) := by
        have hneg_orth : -u ∈ (Vᗮ : Set H) := by
          simpa [AffineSubspace.direction_mk',
            normalCone_affineSubspace_eq_direction_orthogonal_of_mem
              (AffineSubspace.mk' z V) hxC] using hneg
        simpa using Submodule.neg_mem (Vᗮ) hneg_orth
      exact ⟨hxC, ⟨u, hu, hu_orth⟩⟩
    · rw [normalCone_affineSubspace_eq_empty_of_not_mem (AffineSubspace.mk' z V) hxC] at hneg
      exact hneg.elim
  · rintro ⟨hxC, ⟨u, hu, hu_orth⟩⟩
    have hneg_orth : -u ∈ (Vᗮ : Set H) := by
      simpa using Submodule.neg_mem (Vᗮ) hu_orth
    refine ⟨u, hu, ?_⟩
    simpa [AffineSubspace.direction_mk',
      normalCone_affineSubspace_eq_direction_orthogonal_of_mem
        (AffineSubspace.mk' z V) hxC] using hneg_orth

/-- Helper for Proposition 27.16: together with closedness of `V`, the affine-subspace regularity
hypothesis specializes the set-constrained regularity owner from Proposition 27.8 to the affine
constraint `AffineSubspace.mk' z V`. -/
theorem toSetConstraintRegularity
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {V : Submodule ℝ H} {z : H}
    (_hV_closed : IsClosed (V : Set H))
    (hregular : AffineSubspaceConstraintRegularity f V z) :
    SetConstraintRegularity f (AffineSubspace.mk' z V : Set H) := by
  dsimp [AffineSubspaceConstraintRegularity] at hregular
  rcases hregular with ⟨hsubspace, hsubspace_closed⟩
  have htranslated_nonempty :
      (effectiveDomain f - ({z} : Set H)).Nonempty := by
    rcases hf.2.nonempty with ⟨x, hx⟩
    exact ⟨x - z, Set.mem_sub.mpr ⟨x, hx, z, by simp, rfl⟩⟩
  have htranslated_convex :
      Convex ℝ (effectiveDomain f - ({z} : Set H)) := by
    exact hf.2.convex_effectiveDomain.sub (convex_singleton z)
  have hregular_sri :
      strongRelativeInteriorSubImageRegularity
        (effectiveDomain f - ({z} : Set H))
        (V : Set H)
        (ContinuousLinearMap.id ℝ H) := by
    -- Route correction: use Proposition 6.19 branch `(iii)` on the translated domain `dom f - {z}`.
    have hcone_eq :
        (V : Set H) - cone (effectiveDomain f - ({z} : Set H)) =
          (V : Set H) + cone (({z} : Set H) - effectiveDomain f) := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_sub.mp hx with ⟨v, hv, u, hu, hvu⟩
        refine Set.mem_add.mpr ⟨v, hv, -u, ?_, ?_⟩
        · have hneg_u : -u ∈ cone (({z} : Set H) - effectiveDomain f) := by
            rw [cone_translatedDomain_eq_neg_cone_reverseTranslatedDomain hf z, Set.mem_neg]
            simpa using hu
          exact hneg_u
        · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hvu
      · intro hx
        rcases Set.mem_add.mp hx with ⟨v, hv, u, hu, hvu⟩
        refine Set.mem_sub.mpr ⟨v, hv, -u, ?_, ?_⟩
        · have hneg_u : -u ∈ cone (effectiveDomain f - ({z} : Set H)) := by
            rw [cone_translatedDomain_eq_neg_cone_reverseTranslatedDomain hf z, Set.mem_neg] at hu
            exact hu
          exact hneg_u
        · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hvu
    have hbranch :
        IsCone (V : Set H) ∧
          ((V : Set H) - cone (effectiveDomain f - ({z} : Set H)) =
            (Submodule.span ℝ ((V : Set H) - cone (effectiveDomain f - ({z} : Set H))) :
              Set H)) ∧
          IsClosed
            (((Submodule.span ℝ ((V : Set H) - cone (effectiveDomain f - ({z} : Set H))) :
              Submodule ℝ H) : Set H)) := by
      refine ⟨Set.submodule_isCone V, ?_, ?_⟩
      · -- Rewrite the branch-(iii) subspace condition into the textbook regularity hypothesis.
        calc
          (V : Set H) - cone (effectiveDomain f - ({z} : Set H))
              = (V : Set H) + cone (({z} : Set H) - effectiveDomain f) := hcone_eq
          _ = (Submodule.span ℝ ((V : Set H) + cone (({z} : Set H) - effectiveDomain f)) :
                Set H) := hsubspace
          _ = (Submodule.span ℝ ((V : Set H) - cone (effectiveDomain f - ({z} : Set H))) :
                Set H) := by rw [hcone_eq]
      · -- Closedness of the span is exactly the second half of the given regularity hypothesis.
        convert hsubspace_closed using 1
        rw [hcone_eq]
    dsimp [strongRelativeInteriorSubImageRegularity]
    right
    right
    left
    simpa using hbranch
  have hsri_id :
      (0 : H) ∈ sri
        ((V : Set H) - ((ContinuousLinearMap.id ℝ H) '' (effectiveDomain f - ({z} : Set H)))) :=
    zero_mem_strongRelativeInterior_sub_image_of_regularity
      htranslated_nonempty
      ⟨0, V.zero_mem⟩
      htranslated_convex
      V.convex
      (ContinuousLinearMap.id ℝ H)
      hregular_sri
  have hsri :
      (0 : H) ∈ sri ((V : Set H) - (effectiveDomain f - ({z} : Set H))) := by
    simpa using hsri_id
  have hsri_translated := hsri
  rw [sub_translatedEffectiveDomain_eq_direction_add_translatedDomain] at hsri_translated
  have hsri_affine := hsri_translated
  rw [← affineSubspace_sub_effectiveDomain_eq_direction_add_translatedDomain] at hsri_affine
  exact SetConstraintRegularity.zero_mem_sri hsri_affine

end AffineSubspaceConstraintRegularity

/-- Helper for Proposition 27.16: under the closed-subspace and regularity hypotheses, `xbar`
minimizes `f` over the affine subspace `z + V` if and only if it is feasible and the
subdifferential fiber `∂ f(xbar)` meets the orthogonal complement `Vᗮ`. -/
theorem mem_argmin_affineSubspace_iff
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (V : Submodule ℝ H) (hV_closed : IsClosed (V : Set H)) {z : H}
    (hregular : AffineSubspaceConstraintRegularity f V z) {xbar : H} :
    xbar ∈ Argmin[(AffineSubspace.mk' z V : Set H)] f.asEReal ↔
      xbar ∈ (AffineSubspace.mk' z V : Set H) ∧
        (((∂ f) xbar ∩ (Vᗮ : Set H)).Nonempty) := by
  have hC_closed : IsClosed ((AffineSubspace.mk' z V : Set H)) := by
    -- Closedness of the affine translate is equivalent to closedness of its direction.
    exact
      (AffineSubspace.isClosed_direction_iff (AffineSubspace.mk' z V)).mp
        (by simpa [AffineSubspace.direction_mk'] using hV_closed)
  have hC_convex : Convex ℝ ((AffineSubspace.mk' z V : Set H)) :=
    (AffineSubspace.mk' z V).convex
  have hsetRegular :
      SetConstraintRegularity f (AffineSubspace.mk' z V : Set H) :=
    AffineSubspaceConstraintRegularity.toSetConstraintRegularity hf hV_closed hregular
  -- Pass from the constrained argmin criterion to the affine normal-cone witness and then rewrite
  -- that witness as orthogonality to `V`.
  calc
    xbar ∈ Argmin[(AffineSubspace.mk' z V : Set H)] f.asEReal ↔
        xbar ∈ ((N[(AffineSubspace.mk' z V : Set H)]) + (∂ f)).zeros := by
          exact
            mem_argminOn_iff_mem_zeros_normalCone_add_subdifferential_of_regularity
              hf
              hC_closed
              hC_convex
              hsetRegular
    _ ↔ ∃ u : H, u ∈ (∂ f) xbar ∧ -u ∈ N[(AffineSubspace.mk' z V : Set H)] xbar := by
      exact mem_zeros_normalCone_add_subdifferential_iff_exists_mem_subdifferential_neg
    _ ↔ xbar ∈ (AffineSubspace.mk' z V : Set H) ∧
          (((∂ f) xbar ∩ (Vᗮ : Set H)).Nonempty) := by
      exact
        AffineSubspaceConstraintRegularity.exists_mem_subdifferential_neg_normalCone_affine_iff

/-- Helper for Proposition 27.16: if every directional derivative of `f` at `xbar` is represented
by `gradf`, then the subdifferential fiber `(∂ f) xbar` is the singleton `{gradf}`. -/
private theorem directionalDerivativeDataSubdifferentialSingleton
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {xbar gradf : H}
    (hgrad :
      ∀ y : H,
        HasDirectionalDerivativeAt f xbar y
          ((((InnerProductSpace.toDualMap ℝ H gradf) y : ℝ) : EReal))) :
    (∂ f) xbar = ({gradf} : Set H) := by
  have hconv : ConvexOn f (effectiveDomain f) := (mem_gammaZero_iff.mp hf).2
  have hxbar : xbar ∈ effectiveDomain f := (hgrad 0).1
  have hgrad_mem : gradf ∈ (∂ f) xbar := by
    -- The directional-derivative formula gives the affine minorant inequality for `gradf`.
    rw [mem_subdifferential_iff]
    intro z
    have hdir :
        directionalDerivative f xbar (z - xbar) = (⟪z - xbar, gradf⟫_ℝ : EReal) := by
      simpa [real_inner_comm] using
        (directionalDerivative_eq_of_hasDirectionalDerivativeAt
          (f := f) hconv (hgrad (z - xbar)))
    calc
      (⟪z - xbar, gradf⟫_ℝ : EReal) + (f xbar : EReal)
          = directionalDerivative f xbar (z - xbar) + (f xbar : EReal) := by rw [hdir]
      _ ≤ (f z : EReal) := directionalDerivative_add_value_le (f := f) hxbar z
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨hgrad_mem, ?_⟩
  · intro u hu
    -- Any other subgradient has the same inner products against every direction, hence is equal
    -- to `gradf`.
    apply ext_inner_left ℝ
    intro y
    have hu_y :
        (⟪y, u⟫_ℝ : EReal) ≤ ((((InnerProductSpace.toDualMap ℝ H gradf) y : ℝ) : EReal)) := by
      exact inner_le_directionalWitness_of_mem_subdifferential hu (hgrad y)
    have hu_neg :
        (⟪-y, u⟫_ℝ : EReal) ≤
          ((((InnerProductSpace.toDualMap ℝ H gradf) (-y) : ℝ) : EReal)) := by
      exact inner_le_directionalWitness_of_mem_subdifferential hu (hgrad (-y))
    have hu_y_real : ⟪y, u⟫_ℝ ≤ ⟪y, gradf⟫_ℝ := by
      simpa [real_inner_comm] using EReal.coe_le_coe_iff.mp hu_y
    have hu_neg_real : ⟪y, gradf⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
      simpa [real_inner_comm] using EReal.coe_le_coe_iff.mp hu_neg
    exact le_antisymm hu_y_real hu_neg_real

/-- Proposition 27.16. Under the same closed-subspace and regularity hypotheses, if every
directional derivative of `f` at `xbar` is represented by `gradf`, then the proposition
specializes to the feasibility condition together with the orthogonality condition
`gradf ∈ Vᗮ`, i.e. `∇ f(xbar) ⟂ V`. -/
theorem mem_argmin_affineSubspace_iff_grad_mem_orthogonal
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (V : Submodule ℝ H) (hV_closed : IsClosed (V : Set H)) {z : H}
    (hregular : AffineSubspaceConstraintRegularity f V z)
    {xbar gradf : H}
    (hgrad :
      ∀ y : H,
        HasDirectionalDerivativeAt f xbar y
          ((((InnerProductSpace.toDualMap ℝ H gradf) y : ℝ) : EReal))) :
    xbar ∈ Argmin[(AffineSubspace.mk' z V : Set H)] f.asEReal ↔
      xbar ∈ (AffineSubspace.mk' z V : Set H) ∧ gradf ∈ (Vᗮ : Set H) := by
  have hsingle : (∂ f) xbar = ({gradf} : Set H) := by
    -- The directional-derivative data identifies the whole subdifferential fiber with `gradf`.
    exact directionalDerivativeDataSubdifferentialSingleton hf hgrad
  have horth :
      (((∂ f) xbar ∩ (Vᗮ : Set H)).Nonempty) ↔ gradf ∈ (Vᗮ : Set H) := by
    constructor
    · rintro ⟨u, hu_sub, hu_orth⟩
      -- Any witness in the intersection must equal `gradf` after the singleton collapse.
      rw [hsingle] at hu_sub
      have hu_eq : u = gradf := by simpa using hu_sub
      simpa [hu_eq] using hu_orth
    · intro hgrad_orth
      -- Conversely, `gradf` itself provides the required intersection witness.
      refine ⟨gradf, ?_, hgrad_orth⟩
      rw [hsingle]
      simp
  -- Reuse the affine-subgradient criterion and normalize its final clause with the singleton API.
  rw [mem_argmin_affineSubspace_iff hf V hV_closed hregular]
  constructor
  · rintro ⟨hxbar, hnonempty⟩
    exact ⟨hxbar, horth.mp hnonempty⟩
  · rintro ⟨hxbar, hgrad_orth⟩
    exact ⟨hxbar, horth.mpr hgrad_orth⟩

end AffineConstraints

end ERealFunction
