import Mathlib
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap12.Definition_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise InnerProductSpace

universe u

namespace ERealFunction

section Domain

variable {H : Type u} [AddCommGroup H]

/-- Companion theorem: for `]-∞,+∞]`-valued functions on an additive commutative group, the
domain of the infimal convolution is the Minkowski sum of the effective domains. -/
-- Proof sketch: rewrite `(f □ g) x` as an infimum over decompositions `x = y + z`. A finite
-- decomposition shows `x ∈ dom (f □ g)`, while a finite infimal-convolution value together
-- with the
-- no-`⊥` hypotheses yields a decomposition with both summands in the corresponding domains.
theorem dom_infimalConvolution
    (f g : H → Set.Ioi (⊥ : EReal)) :
    dom (f □ g) =
      effectiveDomain f + effectiveDomain g := by
  ext x
  constructor
  · intro hx
    -- A finite infimal-convolution value forces some decomposition with both summands finite.
    by_contra hxsum
    rw [mem_dom_iff_ne_top, infimalConvolution_apply] at hx
    have htop : (⨅ y : H, (f y : EReal) + (g (x - y) : EReal)) = ⊤ := by
      refine iInf_eq_top.2 ?_
      intro y
      by_cases hy : y ∈ effectiveDomain f
      · have hxy : x - y ∉ effectiveDomain g := by
          intro hxy
          have hdecomp : y + (x - y) = x := by
            simp
          exact hxsum <| Set.mem_add.2 ⟨y, hy, x - y, hxy, hdecomp⟩
        have hgy_top : (g (x - y) : EReal) = ⊤ := by
          rw [mem_effectiveDomain_iff] at hxy
          exact le_antisymm le_top (not_lt.mp hxy)
        rw [hgy_top]
        exact EReal.add_top_of_ne_bot (ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2))
      · have hfy_top : (f y : EReal) = ⊤ := by
          rw [mem_effectiveDomain_iff] at hy
          exact le_antisymm le_top (not_lt.mp hy)
        rw [hfy_top]
        exact EReal.top_add_of_ne_bot
          (ne_of_gt (show (⊥ : EReal) < (g (x - y) : EReal) from (g (x - y)).2))
    exact hx htop
  · intro hx
    rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, hxyz⟩
    -- Any finite decomposition bounds the defining infimum by a finite summand.
    rw [mem_dom_iff_ne_top, infimalConvolution_apply]
    refine ne_of_lt <| lt_of_le_of_lt
      (iInf_le (fun t : H ↦ (f t : EReal) + (g (x - t) : EReal)) y) ?_
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hz_top : (g z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
    have hsum_lt : (f y : EReal) + (g z : EReal) < ⊤ :=
      EReal.add_lt_top hy_top hz_top
    have hx_sub : x - y = z := by
      rw [← hxyz]
      abel
    simpa [hx_sub] using hsum_lt

end Domain

section Commutative

variable {H : Type u} [AddCommGroup H]

/-- Companion theorem: infimal convolution is commutative for `EReal`-valued functions. -/
-- Proof sketch: reindex the infimum by swapping a decomposition `x = y + z` with `x = z + y`.
theorem infimalConvolution_comm (f g : H → EReal) :
    f □ g = g □ f := by
  ext x
  rw [infimalConvolution_apply, infimalConvolution_apply]
  refine le_antisymm ?_ ?_
  · -- Swap `y` with `x - y` in the defining infimum.
    refine le_iInf fun y ↦ ?_
    simpa [sub_sub_cancel, add_comm] using
      (iInf_le (fun z : H ↦ f z + g (x - z)) (x - y))
  · -- The reverse inequality is the same reindexing in the opposite direction.
    refine le_iInf fun y ↦ ?_
    simpa [sub_sub_cancel, add_comm] using
      (iInf_le (fun z : H ↦ g z + f (x - z)) (x - y))

end Commutative

section AffineMinorants

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Semantic search note: `lean_leansearch` did not return a relevant infimal-convolution theorem,
-- so this file keeps the source-facing Proposition 12.6 API local.

omit [InnerProductSpace ℝ H] in
/-- Proposition 12.6 (2): for `]-∞,+∞]`-valued functions, the domain of the infimal convolution
is the Minkowski sum of the effective domains. -/
theorem dom_infimalConvolution_ioi
    (f g : H → Set.Ioi (⊥ : EReal)) :
    dom (f □ g) = effectiveDomain f + effectiveDomain g := by
  -- This is exactly the domain theorem proved in the companion API above.
  simpa using dom_infimalConvolution f g

omit [InnerProductSpace ℝ H] in
/-- Proposition 12.6 (3): infimal convolution is commutative on `]-∞,+∞]`-valued functions. -/
theorem infimalConvolution_comm_ioi
    (f g : H → Set.Ioi (⊥ : EReal)) :
    f □ g = g □ f := by
  -- The `]-∞,+∞]`-valued statement is the `EReal` commutativity theorem on coerced functions.
  simpa [Function.asEReal_apply] using infimalConvolution_comm f.asEReal g.asEReal

/-- Helper for Proposition 12 6: a continuous affine minorant excludes the value `-∞` at every
point. -/
private lemma value_ne_bot_of_hasContinuousAffineMinorantWithSlope
    (f : H → EReal) (u x : H)
    (hf : HasContinuousAffineMinorantWithSlope f u) :
    f x ≠ ⊥ := by
  rcases hf with ⟨η, hη⟩
  -- The affine minorant is a real-valued lower bound, so `f x` lies strictly above `-∞`.
  exact ne_of_gt <| lt_of_lt_of_le (EReal.bot_lt_coe (⟪x, u⟫_ℝ + η)) (hη x)

/-- Helper for Proposition 12 6: adding a fixed non-`⊥` extended real commutes with an indexed
infimum whose value is also not `⊥`. -/
private lemma add_iInf_eq_iInf_add_of_ne_bot {ι : Sort*} [Nonempty ι]
    (a : EReal) (s : ι → EReal)
    (ha : a ≠ ⊥) (hs : (⨅ i, s i) ≠ ⊥) :
    a + (⨅ i, s i) = ⨅ i, a + s i := by
  let F : EReal → EReal := fun t ↦ a + t
  have hcont_add : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (a, ⨅ i, s i) :=
    EReal.continuousAt_add (p := (a, ⨅ i, s i)) (Or.inr hs) (Or.inl ha)
  have hcont : ContinuousAt F (⨅ i, s i) := by
    simpa [F] using hcont_add.comp (Continuous.prodMk_right a).continuousAt
  have hmono : Monotone F := by
    intro x y hxy
    simpa [F] using add_le_add le_rfl hxy
  have htop : F ⊤ = ⊤ := by
    simpa [F] using EReal.add_top_of_ne_bot ha
  -- Order-continuity of translation by `a` transports the indexed infimum.
  simpa [F, Function.comp] using
    (Monotone.map_iInf_of_continuousAt (ι := ι) (f := F) (g := s) hcont hmono htop)

/-- Companion theorem: on `EReal`-valued functions, common-slope affine minorants pass to the
infimal convolution. -/
-- Proof sketch: combine the two affine lower bounds in the defining infimum
-- `(f □ g) x = inf_y (f y + g (x - y))` to obtain the affine lower bound
-- `⟪x, u⟫ + η + μ`.
theorem hasContinuousAffineMinorantWithSlope_infimalConvolution
    (f g : H → EReal) (u : H)
    (hf : HasContinuousAffineMinorantWithSlope f u)
    (hg : HasContinuousAffineMinorantWithSlope g u) :
    HasContinuousAffineMinorantWithSlope (f □ g) u := by
  rcases hf with ⟨η, hη⟩
  rcases hg with ⟨μ, hμ⟩
  refine ⟨η + μ, ?_⟩
  intro x
  rw [infimalConvolution_apply]
  -- The sum of the two affine lower bounds is a lower bound for every translated summand.
  refine le_iInf fun y ↦ ?_
  have hreal :
      ⟪x, u⟫_ℝ + (η + μ) = (⟪y, u⟫_ℝ + η) + (⟪x - y, u⟫_ℝ + μ) := by
    calc
      ⟪x, u⟫_ℝ + (η + μ) = ⟪y + (x - y), u⟫_ℝ + (η + μ) := by simp
      _ = (⟪y, u⟫_ℝ + ⟪x - y, u⟫_ℝ) + (η + μ) := by rw [inner_add_left]
      _ = (⟪y, u⟫_ℝ + η) + (⟪x - y, u⟫_ℝ + μ) := by ring
  have hcoe :
      (((⟪x, u⟫_ℝ + (η + μ) : ℝ) : EReal)) =
        (((⟪y, u⟫_ℝ + η : ℝ) : EReal)) +
          (((⟪x - y, u⟫_ℝ + μ : ℝ) : EReal)) := by
    calc
      (((⟪x, u⟫_ℝ + (η + μ) : ℝ) : EReal)) =
          ((((⟪y, u⟫_ℝ + η) + (⟪x - y, u⟫_ℝ + μ) : ℝ) : EReal)) := by
            exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
      _ =
          (((⟪y, u⟫_ℝ + η : ℝ) : EReal)) +
            (((⟪x - y, u⟫_ℝ + μ : ℝ) : EReal)) := by
            rw [EReal.coe_add]
  calc
    (((⟪x, u⟫_ℝ + (η + μ) : ℝ) : EReal)) =
        (((⟪y, u⟫_ℝ + η : ℝ) : EReal)) +
          (((⟪x - y, u⟫_ℝ + μ : ℝ) : EReal)) := hcoe
    _ ≤ f y + g (x - y) := add_le_add (hη y) (hμ (x - y))

/-- Under the hypotheses of Proposition 12.6 (1), the infimal convolution never attains `-∞`. -/
-- Proof sketch: apply Proposition 12.6 (1) to get a continuous affine minorant of `f □ g`, then
-- evaluate that minorant at `x` to bound `(f □ g) x` strictly above `⊥`.
theorem infimalConvolution_ne_bot_of_hasContinuousAffineMinorantWithSlope
    (f g : H → EReal) (u : H)
    (hf : HasContinuousAffineMinorantWithSlope f u)
    (hg : HasContinuousAffineMinorantWithSlope g u) (x : H) :
    (f □ g) x ≠ ⊥ := by
  -- Part (i) supplies the affine minorant, and the pointwise bridge rules out `-∞`.
  exact value_ne_bot_of_hasContinuousAffineMinorantWithSlope
    (f □ g) u x (hasContinuousAffineMinorantWithSlope_infimalConvolution f g u hf hg)

/-- Proposition 12.6 (1): if `f` and `g` admit continuous affine minorants with slope `u`, then
`f □ g` admits a continuous affine minorant with slope `u`, and `(f □ g) x ≠ ⊥` for every
`x`. -/
theorem hasContinuousAffineMinorantWithSlope_infimalConvolution_ioi
    (f g : H → Set.Ioi (⊥ : EReal)) (u : H)
    (hf : HasContinuousAffineMinorantWithSlope f.asEReal u)
    (hg : HasContinuousAffineMinorantWithSlope g.asEReal u) :
    HasContinuousAffineMinorantWithSlope (f □ g) u ∧ ∀ x : H, (f □ g) x ≠ ⊥ := by
  -- Transport both conclusions from the already-proved `EReal`-valued companion theorems.
  refine ⟨?_, ?_⟩
  · simpa [Function.asEReal_apply] using
      hasContinuousAffineMinorantWithSlope_infimalConvolution f.asEReal g.asEReal u hf hg
  · intro x
    simpa [Function.asEReal_apply] using
      infimalConvolution_ne_bot_of_hasContinuousAffineMinorantWithSlope
        f.asEReal g.asEReal u hf hg x

/-- Helper for Proposition 12 6: the left-associated infimal convolution expands to the common
double-infimum normal form indexed by the first two summands of the source triple decomposition. -/
private lemma left_associated_infimalConvolution_eq_iInf_iInf
    (f g h : H → EReal) (u x : H)
    (hf : HasContinuousAffineMinorantWithSlope f u)
    (hg : HasContinuousAffineMinorantWithSlope g u)
    (hh : HasContinuousAffineMinorantWithSlope h u) :
    (f □ (g □ h)) x = ⨅ a : H, ⨅ b : H, f a + g b + h (x - (a + b)) := by
  have hgh :
      HasContinuousAffineMinorantWithSlope (g □ h) u :=
    hasContinuousAffineMinorantWithSlope_infimalConvolution g h u hg hh
  -- First expand the outer infimal convolution, then push the fixed `f a` across the inner infimum.
  calc
    (f □ (g □ h)) x = ⨅ a : H, f a + (g □ h) (x - a) := by
      rw [infimalConvolution_apply]
    _ = ⨅ a : H, ⨅ b : H, f a + (g b + h ((x - a) - b)) := by
      refine iInf_congr fun a ↦ ?_
      rw [infimalConvolution_apply]
      exact add_iInf_eq_iInf_add_of_ne_bot
        (f a)
        (fun b : H ↦ g b + h ((x - a) - b))
        (value_ne_bot_of_hasContinuousAffineMinorantWithSlope f u a hf)
        (value_ne_bot_of_hasContinuousAffineMinorantWithSlope (g □ h) u (x - a) hgh)
    _ = ⨅ a : H, ⨅ b : H, f a + g b + h (x - (a + b)) := by
      refine iInf_congr fun a ↦ ?_
      refine iInf_congr fun b ↦ ?_
      simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Helper for Proposition 12 6: the right-associated infimal convolution expands to the same
double-infimum normal form as the left-associated side. -/
private lemma right_associated_infimalConvolution_eq_iInf_iInf
    (f g h : H → EReal) (u x : H)
    (hf : HasContinuousAffineMinorantWithSlope f u)
    (hg : HasContinuousAffineMinorantWithSlope g u)
    (hh : HasContinuousAffineMinorantWithSlope h u) :
    ((f □ g) □ h) x = ⨅ a : H, ⨅ b : H, f a + g b + h (x - (a + b)) := by
  have hfg :
      HasContinuousAffineMinorantWithSlope (f □ g) u :=
    hasContinuousAffineMinorantWithSlope_infimalConvolution f g u hf hg
  -- Expand the outer infimum and reindex the resulting pair `(c, a)` by `(a, c - a)`.
  calc
    ((f □ g) □ h) x = ⨅ c : H, (f □ g) c + h (x - c) := by
      rw [infimalConvolution_apply]
    _ = ⨅ c : H, ⨅ a : H, h (x - c) + (f a + g (c - a)) := by
      refine iInf_congr fun c ↦ ?_
      rw [infimalConvolution_apply]
      have hfgc_bot : (⨅ i : H, f i + g (c - i)) ≠ ⊥ := by
        simpa [infimalConvolution_apply] using
          value_ne_bot_of_hasContinuousAffineMinorantWithSlope (f □ g) u c hfg
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_iInf_eq_iInf_add_of_ne_bot
          (h (x - c))
          (fun a : H ↦ f a + g (c - a))
          (value_ne_bot_of_hasContinuousAffineMinorantWithSlope h u (x - c) hh)
          hfgc_bot)
    _ = ⨅ a : H, ⨅ c : H, h (x - c) + (f a + g (c - a)) := by
      rw [iInf_comm]
    _ = ⨅ a : H, ⨅ b : H, h (x - (a + b)) + (f a + g b) := by
      refine iInf_congr fun a ↦ ?_
      -- Reindex the outer summand by the translation `c = a + b`.
      refine (Equiv.subRight a).iInf_congr fun b ↦ ?_
      simp [sub_eq_add_neg, add_assoc, add_comm]
    _ = ⨅ a : H, ⨅ b : H, f a + g b + h (x - (a + b)) := by
      refine iInf_congr fun a ↦ ?_
      refine iInf_congr fun b ↦ ?_
      simp [add_assoc, add_comm]

/-- Companion theorem: on `EReal`-valued functions, common-slope affine minorants imply
associativity of infimal convolution. -/
-- Proof sketch: Proposition 12.6 (1) gives affine minorants for `g □ h` and `f □ g`,
-- so both iterated
-- infimal convolutions are well defined. Then rewrite both sides as the infimum of
-- `f u + g v + h w` over triples satisfying `u + v + w = x`.
theorem infimalConvolution_assoc_of_commonSlopeMinorants
    (f g h : H → EReal) (u : H)
    (hf : HasContinuousAffineMinorantWithSlope f u)
    (hg : HasContinuousAffineMinorantWithSlope g u)
    (hh : HasContinuousAffineMinorantWithSlope h u) :
    f □ (g □ h) = (f □ g) □ h := by
  funext x
  -- Both iterated infimal convolutions reduce to the same double-infimum normal form.
  rw [left_associated_infimalConvolution_eq_iInf_iInf f g h u x hf hg hh,
    right_associated_infimalConvolution_eq_iInf_iInf f g h u x hf hg hh]

/-- Proposition 12.6 (4): if `f`, `g`, and `h` admit continuous affine minorants with the same
slope, then infimal convolution is associative on `f`, `g`, and `h`. -/
theorem infimalConvolution_assoc_of_commonSlopeMinorants_ioi
    (f g h : H → Set.Ioi (⊥ : EReal)) (u : H)
    (hf : HasContinuousAffineMinorantWithSlope f.asEReal u)
    (hg : HasContinuousAffineMinorantWithSlope g.asEReal u)
    (hh : HasContinuousAffineMinorantWithSlope h.asEReal u) :
    f □ (g □ h) = (f □ g) □ h := by
  -- The proposition-facing associativity statement is a direct `asEReal` transport.
  simpa [Function.asEReal_apply] using
    infimalConvolution_assoc_of_commonSlopeMinorants
      f.asEReal g.asEReal h.asEReal u hf hg hh

end AffineMinorants

end ERealFunction
