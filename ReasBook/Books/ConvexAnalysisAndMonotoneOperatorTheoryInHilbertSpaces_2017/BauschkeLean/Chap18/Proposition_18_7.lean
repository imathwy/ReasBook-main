import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap09.Definition_9_2
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap17.Proposition_17_48

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped InnerProductSpace
open InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfInfimalConvolutions

variable {H : Type u} [NormedAddCommGroup H]
variable {f g : H → Set.Ioi (⊥ : EReal)}
variable {x y gradf : H}

/-- The Proposition 18.1 continuity-set owner: points admitting a neighborhood contained in
`effectiveDomain f` on which the finite-valued representative is ambiently continuous. -/
def cont (f : H → Set.Ioi (⊥ : EReal)) : Set H :=
  {z | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ effectiveDomain f ∧
    ContinuousAt (fun w ↦ (f w : EReal).toReal) z}

/-- Membership in `cont f` is exactly the source-facing local effective-domain continuity datum. -/
@[simp] theorem mem_cont_iff
    (f : H → Set.Ioi (⊥ : EReal)) (z : H) :
    z ∈ cont f ↔
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ effectiveDomain f ∧
        ContinuousAt (fun w ↦ (f w : EReal).toReal) z :=
  Iff.rfl

/-- Helper for Proposition 18.7: a point of the local continuity set belongs to the effective
domain. -/
lemma mem_effectiveDomain_of_mem_cont_local
    {f : H → Set.Ioi (⊥ : EReal)} {z : H} (hz : z ∈ cont f) :
    z ∈ effectiveDomain f := by
  -- Evaluate the defining ball witness at its center.
  rcases (mem_cont_iff f z).1 hz with ⟨ρ, hρ, hball, _⟩
  exact hball (Metric.mem_ball_self hρ)

/-- Helper for Proposition 18.7: a point of the local continuity set is an interior effective-domain
point. -/
lemma mem_interior_effectiveDomain_of_mem_cont_local
    {f : H → Set.Ioi (⊥ : EReal)} {z : H} (hz : z ∈ cont f) :
    z ∈ interior (effectiveDomain f) := by
  -- The defining ball witness is already an open neighborhood inside the effective domain.
  rcases (mem_cont_iff f z).1 hz with ⟨ρ, hρ, hball, _⟩
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (Metric.ball_mem_nhds z hρ) hball

/-- Helper for Proposition 18.7: the local continuity-set owner repackages directly into the
Chapter 16 continuity-on-effective-domain owner. -/
lemma continuousAtOnEffectiveDomain_of_mem_cont_local
    {f : H → Set.Ioi (⊥ : EReal)} {z : H} (hz : z ∈ cont f) :
    ContinuousAtOnEffectiveDomain f z := by
  -- The ball witness gives effective-domain membership, and ambient continuity restricts.
  rcases (mem_cont_iff f z).1 hz with ⟨ρ, hρ, hball, hcont⟩
  exact ⟨hball (Metric.mem_ball_self hρ), hcont.continuousWithinAt⟩

variable [InnerProductSpace ℝ H] [CompleteSpace H]

local notation:70 f " □ₑ " g =>
  ERealFunction.infimalConvolution (fun z ↦ (f z : EReal)) (fun z ↦ (g z : EReal))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 18.7: once the infimal convolution value at `x` is known to be finite,
the exact splitting at `y` forces both summands to be finite. -/
lemma summands_lt_top_of_infimalConvolution_value_eq_of_mem_dom
    {f g : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hx : x ∈ dom (f □ₑ g))
    (hEq : (f □ₑ g) x = (f y : EReal) + (g (x - y) : EReal)) :
    (f y : EReal) < ⊤ ∧ (g (x - y) : EReal) < ⊤ := by
  -- The exact value is finite because `x` lies in the domain of `f □ g`.
  have hsum_top : ((f y : EReal) + (g (x - y) : EReal)) ≠ ⊤ := by
    rw [← hEq]
    exact ne_of_lt ((mem_dom_iff (f □ₑ g) x).mp hx)
  have hfy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hgy_bot : (g (x - y) : EReal) ≠ ⊥ := ne_of_gt (g (x - y)).2
  -- Split finiteness of the sum into finiteness of each summand.
  have hparts := (EReal.add_ne_top_iff_ne_top₂ hfy_bot hgy_bot).1 hsum_top
  exact ⟨lt_of_le_of_ne le_top hparts.1, lt_of_le_of_ne le_top hparts.2⟩

omit [CompleteSpace H] in
/-- Helper for Proposition 18.7: a local Fréchet-differentiability witness upgrades to the source
Chapter 17 Gâteaux-differentiability owner. -/
lemma gateauxDifferentiableAt_of_mem_cont_and_differentiableAt
    {f : H → Set.Ioi (⊥ : EReal)} {z : H}
    (hzcont : z ∈ cont f)
    (hzdiff : DifferentiableAt ℝ (fun w ↦ (f w : EReal).toReal) z) :
    GateauxDifferentiableAt f z := by
  rcases (mem_cont_iff f z).1 hzcont with ⟨ρ, hρ, hball, _⟩
  -- Restrict the ambient Fréchet derivative to the continuity ball inside the effective domain.
  refine GateauxDifferentiableAt.of_toRealWithin_subset_effectiveDomain
    (x := z) (U := Metric.ball z ρ) (Metric.mem_ball_self hρ) hball ?_
  rw [gateauxDifferentiableWithinAt_iff_exists_hasGateauxDerivativeWithinAt]
  refine ⟨fderiv ℝ (fun w ↦ (f w : EReal).toReal) z, ?_⟩
  exact
    hzdiff.hasFDerivAt.hasFDerivWithinAt.hasGateauxDerivativeWithinAt
      (Metric.ball_mem_nhds z hρ)

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.7 gives the continuity-set, Gâteaux-differentiability, and
  Fréchet-differentiability conclusions for the infimal convolution at `x` from exactness at the
  minimizer `y`.
- `core/canonical`: the primitive data are `IsProper (f □ g)`, `(f □ g) ∈ Γ(H)`, the exactness
  witness `hEq`, the imported Chapter 18 owner `cont`, the canonical `Γ₀(H)` repackaging
  `properIoi (f □ g) hproper`, the source Gâteaux owner, the gradient operator on the finite real
  representative, and `DifferentiableAt`.
- `bridge/view`: `properIoi_mem_gammaZero_of_mem_gamma` upgrades the raw owner to `Γ₀(H)`, and
  Proposition 18.6 and Proposition 17.31 supply the singleton-subdifferential bridge used to
  transfer differentiability data from the minimizing point `y` to the infimal convolution at `x`.

Primitive data vs. derived API:
- primitive data: `IsProper (f □ g)`, `(f □ g) ∈ Γ(H)`, the exactness witness `hEq`, and the
  differentiability data of `f` at the minimizing point `y`;
- derived API: continuity at `x`, source Gâteaux differentiability of
  `properIoi (f □ g) hproper` at `x`, the gradient identity (18.28), and the Fréchet
  differentiability conclusion under the additional Fréchet hypothesis at `y`. -/

-- Proof sketch: the source Chapter 17 Gâteaux-differentiability owner places `y` in the
-- effective domain with the directional-derivative structure needed by Proposition 17.48. The
-- exact equality `hEq` then forces `x - y ∈ effectiveDomain g`, so the effective-domain formula
-- for the infimal convolution places `x` in
-- `interior (effectiveDomain (properIoi (f □ g) hproper))`. Proposition 16.27 turns that into
-- `x ∈ cont (properIoi (f □ g) hproper)`.
/-- Proposition 18.7 (1): if `f, g ∈ Γ₀(H)`, if the raw infimal convolution `f □ g`
is proper and lies in `Γ(H)`, if it is exact at `x` with minimizer `y`, and if `f`
is Gâteaux differentiable at `y` in the Chapter 17 source sense, then
`x ∈ cont (properIoi (f □ₑ g) hproper)`, equivalently `x` admits a ball contained in
the effective domain of `properIoi (f □ₑ g) hproper` on which the finite real
representative of `f □ g` is continuous. -/
theorem mem_cont_properIoi_infimalConvolution_of_value_eq_of_gateauxDifferentiableAt
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hproper : IsProper (f □ₑ g)) (hgamma : (f □ₑ g) ∈ Γ(H))
    (hEq : (f □ₑ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hgateaux : GateauxDifferentiableAt f y) :
    x ∈ cont (properIoi (f □ₑ g) hproper) :=
  -- TODO: the source proof needs `x ∈ dom (f □ₑ g)` (equivalently finiteness of the exact value)
  -- to deduce `g (x - y) < ⊤` from `hEq`, hence `x = y + (x - y) ∈ interior (effectiveDomain f) +
  -- effectiveDomain g`. The current theorem statement only gives the raw `EReal` equality `hEq`,
  -- which still allows the degenerate case `g (x - y) = ⊤`.
  sorry

-- Proof sketch: the source Gâteaux-differentiability hypothesis is transported through the
-- singleton-subdifferential description from Proposition 18.6 and the Chapter 17 bridge back to
-- the source owner at `x`.
/-- Proposition 18.7 (2): under the same hypotheses, the canonical `Γ₀(H)`
repackaging `properIoi (f □ₑ g) hproper` is Gâteaux differentiable at `x`
in the Chapter 17 source sense. -/
theorem gateauxDifferentiableAt_properIoi_infimalConvolution_of_value_eq
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hproper : IsProper (f □ₑ g)) (hgamma : (f □ₑ g) ∈ Γ(H))
    (hEq : (f □ₑ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hgateaux : GateauxDifferentiableAt f y) :
    GateauxDifferentiableAt (properIoi (f □ₑ g) hproper) x :=
  -- TODO: after theorem (1) is repaired with a finiteness/domain hypothesis at `x`, apply
  -- Proposition 18.6 to get the singleton subdifferential at `x`, then Proposition 17.31(2) and
  -- the proved continuity bridge `continuousAtOnEffectiveDomain_of_mem_cont_local`.
  sorry

/-- Proposition 18.7 (3), equation (18.28): under the same hypotheses, the gradient of the
finite real representative of the canonical `Γ₀(H)` repackaging of `f □ g` at `x` agrees with
the gradient of `f` at `y`. -/
theorem gradient_properIoi_infimalConvolution_eq_gradient_of_value_eq_of_gateauxDifferentiableAt
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hproper : IsProper (f □ₑ g)) (hgamma : (f □ₑ g) ∈ Γ(H))
    (hEq : (f □ₑ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hgateaux : GateauxDifferentiableAt f y) :
    ∇ (fun z ↦ (((properIoi (f □ₑ g) hproper) z : EReal).toReal)) x =
      ∇ (fun z ↦ (f z : EReal).toReal) y :=
  -- TODO: the current assumptions only give source Gâteaux differentiability, but Mathlib's
  -- gradient `∇` is defined through the Fréchet derivative. A repaired statement needs either an
  -- explicit `HasGateauxDerivativeAt ... (toDualMap ℝ H gradf)` conclusion or an added
  -- differentiability/Frechet hypothesis at the two endpoints.
  sorry

-- Semantic recall: the existing global source Fréchet-locus owner currently depends on an
-- upstream file that does not compile in this workspace, so this item keeps the source meaning as
-- the single conjunction `cont ∧ DifferentiableAt` on the correct `Γ₀(H)` owner.
/-- Proposition 18.7 (4): if `f` is Fréchet differentiable at `y` in the Chapter 18 source sense,
namely continuous there on its effective domain and Fréchet differentiable through its finite real
representative, then the canonical `Γ₀(H)` repackaging of `f □ g` is Fréchet differentiable at
`x` in the same source sense. -/
theorem differentiableAt_infimalConvolution_toReal_of_value_eq_of_differentiableAt
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hproper : IsProper (f □ₑ g)) (hgamma : (f □ₑ g) ∈ Γ(H))
    (hEq : (f □ₑ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hyFrechet : y ∈ cont f ∧ DifferentiableAt ℝ (fun z ↦ (f z : EReal).toReal) y) :
    x ∈ cont (properIoi (f □ₑ g) hproper) ∧
      DifferentiableAt ℝ
        (fun z ↦ (((properIoi (f □ₑ g) hproper) z : EReal).toReal)) x :=
  -- TODO: first upgrade `hyFrechet` to the source owner with
  -- `gateauxDifferentiableAt_of_mem_cont_and_differentiableAt`, then repair theorem (1) so the
  -- exact-minimizer remainder squeeze can be carried out on a genuine finite neighborhood of `x`.
  sorry

end DifferentiabilityOfInfimalConvolutions

end ERealFunction
