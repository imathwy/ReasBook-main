import Mathlib.Analysis.InnerProductSpace.Orthogonal
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 1.6 names the orthogonal complement of a linear subspace.
- `core/canonical`: at the chapter API layer, this notion only needs pairing-evaluation vanishing,
  so the owner is the pairing annihilator `Submodule.pairingOrthogonal`.
- `bridge/view` (dual model): in the concrete algebraic-dual model this owner is exactly
  mathlib's canonical
  `Submodule.dualAnnihilator`, via `Submodule.pairingOrthogonal_eq_dualAnnihilator`.
- `bridge/view` (inner-product specialization): the textbook notation `Kᗮ` is recorded by
  `Submodule.pairingOrthogonal_eq_orthogonal` and, for the canonical real instance,
  `Submodule.pairingOrthogonal_eq_orthogonal_real`.
- Primitive data vs derived API: primitive data are a submodule `K` and a pairing
  `HasLinearPairing X Y 𝕜`; inner-product self-pairing is derived bridge data.
- Domain-style sampling used here: `HasLinearPairing.pairingLinear.flip`,
  `Submodule.dualAnnihilator`, `Submodule.comap`, `Submodule.orthogonal`,
  `Submodule.mem_orthogonal`.
- Layer target: `core/canonical` at the pairing layer, with the inner-product owner retained as a
  thin specialization.
- Canonicalization checks:
  - codomain/ambient: the owner is submodule-level annihilation; no concrete coordinate codomain.
  - scalar/structure: only `CommSemiring`/module data are used for the owner; inner-product
    bridges use the `Submodule.orthogonal` API layer, whose ambient assumptions are inherited.
  - owner choice: keep `Submodule.pairingOrthogonal` as the intrinsic chapter owner and treat
    `Submodule.orthogonal` as a bridge/view.
  - topology/intrinsic language: no ambient-topology owner is introduced in this item.
  - notation surface: use the textbook-style postfix `Kᗮₚ` directly on theorem surfaces.
-/
namespace Submodule

section PairingOrthogonal

variable {𝕜 : Type*} {X : Type*} {Y : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- Pairing-level orthogonal complement of a submodule: all `y` whose pairing with every
`x ∈ K` vanishes. -/
def pairingOrthogonal (K : Submodule 𝕜 X) : Submodule 𝕜 Y :=
  K.dualAnnihilator.comap
    (HasLinearPairing.pairingLinear.flip : Y →ₗ[𝕜] Module.Dual 𝕜 X)

scoped[Rockafellar] postfix:max "ᗮₚ" => Submodule.pairingOrthogonal

/-- `pairingOrthogonal` is the pullback of `dualAnnihilator` along the flipped pairing map. -/
@[simp] theorem pairingOrthogonal_eq_comap_dualAnnihilator (K : Submodule 𝕜 X) :
    Kᗮₚ = K.dualAnnihilator.comap
      (HasLinearPairing.pairingLinear.flip : Y →ₗ[𝕜] Module.Dual 𝕜 X) :=
  rfl

/-- Membership in `pairingOrthogonal` is exactly pointwise vanishing of the pairing on `K`. -/
@[simp] theorem mem_pairingOrthogonal_iff {K : Submodule 𝕜 X} {y : Y} :
    y ∈ Kᗮₚ ↔ ∀ x ∈ K, ⟪x, y⟫ₚ = (0 : 𝕜) :=
by
  simp [pairingOrthogonal, Submodule.mem_dualAnnihilator, LinearMap.flip_apply]

end PairingOrthogonal

section DualBridge

variable {𝕜 : Type*} {X : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]

/-- In the canonical evaluation pairing with the algebraic dual, `Kᗮₚ` is exactly
`K.dualAnnihilator`. -/
@[simp] theorem pairingOrthogonal_eq_dualAnnihilator (K : Submodule 𝕜 X) :
    Kᗮₚ = K.dualAnnihilator := by
  ext φ
  rw [mem_pairingOrthogonal_iff, Submodule.mem_dualAnnihilator]
  constructor
  · intro h x hx
    exact h x hx
  · intro h x hx
    exact h x hx

end DualBridge

section InnerProductMembershipBridge

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [HasLinearPairing E E 𝕜]

/-- If the chapter pairing agrees pointwise with the ambient inner product, then pairing
orthogonality is exactly textbook orthogonality. -/
@[simp] theorem mem_pairingOrthogonal_iff_inner_eq_zero
    (hpair : ∀ x y : E,
      ⟪x, y⟫ₚ = inner 𝕜 x y)
    {K : Submodule 𝕜 E} {y : E} :
    y ∈ Kᗮₚ ↔ ∀ x ∈ K, inner 𝕜 x y = 0 := by
  rw [mem_pairingOrthogonal_iff]
  constructor
  · intro hy x hx
    exact (hpair x y).symm.trans (hy x hx)
  · intro hy x hx
    exact (hpair x y).trans (hy x hx)

end InnerProductMembershipBridge

section InnerProductOrthogonalBridge

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [HasLinearPairing E E 𝕜]

/-- If the chapter pairing agrees pointwise with the ambient inner product, then pairing
orthogonality is exactly textbook orthogonality. -/
theorem pairingOrthogonal_eq_orthogonal
    (hpair : ∀ x y : E,
      ⟪x, y⟫ₚ = inner 𝕜 x y)
    (K : Submodule 𝕜 E) :
    Kᗮₚ = (Kᗮ : Submodule 𝕜 E) := by
  ext y
  simpa [Submodule.mem_orthogonal] using
    (mem_pairingOrthogonal_iff_inner_eq_zero (hpair := hpair) (K := K) (y := y))

end InnerProductOrthogonalBridge

section InnerProductMembershipBridgeReal

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For the canonical real inner-product pairing, pairing orthogonality is exactly `Kᗮ`. -/
@[simp] theorem mem_pairingOrthogonal_iff_inner_eq_zero_real
    {K : Submodule ℝ E} {y : E} :
    y ∈ Kᗮₚ ↔ ∀ x ∈ K, inner ℝ x y = 0 :=
  mem_pairingOrthogonal_iff_inner_eq_zero (hpair := by intro x y; rfl)

end InnerProductMembershipBridgeReal

section InnerProductOrthogonalBridgeReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For the canonical real inner-product pairing, pairing orthogonality is exactly `Kᗮ`. -/
@[simp] theorem pairingOrthogonal_eq_orthogonal_real (K : Submodule ℝ E) :
    Kᗮₚ = (Kᗮ : Submodule ℝ E) :=
  pairingOrthogonal_eq_orthogonal (hpair := by intro x y; rfl) K

end InnerProductOrthogonalBridgeReal

/- Text 1.6: the canonical chapter owner for orthogonal complement is the pairing-level
`Submodule.pairingOrthogonal` (surface notation `Kᗮₚ`); the textbook inner-product owner `Kᗮ`
(i.e. `Submodule.orthogonal`) is recovered as the bridge specialization
`pairingOrthogonal_eq_orthogonal_real`. -/
recall pairingOrthogonal
recall pairingOrthogonal_eq_comap_dualAnnihilator
recall mem_pairingOrthogonal_iff
recall pairingOrthogonal_eq_dualAnnihilator
recall Submodule.orthogonal
recall Submodule.mem_orthogonal
recall Submodule.mem_orthogonal'
recall mem_pairingOrthogonal_iff_inner_eq_zero
recall mem_pairingOrthogonal_iff_inner_eq_zero_real
recall pairingOrthogonal_eq_orthogonal
recall pairingOrthogonal_eq_orthogonal_real

end Submodule
