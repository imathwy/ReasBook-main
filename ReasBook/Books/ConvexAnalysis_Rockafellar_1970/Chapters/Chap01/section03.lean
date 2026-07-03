import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_1_3 (from Chap01) -/
open scoped Affine Pointwise

/-
Source/core/bridge triage:
- `source-facing`: Text 1.3 characterizes parallel affine subspaces by translation.
- `core/canonical`: the owner is `AffineSubspace.Parallel` (`s ∥ t`), with canonical intrinsic
  criterion `AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot`.
- `bridge/view`: the translation surface is the pointwise notation `v +ᵥ s`.
- Primitive data vs derived API: direction equality plus `⊥`-equivalence is canonical owner-level
  API; nonempty formulations are thin bridges obtained via `nonempty_iff_ne_bot`.
-/
/- Canonicalization decision record (this pass):
- Codomain/ambient check: this item has no ordered extended codomain; keep the affine-subspace
  owner layer.
- Scalar/ambient structure check: reused owner APIs live at the generic `Ring` affine-space layer;
  no concrete `ℝ`/Euclidean specialization is exposed.
- Owner check: keep `AffineSubspace.Parallel` as the primitive owner and expose translation through
  pointwise `+ᵥ` notation rather than map internals; do not introduce a new local nonemptiness
  owner when canonical set-level nonemptiness already exists.
- Topology check: this item is not topology-facing, so no ambient/intrinsic topology refactor.
- Owner-name check: keep short owner-side theorem names under `AffineSubspace`.
- Notation check: use the textbook-primary pointwise translation notation `v +ᵥ s` on theorem
  surfaces.
-/
namespace AffineSubspace

section

variable {k : Type*} {V : Type*} {P : Type*}
variable [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- A parallel affine subspace is a pointwise translation of the original affine subspace. -/
theorem Parallel.exists_vadd_eq {s t : AffineSubspace k P} (h : s ∥ t) :
    ∃ v : V, v +ᵥ s = t := by
  simpa [eq_comm, AffineSubspace.Parallel, pointwise_vadd_eq_map] using h

/-- Text 1.3: two affine subspaces are parallel exactly when one is a translation of the other. -/
theorem parallel_iff_exists_vadd_eq (s t : AffineSubspace k P) :
    s ∥ t ↔ ∃ v : V, v +ᵥ s = t := by
  simpa [eq_comm] using
    (show s ∥ t ↔ ∃ v : V, t = v +ᵥ s by
      simp [AffineSubspace.Parallel, pointwise_vadd_eq_map])

/-- Symmetric orientation of the translation form of parallel affine subspaces. -/
theorem parallel_iff_exists_eq_vadd (s t : AffineSubspace k P) :
    s ∥ t ↔ ∃ v : V, t = v +ᵥ s := by
  simpa [eq_comm] using parallel_iff_exists_vadd_eq (s := s) (t := t)

/-- The translation of an affine subspace is parallel to the original affine subspace. -/
theorem parallel_vadd (v : V) (s : AffineSubspace k P) :
    s ∥ (v +ᵥ s) :=
  (parallel_iff_exists_vadd_eq (s := s) (t := v +ᵥ s)).2 ⟨v, rfl⟩

/-- Direction equality and `⊥`-equivalence are the intrinsic owner-level criterion
for parallelism. -/
theorem parallel_iff_direction_eq_and_eq_bot (s t : AffineSubspace k P) :
    s ∥ t ↔ s.direction = t.direction ∧ (s = ⊥ ↔ t = ⊥) := by
  simpa using (parallel_iff_direction_eq_and_eq_bot_iff_eq_bot (s₁ := s) (s₂ := t))

/-- Direction equality and intrinsic affine-subspace nonemptiness are a criterion for
parallelism. -/
theorem parallel_iff_direction_eq_and_nonempty (s t : AffineSubspace k P) :
    s ∥ t ↔ s.direction = t.direction ∧ ((s : Set P).Nonempty ↔ (t : Set P).Nonempty) := by
  simpa [AffineSubspace.nonempty_iff_ne_bot, not_iff_not] using
    parallel_iff_direction_eq_and_eq_bot (s := s) (t := t)

end

end AffineSubspace

/-! ### Theorem_1_3 (from Chap01) -/
noncomputable section

open scoped RealInnerProductSpace
open scoped Rockafellar
open AffineSubspace

/-
Source/core/bridge triage:
- `source-facing`: Theorem 1.3 identifies hyperplanes with nontrivial normal equations
  and records when two such equations determine the same hyperplane.
- `core/canonical`: the primitive owner layer is `AffineSubspace` together with the codimension-one
  predicate `AffineSubspace.is_hyperplane`, and the correct equation-level owner is the
  linear-functional fiber `linearHyperplane f β`.
- `bridge/view`: the coordinate-free owner API `AffineSubspace.affineDim` remains the dimension
  language, while the inner-product normal-equation family `affineHyperplane b β` is only the
  real-inner-product specialization of `linearHyperplane`.
- Primitive data vs derived API: `AffineSubspace.affineDim` packages the source-facing dimension
  convention, but codimension-one is more canonically primitive as `Module.finrank 𝕜
  (V ⧸ s.direction) = 1`; the affine-dimension equation is kept as a bridge theorem rather than as
  the owner definition of hyperplane, and the linear-functional hyperplane family is kept separate
  from its inner-product normal-vector presentation.
-/

section AffineDimensionBridgeInternal

attribute [local instance] Classical.propDecidable

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

namespace AffineSubspace

-- Internal raw affine-fiber form used to prove the public owner theorem
-- `linearHyperplane_is_hyperplane`.
private theorem linearFiber_is_hyperplane {f : V →ₗ[𝕜] 𝕜}
    (hf : f ≠ 0) (β : 𝕜) :
    ((affineSpan 𝕜 ({β} : Set 𝕜)).comap f.toAffineMap : AffineSubspace 𝕜 V).is_hyperplane := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : V, f x₀ = β := by
    have hsurj : Function.Surjective f :=
      LinearMap.range_eq_top.mp <| Module.Dual.range_eq_top_of_ne_zero hf
    exact hsurj β
  let H : AffineSubspace 𝕜 V := (affineSpan 𝕜 ({β} : Set 𝕜)).comap f.toAffineMap
  have hx₀H : x₀ ∈ H := by
    change x₀ ∈ (affineSpan 𝕜 ({β} : Set 𝕜)).comap f.toAffineMap
    rw [mem_comap, mem_affineSpan_singleton]
    simpa [LinearMap.coe_toAffineMap] using hx₀
  have hH : H = mk' x₀ (LinearMap.ker f) := by
    ext x
    change x ∈ (affineSpan 𝕜 ({β} : Set 𝕜)).comap f.toAffineMap ↔ x ∈ mk' x₀ (LinearMap.ker f)
    rw [mem_comap, mem_affineSpan_singleton, mem_mk', LinearMap.mem_ker]
    simp only [LinearMap.coe_toAffineMap]
    constructor
    · intro hx
      simp [map_sub, hx, hx₀]
    · intro hx
      have hx' : f x - f x₀ = 0 := by
        simpa [map_sub] using hx
      simpa [hx₀] using sub_eq_zero.mp hx'
  refine ⟨?_, ?_⟩
  · intro hbot
    have : x₀ ∈ (⊥ : AffineSubspace 𝕜 V) := by
      simpa [H, hbot] using hx₀H
    simpa using this
  · change Module.finrank 𝕜 (V ⧸ H.direction) = 1
    rw [hH, direction_mk']
    calc
      Module.finrank 𝕜 (V ⧸ LinearMap.ker f) = Module.finrank 𝕜 (LinearMap.range f) := by
        simpa using f.quotKerEquivRange.finrank_eq
      _ = Module.finrank 𝕜 (⊤ : Submodule 𝕜 𝕜) := by
        rw [Module.Dual.range_eq_top_of_ne_zero hf]
      _ = 1 := by simp

end AffineSubspace

end AffineDimensionBridgeInternal

section LinearHyperplane

variable {𝕜 : Type*} {V : Type*}
  [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The affine hyperplane cut out by one scalar-valued linear equation `f x = β`. -/
def linearHyperplane (f : V →ₗ[𝕜] 𝕜) (β : 𝕜) : AffineSubspace 𝕜 V :=
  (affineSpan 𝕜 ({β} : Set 𝕜)).comap f.toAffineMap

/-- Membership in `linearHyperplane f β` is the equation `f x = β`. -/
@[simp] theorem mem_linearHyperplane_iff {f : V →ₗ[𝕜] 𝕜} {x : V} {β : 𝕜} :
    x ∈ linearHyperplane f β ↔ f x = β := by
  rw [linearHyperplane, mem_comap, mem_affineSpan_singleton]
  simp [LinearMap.coe_toAffineMap]

end LinearHyperplane

section LinearHyperplaneDivisionRing

variable {𝕜 : Type*} {V : Type*}
  [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- A nonzero scalar-valued linear equation cuts out a nonempty affine hyperplane. -/
theorem linearHyperplane_nonempty (f : V →ₗ[𝕜] 𝕜) (β : 𝕜) (hf : f ≠ 0) :
    Nonempty (linearHyperplane f β) := by
  have hsurj : Function.Surjective f :=
    LinearMap.range_eq_top.mp <| Module.Dual.range_eq_top_of_ne_zero hf
  rcases hsurj β with ⟨x, rfl⟩
  exact ⟨x, by simp [mem_linearHyperplane_iff]⟩

/-- A nonzero scalar-valued linear equation cuts out a hyperplane. -/
theorem linearHyperplane_is_hyperplane (f : V →ₗ[𝕜] 𝕜)
    (β : 𝕜) (hf : f ≠ 0) :
    (linearHyperplane f β).is_hyperplane := by
  simpa [linearHyperplane] using AffineSubspace.linearFiber_is_hyperplane hf β

section FiniteDimensional

variable [FiniteDimensional 𝕜 V]

namespace AffineSubspace

/-- Every hyperplane in a finite-dimensional affine space is representable as one nontrivial
scalar-valued linear equation `f x = β`. -/
theorem exists_eq_linearHyperplane_of_is_hyperplane {s : AffineSubspace 𝕜 V}
    (hs : s.is_hyperplane) :
    ∃ f : V →ₗ[𝕜] 𝕜, f ≠ 0 ∧ ∃ β : 𝕜, s = linearHyperplane f β := by
  rcases hs with ⟨hsne, hcodim⟩
  rcases s.eq_bot_or_nonempty with rfl | ⟨p, hp⟩
  · exact (hsne rfl).elim
  let q : V →ₗ[𝕜] (V ⧸ s.direction) := s.direction.mkQ
  have hQpos : 0 < Module.finrank 𝕜 (V ⧸ s.direction) := by
    omega
  letI : Nontrivial (V ⧸ s.direction) :=
    Module.nontrivial_of_finrank_pos hQpos
  obtain ⟨z, hz⟩ : ∃ z : V ⧸ s.direction, z ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp hQpos
  obtain ⟨φ, hφz⟩ : ∃ φ : Module.Dual 𝕜 (V ⧸ s.direction), φ z ≠ 0 :=
    Module.Projective.exists_dual_ne_zero 𝕜 hz
  have hφ : (φ : (V ⧸ s.direction) →ₗ[𝕜] 𝕜) ≠ 0 := by
    intro hzero
    have : φ z = 0 := by simp [hzero]
    exact hφz this
  have hker_finrank : Module.finrank 𝕜 (LinearMap.ker φ) = 0 := by
    have hker_add :
        Module.finrank 𝕜 (LinearMap.ker φ) + 1 =
          Module.finrank 𝕜 (V ⧸ s.direction) := by
      simpa using Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    omega
  have hker : LinearMap.ker φ = ⊥ := by
    have hsub : Subsingleton (LinearMap.ker φ) :=
      Module.finrank_zero_iff.mp hker_finrank
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact congrArg Subtype.val (hsub.elim ⟨x, hx⟩ 0)
  let f : V →ₗ[𝕜] 𝕜 := φ.comp q
  have hf : f ≠ 0 := by
    intro hf0
    apply hφ
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective s.direction y
    simpa [f, q] using LinearMap.congr_fun hf0 x
  refine ⟨f, hf, f p, ?_⟩
  ext x
  rw [mem_linearHyperplane_iff]
  constructor
  · intro hx
    have hq : q x = q p := by
      exact (Submodule.Quotient.eq s.direction).2 <|
        (vsub_right_mem_direction_iff_mem hp x).2 hx
    simpa [f, q] using congrArg φ hq
  · intro hx
    have hqx : q x - q p ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      have : f x - f p = 0 := sub_eq_zero.mpr hx
      simpa [f, q, map_sub] using this
    have hzero : q x - q p = 0 := by
      have : q x - q p ∈ (⊥ : Submodule 𝕜 (V ⧸ s.direction)) := by
        simpa [hker] using hqx
      simpa using this
    exact (vsub_right_mem_direction_iff_mem hp x).1 <|
      (Submodule.Quotient.eq s.direction).1 (sub_eq_zero.mp hzero)

end AffineSubspace

end FiniteDimensional

end LinearHyperplaneDivisionRing

section LinearHyperplaneField

variable {𝕜 : Type*} {V : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Two nontrivial scalar linear equations cut out the same affine hyperplane exactly when one
equation is obtained from the other by multiplying both sides by one common nonzero scalar. -/
theorem linearHyperplane_eq_iff (f g : V →ₗ[𝕜] 𝕜) (β β' : 𝕜)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    linearHyperplane f β = linearHyperplane g β' ↔
      ∃ a : 𝕜ˣ, g = (a : 𝕜) • f ∧ β' = (a : 𝕜) * β := by
  constructor
  · intro hH
    rcases linearHyperplane_nonempty f β hf with ⟨x₀, hx₀⟩
    have hx₀' : x₀ ∈ linearHyperplane g β' := by simpa [hH] using hx₀
    have hx₀f : f x₀ = β := mem_linearHyperplane_iff.mp hx₀
    have hx₀g : g x₀ = β' := mem_linearHyperplane_iff.mp hx₀'
    have hker : LinearMap.ker f = LinearMap.ker g := by
      ext x
      constructor
      · intro hx
        have hxH : x + x₀ ∈ linearHyperplane f β := by
          rw [mem_linearHyperplane_iff]
          calc
            f (x + x₀) = f x + f x₀ := map_add _ _ _
            _ = β := by simp [LinearMap.mem_ker.mp hx, hx₀f]
        have hxH' : x + x₀ ∈ linearHyperplane g β' := by simpa [hH] using hxH
        rw [LinearMap.mem_ker]
        have hsum : g x + g x₀ = β' := by
          simpa [map_add] using (mem_linearHyperplane_iff.mp hxH')
        have hsum' : g x + g x₀ = 0 + g x₀ := by simpa [hx₀g] using hsum
        exact add_right_cancel hsum'
      · intro hx
        have hxH : x + x₀ ∈ linearHyperplane g β' := by
          rw [mem_linearHyperplane_iff]
          calc
            g (x + x₀) = g x + g x₀ := map_add _ _ _
            _ = β' := by simp [LinearMap.mem_ker.mp hx, hx₀g]
        have hxH' : x + x₀ ∈ linearHyperplane f β := by simpa [hH] using hxH
        rw [LinearMap.mem_ker]
        have hsum : f x + f x₀ = β := by
          simpa [map_add] using (mem_linearHyperplane_iff.mp hxH')
        have hsum' : f x + f x₀ = 0 + f x₀ := by simpa [hx₀f] using hsum
        exact add_right_cancel hsum'
    obtain ⟨x, hx⟩ :
        ∃ x : V, f x = 1 := (LinearMap.range_eq_top.mp <|
          Module.Dual.range_eq_top_of_ne_zero hf) 1
    let a : 𝕜 := g x
    have hgf : ∀ y : V, g y = a * f y := by
      intro y
      have hyker : y - (f y) • x ∈ LinearMap.ker f := by
        rw [LinearMap.mem_ker]
        simp [f.map_sub, f.map_smul, hx]
      have hyker' : y - (f y) • x ∈ LinearMap.ker g := by
        rw [← hker]
        exact hyker
      rw [LinearMap.mem_ker] at hyker'
      calc
        g y = g ((f y) • x) := by
          have : g y - g ((f y) • x) = 0 := by
            simpa [g.map_sub] using hyker'
          exact sub_eq_zero.mp this
        _ = (f y) * g x := by simp [g.map_smul]
        _ = a * f y := by simp [a, mul_comm]
    have ha : a ≠ 0 := by
      intro ha0
      apply hg
      ext y
      rw [hgf y, ha0]
      simp
    let u : 𝕜ˣ := Units.mk0 a ha
    refine ⟨u, ?_, ?_⟩
    · ext y
      simp [hgf y, u, mul_comm]
    · calc
        β' = g x₀ := hx₀g.symm
        _ = a * f x₀ := hgf x₀
        _ = (u : 𝕜) * β := by simp [u, a, hx₀f]
  · rintro ⟨a, hag, hβ'⟩
    ext x
    rw [mem_linearHyperplane_iff, mem_linearHyperplane_iff]
    constructor
    · intro hx
      calc
        g x = ((a : 𝕜) • f) x := by simp [hag]
        _ = (a : 𝕜) * f x := by simp
        _ = (a : 𝕜) * β := by simp [hx]
        _ = β' := hβ'.symm
    · intro hx
      have hx' : (a : 𝕜) * f x = (a : 𝕜) * β := by
        calc
          (a : 𝕜) * f x = ((a : 𝕜) • f) x := by simp
          _ = g x := by simp [hag]
          _ = β' := hx
          _ = (a : 𝕜) * β := hβ'
      exact mul_left_cancel₀ (Units.ne_zero a) hx'

end LinearHyperplaneField

section PairingLinearFunctional

variable {𝕜 : Type*} {V : Type*} {Y : Type*}
variable [CommSemiring 𝕜] [AddCommMonoid V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]

/-- A pairing normal is nontrivial exactly when the pairing equation is nonzero at some point. -/
theorem pairingLinear_flip_ne_zero_iff_exists_pairing_ne_zero (b : Y) :
    HasLinearPairing.pairingLinear.flip b ≠ (0 : Module.Dual 𝕜 V) ↔
      ∃ x : V, ⟪x, b⟫ₚ ≠ (0 : 𝕜) := by
  constructor
  · intro hb
    by_contra h
    apply hb
    ext x
    have hx0 : ⟪x, b⟫ₚ = (0 : 𝕜) := by
      by_contra hx0
      exact h ⟨x, hx0⟩
    exact hx0
  · rintro ⟨x, hx⟩ hzero
    exact hx <| by
      simpa [HasLinearPairing.pairing_eq_pairingLinear] using LinearMap.congr_fun hzero x

end PairingLinearFunctional

section PairingHyperplane

variable {𝕜 : Type*} {V : Type*} {Y : Type*}
variable [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]

/-- The affine hyperplane cut out by one pairing equation `⟪x, b⟫ₚ = β`. This is the canonical
pairing-level specialization of `linearHyperplane`. -/
def affineHyperplane (b : Y) (β : 𝕜) : AffineSubspace 𝕜 V :=
  linearHyperplane (HasLinearPairing.pairingLinear.flip b) β

/-- Membership in `affineHyperplane b β` is the pairing equation `⟪x, b⟫ₚ = β`. -/
@[simp] theorem mem_affineHyperplane_iff {b : Y} {x : V} {β : 𝕜} :
    x ∈ affineHyperplane b β ↔ ⟪x, b⟫ₚ = β := by
  change x ∈ linearHyperplane (HasLinearPairing.pairingLinear.flip b) β ↔
      HasPairing.pairing x b = β
  rw [mem_linearHyperplane_iff]
  rfl

end PairingHyperplane

section PairingHyperplaneFieldBasic

variable {𝕜 : Type*} {V : Type*} {Y : Type*}
variable [Field 𝕜]

variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]

/-- A nontrivial pairing functional cuts out a nonempty affine hyperplane. -/
theorem affineHyperplane_nonempty_of_nontrivial_pairing (b : Y) (β : 𝕜)
    (hb : ∃ x : V, ⟪x, b⟫ₚ ≠ (0 : 𝕜)) :
    Nonempty ((affineHyperplane b β : AffineSubspace 𝕜 V)) := by
  have hbflip : HasLinearPairing.pairingLinear.flip b ≠ (0 : Module.Dual 𝕜 V) :=
    (pairingLinear_flip_ne_zero_iff_exists_pairing_ne_zero b).2 hb
  simpa [affineHyperplane] using
    (linearHyperplane_nonempty (HasLinearPairing.pairingLinear.flip b) β hbflip)

theorem affineHyperplane_is_hyperplane_of_nontrivial_pairing (b : Y) (β : 𝕜)
    (hb : ∃ x : V, ⟪x, b⟫ₚ ≠ (0 : 𝕜)) :
    ((affineHyperplane b β : AffineSubspace 𝕜 V)).is_hyperplane := by
  have hbflip : HasLinearPairing.pairingLinear.flip b ≠ (0 : Module.Dual 𝕜 V) :=
    (pairingLinear_flip_ne_zero_iff_exists_pairing_ne_zero b).2 hb
  simpa [affineHyperplane] using
    (linearHyperplane_is_hyperplane (HasLinearPairing.pairingLinear.flip b) β hbflip)

section FiniteDimensional

variable [FiniteDimensional 𝕜 V]

namespace AffineSubspace

/-- If pairing normals represent all scalar-valued linear functionals via `flip`, then every
hyperplane is representable as one nontrivial pairing equation `⟪x, b⟫ₚ = β`. -/
theorem exists_eq_affineHyperplane_of_is_hyperplane_of_surjective_pairing
    (hflip :
      Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → Module.Dual 𝕜 V))
    {s : AffineSubspace 𝕜 V} (hs : s.is_hyperplane) :
    ∃ b : Y, (∃ x : V, ⟪x, b⟫ₚ ≠ (0 : 𝕜)) ∧
      ∃ β : 𝕜, s = affineHyperplane b β := by
  rcases exists_eq_linearHyperplane_of_is_hyperplane hs with ⟨f, hf, β, hs'⟩
  rcases hflip f with ⟨b, hb⟩
  have hbflip : HasLinearPairing.pairingLinear.flip b ≠ (0 : Module.Dual 𝕜 V) := by
    simpa [hb] using hf
  refine ⟨b, ?_, β, ?_⟩
  · exact (pairingLinear_flip_ne_zero_iff_exists_pairing_ne_zero b).1 hbflip
  · simpa [affineHyperplane, hb] using hs'

end AffineSubspace

end FiniteDimensional

end PairingHyperplaneFieldBasic

section PairingHyperplaneField

variable {𝕜 : Type*} {V : Type*} {Y : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing V Y 𝕜]

/-- When the map `b ↦ (x ↦ ⟪x, b⟫ₚ)` is injective, two nontrivial pairing equations cut out the
same affine hyperplane exactly when their parameters differ by a common nonzero scalar. -/
theorem affineHyperplane_eq_iff_of_pairing_injective
    (hflip :
      Function.Injective (HasLinearPairing.pairingLinear.flip : Y → Module.Dual 𝕜 V))
    (b b' : Y) (β β' : 𝕜)
    (hb : ∃ x : V, ⟪x, b⟫ₚ ≠ (0 : 𝕜))
    (hb' : ∃ x : V, ⟪x, b'⟫ₚ ≠ (0 : 𝕜)) :
    (affineHyperplane b β : AffineSubspace 𝕜 V) =
      (affineHyperplane b' β' : AffineSubspace 𝕜 V) ↔
      ∃ a : 𝕜ˣ, b' = (a : 𝕜) • b ∧ β' = (a : 𝕜) * β := by
  have hbflip : HasLinearPairing.pairingLinear.flip b ≠ (0 : Module.Dual 𝕜 V) :=
    (pairingLinear_flip_ne_zero_iff_exists_pairing_ne_zero b).2 hb
  have hbflip' : HasLinearPairing.pairingLinear.flip b' ≠ (0 : Module.Dual 𝕜 V) :=
    (pairingLinear_flip_ne_zero_iff_exists_pairing_ne_zero b').2 hb'
  constructor
  · intro hH
    have hlin :
        (linearHyperplane (HasLinearPairing.pairingLinear.flip b) β : AffineSubspace 𝕜 V) =
          linearHyperplane (HasLinearPairing.pairingLinear.flip b') β' := by
      simpa [affineHyperplane] using hH
    rcases (linearHyperplane_eq_iff
        (HasLinearPairing.pairingLinear.flip b)
        (HasLinearPairing.pairingLinear.flip b') β β' hbflip hbflip').1 hlin with
      ⟨a, hgf, hβ'⟩
    refine ⟨a, hflip ?_, hβ'⟩
    calc
      (HasLinearPairing.pairingLinear.flip b' : V →ₗ[𝕜] 𝕜) =
          ((a : 𝕜) • HasLinearPairing.pairingLinear.flip b) := hgf
      _ = HasLinearPairing.pairingLinear.flip ((a : 𝕜) • b) := by
        ext x
        simp
  · rintro ⟨a, hb_smul, hβ'⟩
    have hgf :
        (HasLinearPairing.pairingLinear.flip b' : V →ₗ[𝕜] 𝕜) =
          (a : 𝕜) • HasLinearPairing.pairingLinear.flip b := by
      calc
        (HasLinearPairing.pairingLinear.flip b' : V →ₗ[𝕜] 𝕜) =
            HasLinearPairing.pairingLinear.flip ((a : 𝕜) • b) := by simp [hb_smul]
        _ = (a : 𝕜) • HasLinearPairing.pairingLinear.flip b := by
          ext x
          simp
    have hlin :
        (linearHyperplane (HasLinearPairing.pairingLinear.flip b) β : AffineSubspace 𝕜 V) =
          linearHyperplane (HasLinearPairing.pairingLinear.flip b') β' :=
      (linearHyperplane_eq_iff
        (HasLinearPairing.pairingLinear.flip b)
        (HasLinearPairing.pairingLinear.flip b') β β' hbflip hbflip').2 ⟨a, hgf, hβ'⟩
    simpa [affineHyperplane] using hlin

end PairingHyperplaneField

section InnerProductHyperplane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
local instance : HasLinearPairing V V ℝ := instHasLinearPairingInner V

/-- A nonzero vector induces a nonzero inner-product functional. -/
theorem innerₗ_flip_ne_zero {b : V} (hb : b ≠ 0) :
    ((innerₗ V).flip b : Module.Dual ℝ V) ≠ 0 := by
  intro hzero
  have hbb : ⟪b, b⟫ = (0 : ℝ) := by
    simpa [innerₗ_apply_apply] using LinearMap.congr_fun hzero b
  exact hb <| inner_self_eq_zero.mp hbb

/-- The map `b ↦ (x ↦ ⟪x, b⟫)` is injective. -/
theorem innerₗ_flip_injective :
    Function.Injective ((innerₗ V).flip : V → Module.Dual ℝ V) := by
  intro b b' hflip
  apply ext_inner_left ℝ
  intro x
  have hx : ((innerₗ V).flip b) x = ((innerₗ V).flip b') x := by
    simpa using LinearMap.congr_fun hflip x
  simpa [innerₗ_apply_apply, real_inner_comm] using hx

/-- Membership in the inner-product affine hyperplane is the equation `⟪x, b⟫ = β`. -/
@[simp] theorem mem_affineHyperplane_iff_inner {b x : V} {β : ℝ} :
    x ∈ affineHyperplane b β ↔ ⟪x, b⟫ = β := by
  change x ∈ linearHyperplane ((innerₗ V).flip b) β ↔ ⟪x, b⟫ = β
  rw [mem_linearHyperplane_iff]
  simp [innerₗ_apply_apply, real_inner_comm]

/-- A nondegenerate affine hyperplane `⟪x, b⟫ = β` is nonempty. -/
theorem affineHyperplane_nonempty (b : V) (β : ℝ) (hb : b ≠ 0) :
    Nonempty ((affineHyperplane b β : AffineSubspace ℝ V)) := by
  change Nonempty (linearHyperplane ((innerₗ V).flip b) β)
  exact linearHyperplane_nonempty ((innerₗ V).flip b) β (innerₗ_flip_ne_zero hb)

/-- Theorem 1.3 (1), stated coordinate-free: for `β : ℝ` and nonzero `b` in a real inner product
space, the level set `affineHyperplane b β = {x | ⟪x, b⟫ = β}` is a hyperplane. -/
-- Proof sketch: `affineHyperplane b β` is the affine fiber of the nonzero linear functional
-- `x ↦ ⟪x, b⟫`; quotienting by its kernel gives a one-dimensional scalar range.
theorem affineHyperplane_is_hyperplane {b : V} {β : ℝ} (hb : b ≠ 0) :
    ((affineHyperplane b β : AffineSubspace ℝ V)).is_hyperplane := by
  exact affineHyperplane_is_hyperplane_of_nontrivial_pairing b β <|
    (pairingLinear_flip_ne_zero_iff_exists_pairing_ne_zero b).1 (innerₗ_flip_ne_zero hb)

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- In finite dimensions, every scalar-valued linear functional on a real inner product space is
represented by one normal vector via `b ↦ (x ↦ ⟪x, b⟫)`. -/
theorem innerₗ_flip_surjective :
    Function.Surjective ((innerₗ V).flip : V → Module.Dual ℝ V) := by
  intro f
  let b : V := (InnerProductSpace.toDual ℝ V).symm f.toContinuousLinearMap
  have hpoint (x : V) : f x = ⟪x, b⟫ := by
    calc
      f x = (f.toContinuousLinearMap : V →L[ℝ] ℝ) x := rfl
      _ = ⟪b, x⟫ := by
        simp [b]
      _ = ⟪x, b⟫ := real_inner_comm _ _
  refine ⟨b, ?_⟩
  ext x
  calc
    ((innerₗ V).flip b) x = ⟪x, b⟫ := by
      simp [innerₗ_apply_apply, real_inner_comm]
    _ = f x := by
      simpa using (hpoint x).symm

namespace AffineSubspace

/-- Theorem 1.3 (2), stated as a specialized bridge: every hyperplane in a finite-dimensional real
inner product space is representable as one nontrivial inner-product equation `⟪x, b⟫ = β`.
The primitive owner statement is the pairing-level theorem
`exists_eq_affineHyperplane_of_is_hyperplane_of_surjective_pairing`; this theorem is the
Riesz-style specialization. -/
theorem exists_eq_affineHyperplane_of_is_hyperplane {s : AffineSubspace ℝ V}
    (hs : s.is_hyperplane) :
    ∃ b : V, b ≠ 0 ∧ ∃ β : ℝ, s = affineHyperplane b β := by
  rcases
      (AffineSubspace.exists_eq_affineHyperplane_of_is_hyperplane_of_surjective_pairing
        innerₗ_flip_surjective hs) with
    ⟨b, hbpair, β, hs'⟩
  have hb : b ≠ 0 := by
    intro hb0
    rcases hbpair with ⟨x, hx⟩
    exact hx <| by simp [hb0]
  exact ⟨b, hb, β, hs'⟩

end AffineSubspace

end FiniteDimensional

/-- Theorem 1.3 (3), stated coordinate-free: two nondegenerate normal equations define the same
affine hyperplane exactly when their parameters differ by a common nonzero scalar multiple. -/
-- Proof sketch: compare the associated nonzero linear functionals cutting out the same codimension
-- one affine subspace, show their kernels coincide, and deduce proportionality of the normals and
-- of the corresponding constants; encode the common nonzero scalar as a unit of `ℝ`.
theorem affineHyperplane_eq_iff {b b' : V} {β β' : ℝ} (hb : b ≠ 0) (hb' : b' ≠ 0) :
    (affineHyperplane b β : AffineSubspace ℝ V) =
      (affineHyperplane b' β' : AffineSubspace ℝ V) ↔
      ∃ a : ℝˣ, b' = (a : ℝ) • b ∧ β' = (a : ℝ) * β := by
  have hbpair : ∃ x : V, ⟪x, b⟫ₚ ≠ (0 : ℝ) :=
    (pairingLinear_flip_ne_zero_iff_exists_pairing_ne_zero b).1 (innerₗ_flip_ne_zero hb)
  have hbpair' : ∃ x : V, ⟪x, b'⟫ₚ ≠ (0 : ℝ) :=
    (pairingLinear_flip_ne_zero_iff_exists_pairing_ne_zero b').1 (innerₗ_flip_ne_zero hb')
  simpa [instHasLinearPairingInner] using
    (affineHyperplane_eq_iff_of_pairing_injective
      innerₗ_flip_injective b b' β β'
      hbpair hbpair')

end InnerProductHyperplane
