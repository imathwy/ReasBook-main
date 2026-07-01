import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

variable {k V1 P1 V2 P2 : Type*} [Ring k]
  [AddCommGroup V1] [Module k V1] [AddTorsor V1 P1]
  [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2]

/- Text 1.10: an affine transformation is the canonical affine-map notion `P1 →ᵃ[k] P2`.
Specializing to module affine spaces (`P1 = V1`, `P2 = V2`) recovers the usual map-between-modules
view. The bridge below keeps the same owner object over the general affine-space layer and the
weakest scalar assumptions used by the midpoint-to-linearity construction. -/
#check (P1 →ᵃ[k] P2)

/- The textbook binary-combination formula is the owner theorem `AffineMap.apply_lineMap`. -/
recall AffineMap.apply_lineMap

/-
Source/core/bridge triage:
- `source-facing`: Text 1.10 characterizes affine maps by preservation of binary affine
  combinations.
- `core/canonical`: mathlib owns the notion `P1 →ᵃ[k] P2` together with the evaluation theorem
  `AffineMap.apply_lineMap`.
- `bridge/view`: the reverse direction is a thin constructor from the textbook formula to the
  owner abstraction.
- Primitive data vs derived API: the primitive source-facing datum is the function `T` together
  with its line-map preservation law; the affine map itself is the canonical owner object derived
  from that data, not an existential wrapper.
- Domain-style sampling: the relevant owner-side declarations here are
  `AffineMap.apply_lineMap`, `AffineMap.mk'`, the midpoint-to-linearity bridge
  `AddMonoidHom.ofMapMidpoint`, and the specialized real constructor
  `AffineMap.ofMapMidpoint`.
- Layer target: `bridge/view`; the source-facing line-map formula remains explicit, but the public
  output is the owner object `P1 →ᵃ[k] P2` on the weakest scalar layer used by the construction,
  rather than the stronger real/continuous specialization.
- Canonicalization decision record (this pass):
  - Codomain/ambient check: already at the intrinsic affine-space owner `P1 →ᵃ[k] P2`; no
    concrete model codomain remains.
  - Scalar/ambient check: `AffineMap.lineMap` and `AffineMap.mk'` live at `[Ring k]`; keep this
    minimal available owner layer and keep the midpoint bridge hypothesis `[Invertible (2 : k)]`.
  - Owner check: keep `AffineMap.ofLineMap` as the source-facing bridge owner and expose the
    primitive basepoint-explicit constructor `AffineMap.ofLineMapAt`.
  - Topology check: this item is not topology-facing.
  - Notation check: reuse existing owner notation (`→ᵃ[k]`, `lineMap`) without introducing a new
    notation layer.
-/
namespace AffineMap

variable (k) in
/-- Source-facing predicate for Text 1.10: `T` preserves all binary affine combinations. -/
def PreservesLineMap (T : P1 → P2) : Prop :=
  ∀ x y (t : k), T (lineMap x y t) = lineMap (T x) (T y) t

/-- Owner-form API: every affine map preserves binary affine combinations. -/
theorem preservesLineMap (f : P1 →ᵃ[k] P2) :
    PreservesLineMap k f := by
  intro x y t
  exact f.apply_lineMap x y t

variable (T : P1 → P2)
/-- Any function equal to an affine map preserves all binary affine combinations.
This direction uses only the affine-map owner API and does not need midpoint assumptions. -/
theorem preservesLineMap_of_exists_affineMap
    (hT : ∃ f : P1 →ᵃ[k] P2, f = T) :
    PreservesLineMap k T := by
  rcases hT with ⟨f, rfl⟩
  exact preservesLineMap (k := k) f

section

variable [Invertible (2 : k)]
variable (hT : PreservesLineMap k T)

/- Primitive constructor at the affine-owner layer: once a base point is fixed, a map preserving
line maps canonically induces an affine map with the same underlying function. -/
def ofLineMapAt (p₀ : P1) : P1 →ᵃ[k] P2 := by
  let A : V1 → V2 := fun x ↦ T (x +ᵥ p₀) -ᵥ T p₀
  let hT_midpoint : ∀ x y : P1, T (midpoint k x y) = midpoint k (T x) (T y) := by
    intro x y
    simpa [midpoint] using hT x y (⅟2 : k)
  let hA_mid : ∀ x y : V1, A (midpoint k x y) = midpoint k (A x) (A y) := by
    intro x y
    calc
      A (midpoint k x y) = T (midpoint k x y +ᵥ p₀) -ᵥ midpoint k (T p₀) (T p₀) := by
        simp [A, midpoint_self]
      _ = T (midpoint k (x +ᵥ p₀) (y +ᵥ p₀)) -ᵥ midpoint k (T p₀) (T p₀) := by
        simpa [midpoint_self] using
          congrArg (fun p ↦ T p -ᵥ midpoint k (T p₀) (T p₀)) (midpoint_vadd_midpoint x y p₀ p₀)
      _ = midpoint k (T (x +ᵥ p₀)) (T (y +ᵥ p₀)) -ᵥ midpoint k (T p₀) (T p₀) := by
        rw [hT_midpoint (x +ᵥ p₀) (y +ᵥ p₀)]
      _ = midpoint k (T (x +ᵥ p₀) -ᵥ T p₀) (T (y +ᵥ p₀) -ᵥ T p₀) := by
        simpa using midpoint_vsub_midpoint (T (x +ᵥ p₀)) (T (y +ᵥ p₀)) (T p₀) (T p₀)
      _ = midpoint k (A x) (A y) := rfl
  let hA_smul : ∀ (t : k) (x : V1), A (t • x) = t • A x := by
    intro t x
    calc
      A (t • x) = T (lineMap p₀ (x +ᵥ p₀) t) -ᵥ T p₀ := by
        simp [A, lineMap_apply]
      _ = lineMap (T p₀) (T (x +ᵥ p₀)) t -ᵥ T p₀ := by rw [hT p₀ (x +ᵥ p₀) t]
      _ = t • (T (x +ᵥ p₀) -ᵥ T p₀) := by
        exact lineMap_vsub_left (T p₀) (T (x +ᵥ p₀)) t
      _ = t • A x := rfl
  let hA_zero : A 0 = 0 := by simp [A]
  let linearPart : V1 →ₗ[k] V2 :=
    { AddMonoidHom.ofMapMidpoint k k A hA_zero hA_mid with
      map_smul' := hA_smul }
  exact AffineMap.mk' T linearPart p₀ fun x ↦ by
    have hx : linearPart (x -ᵥ p₀) = T x -ᵥ T p₀ := by
      simp [linearPart, A]
    rw [hx]
    exact (vsub_vadd (T x) (T p₀)).symm

@[simp] theorem ofLineMapAt_apply (p₀ : P1) (x : P1) :
    ofLineMapAt T hT p₀ x = T x := by
  unfold ofLineMapAt
  simp

/- Text 1.10: a map preserving binary affine combinations is the canonical affine map with the same
underlying function on affine spaces over `k`. This point-free form is the thin bridge obtained
from `ofLineMapAt` by choosing a base point. -/
noncomputable def ofLineMap : P1 →ᵃ[k] P2 := by
  classical
  exact ofLineMapAt T hT (Classical.choice (AddTorsor.nonempty : Nonempty P1))

@[simp] theorem ofLineMap_apply (x : P1) :
    ofLineMap T hT x = T x := by
  classical
  unfold ofLineMap
  simp [ofLineMapAt_apply]

/- The bridge owner returned by `ofLineMap` has exactly the source-facing function `T`. -/
theorem ofLineMap_eq : ofLineMap T hT = T := by
  funext x
  exact ofLineMap_apply (T := T) (hT := hT) x

/-- Owner-prefix constructor theorem: under midpoint assumptions, a map preserving binary affine
combinations is the underlying function of an affine map. -/
theorem PreservesLineMap.exists_affineMap (hT : PreservesLineMap k T) :
    ∃ f : P1 →ᵃ[k] P2, f = T := by
  exact ⟨ofLineMap T hT, ofLineMap_eq (T := T) (hT := hT)⟩

/-- Owner-prefix uniqueness theorem: under midpoint assumptions, the affine-map owner underlying
`T` is unique. -/
theorem PreservesLineMap.existsUnique_affineMap (hT : PreservesLineMap k T) :
    ∃! f : P1 →ᵃ[k] P2, f = T := by
  refine ⟨ofLineMap T hT, ofLineMap_eq (T := T) (hT := hT), ?_⟩
  intro f hf
  ext x
  rw [hf]
  exact ofLineMap_apply (T := T) (hT := hT) x

/-- Under midpoint assumptions, a map preserving binary affine combinations is the underlying
function of an affine map. -/
theorem exists_affineMap_of_preservesLineMap :
    PreservesLineMap k T → ∃ f : P1 →ᵃ[k] P2, f = T := by
  intro hT
  exact hT.exists_affineMap

/-- Under midpoint assumptions, the affine-map owner underlying `T` is unique. -/
theorem existsUnique_affineMap_of_preservesLineMap :
    PreservesLineMap k T → ∃! f : P1 →ᵃ[k] P2, f = T := by
  intro hT
  exact hT.existsUnique_affineMap

/-- Text 1.10 in owner form: preserving binary affine combinations identifies a unique affine-map
owner with underlying function `T`. -/
theorem preservesLineMap_iff_existsUnique_affineMap :
    PreservesLineMap k T ↔ ∃! f : P1 →ᵃ[k] P2, f = T := by
  constructor
  · intro hT
    exact hT.existsUnique_affineMap
  · intro hT
    rcases hT with ⟨f, hf, -⟩
    exact preservesLineMap_of_exists_affineMap (T := T) ⟨f, hf⟩

/-- Text 1.10 in owner form: preserving binary affine combinations is equivalent to being the
underlying function of an affine map. -/
theorem preservesLineMap_iff_exists_affineMap :
    PreservesLineMap k T ↔ ∃ f : P1 →ᵃ[k] P2, f = T := by
  constructor
  · intro hT
    exact hT.exists_affineMap
  · exact preservesLineMap_of_exists_affineMap (T := T)

end

end AffineMap
