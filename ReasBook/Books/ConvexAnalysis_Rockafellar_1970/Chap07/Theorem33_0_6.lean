import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing

noncomputable section

open Matrix

section CurryingRepresentation

variable {R U X Y : Type*}
variable [CommSemiring R]
variable [AddCommMonoid U] [Module R U]
variable [AddCommMonoid X] [Module R X]
variable [AddCommMonoid Y] [Module R Y]

/-!
Source/core/bridge triage:

- `source-facing`: first state the intrinsic owner layer: bilinear kernels correspond to unique
  curried linear maps `U →ₗ[R] X →ₗ[R] Y`.
- `core/canonical`: this owner is exactly mathlib's `IsBilinearMap.toLinearMap`.
- `book-facing`: then specialize `Y = R` and recover the intrinsic pairing owner
  `HasLinearPairing U X R`; the dual-valued owner surface `U →ₗ[R] Module.Dual R X` is treated
  as a bridge view of this owner.
- `bridge/view`: the textbook formula `(A u) ⬝ᵥ xStar` is then recovered as a finite-coordinate
  realization through `dotProductEquiv R n` in a separate bridge section.

Domain-style sampling used here:
- `IsBilinearMap.toLinearMap`;
- `U →ₗ[R] X →ₗ[R] Y`;
- `HasLinearPairing U X R`;
- `Module.Dual R X`;
- `dotProductEquiv R n`;
- `dotProduct_eq_iff`.

Primitive data vs. derived API:
- primitive input: a bilinear kernel `K : U → X → Y`;
- primitive owner: `hK.toLinearMap : U →ₗ[R] X →ₗ[R] Y`;
- derived owner: for scalar codomain, `hK.toHasLinearPairing : HasLinearPairing U X R`;
- bridge owner: the dual-valued linear-map surface `U →ₗ[R] Module.Dual R X`;
- derived bridge API: the coordinate representative `hK.toDotProductLinearMap` and the finite
  coordinate unique-existence theorem phrased with `⬝ᵥ`.

Layer target: keep dual and `⬝ᵥ` theorem surfaces as derived views while keeping the canonical
statement at the primitive curried-linear-map layer.
-/

namespace IsBilinearMap

/-- Any curried linear map representing `K` agrees with the canonical owner
`hK.toLinearMap`. -/
theorem toLinearMap_unique
    {K : U → X → Y} (hK : IsBilinearMap R K)
    (A : U →ₗ[R] X →ₗ[R] Y)
    (hA : ∀ u x, K u x = A u x) :
    A = hK.toLinearMap := by
  ext u x
  calc
    A u x = K u x := (hA u x).symm
    _ = hK.toLinearMap u x := rfl

/-- Every bilinear kernel has a unique intrinsic representation as a curried linear map. -/
theorem existsUnique_curriedLinearMap_representation
    {K : U → X → Y} (hK : IsBilinearMap R K) :
    ∃! A : U →ₗ[R] X →ₗ[R] Y,
      ∀ u x, K u x = A u x := by
  refine ⟨hK.toLinearMap, ?_, ?_⟩
  · intro u x
    rfl
  · intro A hA
    exact hK.toLinearMap_unique A hA

end IsBilinearMap

/-- Every bilinear kernel has a unique intrinsic representation as a curried linear map. -/
theorem existsUnique_curriedLinearMap_representation_of_isBilinearMap
    {K : U → X → Y} (hK : IsBilinearMap R K) :
    ∃! A : U →ₗ[R] X →ₗ[R] Y,
      ∀ u x, K u x = A u x :=
  hK.existsUnique_curriedLinearMap_representation

/-- A kernel is bilinear iff it has a unique intrinsic representation by a curried linear map. -/
theorem isBilinearMap_iff_existsUnique_curriedLinearMap_representation
    (K : U → X → Y) :
    IsBilinearMap R K ↔
      ∃! A : U →ₗ[R] X →ₗ[R] Y,
        ∀ u x, K u x = A u x := by
  constructor
  · intro hK
    exact hK.existsUnique_curriedLinearMap_representation
  · rintro ⟨A, hA, _⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u₁ u₂ x
      calc
        K (u₁ + u₂) x = A (u₁ + u₂) x := hA (u₁ + u₂) x
        _ = (A u₁ + A u₂) x := by simp
        _ = A u₁ x + A u₂ x := by rfl
        _ = K u₁ x + K u₂ x := by simp [hA]
    · intro c u x
      calc
        K (c • u) x = A (c • u) x := hA (c • u) x
        _ = (c • A u) x := by simp
        _ = c • A u x := by rfl
        _ = c • K u x := by simp [hA]
    · intro u x₁ x₂
      calc
        K u (x₁ + x₂) = A u (x₁ + x₂) := hA u (x₁ + x₂)
        _ = A u x₁ + A u x₂ := by simp
        _ = K u x₁ + K u x₂ := by simp [hA]
    · intro c u x
      calc
        K u (c • x) = A u (c • x) := hA u (c • x)
        _ = c • A u x := by simp
        _ = c • K u x := by simp [hA]

end CurryingRepresentation

section DualRepresentation

variable {R U X : Type*}
variable [CommSemiring R]
variable [AddCommMonoid U] [Module R U]
variable [AddCommMonoid X] [Module R X]

namespace IsBilinearMap

/-- Scalar specialization of `toLinearMap` packaged in the project's intrinsic pairing owner. -/
abbrev toHasLinearPairing
    {K : U → X → R} (hK : IsBilinearMap R K) :
    HasLinearPairing U X R where
  pairingLinear := hK.toLinearMap

/-- Any pairing owner representing `K` agrees with the canonical owner `hK.toHasLinearPairing`. -/
theorem toHasLinearPairing_unique
    {K : U → X → R} (hK : IsBilinearMap R K)
    (A : HasLinearPairing U X R)
    (hA : ∀ u x, K u x = A.pairingLinear u x) :
    A = hK.toHasLinearPairing := by
  cases A with
  | mk pairingLinear =>
      apply congrArg (fun f => HasLinearPairing.mk (X := U) (Y := X) (𝕜 := R) f)
      ext u x
      exact (hA u x).symm

/-- Every scalar-valued bilinear kernel has a unique representation in the intrinsic pairing
owner `HasLinearPairing U X R`. -/
theorem existsUnique_hasLinearPairing_representation
    {K : U → X → R} (hK : IsBilinearMap R K) :
    ∃! A : HasLinearPairing U X R,
      ∀ u x, K u x = A.pairingLinear u x := by
  refine ⟨hK.toHasLinearPairing, ?_, ?_⟩
  · intro u x
    rfl
  · intro A hA
    exact hK.toHasLinearPairing_unique A hA

/-- Every scalar-valued bilinear kernel has a unique intrinsic representation as a linear map into
`Module.Dual R X`. -/
theorem existsUnique_dualLinearMap_representation
    {K : U → X → R} (hK : IsBilinearMap R K) :
    ∃! A : U →ₗ[R] Module.Dual R X,
      ∀ u xStar, K u xStar = A u xStar := by
  simpa [Module.Dual] using hK.existsUnique_curriedLinearMap_representation

end IsBilinearMap

/-- Every scalar-valued bilinear kernel has a unique representation in the intrinsic pairing
owner `HasLinearPairing U X R`. -/
theorem existsUnique_hasLinearPairing_representation_of_isBilinearMap
    {K : U → X → R} (hK : IsBilinearMap R K) :
    ∃! A : HasLinearPairing U X R,
      ∀ u x, K u x = A.pairingLinear u x :=
  hK.existsUnique_hasLinearPairing_representation

/-- Every scalar-valued bilinear kernel has a unique intrinsic representation as a linear map into
`Module.Dual R X`. -/
theorem existsUnique_dualLinearMap_representation_of_isBilinearMap
    {K : U → X → R} (hK : IsBilinearMap R K) :
    ∃! A : U →ₗ[R] Module.Dual R X,
      ∀ u xStar, K u xStar = A u xStar :=
  hK.existsUnique_dualLinearMap_representation

/-- Bridge equivalence between the intrinsic pairing owner and the dual-linear-map owner. -/
theorem existsUnique_hasLinearPairing_representation_iff_existsUnique_dualLinearMap_representation
    (K : U → X → R) :
    (∃! A : HasLinearPairing U X R,
      ∀ u x, K u x = A.pairingLinear u x) ↔
      ∃! A : U →ₗ[R] Module.Dual R X,
        ∀ u x, K u x = A u x := by
  constructor
  · rintro ⟨A, hA, huniq⟩
    refine ⟨A.pairingLinear, hA, ?_⟩
    intro B hB
    have hEq : (HasLinearPairing.mk (X := U) (Y := X) (𝕜 := R) B) = A :=
      huniq _ hB
    exact congrArg
      (fun P : HasLinearPairing U X R =>
        HasLinearPairing.pairingLinear (X := U) (Y := X) (𝕜 := R) (self := P)) hEq
  · rintro ⟨A, hA, huniq⟩
    refine ⟨HasLinearPairing.mk (X := U) (Y := X) (𝕜 := R) A, hA, ?_⟩
    intro B hB
    apply congrArg (fun f => HasLinearPairing.mk (X := U) (Y := X) (𝕜 := R) f)
    exact huniq B.pairingLinear hB

/-- Theorem33.0.6 (canonical pairing-owner form): a scalar kernel is bilinear exactly when it has
a unique intrinsic representation in `HasLinearPairing U X R`. -/
theorem isBilinearMap_iff_existsUnique_hasLinearPairing_representation
    (K : U → X → R) :
    IsBilinearMap R K ↔
      ∃! A : HasLinearPairing U X R,
        ∀ u x, K u x = A.pairingLinear u x := by
  constructor
  · intro hK
    exact hK.existsUnique_hasLinearPairing_representation
  · rintro ⟨A, hA, _⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u₁ u₂ x
      calc
        K (u₁ + u₂) x = A.pairingLinear (u₁ + u₂) x := hA (u₁ + u₂) x
        _ = (A.pairingLinear u₁ + A.pairingLinear u₂) x := by simp
        _ = A.pairingLinear u₁ x + A.pairingLinear u₂ x := by rfl
        _ = K u₁ x + K u₂ x := by simp [hA]
    · intro c u x
      calc
        K (c • u) x = A.pairingLinear (c • u) x := hA (c • u) x
        _ = (c • A.pairingLinear u) x := by simp
        _ = c • A.pairingLinear u x := by rfl
        _ = c • K u x := by simp [hA]
    · intro u x₁ x₂
      calc
        K u (x₁ + x₂) = A.pairingLinear u (x₁ + x₂) := hA u (x₁ + x₂)
        _ = A.pairingLinear u x₁ + A.pairingLinear u x₂ := by simp
        _ = K u x₁ + K u x₂ := by simp [hA]
    · intro c u x
      calc
        K u (c • x) = A.pairingLinear u (c • x) := hA u (c • x)
        _ = c • A.pairingLinear u x := by simp
        _ = c • K u x := by simp [hA]

/-- Scalar-valued specialization of the curried owner theorem, expressed with the dual owner
surface. -/
theorem isBilinearMap_iff_existsUnique_dualLinearMap_representation
    (K : U → X → R) :
    IsBilinearMap R K ↔
      ∃! A : U →ₗ[R] Module.Dual R X,
        ∀ u xStar, K u xStar = A u xStar := by
  rw [isBilinearMap_iff_existsUnique_hasLinearPairing_representation]
  exact existsUnique_hasLinearPairing_representation_iff_existsUnique_dualLinearMap_representation K

/-- Bridge form of Theorem33.0.6 on the dual-linear-map owner surface. -/
theorem isBilinearMap_iff_existsUnique_linearMap_representation
    (K : U → X → R) :
    IsBilinearMap R K ↔
      ∃! A : U →ₗ[R] Module.Dual R X,
        ∀ u xStar, K u xStar = A u xStar :=
  isBilinearMap_iff_existsUnique_dualLinearMap_representation K

end DualRepresentation

section DotProductBridge

variable {R U n : Type*}
variable [CommSemiring R]
variable [AddCommMonoid U] [Module R U]
variable [Fintype n]

namespace LinearMap

/-- A kernel of the form `(u, xStar) ↦ (A u) ⬝ᵥ xStar` is bilinear. -/
theorem isBilinearMap_dotProduct
    (A : U →ₗ[R] (n → R)) :
    IsBilinearMap R (fun u xStar ↦ (A u) ⬝ᵥ xStar) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u₁ u₂ xStar
    simp
  · intro c u xStar
    simp
  · intro u xStar₁ xStar₂
    simp
  · intro c u xStar
    simp

end LinearMap

namespace IsBilinearMap

/-- The finite-coordinate representative transported from the canonical dual-valued owner through
`dotProductEquiv`. -/
def toDotProductLinearMap
    {K : U → (n → R) → R} (hK : IsBilinearMap R K) :
    U →ₗ[R] (n → R) := by
  classical
  exact (dotProductEquiv R n).symm.toLinearMap.comp hK.toLinearMap

/-- The coordinate representative obtained from `hK.toLinearMap` recovers the original bilinear
kernel through `⬝ᵥ`. -/
theorem toDotProductLinearMap_apply
    {K : U → (n → R) → R} (hK : IsBilinearMap R K)
    (u : U) (xStar : n → R) :
    K u xStar = (hK.toDotProductLinearMap u) ⬝ᵥ xStar := by
  classical
  change hK.toLinearMap u xStar =
      ((dotProductEquiv R n) ((dotProductEquiv R n).symm (hK.toLinearMap u))) xStar
  simp

/-- Any linear map representing a bilinear kernel through the coordinate pairing agrees with the
canonical coordinate representative transported from `hK.toLinearMap`. -/
theorem toDotProductLinearMap_unique
    {K : U → (n → R) → R} (hK : IsBilinearMap R K)
    (A : U →ₗ[R] (n → R))
    (hA : ∀ u xStar, K u xStar = (A u) ⬝ᵥ xStar) :
    A = hK.toDotProductLinearMap := by
  apply LinearMap.ext
  intro u
  exact (dotProduct_eq_iff).1 (fun xStar ↦ by
    calc
      (A u) ⬝ᵥ xStar = K u xStar := (hA u xStar).symm
      _ = (hK.toDotProductLinearMap u) ⬝ᵥ xStar := hK.toDotProductLinearMap_apply u xStar)

/-- Every bilinear kernel on `U × (n → R)` has a unique linear-map representation through the
finite-coordinate pairing `⬝ᵥ`. -/
theorem existsUnique_dotProductLinearMap_representation
    {K : U → (n → R) → R} (hK : IsBilinearMap R K) :
    ∃! A : U →ₗ[R] (n → R),
      ∀ u xStar, K u xStar = (A u) ⬝ᵥ xStar := by
  refine ⟨hK.toDotProductLinearMap, hK.toDotProductLinearMap_apply, ?_⟩
  intro A hA
  exact hK.toDotProductLinearMap_unique A hA

end IsBilinearMap

/-- Every bilinear kernel on `U × (n → R)` has a unique linear-map representation through the
finite-coordinate pairing `⬝ᵥ`. -/
theorem existsUnique_dotProductLinearMap_representation_of_isBilinearMap
    {K : U → (n → R) → R} (hK : IsBilinearMap R K) :
    ∃! A : U →ₗ[R] (n → R),
      ∀ u xStar, K u xStar = (A u) ⬝ᵥ xStar :=
  hK.existsUnique_dotProductLinearMap_representation

/-- Finite-coordinate bridge form of Theorem33.0.6: on kernels `U × (n → R)`, bilinearity is
equivalent to representation through `K(u, xStar) = (A u) ⬝ᵥ xStar` by a unique linear map `A`. -/
theorem isBilinearMap_iff_existsUnique_dotProductLinearMap_representation
    (K : U → (n → R) → R) :
    IsBilinearMap R K ↔
      ∃! A : U →ₗ[R] (n → R),
        ∀ u xStar, K u xStar = (A u) ⬝ᵥ xStar := by
  constructor
  · intro hK
    exact hK.existsUnique_dotProductLinearMap_representation
  · rintro ⟨A, hA, _⟩
    have hK : K = fun u xStar ↦ (A u) ⬝ᵥ xStar := funext (fun u ↦ funext (fun xStar ↦ hA u xStar))
    simpa [hK] using A.isBilinearMap_dotProduct

end DotProductBridge
