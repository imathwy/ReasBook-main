import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Proposition_18_3_3

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` surfaced only general graded tensor-product APIs, not a
-- canonical singular-cohomology cup-product owner beyond the direct quotient-level construction
-- used here, so this item keeps the source-facing singular-cohomology statements explicit.

/-- The Koszul sign `(-1)^(pq)` appearing in graded commutativity. -/
def cupProductKoszulSign (p q : ℤ) : ℤ :=
  (-1 : ℤ) ^ Int.natAbs (p * q)

/-- Closed singular `n`-cochains on `X` with coefficients in `R`. -/
abbrev singularCocycles (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :=
  {φ : singularCochains R X n // singularCochains.coboundary φ = 0}

/-- Cohomology-class equivalence on singular cocycles: in positive degree, two cocycles define the
same class when they differ by a coboundary; in degree `0`, equality is literal. -/
def singularCohomologyRel (R : Type u) [CommRing R] (X : TopCat.{u}) :
    ∀ {n : ℕ}, singularCocycles R X n → singularCocycles R X n → Prop
  | 0, φ, ψ => φ.1 = ψ.1
  | n + 1, φ, ψ => ∃ η : singularCochains R X n,
      ψ.1 = φ.1 + singularCochains.coboundary η

/-- The singular-cocycle relation is reflexive. -/
theorem singularCohomologyRel_refl (R : Type u) [CommRing R] (X : TopCat.{u}) :
    ∀ {n : ℕ} (φ : singularCocycles R X n), singularCohomologyRel R X φ φ := sorry

/-- The singular-cocycle relation is symmetric. -/
theorem singularCohomologyRel_symm (R : Type u) [CommRing R] (X : TopCat.{u}) :
    ∀ {n : ℕ} {φ ψ : singularCocycles R X n},
      singularCohomologyRel R X φ ψ → singularCohomologyRel R X ψ φ := sorry

/-- The singular-cocycle relation is transitive. -/
theorem singularCohomologyRel_trans (R : Type u) [CommRing R] (X : TopCat.{u}) :
    ∀ {n : ℕ} {φ ψ χ : singularCocycles R X n},
      singularCohomologyRel R X φ ψ →
        singularCohomologyRel R X ψ χ →
          singularCohomologyRel R X φ χ := sorry

/-- The setoid of singular-cohomology classes represented by closed singular `n`-cochains. -/
def singularCohomologySetoid (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    Setoid (singularCocycles R X n) where
  r := fun φ ψ ↦ singularCohomologyRel R X φ ψ
  iseqv :=
    ⟨singularCohomologyRel_refl R X, singularCohomologyRel_symm R X,
      singularCohomologyRel_trans R X⟩

/-- Singular cohomology classes represented as cocycles modulo coboundaries. -/
abbrev singularCohomologyClasses (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :=
  Quotient (singularCohomologySetoid R X n)

scoped[singularCohomology] notation "Hˢ[" n "](" X "; " R ")" =>
  singularCohomologyClasses R X n

open scoped singularCohomology

namespace singularCohomologyClasses

/-- Reindex a singular cohomology class along an equality of degrees. -/
def reindex (R : Type u) [CommRing R] (X : TopCat.{u}) {m n : ℕ}
    (h : m = n) : Hˢ[m](X; R) → Hˢ[n](X; R) :=
  fun α ↦ Eq.ndrec α h

@[simp] theorem reindex_rfl (R : Type u) [CommRing R] (X : TopCat.{u}) {n : ℕ}
    (α : Hˢ[n](X; R)) :
    reindex R X rfl α = α :=
  rfl

end singularCohomologyClasses

/-- Two represented singular cohomology classes are equal exactly when their cocycle
representatives are equivalent modulo coboundaries. -/
@[simp] theorem singularCohomologyClass_eq_iff
    (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ)
    (φ ψ : singularCocycles R X n) :
    Quotient.mk (singularCohomologySetoid R X n) φ =
      Quotient.mk (singularCohomologySetoid R X n) ψ ↔
        singularCohomologyRel R X φ ψ := sorry

namespace singularCohomologyClasses

variable (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ)

/-- The zero singular cochain is closed, so it determines the zero cohomology class. -/
theorem zero_closed :
    singularCochains.coboundary (0 : singularCochains R X n) = 0 := by
  simp

end singularCohomologyClasses

/-- The zero class in singular cohomology. -/
def singularCohomologyZeroClass (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    Hˢ[n](X; R) :=
  Quotient.mk (singularCohomologySetoid R X n)
    ⟨0, singularCohomologyClasses.zero_closed R X n⟩

@[simp] theorem singularCohomologyZeroClass_def
    (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) :
    singularCohomologyZeroClass R X n =
      Quotient.mk (singularCohomologySetoid R X n)
        ⟨0, singularCohomologyClasses.zero_closed R X n⟩ :=
  rfl

/-- The singular cochain cup product of two cocycles is again a cocycle. -/
theorem singularCochainCup_closed (R : Type u) [CommRing R] (X : TopCat.{u}) (p q : ℕ)
    (φ : singularCocycles R X p) (ψ : singularCocycles R X q) :
    singularCochains.coboundary (singularCochains.cup φ.1 ψ.1) = 0 := sorry

/-- The cocycle representative of the descended singular cup product on cohomology classes. -/
def singularCohomologyCupRepresentative
    (R : Type u) [CommRing R] (X : TopCat.{u}) (p q : ℕ)
    (φ : singularCocycles R X p) (ψ : singularCocycles R X q) :
    singularCocycles R X (p + q) :=
  ⟨singularCochains.cup φ.1 ψ.1,
    singularCochainCup_closed R X p q φ ψ⟩

/-- Theorem 18.3.4 (1). The singular-cochain cup product from Construction 18.3.2 respects the
cohomology-class relation in both arguments, hence descends to a well-defined multiplication on
singular cohomology classes. -/
theorem singularCohomologyCup_descends
    (R : Type u) [CommRing R] (X : TopCat.{u}) (p q : ℕ)
    {φ₁ φ₂ : singularCocycles R X p} {ψ₁ ψ₂ : singularCocycles R X q} :
    singularCohomologyRel R X φ₁ φ₂ →
      singularCohomologyRel R X ψ₁ ψ₂ →
        singularCohomologyRel R X
          (singularCohomologyCupRepresentative R X p q φ₁ ψ₁)
          (singularCohomologyCupRepresentative R X p q φ₂ ψ₂) := sorry

/-- The cup product on singular cohomology classes induced by `singularCochainCup`. -/
def singularCohomologyCup (R : Type u) [CommRing R] (X : TopCat.{u}) (p q : ℕ) :
    Hˢ[p](X; R) → Hˢ[q](X; R) → Hˢ[p + q](X; R) :=
  Quotient.map₂ (singularCohomologyCupRepresentative R X p q)
    (fun _ _ hφ _ _ hψ ↦ singularCohomologyCup_descends R X p q hφ hψ)

namespace singularCohomologyClasses

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {p q : ℕ}

/-- The quotient-level singular cup product on cohomology classes. -/
abbrev cup (α : Hˢ[p](X; R)) (β : Hˢ[q](X; R)) : Hˢ[p + q](X; R) :=
  singularCohomologyCup R X p q α β

/-- The quotient-level singular cup product on cohomology classes. -/
scoped[singularCohomology] infixr:70 " ⌣ " => singularCohomologyClasses.cup

end singularCohomologyClasses

/-- Pullback of a singular `n`-cochain along a map of spaces. -/
def singularCochainPullback (R : Type u) [CommRing R] {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    singularCochains R Y n → singularCochains R X n :=
  fun φ σ ↦
    φ (f.hom.comp σ)

/-- Pulling back a closed singular cochain along a map of spaces again gives a cocycle. -/
theorem singularCocyclePullback_closed (R : Type u) [CommRing R] {X Y : TopCat.{u}}
    (f : X ⟶ Y) (n : ℕ) (φ : singularCocycles R Y n) :
    singularCochains.coboundary (singularCochainPullback R f n φ.1) = 0 := sorry

/-- Pullback of a singular cohomology cocycle representative along a map of spaces. -/
def singularCocyclePullback (R : Type u) [CommRing R] {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    singularCocycles R Y n → singularCocycles R X n :=
  fun φ ↦
    ⟨singularCochainPullback R f n φ.1, singularCocyclePullback_closed R f n φ⟩

/-- Pullback respects the singular-cohomology equivalence relation on cocycle representatives. -/
theorem singularCohomologyRel_pullback (R : Type u) [CommRing R] {X Y : TopCat.{u}}
    (f : X ⟶ Y) (n : ℕ) {φ ψ : singularCocycles R Y n} :
    singularCohomologyRel R Y φ ψ →
      singularCohomologyRel R X
        (singularCocyclePullback R f n φ)
        (singularCocyclePullback R f n ψ) := sorry

/-- Pullback on singular cohomology classes induced by precomposition of singular cocycles. -/
def singularCohomologyPullback (R : Type u) [CommRing R] {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    Hˢ[n](Y; R) → Hˢ[n](X; R) :=
  Quotient.map (singularCocyclePullback R f n)
    (fun _ _ h ↦ singularCohomologyRel_pullback R f n h)

/-- Pullback on singular cohomology classes sends a represented cocycle class to the pullback of
that cocycle representative. -/
@[simp] theorem singularCohomologyPullback_onRepresentatives
    (R : Type u) [CommRing R] {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCocycles R Y n) :
    singularCohomologyPullback R f n
        (Quotient.mk (singularCohomologySetoid R Y n) φ) =
      Quotient.mk (singularCohomologySetoid R X n)
        (singularCocyclePullback R f n φ) :=
  rfl

/-- The constant singular `0`-cochain with value `1`. -/
def singularZeroCochainOne (R : Type u) [CommRing R] (X : TopCat.{u}) :
    singularCochains R X 0 :=
  fun _ ↦ 1

/-- The constant singular `0`-cochain with value `1` is closed. -/
theorem singularZeroCochainOne_closed (R : Type u) [CommRing R] (X : TopCat.{u}) :
    singularCochains.coboundary (singularZeroCochainOne R X) = 0 := sorry

/-- The degree-`0` unit class in singular cohomology. -/
def singularCohomologyOneClass (R : Type u) [CommRing R] (X : TopCat.{u}) :
    Hˢ[0](X; R) :=
  Quotient.mk (singularCohomologySetoid R X 0)
    ⟨singularZeroCochainOne R X, singularZeroCochainOne_closed R X⟩

/-- Integer scaling preserves the cocycle condition on singular cochains. -/
theorem singularCocycleZsmul_closed (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ)
    (m : ℤ) (φ : singularCocycles R X n) :
    singularCochains.coboundary (m • φ.1) = 0 := sorry

/-- Integer scaling of a singular-cocycle representative. -/
def singularCocycleZsmul (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) (m : ℤ) :
    singularCocycles R X n → singularCocycles R X n :=
  fun φ ↦
    ⟨m • φ.1, singularCocycleZsmul_closed R X n m φ⟩

/-- Integer scaling respects the singular-cohomology equivalence relation on cocycle
representatives. -/
theorem singularCohomologyRel_zsmul (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) (m : ℤ)
    {φ ψ : singularCocycles R X n} :
    singularCohomologyRel R X φ ψ →
      singularCohomologyRel R X
        (singularCocycleZsmul R X n m φ)
        (singularCocycleZsmul R X n m ψ) := sorry

/-- Integer scaling on singular cohomology classes. -/
def singularCohomologyClassZsmul (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) (m : ℤ) :
    Hˢ[n](X; R) → Hˢ[n](X; R) :=
  Quotient.map (singularCocycleZsmul R X n m)
    (fun _ _ h ↦ singularCohomologyRel_zsmul R X n m h)

/-- Integer scaling on singular cohomology classes sends a represented cocycle class to the class
of the scaled cocycle representative. -/
@[simp] theorem singularCohomologyClassZsmul_onRepresentatives
    (R : Type u) [CommRing R] (X : TopCat.{u}) (n : ℕ) (m : ℤ)
    (φ : singularCocycles R X n) :
    singularCohomologyClassZsmul R X n m
        (Quotient.mk (singularCohomologySetoid R X n) φ) =
      Quotient.mk (singularCohomologySetoid R X n)
        (singularCocycleZsmul R X n m φ) :=
  rfl

/-- The cup product on quotient classes sends chosen cocycle representatives to their cocycle-level
cup-product representative. -/
@[simp] theorem singularCohomologyCup_onRepresentatives
    (R : Type u) [CommRing R] (X : TopCat.{u}) (p q : ℕ)
    (φ : singularCocycles R X p) (ψ : singularCocycles R X q) :
    (Quotient.mk (singularCohomologySetoid R X p) φ : Hˢ[p](X; R)) ⌣
        (Quotient.mk (singularCohomologySetoid R X q) ψ : Hˢ[q](X; R)) =
      Quotient.mk (singularCohomologySetoid R X (p + q))
        (singularCohomologyCupRepresentative R X p q φ ψ) := sorry

/-- Theorem 18.3.4 (2). The descended singular cohomology cup product is natural with respect to
pullback along maps of spaces. -/
theorem singularCohomologyCup_naturality (R : Type u) [CommRing R] {X Y : TopCat.{u}}
    (f : X ⟶ Y) (p q : ℕ) (α : Hˢ[p](Y; R)) (β : Hˢ[q](Y; R)) :
    singularCohomologyPullback R f (p + q) (α ⌣ β) =
      singularCohomologyPullback R f p α ⌣ singularCohomologyPullback R f q β := sorry

/-- Theorem 18.3.4 (3). The descended singular cohomology cup product is unital in degree `0`. -/
theorem singularCohomologyCup_unital (R : Type u) [CommRing R] (X : TopCat.{u}) (p : ℕ)
    (α : Hˢ[p](X; R)) :
    singularCohomologyClasses.reindex R X (Nat.zero_add p)
        (singularCohomologyOneClass R X ⌣ α) = α ∧
      singularCohomologyClasses.reindex R X (Nat.add_zero p)
        (α ⌣ singularCohomologyOneClass R X) = α := sorry

/-- The degree-`0` unit class acts as a left unit for the singular cohomology cup product. -/
theorem singularCohomologyCup_left_unit
    (R : Type u) [CommRing R] (X : TopCat.{u}) (p : ℕ)
    (α : Hˢ[p](X; R)) :
    singularCohomologyClasses.reindex R X (Nat.zero_add p)
        (singularCohomologyOneClass R X ⌣ α) = α :=
  (singularCohomologyCup_unital R X p α).1

/-- The degree-`0` unit class acts as a right unit for the singular cohomology cup product. -/
theorem singularCohomologyCup_right_unit
    (R : Type u) [CommRing R] (X : TopCat.{u}) (p : ℕ)
    (α : Hˢ[p](X; R)) :
    singularCohomologyClasses.reindex R X (Nat.add_zero p)
        (α ⌣ singularCohomologyOneClass R X) = α :=
  (singularCohomologyCup_unital R X p α).2

/-- Theorem 18.3.4 (4). The descended singular cohomology cup product is associative on
homogeneous cohomology classes. -/
theorem singularCohomologyCup_assoc (R : Type u) [CommRing R] (X : TopCat.{u}) (p q r : ℕ)
    (α : Hˢ[p](X; R)) (β : Hˢ[q](X; R)) (γ : Hˢ[r](X; R)) :
    singularCohomologyClasses.cup (singularCohomologyClasses.cup α β) γ =
      singularCohomologyClasses.reindex R X (Nat.add_assoc p q r).symm
        (singularCohomologyClasses.cup α (singularCohomologyClasses.cup β γ)) := sorry

/-- Theorem 18.3.4 (5). The descended singular cohomology cup product is graded-commutative with
the Koszul sign `(-1)^(pq)`. -/
theorem singularCohomologyCup_gradedComm (R : Type u) [CommRing R] (X : TopCat.{u}) (p q : ℕ)
    (α : Hˢ[p](X; R)) (β : Hˢ[q](X; R)) :
    singularCohomologyClasses.reindex R X (Nat.add_comm q p) (β ⌣ α) =
      singularCohomologyClassZsmul R X (p + q)
        (cupProductKoszulSign (p : ℤ) (q : ℤ))
        (α ⌣ β) := sorry
