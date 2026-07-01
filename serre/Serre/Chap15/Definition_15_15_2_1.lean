import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w x

open scoped Pointwise
open Representation

section

variable {A : Type u} [CommRing A]
variable {K : Type v} [CommRing K] [Algebra A K]
variable {G : Type w} [Monoid G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

/-
Domain-style sampling for this file:
* `source-facing`: stable `A`-lattices in a `K`-linear `G`-representation and their reduction
  modulo the maximal ideal.
* `core/canonical`: `Subrepresentation`, `Subrepresentation.toRepresentation`,
  `Representation.quotient`, and `Submodule.IsLattice`.
* `bridge/view`: scalar restriction of a `K`-linear representation along `A → K`.

Primitive data vs derived API:
* primitive data: a stable lattice is a `Subrepresentation` of the restricted representation
  together with the lattice property on the underlying `A`-submodule;
* derived API: the induced representation on the lattice and on its maximal-ideal quotient.
-/

namespace Representation

private def restrictScalarsEnd :
    Module.End K E →* Module.End A E where
  toFun := LinearMap.restrictScalars A
  map_one' := by
    ext x
    simp
  map_mul' _ _ := by
    ext x
    simp

/-- The `A`-linear representation underlying a `K`-linear representation after restricting
scalars along `A → K`. -/
abbrev restrictScalars (A : Type u) [CommRing A] [Algebra A K] [Module A E] [IsScalarTower A K E]
    (ρ : Representation K G E) : Representation A G E :=
  restrictScalarsEnd.comp ρ

@[simp] theorem restrictScalars_apply
    (ρ : Representation K G E) (g : G) (x : E) :
    ρ.restrictScalars A g x = ρ g x :=
  rfl

end Representation

/-- A `G`-stable `A`-lattice inside a `K[G]`-module `E`. -/
structure StableLattice (A : Type u) [CommRing A] [Algebra A K] [Module A E]
    [IsScalarTower A K E] (ρ : Representation K G E)
    extends Subrepresentation (ρ.restrictScalars A) where
  isLattice : Submodule.IsLattice K toSubmodule

namespace StableLattice

instance {ρ : Representation K G E} (L : StableLattice A ρ) :
    Submodule.IsLattice K L.toSubmodule :=
  L.isLattice

/-- A unit of `K` rescales a stable lattice to another stable lattice. -/
instance {ρ : Representation K G E} : SMul Kˣ (StableLattice A ρ) where
  smul a L :=
    { toSubmodule := a • L.toSubmodule
      apply_mem_toSubmodule g := by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨ρ g x, L.apply_mem_toSubmodule g hx, ?_⟩
        change ↑a • ρ g x = ρ g (↑a • x)
        exact ((ρ g).map_smul ↑a x).symm
      isLattice := by
        letI : Submodule.IsLattice K L.toSubmodule := L.isLattice
        refine
          { fg := by
              obtain ⟨s, hs⟩ := Submodule.IsLattice.fg (A := K) (M := L.toSubmodule)
              rw [← hs]
              rw [show (a • Submodule.span A (↑s : Set E) : Submodule A E) =
                Submodule.span A (a • (↑s : Set E)) by
                  simpa using (Submodule.smul_span (R := A) (a := a) (s := (↑s : Set E)))]
              have : Finite (a • (s : Set E) : Set E) := Finite.Set.finite_image _ _
              exact Submodule.fg_span (Set.toFinite (a • (s : Set E)))
            span_eq_top := by
              change Submodule.span K (a • (L.toSubmodule : Set E)) = ⊤
              rw [Submodule.span_smul]
              rw [Submodule.IsLattice.span_eq_top (A := K) (M := L.toSubmodule)]
              ext x
              constructor
              · intro _
                trivial
              · intro _
                refine ⟨↑a⁻¹ • x, ?_, ?_⟩
                · trivial
                · simp [smul_smul] } }

@[simp] theorem toSubmodule_smul {ρ : Representation K G E} (a : Kˣ) (L : StableLattice A ρ) :
    (a • L).toSubmodule = a • L.toSubmodule :=
  rfl

/-- Stable lattices are determined by their underlying stable subrepresentation. -/
@[ext] theorem ext {ρ : Representation K G E} {L M : StableLattice A ρ}
    (h : L.toSubrepresentation = M.toSubrepresentation) : L = M := by
  cases L
  cases M
  cases h
  simp

/-- Stable lattices are determined by their underlying `A`-submodule. -/
theorem ext_toSubmodule {ρ : Representation K G E} {L M : StableLattice A ρ}
    (h : L.toSubmodule = M.toSubmodule) : L = M := by
  apply ext
  exact Subrepresentation.toSubmodule_injective h

/-- Units of `K` act on stable lattices by homothety. -/
instance {ρ : Representation K G E} : MulAction Kˣ (StableLattice A ρ) where
  smul := (· • ·)
  one_smul L := by
    apply ext_toSubmodule
    simp [toSubmodule_smul]
  mul_smul a b L := by
    apply ext_toSubmodule
    simp [toSubmodule_smul, smul_smul]

/-- The induced action on a stable lattice is the restriction of the ambient action. -/
@[simp] theorem toRepresentation_apply_coe {ρ : Representation K G E} (L : StableLattice A ρ)
    (g : G) (x : L.toSubmodule) :
    ((L.toRepresentation g x : L.toSubmodule) : E) = ρ g x := rfl

end StableLattice

section Existence

variable (A : Type u) [CommRing A]
variable {K' : Type v} [Field K'] [Algebra A K'] [IsFractionRing A K']
variable {G' : Type w} [Monoid G'] [Finite G']
variable {V : Type x} [AddCommGroup V] [Module A V] [Module K' V] [IsScalarTower A K' V]
variable [FiniteDimensional K' V]

/-- Every finite-dimensional `K'`-representation of a finite monoid admits a `G'`-stable
`A`-lattice. This is the canonical existence theorem for the owner `StableLattice`. -/
theorem Representation.exists_stableLattice (ρ : Representation K' G' V) :
    Nonempty (StableLattice A ρ) := by
  let b : Module.Basis (Fin (Module.finrank K' V)) K' V := Module.finBasis K' V
  let S : Set V := Set.range fun p : G' × Fin (Module.finrank K' V) ↦ ρ p.1 (b p.2)
  let N : Submodule A V := Submodule.span A S
  -- Start from the `A`-span of all translates of a finite `K'`-basis.
  have hbasis_mem (i : Fin (Module.finrank K' V)) : b i ∈ N := by
    change b i ∈ Submodule.span A S
    apply Submodule.subset_span
    refine ⟨(1, i), ?_⟩
    simp
  -- Since the original basis lies in `N`, the `K'`-span of `N` is all of `V`.
  have hspan_top : Submodule.span K' (N : Set V) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact hbasis_mem i
  -- Acting by `g` just changes the orbit parameter from `h` to `g * h`.
  have hstable (g : G') {x : V} (hx : x ∈ N) : ρ g x ∈ N := by
    change x ∈ Submodule.span A S at hx
    change ρ g x ∈ Submodule.span A S
    refine Submodule.span_induction (p := fun y _ ↦ ρ g y ∈ Submodule.span A S) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with ⟨⟨h, i⟩, rfl⟩
      change ρ g (ρ h (b i)) ∈ Submodule.span A S
      have hmul : ρ g (ρ h (b i)) = ρ (g * h) (b i) := by
        simpa [Module.End.mul_eq_comp, LinearMap.comp_apply] using
          congrArg (fun f : Module.End K' V ↦ f (b i)) (MonoidHom.map_mul ρ g h).symm
      rw [hmul]
      apply Submodule.subset_span
      exact ⟨(g * h, i), rfl⟩
    · simpa using (Submodule.zero_mem (Submodule.span A S))
    · intro y z _ _ hy hz
      simpa using (Submodule.add_mem (Submodule.span A S) hy hz)
    · intro a y _ hy
      simpa [LinearMap.map_smul_of_tower] using (Submodule.span A S).smul_mem a hy
  -- The orbit set is finite, so its span is finitely generated over `A`.
  have hfg : N.FG := by
    change (Submodule.span A S).FG
    exact Submodule.fg_span (Set.finite_range _)
  have hIsLattice : Submodule.IsLattice K' N :=
    Submodule.IsLattice.mk hfg hspan_top
  refine ⟨{ toSubmodule := N, apply_mem_toSubmodule := ?_, isLattice := hIsLattice }⟩
  intro g x hx
  simpa [Representation.restrictScalars_apply] using hstable g hx

end Existence

end

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type v} [CommRing K] [Algebra A K]
variable {G : Type w} [Monoid G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

namespace StableLattice

variable {ρ : Representation K G E}

/-- The maximal-ideal multiple `𝔪_A L` inside a stable lattice `L`. -/
abbrev maximalIdealSubmodule (L : StableLattice A ρ) : Submodule A L.toSubmodule :=
  IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule)

/-- Definition 15-15.2-1: for a `G`-stable `A`-lattice `L` in a `K[G]`-module `E`, its reduction
modulo the maximal ideal is the quotient `L / 𝔪_A L`. -/
abbrev reduction (L : StableLattice A ρ) : Type _ :=
  L.toSubmodule ⧸ L.maximalIdealSubmodule

instance (L : StableLattice A ρ) : SMul (IsLocalRing.ResidueField A) L.reduction where
  smul c x :=
    Quotient.liftOn' c
      (fun a ↦
        Quotient.liftOn' x
          (fun y ↦ (Submodule.Quotient.mk (a • y) : L.reduction))
          (by
            intro y z hyz
            apply Quotient.sound
            apply (Submodule.quotientRel_def _).2
            rw [show a • y - a • z = a • (y - z) by simp [smul_sub]]
            exact L.maximalIdealSubmodule.smul_mem a <|
              (Submodule.quotientRel_def _).1 hyz))
      (by
        intro a b hab
        refine Quotient.inductionOn' x ?_
        intro y
        apply Quotient.sound
        apply (Submodule.quotientRel_def _).2
        rw [show a • y - b • y = (a - b) • y by simp [sub_smul]]
        rw [Submodule.mem_smul_top_iff (IsLocalRing.maximalIdeal A) (N := L.toSubmodule)
          ((a - b) • y)]
        exact Submodule.smul_mem_smul ((Submodule.quotientRel_def _).1 hab) y.property)

instance (L : StableLattice A ρ) : Module (IsLocalRing.ResidueField A) L.reduction where
  one_smul := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro y
    change (Submodule.Quotient.mk ((1 : A) • y) : L.reduction) = Submodule.Quotient.mk y
    simp
  mul_smul := by
    intro a b x
    refine Quotient.inductionOn' a ?_
    intro a
    refine Quotient.inductionOn' b ?_
    intro b
    refine Quotient.inductionOn' x ?_
    intro y
    change (Submodule.Quotient.mk (((a * b) : A) • y) : L.reduction) =
      (Submodule.Quotient.mk ((a : A) • (b • y)) : L.reduction)
    simp [mul_smul]
  smul_zero := by
    intro a
    refine Quotient.inductionOn' a ?_
    intro a
    change (Submodule.Quotient.mk ((a : A) • (0 : L.toSubmodule)) : L.reduction) = 0
    simp
  smul_add := by
    intro a x y
    refine Quotient.inductionOn' a ?_
    intro a
    refine Quotient.inductionOn' x ?_
    intro x
    refine Quotient.inductionOn' y ?_
    intro y
    change (Submodule.Quotient.mk ((a : A) • (x + y)) : L.reduction) =
      (Submodule.Quotient.mk ((a : A) • x) : L.reduction) +
        (Submodule.Quotient.mk ((a : A) • y) : L.reduction)
    simp [smul_add]
  add_smul := by
    intro a b x
    refine Quotient.inductionOn' a ?_
    intro a
    refine Quotient.inductionOn' b ?_
    intro b
    refine Quotient.inductionOn' x ?_
    intro x
    change (Submodule.Quotient.mk (((a + b) : A) • x) : L.reduction) =
      (Submodule.Quotient.mk ((a : A) • x) : L.reduction) +
        (Submodule.Quotient.mk ((b : A) • x) : L.reduction)
    simp [add_smul]
  zero_smul := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro y
    change (Submodule.Quotient.mk ((0 : A) • y) : L.reduction) = 0
    simp

@[simp] theorem reduction_smul_mk (L : StableLattice A ρ) (a : A) (y : L.toSubmodule) :
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
        (Submodule.Quotient.mk y : L.reduction) =
      (Submodule.Quotient.mk (a • y) : L.reduction) :=
  rfl

-- Proof sketch: each `ρ g` preserves `L`, so the restricted `A`-linear action on `L` also
-- preserves every `A`-submodule of the form `I • L`, in particular `𝔪_A L`.
/-- The maximal-ideal multiple of a stable lattice is stable under the restricted action. -/
private theorem maximalIdealSubmodule_stable (L : StableLattice A ρ) (g : G) :
    L.maximalIdealSubmodule ≤
      Submodule.comap (L.toRepresentation g) L.maximalIdealSubmodule := by
  -- The maximal-ideal multiple is exactly an `I • ⊤` submodule, so the standard stability lemma
  -- for ideal multiples applies directly to the restricted lattice action.
  simpa [maximalIdealSubmodule] using
    (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal A) (L.toRepresentation g))

/-- Helper for Definition 15-15.2-1: the quotient `A`-representation on the reduction
`L / 𝔪_A L`. -/
private abbrev reductionAsRepresentation (L : StableLattice A ρ) :
    Representation A G L.reduction :=
  L.toRepresentation.quotient L.maximalIdealSubmodule (maximalIdealSubmodule_stable L)

/-- Helper for Definition 15-15.2-1: the quotient representation sends the class of `x`
to the class of the image of `x` upstairs. -/
@[simp] private theorem reductionAsRepresentation_apply_mk (L : StableLattice A ρ) (g : G)
    (x : L.toSubmodule) :
    reductionAsRepresentation L g (Submodule.Quotient.mk x : L.reduction) =
      (Submodule.Quotient.mk ((L.toRepresentation g) x) : L.reduction) := by
  -- The quotient action is implemented by `Submodule.mapQ`, so evaluating it on a class is
  -- exactly the quotient class of the image of any representative.
  simp [reductionAsRepresentation, Submodule.mapQ_apply]

/-- Helper for Definition 15-15.2-1: each quotient action map is linear over the residue field. -/
private theorem reduction_quotient_residueField_linear (L : StableLattice A ρ) (g : G) :
    ∀ c : IsLocalRing.ResidueField A, ∀ x : L.reduction,
      reductionAsRepresentation L g (c • x) = c • reductionAsRepresentation L g x := by
  intro c x
  -- The residue-field scalar is represented by an element of `A`, and every quotient class is
  -- represented by an element of `L`; reduce to that concrete situation.
  refine Quotient.inductionOn' c ?_
  intro a
  refine Quotient.inductionOn' x ?_
  intro y
  -- Evaluate the quotient map on a represented class, use `A`-linearity upstairs, then descend
  -- back to the quotient scalar action.
  calc
    reductionAsRepresentation L g
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
          (Submodule.Quotient.mk y : L.reduction)) =
        reductionAsRepresentation L g (Submodule.Quotient.mk (a • y) : L.reduction) := by
          rw [reduction_smul_mk]
    _ = (Submodule.Quotient.mk ((L.toRepresentation g) (a • y)) : L.reduction) := by
      rw [reductionAsRepresentation_apply_mk]
    _ = (Submodule.Quotient.mk (a • (L.toRepresentation g y)) : L.reduction) := by
      rw [LinearMap.map_smul]
    _ = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
          (Submodule.Quotient.mk ((L.toRepresentation g) y) : L.reduction) := by
      rw [reduction_smul_mk]

/-- Helper for Definition 15-15.2-1: the induced quotient action map viewed as a residue-field
linear endomorphism. -/
private def reductionLinearMap (L : StableLattice A ρ) (g : G) :
    L.reduction →ₗ[IsLocalRing.ResidueField A] L.reduction :=
  { toFun := reductionAsRepresentation L g
    map_add' := (reductionAsRepresentation L g).map_add
    map_smul' := reduction_quotient_residueField_linear L g }

/-- Helper for Definition 15-15.2-1: evaluating the reduced linear map on a quotient class
returns the quotient class of the image upstairs. -/
@[simp] private theorem reductionLinearMap_apply_mk (L : StableLattice A ρ) (g : G)
    (x : L.toSubmodule) :
    reductionLinearMap L g (Submodule.Quotient.mk x : L.reduction) =
      (Submodule.Quotient.mk ((L.toRepresentation g) x) : L.reduction) :=
  reductionAsRepresentation_apply_mk L g x

/-- Helper for Definition 15-15.2-1: the reduced linear map commutes with represented
residue-field scalars on quotient classes. -/
@[simp] private theorem reductionLinearMap_apply_smul_mk (L : StableLattice A ρ) (g : G)
    (a : A) (x : L.toSubmodule) :
    reductionLinearMap L g
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
          (Submodule.Quotient.mk x : L.reduction)) =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
        (Submodule.Quotient.mk ((L.toRepresentation g) x) : L.reduction) := by
  -- Pull the residue-field scalar through the reduced linear map using the quotient-linearity
  -- established when the quotient `A`-representation was upgraded to the residue field.
  calc
    reductionLinearMap L g
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
          (Submodule.Quotient.mk x : L.reduction)) =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
        reductionLinearMap L g (Submodule.Quotient.mk x : L.reduction) := by
          exact
            reduction_quotient_residueField_linear L g
              (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A)
              (Submodule.Quotient.mk x : L.reduction)
    -- Now rewrite the reduced action on the represented class by the upstairs action.
    _ = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
          (Submodule.Quotient.mk ((L.toRepresentation g) x) : L.reduction) := by
            rw [reductionLinearMap_apply_mk]

/-- Helper for Definition 15-15.2-1: the composite of two reduced action maps sends the class
of `x` to the class of the upstairs action by `g * h`. -/
@[simp] private theorem reductionLinearMap_mul_apply_mk (L : StableLattice A ρ) (g h : G)
    (x : L.toSubmodule) :
    (reductionLinearMap L g * reductionLinearMap L h) (Submodule.Quotient.mk x : L.reduction) =
      (Submodule.Quotient.mk ((L.toRepresentation (g * h)) x) : L.reduction) := by
  -- Evaluate the composition on a represented class and rewrite the upstairs action using the
  -- multiplicativity of the original representation.
  simp [reductionLinearMap_apply_mk]

/-- Helper for Definition 15-15.2-1: quotient endomorphisms of the reduction are determined by
their values on represented classes. -/
private theorem reductionLinearMap_ext_mk (L : StableLattice A ρ)
    {f g : L.reduction →ₗ[IsLocalRing.ResidueField A] L.reduction}
    (h : ∀ x : L.toSubmodule,
      f (Submodule.Quotient.mk x : L.reduction) =
        g (Submodule.Quotient.mk x : L.reduction)) :
    f = g := by
  -- Every reduction class has a representative upstairs, so agreement on those represented
  -- classes already determines the entire quotient endomorphism.
  refine DFunLike.ext _ _ ?_
  intro x
  rcases Submodule.Quotient.mk_surjective L.maximalIdealSubmodule x with ⟨y, rfl⟩
  exact h y

/-- Helper for Definition 15-15.2-1: the quotient action sends the identity element of `G`
to the identity endomorphism. -/
private theorem reductionLinearMap_map_one (L : StableLattice A ρ) :
    reductionLinearMap L 1 = 1 := by
  -- Quotient classes generate the reduction, so it is enough to check the identity law there.
  refine reductionLinearMap_ext_mk L ?_
  intro x
  -- Check the identity law on represented classes, where the quotient action is explicit.
  simp

/-- Helper for Definition 15-15.2-1: the quotient action respects multiplication in `G`. -/
private theorem reductionLinearMap_map_mul (L : StableLattice A ρ) (g h : G) :
    reductionLinearMap L (g * h) = reductionLinearMap L g * reductionLinearMap L h := by
  -- Again, quotient classes are a sufficient test family for equality of quotient endomorphisms.
  refine reductionLinearMap_ext_mk L ?_
  intro x
  -- On quotient classes, compare both sides using the explicit quotient computation rules.
  rw [reductionLinearMap_apply_mk]
  exact (reductionLinearMap_mul_apply_mk L g h x).symm

/-- The reduction of a stable lattice carries the induced
`(IsLocalRing.ResidueField A)[G]`-representation. -/
def reductionRepresentation (L : StableLattice A ρ) :
    Representation (IsLocalRing.ResidueField A) G L.reduction :=
  -- Route correction: define the reduced action by reusing the quotient representation over `A`,
  -- then upgrade each quotient map to residue-field linearity instead of rebuilding the action.
  { toFun := reductionLinearMap L
    map_one' := reductionLinearMap_map_one L
    map_mul' := reductionLinearMap_map_mul L }

instance (L : StableLattice A ρ) :
    Module (MonoidAlgebra (A ⧸ IsLocalRing.maximalIdeal A) G)
      L.reductionRepresentation.asModule := by
  change Module (MonoidAlgebra (IsLocalRing.ResidueField A) G)
    L.reductionRepresentation.asModule
  infer_instance

-- Proof sketch: `L.reductionRepresentation` is defined via `Submodule.mapQ`, so
-- evaluating it on a quotient class gives the quotient class of the image of any representative.
/-- Applying the induced action to the class of `x` gives the class of the action on `x`. -/
theorem reductionRepresentation_apply_mk (L : StableLattice A ρ) (g : G) (x : L.toSubmodule) :
    L.reductionRepresentation g (Submodule.Quotient.mk x : L.reduction) =
      (Submodule.Quotient.mk ((L.toRepresentation g) x) : L.reduction) :=
  -- This is the public computation rule obtained from the internal quotient-linear map formula.
  reductionLinearMap_apply_mk L g x

/-- Helper for Definition 15-15.2-1: on represented quotient classes, the reduced action of
`g * h` agrees with first acting by `h` and then by `g`. -/
@[simp] theorem reductionRepresentation_mul_apply_mk (L : StableLattice A ρ) (g h : G)
    (x : L.toSubmodule) :
    L.reductionRepresentation (g * h) (Submodule.Quotient.mk x : L.reduction) =
      L.reductionRepresentation g
        (L.reductionRepresentation h (Submodule.Quotient.mk x : L.reduction)) := by
  -- Rewrite both reduced actions on represented classes back upstairs.
  rw [reductionRepresentation_apply_mk, reductionRepresentation_apply_mk,
    reductionRepresentation_apply_mk]
  -- The representation law upstairs now gives the desired equality of quotient classes.
  simp

/-- Helper for Definition 15-15.2-1: each reduced action map commutes with residue-field scalar
multiplication on the quotient reduction. -/
@[simp] private theorem reductionRepresentation_smul (L : StableLattice A ρ) (g : G)
    (c : IsLocalRing.ResidueField A) (x : L.reduction) :
    L.reductionRepresentation g (c • x) = c • L.reductionRepresentation g x := by
  -- The final reduced representation is built from the quotient action, so the previously proved
  -- residue-field linearity of that quotient action applies verbatim after unfolding once.
  exact reduction_quotient_residueField_linear L g c x

/-- Helper for Definition 15-15.2-1: the reduced action commutes with residue-field scalars on
represented classes. -/
@[simp] theorem reductionRepresentation_apply_smul_mk (L : StableLattice A ρ) (g : G) (a : A)
    (x : L.toSubmodule) :
    L.reductionRepresentation g
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
          (Submodule.Quotient.mk x : L.reduction)) =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
        (Submodule.Quotient.mk ((L.toRepresentation g) x) : L.reduction) := by
  -- Reuse the internal linear-map computation on represented scalar multiples and then unfold
  -- the final representation owner once.
  simpa [reductionRepresentation] using reductionLinearMap_apply_smul_mk L g a x

end StableLattice

end
