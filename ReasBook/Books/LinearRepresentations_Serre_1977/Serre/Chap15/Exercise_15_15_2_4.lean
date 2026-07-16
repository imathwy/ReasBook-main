import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]

namespace Representation

local notation "k" => IsLocalRing.ResidueField A
local notation "ρA" => leftRegular A G
local notation "ρK" => leftRegular K G
local notation "ρk" => leftRegular k G
local notation "τk" => Representation.prod (trivial k G k) (trivial k G k)

section OrderTwoResidueCharacteristicTwo

variable [CharP (IsLocalRing.ResidueField A) 2]

/-- Helper for Exercise 15-15.2-4: a group of cardinality `2` has a unique nonidentity element,
and every element is either the identity or that generator, whose square is `1`. -/
private theorem order_two_generator_spec
    (hG : Nat.card G = 2) :
    ∃ s : G, s ≠ 1 ∧ (∀ g : G, g = 1 ∨ g = s) ∧ s * s = 1 := by
  rcases (Nat.card_eq_two_iff' (1 : G)).mp hG with ⟨s, hsne, hsuniq⟩
  refine ⟨s, hsne, ?_, ?_⟩
  · intro g
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr (hsuniq g hg)
  · by_cases hs2 : s * s = 1
    · exact hs2
    · have hss : s * s = s := hsuniq (s * s) hs2
      have : s = 1 := by
        simpa [mul_assoc] using congrArg (fun x => s⁻¹ * x) hss
      exact False.elim (hsne this)

/-- Helper for Exercise 15-15.2-4: transport subrepresentations along a representation
equivalence by mapping their underlying submodules. -/
private noncomputable def subrepresentationOrderIso_local
    {V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨ρ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, hy, rfl⟩
        refine ⟨σ g y, U.apply_mem_toSubmodule g hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv := by
    intro U
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e x := by
        simpa using congrArg e hxy
      subst this
      simp at hy
      exact hy
    · intro hx
      change x ∈
        Submodule.map e.symm.toLinearMap (Submodule.map e.toLinearMap U.toSubmodule)
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv := by
    intro U
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e.symm x := by
        simpa using congrArg e.symm hxy
      subst this
      simp at hy
      exact hy
    · intro hx
      change x ∈
        Submodule.map e.toLinearMap (Submodule.map e.symm.toLinearMap U.toSubmodule)
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  map_rel_iff' := by
    intro U V
    constructor
    · intro h x hx
      have hx' : e x ∈ U.toSubmodule.map e.toLinearMap := ⟨x, hx, rfl⟩
      rcases h hx' with ⟨y, hy, hxy⟩
      have : y = x := by
        apply e.toLinearEquiv.injective
        simpa using hxy
      simpa [this] using hy
    · intro h x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, h hy, rfl⟩

/-- Helper for Exercise 15-15.2-4: semisimplicity transports across representation
equivalences. -/
private theorem isSemisimpleRepresentation_of_equiv
    {V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (hρ : IsSemisimpleRepresentation ρ) :
    IsSemisimpleRepresentation σ := by
  letI : ComplementedLattice (Subrepresentation ρ) := hρ
  exact OrderIso.complementedLattice (subrepresentationOrderIso_local (G := G) e)

/-- Helper for Exercise 15-15.2-4: the trivial representation is semisimple because its
subrepresentations are exactly the ambient vector subspaces. -/
private theorem trivial_isSemisimpleRepresentation
    {V : Type*} [Field k] [AddCommGroup V] [Module k V] :
    IsSemisimpleRepresentation (Representation.trivial k G V) := by
  let e : Submodule k V ≃o Subrepresentation (Representation.trivial k G V) :=
    { toFun := fun W ↦
        { toSubmodule := W
          apply_mem_toSubmodule := by
            intro g x hx
            simpa [Representation.trivial] using hx }
      invFun := Subrepresentation.toSubmodule
      left_inv := by
        intro W
        rfl
      right_inv := by
        intro W
        rfl
      map_rel_iff' := by
        intro W W'
        rfl }
  letI : ComplementedLattice (Subrepresentation (Representation.trivial k G V)) :=
    OrderIso.complementedLattice e
  infer_instance

/-- Helper for Exercise 15-15.2-4: a trivial representation is semisimple. -/
private theorem isSemisimpleRepresentation_of_isTrivial
    {V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} (hρ : ρ.IsTrivial) :
    IsSemisimpleRepresentation ρ := by
  let e : ρ.Equiv (Representation.trivial k G V) :=
    Representation.Equiv.mk (LinearEquiv.refl k V) fun g ↦ by
      ext x
      simpa [Representation.trivial] using LinearMap.congr_fun (hρ.1 g) x
  have htriv : IsSemisimpleRepresentation (Representation.trivial k G V) := by
    exact trivial_isSemisimpleRepresentation
  exact isSemisimpleRepresentation_of_equiv (G := G) e.symm htriv

/-- Helper for Exercise 15-15.2-4: an `A`-linear equivalence between residue-field modules is
automatically `k`-linear because every residue scalar lifts from `A`. -/
private noncomputable def residue_field_linear_equiv_of_linear_equiv
    {V W : Type*}
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower A k V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower A k W]
    (e : V ≃ₗ[A] W) : V ≃ₗ[k] W where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' c x := by
    obtain ⟨a, rfl⟩ : ∃ a : A, (algebraMap A k a : k) = c := by
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using
        (IsLocalRing.residue_surjective (R := A) c)
    show e ((algebraMap A k a) • x) = ((algebraMap A k a : k) • e x)
    simpa only [IsScalarTower.algebraMap_smul] using e.map_smul a x

/-- Helper for Exercise 15-15.2-4: the reduction of a stable lattice still carries the natural
scalar tower from `A` to the residue field. -/
private instance reduction_isScalarTower (L : StableLattice A ρK) :
    IsScalarTower A k L.reduction where
  smul_assoc a c x := by
    -- Unpack both quotient representatives and compare the two induced quotient classes upstairs.
    refine Quotient.inductionOn' c ?_
    intro b
    refine Quotient.inductionOn' x ?_
    intro y
    change
      (Submodule.Quotient.mk (((a * b) : A) • y) : L.reduction) =
        (Submodule.Quotient.mk ((a : A) • (b • y)) : L.reduction)
    simp [smul_smul]

/-- Helper for Exercise 15-15.2-4: the coordinatewise finitely-supported ideal submodule is the
same as the ideal multiple of the full `Finsupp` module. -/
private theorem finsupp_submodule_eq_smul_top
    (X : Type*) (I : Ideal A) :
    Finsupp.submodule (α := X) (R := A) (fun _ => (I : Submodule A A)) =
      I • (⊤ : Submodule A (X →₀ A)) := by
  refine le_antisymm ?_ ?_
  · intro f hf
    classical
    rw [← f.sum_single]
    refine Submodule.sum_mem _ ?_
    intro x hx
    have hcoeff : f x ∈ I := hf x
    simpa [Finsupp.smul_single_one] using
      Submodule.smul_mem_smul hcoeff
        (show Finsupp.single x (1 : A) ∈ (⊤ : Submodule A (X →₀ A)) by simp)
  · intro f hf
    refine Submodule.smul_induction_on hf ?_ ?_
    · intro a ha g hg
      exact fun x ↦ by
        simpa [Finsupp.smul_apply] using I.mul_mem_right (g x) ha
    · intro f g hf hg
      exact fun x ↦ I.add_mem (hf x) (hg x)

/-- Helper for Exercise 15-15.2-4: reducing coefficients modulo the maximal ideal identifies the
quotient of `X →₀ A` by the maximal-ideal multiple with `X →₀ k`. -/
private noncomputable def finsupp_residue_quotient_equiv
    (X : Type*) :
    ((X →₀ A) ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (X →₀ A)))) ≃ₗ[A] (X →₀ k) := by
  let q : (X →₀ A) →ₗ[A] (X →₀ k) :=
    Finsupp.mapRange.linearMap (Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal A)).toLinearMap
  have hsurj : Function.Surjective q := by
    have hrange : q.range = ⊤ := by
      apply eq_top_iff.2
      intro f hf
      -- Each basis vector in the residue-field `Finsupp` lifts coefficientwise from `A`.
      rw [← f.sum_single]
      refine Submodule.sum_mem _ ?_
      intro x hx
      obtain ⟨b, hb⟩ : ∃ b : A, (Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal A) b : k) = f x := by
        simpa [IsLocalRing.ResidueField.algebraMap_eq] using
          (IsLocalRing.residue_surjective (R := A) (f x))
      refine ⟨Finsupp.single x b, ?_⟩
      ext y
      by_cases hxy : y = x
      · subst hxy
        simpa [q] using hb
      · simp [q, hxy]
    exact (LinearMap.range_eq_top.1 hrange)
  have hsub :
      LinearMap.ker q =
        Finsupp.submodule (α := X) (R := A)
          (fun _ => (IsLocalRing.maximalIdeal A : Submodule A A)) := by
    ext f
    constructor
    · intro hf
      intro x
      have hx : q f x = 0 := by
        simpa [LinearMap.mem_ker] using congrArg (fun g ↦ g x) hf
      exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa [q] using hx)
    · intro hf
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hf x)
  have hker :
      LinearMap.ker q = IsLocalRing.maximalIdeal A • (⊤ : Submodule A (X →₀ A)) := by
    calc
      LinearMap.ker q =
          Finsupp.submodule (α := X) (R := A)
            (fun _ => (IsLocalRing.maximalIdeal A : Submodule A A)) := hsub
      _ = IsLocalRing.maximalIdeal A • (⊤ : Submodule A (X →₀ A)) := by
        exact
          finsupp_submodule_eq_smul_top (A := A) (X := X) (I := IsLocalRing.maximalIdeal A)
  -- First rewrite the quotient by the maximal-ideal multiple as the quotient by the kernel,
  -- then apply the first isomorphism theorem for the coefficientwise reduction map.
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (q.quotKerEquivOfSurjective hsurj)

/-- Helper for Exercise 15-15.2-4: the quotient equivalence for coefficientwise reduction sends
the class of a finitely-supported function to the function of residue classes of its coordinates. -/
@[simp] private theorem finsupp_residue_quotient_equiv_apply_mk
    (X : Type*) (f : X →₀ A) :
    finsupp_residue_quotient_equiv (A := A) (X := X) (Submodule.Quotient.mk f) =
      Finsupp.mapRange
        (fun a : A ↦ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : k))
        (by simp) f := by
  rfl

set_option maxHeartbeats 50000000 in
/-- Helper for Exercise 15-15.2-4: transport the reduction of a coefficient-image lattice coming
from `A[G]` to the reduced regular coefficient module `k[G]`. -/
private noncomputable def regular_range_reduction_linear_equiv
    (L : StableLattice A ρK)
    (rangeEquiv : (G →₀ A) ≃ₗ[A] L.toSubmodule)
    (hmax_map :
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A))).map rangeEquiv.toLinearMap =
        L.maximalIdealSubmodule) :
    L.reduction ≃ₗ[k] (G →₀ k) :=
  residue_field_linear_equiv_of_linear_equiv (A := A) <|
    (Submodule.Quotient.equiv
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A)))
      L.maximalIdealSubmodule
      rangeEquiv
      hmax_map).symm.trans
      (finsupp_residue_quotient_equiv (A := A) (X := G))

/-- Helper for Exercise 15-15.2-4: the regular-branch transport sends the quotient class of an
image-lattice element back to the reduced source class it came from. -/
@[simp] private theorem regular_range_reduction_linear_equiv_apply_mk_range
    (L : StableLattice A ρK)
    (rangeEquiv : (G →₀ A) ≃ₗ[A] L.toSubmodule)
    (hmax_map :
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A))).map rangeEquiv.toLinearMap =
        L.maximalIdealSubmodule)
    (z : G →₀ A) :
    regular_range_reduction_linear_equiv L rangeEquiv hmax_map
        (Submodule.Quotient.mk (rangeEquiv z) : L.reduction) =
      finsupp_residue_quotient_equiv (A := A) (X := G) (Submodule.Quotient.mk z) := by
  change
    (finsupp_residue_quotient_equiv (A := A) (X := G))
        (((Submodule.Quotient.equiv
            (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A)))
            L.maximalIdealSubmodule
            rangeEquiv
            hmax_map).symm) (Submodule.Quotient.mk (rangeEquiv z))) =
      finsupp_residue_quotient_equiv (A := A) (X := G) (Submodule.Quotient.mk z)
  simp [finsupp_residue_quotient_equiv_apply_mk]

set_option maxHeartbeats 50000000 in
/-- Helper for Exercise 15-15.2-4: transport the reduction of a split-basis lattice coming from
`A²` to the reduced split coordinate module `k²`. -/
private noncomputable def split_range_reduction_linear_equiv
    (L : StableLattice A ρK)
    (rangeEquiv : (Fin 2 →₀ A) ≃ₗ[A] L.toSubmodule)
    (hmax_map :
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A))).map
          rangeEquiv.toLinearMap =
        L.maximalIdealSubmodule) :
    L.reduction ≃ₗ[k] (Fin 2 →₀ k) :=
  residue_field_linear_equiv_of_linear_equiv (A := A) <|
    (Submodule.Quotient.equiv
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A)))
      L.maximalIdealSubmodule
      rangeEquiv
      hmax_map).symm.trans
      (finsupp_residue_quotient_equiv (A := A) (X := Fin 2))

/-- Helper for Exercise 15-15.2-4: the split-branch transport sends the quotient class of an
image-lattice element back to the reduced source class it came from. -/
@[simp] private theorem split_range_reduction_linear_equiv_apply_mk_range
    (L : StableLattice A ρK)
    (rangeEquiv : (Fin 2 →₀ A) ≃ₗ[A] L.toSubmodule)
    (hmax_map :
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A))).map
          rangeEquiv.toLinearMap =
        L.maximalIdealSubmodule)
    (z : Fin 2 →₀ A) :
    split_range_reduction_linear_equiv L rangeEquiv hmax_map
        (Submodule.Quotient.mk (rangeEquiv z) : L.reduction) =
      finsupp_residue_quotient_equiv (A := A) (X := Fin 2) (Submodule.Quotient.mk z) := by
  change
    (finsupp_residue_quotient_equiv (A := A) (X := Fin 2))
        (((Submodule.Quotient.equiv
            (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A)))
            L.maximalIdealSubmodule
            rangeEquiv
            hmax_map).symm) (Submodule.Quotient.mk (rangeEquiv z))) =
      finsupp_residue_quotient_equiv (A := A) (X := Fin 2) (Submodule.Quotient.mk z)
  simp [finsupp_residue_quotient_equiv_apply_mk]

/-- Helper for Exercise 15-15.2-4: finitely supported functions on `Fin 2` are linearly
equivalent to pairs of scalars via their two coordinates. -/
private noncomputable def finTwoPairLinearEquiv :
    (Fin 2 →₀ k) ≃ₗ[k] k × k where
  toFun := fun f ↦ (f 0, f 1)
  invFun := fun p ↦ Finsupp.single 0 p.1 + Finsupp.single 1 p.2
  left_inv := by
    intro f
    ext i
    fin_cases i <;> simp
  right_inv := by
    intro p
    simp
  map_add' := by
    intro f g
    simp
  map_smul' := by
    intro a f
    simp

/-- Helper for Exercise 15-15.2-4: the nontrivial element of a group of order `2` is its own
inverse. -/
private theorem order_two_generator_inv
    {s : G} (hs2 : s * s = 1) :
    s⁻¹ = s := by
  -- Multiply the relation `s² = 1` on the left by `s⁻¹` to isolate `s⁻¹`.
  have h := congrArg (fun t => s⁻¹ * t) hs2
  simpa [mul_assoc] using h.symm

/-- Helper for Exercise 15-15.2-4: the diagonal vector in the regular representation attached to
the basis vectors at `1` and the nontrivial generator `s`. -/
private def regular_diagonal_vector (s : G) : G →₀ k :=
  Finsupp.single (1 : G) (1 : k) + Finsupp.single s (1 : k)

/-- Helper for Exercise 15-15.2-4: the nontrivial generator fixes the diagonal vector in the
residue-field regular representation. -/
private theorem leftRegular_generator_fixes_diagonal
    {s : G} (hs2 : s * s = 1) :
    ρk s (regular_diagonal_vector s) = regular_diagonal_vector s := by
  -- The order-two generator swaps the two basis vectors, so their sum is fixed.
  simp [regular_diagonal_vector, hs2, add_comm]

/-- Helper for Exercise 15-15.2-4: every fixed vector for the order-two generator in the regular
representation lies on the diagonal line. -/
private theorem leftRegular_fixed_mem_diagonal
    {s : G} (hsne : s ≠ 1) (hsall : ∀ g : G, g = 1 ∨ g = s) (hs2 : s * s = 1)
    {x : G →₀ k} (hx : ρk s x = x) :
    x ∈ Submodule.span k ({regular_diagonal_vector s} : Set (G →₀ k)) := by
  -- Evaluate the fixed-vector equation at `1` to show the `1`- and `s`-coordinates agree.
  have hsinv : s⁻¹ = s := order_two_generator_inv hs2
  have h1 : x 1 = x s := by
    have h := congrArg (fun f => f 1) hx
    simpa [Representation.ofMulAction_apply, hsinv] using h.symm
  -- Then reconstruct the whole finitely supported function from that common coefficient.
  refine Submodule.mem_span_singleton.2 ?_
  refine ⟨x 1, ?_⟩
  ext g
  rcases hsall g with rfl | rfl
  · simp [regular_diagonal_vector, h1, hsne]
  · simp [regular_diagonal_vector, h1, hsne]

/-- Helper for Exercise 15-15.2-4: the order-two generator acts involutively on the regular
representation over the residue field. -/
private theorem leftRegular_generator_involutive
    {s : G} (hs2 : s * s = 1) (x : G →₀ k) :
    ρk s (ρk s x) = x := by
  -- Apply the regular action formula twice and collapse `s⁻¹ * (s⁻¹ * g)` using `s² = 1`.
  ext g
  have harg : s⁻¹ * (s⁻¹ * g) = g := by
    calc
      s⁻¹ * (s⁻¹ * g) = s * (s * g) := by
        simpa [order_two_generator_inv hs2]
      _ = g := by
        rw [← mul_assoc, hs2, one_mul]
  simpa [Representation.ofMulAction_apply] using congrArg x harg

/-- Helper for Exercise 15-15.2-4: in residue characteristic `2`, the regular representation of a
group of order `2` is not semisimple because the diagonal line has no stable complement. -/
private theorem leftRegular_not_semisimple_order_two_char_two
    {s : G} (hsne : s ≠ 1) (hsall : ∀ g : G, g = 1 ∨ g = s) (hs2 : s * s = 1) :
    ¬ IsSemisimpleRepresentation ρk := by
  intro hsemi
  let U : Subrepresentation ρk :=
    { toSubmodule := Submodule.span k ({regular_diagonal_vector s} : Set (G →₀ k))
      apply_mem_toSubmodule := by
        intro g x hx
        -- The diagonal line is stable because every group element is either `1` or `s`.
        rcases Submodule.mem_span_singleton.1 hx with ⟨a, rfl⟩
        rcases hsall g with rfl | rfl
        · exact Submodule.mem_span_singleton.2 ⟨a, by simp [regular_diagonal_vector]⟩
        · exact Submodule.mem_span_singleton.2 ⟨a, by
            simp [leftRegular_generator_fixes_diagonal, hs2]⟩ }
  have hU_ne_bot : U ≠ ⊥ := by
    -- The diagonal vector is visibly nonzero because its `1`-coordinate is `1`.
    intro hUbot
    have hd : regular_diagonal_vector s = (0 : G →₀ k) := by
      have hdmem : regular_diagonal_vector s ∈ U.toSubmodule := by
        exact Submodule.subset_span (by simp)
      have hdmem' : regular_diagonal_vector s ∈ (⊥ : Subrepresentation ρk).toSubmodule := by
        simpa [hUbot] using hdmem
      simpa using hdmem'
    have h1 := congrArg (fun f => f 1) hd
    simpa [regular_diagonal_vector, hsne] using h1
  have hU_ne_top : U ≠ ⊤ := by
    -- The basis vector `δ₁` is not on the diagonal line, so that line is proper.
    intro hUtop
    have hmem : Finsupp.single (1 : G) (1 : k) ∈ U.toSubmodule := by
      simpa [hUtop] using
        (show Finsupp.single (1 : G) (1 : k) ∈ (⊤ : Submodule k (G →₀ k)) by
          simp)
    rcases Submodule.mem_span_singleton.1 hmem with ⟨a, ha⟩
    have hscoord : a = 0 := by
      have h := congrArg (fun f => f s) ha
      simpa [regular_diagonal_vector, hsne] using h
    have h1coord : a = 1 := by
      have h := congrArg (fun f => f 1) ha
      simpa [regular_diagonal_vector, hsne] using h
    exact zero_ne_one (hscoord.symm.trans h1coord)
  letI : ComplementedLattice (Subrepresentation ρk) := hsemi
  rcases ComplementedLattice.exists_isCompl U with ⟨V, hUV⟩
  have hV_ne_bot : V ≠ ⊥ := by
    -- A complement to a proper subrepresentation cannot be trivial.
    intro hVbot
    have : U = ⊤ := by
      simpa [hVbot] using hUV.sup_eq_top
    exact hU_ne_top this
  have hVsub_ne_bot : V.toSubmodule ≠ ⊥ := by
    intro hVsub
    exact hV_ne_bot (Subrepresentation.toSubmodule_injective hVsub)
  rcases (Submodule.ne_bot_iff _).1 hVsub_ne_bot with ⟨x, hxV, hx0⟩
  let y : G →₀ k := x + ρk s x
  have hyV : y ∈ V.toSubmodule := by
    -- The complement is stable, so it contains both `x` and its translate by `s`.
    exact V.toSubmodule.add_mem hxV (V.apply_mem_toSubmodule s hxV)
  have hyfix : ρk s y = y := by
    -- Symmetrizing a vector by `x + s • x` produces an `s`-fixed vector.
    dsimp [y]
    simp [leftRegular_generator_involutive, hs2, add_comm, add_left_comm, add_assoc]
  by_cases hy0 : y = 0
  · -- If the symmetrization vanishes, then `x` itself is fixed because `-x = x` in
    -- characteristic `2`, so `x` already lies on the diagonal line.
    have hxx : x + x = 0 := by
      calc
        x + x = (2 : k) • x := by simp [two_smul]
        _ = 0 := by
          have htwo : (2 : k) = 0 := by
            simpa using (CharP.cast_eq_zero (R := k) 2)
          simp [htwo]
    have hx_eq_neg : x = -x := add_eq_zero_iff_eq_neg.mp hxx
    have hsx_eq_negx : ρk s x = -x := by
      exact eq_neg_of_add_eq_zero_right (by simpa [y] using hy0)
    have hfixx : ρk s x = x := by
      calc
        ρk s x = -x := hsx_eq_negx
        _ = x := hx_eq_neg.symm
    have hxU : x ∈ U.toSubmodule := leftRegular_fixed_mem_diagonal hsne hsall hs2 hfixx
    have hxbot : x ∈ (⊥ : Subrepresentation ρk).toSubmodule := by
      simpa [hUV.inf_eq_bot] using
        (show x ∈ (U ⊓ V : Subrepresentation ρk).toSubmodule from ⟨hxU, hxV⟩)
    exact hx0 (by simpa using hxbot)
  · -- Otherwise the nonzero symmetrization is a fixed vector in the complement, hence also on the
    -- diagonal line, contradicting that the complement intersects `U` trivially.
    have hyU : y ∈ U.toSubmodule := leftRegular_fixed_mem_diagonal hsne hsall hs2 hyfix
    have hybot : y ∈ (⊥ : Subrepresentation ρk).toSubmodule := by
      simpa [hUV.inf_eq_bot] using
        (show y ∈ (U ⊓ V : Subrepresentation ρk).toSubmodule from ⟨hyU, hyV⟩)
    exact hy0 (by simpa using hybot)

/-- Helper for Exercise 15-15.2-4: extending coefficients from `A` to `K` on finitely supported
functions is injective. -/
private theorem regular_coeff_embedding_injective :
    Function.Injective
      (Finsupp.mapRange (algebraMap A K) (by simp) : (G →₀ A) → G →₀ K) := by
  -- Compare coordinates after applying the coefficient embedding and use injectivity of `A → K`.
  intro x y hxy
  ext g
  exact (IsFractionRing.injective A K) (congrArg (fun f : G →₀ K ↦ f g) hxy)

/-- Helper for Exercise 15-15.2-4: coefficient extension commutes with the left regular action. -/
private theorem regular_coeff_embedding_comm (g : G) (x : G →₀ A) :
    Finsupp.mapRange (algebraMap A K) (by simp) (ρA g x) =
      ρK g (Finsupp.mapRange (algebraMap A K) (by simp) x) := by
  -- Both sides are obtained by translating the support and then applying the same coefficient map.
  ext h
  simp [Representation.ofMulAction_apply]

/-- Helper for Exercise 15-15.2-4: the coefficient image of `A[G]` in `K[G]` is a stable lattice,
equipped with the source-to-range equivalence needed to transport reduction. -/
private theorem regular_coefficient_stable_lattice
    (hG : Nat.card G = 2) :
    ∃ (L : StableLattice A ρK) (rangeEquiv : (G →₀ A) ≃ₗ[A] L.toSubmodule),
      (∀ z : G →₀ A, ((rangeEquiv z : L.toSubmodule) : G →₀ K) =
        Finsupp.mapRange (algebraMap A K) (by simp) z) ∧
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A))).map rangeEquiv.toLinearMap =
        L.maximalIdealSubmodule := by
  have hcard_ne_zero : Nat.card G ≠ 0 := by
    simp [hG]
  letI : Finite G := ((Nat.card_ne_zero (α := G)).1 hcard_ne_zero).2
  let coeffMap : (G →₀ A) →ₗ[A] (G →₀ K) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A K)
  have hcoeff_inj : Function.Injective coeffMap := by
    intro x y hxy
    apply regular_coeff_embedding_injective (A := A) (K := K) (G := G)
    exact hxy
  let L : StableLattice A ρK :=
    { toSubmodule := coeffMap.range
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨y, rfl⟩
        -- Translate a coefficient vector upstairs by translating its source coefficients first.
        refine ⟨ρA g y, ?_⟩
        simpa [coeffMap] using regular_coeff_embedding_comm (A := A) (K := K) (G := G) g y
      isLattice := by
        refine
          { fg := ?_
            span_eq_top := ?_ }
        · -- The coefficient lattice is the image of the finitely generated free `A`-module `A[G]`.
          have hfg_top : (⊤ : Submodule A (G →₀ A)).FG := by
            letI : Module.Finite A (G →₀ A) := Module.Finite.finsupp
            exact (Module.Finite.iff_fg (N := (⊤ : Submodule A (G →₀ A)))).1 inferInstance
          rw [LinearMap.range_eq_map]
          exact Submodule.FG.map coeffMap hfg_top
        · -- Over `K`, the image still contains every basis vector `δ_g`, hence spans all of `K[G]`.
          apply eq_top_iff.2
          intro x hx
          rw [← x.sum_single]
          refine Submodule.sum_mem _ ?_
          intro g hg
          have hsingle_mem :
              Finsupp.single g (1 : K) ∈
                Submodule.span K ((coeffMap.range : Submodule A (G →₀ K)) : Set (G →₀ K)) := by
            apply Submodule.subset_span
            refine ⟨Finsupp.single g (1 : A), ?_⟩
            ext h
            by_cases hh : h = g
            · subst hh
              simp [coeffMap]
            · simp [coeffMap, hh]
          have hterm_mem :
              x g • Finsupp.single g (1 : K) ∈
                Submodule.span K ((coeffMap.range : Submodule A (G →₀ K)) : Set (G →₀ K)) :=
            Submodule.smul_mem _ (x g) hsingle_mem
          simpa [Finsupp.smul_single_one] using hterm_mem }
  let rangeEquiv : (G →₀ A) ≃ₗ[A] L.toSubmodule :=
    LinearEquiv.ofBijective coeffMap.rangeRestrict
      ⟨(LinearMap.injective_rangeRestrict_iff (f := coeffMap)).2 hcoeff_inj,
        LinearMap.surjective_rangeRestrict coeffMap⟩
  have hmax_map :
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A))).map rangeEquiv.toLinearMap =
        L.maximalIdealSubmodule := by
    -- Transport the maximal-ideal multiple through the source-to-range equivalence.
    rw [StableLattice.maximalIdealSubmodule, Submodule.map_smul'']
    have htop :
        (⊤ : Submodule A (G →₀ A)).map rangeEquiv.toLinearMap = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.2 rangeEquiv.surjective
    simp [htop]
  refine ⟨L, rangeEquiv, ?_⟩
  constructor
  · intro z
    rfl
  · exact hmax_map

/-- Helper for Exercise 15-15.2-4: on source representatives in the coefficient lattice, the
transported reduction action is the regular action over the residue field. -/
private theorem regular_reduction_commutes_on_source
    {L : StableLattice A ρK}
    (rangeEquiv : (G →₀ A) ≃ₗ[A] L.toSubmodule)
    (happly : ∀ z : G →₀ A, ((rangeEquiv z : L.toSubmodule) : G →₀ K) =
      Finsupp.mapRange (algebraMap A K) (by simp) z)
    (hmax_map :
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A))).map rangeEquiv.toLinearMap =
        L.maximalIdealSubmodule)
    (g : G) (z : G →₀ A) :
    let rangeReductionEquiv :=
      Submodule.Quotient.equiv
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A)))
        L.maximalIdealSubmodule
        rangeEquiv
        hmax_map
    let ek :=
      regular_range_reduction_linear_equiv L rangeEquiv hmax_map
    ek (L.reductionRepresentation g (rangeReductionEquiv (Submodule.Quotient.mk z))) =
      ρk g (ek (rangeReductionEquiv (Submodule.Quotient.mk z))) := by
  let rangeReductionEquiv :
      ((G →₀ A) ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A)))) ≃ₗ[A]
        L.reduction :=
    Submodule.Quotient.equiv
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A)))
      L.maximalIdealSubmodule
      rangeEquiv
      hmax_map
  let ek :=
    regular_range_reduction_linear_equiv L rangeEquiv hmax_map
  change
    ek (L.reductionRepresentation g (rangeReductionEquiv (Submodule.Quotient.mk z : _))) =
      ρk g (ek (rangeReductionEquiv (Submodule.Quotient.mk z : _)))
  have hrange_comm :
      rangeEquiv (ρA g z) = L.toRepresentation g (rangeEquiv z) := by
    -- The source regular action and the lattice action agree after coefficient embedding.
    ext h
    rw [happly, StableLattice.toRepresentation_apply_coe, happly]
    exact congrArg (fun x : G →₀ K ↦ x h)
      (regular_coeff_embedding_comm (A := A) (K := K) (G := G) g z)
  have hreduce_comm :
      L.reductionRepresentation g
          (rangeReductionEquiv (Submodule.Quotient.mk z : _)) =
        rangeReductionEquiv (Submodule.Quotient.mk (ρA g z) : _) := by
    -- Push the reduced action back to the source quotient through the source-to-range equivalence.
    change
      L.reductionRepresentation g (Submodule.Quotient.mk (rangeEquiv z)) =
        Submodule.Quotient.mk (rangeEquiv (ρA g z))
    rw [StableLattice.reductionRepresentation_apply_mk]
    congr 1
    exact hrange_comm.symm
  -- After rewriting on the source quotient, coefficientwise reduction commutes with translation.
  rw [hreduce_comm]
  change
    ek (Submodule.Quotient.mk (rangeEquiv ((ρA g) z))) =
      ρk g (ek (Submodule.Quotient.mk (rangeEquiv z)))
  have hcoeff_comm :
      finsupp_residue_quotient_equiv (A := A) (X := G) (Submodule.Quotient.mk (ρA g z)) =
        ρk g (finsupp_residue_quotient_equiv (A := A) (X := G) (Submodule.Quotient.mk z)) := by
    rw [finsupp_residue_quotient_equiv_apply_mk, finsupp_residue_quotient_equiv_apply_mk]
    ext h
    calc
      (Finsupp.mapRange
          (fun a : A ↦ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : k))
          (by rfl) ((ρA g) z)) h =
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (z (g⁻¹ * h)) : k) := by
            simp [Representation.ofMulAction_apply]
      _ =
          ((ρk g)
            (Finsupp.mapRange
              (fun a : A ↦ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : k))
              (by rfl) z)) h := by
            rw [Representation.ofMulAction_apply]
            rfl
  rw [regular_range_reduction_linear_equiv_apply_mk_range,
    regular_range_reduction_linear_equiv_apply_mk_range]
  exact hcoeff_comm

/-- Helper for Exercise 15-15.2-4: the coefficientwise lattice `A[G]` inside `K[G]` reduces to
the regular representation over the residue field. -/
private theorem regular_lattice_reduction_equiv_leftRegular
    (hG : Nat.card G = 2) :
    ∃ L : StableLattice A ρK, ∃ e : L.reductionRepresentation.Equiv ρk, True := by
  rcases regular_coefficient_stable_lattice (A := A) (K := K) (G := G) hG with
    ⟨L, rangeEquiv, happly, hmax_map⟩
  let rangeReductionEquiv :
      ((G →₀ A) ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A)))) ≃ₗ[A]
        L.reduction :=
    Submodule.Quotient.equiv
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A)))
      L.maximalIdealSubmodule
      rangeEquiv
      hmax_map
  let ek :
      L.reduction ≃ₗ[k] (G →₀ k) :=
    regular_range_reduction_linear_equiv L rangeEquiv hmax_map
  let e : L.reductionRepresentation.Equiv ρk :=
    Representation.Equiv.mk
      ek
      (fun g ↦ by
        apply LinearMap.ext
        intro x
        rcases rangeReductionEquiv.surjective x with ⟨q, rfl⟩
        rcases Submodule.Quotient.mk_surjective
            (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (G →₀ A))) q with ⟨z, rfl⟩
        -- Reduce to an explicit source representative and reuse the source-level intertwining lemma.
        simpa [rangeReductionEquiv, ek] using
          regular_reduction_commutes_on_source (L := L) rangeEquiv happly hmax_map g z)
  refine ⟨L, e, True.intro⟩

/-- Helper for Exercise 15-15.2-4: the `+1`-eigenvector for the order-two generator in the split
basis of `K[G]`. -/
private def split_plus_vector (s : G) : G →₀ K :=
  Finsupp.single (1 : G) (1 : K) + Finsupp.single s (1 : K)

/-- Helper for Exercise 15-15.2-4: the `-1`-eigenvector for the order-two generator in the split
basis of `K[G]`. -/
private def split_minus_vector (s : G) : G →₀ K :=
  Finsupp.single (1 : G) (1 : K) - Finsupp.single s (1 : K)

/-- Helper for Exercise 15-15.2-4: the split basis map from `K²` to `K[G]` sending the two
standard basis vectors to `u = δ₁ + δ_s` and `w = δ₁ - δ_s`. -/
private noncomputable def split_basis_map_K (s : G) :
    (Fin 2 →₀ K) →ₗ[K] (G →₀ K) :=
  (Finsupp.lapply (R := K) (M := K) 0).smulRight (split_plus_vector (K := K) s) +
    (Finsupp.lapply (R := K) (M := K) 1).smulRight (split_minus_vector (K := K) s)

/-- Helper for Exercise 15-15.2-4: the coefficientwise embedding of the split `A`-lattice into
the split `K`-basis of `K[G]`. -/
private noncomputable def split_basis_map_A (s : G) :
    (Fin 2 →₀ A) →ₗ[A] (G →₀ K) :=
  ((split_basis_map_K (K := K) s).restrictScalars A).comp
    (Finsupp.mapRange.linearMap (Algebra.linearMap A K))

/-- Helper for Exercise 15-15.2-4: the inverse split-coordinate map recovered from the `1`- and
`s`-coordinates by dividing by `2`. -/
private def split_basis_inv (s : G) (x : G →₀ K) : Fin 2 →₀ K :=
  Finsupp.single 0 ((x 1 + x s) / 2) + Finsupp.single 1 ((x 1 - x s) / 2)

/-- Helper for Exercise 15-15.2-4: the source-side sign change in the split basis. -/
private noncomputable def split_generator_source (R : Type*) [CommRing R] :
    (Fin 2 →₀ R) →ₗ[R] (Fin 2 →₀ R) :=
  (Finsupp.lapply (R := R) (M := R) 0).smulRight (Finsupp.single 0 (1 : R)) +
    (Finsupp.lapply (R := R) (M := R) 1).smulRight (Finsupp.single 1 (- (1 : R)))

/-- Helper for Exercise 15-15.2-4: on coordinates, the split sign-change keeps the first basis
vector and negates the second coordinate. -/
@[simp] private theorem split_generator_source_apply
    {R : Type*} [CommRing R] (z : Fin 2 →₀ R) :
    (split_generator_source R) z = Finsupp.single 0 (z 0) + Finsupp.single 1 (- z 1) := by
  ext i
  fin_cases i <;> simp [split_generator_source]

/-- Helper for Exercise 15-15.2-4: the order-two generator fixes `u = δ₁ + δ_s` and sends
`w = δ₁ - δ_s` to `-w`. -/
private theorem leftRegular_generator_split_basis_action
    {s : G} (hsne : s ≠ 1) (hsall : ∀ g : G, g = 1 ∨ g = s) (hs2 : s * s = 1) :
    ρK s (split_plus_vector (K := K) s) = split_plus_vector (K := K) s ∧
      ρK s (split_minus_vector (K := K) s) = - split_minus_vector (K := K) s := by
  have hsinv : s⁻¹ = s := order_two_generator_inv hs2
  constructor
  · -- The generator swaps the two basis vectors, so their sum is fixed.
    ext g
    rcases hsall g with rfl | rfl
    · simp [split_plus_vector, Representation.ofMulAction_apply, hsinv, hs2, hsne]
    · simp [split_plus_vector, Representation.ofMulAction_apply, hsinv, hs2, hsne]
  · -- The same swap changes the sign of the alternating vector.
    ext g
    rcases hsall g with rfl | rfl
    · simp [split_minus_vector, Representation.ofMulAction_apply, hsinv, hs2, hsne]
    · simp [split_minus_vector, Representation.ofMulAction_apply, hsinv, hs2, hsne]

/-- Helper for Exercise 15-15.2-4: the split basis really is a `K`-basis of `K[G]` when `|G|=2`
and `2` is nonzero in `K`. -/
private noncomputable def split_basis_linear_equiv_order_two
    [NeZero (2 : K)] {s : G} (hsne : s ≠ 1) (hsall : ∀ g : G, g = 1 ∨ g = s) :
    (Fin 2 →₀ K) ≃ₗ[K] (G →₀ K) :=
  LinearEquiv.ofBijective (split_basis_map_K (K := K) s) <| by
    have hleft :
        Function.LeftInverse (split_basis_inv (K := K) s) (split_basis_map_K (K := K) s) := by
      intro z
      ext i
      fin_cases i
      · simp [split_basis_inv, split_basis_map_K, split_plus_vector, split_minus_vector, hsne,
          sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      · simp [split_basis_inv, split_basis_map_K, split_plus_vector, split_minus_vector, hsne,
          sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hright :
        Function.RightInverse (split_basis_inv (K := K) s) (split_basis_map_K (K := K) s) := by
      intro x
      ext g
      rcases hsall g with rfl | rfl
      · simp [split_basis_inv, split_basis_map_K, split_plus_vector, split_minus_vector, hsne,
          sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        field_simp
        ring
      · simp [split_basis_inv, split_basis_map_K, split_plus_vector, split_minus_vector, hsne,
          sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        field_simp
        ring
    constructor
    · exact hleft.injective
    · exact hright.surjective

@[simp] private theorem split_basis_linear_equiv_order_two_apply
    [NeZero (2 : K)] {s : G} (hsne : s ≠ 1) (hsall : ∀ g : G, g = 1 ∨ g = s)
    (z : Fin 2 →₀ K) :
    split_basis_linear_equiv_order_two (K := K) hsne hsall z = split_basis_map_K (K := K) s z := rfl

/-- Helper for Exercise 15-15.2-4: the split-basis embedding intertwines the generator with the
diagonal sign change on the source coordinates. -/
private theorem split_basis_map_A_generator_comm
    {s : G} (hsne : s ≠ 1) (hsall : ∀ g : G, g = 1 ∨ g = s) (hs2 : s * s = 1)
    (z : Fin 2 →₀ A) :
    ρK s (split_basis_map_A (A := A) (K := K) s z) =
      split_basis_map_A (A := A) (K := K) s ((split_generator_source A) z) := by
  rcases leftRegular_generator_split_basis_action (K := K) hsne hsall hs2 with ⟨hu, hw⟩
  -- Rewrite the image in the split basis and apply the eigenvector identities termwise.
  simp [split_basis_map_A, split_basis_map_K, split_generator_source, hu, hw]

/-- Helper for Exercise 15-15.2-4: in residue characteristic `2`, every residue scalar equals its
negative. -/
private theorem neg_eq_self_residue (a : k) : -a = a := by
  have htwo : (2 : k) = 0 := by
    simpa using (CharP.cast_eq_zero (R := k) 2)
  have htwo' : (1 : k) + 1 = 0 := by
    simpa [one_add_one_eq_two] using htwo
  have hnegone : (- (1 : k)) = 1 := by
    have h : (1 : k) = - (1 : k) := eq_neg_iff_add_eq_zero.mpr htwo'
    simpa using h.symm
  calc
    -a = (- (1 : k)) * a := by simp
    _ = 1 * a := by rw [hnegone]
    _ = a := by simp

/-- Helper for Exercise 15-15.2-4: after coefficient reduction, the split sign change becomes the
identity because `-1 = 1` in characteristic `2`. -/
private theorem split_generator_source_reduction_eq (z : Fin 2 →₀ A) :
    finsupp_residue_quotient_equiv (A := A) (X := Fin 2)
        (Submodule.Quotient.mk ((split_generator_source A) z)) =
      finsupp_residue_quotient_equiv (A := A) (X := Fin 2)
        (Submodule.Quotient.mk z) := by
  -- After reduction, the second sign disappears because residue characteristic is `2`.
  rw [finsupp_residue_quotient_equiv_apply_mk, finsupp_residue_quotient_equiv_apply_mk,
    split_generator_source_apply]
  ext i
  fin_cases i
  · simp
  · simpa using
      (neg_eq_self_residue (A := A)
        (a := (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (z 1) : k)))

/-- Helper for Exercise 15-15.2-4: the split-basis image of `A²` in `K[G]` is a stable lattice,
equipped with the source-to-range equivalence needed to transport reduction. -/
private theorem split_basis_stable_lattice
    [NeZero (2 : K)] {s : G} (hsne : s ≠ 1) (hsall : ∀ g : G, g = 1 ∨ g = s) (hs2 : s * s = 1) :
    ∃ (L : StableLattice A ρK) (rangeEquiv : (Fin 2 →₀ A) ≃ₗ[A] L.toSubmodule),
      (∀ z : Fin 2 →₀ A, ((rangeEquiv z : L.toSubmodule) : G →₀ K) =
        split_basis_map_A (A := A) (K := K) s z) ∧
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A))).map
          rangeEquiv.toLinearMap =
        L.maximalIdealSubmodule := by
  let coeffMap : (Fin 2 →₀ A) →ₗ[A] (Fin 2 →₀ K) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A K)
  let splitMap : (Fin 2 →₀ A) →ₗ[A] (G →₀ K) := split_basis_map_A (A := A) (K := K) s
  have hcoeff_inj : Function.Injective coeffMap := by
    simpa [coeffMap] using
      (Finsupp.mapRange_injective (algebraMap A K) (by simp) (IsFractionRing.injective A K))
  have hsplit_inj : Function.Injective splitMap := by
    intro z z' hzz'
    apply hcoeff_inj
    exact (split_basis_linear_equiv_order_two (K := K) hsne hsall).injective (by
      simpa [splitMap, split_basis_map_A, coeffMap] using hzz')
  let L : StableLattice A ρK :=
    { toSubmodule := splitMap.range
      apply_mem_toSubmodule := by
        intro g x hx
        rcases hx with ⟨z, rfl⟩
        -- Every group element is `1` or `s`, so the range is closed under the action.
        rcases hsall g with rfl | rfl
        · exact ⟨z, by simp [splitMap, split_basis_map_A]⟩
        · refine ⟨(split_generator_source A) z, ?_⟩
          simpa [splitMap] using
            (split_basis_map_A_generator_comm (A := A) (K := K) hsne hsall hs2 z).symm
      isLattice := by
        refine
          { fg := ?_
            span_eq_top := ?_ }
        · -- The split lattice is the image of the finite free `A`-module `A²`.
          have hfg_top : (⊤ : Submodule A (Fin 2 →₀ A)).FG := by
            letI : Module.Finite A (Fin 2 →₀ A) := Module.Finite.finsupp
            exact (Module.Finite.iff_fg (N := (⊤ : Submodule A (Fin 2 →₀ A)))).1 inferInstance
          rw [LinearMap.range_eq_map]
          exact Submodule.FG.map splitMap hfg_top
        · -- The images of the two split basis vectors span `K[G]`.
          apply eq_top_iff.2
          intro x hx
          rcases (split_basis_linear_equiv_order_two (K := K) hsne hsall).surjective x with
            ⟨z, rfl⟩
          have hu :
              split_plus_vector (K := K) s ∈
                Submodule.span K ((splitMap.range : Submodule A (G →₀ K)) : Set (G →₀ K)) := by
            apply Submodule.subset_span
            refine ⟨Finsupp.single 0 (1 : A), ?_⟩
            simp [splitMap, split_basis_map_A, split_basis_map_K, split_plus_vector]
          have hw :
              split_minus_vector (K := K) s ∈
                Submodule.span K ((splitMap.range : Submodule A (G →₀ K)) : Set (G →₀ K)) := by
            apply Submodule.subset_span
            refine ⟨Finsupp.single 1 (1 : A), ?_⟩
            simp [splitMap, split_basis_map_A, split_basis_map_K, split_minus_vector]
          have hz0 :
              z 0 • split_plus_vector (K := K) s ∈
                Submodule.span K ((splitMap.range : Submodule A (G →₀ K)) : Set (G →₀ K)) :=
            Submodule.smul_mem _ (z 0) hu
          have hz1 :
              z 1 • split_minus_vector (K := K) s ∈
                Submodule.span K ((splitMap.range : Submodule A (G →₀ K)) : Set (G →₀ K)) :=
            Submodule.smul_mem _ (z 1) hw
          simpa [split_basis_linear_equiv_order_two, split_basis_map_K] using
            Submodule.add_mem _ hz0 hz1 }
  let rangeEquiv : (Fin 2 →₀ A) ≃ₗ[A] L.toSubmodule :=
    LinearEquiv.ofBijective splitMap.rangeRestrict
      ⟨(LinearMap.injective_rangeRestrict_iff (f := splitMap)).2 hsplit_inj,
        LinearMap.surjective_rangeRestrict splitMap⟩
  have hmax_map :
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A))).map
          rangeEquiv.toLinearMap =
        L.maximalIdealSubmodule := by
    -- Transport the maximal-ideal multiple through the source-to-range equivalence.
    rw [StableLattice.maximalIdealSubmodule, Submodule.map_smul'']
    have htop :
        (⊤ : Submodule A (Fin 2 →₀ A)).map rangeEquiv.toLinearMap = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.2 rangeEquiv.surjective
    simp [htop]
  refine ⟨L, rangeEquiv, ?_⟩
  constructor
  · intro z
    rfl
  · exact hmax_map

/-- Helper for Exercise 15-15.2-4: on source representatives in the split lattice, the
transported reduction action is trivial over the residue field. -/
private theorem split_reduction_commutes_on_source
    {L : StableLattice A ρK} {s : G}
    (hsne : s ≠ 1) (hsall : ∀ g : G, g = 1 ∨ g = s) (hs2 : s * s = 1)
    (rangeEquiv : (Fin 2 →₀ A) ≃ₗ[A] L.toSubmodule)
    (happly : ∀ z : Fin 2 →₀ A, ((rangeEquiv z : L.toSubmodule) : G →₀ K) =
      split_basis_map_A (A := A) (K := K) s z)
    (hmax_map :
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A))).map
          rangeEquiv.toLinearMap =
        L.maximalIdealSubmodule)
    (g : G) (z : Fin 2 →₀ A) :
    let rangeReductionEquiv :=
      Submodule.Quotient.equiv
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A)))
        L.maximalIdealSubmodule
        rangeEquiv
        hmax_map
    let ek :=
      split_range_reduction_linear_equiv L rangeEquiv hmax_map
    ek (L.reductionRepresentation g (rangeReductionEquiv (Submodule.Quotient.mk z))) =
      (Representation.trivial k G (Fin 2 →₀ k) g)
        (ek (rangeReductionEquiv (Submodule.Quotient.mk z))) := by
  let rangeReductionEquiv :
      ((Fin 2 →₀ A) ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A)))) ≃ₗ[A]
        L.reduction :=
    Submodule.Quotient.equiv
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A)))
      L.maximalIdealSubmodule
      rangeEquiv
      hmax_map
  let ek :=
    split_range_reduction_linear_equiv L rangeEquiv hmax_map
  change
    ek (L.reductionRepresentation g (rangeReductionEquiv (Submodule.Quotient.mk z : _))) =
      (Representation.trivial k G (Fin 2 →₀ k) g)
        (ek (rangeReductionEquiv (Submodule.Quotient.mk z : _)))
  rcases hsall g with hg | hg
  · subst g
    have hrange_comm :
        rangeEquiv z = L.toRepresentation 1 (rangeEquiv z) := by
      -- The identity element acts trivially on the split lattice.
      ext h
      rw [happly, StableLattice.toRepresentation_apply_coe, happly]
      simp [split_basis_map_A, Representation.ofMulAction_apply]
    have hreduce_comm :
        L.reductionRepresentation 1
            (rangeReductionEquiv (Submodule.Quotient.mk z : _)) =
          rangeReductionEquiv (Submodule.Quotient.mk z : _) := by
      -- Push the identity action back to the source quotient and use that it is literally `id`.
      change
        L.reductionRepresentation 1 (Submodule.Quotient.mk (rangeEquiv z)) =
          Submodule.Quotient.mk (rangeEquiv z)
      rw [StableLattice.reductionRepresentation_apply_mk]
      congr 1
      exact hrange_comm.symm
    -- After rewriting on the source quotient, both sides are the same reduced coefficient vector.
    rw [hreduce_comm]
    change
      ek (Submodule.Quotient.mk (rangeEquiv z)) =
        (Representation.trivial k G (Fin 2 →₀ k) 1) (ek (Submodule.Quotient.mk (rangeEquiv z)))
    have hcoeff_id :
        finsupp_residue_quotient_equiv (A := A) (X := Fin 2) (Submodule.Quotient.mk z) =
          (Representation.trivial k G (Fin 2 →₀ k) 1)
            (finsupp_residue_quotient_equiv (A := A) (X := Fin 2) (Submodule.Quotient.mk z)) := by
      simp [Representation.trivial]
    simpa using hcoeff_id
  · subst g
    have hrange_comm :
        rangeEquiv ((split_generator_source A) z) = L.toRepresentation s (rangeEquiv z) := by
      -- The chosen split basis diagonalizes the generator on the source coordinates.
      ext h
      rw [happly, StableLattice.toRepresentation_apply_coe, happly]
      have hcomm :=
        congrArg (fun x : G →₀ K ↦ x h)
          (split_basis_map_A_generator_comm (A := A) (K := K) (s := s) hsne hsall hs2 z)
      simpa [Representation.ofMulAction_apply] using hcomm.symm
    have hreduce_comm :
        L.reductionRepresentation s
            (rangeReductionEquiv (Submodule.Quotient.mk z : _)) =
          rangeReductionEquiv (Submodule.Quotient.mk ((split_generator_source A) z) : _) := by
      -- Push the generator action back to the source quotient, where it is the diagonal sign map.
      change
        L.reductionRepresentation s (Submodule.Quotient.mk (rangeEquiv z)) =
          Submodule.Quotient.mk (rangeEquiv ((split_generator_source A) z))
      rw [StableLattice.reductionRepresentation_apply_mk]
      congr 1
      exact hrange_comm.symm
    -- Reduce the source sign change; in characteristic `2` it becomes the identity.
    rw [hreduce_comm]
    change
      ek (Submodule.Quotient.mk (rangeEquiv ((split_generator_source A) z))) =
        (Representation.trivial k G (Fin 2 →₀ k) s) (ek (Submodule.Quotient.mk (rangeEquiv z)))
    have hcoeff_trivial :
        finsupp_residue_quotient_equiv (A := A) (X := Fin 2)
            (Submodule.Quotient.mk ((split_generator_source A) z)) =
          (Representation.trivial k G (Fin 2 →₀ k) s)
            (finsupp_residue_quotient_equiv (A := A) (X := Fin 2) (Submodule.Quotient.mk z)) := by
      rw [split_generator_source_reduction_eq]
      simp [Representation.trivial]
    rw [split_range_reduction_linear_equiv_apply_mk_range,
      split_range_reduction_linear_equiv_apply_mk_range]
    exact hcoeff_trivial

/-- Helper for Exercise 15-15.2-4: the split-basis lattice in `K[G]` reduces to the trivial
two-dimensional residue representation. -/
private theorem split_lattice_reduction_equiv_trivial_finsupp
    [NeZero (2 : K)] (hG : Nat.card G = 2) :
    ∃ L : StableLattice A ρK,
      ∃ e : L.reductionRepresentation.Equiv (Representation.trivial k G (Fin 2 →₀ k)), True := by
  rcases order_two_generator_spec hG with ⟨s, hsne, hsall, hs2⟩
  rcases split_basis_stable_lattice (A := A) (K := K) (G := G) hsne hsall hs2 with
    ⟨L, rangeEquiv, happly, hmax_map⟩
  let rangeReductionEquiv :
      ((Fin 2 →₀ A) ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A)))) ≃ₗ[A]
        L.reduction :=
    Submodule.Quotient.equiv
      (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A)))
      L.maximalIdealSubmodule
      rangeEquiv
      hmax_map
  let ek :
      L.reduction ≃ₗ[k] (Fin 2 →₀ k) :=
    split_range_reduction_linear_equiv L rangeEquiv hmax_map
  let e : L.reductionRepresentation.Equiv (Representation.trivial k G (Fin 2 →₀ k)) :=
    Representation.Equiv.mk
      ek
      (fun g ↦ by
        apply LinearMap.ext
        intro x
        rcases rangeReductionEquiv.surjective x with ⟨q, rfl⟩
        rcases Submodule.Quotient.mk_surjective
            (IsLocalRing.maximalIdeal A • (⊤ : Submodule A (Fin 2 →₀ A))) q with ⟨z, rfl⟩
        -- Reduce to an explicit source representative and reuse the source-level intertwining lemma.
        simpa [rangeReductionEquiv, ek] using
          split_reduction_commutes_on_source (L := L) hsne hsall hs2 rangeEquiv happly hmax_map g z)
  refine ⟨L, e, True.intro⟩

-- Proof sketch: when `Nat.card G = 2` and `2 ≠ 0` in `K`, the regular representation over `K`
-- splits into two one-dimensional eigenspaces. A stable lattice adapted to this decomposition
-- reduces in residue characteristic `2` to the product of two trivial representations.
/-- Exercise 15-15.2-4 (1): when the residue characteristic is `2`, `2 ≠ 0` in `K`, and `G` has
order `2`, the regular `K[G]`-module admits a stable lattice whose reduction representation is
equivalent to the canonical product of two trivial residue-field representations. -/
theorem leftRegular_order_two_has_semisimple_stable_reduction
    [NeZero (2 : K)]
    (hG : Nat.card G = 2) :
    ∃ L : StableLattice A ρK,
      ∃ e : L.reductionRepresentation.Equiv τk,
        IsSemisimpleRepresentation L.reductionRepresentation := by
  -- Route correction: the stabilized proof route is to use the split basis
  -- `u = δ₁ + δs`, `w = δ₁ - δs`, build the image lattice of `A²`, identify the reduction with
  -- `k²`, and show the reduced action is trivial because `-1 = 1` in characteristic `2`.
  rcases split_lattice_reduction_equiv_trivial_finsupp (A := A) (K := K) (G := G) hG with
    ⟨L, e₀, -⟩
  let eτ : (Representation.trivial k G (Fin 2 →₀ k)).Equiv τk :=
    Representation.Equiv.mk finTwoPairLinearEquiv <| by
      intro g
      ext x <;> simp [Representation.trivial, Representation.prod, finTwoPairLinearEquiv]
  let e : L.reductionRepresentation.Equiv τk :=
    e₀.trans eτ
  have hsemi_triv : IsSemisimpleRepresentation (Representation.trivial k G (Fin 2 →₀ k)) := by
    exact trivial_isSemisimpleRepresentation (G := G)
  have hsemi_tau : IsSemisimpleRepresentation τk := by
    exact isSemisimpleRepresentation_of_equiv (G := G) eτ hsemi_triv
  have hsemi_L : IsSemisimpleRepresentation L.reductionRepresentation := by
    exact isSemisimpleRepresentation_of_equiv (G := G) e.symm hsemi_tau
  exact ⟨L, e, hsemi_L⟩

-- Proof sketch: the obvious lattice `A[G]` inside the left regular `K[G]`-module is stable, and
-- after reduction modulo the maximal ideal its representation is the regular representation of `G`
-- over `k`; in residue characteristic `2` and for `|G| = 2`, this regular representation is not
-- semisimple.
/-- Exercise 15-15.2-4 (2): when the residue characteristic is `2` and `G` has order `2`, the
regular `K[G]`-module also admits a stable lattice whose reduction representation is not
semisimple and equivalent to the regular representation `k[G]`. -/
theorem leftRegular_order_two_has_nonsemisimple_regular_stable_reduction
    (hG : Nat.card G = 2) :
    ∃ L : StableLattice A ρK,
      ∃ e : L.reductionRepresentation.Equiv ρk,
        ¬ IsSemisimpleRepresentation L.reductionRepresentation := by
  -- Route correction: use the coefficientwise lattice `A[G]`, identify its reduction with
  -- `k[G]`, and then transport the explicit characteristic-`2` obstruction from `ρk`.
  rcases order_two_generator_spec hG with ⟨s, hsne, hsall, hs2⟩
  rcases regular_lattice_reduction_equiv_leftRegular (A := A) (K := K) (G := G) hG with
    ⟨L, e, -⟩
  refine ⟨L, e, ?_⟩
  intro hsemi
  have hsemi_regular : IsSemisimpleRepresentation ρk :=
    isSemisimpleRepresentation_of_equiv (G := G) e hsemi
  exact leftRegular_not_semisimple_order_two_char_two hsne hsall hs2 hsemi_regular

end OrderTwoResidueCharacteristicTwo

end Representation

end
