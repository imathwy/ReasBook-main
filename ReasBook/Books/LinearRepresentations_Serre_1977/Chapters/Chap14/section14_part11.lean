import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_14_14_5_2 (from Chap14) -/
open scoped BigOperators MonoidAlgebra
open Module Submodule

universe u v w

namespace Representation

section NormComparison

variable {k : Type u}
variable {G : Type v}
variable {V : Type w}
variable [CommRing k] [Group G] [Fintype G]
variable [AddCommGroup V] [Module k V]

-- Source/core/bridge triage:
-- * source-facing: the norm comparison between the coinvariants and invariants of a
--   representation, and its low-degree homology/cohomology consequence under projectivity.
-- * core/canonical: `Representation.norm`, `Representation.Coinvariants`,
--   `Representation.invariants`, `Rep.desc`, `groupHomology.H0Iso`, and
--   `groupCohomology.H0Iso`.
-- * bridge/view: `normToTrivialInvariants` is the owner-level norm morphism into the trivial
--   representation on `ρ.invariants`, and `normToInvariants` is its canonical descent to
--   coinvariants; the remaining declarations record its projective and homological consequences.

/-- The norm morphism from `ρ` to the trivial representation on its invariant subspace. -/
noncomputable def normToTrivialInvariants (ρ : Representation k G V) :
    Rep.of ρ ⟶ Rep.trivial k G ρ.invariants :=
  Rep.ofHom
    ⟨ρ.norm.codRestrict ρ.invariants fun x g ↦ ρ.self_norm_apply g x, fun g ↦ by
      ext x
      simp
    ⟩

/-- The linear map on coinvariants induced by the owner-level norm morphism
`ρ ⟶ Rep.trivial k G ρ.invariants`. -/
noncomputable abbrev normToInvariants (ρ : Representation k G V) :
    ρ.Coinvariants →ₗ[k] ρ.invariants :=
  (Rep.desc (normToTrivialInvariants ρ)).hom

/-- On a class represented by `x`, the norm-induced map is the canonical norm `ρ.norm x`. -/
@[simp]
theorem normToInvariants_mk (ρ : Representation k G V) (x : V) :
    ↑(ρ.normToInvariants (Coinvariants.mk ρ x)) = ρ.norm x := by
  rfl

/-- Helper for Exercise 14-14.5-2: a left-regular invariant is determined by its value at `1`. -/
lemma leftRegular_invariant_apply_eq_apply_one
    (x : (leftRegular k G).invariants) (g : G) : x.1 g = x.1 1 := by
  -- Evaluate the invariance relation at the matching group element.
  simpa using (congrArg (fun f : G →₀ k => f g) (x.2 g)).symm

/-- Helper for Exercise 14-14.5-2: the scalar `r` corresponds to the constant left-regular
invariant obtained by taking the norm of `single 1 r`. -/
noncomputable def scalarToLeftRegularInvariants :
    k →ₗ[k] (leftRegular k G).invariants := by
  -- The norm is already `G`-invariant, so we can cod-restrict it.
  refine ((((leftRegular k G).norm).comp (Finsupp.lsingle (1 : G))).codRestrict _ ?_)
  intro r
  rw [Representation.mem_invariants]
  intro g
  exact (leftRegular k G).self_norm_apply g _

/-- Helper for Exercise 14-14.5-2: evaluation at `1` identifies left-regular invariants with
scalars. -/
noncomputable def leftRegularInvariantsEvalAtOne :
    (leftRegular k G).invariants →ₗ[k] k := by
  refine
    { toFun := fun x => x.1 1
      map_add' := by simp
      map_smul' := by simp }

/-- Helper for Exercise 14-14.5-2: evaluating at `1` after coordinatewise reconstruction is the
identity on scalars. -/
lemma leftRegular_invariants_eval_comp_reconstruct :
    leftRegularInvariantsEvalAtOne (k := k) (G := G) ∘ₗ
      scalarToLeftRegularInvariants (k := k) (G := G) =
        LinearMap.id := by
  -- The norm of `single 1 r` has value `r` at the identity.
  ext
  simp [scalarToLeftRegularInvariants, leftRegularInvariantsEvalAtOne, Representation.norm]

/-- Helper for Exercise 14-14.5-2: reconstructing from the value at `1` is the identity on the
left-regular invariant line. -/
lemma leftRegular_invariants_reconstruct_comp_eval :
    scalarToLeftRegularInvariants (k := k) (G := G) ∘ₗ
      leftRegularInvariantsEvalAtOne (k := k) (G := G) =
        LinearMap.id := by
  -- Two left-regular invariants agree once their coefficients agree pointwise.
  ext x g
  simp [scalarToLeftRegularInvariants, leftRegularInvariantsEvalAtOne, Representation.norm,
    leftRegular_invariant_apply_eq_apply_one]

/-- Helper for Exercise 14-14.5-2: the invariant line in the left-regular representation is
canonically isomorphic to `k`. -/
noncomputable def leftRegularInvariantsEquivScalar :
    (leftRegular k G).invariants ≃ₗ[k] k :=
  LinearEquiv.ofLinear
    (leftRegularInvariantsEvalAtOne (k := k) (G := G))
    (scalarToLeftRegularInvariants (k := k) (G := G))
    (leftRegular_invariants_eval_comp_reconstruct (k := k) (G := G))
    (leftRegular_invariants_reconstruct_comp_eval (k := k) (G := G))

/-- Helper for Exercise 14-14.5-2: summing the coefficients descends to the left-regular
coinvariants. -/
noncomputable def leftRegularCoinvariantsToScalar :
    (leftRegular k G).Coinvariants →ₗ[k] k := by
  -- The sum of coefficients is unchanged by left translation.
  refine Representation.Coinvariants.lift _ (Finsupp.linearCombination k (fun _ : G => (1 : k))) ?_
  intro g
  ext x
  simp [Finsupp.linearCombination_apply]

/-- Helper for Exercise 14-14.5-2: the class of `single 1 r` recovers a scalar in the
left-regular coinvariants. -/
noncomputable def scalarToLeftRegularCoinvariants :
    k →ₗ[k] (leftRegular k G).Coinvariants := by
  exact Representation.Coinvariants.mk _ ∘ₗ Finsupp.lsingle (1 : G)

/-- Helper for Exercise 14-14.5-2: `single g r` and `single 1 r` represent the same left-regular
coinvariant class. -/
lemma leftRegular_mk_single_eq_mk_single_one (g : G) (r : k) :
    Representation.Coinvariants.mk (leftRegular k G) (Finsupp.single g r) =
      Representation.Coinvariants.mk (leftRegular k G) (Finsupp.single (1 : G) r) := by
  -- Translate `single 1 r` by `g` and pass to coinvariants.
  simpa using (Representation.Coinvariants.mk_self_apply
    (ρ := leftRegular k G) g (Finsupp.single (1 : G) r))

/-- Helper for Exercise 14-14.5-2: summing coefficients after passing to the distinguished
coinvariant generator is the identity on scalars. -/
lemma leftRegular_coinvariants_scalar_comp_reconstruct :
    leftRegularCoinvariantsToScalar (k := k) (G := G) ∘ₗ
      scalarToLeftRegularCoinvariants (k := k) (G := G) =
        LinearMap.id := by
  -- The quotient preserves the coefficient sum on `single 1 r`.
  ext
  simp [leftRegularCoinvariantsToScalar, scalarToLeftRegularCoinvariants]

/-- Helper for Exercise 14-14.5-2: reconstructing a coinvariant class from its coefficient sum is
the identity on left-regular coinvariants. -/
lemma leftRegular_coinvariants_reconstruct_comp_scalar :
    scalarToLeftRegularCoinvariants (k := k) (G := G) ∘ₗ
      leftRegularCoinvariantsToScalar (k := k) (G := G) =
        LinearMap.id := by
  -- Reduce to generators `single g r` and move them to `single 1 r`.
  apply Representation.Coinvariants.hom_ext
  apply LinearMap.ext
  intro y
  induction y using Finsupp.induction_linear with
  | zero =>
      simp [leftRegularCoinvariantsToScalar, scalarToLeftRegularCoinvariants]
  | single g r =>
      simp [leftRegularCoinvariantsToScalar, scalarToLeftRegularCoinvariants,
        leftRegular_mk_single_eq_mk_single_one]
  | add y z hy hz =>
      simpa using congrArg₂ (· + ·) hy hz

/-- Helper for Exercise 14-14.5-2: the left-regular coinvariants are canonically isomorphic to
`k`. -/
noncomputable def leftRegularCoinvariantsEquivScalar :
    (leftRegular k G).Coinvariants ≃ₗ[k] k :=
  LinearEquiv.ofLinear
    (leftRegularCoinvariantsToScalar (k := k) (G := G))
    (scalarToLeftRegularCoinvariants (k := k) (G := G))
    (leftRegular_coinvariants_scalar_comp_reconstruct (k := k) (G := G))
    (leftRegular_coinvariants_reconstruct_comp_scalar (k := k) (G := G))

/-- Helper for Exercise 14-14.5-2: under the scalar models, the left-regular norm map is the
identity. -/
lemma leftRegular_normToInvariants_compat (x : (leftRegular k G).Coinvariants) :
    leftRegularInvariantsEquivScalar
        ((leftRegular k G).normToInvariants x) =
      leftRegularCoinvariantsEquivScalar x :=
by
  -- Compare the two scalar-valued linear maps on the quotient by checking generators.
  have hmaps :
      (leftRegularInvariantsEquivScalar (k := k) (G := G)).toLinearMap ∘ₗ
        (leftRegular k G).normToInvariants =
      (leftRegularCoinvariantsEquivScalar (k := k) (G := G)).toLinearMap := by
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro y
    induction y using Finsupp.induction_linear with
    | zero =>
        simp [leftRegularInvariantsEquivScalar, leftRegularInvariantsEvalAtOne,
          leftRegularCoinvariantsEquivScalar, leftRegularCoinvariantsToScalar]
    | single g r =>
        have hnorm :
            (((leftRegular k G).norm) (Finsupp.single g r)) 1 = r := by
          have h :=
            congrArg (fun T : (G →₀ k) →ₗ[k] G →₀ k => T (Finsupp.single g r))
              (Representation.leftRegular_norm_apply (k := k) (G := G))
          have h' := congrArg (fun f : G →₀ k => f 1) h
          have hone : (((leftRegular k G).norm) (Finsupp.single (1 : G) (1 : k))) 1 = 1 := by
            simp [Representation.norm]
          calc
            (((leftRegular k G).norm) (Finsupp.single g r)) 1 =
                r * (((leftRegular k G).norm) (Finsupp.single (1 : G) (1 : k))) 1 := by
                  simpa [Finsupp.linearCombination_apply] using h'
            _ = r := by rw [hone]; simp
        calc
          leftRegularInvariantsEquivScalar (k := k) (G := G)
              ((leftRegular k G).normToInvariants
                (Representation.Coinvariants.mk (leftRegular k G) (Finsupp.single g r))) = r := by
                  simpa [leftRegularInvariantsEquivScalar, leftRegularInvariantsEvalAtOne,
                    Representation.normToInvariants_mk] using hnorm
          _ = leftRegularCoinvariantsEquivScalar (k := k) (G := G)
                (Representation.Coinvariants.mk (leftRegular k G) (Finsupp.single g r)) := by
                  simp [leftRegularCoinvariantsEquivScalar, leftRegularCoinvariantsToScalar]
    | add y z hy hz =>
        simpa [LinearMap.map_add] using congrArg₂ (fun a b => a + b) hy hz
  -- Evaluating the linear-map identity at `x` gives the desired comparison.
  simpa using congrArg (fun f : (leftRegular k G).Coinvariants →ₗ[k] k => f x) hmaps

/-- Helper for Exercise 14-14.5-2: the norm map is bijective on the left-regular representation. -/
lemma leftRegular_normToInvariants_bijective :
    Function.Bijective ((leftRegular k G).normToInvariants) := by
  constructor
  · intro x y hxy
    apply (leftRegularCoinvariantsEquivScalar).injective
    simpa [leftRegular_normToInvariants_compat] using congrArg
      (leftRegularInvariantsEquivScalar) hxy
  · intro y
    refine ⟨(leftRegularCoinvariantsEquivScalar).symm
      ((leftRegularInvariantsEquivScalar) y), ?_⟩
    apply (leftRegularInvariantsEquivScalar).injective
    simp [leftRegular_normToInvariants_compat]

/-- Helper for Exercise 14-14.5-2: the invariant subspace of a free representation is the
finitely supported family of invariant lines in each left-regular coordinate. -/
noncomputable def freeCoordinateInvariantsEquiv (α : Type*) :
    let ρfree : Representation k G (α →₀ G →₀ k) := Representation.free k G α
    ρfree.invariants ≃ₗ[k] α →₀ (leftRegular k G).invariants := by
  let ρfree : Representation k G (α →₀ G →₀ k) := Representation.free k G α
  let forward : ρfree.invariants →ₗ[k] α →₀ (leftRegular k G).invariants :=
    { toFun := fun x =>
        let z : α →₀ (leftRegular k G).invariants :=
          { support := x.1.support
            toFun := fun i => ⟨x.1 i, fun g => by
              -- Each coordinate of a free invariant vector is left-regular invariant.
              classical
              have hcoord : (((Representation.free k G α) g) x.1) i = x.1 i := by
                exact congrArg (fun f : α →₀ G →₀ k => f i) (x.2 g)
              by_cases hx0 : x.1 i = 0
              · simp [hx0]
              · simpa [Representation.free, Representation.finsupp_apply, Finsupp.lsum_apply,
                  Finsupp.sum, Finsupp.single_apply, hx0] using hcoord⟩
            mem_support_toFun := by
              intro i
              constructor
              · intro hi
                have hx : x.1 i ≠ 0 := (Finsupp.mem_support_iff).1 hi
                intro h0
                exact hx (congrArg Subtype.val h0)
              · intro hi
                exact (Finsupp.mem_support_iff).2 (by
                  intro h0
                  apply hi
                  exact Subtype.ext h0) }
        z
      map_add' := by
        -- The coordinatewise construction is additive by definition.
        intro x y
        ext i g
        rfl
      map_smul' := by
        -- Scalar multiplication is also coordinatewise.
        intro r x
        ext i g
        rfl }
  let backward : (α →₀ (leftRegular k G).invariants) →ₗ[k] ρfree.invariants :=
    { toFun := fun y =>
        let z : α →₀ G →₀ k :=
          { support := y.support
            toFun := fun i => (y i).1
            mem_support_toFun := by
              intro i
              constructor
              · intro hi
                have hy : y i ≠ 0 := (Finsupp.mem_support_iff).1 hi
                intro h0
                apply hy
                exact Subtype.ext h0
              · intro hi
                exact (Finsupp.mem_support_iff).2 (by
                  intro h0
                  apply hi
                  exact congrArg Subtype.val h0) }
        ⟨z, by
          -- Reassembling invariant coordinates gives a free invariant vector.
          rw [Representation.mem_invariants]
          intro g
          ext i h
          classical
          have hcoord : (((Representation.free k G α) g) z) i = z i := by
            by_cases hy0 : y i = 0
            · have hz0 : z i = 0 := congrArg Subtype.val hy0
              simpa [Representation.free, Representation.finsupp_apply, Finsupp.lsum_apply,
                Finsupp.sum, Finsupp.single_apply, hz0]
            · have hz0 : z i ≠ 0 := by
                intro hz
                apply hy0
                exact Subtype.ext hz
              have hzi : (leftRegular k G) g (z i) = z i := by
                simpa using (y i).2 g
              simpa [Representation.free, Representation.finsupp_apply, Finsupp.lsum_apply,
                Finsupp.sum, Finsupp.single_apply, hz0, hzi] using hcoord
          exact congrArg (fun f : G →₀ k => f h) hcoord⟩
      map_add' := by
        -- The coordinatewise reassembly respects addition.
        intro x y
        ext i g
        rfl
      map_smul' := by
        -- The same reassembly is linear in scalars.
        intro r x
        ext i g
        rfl }
  exact
    LinearEquiv.ofLinear forward backward
      (by
        -- Forgetting and rebuilding recovers the original invariant family.
        ext x i g
        rfl)
      (by
        -- Rebuilding and then taking coordinates recovers the original free invariant vector.
        ext y i g
        rfl)

/-- Helper for Exercise 14-14.5-2: evaluating each free-invariant coordinate at `1` identifies
the invariant subspace of the free representation with `α →₀ k`. -/
noncomputable def freeInvariantsEquivFinsuppScalar (α : Type*) :
    let ρfree : Representation k G (α →₀ G →₀ k) := Representation.free k G α
    ρfree.invariants ≃ₗ[k] α →₀ k :=
  -- First keep the invariant proof coordinatewise, then evaluate each left-regular invariant at
  -- the identity element.
  (freeCoordinateInvariantsEquiv (k := k) (G := G) α).trans
    (Finsupp.mapRange.linearEquiv (leftRegularInvariantsEquivScalar (k := k) (G := G)))

/-- Helper for Exercise 14-14.5-2: the coinvariants of a free representation identify
coordinatewise with `α →₀ k`. -/
noncomputable def freeCoinvariantsEquivFinsuppScalar (α : Type*) :
    let ρfree : Representation k G (α →₀ G →₀ k) := Representation.free k G α
    ρfree.Coinvariants ≃ₗ[k] α →₀ k :=
  -- Descend coordinatewise to left-regular coinvariants, then use the scalar model in each slot.
  (Representation.coinvariantsFinsuppLEquiv (leftRegular k G) α).trans
    (Finsupp.mapRange.linearEquiv (leftRegularCoinvariantsEquivScalar (k := k) (G := G)))

/-- Helper for Exercise 14-14.5-2: the norm of a free basis vector is computed in its own
left-regular coordinate. -/
lemma free_norm_single_apply_self (α : Type*) (i : α) (y : G →₀ k) :
    ((Representation.free k G α).norm (Finsupp.single i y)) i = (leftRegular k G).norm y := by
  -- Linearity reduces the computation to a single basis vector in the left-regular coordinate.
  induction y using Finsupp.induction_linear with
  | zero =>
      simp [Representation.norm]
  | single g r =>
      ext h
      simp [Representation.norm]
  | add y z hy hz =>
      simp [Finsupp.single_add, LinearMap.map_add, hy, hz]

/-- Helper for Exercise 14-14.5-2: the norm of a free basis vector vanishes away from its chosen
coordinate. -/
lemma free_norm_single_apply_of_ne (α : Type*) {i j : α} (hji : j ≠ i) (y : G →₀ k) :
    ((Representation.free k G α).norm (Finsupp.single i y)) j = 0 := by
  -- The off-coordinate component also reduces linearly to the single-basis computation.
  induction y using Finsupp.induction_linear with
  | zero =>
      simp [Representation.norm]
  | single g r =>
      ext h
      simp [Representation.norm, hji]
  | add y z hy hz =>
      simp [Finsupp.single_add, LinearMap.map_add, hy, hz]

/-- Helper for Exercise 14-14.5-2: under the coordinatewise scalar models, the norm map on a free
representation is the identity. -/
lemma free_normToInvariants_compat (α : Type*) :
    let ρfree : Representation k G (α →₀ G →₀ k) := Representation.free k G α
    (freeInvariantsEquivFinsuppScalar (k := k) (G := G) α).toLinearMap ∘ₗ
      ρfree.normToInvariants =
        (freeCoinvariantsEquivFinsuppScalar (k := k) (G := G) α).toLinearMap := by
  let ρfree : Representation k G (α →₀ G →₀ k) := Representation.free k G α
  -- Check the two scalar-valued maps on coinvariants by reducing to free generators.
  apply Representation.Coinvariants.hom_ext
  apply LinearMap.ext
  intro y
  induction y using Finsupp.induction_linear with
  | zero =>
      ext i
      simp [freeInvariantsEquivFinsuppScalar, freeCoordinateInvariantsEquiv,
        freeCoinvariantsEquivFinsuppScalar]
  | single i y =>
      ext j
      by_cases hji : j = i
      · subst hji
        -- On a single free generator, everything reduces to the left-regular comparison.
        simpa [freeInvariantsEquivFinsuppScalar, freeCoordinateInvariantsEquiv,
          freeCoinvariantsEquivFinsuppScalar, Representation.normToInvariants_mk,
          free_norm_single_apply_self] using
            (leftRegular_normToInvariants_compat (k := k) (G := G)
              (x := Representation.Coinvariants.mk (leftRegular k G) y))
      · -- Off the distinguished coordinate, both transported maps vanish.
        simp [freeInvariantsEquivFinsuppScalar, freeCoordinateInvariantsEquiv,
          freeCoinvariantsEquivFinsuppScalar, Representation.normToInvariants_mk, hji,
          free_norm_single_apply_of_ne]
  | add y z hy hz =>
      -- The generator computation extends by linearity.
      simpa [LinearMap.map_add] using congrArg₂ (fun a b => a + b) hy hz

/-- Helper for Exercise 14-14.5-2: the norm map is bijective on free representations. -/
lemma free_normToInvariants_bijective (α : Type*) :
    let ρfree : Representation k G (α →₀ G →₀ k) := Representation.free k G α
    Function.Bijective ρfree.normToInvariants :=
by
  let ρfree : Representation k G (α →₀ G →₀ k) := Representation.free k G α
  constructor
  · intro x y hxy
    -- Compare both classes after transporting source and target to `α →₀ k`.
    apply (freeCoinvariantsEquivFinsuppScalar (k := k) (G := G) α).injective
    have hxy' := congrArg (freeInvariantsEquivFinsuppScalar (k := k) (G := G) α) hxy
    have hcompat := free_normToInvariants_compat (k := k) (G := G) (α := α)
    calc
      (freeCoinvariantsEquivFinsuppScalar (k := k) (G := G) α) x =
          (freeInvariantsEquivFinsuppScalar (k := k) (G := G) α) (ρfree.normToInvariants x) := by
            simpa using (LinearMap.congr_fun hcompat x).symm
      _ = (freeInvariantsEquivFinsuppScalar (k := k) (G := G) α) (ρfree.normToInvariants y) := by
            rw [hxy]
      _ = (freeCoinvariantsEquivFinsuppScalar (k := k) (G := G) α) y := by
            simpa using LinearMap.congr_fun hcompat y
  · intro y
    -- Use the scalar model to write down the inverse image explicitly.
    refine
      ⟨(freeCoinvariantsEquivFinsuppScalar (k := k) (G := G) α).symm
          ((freeInvariantsEquivFinsuppScalar (k := k) (G := G) α) y), ?_⟩
    apply (freeInvariantsEquivFinsuppScalar (k := k) (G := G) α).injective
    have hcompat := free_normToInvariants_compat (k := k) (G := G) (α := α)
    simpa using
      LinearMap.congr_fun hcompat
        ((freeCoinvariantsEquivFinsuppScalar (k := k) (G := G) α).symm
          ((freeInvariantsEquivFinsuppScalar (k := k) (G := G) α) y))

/-- Helper for Exercise 14-14.5-2: an intertwining map induces a map on invariant subspaces. -/
noncomputable def mapInvariants {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {τ : Representation k G W} (f : ρ.IntertwiningMap τ) :
    ρ.invariants →ₗ[k] τ.invariants := by
  refine (f.toLinearMap.comp ρ.invariants.subtype).codRestrict _ ?_
  intro x
  rw [Representation.mem_invariants]
  intro g
  have hf : f (ρ g x.1) = f x.1 := congrArg (fun v => f v) (x.2 g)
  calc
    τ g (f x.1) = f (ρ g x.1) := by
      simpa using (congrArg (fun T : V →ₗ[k] W => T x.1) (f.2 g)).symm
    _ = f x.1 := hf

/-- Helper for Exercise 14-14.5-2: `normToInvariants` is natural with respect to intertwining
maps. -/
lemma normToInvariants_commutes {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {τ : Representation k G W} (f : ρ.IntertwiningMap τ) :
    mapInvariants f ∘ₗ ρ.normToInvariants =
      τ.normToInvariants ∘ₗ
        Representation.Coinvariants.map ρ τ f.toLinearMap (fun g => f.isIntertwining' g) := by
  -- Check the square on representatives and descend by `Coinvariants.hom_ext`.
  apply Representation.Coinvariants.hom_ext
  ext x
  simp [mapInvariants, Representation.normToInvariants_mk, Representation.norm, f.isIntertwining]

/-- Helper for Exercise 14-14.5-2: projectivity supplies the canonical map into the free module
on the underlying `k[G]`-module. -/
noncomputable def projectiveSplit (ρ : Representation k G V)
    [Module.Projective k[G] ρ.asModule] :
    ρ.asModule →ₗ[k[G]] (ρ.asModule →₀ k[G]) := by
  exact Classical.choose (Module.projective_def'.mp ‹Module.Projective k[G] ρ.asModule›)

/-- Helper for Exercise 14-14.5-2: the canonical projective split is a right inverse to linear
combination. -/
lemma projectiveSplit_comp (ρ : Representation k G V)
    [Module.Projective k[G] ρ.asModule] :
    Finsupp.linearCombination k[G] (id : ρ.asModule → ρ.asModule) ∘ₗ
      projectiveSplit ρ =
        LinearMap.id := by
  exact Classical.choose_spec (Module.projective_def'.mp ‹Module.Projective k[G] ρ.asModule›)

/-- Helper for Exercise 14-14.5-2: projectivity realizes `ρ` as a summand of the canonical free
representation on `ρ.asModule`. -/
noncomputable def projectiveSection (ρ : Representation k G V)
    [Module.Projective k[G] ρ.asModule] :
    ρ.IntertwiningMap (Representation.free k G ρ.asModule) := by
  -- Convert the module-level splitting to an intertwining map.
  refine (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := ρ) (σ := Representation.free k G ρ.asModule)).symm ?_
  exact (Representation.finsuppLEquivFreeAsModule k G ρ.asModule).toLinearMap ∘ₗ
    projectiveSplit ρ

/-- Helper for Exercise 14-14.5-2: the free representation on `ρ.asModule` retracts onto `ρ`. -/
noncomputable def projectiveRetraction (ρ : Representation k G V) :
    (Representation.free k G ρ.asModule).IntertwiningMap ρ := by
  -- This is the universal free-module linear combination map, viewed as an intertwiner.
  refine (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := Representation.free k G ρ.asModule) (σ := ρ)).symm ?_
  exact Finsupp.linearCombination k[G] (id : ρ.asModule → ρ.asModule) ∘ₗ
    (Representation.finsuppLEquivFreeAsModule k G ρ.asModule).symm.toLinearMap

/-- Helper for Exercise 14-14.5-2: the inverse direction of `equivLinearMapAsModule` evaluates by
definition on underlying vectors. -/
@[simp] theorem IntertwiningMap.symm_equivLinearMapAsModule_apply {W : Type*}
    [AddCommGroup W] [Module k W] {ρ : Representation k G V} {τ : Representation k G W}
    (ℓ : ρ.asModule →ₗ[k[G]] τ.asModule) (x : V) :
    ((Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := τ)).symm ℓ)
      (ρ.asModuleEquiv.symm x) =
        ℓ (ρ.asModuleEquiv.symm x) := by
  rfl

/-- Helper for Exercise 14-14.5-2: the projective retraction cancels the projective section on
underlying vectors. -/
lemma projectiveRetraction_section_apply (ρ : Representation k G V)
    [Module.Projective k[G] ρ.asModule] (x : V) :
    projectiveRetraction ρ ((projectiveSection ρ) x) = x := by
  -- After transporting through the free-module equivalence, the statement is exactly the
  -- module-level splitting identity chosen from projectivity.
  change
    (Finsupp.linearCombination k[G] (id : ρ.asModule → ρ.asModule))
      (((Representation.finsuppLEquivFreeAsModule k G ρ.asModule).symm)
        (((Representation.finsuppLEquivFreeAsModule k G ρ.asModule).toLinearMap)
          (projectiveSplit ρ (ρ.asModuleEquiv.symm x)))) = ρ.asModuleEquiv.symm x
  simpa using LinearMap.congr_fun (projectiveSplit_comp (ρ := ρ)) (ρ.asModuleEquiv.symm x)

/-- Helper for Exercise 14-14.5-2: the projective section and retraction compose to the identity. -/
lemma projectiveRetraction_comp_section (ρ : Representation k G V)
    [Module.Projective k[G] ρ.asModule] :
    (projectiveRetraction ρ).toLinearMap.comp
        (projectiveSection ρ).toLinearMap =
      LinearMap.id :=
by
  -- The new pointwise retract lemma turns the linear-map identity into a direct extensionality
  -- argument.
  ext x
  exact projectiveRetraction_section_apply (ρ := ρ) x

/-- Helper for Exercise 14-14.5-2: bijectivity of `normToInvariants` descends along a retract. -/
lemma normToInvariants_bijective_of_retract {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {τ : Representation k G W}
    (i : ρ.IntertwiningMap τ) (p : τ.IntertwiningMap ρ)
    (hpi : p.toLinearMap.comp i.toLinearMap = LinearMap.id)
    (hτ : Function.Bijective τ.normToInvariants) :
    Function.Bijective ρ.normToInvariants :=
by
  let coinvMapI :=
    Representation.Coinvariants.map ρ τ i.toLinearMap (fun g => i.isIntertwining' g)
  let coinvMapP :=
    Representation.Coinvariants.map τ ρ p.toLinearMap (fun g => p.isIntertwining' g)
  have hcoinv : coinvMapP.comp coinvMapI = LinearMap.id := by
    -- The source-side retract identity descends functorially to coinvariants.
    simp [coinvMapI, coinvMapP, Representation.Coinvariants.map_comp, hpi]
  have hinv : mapInvariants p ∘ₗ mapInvariants i = LinearMap.id := by
    -- The target-side retract identity restricts directly to invariant subspaces.
    ext x
    change p (i x.1) = x.1
    simpa using congrArg (fun T : V →ₗ[k] V => T x.1) hpi
  constructor
  · intro x y hxy
    -- Apply the retract inclusion on invariants, use injectivity in the larger object, and
    -- descend back with the source-side split.
    have hxy' : τ.normToInvariants (coinvMapI x) = τ.normToInvariants (coinvMapI y) := by
      calc
        τ.normToInvariants (coinvMapI x) = mapInvariants i (ρ.normToInvariants x) := by
          simpa [coinvMapI] using
            (LinearMap.congr_fun (normToInvariants_commutes (f := i)) x).symm
        _ = mapInvariants i (ρ.normToInvariants y) := by rw [hxy]
        _ = τ.normToInvariants (coinvMapI y) := by
          simpa [coinvMapI] using
            (LinearMap.congr_fun (normToInvariants_commutes (f := i)) y)
    have hi : coinvMapI x = coinvMapI y := hτ.1 hxy'
    calc
      x = coinvMapP (coinvMapI x) := by
        symm
        show coinvMapP (coinvMapI x) = x
        simpa using LinearMap.congr_fun hcoinv x
      _ = coinvMapP (coinvMapI y) := by simpa [coinvMapP] using congrArg coinvMapP hi
      _ = y := by
        show coinvMapP (coinvMapI y) = y
        simpa using LinearMap.congr_fun hcoinv y
  · intro y
    -- Lift `mapInvariants i y` through surjectivity upstairs, then project back along the retract.
    rcases hτ.2 (mapInvariants i y) with ⟨z, hz⟩
    refine ⟨coinvMapP z, ?_⟩
    calc
      ρ.normToInvariants (coinvMapP z) = mapInvariants p (τ.normToInvariants z) := by
        simpa [coinvMapP] using
          (LinearMap.congr_fun (normToInvariants_commutes (f := p)) z).symm
      _ = mapInvariants p (mapInvariants i y) := by rw [hz]
      _ = y := by simpa using LinearMap.congr_fun hinv y

-- Proof sketch: projectivity of the underlying `k[G]`-module gives a splitting of the quotient
-- `V → V_G`; compare that splitting with the norm-induced comparison to prove injectivity and
-- surjectivity.
/-- For a projective representation, the norm-induced comparison
`ρ.Coinvariants →ₗ[k] ρ.invariants` is bijective. -/
theorem normToInvariants_bijective_of_projective (ρ : Representation k G V)
    [Module.Projective k[G] ρ.asModule] :
    Function.Bijective ρ.normToInvariants :=
by
  -- Projectivity identifies `ρ` as a retract of the free representation on `ρ.asModule`.
  simpa using
    normToInvariants_bijective_of_retract
      (i := projectiveSection ρ)
      (p := projectiveRetraction ρ)
      (hpi := projectiveRetraction_comp_section (ρ := ρ))
      (hτ := free_normToInvariants_bijective (k := k) (G := G) (α := ρ.asModule))

end NormComparison

section NormComparisonHomology

variable {k G V : Type u}
variable [CommRing k] [Group G] [Fintype G]
variable [AddCommGroup V] [Module k V]

/-- Exercise 14-14.5-2: if the `k[G]`-module underlying `ρ` is projective, then the norm-induced
comparison on coinvariants identifies the canonical low-degree objects `H₀(G, ρ)` and `H⁰(G, ρ).
-/
noncomputable def homologyH0IsoCohomologyH0_of_projective (ρ : Representation k G V)
    [Module.Projective k[G] ρ.asModule] :
    groupHomology.H0 (A := (Rep.of ρ : Rep k G)) ≅
      groupCohomology.H0 (A := (Rep.of ρ : Rep k G)) := by
  let A : Rep k G := Rep.of ρ
  exact
    groupHomology.H0Iso A ≪≫
      (LinearEquiv.ofBijective ρ.normToInvariants
        (normToInvariants_bijective_of_projective ρ)).toModuleIso ≪≫
      (groupCohomology.H0Iso A).symm

end NormComparisonHomology

section DualCoannihilator

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

-- Proof sketch: a functional on `(ρ.dual).Coinvariants` is the same as a functional on
-- `Module.Dual k V` killing the relations `ρ.dual g φ - φ`; this is exactly evaluation at a
-- `G`-fixed vector of `V`, so no finite-dimensional hypothesis is needed here.
theorem invariants_eq_dualCoannihilator [Module.Projective k V] :
    ρ.invariants = (Coinvariants.ker ρ.dual).dualCoannihilator := by
  ext x
  rw [Submodule.mem_dualCoannihilator, Representation.mem_invariants]
  constructor
  · intro hx φ hφ
    rw [Coinvariants.ker] at hφ
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
    · intro ψ hψ
      rcases hψ with ⟨⟨g, χ⟩, rfl⟩
      change (ρ.dual g χ) x - χ x = 0
      simp [Representation.dual, hx g⁻¹]
    · simp
    · intro ψ χ _ _ hψ hχ
      simp [hψ, hχ]
    · intro a ψ _ hψ
      simp [hψ]
  · intro hx g
    apply sub_eq_zero.mp
    apply (forall_dual_apply_eq_zero_iff k ((ρ g) x - x)).mp
    intro φ
    specialize hx (ρ.dual g⁻¹ φ - φ) (Coinvariants.sub_mem_ker g⁻¹ φ)
    simpa [Representation.dual] using hx

end DualCoannihilator

section Dualities

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

section FiniteDimensional

variable [FiniteDimensional k V]

/-- The invariant subspace of a finite-dimensional representation is naturally dual to the
coinvariants of its dual representation. -/
noncomputable def invariants_equiv_dual_coinvariants_dual :
    ρ.invariants ≃ₗ[k] Module.Dual k (ρ.dual.Coinvariants) := by
  let h : ρ.invariants.map (Module.evalEquiv k V).toLinearMap =
      (Coinvariants.ker ρ.dual).dualAnnihilator := by
    rw [invariants_eq_dualCoannihilator ρ]
    simpa using Subspace.map_dualCoannihilator (Coinvariants.ker ρ.dual)
  exact
    ((Module.evalEquiv k V).submoduleMap ρ.invariants).trans <|
      (LinearEquiv.ofEq _ _ h).trans <|
        (Coinvariants.ker ρ.dual).dualQuotEquivDualAnnihilator.symm

/-- Helper for Exercise 14-14.5-2: a representation equivalence induces an equivalence on
coinvariants. -/
noncomputable def coinvariantsCongr {W : Type*} [AddCommGroup W] [Module k W]
    {τ : Representation k G W} (e : ρ.Equiv τ) :
    ρ.Coinvariants ≃ₗ[k] τ.Coinvariants :=
  LinearEquiv.ofLinear
    (Representation.Coinvariants.map ρ τ e.toLinearMap fun g => e.isIntertwining' g)
    (Representation.Coinvariants.map τ ρ e.symm.toLinearMap fun g => e.symm.isIntertwining' g)
    (by
      -- The forward and backward maps compose to the identity on coinvariants.
      ext x
      simp [Representation.Coinvariants.map_comp])
    (by
      -- The same computation gives the reverse composition identity.
      ext x
      simp [Representation.Coinvariants.map_comp])

/-- Helper for Exercise 14-14.5-2: evaluation identifies a finite-dimensional representation with
its bidual representation. -/
noncomputable def dual_eval_rep_equiv : ρ.Equiv ρ.dual.dual := by
  refine Representation.Equiv.mk (Module.evalEquiv k V) ?_
  intro g
  -- Evaluate the bidual action against a dual vector and simplify both sides.
  ext x φ
  simp [Representation.dual_apply, Module.Dual.transpose_apply]

-- Proof sketch: combine `invariants_equiv_dual_coinvariants_dual` with the fact that dual
-- vector spaces have the same finite dimension, and use the projective comparison from part (a)
-- for `ρ.dual`; only finiteness of `G` is needed here, and a local `Fintype` instance supplies
-- the norm-comparison theorem.
/-- Helper for Exercise 14-14.5-2: for a finite-dimensional projective representation, the
invariant subspaces of `ρ` and of its dual representation have the same dimension. -/
theorem finrank_invariants_eq_finrank_dual_invariants_of_projective
    [Finite G]
    [Module.Projective k[G] ρ.asModule] :
    Module.finrank k ρ.invariants = Module.finrank k ρ.dual.invariants := by
  -- A finite group is enough; instantiate the canonical `Fintype` structure only where the
  -- norm comparison from part (a) needs it.
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional k ρ.Coinvariants :=
    FiniteDimensional.of_surjective (Coinvariants.mk ρ) (Coinvariants.mk_surjective (ρ := ρ))
  letI : FiniteDimensional k ρ.dual.dual.Coinvariants :=
    FiniteDimensional.of_surjective (Coinvariants.mk ρ.dual.dual)
      (Coinvariants.mk_surjective (ρ := ρ.dual.dual))
  have hbij := normToInvariants_bijective_of_projective (ρ := ρ)
  have hnorm_le : Module.finrank k ρ.invariants ≤ Module.finrank k ρ.Coinvariants :=
    LinearMap.finrank_le_finrank_of_surjective (f := ρ.normToInvariants) hbij.surjective
  have hnorm_ge : Module.finrank k ρ.Coinvariants ≤ Module.finrank k ρ.invariants :=
    LinearMap.finrank_le_finrank_of_injective (f := ρ.normToInvariants) hbij.injective
  have hnorm : Module.finrank k ρ.invariants = Module.finrank k ρ.Coinvariants :=
    le_antisymm hnorm_le hnorm_ge
  have hbidual :
      Module.finrank k ρ.Coinvariants = Module.finrank k ρ.dual.dual.Coinvariants :=
    (coinvariantsCongr (ρ := ρ) (dual_eval_rep_equiv (ρ := ρ))).finrank_eq
  have hdual :
      Module.finrank k ρ.dual.invariants =
        Module.finrank k (Module.Dual k ρ.dual.dual.Coinvariants) :=
    (invariants_equiv_dual_coinvariants_dual (ρ := ρ.dual)).finrank_eq
  have hdual' :
      Module.finrank k ρ.dual.dual.Coinvariants =
        Module.finrank k (Module.Dual k ρ.dual.dual.Coinvariants) := by
    -- Dual vector spaces have the same finite dimension.
    exact (Subspace.dual_finrank_eq (K := k) (V := ρ.dual.dual.Coinvariants)).symm
  -- Replace invariants by coinvariants for `ρ`, transport through the bidual equivalence,
  -- and identify the result with the dual description of `ρ.dual.invariants`.
  rw [hnorm, hbidual, hdual']
  exact hdual.symm

end FiniteDimensional

end Dualities

end Representation

/-! ### Exercise_14_14_5_3 (from Chap14) -/
open scoped MonoidAlgebra

universe u v w x

noncomputable section

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Finite G]
variable {E : Type w} [AddCommGroup E] [Module k E] [Module k[G] E] [IsScalarTower k k[G] E]
variable {F : Type x} [AddCommGroup F] [Module k F] [Module k[G] F] [IsScalarTower k k[G] F]

/-- Exercise 14-14.5-3: if `E` is a projective `k[G]`-module, then the spaces of
`k[G]`-linear maps `E → F` and `F → E` have the same dimension over `k`. -/
theorem finrank_hom_eq_finrank_hom_swap_of_projective
    [Module.Projective k[G] E]
    [FiniteDimensional k E] [FiniteDimensional k F] :
    Module.finrank k (E →ₗ[k[G]] F) = Module.finrank k (F →ₗ[k[G]] E) :=
by
  -- Route correction: follow LinearRepresentations_Serre_1977's source proof literally through the internal-Hom
  -- representation `ρ := Hom(E,F)`, rather than switching to the trace-pairing shortcut.
  letI : Module k (RestrictScalars k k[G] E) :=
    restrictScalars_module (k := k) (G := G) E
  letI : Module k (RestrictScalars k k[G] F) :=
    restrictScalars_module (k := k) (G := G) F
  letI : Module k (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F) :=
    wrapped_restrictScalars_linHom_module (k := k) (G := G) E F
  letI : Module k (RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] E) :=
    wrapped_restrictScalars_linHom_module (k := k) (G := G) F E
  let ρEF := ofModule_linHom_rep (k := k) (G := G) E F
  -- Package projectivity so that Exercise 14-14.5-2 applies directly to the frozen owner.
  have hproj : Module.Projective k[G] ρEF.asModule := by
    simpa [ρEF, ofModule_linHom_rep_rfl] using
      linHom_projective_of_projective_source (k := k) (G := G) (E := E) (F := F)
  -- This is the core equality supplied by Exercise 14-14.5-2.
  have hcore := by
    letI := @FiniteDimensional.of_injective k
      (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F)
      inferInstance
      inferInstance
      (wrapped_restrictScalars_linHom_module (k := k) (G := G) E F)
      (E →ₗ[k] F)
      inferInstance
      inferInstance
      (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)).toLinearMap
      (restrictScalars_linHom_linearEquiv (k := k) (G := G) (E := E) (F := F)).injective
    exact @Representation.finrank_invariants_eq_finrank_dual_invariants_of_projective
      k inferInstance G inferInstance
      (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F)
      inferInstance
      (wrapped_restrictScalars_linHom_module (k := k) (G := G) E F)
      ρEF inferInstance inferInstance hproj
  -- The left invariant space is exactly `Hom_G(E,F)`.
  have hleftIntertwining :=
    (@Representation.invariantsEquivIntertwiningMap k G
      (RestrictScalars k k[G] E) (RestrictScalars k k[G] F)
      inferInstance inferInstance inferInstance
      (restrictScalars_module (k := k) (G := G) E)
      inferInstance
      (restrictScalars_module (k := k) (G := G) F)
      (Representation.ofModule (k := k) (G := G) E)
      (Representation.ofModule (k := k) (G := G) F)).finrank_eq
  -- The source-facing bridge from intertwining maps to `k[G]`-linear maps is already packaged.
  have hleftLinear :=
    ofModule_intertwining_finrank_eq (k := k) (G := G) (E := E) (F := F)
  have hleft := by
    simpa [ρEF, ofModule_linHom_rep_rfl] using hleftIntertwining.trans hleftLinear
  -- The dual internal-Hom owner is identified with the swapped internal-Hom representation.
  have hrightSwap :=
    (@invariantsCongr k inferInstance G inferInstance
      (Module.Dual k (RestrictScalars k k[G] E →ₗ[k] RestrictScalars k k[G] F))
      inferInstance inferInstance
      (RestrictScalars k k[G] F →ₗ[k] RestrictScalars k k[G] E)
      inferInstance
      (wrapped_restrictScalars_linHom_module (k := k) (G := G) F E)
      ρEF.dual
      (ofModule_linHom_rep (k := k) (G := G) F E)
      (dual_linHom_ofModule_equiv_linHom_swap
        (k := k) (G := G) (E := E) (F := F))).finrank_eq
  -- Once swapped, the same intertwining/Hom bridge identifies the right-hand side with
  -- `Hom_G(F,E)`.
  have hrightIntertwining :=
    (@Representation.invariantsEquivIntertwiningMap k G
      (RestrictScalars k k[G] F) (RestrictScalars k k[G] E)
      inferInstance inferInstance inferInstance
      (restrictScalars_module (k := k) (G := G) F)
      inferInstance
      (restrictScalars_module (k := k) (G := G) E)
      (Representation.ofModule (k := k) (G := G) F)
      (Representation.ofModule (k := k) (G := G) E)).finrank_eq
  have hrightLinear :=
    ofModule_intertwining_finrank_eq (k := k) (G := G) (E := F) (F := E)
  have hrightStep := by
    simpa [ofModule_linHom_rep_rfl] using hrightIntertwining.trans hrightLinear
  have hright := by
    simpa [ρEF] using hrightSwap.trans hrightStep
  -- Compose the two source-faithful bridge identifications with Exercise 14-14.5-2.
  exact hleft.symm.trans (hcore.trans hright)

end
