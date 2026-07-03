import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_3_1
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_5_4
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_5_5.DualEnvelopeBridge

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra
open Representation

universe u w x y

noncomputable section

section

variable (k : Type u) [Field k]
variable (G : Type u) [Group G] [Finite G]

local notation "ofModule" => @Representation.ofModule k G _ _

variable {k G}
variable {E : Type w} [AddCommGroup E] [Module k E] [Module k[G] E]
  [IsScalarTower k k[G] E]
variable {P : Type x} [AddCommGroup P] [Module k[G] P]
variable {Q : Type y} [AddCommGroup Q] [Module k[G] Q]

/-- Helper for Exercise 14-14.5-5: the plain `k`-linear dual of a finite direct sum is the finite
direct sum of the plain duals. -/
private noncomputable abbrev linearDual_dfinsupp_linearEquiv_fin
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)] :
    Module.Dual k (Π₀ i : Fin n, P i) ≃ₗ[k] (Π₀ i : Fin n, Module.Dual k (P i)) :=
  let eDfinsupp :
      Module.Dual k (Π₀ i : Fin n, P i) ≃ₗ[k] Module.Dual k ((i : Fin n) → P i) :=
    (DFinsupp.linearEquivFunOnFintype (R := k) (M := P)).symm.dualMap
  let ePi :
      Module.Dual k ((i : Fin n) → P i) ≃ₗ[k] ((i : Fin n) → Module.Dual k (P i)) :=
    (LinearMap.lsum k P k).symm
  let eBack :
      ((i : Fin n) → Module.Dual k (P i)) ≃ₗ[k] (Π₀ i : Fin n, Module.Dual k (P i)) :=
    (DFinsupp.linearEquivFunOnFintype (R := k) (M := fun i => Module.Dual k (P i))).symm
  eDfinsupp.trans (ePi.trans eBack)

/-- Helper for Exercise 14-14.5-5: the finite direct-sum dual bridge evaluates a functional on the
singleton vector in the chosen summand. -/
private theorem dfinsupp_equivFunOnFintype_symm_single
    {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Zero (β i)]
    (i : ι) (x : β i) :
    DFinsupp.equivFunOnFintype.symm (Pi.single i x) = DFinsupp.single i x := by
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp

/-- Helper for Exercise 14-14.5-5: the finite direct-sum dual bridge evaluates a functional on the
singleton vector in the chosen summand. -/
private theorem linearDual_dfinsupp_linearEquiv_fin_apply
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    (φ : Module.Dual k (Π₀ i : Fin n, P i)) (i : Fin n) (x : P i) :
    (linearDual_dfinsupp_linearEquiv_fin (k := k) (P := P) φ i) x = φ (DFinsupp.single i x) := by
  classical
  -- The bridge is the usual finite-product duality transported across the
  -- `DFinsupp.linearEquivFunOnFintype` identifications.
  change
    (((DFinsupp.linearEquivFunOnFintype (R := k) (M := fun j => Module.Dual k (P j))).symm
        ((LinearMap.lsum k P k).symm
          (((DFinsupp.linearEquivFunOnFintype (R := k) (M := P)).symm).dualMap φ))) i) x =
      φ (DFinsupp.single i x)
  rw [DFinsupp.linearEquivFunOnFintype_symm_apply]
  change
    (((LinearMap.lsum k P k).symm
        (((DFinsupp.linearEquivFunOnFintype (R := k) (M := P)).symm).dualMap φ)) i) x =
      φ (DFinsupp.single i x)
  rw [LinearMap.lsum_symm_apply]
  change
    ((DFinsupp.linearEquivFunOnFintype (R := k) (M := P)).symm.dualMap φ)
        (Pi.single i x) =
      φ (DFinsupp.single i x)
  change φ ((DFinsupp.linearEquivFunOnFintype (R := k) (M := P)).symm (Pi.single i x)) =
    φ (DFinsupp.single i x)
  rw [DFinsupp.linearEquivFunOnFintype_symm_apply]
  rw [dfinsupp_equivFunOnFintype_symm_single]

/-- Helper for Exercise 14-14.5-5: the canonical `k`-module structure on the finite DFinsupp of
owner duals is the pointwise one. -/
private noncomputable instance dfinsupp_ownerDual_module
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)] :
    Module k (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) :=
  DFinsupp.module

/-- Helper for Exercise 14-14.5-5: the canonical `k[G]`-module structure on the finite DFinsupp
of owner duals is the pointwise one. -/
private noncomputable instance dfinsupp_ownerDual_groupAlgebra_module
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)] :
    Module k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) :=
  DFinsupp.module

/-- Helper for Exercise 14-14.5-5: the finite DFinsupp of owner duals inherits the pointwise
scalar tower from its summands. -/
private instance dfinsupp_ownerDual_isScalarTower
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)] :
    IsScalarTower k k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) where
  smul_assoc a b x := by
    -- Route correction: register the canonical pointwise tower once, instead of quantifying over
    -- an arbitrary whole-space DFinsupp tower in every later bridge lemma.
    ext i
    change ((a • b) • x i) = a • (b • x i)
    exact smul_assoc a b (x i)

section
omit [Finite G] [Module k E] [IsScalarTower k k[G] E]

/-- Helper for Exercise 14-14.5-5: on the canonical DFinsupp direct sum of owner duals, the
scalar-tower action is computed componentwise. -/
private theorem dfinsupp_ownerDual_smul_assoc
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)]
    [Module k (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))]
    [Module k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))]
    [IsScalarTower k k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))]
    (a : k) (b : k[G]) (x : Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) (i : Fin n) :
    (((a • b) • x : Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) i) =
      ((a • (b • x) : Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) i) := by
  -- Both scalar actions on the finite direct sum are computed componentwise.
  exact congrArg (fun y : Π₀ i : Fin n, ((ofModule (P i)).dual.asModule) => y i)
    (smul_assoc a b x)

end

section
omit [Finite G] [Module k E] [IsScalarTower k k[G] E]
variable {E : Type w} [AddCommGroup E] [Module k[G] E]

/-- Helper for Exercise 14-14.5-5: the canonical `k[G]`-action on the finite DFinsupp direct sum
of owner duals is computed componentwise. -/
private theorem dfinsupp_ownerDual_groupAlgebra_smul_apply
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)]
    [∀ i, SMulZeroClass k[G] ((ofModule (P i)).dual.asModule)]
    [Module k (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))]
    [Module k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))]
    [IsScalarTower k k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))]
    (b : k[G]) (x : Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) (i : Fin n) :
    ((b • x : Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) i) = b • x i := by
  -- The DFinsupp module structure is pointwise on every group-algebra scalar.
  exact DFinsupp.smul_apply b x i

end

section
omit [Finite G]

/-- Helper for Exercise 14-14.5-5: the basis group element action on the owner-dual DFinsupp
target is already componentwise. -/
private theorem dfinsupp_ownerDual_of_smul_apply
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)]
    [∀ i, SMulZeroClass k[G] ((ofModule (P i)).dual.asModule)]
    [Module k (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))]
    [Module k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))]
    [IsScalarTower k k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))]
    (g : G) (x : Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) (i : Fin n) :
    ((MonoidAlgebra.of k G g) • x : Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) i =
      (MonoidAlgebra.of k G g) • x i := by
  -- This is the basis-scalar specialization of the pointwise DFinsupp action.
  exact dfinsupp_ownerDual_groupAlgebra_smul_apply
    (k := k) (G := G) (P := P) (b := MonoidAlgebra.of k G g) (x := x) (i := i)

end

/-- Helper for Exercise 14-14.5-5: forgetting the owner `k[G]`-structure on the finite direct sum
of owner duals and then transporting each summand identifies the whole codomain with the plain
finite direct sum of `k`-linear duals. -/
private noncomputable abbrev dfinsupp_ownerDual_restrictScalars_to_linearDual_fin
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)] :
    RestrictScalars k k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) ≃ₗ[k]
      (Π₀ i : Fin n, Module.Dual k (P i)) :=
  -- Route correction: unwrap the outer `RestrictScalars` only once on the whole DFinsupp, then
  -- transport each coordinate by the existing summandwise owner-dual/plain-dual equivalence.
  (restrictScalars_linearEquiv (k := k) (G := G)
      (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))).trans
    (DFinsupp.mapRange.linearEquiv fun i =>
      owner_dual_to_linearDual (k := k) (G := G) (P := P i))

section
omit [Finite G]

/-- Helper for Exercise 14-14.5-5: the canonical DFinsupp codomain transport acts componentwise
after the `RestrictScalars` rewrapping of the whole owner-dual direct sum. -/
private theorem dfinsupp_ownerDual_restrictScalars_to_linearDual_fin_apply
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)]
    (x : RestrictScalars k k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)))
    (i : Fin n) :
    dfinsupp_ownerDual_restrictScalars_to_linearDual_fin (k := k) (G := G) (P := P) x i =
      owner_dual_to_linearDual (k := k) (G := G) (P := P i)
        (((restrictScalars_linearEquiv (k := k) (G := G)
            (Π₀ j : Fin n, ((ofModule (P j)).dual.asModule))) x) i) := by
  -- Read the `i`-th coordinate after the outer unwrap, then use the component map of
  -- `DFinsupp.mapRange.linearEquiv`.
  rw [dfinsupp_ownerDual_restrictScalars_to_linearDual_fin]
  rw [LinearEquiv.trans_apply]
  -- After unfolding the transport, the `i`-th coordinate is definitionally the component map.
  rfl

end

/-- Helper for Exercise 14-14.5-5: the inverse DFinsupp codomain transport also reads
componentwise after rewrapping through `RestrictScalars`. -/
private theorem dfinsupp_ownerDual_restrictScalars_to_linearDual_fin_symm_apply
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)]
    (Φ : Π₀ i : Fin n, Module.Dual k (P i)) (i : Fin n) :
    (((restrictScalars_linearEquiv (k := k) (G := G)
        (Π₀ j : Fin n, ((ofModule (P j)).dual.asModule)))
        ((dfinsupp_ownerDual_restrictScalars_to_linearDual_fin
          (k := k) (G := G) (P := P)).symm Φ)) i) =
      (owner_dual_to_linearDual (k := k) (G := G) (P := P i)).symm (Φ i) := by
  -- Apply the forward coordinate formula to the inverse image and cancel the composed finite
  -- transport componentwise.
  apply (owner_dual_to_linearDual (k := k) (G := G) (P := P i)).injective
  have h :=
    dfinsupp_ownerDual_restrictScalars_to_linearDual_fin_apply (k := k) (G := G) (P := P)
      (x := (dfinsupp_ownerDual_restrictScalars_to_linearDual_fin
        (k := k) (G := G) (P := P)).symm Φ)
      (i := i)
  simpa using h.symm

/-- Helper for Exercise 14-14.5-5: the underlying `k`-linear equivalence comparing the owner dual
of a finite direct sum with the finite direct sum of the owner duals. -/
private noncomputable abbrev dfinsupp_dual_asModule_linearEquiv_fin_aux
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)] :
    ((ofModule (Π₀ i : Fin n, P i)).dual.asModule) ≃ₗ[k]
      (RestrictScalars k k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))) :=
  -- Route correction: make the owner-dual/`RestrictScalars` transport explicit first, then use
  -- the already-closed plain finite-dual equivalence.
  (owner_dual_to_linearDual (k := k) (G := G) (P := Π₀ i : Fin n, P i)).trans <|
    (linearDual_dfinsupp_linearEquiv_fin (k := k) (P := P)).trans <|
      (dfinsupp_ownerDual_restrictScalars_to_linearDual_fin
        (k := k) (G := G) (P := P)).symm

/-- Helper for Exercise 14-14.5-5: after transporting the owner dual to the plain linear dual, the
finite direct-sum dual bridge is still the canonical singleton-evaluation map. -/
private theorem dfinsupp_dual_asModule_linearEquiv_fin_apply
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)]
    (ψ : ((ofModule (Π₀ i : Fin n, P i)).dual.asModule)) (i : Fin n) (x : P i) :
    (owner_dual_to_linearDual (k := k) (G := G) (P := P i)
        (((restrictScalars_linearEquiv (k := k) (G := G)
            (Π₀ j : Fin n, ((ofModule (P j)).dual.asModule)))
            (dfinsupp_dual_asModule_linearEquiv_fin_aux
              (k := k) (G := G) (P := P) ψ)) i)) x =
      (owner_dual_to_linearDual
          (k := k) (G := G) (P := Π₀ i : Fin n, P i) ψ)
        (DFinsupp.single i x) := by
  -- Normalize the inverse finite transport first, then reduce to the already-closed plain
  -- finite-direct-sum dual evaluation formula.
  let Φ : Π₀ i : Fin n, Module.Dual k (P i) :=
    linearDual_dfinsupp_linearEquiv_fin (k := k) (P := P)
      (owner_dual_to_linearDual (k := k) (G := G) (P := Π₀ i : Fin n, P i) ψ)
  -- After rewriting the repaired inverse finite transport coordinatewise, the claim is the
  -- already-closed singleton-evaluation formula for the plain finite dual bridge.
  change
      (owner_dual_to_linearDual (k := k) (G := G) (P := P i)
        (((restrictScalars_linearEquiv (k := k) (G := G)
            (Π₀ j : Fin n, ((ofModule (P j)).dual.asModule)))
            ((dfinsupp_ownerDual_restrictScalars_to_linearDual_fin
              (k := k) (G := G) (P := P)).symm Φ)) i)) x =
        (owner_dual_to_linearDual (k := k) (G := G) (P := Π₀ i : Fin n, P i) ψ)
          (DFinsupp.single i x)
  rw [dfinsupp_ownerDual_restrictScalars_to_linearDual_fin_symm_apply
    (k := k) (G := G) (P := P) (Φ := Φ) (i := i)]
  simpa [Φ] using
    (linearDual_dfinsupp_linearEquiv_fin_apply (k := k) (P := P)
      (φ := owner_dual_to_linearDual (k := k) (G := G) (P := Π₀ i : Fin n, P i) ψ)
      (i := i) (x := x))

/-- Helper for Exercise 14-14.5-5: after forgetting the outer `RestrictScalars` wrapper, the
auxiliary finite direct-sum dual bridge is a plain `k`-linear equivalence to the DFinsupp family
of owner duals. -/
private noncomputable abbrev dfinsupp_dual_asModule_linearEquiv_fin_linear
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)] :
    ((ofModule (Π₀ i : Fin n, P i)).dual.asModule) ≃ₗ[k]
      (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) :=
  (dfinsupp_dual_asModule_linearEquiv_fin_aux (k := k) (G := G) (P := P)).trans
    (restrictScalars_linearEquiv (k := k) (G := G)
      (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)))

section
omit [Finite G]

/-- Helper for Exercise 14-14.5-5: the plain finite direct-sum dual bridge intertwines the
`G`-action on the source owner dual with the componentwise `G`-action on the target DFinsupp. -/
private theorem dfinsupp_single_groupAlgebra_smul
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k[G] (P i)]
    (a : k[G]) (i : Fin n) (x : P i) :
    a • (DFinsupp.single i x : Π₀ j : Fin n, P j) =
      DFinsupp.single i (a • x) := by
  -- The canonical `k[G]`-action on a finite direct sum is pointwise on every singleton summand.
  ext j
  by_cases h : j = i
  · subst h
    simp [DFinsupp.smul_apply]
  · simp [DFinsupp.smul_apply]

end

/-- Helper for Exercise 14-14.5-5: the plain finite direct-sum dual bridge intertwines the
`G`-action on the source owner dual with the componentwise `G`-action on the target DFinsupp. -/
private theorem dfinsupp_dual_asModule_linearEquiv_fin_linear_comm
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)]
    (g : G) (ψ : ((ofModule (Π₀ i : Fin n, P i)).dual.asModule)) :
    dfinsupp_dual_asModule_linearEquiv_fin_linear (k := k) (G := G) (P := P)
        ((MonoidAlgebra.of k G g) • ψ) =
      (MonoidAlgebra.of k G g) •
        dfinsupp_dual_asModule_linearEquiv_fin_linear (k := k) (G := G) (P := P) ψ := by
  -- Compare both sides on each summand after transporting that summand to the plain `k`-dual.
  ext i
  apply (owner_dual_to_linearDual (k := k) (G := G) (P := P i)).injective
  ext x
  -- The source-faithful route is: evaluate on the singleton basis vector, move the group action
  -- across the whole dual by the owner-dual transport, then repackage the result summandwise.
  calc
    (owner_dual_to_linearDual (k := k) (G := G) (P := P i)
        (dfinsupp_dual_asModule_linearEquiv_fin_linear
          (k := k) (G := G) (P := P) ((MonoidAlgebra.of k G g) • ψ) i)) x
        =
      (owner_dual_to_linearDual (k := k) (G := G) (P := Π₀ j : Fin n, P j) ψ)
        ((MonoidAlgebra.of k G g⁻¹) • (DFinsupp.single i x : Π₀ j : Fin n, P j)) := by
          rw [← owner_dual_to_linearDual_smul_apply
            (k := k) (G := G) (P := Π₀ j : Fin n, P j)
            (g := g⁻¹) (ψ := ψ) (x := DFinsupp.single i x)]
          simpa [dfinsupp_dual_asModule_linearEquiv_fin_linear] using
            (dfinsupp_dual_asModule_linearEquiv_fin_apply
              (k := k) (G := G) (P := P) (ψ := (MonoidAlgebra.of k G g) • ψ)
              (i := i) (x := x))
    _ =
      (owner_dual_to_linearDual (k := k) (G := G) (P := Π₀ j : Fin n, P j) ψ)
        (DFinsupp.single i ((MonoidAlgebra.of k G g⁻¹) • x)) := by
          rw [dfinsupp_single_groupAlgebra_smul
            (k := k) (P := P) (a := MonoidAlgebra.of k G g⁻¹) (i := i) (x := x)]
    _ =
      (owner_dual_to_linearDual (k := k) (G := G) (P := P i)
        (dfinsupp_dual_asModule_linearEquiv_fin_linear
          (k := k) (G := G) (P := P) ψ i))
        ((MonoidAlgebra.of k G g⁻¹) • x) := by
          symm
          simpa [dfinsupp_dual_asModule_linearEquiv_fin_linear] using
            (dfinsupp_dual_asModule_linearEquiv_fin_apply
              (k := k) (G := G) (P := P) (ψ := ψ)
              (i := i) (x := (MonoidAlgebra.of k G g⁻¹) • x))
    _ =
      (owner_dual_to_linearDual (k := k) (G := G) (P := P i)
        ((MonoidAlgebra.of k G g) •
          dfinsupp_dual_asModule_linearEquiv_fin_linear
            (k := k) (G := G) (P := P) ψ i)) x := by
          symm
          simpa [MonoidAlgebra.of] using owner_dual_to_linearDual_smul_apply
            (k := k) (G := G) (P := P i) (g := g⁻¹)
            (ψ := dfinsupp_dual_asModule_linearEquiv_fin_linear
              (k := k) (G := G) (P := P) ψ i)
            (x := x)
    _ =
      (owner_dual_to_linearDual (k := k) (G := G) (P := P i)
        (((MonoidAlgebra.of k G g) •
          dfinsupp_dual_asModule_linearEquiv_fin_linear
            (k := k) (G := G) (P := P) ψ) i)) x := by
          have hs :
              (((MonoidAlgebra.of k G g) •
                dfinsupp_dual_asModule_linearEquiv_fin_linear
                  (k := k) (G := G) (P := P) ψ) i) =
                (MonoidAlgebra.of k G g) •
                  dfinsupp_dual_asModule_linearEquiv_fin_linear
                    (k := k) (G := G) (P := P) ψ i := by
            rfl
          rw [hs]

/-- Helper for Exercise 14-14.5-5: the inverse plain finite direct-sum dual bridge also
intertwines the `G`-action componentwise. -/
private theorem dfinsupp_dual_asModule_linearEquiv_fin_linear_symm_comm
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)]
    (g : G) (Φ : Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) :
    (dfinsupp_dual_asModule_linearEquiv_fin_linear
      (k := k) (G := G) (P := P)).symm
        ((MonoidAlgebra.of k G g) • Φ) =
      (MonoidAlgebra.of k G g) •
        (dfinsupp_dual_asModule_linearEquiv_fin_linear
          (k := k) (G := G) (P := P)).symm Φ := by
  let e := dfinsupp_dual_asModule_linearEquiv_fin_linear (k := k) (G := G) (P := P)
  apply e.injective
  -- Push the inverse statement through the forward bridge and cancel with `apply_symm_apply`.
  calc
    e (e.symm ((MonoidAlgebra.of k G g) • Φ)) = (MonoidAlgebra.of k G g) • Φ := by
      simp
    _ = (MonoidAlgebra.of k G g) • e (e.symm Φ) := by
      simp
    _ = e ((MonoidAlgebra.of k G g) • e.symm Φ) := by
      rw [dfinsupp_dual_asModule_linearEquiv_fin_linear_comm
        (k := k) (G := G) (P := P) (g := g) (ψ := e.symm Φ)]

/-- Helper for Exercise 14-14.5-5: a `k`-linear equivalence between `k[G]`-modules upgrades to a
`k[G]`-linear equivalence once both directions commute with the basis group elements. -/
private noncomputable def linearEquiv_to_groupAlgebraLinearEquiv_of_of_comm
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module k[G] M] [Module k[G] N]
    [IsScalarTower k k[G] M] [IsScalarTower k k[G] N]
    (e : M ≃ₗ[k] N)
    (he : ∀ g : G, ∀ x : M,
      e ((MonoidAlgebra.of k G g) • x) = (MonoidAlgebra.of k G g) • e x)
    (he_symm : ∀ g : G, ∀ y : N,
      e.symm ((MonoidAlgebra.of k G g) • y) = (MonoidAlgebra.of k G g) • e.symm y) :
    M ≃ₗ[k[G]] N := by
  let f : M →ₗ[k[G]] N :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro a x
        -- Extend the basis-element commutation from `MonoidAlgebra.of` to all of `k[G]`.
        refine MonoidAlgebra.induction_on
          (p := fun b : k[G] => e (b • x) = b • e x) a ?_ ?_ ?_
        · intro g
          exact he g x
        · intro a b ha hb
          simp [add_smul, ha, hb]
        · intro c a ha
          simpa [smul_smul] using congrArg (fun z : N => c • z) ha }
  let g : N →ₗ[k[G]] M :=
    { toFun := e.symm
      map_add' := e.symm.map_add
      map_smul' := by
        intro a y
        -- The same scalar induction packages the inverse map.
        refine MonoidAlgebra.induction_on
          (p := fun b : k[G] => e.symm (b • y) = b • e.symm y) a ?_ ?_ ?_
        · intro h
          exact he_symm h y
        · intro a b ha hb
          simp [add_smul, ha, hb]
        · intro c a ha
          simpa [smul_smul] using congrArg (fun z : M => c • z) ha }
  refine LinearEquiv.ofLinear f g ?_ ?_
  · ext y
    -- The forward-then-backward composite is the original `k`-linear equivalence cancellation.
    exact e.apply_symm_apply y
  · ext x
    -- The reverse composite is the same cancellation on the source.
    exact e.symm_apply_apply x

/-- Helper for Exercise 14-14.5-5: the owner dual of a finite direct sum is the finite direct sum
of the owner duals. -/
private noncomputable def dfinsupp_dual_asModule_linearEquiv_fin
    {n : ℕ} {P : Fin n → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]
    [∀ i, Module k[G] (P i)] [∀ i, IsScalarTower k k[G] (P i)] :
    ((ofModule (Π₀ i : Fin n, P i)).dual.asModule) ≃ₗ[k[G]]
      (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) := by
  -- Package the already-verified `k`-linear bridge by reusing the forward and inverse
  -- basis-element commutation lemmas.
  let M := ((ofModule (Π₀ i : Fin n, P i)).dual.asModule)
  let N := (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule))
  let hMk : Module k ((ofModule (Π₀ i : Fin n, P i)).dual.asModule) :=
    representation_asModuleModule
      (ρ := Representation.dual (ofModule (Π₀ i : Fin n, P i)))
  let hMst : IsScalarTower k k[G] ((ofModule (Π₀ i : Fin n, P i)).dual.asModule) :=
    representation_asModule_isScalarTower
      (ρ := Representation.dual (ofModule (Π₀ i : Fin n, P i)))
  let hMkg : Module k[G] ((ofModule (Π₀ i : Fin n, P i)).dual.asModule) := by
    infer_instance
  let hNk : Module k (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) :=
    dfinsupp_ownerDual_module (k := k) (G := G) (P := P)
  let hNkg : Module k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) :=
    dfinsupp_ownerDual_groupAlgebra_module (k := k) (G := G) (P := P)
  let hNst : IsScalarTower k k[G] (Π₀ i : Fin n, ((ofModule (P i)).dual.asModule)) :=
    dfinsupp_ownerDual_isScalarTower (k := k) (G := G) (P := P)
  -- Route correction: keep the finite direct-sum proof at the already-closed `k`-linear level
  -- and upgrade it only here, instead of reopening the DFinsupp transport algebra.
  change M ≃ₗ[k[G]] N
  exact
    @linearEquiv_to_groupAlgebraLinearEquiv_of_of_comm
      k _ G _ M N
      (by infer_instance) (by infer_instance)
      hMk hNk hMkg hNkg hMst hNst
      (e := dfinsupp_dual_asModule_linearEquiv_fin_linear (k := k) (G := G) (P := P))
      (he := dfinsupp_dual_asModule_linearEquiv_fin_linear_comm
        (k := k) (G := G) (P := P))
      (he_symm := dfinsupp_dual_asModule_linearEquiv_fin_linear_symm_comm
        (k := k) (G := G) (P := P))

/-- Helper for Exercise 14-14.5-5: dualizing a finite direct-sum decomposition gives the
orientation needed for the final envelope comparison. -/
private noncomputable abbrev dual_dfinsupp_congr_fin
    {M : Type*} [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    {n : ℕ} {S : Fin n → Type*}
    [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module k[G] (S i)] [∀ i, IsScalarTower k k[G] (S i)]
    (e : M ≃ₗ[k[G]] Π₀ i : Fin n, S i) :
    (Π₀ i : Fin n, ((ofModule (S i)).dual.asModule)) ≃ₗ[k[G]] ((ofModule M).dual.asModule) :=
  -- Compose the finite direct-sum dual bridge with the already-closed owner-dual congruence.
  (dfinsupp_dual_asModule_linearEquiv_fin (k := k) (G := G) (P := S)).symm.trans
    (Classical.choice (dual_asModule_congr (k := k) (G := G) e))

section
omit [Finite G]

/-- Helper for Exercise 14-14.5-5: projective envelopes landing in the same module remain
isomorphic after lifting all three modules into a common universe. -/
private theorem isProjectiveEnvelope_unique_across_universes
    {M : Type w} [AddCommGroup M] [Module k[G] M]
    {P : Type x} [AddCommGroup P] [Module k[G] P]
    {Q : Type y} [AddCommGroup Q] [Module k[G] Q]
    {f : P →ₗ[k[G]] M} {g : Q →ₗ[k[G]] M}
    (hf : f.IsProjectiveEnvelope) (hg : g.IsProjectiveEnvelope) :
    Nonempty (P ≃ₗ[k[G]] Q) := by
  let PU : Type (max x (max y w)) := ULift.{max x (max y w), x} P
  let QU : Type (max x (max y w)) := ULift.{max x (max y w), y} Q
  let MU : Type (max x (max y w)) := ULift.{max x (max y w), w} M
  let eP : P ≃ₗ[k[G]] PU := ULift.moduleEquiv.symm
  let eQ : Q ≃ₗ[k[G]] QU := ULift.moduleEquiv.symm
  let eM : M ≃ₗ[k[G]] MU := ULift.moduleEquiv.symm
  let fU : PU →ₗ[k[G]] MU := (eM.toLinearMap.comp f).comp eP.symm.toLinearMap
  let gU : QU →ₗ[k[G]] MU := (eM.toLinearMap.comp g).comp eQ.symm.toLinearMap
  have hfU : fU.IsProjectiveEnvelope := by
    -- Conjugate the first envelope into the lifted common universe.
    simpa [fU, eP, eM] using
      (LinearMap.isProjectiveEnvelope_iff_conj (R := k[G]) eP eM).2 hf
  have hgU : gU.IsProjectiveEnvelope := by
    -- Conjugate the second envelope into the same lifted universe.
    simpa [gU, eQ, eM] using
      (LinearMap.isProjectiveEnvelope_iff_conj (R := k[G]) eQ eM).2 hg
  obtain ⟨eU, _⟩ := LinearMap.isProjectiveEnvelope_unique hfU hgU
  -- Descend the lifted source isomorphism back to the original modules.
  exact ⟨(eP.trans eU).trans eQ.symm⟩

end

section
omit [Finite G] [Module k E] [IsScalarTower k k[G] E]

/-- Helper for Exercise 14-14.5-5: assembling projective envelopes of simple summands and then
transporting only the codomain along a semisimple decomposition gives a projective envelope of the
whole module. -/
private theorem semisimple_dfinsupp_projectiveEnvelope_of_simple_family
    {n : ℕ} {S : Fin n → Type w}
    [∀ i, AddCommGroup (S i)] [∀ i, Module k[G] (S i)]
    (e : E ≃ₗ[k[G]] Π₀ i : Fin n, S i)
    {P' : Fin n → Type w}
    [∀ i, AddCommGroup (P' i)] [∀ i, Module k[G] (P' i)]
    (f : ∀ i, P' i →ₗ[k[G]] S i)
    (hf : ∀ i, (f i).IsProjectiveEnvelope) :
    (e.symm.toLinearMap.comp (DirectSum.lmap fun i ↦ f i)).IsProjectiveEnvelope := by
  let fSigma : (Π₀ i : Fin n, P' i) →ₗ[k[G]] (Π₀ i : Fin n, S i) :=
    DirectSum.lmap fun i ↦ f i
  have hfSigma : fSigma.IsProjectiveEnvelope := by
    -- First assemble the projective envelopes summandwise on the semisimple decomposition.
    simpa [fSigma] using
      DirectSum.lmap_isProjectiveEnvelope (R := k[G]) (fun i ↦ f i) hf
  -- Then conjugate only the codomain back from the DFinsupp decomposition to `E`.
  simpa [fSigma] using
    (LinearMap.isProjectiveEnvelope_iff_conj
      (R := k[G]) (LinearEquiv.refl k[G] (Π₀ i : Fin n, P' i)) e.symm).2 hfSigma

end

/-- Helper for Exercise 14-14.5-5: the dual of a finite DFinsupp decomposition is transported by
reusing the already-closed owner-dual direct-sum bridge, with no source-side transport. -/
private noncomputable abbrev dual_dfinsupp_congr_fin_restrictScalars_owner
    [IsScalarTower k k[G] E]
    {n : ℕ} {S : Fin n → Type w}
    [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module k[G] (S i)] [∀ i, IsScalarTower k k[G] (S i)]
    (e : E ≃ₗ[k[G]] Π₀ i : Fin n, S i) :
    (Π₀ i : Fin n, ((ofModule (S i)).dual.asModule)) ≃ₗ[k[G]] ((ofModule E).dual.asModule) :=
  -- Route correction: keep the summandwise owner-dual source unchanged and transport only the
  -- codomain decomposition of `E`.
  dual_dfinsupp_congr_fin (k := k) (G := G) e

/-- Helper for Exercise 14-14.5-5: assembling the transposes of injective envelopes of the simple
summands already gives a projective envelope on the owner-dual DFinsupp types, before any codomain
transport. -/
private theorem owner_dual_dfinsupp_lmap_isProjectiveEnvelope_typed
    {n : ℕ} {S : Fin n → Type w}
    [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module k[G] (S i)] [∀ i, IsScalarTower k k[G] (S i)]
    [∀ i, FiniteDimensional k (S i)] [∀ i, IsSimpleModule k[G] (S i)]
    {P' : Fin n → Type w}
    [∀ i, AddCommGroup (P' i)] [∀ i, Module k (P' i)]
    [∀ i, Module k[G] (P' i)] [∀ i, IsScalarTower k k[G] (P' i)]
    [∀ i, FiniteDimensional k (P' i)]
    (j : ∀ i, S i →ₗ[k[G]] P' i)
    (hj : ∀ i, (j i).IsInjectiveEnvelope) :
    (DirectSum.lmap fun i ↦ owner_dual_transpose (k := k) (G := G) (j i)).IsProjectiveEnvelope := by
  let Pdual : Fin n → Type (max u w) := fun i ↦ ((ofModule (P' i)).dual.asModule)
  let Sdual : Fin n → Type (max u w) := fun i ↦ ((ofModule (S i)).dual.asModule)
  letI : ∀ i, Module k[G] ((ofModule (P' i)).dual.asModule) := fun i ↦
    Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule (P' i)).dual)
  letI : ∀ i, Module k[G] ((ofModule (S i)).dual.asModule) := fun i ↦
    Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule (S i)).dual)
  letI : ∀ i, AddCommGroup (Pdual i) := fun i ↦ by
    dsimp [Pdual]
    infer_instance
  letI : ∀ i, AddCommGroup (Sdual i) := fun i ↦ by
    dsimp [Sdual]
    infer_instance
  letI : ∀ i, Module k[G] (Pdual i) := fun i ↦
    Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule (P' i)).dual)
  letI : ∀ i, Module k[G] (Sdual i) := fun i ↦
    Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule (S i)).dual)
  letI : Module k[G] (Π₀ i : Fin n, Pdual i) := by
    dsimp [Pdual]
    exact dfinsupp_ownerDual_groupAlgebra_module (k := k) (G := G) (P := P')
  letI : Module k[G] (Π₀ i : Fin n, Sdual i) := by
    dsimp [Sdual]
    exact dfinsupp_ownerDual_groupAlgebra_module (k := k) (G := G) (P := S)
  let gSigma :
      (Π₀ i : Fin n, Pdual i) →ₗ[k[G]] (Π₀ i : Fin n, Sdual i) :=
    DirectSum.lmap fun i ↦ owner_dual_transpose (k := k) (G := G) (j i)
  have hpack :
      ∀ i, ((owner_dual_transpose (k := k) (G := G) (j i) :
        Pdual i →ₗ[k[G]] Sdual i)).IsProjectiveEnvelope := by
    intro i
    -- Reinterpret the simple-case transpose envelope on the frozen owner-dual summand types.
    simpa [Pdual, Sdual] using
      (transpose_simple_injectiveEnvelope_isProjectiveEnvelope
        (k := k) (G := G) (hi := hj i))
  have hgSigma : gSigma.IsProjectiveEnvelope := by
    -- Assemble the simple-summand transpose envelopes before any semisimple codomain transport.
    simpa [gSigma] using
      (@DirectSum.lmap_isProjectiveEnvelope
        (k[G]) _ (Fin n) inferInstance Pdual Sdual
        (fun i ↦ by
          dsimp [Pdual]
          infer_instance)
        (fun i ↦
          Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule (P' i)).dual))
        (fun i ↦ by
          dsimp [Sdual]
          infer_instance)
        (fun i ↦
          Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule (S i)).dual))
        (fun i ↦
          (owner_dual_transpose (k := k) (G := G) (j i) :
            Pdual i →ₗ[k[G]] Sdual i))
        hpack)
  simpa [gSigma, Pdual, Sdual] using hgSigma

section
omit [Finite G] [Module k E] [IsScalarTower k k[G] E]

/-- Helper for Exercise 14-14.5-5: once the owner-dual DFinsupp envelope is frozen, transporting
only the codomain along the semisimple decomposition preserves the projective-envelope property. -/
private theorem owner_dual_codomain_conj_isProjectiveEnvelope_typed
    {E' : Type w} [AddCommGroup E'] [Module k[G] E']
    {n : ℕ} {S : Fin n → Type w}
    [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module k[G] (S i)] [∀ i, IsScalarTower k k[G] (S i)]
    {P' : Fin n → Type w}
    [∀ i, AddCommGroup (P' i)] [∀ i, Module k (P' i)]
    [∀ i, Module k[G] (P' i)] [∀ i, IsScalarTower k k[G] (P' i)]
    (gSigma :
      (Π₀ i : Fin n, ((ofModule (P' i)).dual.asModule)) →ₗ[k[G]]
        (Π₀ i : Fin n, ((ofModule (S i)).dual.asModule)))
    (hgSigma : gSigma.IsProjectiveEnvelope)
    (eDualE :
      (Π₀ i : Fin n, ((ofModule (S i)).dual.asModule)) ≃ₗ[k[G]]
        ((ofModule E').dual.asModule)) :
    (eDualE.toLinearMap.comp gSigma).IsProjectiveEnvelope := by
  let Pdual : Fin n → Type (max u w) := fun i ↦ ((ofModule (P' i)).dual.asModule)
  let Edual : Type (max u w) := ((ofModule E').dual.asModule)
  letI : ∀ i, Module k[G] ((ofModule (P' i)).dual.asModule) := fun i ↦
    Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule (P' i)).dual)
  letI : Module k[G] ((ofModule E').dual.asModule) :=
    Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule E').dual)
  letI : ∀ i, AddCommGroup (Pdual i) := fun i ↦ by
    dsimp [Pdual]
    infer_instance
  letI : ∀ i, Module k[G] (Pdual i) := fun i ↦
    Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule (P' i)).dual)
  letI : Module k[G] (Π₀ i : Fin n, Pdual i) := by
    dsimp [Pdual]
    exact dfinsupp_ownerDual_groupAlgebra_module (k := k) (G := G) (P := P')
  letI : Module k[G] Edual := by
    dsimp [Edual]
    exact Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule E').dual)
  let eDualE' :
      (Π₀ i : Fin n, ((ofModule (S i)).dual.asModule)) ≃ₗ[k[G]] Edual := by
    simpa [Edual] using eDualE
  -- Only the codomain changes here; the source stays frozen as the assembled owner-dual DFinsupp.
  simpa using
    ((@LinearMap.isProjectiveEnvelope_iff_conj
      (k[G]) _
      (Π₀ i : Fin n, Pdual i) (Π₀ i : Fin n, Pdual i)
      (Π₀ i : Fin n, ((ofModule (S i)).dual.asModule)) Edual
      (by infer_instance)
      (by
        dsimp [Pdual]
        exact dfinsupp_ownerDual_groupAlgebra_module (k := k) (G := G) (P := P'))
      (by infer_instance)
      (by
        dsimp [Pdual]
        exact dfinsupp_ownerDual_groupAlgebra_module (k := k) (G := G) (P := P'))
      (by infer_instance)
      (by
        exact dfinsupp_ownerDual_groupAlgebra_module (k := k) (G := G) (P := S))
      (by
        dsimp [Edual]
        infer_instance)
      (by
        dsimp [Edual]
        exact Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule E').dual))
      (LinearEquiv.refl k[G] (Π₀ i : Fin n, Pdual i))
      eDualE').2 hgSigma)

end

section
omit [IsScalarTower k k[G] E]

/-- Helper for Exercise 14-14.5-5: assembling the transposes of injective envelopes of the simple
summands and transporting only the codomain along the semisimple decomposition gives a projective
envelope of the dual module. -/
private theorem directSum_owner_dual_projectiveEnvelope_of_simple_family
    [IsScalarTower k k[G] E]
    {n : ℕ} {S : Fin n → Type w}
    [∀ i, AddCommGroup (S i)] [∀ i, Module k (S i)]
    [∀ i, Module k[G] (S i)] [∀ i, IsScalarTower k k[G] (S i)]
    [∀ i, FiniteDimensional k (S i)] [∀ i, IsSimpleModule k[G] (S i)]
    (e : E ≃ₗ[k[G]] Π₀ i : Fin n, S i)
    {P' : Fin n → Type w}
    [∀ i, AddCommGroup (P' i)] [∀ i, Module k (P' i)]
    [∀ i, Module k[G] (P' i)] [∀ i, IsScalarTower k k[G] (P' i)]
    [∀ i, FiniteDimensional k (P' i)]
    (j : ∀ i, S i →ₗ[k[G]] P' i)
    (hj : ∀ i, (j i).IsInjectiveEnvelope) :
    (((dual_dfinsupp_congr_fin_restrictScalars_owner
        (k := k) (G := G) (E := E) e).toLinearMap).comp
      (DirectSum.lmap
        fun i ↦ owner_dual_transpose (k := k) (G := G) (j i))).IsProjectiveEnvelope := by
  let gSigma :
      (Π₀ i : Fin n, ((ofModule (P' i)).dual.asModule)) →ₗ[k[G]]
        (Π₀ i : Fin n, ((ofModule (S i)).dual.asModule)) :=
    DirectSum.lmap fun i ↦ owner_dual_transpose (k := k) (G := G) (j i)
  have hgSigma : gSigma.IsProjectiveEnvelope := by
    -- First package the summandwise transpose envelopes on the exact owner-dual DFinsupp source.
    simpa [gSigma] using
      owner_dual_dfinsupp_lmap_isProjectiveEnvelope_typed
        (k := k) (G := G) (S := S) (P' := P') j hj
  let eDualE :
      (Π₀ i : Fin n, ((ofModule (S i)).dual.asModule)) ≃ₗ[k[G]]
        ((ofModule E).dual.asModule) :=
    dual_dfinsupp_congr_fin_restrictScalars_owner (k := k) (G := G) (E := E) e
  -- Then conjugate only the codomain back from the semisimple decomposition of `E`.
  simpa [gSigma, eDualE] using
    owner_dual_codomain_conj_isProjectiveEnvelope_typed
      (k := k) (G := G) (E' := E) (gSigma := gSigma) hgSigma eDualE

end

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's comparison, for a finite group `G`, between projective envelopes of a
--   semisimple `k[G]`-module and of its contragredient dual.
-- * core/canonical: `Representation.dual`, viewed on the module side through `asModule`, together
--   with `LinearMap.IsProjectiveEnvelope` and the `ModuleCat`-level existence surface
--   `exists_isProjectiveEnvelope`.
-- * bridge/view: pass from a `k[G]`-module `M` directly to `((ofModule M).dual.asModule)`, the
--   canonical module-side view of the dual representation, without introducing a parallel owner.

-- Proof sketch: write the semisimple module `E` as a finite direct sum of simple modules, use
-- Exercise `14-14.5-4` to identify the dual of a projective envelope of each simple summand with
-- the projective envelope of its dual, then reassemble the summands with
-- `DirectSum.lmap_isProjectiveEnvelope` and finish by uniqueness of projective envelopes.
section

/-- Exercise 14-14.5-5: for a finite group `G`, if `E` is a semisimple finite-dimensional
`k[G]`-module and
`f : P →ₗ[k[G]] E` is a projective envelope, then any projective envelope of the contragredient
dual of `E` has source isomorphic to the contragredient dual of `P`. -/
theorem projectiveEnvelope_toDual_linearEquiv_of_semisimple
    {f : P →ₗ[k[G]] E} [Module k P] [IsScalarTower k k[G] P]
    [FiniteDimensional k E] [Module.Finite k[G] E] [IsSemisimpleModule k[G] E]
    (hf : f.IsProjectiveEnvelope)
    {g : Q →ₗ[k[G]] ((ofModule E).dual.asModule)}
    (hg : g.IsProjectiveEnvelope) :
    Nonempty (Q ≃ₗ[k[G]] ((ofModule P).dual.asModule)) := by
  classical
  obtain ⟨n, S, e, hSsimple⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (k[G]) E
  choose Ps fs hfs using
    fun i : Fin n ↦ exists_isProjectiveEnvelope (ModuleCat.of k[G] (S i))
  letI : ∀ i, Module k ↥(S i) := fun i ↦ by
    infer_instance
  letI : ∀ i, IsScalarTower k k[G] ↥(S i) := fun i ↦ by
    infer_instance
  letI : ∀ i, Module k ↥(Ps i) := fun i ↦
    Module.compHom ↥(Ps i) (algebraMap k k[G])
  letI : ∀ i, IsScalarTower k k[G] ↥(Ps i) := fun i ↦
    IsScalarTower.of_compHom k k[G] ↥(Ps i)
  letI : ∀ i, FiniteDimensional k ↥(S i) := fun i ↦ by
    let N' : Submodule k E := Submodule.restrictScalars k (S i)
    letI : FiniteDimensional k N' :=
      FiniteDimensional.of_injective N'.subtype (Submodule.injective_subtype N')
    simpa using (inferInstance : FiniteDimensional k N')
  have hfAssembled :
      (e.symm.toLinearMap.comp (DirectSum.lmap fun i ↦ (fs i).hom)).IsProjectiveEnvelope := by
    -- Assemble the chosen projective envelopes on the simple summands of `E`.
    simpa using
      semisimple_dfinsupp_projectiveEnvelope_of_simple_family
        (k := k) (G := G) (E := E) (e := e)
        (f := fun i ↦ (fs i).hom) (hf := fun i ↦ hfs i)
  obtain ⟨ePsum⟩ :=
    isProjectiveEnvelope_unique_across_universes
      (k := k) (G := G) (hf := hf) (hg := hfAssembled)
  choose j hj using
    fun i : Fin n ↦
      exists_isInjectiveEnvelope_of_isProjectiveEnvelope_of_simple
        (k := k) (G := G) (hS := hSsimple i) (hf := hfs i)
  letI : ∀ i, Module.Finite k[G] ↥(Ps i) := fun i ↦
    projectiveEnvelope_simple_source_finite
      (k := k) (G := G) (hS := hSsimple i) (hf := hfs i)
  letI : ∀ i, Module.Finite k ↥(Ps i) := fun i ↦
    groupAlgebra_moduleFinite_restrictScalars
      (k := k) (G := G) (M := ↥(Ps i))
      (hM := inferInstance)
  letI : ∀ i, FiniteDimensional k ↥(Ps i) := fun i ↦ by
    infer_instance
  let Edual := ((ofModule E).dual.asModule)
  letI : Module k[G] Edual :=
    Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule E).dual)
  let gDual : Q →ₗ[k[G]] Edual := g
  let gAssembled :
      (Π₀ i : Fin n, ((ofModule ↥(Ps i)).dual.asModule)) →ₗ[k[G]]
        Edual :=
    ((dual_dfinsupp_congr_fin_restrictScalars_owner
        (k := k) (G := G) (E := E) e).toLinearMap).comp
      (DirectSum.lmap fun i ↦ owner_dual_transpose (k := k) (G := G) (j i))
  have hgAssembled : gAssembled.IsProjectiveEnvelope := by
    -- Reassemble the simple-case dual envelopes and transport only the codomain back to `E`.
    simpa using
      directSum_owner_dual_projectiveEnvelope_of_simple_family
        (k := k) (G := G) (E := E) (e := e) (P' := fun i ↦ ↥(Ps i)) (j := j) (hj := hj)
  have hQsum :
      Nonempty (Q ≃ₗ[k[G]] (Π₀ i : Fin n, ((ofModule ↥(Ps i)).dual.asModule))) := by
    have hgDual : gDual.IsProjectiveEnvelope := by
      simpa [gDual, Edual] using hg
    let gAssembled' :
        (Π₀ i : Fin n, ((ofModule ↥(Ps i)).dual.asModule)) →ₗ[k[G]]
          ((ofModule E).dual.asModule) :=
      gAssembled
    exact
      @isProjectiveEnvelope_unique_across_universes
        k _ G _
        ((ofModule E).dual.asModule)
        (by infer_instance)
        (Representation.instModuleMonoidAlgebraAsModule (ρ := (ofModule E).dual))
        Q
        (by infer_instance)
        (by infer_instance)
        (Π₀ i : Fin n, ((ofModule ↥(Ps i)).dual.asModule))
        (by infer_instance)
        (by infer_instance)
        gDual gAssembled' hgDual (by simpa [gAssembled'] using hgAssembled)
  obtain ⟨eQsum⟩ := hQsum
  -- The two uniqueness comparisons reduce the result to the canonical dual of the assembled
  -- source decomposition.
  exact ⟨eQsum.trans (dual_dfinsupp_congr_fin (k := k) (G := G) (M := P) ePsum)⟩

end

-- Proof sketch: choose a projective envelope of the dual module by Proposition `14-14.3-1`, then
-- apply `projectiveEnvelope_toDual_linearEquiv_of_semisimple` to that chosen
-- envelope.
section

/-- For a finite group `G`, a projective envelope of the contragredient dual exists with source
isomorphic to the contragredient dual of the chosen projective envelope. -/
theorem exists_projectiveEnvelope_toDual_linearEquiv_of_semisimple
    {f : P →ₗ[k[G]] E} [Module k P] [IsScalarTower k k[G] P]
    [FiniteDimensional k E] [Module.Finite k[G] E] [IsSemisimpleModule k[G] E]
    (hf : f.IsProjectiveEnvelope) :
    ∃ Q : ModuleCat.{max u w} k[G],
      ∃ g : Q →ₗ[k[G]] ((ofModule E).dual.asModule),
        g.IsProjectiveEnvelope ∧
          Nonempty (Q ≃ₗ[k[G]] ((ofModule P).dual.asModule)) := by
  let Edual : ModuleCat.{max u w} k[G] :=
    @ModuleCat.of (k[G]) _ ((ofModule E).dual.asModule) _
      (inferInstance : Module k[G] ((ofModule E).dual.asModule))
  obtain ⟨Q', g', hg'⟩ :=
    exists_isProjectiveEnvelope (k := k) (G := G) Edual
  -- Choose a projective envelope of the dual module and compare it to the dual of the chosen
  -- envelope of `E`.
  refine ⟨Q', g'.hom, hg', ?_⟩
  exact projectiveEnvelope_toDual_linearEquiv_of_semisimple
    (k := k) (G := G) (P := P) (Q := Q') hf hg'

end

end
