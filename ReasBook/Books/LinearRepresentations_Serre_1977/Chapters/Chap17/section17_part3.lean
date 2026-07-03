import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_17_17_3_2 (from Chap17) -/
noncomputable section

universe u w x y

namespace Representation

section ElementaryDirectProductLifting

open MonoidHom

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {p : ℕ}
variable {C : Type u} [Group C]
variable {P : Type w} [Group P]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance : Module A V :=
  Module.compHom V (algebraMap A k)
local instance : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's elementary direct-product lifting remark, whose mathematically active
--   content is that a trivial `P`-action lets one inflate a lift of the left-factor
--   `k[C]`-representation back to `C × P`.
-- * core/canonical: `LinearMap.IsResidueFieldReduction` from Chapter 14 is the reduction owner.
-- * bridge/view: `IsResidueFieldLift` from Chapter 15 and the companion theorem
--   `directProduct_exists_residueFieldLift_of_rightFactor_trivial`, which is the public owner
--   statement for this item: it keeps only the mathematically active hypotheses
--   `¬ p ∣ Nat.card C` and triviality of the right-factor action, then extends the lifted
--   left-factor representation back along `C × P → C`.

omit [FiniteDimensional k V] in
/-- Helper for Remark 17-17.3-2: a trivial right-factor action identifies the original product
representation with the inflation of its restriction to the left factor. -/
private theorem eq_comp_inl_comp_fst
    (ρ : Representation k (C × P) V) (hTriv : IsTrivial (ρ.comp (inr C P)))
    : ρ = (ρ.comp (inl C P)).comp (fst C P) := by
  -- Factor `(c, p')` through the two product inclusions and kill the trivial right action.
  letI : IsTrivial (ρ.comp (inr C P)) := hTriv
  ext g x
  rcases g with ⟨c, p'⟩
  calc
    ρ (c, p') x = ρ ((c, 1) * (1, p')) x := by simp
    _ = (ρ (c, 1) * ρ (1, p')) x := by rw [map_mul]
    _ = ρ (c, 1) (ρ (1, p') x) := rfl
    _ = ρ (c, 1) x := by
      have hp' : ρ (1, p') x = x := by
        change ((ρ.comp (inr C P)) p') x = x
        exact isTrivial_apply (ρ.comp (inr C P)) p' x
      simp [hp']
    _ = ((ρ.comp (inl C P)).comp (fst C P)) (c, p') x := rfl

omit [FiniteDimensional k V] in
/-- Helper for Remark 17-17.3-2: once the restriction of `ρ` to the left factor `C` has a
residue-field lift, the same lift inflates along `fst C P : C × P →* C` to a lift of `ρ`
whenever the right factor acts trivially. -/
theorem isResidueFieldLift_of_rightFactor_trivial
    (ρ : Representation k (C × P) V) (hTriv : IsTrivial (ρ.comp (inr C P)))
    {W : Type y} [AddCommGroup W] [Module A W] [Module.Free A W] [Module.Finite A W]
    (ρA : Representation A C W) (red : W →ₗ[A] V)
    (hLift : IsResidueFieldLift (ρ.comp (inl C P)) ρA red) :
    IsResidueFieldLift ρ (ρA.comp (fst C P)) red := by
  -- First inflate the left-factor lift along the product projection.
  have hInflated :
      IsResidueFieldLift ((ρ.comp (inl C P)).comp (fst C P)) (ρA.comp (fst C P)) red :=
    isResidueFieldLift_comp hLift (fst C P)
  -- Then rewrite the source representation using the triviality of the `P`-action.
  simpa [← eq_comp_inl_comp_fst ρ hTriv] using hInflated

-- Proof sketch: because the right factor acts trivially, the whole representation is obtained by
-- inflating its restriction along `C ↪ C × P`. Since `|C|` is prime to `p`, Chapter 15 already
-- provides a canonical henselian-local lift of that restricted `C`-representation through
-- `exists_residueFieldLift`; composing the resulting representation with `C × P → C` yields the
-- desired lift of the original representation. In the source text this is applied to an
-- irreducible/simple module, but irreducibility plays no role in the lifting construction.
/-- Remark 17-17.3-2: let `k = IsLocalRing.ResidueField A` have characteristic `p`. If a
finite-dimensional representation of the elementary direct product `C × P` over `k` has trivial
`P`-action and `p ∤ |C|`, then it admits a free finitely generated lift over `A`. This keeps the
source semantics while exposing only the mathematically active hypotheses on the theorem surface;
the simple-module reading is commentary rather than extra public data. -/
theorem directProduct_exists_residueFieldLift_of_rightFactor_trivial
    [HenselianLocalRing A] [CharP k p] (hC : ¬ p ∣ Nat.card C) (ρ : Representation k (C × P) V)
    (hTriv : IsTrivial (ρ.comp (inr C P))) :
    ∃ (W : Type y) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A (C × P) W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  letI : Finite C := by
    refine Nat.finite_of_card_ne_zero ?_
    intro hcard
    exact hC <| hcard.symm ▸ dvd_zero p
  have hLeftLift :
      ∃ (W : Type y) (_ : AddCommGroup W) (_ : Module A W)
        (_ : Module.Free A W) (_ : Module.Finite A W)
        (ρA : Representation A C W)
        (red : W →ₗ[A] V),
          IsResidueFieldLift (ρ.comp (inl C P)) ρA red := by
    simpa using exists_residueFieldLift hC (ρ.comp (inl C P))
  rcases hLeftLift with ⟨W, _instWAdd, _instWMod, _instWFree, _instWFinite, ρA, red, hLift⟩
  -- Once the left-factor lift exists, inflate it back to `C × P`.
  refine ⟨W, _instWAdd, _instWMod, _instWFree, _instWFinite, ρA.comp (fst C P), red, ?_⟩
  exact isResidueFieldLift_of_rightFactor_trivial ρ hTriv ρA red hLift

end ElementaryDirectProductLifting

end Representation
