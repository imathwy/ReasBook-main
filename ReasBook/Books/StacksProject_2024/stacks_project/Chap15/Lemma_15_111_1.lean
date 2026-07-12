import Mathlib.RingTheory.Invariant.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Polynomial

/- Domain-style sampling for Lemma 15.111.1:
- primary domain: invariant theory for fixed subrings under finite group actions
- sampled owner declarations:
  `RingHom.codRestrict`,
  `MulSemiringAction.charpoly_eq`,
  `Algebra.IsInvariant.charpoly_mem_lifts`,
  `Polynomial.lifts_and_natDegree_eq_and_monic`
- best owner abstraction: the orbit polynomial owner `MulSemiringAction.charpoly` together with the
  canonical lift-to-subring theorem `Algebra.IsInvariant.charpoly_mem_lifts`; the induced map on
  fixed subrings is a small bridge built from `RingHom.codRestrict`
- primitive data: an equivariant ring homomorphism `φ : A →+*[G] B`, its surjectivity, and a fixed
  element `b : B^G`
- derived API: the monic polynomial over `A^G` mapping to `(X - C b) ^ |G|`

Layer triage:
- `source-facing`: the existence of the monic polynomial over the fixed subring
- `core/canonical`: `MulSemiringAction.charpoly` and `Algebra.IsInvariant.charpoly_mem_lifts`
- `bridge/view`: the induced ring homomorphism on fixed subrings

The theorem should stay source-facing, while its proof reuses the invariant-ring owner API instead
of rebuilding the coefficient-lift argument entrywise.
-/

section

variable {G : Type u} [Group G]
variable {A : Type v} {B : Type w} [CommRing A] [CommRing B]
variable [MulSemiringAction G A] [MulSemiringAction G B]

local notation "AFix" => FixedPoints.subring A G
local notation "BFix" => FixedPoints.subring B G

namespace FixedPoints

/-- A ring is invariant over its own fixed subring. -/
instance subring_isInvariant : Algebra.IsInvariant (FixedPoints.subring A G) A G where
  isInvariant a ha := ⟨⟨a, ha⟩, rfl⟩

end FixedPoints

namespace MulSemiringActionHom

/-- The ring homomorphism induced on fixed subrings by an equivariant ring homomorphism. -/
def fixedPoints (φ : A →+*[G] B) : AFix →+* BFix :=
  RingHom.codRestrict
    ((φ : A →+* B).comp (FixedPoints.subring A G).subtype)
    BFix fun a g ↦ by
    simpa [MulSemiringActionHom.map_smul] using congrArg φ (a.2 g)

/-- Composing the induced map on fixed subrings with the subtype recovers the underlying ring
homomorphism restricted to the fixed subring. -/
@[simp] theorem subtype_comp_fixedPoints (φ : A →+*[G] B) :
    (FixedPoints.subring B G).subtype.comp φ.fixedPoints =
      (φ : A →+* B).comp (FixedPoints.subring A G).subtype :=
  rfl

end MulSemiringActionHom

variable [Finite G]

-- Proof sketch: choose `a : A` with `φ a = b`, form the orbit product
-- `∏ g : G, (X - C ⟨g • a, ...⟩)`, and use equivariance to see that its coefficients lie in
-- `A^G`; after applying the induced map on fixed subrings, this becomes `(X - C b) ^ |G|`.
/-- Lemma 15.111.1: for a surjective equivariant ring homomorphism and a fixed element `b` of `B`,
there is a monic polynomial over the fixed subring of `A` mapping to `(X - C b) ^ |G|` over the
fixed subring of `B`. -/
theorem exists_monic_polynomial_over_fixedPoints_map_eq_X_sub_C_pow
    (φ : A →+*[G] B) (hφ : Function.Surjective φ) (b : BFix) :
    ∃ P : Polynomial AFix,
      P.Monic ∧
        P.map φ.fixedPoints = (X - C b) ^ Nat.card G := by
  classical
  cases nonempty_fintype G
  obtain ⟨a, ha⟩ := hφ b
  have hchar_lifts :
      MulSemiringAction.charpoly G a ∈ Polynomial.lifts (FixedPoints.subring A G).subtype := by
    simpa using Algebra.IsInvariant.charpoly_mem_lifts AFix A G a
  obtain ⟨P, hPmap, -, hPmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hchar_lifts
      (MulSemiringAction.monic_charpoly G a)
  refine ⟨P, hPmonic, ?_⟩
  have hb : ∀ g : G, g • (b : B) = b := b.2
  exact (Polynomial.map_injective (FixedPoints.subring B G).subtype Subtype.val_injective) <|
    calc
      Polynomial.map (FixedPoints.subring B G).subtype (P.map φ.fixedPoints) =
          Polynomial.map ((FixedPoints.subring B G).subtype.comp φ.fixedPoints) P := by
            rw [Polynomial.map_map]
      _ = Polynomial.map ((φ : A →+* B).comp (FixedPoints.subring A G).subtype) P := by
            rw [MulSemiringActionHom.subtype_comp_fixedPoints]
      _ = Polynomial.map (φ : A →+* B) (MulSemiringAction.charpoly G a) := by
            rw [← hPmap, Polynomial.map_map]
      _ = (X - C (b : B)) ^ Fintype.card G := by
            rw [MulSemiringAction.charpoly_eq, Polynomial.map_prod]
            calc
              ∏ g : G, Polynomial.map (φ : A →+* B) (X - C (g • a)) =
                  ∏ g : G, (X - C (g • (b : B))) := by
                    refine Finset.prod_congr rfl ?_
                    intro g _
                    simp [ha]
              _ = ∏ _ : G, (X - C (b : B)) := by
                    refine Finset.prod_congr rfl ?_
                    intro g _
                    rw [hb g]
              _ = (X - C (b : B)) ^ Fintype.card G := by
                    simp
      _ = Polynomial.map (FixedPoints.subring B G).subtype ((X - C b) ^ Nat.card G) := by
            simp [Nat.card_eq_fintype_card]

end
