import StacksProject_2024.stacks_project.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry

open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules

/- Semantic recall: Chapter 28 already packages invertible `\mathcal O_X`-modules by the owner
`Scheme.Modules.Invertible`, exposing the positive tensor powers needed in Definition 29.12.1.
The family notion here is therefore source-facing only in the new family parameter; the
nonvanishing-open condition remains stated explicitly via an affine open `U` together with the
stalkwise predicate characterizing `X_s`. -/

section

variable {X : Scheme.{u}} {ι : Type v}
variable [MonoidalCategory X.Modules]

local notation "ModX" => X.Modules

/-- The pointwise affine nonvanishing-open condition appearing in Definition 29.12.1. -/
class AffineNonvanishingFamily
    (L : ι → ModX)
    [hL : ∀ i : ι, Invertible (L i)] : Prop where
  /-- Every point of `X` lies in an affine nonvanishing open coming from some positive tensor
  power of one member of the family. -/
  exists_affine_nonvanishing (x : X) :
    ∃ i : ι, ∃ n : ℕ, 0 < n ∧
      ∃ s : Γ(Invertible.tensorPow (L i) n, ⊤),
        AffineOpenNeighborhood x ((hL i).nonvanishingOpen s)

/-- Definition 29.12.1: a family `\{\mathcal L_i\}_{i \in I}` of invertible
`\mathcal O_X`-modules on a scheme `X` is ample if `X` is quasi-compact and every point of `X`
lies in an affine nonvanishing open `(X)_[s]` cut out by a global section of a positive tensor
power `\mathcal L_i^{\otimes n}`. -/
@[stacks 0FXR]
class AmpleFamily
    (L : ι → ModX)
    [∀ i : ι, Invertible (L i)] : Prop
    extends CompactSpace X, AffineNonvanishingFamily L

/-- Unfolding form of `AffineNonvanishingFamily`: every point lies in an affine nonvanishing open
coming from a positive tensor power of one member of the family. -/
theorem affineNonvanishingFamily_iff
    (L : ι → ModX)
    [hL : ∀ i : ι, Invertible (L i)] :
    AffineNonvanishingFamily L ↔
      ∀ x : X, ∃ i : ι, ∃ n : ℕ, 0 < n ∧
        ∃ s : Γ(Invertible.tensorPow (L i) n, ⊤),
          AffineOpenNeighborhood x ((hL i).nonvanishingOpen s) := by
  constructor
  · intro hL x
    exact hL.exists_affine_nonvanishing x
  · intro hL
    exact
      { exists_affine_nonvanishing := hL }

/-- Unfolding form of `AmpleFamily`: it is exactly quasi-compactness of `X` together with the
pointwise affine nonvanishing-open condition from the source definition. -/
theorem ampleFamily_iff
    (L : ι → ModX)
    [hL : ∀ i : ι, Invertible (L i)] :
    AmpleFamily L ↔
      IsCompact (Set.univ : Set X) ∧
        ∀ x : X, ∃ i : ι, ∃ n : ℕ, 0 < n ∧
          ∃ s : Γ(Invertible.tensorPow (L i) n, ⊤),
            AffineOpenNeighborhood x ((hL i).nonvanishingOpen s) := by
  constructor
  · intro hL
    exact ⟨hL.isCompact_univ, hL.exists_affine_nonvanishing⟩
  · intro hL
    exact
      { toCompactSpace := ⟨hL.1⟩
        exists_affine_nonvanishing := hL.2 }

/-- The constant-family case of Definition 29.12.1 recovers the single-module owner from
Definition 28.26.1. -/
instance isAmple_pUnit
    (L : ModX) [Invertible L] [hL : AmpleFamily (fun _ : PUnit ↦ L)] :
    Scheme.Modules.IsAmple L where
  toCompactSpace := hL.toCompactSpace
  affine_nonvanishing x := by
    rcases hL.exists_affine_nonvanishing x with ⟨_, n, hn, s, hs⟩
    exact ⟨n, hn, s, hs⟩

/-- The single-module owner from Definition 28.26.1 induces the constant-family owner from
Definition 29.12.1. This is kept as an explicit theorem so the constant-family bridge does not
enter global typeclass search. -/
theorem ampleFamily_pUnit
    (L : ModX) [Invertible L] (hL : Scheme.Modules.IsAmple L) :
    AmpleFamily (fun _ : PUnit ↦ L) where
  toCompactSpace := hL.toCompactSpace
  exists_affine_nonvanishing x := by
    rcases hL.affine_nonvanishing x with ⟨n, hn, s, hs⟩
    exact ⟨PUnit.unit, n, hn, s, hs⟩

/-- Bridge between Definition 29.12.1 and the single-module owner from Definition 28.26.1. -/
theorem ampleFamily_pUnit_iff_isAmple
    (L : ModX) [Invertible L] :
    AmpleFamily (fun _ : PUnit ↦ L) ↔ Scheme.Modules.IsAmple L := by
  constructor
  · intro hL
    exact
      { toCompactSpace := hL.toCompactSpace
        affine_nonvanishing := fun x ↦ by
          rcases hL.exists_affine_nonvanishing x with ⟨_, n, hn, s, hs⟩
          exact ⟨n, hn, s, hs⟩ }
  · intro hL
    exact ampleFamily_pUnit L hL

end

end AlgebraicGeometry
