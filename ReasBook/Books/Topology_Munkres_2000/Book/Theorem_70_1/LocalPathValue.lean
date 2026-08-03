module

public import Topology_Munkres_2000.Book.Theorem_59_1
public import Mathlib.CategoryTheory.SingleObj

public section

universe u v w

open CategoryTheory

namespace SeifertVanKampen

/-- Helper for Theorem 70.1: conjugating an identity arrow by a connector gives
the identity endomorphism at the chosen base object. -/
lemma basedLoop_map_id {C : Type u} [Groupoid.{v} C] (b : C)
    (q : ∀ x : C, b ⟶ x) (x : C) :
    End.of (q x ≫ 𝟙 x ≫ Groupoid.inv (q x)) = (1 : End b) := by
  -- Reassociate toward the connector-inverse cancellation law.
  simp only [Category.id_comp, Groupoid.comp_inv, End.one_def]

/-- Helper for Theorem 70.1: connector-based loops turn composition into the
endomorphism multiplication used by a vertex-group homomorphism. -/
lemma basedLoop_map_comp {C : Type u} [Groupoid.{v} C] (b : C)
    (q : ∀ x : C, b ⟶ x) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    End.of (q x ≫ (f ≫ g) ≫ Groupoid.inv (q z)) =
      End.of (q y ≫ g ≫ Groupoid.inv (q z)) *
        End.of (q x ≫ f ≫ Groupoid.inv (q y)) := by
  -- Reassociate the product until the middle connector pair is adjacent.
  simp [End.mul_def, Category.assoc]

/-- Helper for Theorem 70.1: the connector construction preserves identity arrows
after applying the prescribed vertex-group homomorphism. -/
lemma basedPathFunctor_map_id {C : Type u} [Groupoid.{v} C] {H : Type w}
    [Group H] (b : C) (q : ∀ x : C, b ⟶ x) (k : End b →* H) (x : C) :
    k (End.of (q x ≫ 𝟙 x ≫ Groupoid.inv (q x))) =
      𝟙 (CategoryTheory.SingleObj.star H) := by
  -- Reduce the closed identity arrow to the unit and use preservation of one.
  rw [basedLoop_map_id]
  exact k.map_one

/-- Helper for Theorem 70.1: the connector construction preserves composition
after applying the prescribed vertex-group homomorphism. -/
lemma basedPathFunctor_map_comp {C : Type u} [Groupoid.{v} C] {H : Type w}
    [Group H] (b : C) (q : ∀ x : C, b ⟶ x) (k : End b →* H)
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    k (End.of (q x ≫ (f ≫ g) ≫ Groupoid.inv (q z))) =
      k (End.of (q y ≫ g ≫ Groupoid.inv (q z))) *
        k (End.of (q x ≫ f ≫ Groupoid.inv (q y))) := by
  -- Map the connector cancellation formula through the homomorphism.
  rw [basedLoop_map_comp, map_mul]

/-- Helper for Theorem 70.1: a homomorphism from one vertex group of a connected
groupoid extends along a chosen connector to a one-object-groupoid functor. -/
def basedPathFunctor {C : Type u} [Groupoid.{v} C] {H : Type w}
    [Group H] (b : C) (q : ∀ x : C, b ⟶ x) (k : End b →* H) :
    C ⥤ CategoryTheory.SingleObj H :=
  { obj := fun _ ↦ CategoryTheory.SingleObj.star H
    map := fun f ↦ k (End.of (q _ ≫ f ≫ Groupoid.inv (q _)))
    map_id := basedPathFunctor_map_id b q k
    map_comp := basedPathFunctor_map_comp b q k }

/-- Helper for Theorem 70.1: at the base object, identity connectors recover
the prescribed homomorphism pointwise. -/
lemma basedPathFunctor_map_at_base {C : Type u} [Groupoid.{v} C] {H : Type w}
    [Group H] (b : C) (q : ∀ x : C, b ⟶ x) (k : End b →* H)
    (hq : q b = 𝟙 b) (f : End b) : (basedPathFunctor b q k).map f = k f := by
  -- Unfold the arrow map, then remove the two identity connectors.
  simp only [basedPathFunctor]
  rw [hq]
  simp

/-- Helper for Theorem 70.1: the connector construction recovers the original
homomorphism when the connector at the base object is the identity. -/
lemma basedPathFunctor_mapEnd_eq {C : Type u} [Groupoid.{v} C] {H : Type w}
    [Group H] (b : C) (q : ∀ x : C, b ⟶ x) (k : End b →* H)
    (hq : q b = 𝟙 b) : (basedPathFunctor b q k).mapEnd b = k := by
  -- Extensionality reduces the equality to the pointwise connector computation.
  apply MonoidHom.ext
  intro f
  exact basedPathFunctor_map_at_base b q k hq f

/-- Helper for Theorem 70.1: compatible local groupoid functors, together with
their prescribed basepoint homomorphisms. -/
structure LocalSystem {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) {H : Type w} [Group H]
    (φ₁ : FundamentalGroup U ⟨x₀, hx₀.1⟩ →* H)
    (φ₂ : FundamentalGroup V ⟨x₀, hx₀.2⟩ →* H) where
  left : FundamentalGroupoid U ⥤ CategoryTheory.SingleObj H
  right : FundamentalGroupoid V ⥤ CategoryTheory.SingleObj H
  agree : ∀ {x y : FundamentalGroupoid (U ∩ V : Set X)} (p : x ⟶ y),
    left.map
        ((FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_left)).map p) =
      right.map
        ((FundamentalGroupoid.map
          (ContinuousMap.inclusion Set.inter_subset_right)).map p)
  left_at_base : left.mapEnd (FundamentalGroupoid.mk ⟨x₀, hx₀.1⟩) = φ₁
  right_at_base : right.mapEnd (FundamentalGroupoid.mk ⟨x₀, hx₀.2⟩) = φ₂

end SeifertVanKampen
