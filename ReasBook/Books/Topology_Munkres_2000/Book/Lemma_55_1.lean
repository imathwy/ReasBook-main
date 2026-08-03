module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

universe u

namespace FundamentalGroup

universe v

/-- Helper for Lemma 55.1: continuous left inverses induce endpoint-adjusted left
inverses on fundamental groups. -/
lemma mapLeftInverseOfLeftInverse {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X)) (hgf : Function.LeftInverse g f) (x : X) :
    Function.LeftInverse (mapOfEq g (hgf x)) (map f x) := by
  -- Expand the induced maps, then work with one representative based loop.
  intro p
  rw [mapOfEq_apply, map_apply]
  induction p using Quotient.ind
  case _ path =>
    apply Quotient.sound
    -- The retraction law identifies the twice-mapped path pointwise with the original path.
    suffices hpath :
        (fun q ↦ q.cast (hgf x).symm (hgf x).symm)
          ((fun q ↦ q.map g.continuous)
            ((fun q ↦ q.map f.continuous) path)) = path by
      rw [hpath]
    ext t
    exact hgf (path t)

/-- Helper for Lemma 55.1: a continuous map with a continuous left inverse induces
an injective homomorphism on fundamental groups. -/
lemma mapInjectiveOfLeftInverse {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X)) (hgf : Function.LeftInverse g f) (x : X) :
    Function.Injective (map f x) := by
  -- Apply the elementary fact that every function admitting a left inverse is injective.
  exact (mapLeftInverseOfLeftInverse f g hgf x).injective

end FundamentalGroup

/-- Lemma 55.1. If `A` is a retract of `X`, then the homomorphism on fundamental
groups induced by the inclusion `A → X` is injective at every basepoint in `A`. -/
theorem fundamentalGroupMap_injective_of_isRetract {X : Type u}
    [TopologicalSpace X] {A : Set X} (hA : Set.IsRetract A) (a₀ : A) :
    Function.Injective (FundamentalGroup.mapOfSubtype A a₀) := by
  -- Choose the continuous retraction and expose the inclusion underlying `mapOfSubtype`.
  obtain ⟨r, hr⟩ := (Set.isRetract_iff A).mp hA
  -- Route correction: the private `import all` makes the inclusion definition reducible here.
  unfold FundamentalGroup.mapOfSubtype
  -- The retraction is a left inverse to inclusion, so the general induced-map result applies.
  exact FundamentalGroup.mapInjectiveOfLeftInverse
    ⟨Subtype.val, continuous_subtype_val⟩ r hr a₀
