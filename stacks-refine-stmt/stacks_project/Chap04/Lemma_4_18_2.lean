import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v' u' v u

namespace CategoryTheory.Limits

/- Domain-style sampling for Lemma 4.18.2:
- primary domain: connected finite limit shapes in `CategoryTheory.Limits`;
- sampled owner API:
  `HasFiniteLimits`,
  `hasFiniteLimits_of_hasLimitsOfSize`,
  `hasLimit_of_equalizer_and_product`,
  `HasLimitsOfShape`;
- primitive data: the owner class `HasFiniteConnectedLimits`, whose only primitive field is the
  family of `HasLimitsOfShape J C` instances for finite connected shapes;
- derived API: the shape-transfer instance, the size-change theorem, and the source-facing
  equivalence theorem below;
- layer triage:
  - `source-facing`: the constructor theorem from equalizers and pullbacks and the final `iff`;
  - `core/canonical`: `HasFiniteConnectedLimits`;
  - `bridge/view`: the universe-change theorem and the shape-transfer instance. -/

/-- A category has finite connected limits if it has limits of every finite connected small
diagram. -/
class HasFiniteConnectedLimits (C : Type u) [Category.{v} C] : Prop where
  /-- A finite connected shape admits limits in the ambient category. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J] : HasLimitsOfShape J C

variable (C : Type u) [Category.{v} C]

instance hasLimitsOfShape_of_hasFiniteConnectedLimits
    [HasFiniteConnectedLimits C] (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J] :
    HasLimitsOfShape J C := by
  refine @hasLimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J) ?_
  haveI : IsConnected (FinCategory.AsType J) :=
    isConnected_of_equivalent (FinCategory.equivAsType J).symm
  exact HasFiniteConnectedLimits.out (FinCategory.AsType J)

attribute [instance 100] hasLimitsOfShape_of_hasFiniteConnectedLimits

/-- Finite limits are in particular finite connected limits. -/
instance hasFiniteConnectedLimits_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteConnectedLimits C where
  out _ := inferInstance

attribute [instance 100] hasFiniteConnectedLimits_of_hasFiniteLimits

/-- If `C` has limits of a fixed size, then it has finite connected limits. -/
lemma hasFiniteConnectedLimits_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] :
    HasFiniteConnectedLimits C := by
  letI : HasFiniteLimits C := hasFiniteLimits_of_hasLimitsOfSize C
  infer_instance

/-- We can derive finite connected limits by supplying them in one arbitrary universe. -/
theorem hasFiniteConnectedLimits_of_hasFiniteConnectedLimits_of_size
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J], HasLimitsOfShape J C) :
    HasFiniteConnectedLimits C where
  out := fun J hJ hJ' hJc ↦ by
    haveI := h (ULiftHom.{w} (ULift.{w} J))
    haveI : IsConnected (ULiftHom (ULift J)) :=
      isConnected_of_equivalent (ULiftHomULiftCategory.equiv J)
    exact hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv J).symm

/-- Unpack `HasFiniteConnectedLimits` into the corresponding family of limit instances. -/
theorem hasFiniteConnectedLimits_iff :
    HasFiniteConnectedLimits C ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J], HasLimitsOfShape J C := by
  constructor
  · intro h J _ _ _
    letI := h
    infer_instance
  · intro h
    exact hasFiniteConnectedLimits_of_hasFiniteConnectedLimits_of_size C h

/-- If `C` has equalizers and pullbacks, then it has finite connected limits. -/
theorem hasFiniteConnectedLimits_of_hasEqualizers_and_pullbacks [HasEqualizers C] [HasPullbacks C] :
    HasFiniteConnectedLimits C where
  out := fun J _ _ _ ↦ by
    -- Reduce the finite connected indexing shape to the finite bipartite form from
    -- Lemma 4.18.1 and construct its limit by iterated pullbacks followed by an equalizer.
    sorry

/-- Lemma 4.18.2: a category has limits of every finite connected small diagram if and only if it
has equalizers and fibre products. -/
-- Proof sketch: equalizers and pullbacks are themselves finite connected limits, so the forward
-- implication is immediate. For the converse, use Lemma 4.18.1 to replace any finite connected
-- indexing category by a finite bipartite one, then inductively merge source vertices using
-- pullbacks until only one source remains; the remaining limit is a successive equalizer.
theorem finite_connected_limits_iff_equalizers_and_pullbacks :
    HasFiniteConnectedLimits C ↔ HasEqualizers C ∧ HasPullbacks C := by
  constructor
  · intro h
    letI : HasFiniteConnectedLimits C := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hE, hPB⟩
    letI : HasEqualizers C := hE
    letI : HasPullbacks C := hPB
    exact hasFiniteConnectedLimits_of_hasEqualizers_and_pullbacks C

end CategoryTheory.Limits
