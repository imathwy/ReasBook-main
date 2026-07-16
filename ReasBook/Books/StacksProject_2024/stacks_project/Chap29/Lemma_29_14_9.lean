import StacksProject_2024.stacks_project.Chap29.Lemma_29_14_7_Core

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace RingHom

/- Semantic recall:
- `lean_leansearch` surfaced the generic composition theorem
  `RingHom.locally_stableUnderComposition` together with
  `RingHom.IsStandardOpenImmersion.stableUnderComposition`;
- the local chapter owner file `Lemma_29_14_7_Core` already records the source-faithful ring-hom
  predicates `RingHom.isIsoOnLocalRings` and `RingHom.targetIsNoetherian`;
- the canonical open-immersion clause is stated directly on the owner
  `RingHom.StableUnderComposition (RingHom.Locally RingHom.IsStandardOpenImmersion)`, while the
  two source-facing local predicates remain theorem-shaped bridges.
-/

/-- Lemma 29.14.9 (1): the property that `R → A` induces an isomorphism
`R_𝔭 → A_𝔮` on local rings for every prime `𝔮` of `A` is stable under composition. -/
theorem isIsoOnLocalRings_stableUnderComposition :
    RingHom.StableUnderComposition RingHom.isIsoOnLocalRings :=
  RingHom.isIsoOnLocalRings_propertyIsLocal.locally_stableUnderComposition

/-- Lemma 29.14.9 (2): the open-immersion ring-map condition, expressed as being locally a
standard open immersion on the target, is stable under composition. -/
theorem openImmersion_stableUnderComposition :
    RingHom.StableUnderComposition (RingHom.Locally RingHom.IsStandardOpenImmersion) :=
  RingHom.IsStandardOpenImmersion.stableUnderComposition

/-- Lemma 29.14.9 (3): the property that the target ring `A` is Noetherian is stable under
composition. -/
theorem targetIsNoetherian_stableUnderComposition :
    RingHom.StableUnderComposition RingHom.targetIsNoetherian :=
  RingHom.targetIsNoetherian_propertyIsLocal.locally_stableUnderComposition

end RingHom
