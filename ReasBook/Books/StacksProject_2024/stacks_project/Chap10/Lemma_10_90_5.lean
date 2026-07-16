import StacksProject_2024.stacks_project.Chap10.Lemma_10_90_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

variable [IsNoetherianRing R]

-- Proof sketch: by Lemma 10.31.4, every finite `R`-module over a Noetherian ring is finitely
-- presented; apply this to any finite ideal `I` of `R`.
/-- Lemma 10.90.5: a Noetherian ring is a coherent ring. -/
instance noetherianRing_isCoherentRing : IsCoherentRing R where
  toCoherent :=
    { toFinite := inferInstance
      finitePresentation_submodule := fun I _ ↦ Module.finitePresentation_of_finite R I }

end
