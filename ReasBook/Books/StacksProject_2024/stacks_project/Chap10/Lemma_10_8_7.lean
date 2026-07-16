import StacksProject_2024.stacks_project.Chap04.Lemma_4_14_8
import StacksProject_2024.stacks_project.Chap10.Definition_10_8_6

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]
variable {M N : I ⥤ ModuleCat R} [HasColimit M] [HasColimit N]
variable (Φ : M ⟶ N)

/- Lemma 10.8.7 is a `bridge/view` item in the colimit-of-module-systems domain: a morphism of
systems `Φ : M ⟶ N` over the same preordered set induces the canonical morphism on direct limits.
The owner abstraction is the colimit functor, so the source-facing specialization is the induced
map `colim.map Φ`, while the Chapter 4 theorem supplies its universal-property characterization. -/
#check (colim.map Φ : colimit M ⟶ colimit N)

/- Companion recall: the Chapter 4 owner theorem specializes to the uniqueness statement for the
induced map on colimits of module systems over the same preorder. -/
#check (show ∃! θ : colimit M ⟶ colimit N,
    ∀ i : I, colimit.ι M i ≫ θ = Φ.app i ≫ colimit.ι N i from
  by
    refine ⟨colim.map Φ, ?_, ?_⟩
    · intro i
      exact colimit.ι_map Φ i
    · intro θ hθ
      refine colimit.hom_ext (fun i ↦ ?_)
      calc
        colimit.ι M i ≫ θ = Φ.app i ≫ colimit.ι N i := hθ i
        _ = colimit.ι M i ≫ colim.map Φ := (colimit.ι_map Φ i).symm)

end

end CategoryTheory
