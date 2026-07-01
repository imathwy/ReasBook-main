import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} [TopologicalSpace E]
variable {α : Type v} [LinearOrder α]

/-- Compatibility bridge for existing `WithBotTop` consumers: scalar-sublevel characterization of
lower semicontinuity. The canonical owner layer remains `WithTopBot`. -/
theorem lowerSemicontinuous_iff_isClosed_sublevel_withBotTop
    [NoMinOrder α] [Nonempty α] {f : E → WithBotTop α} :
    LowerSemicontinuous f ↔ ∀ r : α, IsClosed {x : E | f x ≤ r} := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  constructor
  · intro hf r
    simpa using hf ((r : α) : WithBotTop α)
  · intro h y
    change WithBot (WithTop α) at y
    induction y using WithBot.recBotCoe with
    | bot =>
        have hpreimage_eq :
            f ⁻¹' Set.Iic (⊥ : WithBotTop α) = ⋂ r : α, {x : E | f x ≤ r} := by
          ext x
          constructor
          · intro hx
            rw [Set.mem_iInter]
            intro r
            exact le_trans (le_of_eq (by simpa [Set.mem_preimage] using hx)) bot_le
          · intro hx
            rw [Set.mem_iInter] at hx
            by_cases hbot : f x = ⊥
            · change f x ≤ (⊥ : WithBotTop α)
              exact le_of_eq hbot
            · exfalso
              rcases WithBot.ne_bot_iff_exists.mp hbot with ⟨z, hz⟩
              have hz' : f x = (↑z : WithBotTop α) := by
                simpa using hz.symm
              induction z using WithTop.recTopCoe with
              | top =>
                  let a : α := Classical.choice inferInstance
                  have hxa : f x ≤ (a : WithBotTop α) := by
                    simpa using hx a
                  rw [hz'] at hxa
                  simp at hxa
              | coe z =>
                  rcases exists_lt z with ⟨r, hr⟩
                  have hxr : f x ≤ (r : WithBotTop α) := by
                    simpa using hx r
                  rw [hz'] at hxr
                  change ((z : α) : WithBotTop α) ≤ (r : WithBotTop α) at hxr
                  have hzle : z ≤ r := (WithBotTop.coe_le_coe).mp hxr
                  exact (not_le_of_gt hr hzle).elim
        rw [hpreimage_eq]
        exact isClosed_iInter h
    | coe y =>
        induction y using WithTop.recTopCoe with
        | top =>
            simp
        | coe r =>
            simpa using h r

end
