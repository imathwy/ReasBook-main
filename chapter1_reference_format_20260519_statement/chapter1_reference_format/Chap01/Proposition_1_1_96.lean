import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G]

/-- Proposition 1.1.96: a group is isomorphic to a direct product of two groups if and only if it
contains two complementary normal subgroups. Equivalently, it contains two normal subgroups with
trivial intersection whose product is the whole group. -/
-- Proof sketch: For a product `G₁ × G₂`, take the images of the two coordinate subgroups under an
-- isomorphism `G₁ × G₂ ≃* G`. Conversely, complementary normal subgroups commute elementwise, so
-- the multiplication map `A × B → G` is a bijective homomorphism.
theorem exists_mulEquiv_prod_iff_exists_complementary_normal_subgroups :
    (∃ (G₁ : Type u) (_ : Group G₁) (G₂ : Type u) (_ : Group G₂),
      Nonempty (G ≃* G₁ × G₂)) ↔
    ∃ A B : Subgroup G, A.Normal ∧ B.Normal ∧ A.IsComplement' B := by
  constructor
  · rintro ⟨G₁, _, G₂, _, ⟨e⟩⟩
    let A₀ : Subgroup (G₁ × G₂) := (⊤ : Subgroup G₁).prod ⊥
    let B₀ : Subgroup (G₁ × G₂) := (⊥ : Subgroup G₁).prod ⊤
    let A : Subgroup G := A₀.map e.symm.toMonoidHom
    let B : Subgroup G := B₀.map e.symm.toMonoidHom
    refine ⟨A, B, ?_, ?_, ?_⟩
    · have hA₀ : A₀.Normal := inferInstance
      simpa [A] using hA₀.map e.symm.toMonoidHom e.symm.surjective
    · have hB₀ : B₀.Normal := inferInstance
      simpa [B] using hB₀.map e.symm.toMonoidHom e.symm.surjective
    · refine ⟨?_, ?_⟩
      · intro x y hxy
        rcases x with ⟨a, b⟩
        rcases y with ⟨a', b'⟩
        have ha₀ : e a ∈ A₀ :=
          (Subgroup.mem_map_equiv).mp a.property
        have hb₀ : e b ∈ B₀ :=
          (Subgroup.mem_map_equiv).mp b.property
        have ha₀' : e a' ∈ A₀ :=
          (Subgroup.mem_map_equiv).mp a'.property
        have hb₀' : e b' ∈ B₀ :=
          (Subgroup.mem_map_equiv).mp b'.property
        have ha₂ : (e a).2 = 1 := by
          simpa [A₀, Subgroup.mem_prod] using ha₀
        have hb₁ : (e b).1 = 1 := by
          simpa [B₀, Subgroup.mem_prod] using hb₀
        have ha₂' : (e a').2 = 1 := by
          simpa [A₀, Subgroup.mem_prod] using ha₀'
        have hb₁' : (e b').1 = 1 := by
          simpa [B₀, Subgroup.mem_prod] using hb₀'
        apply Prod.ext
        · apply Subtype.ext
          apply e.injective
          ext
          · have hfst := congrArg Prod.fst (congrArg e hxy)
            simpa [hb₁, hb₁'] using hfst
          · exact ha₂.trans ha₂'.symm
        · apply Subtype.ext
          apply e.injective
          ext
          · exact hb₁.trans hb₁'.symm
          · have hsnd := congrArg Prod.snd (congrArg e hxy)
            simpa [ha₂, ha₂'] using hsnd
      · intro g
        refine ⟨⟨⟨e.symm ((e g).1, 1), ?_⟩, ⟨e.symm (1, (e g).2), ?_⟩⟩, ?_⟩
        · exact
            (Subgroup.mem_map_equiv).2 (by simp [A₀, Subgroup.mem_prod])
        · exact
            (Subgroup.mem_map_equiv).2 (by simp [B₀, Subgroup.mem_prod])
        · apply e.injective
          simp
  · rintro ⟨A, B, hA, hB, h⟩
    let φ : A × B →* G :=
      { toFun := fun x ↦ x.1 * x.2
        map_one' := by simp
        map_mul' := by
          intro x y
          rcases x with ⟨a, b⟩
          rcases y with ⟨a', b'⟩
          have hcomm : Commute (a' : G) (b : G) :=
            Subgroup.commute_of_normal_of_disjoint A B hA hB h.disjoint a' b a'.2 b.2
          simp only [Prod.mk_mul_mk]
          simpa [mul_assoc] using congrArg (fun z : G ↦ (a : G) * z * b') hcomm.eq }
    exact ⟨A, inferInstance, B, inferInstance, ⟨MulEquiv.symm (MulEquiv.ofBijective φ h)⟩⟩

end
