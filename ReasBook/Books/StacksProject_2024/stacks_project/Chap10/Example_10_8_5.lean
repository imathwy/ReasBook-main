import Mathlib

open CategoryTheory CategoryTheory.Limits ModuleCat

universe u v

section

variable {R : Type u} [Ring R]
variable {Ma : Type v} [AddCommGroup Ma] [Module R Ma]
variable {Mb : Type v} [AddCommGroup Mb] [Module R Mb]
variable {Mc : Type v} [AddCommGroup Mc] [Module R Mc]

/-
Layering for Example 10.8.5:
* source-facing: the explicit quotient model for the colimit of the fork-shaped system
  `{a, b, c}` with `a < b` and `a < c`.
* core/canonical owner: `span (ModuleCat.ofHom μab) (ModuleCat.ofHom μac)`.
* bridge/view: the explicit quotient model `Coker(μab ⊕ -μac)` computing the colimit of that
  system.
-/

/-- The map `Ma → Mb × Mc` whose cokernel computes the colimit of the fork system from
Example 10.8.5. -/
def example_10_8_5_difference_map (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    Ma →ₗ[R] Mb × Mc :=
  μab.prod (-μac)

/-- The explicit quotient model computing the colimit in Example 10.8.5. -/
abbrev example_10_8_5_colimit_model (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :=
  (Mb × Mc) ⧸ LinearMap.range (example_10_8_5_difference_map μab μac)

/-- The canonical map from stage `b` into the explicit colimit model of Example 10.8.5. -/
def example_10_8_5_from_b (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    Mb →ₗ[R] example_10_8_5_colimit_model μab μac :=
  (LinearMap.range (example_10_8_5_difference_map μab μac)).mkQ.comp (LinearMap.inl R Mb Mc)

/-- The canonical map from stage `c` into the explicit colimit model of Example 10.8.5. -/
def example_10_8_5_from_c (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    Mc →ₗ[R] example_10_8_5_colimit_model μab μac :=
  (LinearMap.range (example_10_8_5_difference_map μab μac)).mkQ.comp (LinearMap.inr R Mb Mc)

/-- The canonical map from stage `a` into the explicit colimit model of Example 10.8.5. -/
def example_10_8_5_from_a (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    Ma →ₗ[R] example_10_8_5_colimit_model μab μac :=
  (example_10_8_5_from_b μab μac).comp μab

/-- The explicit quotient model of Example 10.8.5 gives a pushout cocone on
`Ma ⟶ Mb`, `Ma ⟶ Mc`. -/
private theorem example_10_8_5_comm
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    CommSq (ModuleCat.ofHom μab) (ModuleCat.ofHom μac)
      (ModuleCat.ofHom (example_10_8_5_from_b μab μac))
      (ModuleCat.ofHom (example_10_8_5_from_c μab μac)) := by
  refine ⟨?_⟩
  apply ModuleCat.hom_ext
  ext x
  change Submodule.Quotient.mk
      (((LinearMap.inl R Mb Mc).comp μab) x : Mb × Mc) =
    Submodule.Quotient.mk (((LinearMap.inr R Mb Mc).comp μac) x : Mb × Mc)
  exact (Submodule.Quotient.eq _).2 ⟨x, by
    simp [example_10_8_5_difference_map]⟩

/-- The explicit quotient cocone over the fork system from Example 10.8.5. -/
def example_10_8_5_cocone (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    PushoutCocone (ModuleCat.ofHom μab) (ModuleCat.ofHom μac) :=
  PushoutCocone.mk
    (ModuleCat.ofHom (example_10_8_5_from_b μab μac))
    (ModuleCat.ofHom (example_10_8_5_from_c μab μac))
    (example_10_8_5_comm μab μac).w

section Desc

variable {P : Type v} [AddCommGroup P] [Module R P]

/-- The unique factorization through the explicit colimit model induced by compatible maps out of
stages `b` and `c`. -/
private def example_10_8_5_desc
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (β : Mb →ₗ[R] P) (γ : Mc →ₗ[R] P) (hβγ : β.comp μab = γ.comp μac) :
    example_10_8_5_colimit_model μab μac →ₗ[R] P :=
  (LinearMap.range (example_10_8_5_difference_map μab μac)).liftQ (LinearMap.coprod β γ) <| by
    rw [LinearMap.range_le_ker_iff]
    ext x
    have hx : β (μab x) = γ (μac x) := LinearMap.congr_fun hβγ x
    simpa [example_10_8_5_difference_map, sub_eq_add_neg] using sub_eq_zero.mpr hx

@[simp] private theorem example_10_8_5_inl_desc
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (β : Mb →ₗ[R] P) (γ : Mc →ₗ[R] P) (hβγ : β.comp μab = γ.comp μac) :
    (example_10_8_5_desc μab μac β γ hβγ).comp (example_10_8_5_from_b μab μac) = β := by
  rw [example_10_8_5_desc, example_10_8_5_from_b, ← LinearMap.comp_assoc, Submodule.liftQ_mkQ,
    LinearMap.coprod_inl]

@[simp] private theorem example_10_8_5_inr_desc
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (β : Mb →ₗ[R] P) (γ : Mc →ₗ[R] P) (hβγ : β.comp μab = γ.comp μac) :
    (example_10_8_5_desc μab μac β γ hβγ).comp (example_10_8_5_from_c μab μac) = γ := by
  rw [example_10_8_5_desc, example_10_8_5_from_c, ← LinearMap.comp_assoc, Submodule.liftQ_mkQ,
    LinearMap.coprod_inr]

private theorem example_10_8_5_desc_unique
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (β : Mb →ₗ[R] P) (γ : Mc →ₗ[R] P) (hβγ : β.comp μab = γ.comp μac)
    {δ : example_10_8_5_colimit_model μab μac →ₗ[R] P}
    (hδB : δ.comp (example_10_8_5_from_b μab μac) = β)
    (hδC : δ.comp (example_10_8_5_from_c μab μac) = γ) :
    δ = example_10_8_5_desc μab μac β γ hβγ := by
  apply LinearMap.ext
  intro q
  refine
    Submodule.Quotient.induction_on (LinearMap.range (example_10_8_5_difference_map μab μac)) q
      ?_
  intro z
  rcases z with ⟨x, y⟩
  have hxy : (Submodule.Quotient.mk (x, y) : example_10_8_5_colimit_model μab μac) =
      Submodule.Quotient.mk (x, 0) + Submodule.Quotient.mk (0, y) := by
    simpa using
      (Submodule.Quotient.mk_add
        (LinearMap.range (example_10_8_5_difference_map μab μac)) :
        (Submodule.Quotient.mk
            ((((x, (0 : Mc)) : Mb × Mc) + (((0 : Mb), y) : Mb × Mc)) :
              Mb × Mc) :
          example_10_8_5_colimit_model μab μac) =
      Submodule.Quotient.mk (((x, (0 : Mc)) : Mb × Mc)) +
            Submodule.Quotient.mk (((0 : Mb), y) : Mb × Mc))
  have hxB : δ (Submodule.Quotient.mk (x, 0) : example_10_8_5_colimit_model μab μac) = β x := by
    simpa [example_10_8_5_from_b] using LinearMap.congr_fun hδB x
  have hyC : δ (Submodule.Quotient.mk (0, y) : example_10_8_5_colimit_model μab μac) = γ y := by
    simpa [example_10_8_5_from_c] using LinearMap.congr_fun hδC y
  have hxB' :
      example_10_8_5_desc μab μac β γ hβγ
          (Submodule.Quotient.mk (x, 0) : example_10_8_5_colimit_model μab μac) =
        β x := by
    simpa [example_10_8_5_from_b] using
      LinearMap.congr_fun (example_10_8_5_inl_desc μab μac β γ hβγ) x
  have hyC' :
      example_10_8_5_desc μab μac β γ hβγ
          (Submodule.Quotient.mk (0, y) : example_10_8_5_colimit_model μab μac) =
        γ y := by
    simpa [example_10_8_5_from_c] using
      LinearMap.congr_fun (example_10_8_5_inr_desc μab μac β γ hβγ) y
  rw [hxy, map_add, map_add, hxB, hyC, hxB', hyC']

end Desc

/-- Example 10.8.5: the explicit quotient cocone computes the colimit of the fork-shaped system
`a < b`, `a < c`. -/
def example_10_8_5_isColimit (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    IsColimit (example_10_8_5_cocone μab μac) := by
  exact
    PushoutCocone.IsColimit.mk (example_10_8_5_comm μab μac).w
      (fun s ↦ ModuleCat.ofHom <|
        example_10_8_5_desc μab μac s.inl.hom s.inr.hom
          (congrArg ModuleCat.Hom.hom s.condition))
      (fun s ↦ by
        apply ModuleCat.hom_ext
        exact
          (example_10_8_5_inl_desc μab μac s.inl.hom s.inr.hom
            (congrArg ModuleCat.Hom.hom s.condition)))
      (fun s ↦ by
        apply ModuleCat.hom_ext
        exact
          (example_10_8_5_inr_desc μab μac s.inl.hom s.inr.hom
            (congrArg ModuleCat.Hom.hom s.condition)))
      (fun s m hmB hmC ↦ by
        apply ModuleCat.hom_ext
        exact example_10_8_5_desc_unique μab μac s.inl.hom s.inr.hom
          (congrArg ModuleCat.Hom.hom s.condition)
          (congrArg ModuleCat.Hom.hom <| by simpa using hmB)
          (congrArg ModuleCat.Hom.hom <| by simpa using hmC))

/-- Example 10.8.5: in the explicit colimit model of the fork system, the kernel of the map from
stage `a` is `ker μab + ker μac`, and the kernel of the map from stage `b` is the image of
`ker μac` under `μab`. -/
theorem example_10_8_5_kernels
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc) :
    LinearMap.ker (example_10_8_5_from_a μab μac) = LinearMap.ker μab ⊔ LinearMap.ker μac ∧
      LinearMap.ker (example_10_8_5_from_b μab μac) =
        Submodule.map μab (LinearMap.ker μac) := by
  sorry

/-- If `μab (ker μac)` is nonzero, then some nonzero element of stage `b` dies in the explicit
colimit model of Example 10.8.5. -/
private theorem example_10_8_5_nonzero_from_b_maps_to_zero
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (hker : Submodule.map μab (LinearMap.ker μac) ≠ ⊥) :
    ∃ x : Mb, example_10_8_5_from_b μab μac x = 0 ∧ x ≠ 0 := by
  sorry

/-- Example 10.8.5 gives the direct failure of Lemma 10.8.4 without directedness: if
`μab (ker μac)` is nonzero, then some nonzero element of stage `b` maps to `0` in the colimit of
the fork-shaped system, but it cannot become `0` in any later stage of that system. -/
theorem example_10_8_5_counterexample_to_lemma_10_8_4
    (μab : Ma →ₗ[R] Mb) (μac : Ma →ₗ[R] Mc)
    (hker : Submodule.map μab (LinearMap.ker μac) ≠ ⊥) :
    ∃ x : Mb,
      example_10_8_5_from_b μab μac x = 0 ∧
        ¬ ∃ j : WalkingSpan, ∃ f : WalkingSpan.left ⟶ j,
          ((span (ModuleCat.ofHom μab) (ModuleCat.ofHom μac)).map f).hom x = 0 := by
  obtain ⟨x, hx, hx_ne⟩ := example_10_8_5_nonzero_from_b_maps_to_zero μab μac hker
  refine ⟨x, hx, ?_⟩
  rintro ⟨j, f, hf⟩
  cases j with
  | none =>
      nomatch f
  | some val =>
      cases val with
      | left =>
          have hf_id : f = 𝟙 WalkingSpan.left := Subsingleton.elim _ _
          subst f
          exact hx_ne <| by simpa using hf
      | right =>
          nomatch f

end
