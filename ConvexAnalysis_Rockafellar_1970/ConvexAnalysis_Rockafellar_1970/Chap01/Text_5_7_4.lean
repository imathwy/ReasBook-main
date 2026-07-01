import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {Y : Type*} {Z : Type*} {𝕜 : Type*}
variable [InfSet 𝕜] [Add 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.7.4 uses infimal convolution of bifunction slices
  `f y, g y : Z → 𝕜`, i.e. convolution in the `Z` variable with `y` fixed.
- `core/canonical`: the owner abstraction is the chapter declaration `infimal_convolution` on
  one-variable functions; the bifunction formulas are direct slice specializations of this owner.
- `bridge/view`: evaluation at `(y, z)` is the one-variable evaluation of
  `((f y) □ (g y)) z`, with decomposition and one-parameter formulas inherited directly from
  `Text_5_4_0`.

Domain-style sampling used here:
- the chapter owner `infimal_convolution` from `Text_5_4_0`;
- its evaluation theorem `infimal_convolution_apply`;
- its left-substitution companion `infimal_convolution_apply_neg_add`;
- its decomposition companion `infimal_convolution_eq_sInf_decompositions`;
- the codomain-level infimum `⨅ u, ...` used throughout the surrounding section;
- ordinary one-variable slices `f y` and `g y` at fixed `y`.
- Abstraction checks:
  - codomain/ambient layer: owner-generic `InfSet`/`Add` layer, not specialized to `EReal`/`ℝ`;
  - scalar/space structure: only additive structure on `Z` for the primitive layer;
  - owner choice: use canonical owner `□` on slices, with no parallel wrapper owner;
  - topology language: not applicable for this algebraic item;
  - notation surface: reuse existing chapter notation `□` directly on theorem surfaces.
- Layer target: direct slice-level reuse of `infimal_convolution`.
-/

/-- Helper for Text 5.7.4: the decomposition-value owner at `z` collects all values
`f z₁ + g z₂` coming from additive decompositions `z₁ + z₂ = z`. -/
def infimalConvolutionDecompositionValues [Add Z]
    (f g : Z → 𝕜) (z : Z) : Set 𝕜 :=
  (fun p : Z × Z ↦ f p.1 + g p.2) '' {p : Z × Z | p.1 + p.2 = z}

/-- Helper for Text 5.7.4: the one-variable infimal convolution of `f` and `g` sends `z` to the
infimum of the decomposition-value owner at `z`. -/
def infimal_convolution [Add Z] (f g : Z → 𝕜) : Z → 𝕜 :=
  fun z ↦ sInf (infimalConvolutionDecompositionValues f g z)

infixl:70 " □ " => infimal_convolution

/-- Helper for Text 5.7.4: evaluating the one-variable infimal convolution at `z` is, by
definition, the infimum of its decomposition-value owner. -/
theorem infimal_convolution_eq_sInf_decompositionValues [Add Z]
    (f g : Z → 𝕜) (z : Z) :
    (f □ g) z = sInf (infimalConvolutionDecompositionValues f g z) := rfl

/-- Helper for Text 5.7.4: under additive-group structure on `Z`, evaluating the one-variable
infimal convolution at `z` gives the one-parameter infimum `⨅ u, f u + g (-u + z)`. -/
theorem infimal_convolution_apply_neg_add [AddGroup Z]
    (f g : Z → 𝕜) (z : Z) :
    (f □ g) z = ⨅ u : Z, f u + g (-u + z) := by
  rw [infimal_convolution_eq_sInf_decompositionValues, show
    infimalConvolutionDecompositionValues f g z = Set.range (fun u : Z ↦ f u + g (-u + z)) by
      ext a
      constructor
      · rintro ⟨⟨u, v⟩, hp, rfl⟩
        refine ⟨u, ?_⟩
        have hv : v = -u + z := eq_neg_add_of_add_eq hp
        simp [hv]
      · rintro ⟨u, rfl⟩
        refine ⟨(u, -u + z), ?_, rfl⟩
        simp, sInf_range]

/-- Helper for Text 5.7.4: under additive-commutative-group structure on `Z`, evaluating the
one-variable infimal convolution at `z` gives the textbook one-parameter infimum
`⨅ u, f u + g (z - u)`. -/
@[simp] theorem infimal_convolution_apply [AddCommGroup Z]
    (f g : Z → 𝕜) (z : Z) :
    (f □ g) z = ⨅ u : Z, f u + g (z - u) := by
  simpa [sub_eq_add_neg, add_comm] using
    (infimal_convolution_apply_neg_add (f := f) (g := g) (z := z))

section DecompositionFormula

variable [Add Z]

-- Proof sketch: specialize the owner-level decomposition formula
-- `infimal_convolution_eq_sInf_decompositionValues` to the fixed slice `y`.
/-- Helper for Text 5.7.4: evaluating the slice infimal convolution at `(y, z)` is the infimum of
the canonical decomposition-value owner for the fixed slice pair `(f y, g y)`. -/
theorem infimal_convolution_slice_eq_sInf_decompositionValues
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    ((f y) □ (g y)) z = sInf (infimalConvolutionDecompositionValues (f y) (g y) z) := by
  simpa using
    (infimal_convolution_eq_sInf_decompositionValues (f := f y) (g := g y) (z := z))

/-- Helper for Text 5.7.4: evaluating slice infimal convolution at `(y, z)` gives the infimum over
all decompositions `z = z₁ + z₂` of the `z`-coordinate while `y` is held fixed. -/
theorem infimal_convolution_slice_eq_sInf_decompositions
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    ((f y) □ (g y)) z =
      sInf ((fun p : Z × Z ↦ f y p.1 + g y p.2) '' {p : Z × Z | p.1 + p.2 = z}) := by
  simpa [infimalConvolutionDecompositionValues] using
    (infimal_convolution_slice_eq_sInf_decompositionValues (f := f) (g := g) (y := y) (z := z))

end DecompositionFormula

section LeftSubFormula

variable [AddGroup Z]

-- Proof sketch: specialize the one-variable owner theorem
-- `infimal_convolution_apply_neg_add` to the fixed-`y` slices.
/-- Helper for Text 5.7.4: under additive-group structure on `Z`, evaluating slice infimal
convolution at `(y, z)` gives `⨅ u, f y u + g y (-u + z)`. -/
theorem infimal_convolution_slice_apply_neg_add
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    ((f y) □ (g y)) z = ⨅ u : Z, f y u + g y (-u + z) := by
  simpa using infimal_convolution_apply_neg_add (f y) (g y) z

end LeftSubFormula

section SubtractionFormula

variable [AddCommGroup Z]

-- Proof sketch: this is the commutative-group specialization of the slice owner formula.
/-- Helper for Text 5.7.4: under additive-commutative-group structure on `Z`, evaluating slice
infimal convolution at `(y, z)` gives the one-parameter infimum `⨅ u, f y u + g y (z - u)`. -/
@[simp] theorem infimal_convolution_slice_apply
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    ((f y) □ (g y)) z = ⨅ u : Z, f y u + g y (z - u) := by
  exact infimal_convolution_apply (f y) (g y) z

end SubtractionFormula

section PartialInfimalConvolution

variable [Add Z]

/-- Text 5.7.4: the partial infimal convolution of `f` and `g` with respect to the `z`-variable
freezes `y` and takes the ordinary infimal convolution of the corresponding `Z`-slices. -/
abbrev partial_infimal_convolution (f g : Y → Z → 𝕜) : Y → Z → 𝕜 :=
  fun y ↦ (f y) □ (g y)

/-- Helper for Text 5.7.4: evaluating the source-facing owner at a fixed `y` recovers the
canonical slice infimal convolution. -/
@[simp] theorem partial_infimal_convolution_eq_slice_owner
    (f g : Y → Z → 𝕜) (y : Y) :
    partial_infimal_convolution f g y = (f y) □ (g y) := by
  rfl

end PartialInfimalConvolution

section PartialInfimalConvolutionFormula

variable [AddCommGroup Z]

/-- Helper for Text 5.7.4: reindexing the slice infimal convolution by `u ↦ z - u` puts the
one-parameter infimum into the textbook order `f y (z - u) + g y u`. -/
theorem infimal_convolution_slice_apply_sub_right
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    ((f y) □ (g y)) z = ⨅ u : Z, f y (z - u) + g y u := by
  -- Freeze `y` and start from the canonical slice formula already proved above.
  calc
    ((f y) □ (g y)) z = ⨅ u : Z, f y u + g y (z - u) := by
      exact infimal_convolution_slice_apply (f := f) (g := g) (y := y) (z := z)
    _ = ⨅ u : Z, f y (z - u) + g y u := by
      -- Reindex the infimum by the involution `u ↦ z - u`.
      let e : Z ≃ Z :=
        { toFun := fun u ↦ z - u
          invFun := fun u ↦ z - u
          left_inv := sub_sub_cancel z
          right_inv := sub_sub_cancel z }
      exact Equiv.iInf_congr e fun u ↦ by
        simp [e]

/-- Text 5.7.4: evaluating the partial infimal convolution at `(y, z)` gives the infimum over
`u` of `f y (z - u) + g y u`, i.e. infimal convolution in the `z`-variable with `y` fixed. -/
@[simp] theorem partial_infimal_convolution_apply
    (f g : Y → Z → 𝕜) (y : Y) (z : Z) :
    partial_infimal_convolution f g y z = ⨅ u : Z, f y (z - u) + g y u := by
  -- Unfold the source-facing owner once, then reuse the reindexed slice formula.
  rw [partial_infimal_convolution_eq_slice_owner]
  exact infimal_convolution_slice_apply_sub_right (f := f) (g := g) (y := y) (z := z)

end PartialInfimalConvolutionFormula

end
