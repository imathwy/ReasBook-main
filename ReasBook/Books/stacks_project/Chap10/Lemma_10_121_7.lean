import stacks_project.Chap10.Definition_10_121_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [FiniteDimensional K V]

open Submodule

/- Domain triage:
* primary domain: lattices in a fraction-field vector space and the order of vanishing of the
  determinant of a `K`-linear automorphism;
* sampled owner API: `Submodule.IsLattice`, `Submodule.latticeDistance`, `Ring.ordFrac`, and
  `WithZero.log`;
* core/canonical owners: `Submodule.IsLattice K` for latticehood and `Ring.ordFrac R` for the
  multiplicative order of vanishing;
* source-facing bridge: `WithZero.log` is the additive recovery map singled out in
  `Definition_10_121_2`;
* layer: this numbered item is a `bridge/view` theorem comparing the source-facing additive
  lattice distance with the canonical determinant valuation;
* primitive data: the lattice `M` and automorphism `φ`;
* derived API: the raw `Ring.ordFrac` equality is only a companion bridge, while the main theorem
  should live at the additive/source-facing layer.
-/

private instance isLattice_map_restrictScalars
    (φ : V ≃ₗ[K] V) (M : Submodule R V) [IsLattice K M] :
    IsLattice K (M.map ((φ.restrictScalars R) : V →ₗ[R] V)) where
  fg := by
    -- A lattice image stays finitely generated because `Submodule.map` preserves finite generation.
    exact IsLattice.fg.map ((φ.restrictScalars R) : V →ₗ[R] V)
  span_eq_top := by
    let φR : V ≃ₗ[R] V := φ.restrictScalars R
    have himage :
        (φ : V →ₗ[K] V) '' (M : Set V) =
          ((M.map ((φ.restrictScalars R) : V →ₗ[R] V) : Submodule R V) : Set V) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Submodule.mem_map_of_mem hy
      · intro hx
        refine ⟨φ.symm x, ?_, by simp⟩
        simpa [φR] using
          (Submodule.mem_map_equiv
            (p := M) (e := φR) (x := x)).mp hx
    -- Map the spanning equality for `M` across the `K`-linear automorphism.
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := φ.surjective x
    have hy : y ∈ Submodule.span K (M : Set V) := by
      rw [IsLattice.span_eq_top]
      trivial
    have hφy : φ y ∈ (Submodule.span K (M : Set V)).map (φ : V →ₗ[K] V) :=
      Submodule.mem_map_of_mem hy
    rw [Submodule.map_span, himage] at hφy
    exact hφy

-- Proof sketch: first prove the canonical multiplicative bridge in `Ring.ordFrac`, then pass to
-- the additive textbook order of vanishing by applying `WithZero.log` as in
-- `Definition_10_121_2`.
/-- Companion bridge: the lattice-distance identity expressed directly in the canonical
`Ring.ordFrac` owner. -/
theorem exp_latticeDistance_image_eq_ordFrac_det
    [Ring.KrullDimLE 1 R] (φ : V ≃ₗ[K] V) (M : Submodule R V) [IsLattice K M] :
    WithZero.exp (latticeDistance M (M.map ((φ.restrictScalars R) : V →ₗ[R] V))) =
      Ring.ordFrac R (LinearEquiv.det φ : K) := by
  -- TODO: first prove lattice-independence and multiplicativity without importing the currently
  -- broken earlier file `Lemma_10_121_6`, then reduce to standard generators in `K^n`.
  sorry

/-- Lemma 10.121.7: for a lattice `M` in a finite-dimensional `K`-vector space, the lattice
distance between `M` and its image under a `K`-linear automorphism `φ` equals the additive order
of vanishing of `det φ`, recovered from the canonical `Ring.ordFrac` owner by `WithZero.log`. -/
theorem latticeDistance_image_eq_ordFrac_det
    [Ring.KrullDimLE 1 R] (φ : V ≃ₗ[K] V) (M : Submodule R V) [IsLattice K M] :
    latticeDistance M (M.map ((φ.restrictScalars R) : V →ₗ[R] V)) =
      WithZero.log (Ring.ordFrac R (LinearEquiv.det φ : K)) := by
  simpa using congrArg WithZero.log (exp_latticeDistance_image_eq_ordFrac_det φ M)

end
