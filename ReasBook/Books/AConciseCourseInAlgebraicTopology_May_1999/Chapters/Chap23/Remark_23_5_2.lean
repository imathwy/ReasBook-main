import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

-- Semantic recall: Chapter 23 now keeps the all-ranks comparison
-- `thomDiskQuotientEquivThomSpace` as the primary owner for Definition 23.5.1 (2), while
-- `thomDiskSphereQuotientHomeomorphThomSpace` is its positive-rank disk/sphere companion. This
-- remark records the symmetric source-facing homeomorphism from `T(ξ)` to the disk/sphere
-- quotient model.

section

variable {B : Type u} {n : ℕ} {E : B → Type v}
variable [normAddE : ∀ b, NormedAddCommGroup (E b)] [normSpaceE : ∀ b, NormedSpace ℝ (E b)]
variable [tB : TopologicalSpace B]
variable [tTot : TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [tE : ∀ b, TopologicalSpace (E b)] [fBun : FiberBundle (Fin n → ℝ) E]
variable [hvb : VectorBundle ℝ (Fin n → ℝ) E]

/-- Remark 23.5.2: for a metric bundle, the Thom space `T(ξ)` is homeomorphic to the quotient of
the unit disk bundle by the unit sphere bundle. -/
noncomputable abbrev thomSpaceHomeomorphThomDiskSphereQuotient (hn : 0 < n)
    (hnorm : Continuous fun x : Bundle.TotalSpace (Fin n → ℝ) E ↦ ‖x.2‖) :
    ThomSpace n E ≃ₜ ThomDiskSphereQuotient n E :=
  -- Reuse the positive-rank disk/sphere quotient model from Definition 23.5.1 and reverse it.
  (@thomDiskSphereQuotientHomeomorphThomSpace B n E
      normAddE normSpaceE tB tTot tE fBun
      hvb hn hnorm).symm

/-- The forward map of `thomSpaceHomeomorphThomDiskSphereQuotient` is the canonical
Thom-space-to-disk/sphere-quotient comparison map. -/
theorem thomSpaceHomeomorphThomDiskSphereQuotient_toFun (hn : 0 < n)
    (hnorm : Continuous fun x : Bundle.TotalSpace (Fin n → ℝ) E ↦ ‖x.2‖) :
    (thomSpaceHomeomorphThomDiskSphereQuotient hn hnorm).toFun =
      @thomSpaceToThomDiskSphereQuotient B n E
        normAddE normSpaceE tB tTot tE fBun
        hvb hn := by
  -- Unfold the wrapper once so the forward map is definitionally the canonical comparison map.
  rfl

/-- The homeomorphism `thomSpaceHomeomorphThomDiskSphereQuotient` acts by the canonical
Thom-space-to-disk/sphere-quotient comparison map. -/
@[simp] theorem thomSpaceHomeomorphThomDiskSphereQuotient_apply (hn : 0 < n)
    (hnorm : Continuous fun x : Bundle.TotalSpace (Fin n → ℝ) E ↦ ‖x.2‖) (x : ThomSpace n E) :
    thomSpaceHomeomorphThomDiskSphereQuotient hn hnorm x =
      @thomSpaceToThomDiskSphereQuotient B n E
        normAddE normSpaceE tB tTot tE fBun
        hvb hn x := by
  -- Evaluate the homeomorphism through its forward-map computation rule.
  rfl

/-- The inverse map of `thomSpaceHomeomorphThomDiskSphereQuotient` is the canonical
disk/sphere-quotient-to-Thom comparison map. -/
theorem thomSpaceHomeomorphThomDiskSphereQuotient_symm_toFun (hn : 0 < n)
    (hnorm : Continuous fun x : Bundle.TotalSpace (Fin n → ℝ) E ↦ ‖x.2‖) :
    ((thomSpaceHomeomorphThomDiskSphereQuotient hn hnorm).symm).toFun =
      thomDiskSphereQuotientToThomSpace n E := by
  -- Route correction: `((e.symm).symm)` does not reduce definitionally far enough here, so
  -- transport the computation rule from Definition 23.5.1 instead of forcing `rfl`.
  simpa [thomSpaceHomeomorphThomDiskSphereQuotient] using
    (@thomDiskSphereQuotientHomeomorphThomSpace_toFun B n E
      normAddE normSpaceE tB tTot tE fBun
      hvb hn hnorm)

/- The inverse homeomorphism is definitionally `thomDiskSphereQuotientHomeomorphThomSpace`, but
the reusable companion surface is its action by the canonical quotient-to-Thom map. -/
@[simp] theorem thomSpaceHomeomorphThomDiskSphereQuotient_symm_apply (hn : 0 < n)
    (hnorm : Continuous fun x : Bundle.TotalSpace (Fin n → ℝ) E ↦ ‖x.2‖)
    (x : ThomDiskSphereQuotient n E) :
    (thomSpaceHomeomorphThomDiskSphereQuotient hn hnorm).symm x =
      thomDiskSphereQuotientToThomSpace n E x := by
  -- Evaluate the inverse by applying the function-level companion theorem at `x`.
  exact
    congrArg (fun f : ThomDiskSphereQuotient n E → ThomSpace n E ↦ f x)
      (thomSpaceHomeomorphThomDiskSphereQuotient_symm_toFun (B := B) (n := n) (E := E) hn hnorm)

end
