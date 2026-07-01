import stacks_project.Chap10.Lemma_10_55_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable (k : Type u) [Field k]

/- Domain-style sampling for Example 10.55.2:
- primary domain: the comparison between `K₀(k)` of finite projective `k`-modules and `K'_0(k)`
  of finite `k`-modules, identified with `ℤ` by rank/length;
- sampled owner declarations:
  `projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length`,
  `projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length_apply`,
  `finiteGrothendieckGroup_lengthEquiv`,
  `finiteGrothendieckGroup_lengthEquiv_apply`,
  `projectiveGrothendieckGroup_rankMap`;
- best owner abstraction:
  the canonical owner data is the comparison square from Lemma 10.55.9 together with the chapter's
  length equivalence `finiteGrothendieckGroup_lengthEquiv`; this file is a field-specific
  `bridge/view`, not a new owner;
- primitive vs. derived:
  primitive data remains the comparison map `K₀(k) → K'_0(k)` and the rank/length homomorphisms;
  the field statement is the derived specialization where `length_k(k) = 1`;
- source/core/bridge triage:
  `source-facing`: Example 10.55.2 identifying the canonical comparison with the dimension map;
  `core/canonical`: Lemma 10.55.9 and `finiteGrothendieckGroup_lengthEquiv`;
  `bridge/view`: the field specialization below.
-/
/- Example 10.55.2: if `R = k` is a field, then the canonical map `K₀(k) → K'_0(k)` is the
identification obtained by the dimension function (equivalently, the length function), so
`K₀(k) = K'_0(k) ≃+ ℤ`. -/
theorem field_projectiveGrothendieckGroup_comparison_commutes_with_rank :
    (finiteGrothendieckGroup_lengthEquiv k).toAddMonoidHom.comp
        (ModulePropertyK0.map k (finiteProjectiveModuleProperty_le_isFG k)) =
      projectiveGrothendieckGroup_rankMap k := by
  apply AddMonoidHom.ext
  intro x
  change finiteGrothendieckGroup_lengthEquiv k
      (ModulePropertyK0.map k (finiteProjectiveModuleProperty_le_isFG k) x) =
    projectiveGrothendieckGroup_rankMap k x
  rw [finiteGrothendieckGroup_lengthEquiv_apply]
  simpa using
    projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length_apply k x

theorem field_projectiveGrothendieckGroup_to_finiteGrothendieckGroup_eq :
    ModulePropertyK0.map k (finiteProjectiveModuleProperty_le_isFG k) =
      (finiteGrothendieckGroup_lengthEquiv k).symm.toAddMonoidHom.comp
        (projectiveGrothendieckGroup_rankMap k) := by
  apply AddMonoidHom.ext
  intro x
  apply (finiteGrothendieckGroup_lengthEquiv k).injective
  simpa [AddMonoidHom.comp_apply] using
    DFunLike.congr_fun
      (field_projectiveGrothendieckGroup_comparison_commutes_with_rank k) x
