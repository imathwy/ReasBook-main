import StacksProject_2024.stacks_project.Chap05.Lemma_5_8_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace Topology

/-
Domain-style sampling for soberification and spectral transfer:
- primary domain: soberification via `IrreducibleCloseds X`, viewed through the lattice of open
  subsets;
- sampled owner declarations:
  `toIrreducibleCloseds_opensComap_bijective`,
  `TopologicalSpace.Opens.comap`,
  `PrespectralSpace.isBasis_opens`,
  `QuasiSeparatedSpace.inter_isCompact`;
- best owner abstraction: the key owner here is the order isomorphism on opens induced by
  `toIrreducibleCloseds`; compactness, Noetherianity, prespectrality, quasi-separatedness, and
  spectrality of `IrreducibleCloseds X` are all derived API transported across that owner;
- primitive-vs-derived split: the primitive data for this file is only the open-lattice
  equivalence; the various topological typeclass instances are derived from it and should not be
  packaged as separate wrapper data.

Layer triage:
- `source-facing`: the Stacks claims that soberification preserves quasi-compactness, the compact
  open basis, quasi-separatedness, and Noetherianity;
- `core/canonical`: `Opens`, `CompactSpace`, `NoetherianSpace`, `PrespectralSpace`,
  `QuasiSeparatedSpace`, and `SpectralSpace`;
- `bridge/view`: `toIrreducibleCloseds` and the induced order isomorphism on opens.
-/

section

variable {X : Type u} [TopologicalSpace X]

-- Proof sketch: the soberification map induces a bijection on opens. Since this bijection commutes
-- with arbitrary unions, quasi-compactness of the soberification space transfers across it, so
-- compactness of `X` gives compactness of `IrreducibleCloseds X`.
/-- Lemma 5.23.15 (1): if `X` is quasi-compact, then the soberification space
`IrreducibleCloseds X` is quasi-compact. In Lean this is the canonical `CompactSpace`
instance. -/
instance irreducibleCloseds_compactSpace [CompactSpace X] :
    CompactSpace (IrreducibleCloseds X) := sorry

-- Proof sketch: the open-bijection property of the soberification map transfers compact opens and
-- their pairwise intersections from `X` to `IrreducibleCloseds X`. Together with the quasi-sober
-- and `T₀` structure from Lemma 5.8.16 and compactness from part (1), this yields a spectral
-- structure on `IrreducibleCloseds X`.
/-- Lemma 5.23.15 (2): if `X` is quasi-compact, has a basis of quasi-compact opens, and the
intersection of two quasi-compact opens is quasi-compact, then `IrreducibleCloseds X` is
spectral. The textbook hypotheses are expressed canonically by
`[CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]`. -/
instance irreducibleCloseds_spectralSpace [CompactSpace X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] : SpectralSpace (IrreducibleCloseds X) := sorry

-- Proof sketch: the soberification map gives a bijection on opens, so the ascending chain
-- condition on open subsets transfers from `X` to `IrreducibleCloseds X`.
/-- The soberification space `IrreducibleCloseds X` of a Noetherian space is again Noetherian. -/
instance irreducibleCloseds_noetherianSpace [NoetherianSpace X] :
    NoetherianSpace (IrreducibleCloseds X) := sorry

-- Proof sketch: combine the transferred Noetherianity of `IrreducibleCloseds X` with the
-- quasi-sober and `T₀` properties from Lemma 5.8.16. Mathlib's Noetherian-space instances provide
-- compactness, a basis of compact opens, and quasi-separatedness, so `IrreducibleCloseds X` is
-- spectral as well.
/-- Lemma 5.23.15 (3): if `X` is Noetherian, then `IrreducibleCloseds X` is a Noetherian
spectral space. -/
theorem irreducibleCloseds_noetherian_and_spectral [NoetherianSpace X] :
    NoetherianSpace (IrreducibleCloseds X) ∧ SpectralSpace (IrreducibleCloseds X) := by
  exact ⟨inferInstance, inferInstance⟩

end
