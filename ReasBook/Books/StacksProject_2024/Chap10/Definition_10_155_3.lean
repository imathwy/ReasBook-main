import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling pass for Definition 10.155.3.

Primary domain: local commutative algebra of henselizations and strict henselizations.

Sampled owner declarations:
* `HenselianLocalRing`;
* `StrictHenselianLocalRing`;
* `IsHenselizationOf`;
* `IsStrictHenselizationOf`.

Owner abstraction: the source-facing owners for this item already exist upstream in the chapter as
`IsHenselizationOf` and `IsStrictHenselizationOf`, built from the canonical local-ring owners
above. This file should therefore be recall-only, not a second wrapper layer.

Primitive data vs derived API:
* primitive owner data live in `IsHenselizationOf` and `IsStrictHenselizationOf`;
* existence theorems and residue-field comparison maps are derived API in
  `Lemma_10_155_1` and `Lemma_10_155_2`.

Source/core/bridge triage:
* source-facing: `IsHenselizationOf`, `IsStrictHenselizationOf`;
* core/canonical: `HenselianLocalRing`, `StrictHenselianLocalRing`, `IsLocalHom`,
  `RingHom.IsFilteredColimitOfEtale`;
* bridge/view: the existence theorems and residue-field comparison data attached to those owners.
-/

/- Definition 10.155.3: the henselization of a local ring is the canonical project notion
`IsHenselizationOf R S`, expressing that the local map `R → S` constructed in Lemma 10.155.1 is a
henselian local étale-neighborhood colimit with unchanged residue field. -/
#check IsHenselizationOf

/- Companion recall: the strict henselization of a local ring is the canonical project notion
`IsStrictHenselizationOf R S`, expressing the local maps produced in Lemma 10.155.2 after choosing
a separable closure of the residue field. -/
#check IsStrictHenselizationOf
