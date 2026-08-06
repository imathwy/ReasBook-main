# A Concise Course in Algebraic Topology

Lean formalization of J. Peter May's *A Concise Course in Algebraic Topology*,
University of Chicago Press, 1999.

- Contributor: Ze Yuan
- Lean: 4.29.1
- Mathlib: `5e932f97dd25535344f80f9dd8da3aab83df0fe6`
- Chapters: 25
- Numbered sections: 159
- Migrated source modules: 1116
- Total Lean files: 1300

## Formalization Status

- Source items: 985
- Items whose main labeled statements contain no `sorry`: 732 (74.3%)
- Items with at least one main labeled statement containing `sorry`: 253 (25.7%)
- Main labeled declarations containing `sorry`: 364
- `sorry` placeholders in those declarations: 383

An item is identified by its source label, such as `Theorem 25.5.2`. A main
statement is a Lean declaration directly attached to a comment beginning with
that label; one item may contain several numbered main statements. The counts
exclude supporting declarations, development probes, comments that merely
mention `sorry`, and `sorry` declarations occurring only in helper lemmas.

## Migration Notes

The formal source files were migrated from the JPMay project without changing
their proof bodies. Imports under `MayConciseRevised` were rewritten to use the
ReasBook prefix `Books.AConciseCourseInAlgebraicTopology_May_1999`.

The source project contains 1180 occurrences of `sorry`; the migrated project
contains the same number. No proof was replaced with `sorry`, and no explicit
`axiom` declaration was introduced during migration.

Three unreferenced development probes were intentionally excluded:

- `__tmp_Lemma_1_5_10_probe.lean`
- `def2417probewldGAG.lean`
- `def2425probedSOjUD.lean`

## Organization

- `Book.lean` indexes all 25 chapter modules.
- `Chapters/ChapXX.lean` indexes the numbered sections in a chapter.
- `Chapters/ChapXX/sectionYY.lean` lists the independent source units belonging
  to a section.
- The remaining files contain the migrated definitions, statements, proofs,
  and supporting APIs.

The theorem files remain independent compilation units. Importing all of them
into one environment would merge declarations that were intentionally local to
separate source units. The `Books` Lake target uses submodule globs and is a
default target, so `lake build` checks every source file without merging those
environments.

## Build

From the repository root:

```bash
cd ReasBook
lake build
```

To build the books library explicitly:

```bash
cd ReasBook
lake build Books
```

To check an individual theorem file:

```bash
cd ReasBook
lake env lean Books/AConciseCourseInAlgebraicTopology_May_1999/Chapters/Chap25/Theorem_25_5_2.lean
```

The build emits warnings for source-level `sorry` declarations and existing
linter findings. These warnings do not indicate migration errors.

## Chapters

- [Chapter 01](./Chapters/Chap01/)
- [Chapter 02](./Chapters/Chap02/)
- [Chapter 03](./Chapters/Chap03/)
- [Chapter 04](./Chapters/Chap04/)
- [Chapter 05](./Chapters/Chap05/)
- [Chapter 06](./Chapters/Chap06/)
- [Chapter 07](./Chapters/Chap07/)
- [Chapter 08](./Chapters/Chap08/)
- [Chapter 09](./Chapters/Chap09/)
- [Chapter 10](./Chapters/Chap10/)
- [Chapter 11](./Chapters/Chap11/)
- [Chapter 12](./Chapters/Chap12/)
- [Chapter 13](./Chapters/Chap13/)
- [Chapter 14](./Chapters/Chap14/)
- [Chapter 15](./Chapters/Chap15/)
- [Chapter 16](./Chapters/Chap16/)
- [Chapter 17](./Chapters/Chap17/)
- [Chapter 18](./Chapters/Chap18/)
- [Chapter 19](./Chapters/Chap19/)
- [Chapter 20](./Chapters/Chap20/)
- [Chapter 21](./Chapters/Chap21/)
- [Chapter 22](./Chapters/Chap22/)
- [Chapter 23](./Chapters/Chap23/)
- [Chapter 24](./Chapters/Chap24/)
- [Chapter 25](./Chapters/Chap25/)
