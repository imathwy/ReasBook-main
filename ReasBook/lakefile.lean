import Lake
open Lake DSL

package «ReasBook» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩,
    ⟨`weak.linter.style.longLine, false⟩,
    ⟨`weak.linter.style.emptyLine, false⟩,
    ⟨`weak.linter.style.cdot, false⟩,
    ⟨`weak.linter.style.maxHeartbeats, false⟩,
    ⟨`weak.linter.unnecessarySimpa, false⟩
  ]

-- Keep documentation and literate extraction on the same Lean release as the
-- formalization project.
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.30.0-rc1"

require subverso from git
  "https://github.com/leanprover/subverso" @ "52b9dfbd2658408e37ae6e8b72601ddeaaa25a0c"
require MD4Lean from git
  "https://github.com/acmepjz/md4lean" @ "6a3fb240133bcb7e1a066fdc784b3fdc304e3fc5"

-- Keep Mathlib last so its dependency pins take precedence over the
-- documentation packages' transitive pins.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc1"

@[default_target]
lean_lib «ReasBook» where

lean_lib Books where

lean_exe "literate-extract" where
  root := `LiterateExtract
  supportInterpreter := true

module_facet literate mod : System.FilePath := do
  let ws ← getWorkspace

  let exeJob ← «literate-extract».fetch
  let modJob ← mod.olean.fetch

  let buildDir := ws.root.buildDir
  let hlFile := mod.filePath (buildDir / "literate") "json"

  exeJob.bindM fun exeFile =>
    modJob.mapM fun _oleanPath => do
      buildFileUnlessUpToDate' (text := true) hlFile <|
        proc {
          cmd := exeFile.toString
          args := #[mod.name.toString, hlFile.toString]
          env := ← getAugmentedEnv
        }
      pure hlFile

library_facet literate lib : Array System.FilePath := do
  let mods ← (← lib.modules.fetch).await
  let modJobs ← mods.mapM (·.facet `literate |>.fetch)
  let out ← modJobs.mapM (·.await)
  pure (.pure out)
