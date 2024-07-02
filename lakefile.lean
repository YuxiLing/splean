import Lake
open Lake DSL

package lean_lgtm where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require batteries from
    git "https://github.com/leanprover-community/batteries" @ "main"
require mathlib from
    git "https://github.com/leanprover-community/mathlib4.git" @ "master"
-- require loogle from git "https://github.com/nomeata/loogle.git" @ "master"
require ssreflect from
    git "https://github.com/verse-lab/lean-ssr.git" @ "master"

@[default_target]
lean_lib LeanLgtm where
  -- add any library configuration options here
