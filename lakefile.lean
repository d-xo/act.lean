import Lake
open Lake DSL

package "act" where
  -- add package configuration options here

lean_lib «Act» where
  -- add library configuration options here

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.11.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.11.0"

@[default_target]
lean_exe "act" where
  root := `Main
