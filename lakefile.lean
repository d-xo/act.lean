import Lake
open Lake DSL

package "act-lean" where
  -- add package configuration options here

lean_lib «Act».«Lean» where
  -- add library configuration options here

@[default_target]
lean_exe "act-lean" where
  root := `Main
