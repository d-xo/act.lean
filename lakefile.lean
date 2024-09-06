import Lake
open Lake DSL

package "act" where
  -- add package configuration options here

lean_lib «Act» where
  -- add library configuration options here

@[default_target]
lean_exe "act" where
  root := `Main
