import Lake
open Lake DSL

package «lean-christina» where
  -- add package configuration options here

lean_lib «LeanChristina» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-christina» where
  root := `Main
