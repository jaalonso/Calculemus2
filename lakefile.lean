import Lake
open Lake DSL

package «Calculemus2» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Calculemus2» {
  -- add any library configuration options here
  globs := #[.submodules `src]
}
