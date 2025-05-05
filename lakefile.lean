import Lake
open Lake DSL

package «legendre_QF» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"

@[default_target]
lean_lib «LegendreQF» {
  globs := #[.submodules `LegendreQF]
  -- add any library configuration options here
}
