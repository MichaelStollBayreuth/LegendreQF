import Lake
open Lake DSL

package «legendre_QF» {
  -- The files predate the module system; this silences Lake's "consider adding `module`"
  -- warning on every Mathlib import.
  allowNonModules := true
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib «LegendreQF» {
  globs := #[.submodules `LegendreQF]
  -- add any library configuration options here
}
