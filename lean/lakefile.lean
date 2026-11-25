import Lake
open Lake DSL

package «KoszulWordle» where
  srcDir := "."

@[default_target]
lean_lib «KoszulWordle» where
  roots := #[`KoszulWordle]
