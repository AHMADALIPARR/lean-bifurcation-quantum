import Lake
open Lake DSL

package «lean-bifurcation-quantum» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.9.0"

@[default_target]
lean_lib «LeanBifurcationQuantum» where
  -- Modules are independent (each defines its own `ShadowState`), so they are
  -- listed as separate roots rather than imported from one umbrella file.
  roots := #[`LeanBifurcationQuantum.BifurcationLemmas,
             `LeanBifurcationQuantum.GodelBifurcation,
             `LeanBifurcationQuantum.EverettManyWorlds,
             `LeanBifurcationQuantum.EinsteinRosenBridge,
             `LeanBifurcationQuantum.CommutativeTorus]
