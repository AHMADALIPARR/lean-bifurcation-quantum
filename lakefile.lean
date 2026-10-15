import Lake
open Lake DSL

package «lean-bifurcation-quantum» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.9.0"

@[default_target]
lean_lib «LeanBifurcationQuantum» where
  roots := #[`BifurcationLemmas, `GodelBifurcation, `EverettManyWorlds, `EinsteinRosenBridge, `CommutativeTorus]
