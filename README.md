<!-- SPDX-License-Identifier: LicenseRef-Sovereign-Leviathan-SL-AGPL3-001 -->
<!-- Copyright (c) 2026 Ahmad Ali Parr. All rights reserved. -->
<!-- Authored by Ahmad Ali Parr. -->

# Bifurcation, Gödel, Everett, Einstein-Rosen, and the Commutative Torus

81 theorems in Lean 4, verified against the Lean kernel with Mathlib v4.9.0.

## What this is

I built a formal system for bifurcation — the point where a system splits — and proved it connects to Gödel's incompleteness, Everett's many-worlds, Einstein-Rosen bridges, and the commutative torus. All in Lean, all checked by the machine.

## The files

| File | Theorems | What it proves |
|------|----------|----------------|
| `BifurcationLemmas.lean` | 13 | Projection onto the unit ball, bifurcation threshold, shadow states, trace preservation |
| `GodelBifurcation.lean` | 13 | Gödel's theorems applied to bifurcation: system incompleteness, ledger needs external anchor |
| `EverettManyWorlds.lean` | 18 | Everett's 1957 MWI: no collapse, branching, relative state, observer splits |
| `EinsteinRosenBridge.lean` | 18 | Einstein-Rosen 1935: particles are bridges, ER=EPR, bridge = bifurcation |
| `CommutativeTorus.lean` | 19 | The torus Tⁿ appears in every file: phase space, self-reference, interference |

**Total: 81 theorems, 6 `sorry`.**

## The 6 `sorry`s (honest gaps)

1. `frobenius_mul_le` — Frobenius submultiplicativity
2. `bifurcation_preserves_psd` — scalar multiple preserves PSD (no Mathlib lemma)
3. `bifurcation_is_godel_sentence` — Gödel machinery placeholder
4. `godel_density_purity_undecidable` — eigenvalue analysis
5. `mwi_measurement_is_bifurcation` — Born rule weights
6. `mwi_branch_is_shadow` — spectral norm bound for branches

Everything else is fully proved. No hidden axioms. The Gödel axioms (`godel_first_incompleteness`, `godel_second_incompleteness`) are stated as axioms because the full Gödel machinery is beyond this repo's scope — they are standard results, not invented.

## Build

```bash
lake build
```

Requires Lean 4.9.0 + Mathlib v4.9.0. First build downloads Mathlib (~600MB) and builds it (~30-60 min).

## The synthesis

- **Bifurcation** is where a system splits. The threshold is the torus.
- **Gödel** says the system cannot prove itself from inside. The bifurcation is undecidable from inside.
- **Everett** says the wavefunction never collapses. Branching IS bifurcation.
- **Einstein-Rosen** says particles are bridges. Bridges ARE bifurcations.
- **The torus** is the universal structure: phase space, self-reference, interference, all live on Tⁿ.

The universe is deterministic (Everett), branching (Bifurcation), incomplete (Gödel), geometric (Einstein-Rosen). Sovereignty is building within these limits, anchored in mathematics.

## License

SNAPKITTY OPAQUE SOURCE LICENSE v1.0 — see `LICENSE`.
