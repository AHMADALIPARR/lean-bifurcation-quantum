<!-- SPDX-License-Identifier: LicenseRef-Sovereign-Leviathan-SL-AGPL3-001 -->
<!-- Copyright (c) 2026 Ahmad Ali Parr. All rights reserved. -->
<!-- Authored by Ahmad Ali Parr. -->

# Bifurcation, Gödel, Everett, Einstein-Rosen, and the Commutative Torus

81 theorems in Lean 4 (toolchain `leanprover/lean4:v4.9.0`, Mathlib `v4.9.0`), checked by the Lean kernel. **0 `sorry`.**

![AI agent branching into sub-agents](assets/agent-branching.png)

*One agent bifurcates into five. Each branch is a theorem file. Each theorem is a world.*

## Overview

I built a formal system for bifurcation — the point where a system splits — and connected it to Gödel's incompleteness, Everett's many-worlds, Einstein-Rosen bridges, and the commutative torus. All in Lean, all checked by the machine. See [Proof status](#proof-status) for exactly what the kernel checks, and the [Theorem atlas](#theorem-atlas) for the map.

| Module | Theorems | Color in image |
|--------|---------:|----------------|
| [`BifurcationLemmas.lean`](LeanBifurcationQuantum/BifurcationLemmas.lean) | 13 | 🔵 Cyan — the foundation |
| [`GodelBifurcation.lean`](LeanBifurcationQuantum/GodelBifurcation.lean) | 13 | 🟣 Violet — incompleteness |
| [`EverettManyWorlds.lean`](LeanBifurcationQuantum/EverettManyWorlds.lean) | 18 | 🟢 Green — branching worlds |
| [`EinsteinRosenBridge.lean`](LeanBifurcationQuantum/EinsteinRosenBridge.lean) | 18 | 🟡 Gold — spacetime bridges |
| [`CommutativeTorus.lean`](LeanBifurcationQuantum/CommutativeTorus.lean) | 19 | 🩷 Magenta — the torus in everything |
| **Total** | **81** | |

## Theorem atlas

Five regions, one map. Bifurcation is the source; every other module draws on it, and the torus runs through all of them.

```mermaid
flowchart LR
    B["🔵 Bifurcation<br/>13 theorems"]
    G["🟣 Gödel<br/>13 theorems"]
    E["🟢 Everett<br/>18 theorems"]
    R["🟡 Einstein-Rosen<br/>18 theorems"]
    T["🩷 Commutative Torus<br/>19 theorems"]
    B --> G
    B --> E
    B --> R
    G --> E
    G --> R
    E --> R
    B --> T
    G --> T
    E --> T
    R --> T
```

**Legend.** ✅ Lean statement proved, standard axioms only · 🔷 Lean statement proved using a declared Gödel axiom · ○ concludes `True`; the content is the interpretation in the docstring. In every row the kernel checks the Lean statement; the *Meaning* column is the reading.

| Region | ✅ | 🔷 | ○ | Total |
|---|--:|--:|--:|--:|
| 🔵 [The Foundation](#bifurcationlemmas) | 13 | 0 | 0 | 13 |
| 🟣 [Incompleteness](#godelbifurcation) | 5 | 6 | 2 | 13 |
| 🟢 [Many-Worlds](#everettmanyworlds) | 6 | 0 | 12 | 18 |
| 🟡 [Wormholes](#einsteinrosenbridge) | 12 | 0 | 6 | 18 |
| 🩷 [The Torus in Everything](#commutativetorus) | 0 | 0 | 19 | 19 |
| **All** | **36** | **6** | **39** | **81** |

<a id="bifurcationlemmas"></a>

### 🔵 The Foundation — [`BifurcationLemmas.lean`](LeanBifurcationQuantum/BifurcationLemmas.lean)

> *No matter how wild the step, projection catches it.*

The core: projection, bifurcation, shadow states, quantum basics.

$$\lVert \mathrm{projB}(M) \rVert \le 1 \qquad \lVert AB \rVert_F \le \lVert A \rVert_F \, \lVert B \rVert_F$$

<details>
<summary>Definitions</summary>

> **Note on the norm.** Despite the name `FrobeniusBall`, the norm ‖·‖ in this file is Mathlib's `Matrix.normedAddCommGroup`, the **entrywise sup norm** ‖M‖ = maxᵢⱼ |Mᵢⱼ|. Only `frobenius_mul_le` uses the Frobenius norm, through the explicit helper `frobNorm`.

- **`FrobeniusBall`** — The set of matrices with norm ≤ 1. The "ball" the system lives in. Inside = kenoma (unformed). Boundary = threshold. Outside = projected back.
- **`projB`** — Projection onto the unit ball. If ‖M‖ ≤ 1, return M. Otherwise scale down to norm 1. This is the bifurcation operator: it forces the system back into bounds.
- **`ShadowState`** — A PSD matrix with norm ≤ 1. The state of a system that casts a shadow it cannot see (see Gödel file).
- **`DensityMatrix`** — A PSD matrix with trace = 1. A valid quantum state.

</details>

| | Theorem | Meaning |
|:-:|---|---|
| ✅ | [`projB_in_ball`](LeanBifurcationQuantum/BifurcationLemmas.lean#L42) | Projection always lands in the ball. |
| ✅ | [`projB_idempotent`](LeanBifurcationQuantum/BifurcationLemmas.lean#L58) | Projecting twice = projecting once. |
| ✅ | [`bifurcation_small_step`](LeanBifurcationQuantum/BifurcationLemmas.lean#L78) | If the step size η is small enough (η·‖grad‖ < 1 − ‖S‖), the state stays in the ball *without* projection. |
| ✅ | [`bifurcation_projected_step`](LeanBifurcationQuantum/BifurcationLemmas.lean#L95) | No matter how large the step, `projB` brings it back. |
| ✅ | [`bifurcation_threshold`](LeanBifurcationQuantum/BifurcationLemmas.lean#L102) | There exists an η* where ‖S‖ + η*·‖grad‖ = 1 exactly. |
| ✅ | [`bifurcation_below_threshold`](LeanBifurcationQuantum/BifurcationLemmas.lean#L113) | Below the threshold, `projB` is the identity. |
| ✅ | [`bifurcation_above_threshold`](LeanBifurcationQuantum/BifurcationLemmas.lean#L125) | Above the threshold, `projB` scales. |
| ✅ | [`trace_unitary_conj`](LeanBifurcationQuantum/BifurcationLemmas.lean#L145) | Trace is preserved under unitary conjugation: trace(U·ρ·U†) = trace(ρ). |
| ✅ | [`frobenius_mul_le`](LeanBifurcationQuantum/BifurcationLemmas.lean#L172) | The Frobenius norm is submultiplicative: ‖AB‖_F ≤ ‖A‖_F·‖B‖_F, stated with `frobNorm` and proved via Mathlib's `Matrix.frobenius_norm_mul`. |
| ✅ | [`bifurcation_preserves_psd`](LeanBifurcationQuantum/BifurcationLemmas.lean#L178) | If S and grad are PSD, then S + η·grad is PSD for η > 0. |
| ✅ | [`shadow_invariant_preserved`](LeanBifurcationQuantum/BifurcationLemmas.lean#L193) | The shadow invariant (‖S‖ ≤ 1) is preserved under projected steps. |
| ✅ | [`shadow_two_step`](LeanBifurcationQuantum/BifurcationLemmas.lean#L200) | After two projected steps, still in the ball. |
| ✅ | [`shadow_iterate_bounded`](LeanBifurcationQuantum/BifurcationLemmas.lean#L207) | Any finite sequence of projected steps stays bounded. |

<a id="godelbifurcation"></a>

### 🟣 Incompleteness — [`GodelBifurcation.lean`](LeanBifurcationQuantum/GodelBifurcation.lean)

> *“I cannot prove this, so I will force it.”*

Gödel's theorems applied to the bifurcation system. The system cannot prove itself from inside.

$$\mathrm{Tr}(\rho^2) \le 1 \quad \text{for } \rho \succeq 0,\ \mathrm{Tr}\,\rho = 1$$

<details>
<summary>Definitions</summary>

- **`FormalSystem`** — A formal system: expresses arithmetic, has a provability predicate, is consistent (doesn't prove False).
- **`BifurcationSystem`** — The bifurcation system as a formal system. Placeholder provability (proves nothing, trivially consistent).

**Declared axioms** (standard results, stated without proof):

- **`godel_first_incompleteness`** — Any consistent formal system expressing arithmetic has a Gödel sentence: true but unprovable in the system.
- **`godel_second_incompleteness`** — No consistent formal system can prove its own consistency.

</details>

| | Theorem | Meaning |
|:-:|---|---|
| 🔷 | [`godel_bifurcation_incomplete`](LeanBifurcationQuantum/GodelBifurcation.lean#L89) | The bifurcation system is incomplete. |
| 🔷 | [`godel_bifurcation_cannot_prove_consistency`](LeanBifurcationQuantum/GodelBifurcation.lean#L98) | The bifurcation system cannot prove its own projection rules are consistent. |
| ✅ | [`bifurcation_is_godel_sentence`](LeanBifurcationQuantum/GodelBifurcation.lean#L107) | At the threshold η*, "this step stays in the ball" is true but the system cannot prove it without stepping outside itself. |
| 🔷 | [`godel_quantum_observer_limit`](LeanBifurcationQuantum/GodelBifurcation.lean#L139) | An observer inside the system cannot fully describe the system. |
| ✅ | [`godel_density_purity_undecidable`](LeanBifurcationQuantum/GodelBifurcation.lean#L171) | A density matrix cannot prove from inside if it's pure (rank 1) vs mixed. |
| ✅ | [`godel_spectral_self_reference`](LeanBifurcationQuantum/GodelBifurcation.lean#L190) | "‖ρ‖ ≤ 1" is provable, but "this proof is correct" needs a meta-system. |
| 🔷 | [`godel_ledger_cannot_prove_immutability`](LeanBifurcationQuantum/GodelBifurcation.lean#L202) | Formal version of the hologram-wat correction: "actually immutable" → "tamper-evident." Gödel's Second Theorem applied to ledgers. |
| 🔷 | [`godel_shadow_incomplete`](LeanBifurcationQuantum/GodelBifurcation.lean#L222) | Shadow states are incomplete. |
| ✅ | [`godel_shadow_cannot_see_itself`](LeanBifurcationQuantum/GodelBifurcation.lean#L233) | A shadow state cannot prove it is a shadow state from within the formalism. |
| ✅ | [`godel_bifurcation_undecidable`](LeanBifurcationQuantum/GodelBifurcation.lean#L247) | The system cannot decide from inside whether the next step will bifurcate without actually taking the step. |
| 🔷 | [`godel_needs_external_anchor`](LeanBifurcationQuantum/GodelBifurcation.lean#L302) | Every formal system needs an external anchor. |

<details>
<summary>○ 2 interpretive theorems (conclude <code>True</code>)</summary>

| | Theorem | Meaning |
|:-:|---|---|
| ○ | [`godel_projection_is_escape`](LeanBifurcationQuantum/GodelBifurcation.lean#L259) | `projB` is the system's way of handling its own incompleteness. |
| ○ | [`godel_bifurcation_is_anchor`](LeanBifurcationQuantum/GodelBifurcation.lean#L311) | At the bifurcation threshold, the system must choose: appeal to mathematics (external) or collapse (internal). |

</details>

<a id="everettmanyworlds"></a>

### 🟢 Many-Worlds — [`EverettManyWorlds.lean`](LeanBifurcationQuantum/EverettManyWorlds.lean)

> *The wavefunction never collapses. Every outcome occurs in a different branch.*

Hugh Everett III, 1957, Princeton (advisor: John Archibald Wheeler). The wavefunction never collapses. Every outcome occurs in a different branch.

$$\sum_{k=1}^{N} \left(\frac{a}{\sqrt{N}}\right)^2 = a^2$$

<details>
<summary>Definitions</summary>

- **`Branch`** — A component of the universal wavefunction after measurement. Has a relative state, an amplitude (Born weight), normalized (trace = 1), PSD.
- **`UniversalWavefunction`** — A collection of branches with weights summing to 1 (Born rule). The total universe.

</details>

| | Theorem | Meaning |
|:-:|---|---|
| ✅ | [`everett_branching`](LeanBifurcationQuantum/EverettManyWorlds.lean#L81) | When a measurement occurs, the wavefunction branches. |
| ✅ | [`mwi_measurement_is_bifurcation`](LeanBifurcationQuantum/EverettManyWorlds.lean#L113) | A measurement IS a bifurcation point. |
| ✅ | [`mwi_bifurcation_preserves_weight`](LeanBifurcationQuantum/EverettManyWorlds.lean#L133) | Branching does not create or destroy probability. |
| ✅ | [`mwi_observer_splits`](LeanBifurcationQuantum/EverettManyWorlds.lean#L146) | The observer is part of the system. |
| ✅ | [`mwi_godel_born_rule`](LeanBifurcationQuantum/EverettManyWorlds.lean#L215) | "P(outcome) = \|amplitude\|²" is true from outside, unprovable from inside the branch. |
| ✅ | [`mwi_branch_is_shadow`](LeanBifurcationQuantum/EverettManyWorlds.lean#L262) | Every branch's density matrix is a valid shadow state (PSD + norm ≤ 1). |

<details>
<summary>○ 12 interpretive theorems (conclude <code>True</code>)</summary>

| | Theorem | Meaning |
|:-:|---|---|
| ○ | [`everett_no_collapse`](LeanBifurcationQuantum/EverettManyWorlds.lean#L69) | The universal wavefunction evolves unitarily. |
| ○ | [`everett_relative_state`](LeanBifurcationQuantum/EverettManyWorlds.lean#L95) | The state of a subsystem is only defined relative to the observer's state. |
| ○ | [`mwi_branching_deterministic`](LeanBifurcationQuantum/EverettManyWorlds.lean#L157) | Branching is deterministic (Schrödinger evolution). |
| ○ | [`mwi_godel_observer_blind`](LeanBifurcationQuantum/EverettManyWorlds.lean#L177) | Observer in branch B cannot access other branches. |
| ○ | [`mwi_godel_universe_cannot_prove_itself`](LeanBifurcationQuantum/EverettManyWorlds.lean#L191) | The universal wavefunction cannot prove its own consistency from within. |
| ○ | [`mwi_godel_branch_count_undecidable`](LeanBifurcationQuantum/EverettManyWorlds.lean#L204) | Observer sees one branch, cannot count total from inside. |
| ○ | [`mwi_universal_is_sum_of_shadows`](LeanBifurcationQuantum/EverettManyWorlds.lean#L286) | The universal wavefunction is the weighted sum of all branch shadow states, weights = Born probabilities. |
| ○ | [`mwi_shadow_projection_is_branch_selection`](LeanBifurcationQuantum/EverettManyWorlds.lean#L298) | `projB` is the mathematical analogue of branch selection. |
| ○ | [`mwi_ledger_branches`](LeanBifurcationQuantum/EverettManyWorlds.lean#L317) | When the wavefunction branches, the ledger branches too. |
| ○ | [`mwi_ledger_cross_branch_unverifiable`](LeanBifurcationQuantum/EverettManyWorlds.lean#L329) | Observer in branch A cannot verify the ledger of branch B. |
| ○ | [`mwi_ledger_universal_is_union`](LeanBifurcationQuantum/EverettManyWorlds.lean#L339) | The complete history is the union of all branch histories. |
| ○ | [`everett_godel_bifurcation_synthesis`](LeanBifurcationQuantum/EverettManyWorlds.lean#L386) | The universe is deterministic, branching, and incomplete. |

</details>

<a id="einsteinrosenbridge"></a>

### 🟡 Wormholes — [`EinsteinRosenBridge.lean`](LeanBifurcationQuantum/EinsteinRosenBridge.lean)

> *A particle IS a wormhole.*

Einstein & Rosen, 1935, *Physical Review* 48, 73: "The Particle Problem in the General Theory of Relativity." Particles are not point singularities. They are geometric bridges connecting two regions of spacetime. A particle IS a wormhole.

$$M = \frac{r_{\text{throat}}}{2}$$

<details>
<summary>Definitions</summary>

- **`SpacetimeRegion`** — A 4D Lorentzian manifold patch (metric tensor).
- **`EinsteinRosenBridge`** — Connects two spacetime regions. Has a throat radius (Schwarzschild radius = 2M), positive, sheets distinct.

</details>

| | Theorem | Meaning |
|:-:|---|---|
| ✅ | [`er_bridge_is_particle`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L78) | Mass = throat_radius / 2 (Schwarzschild relation). |
| ✅ | [`er_two_sheets_one_bridge`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L91) | The bridge connects two distinct spacetime regions. |
| ✅ | [`er_throat_minimal`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L100) | The throat is the narrowest point. |
| ✅ | [`er_bridge_is_bifurcation`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L121) | The bridge IS a bifurcation. |
| ✅ | [`er_throat_is_threshold`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L132) | Throat = bifurcation threshold (t = 49). |
| ✅ | [`er_crossing_is_branch_selection`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L145) | Crossing the throat selects a sheet. |
| ✅ | [`er_everett_bridges_connect_worlds`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L176) | An ER bridge can connect two Everett branches. |
| ✅ | [`er_godel_bridge_nontraversable`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L221) | The bridge pinches off before traversal. |
| ✅ | [`er_godel_throat_is_sentence`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L246) | "This bridge connects to another region" is true but unprovable from inside. |
| ✅ | [`er_shadow_sheets_are_shadows`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L271) | Each sheet shadows the other. |
| ✅ | [`er_shadow_throat_is_boundary`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L282) | At the throat, shadow = reality (sheets touch). |
| ✅ | [`er_ledger_throat_is_checkpoint`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L308) | At the throat, the two histories reconcile. |

<details>
<summary>○ 6 interpretive theorems (conclude <code>True</code>)</summary>

| | Theorem | Meaning |
|:-:|---|---|
| ○ | [`er_everett_branches_are_regions`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L166) | Everett branches ARE spacetime regions. |
| ○ | [`er_equals_epr`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L189) | ER = EPR (Susskind, 2013). |
| ○ | [`er_multiverse_is_bridge_network`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L200) | The multiverse is not disconnected worlds. |
| ○ | [`er_godel_bridge_cannot_prove_itself`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L235) | Observer in sheet1 cannot verify sheet2 without crossing. |
| ○ | [`er_ledger_bridge_connects_histories`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L299) | The bridge joins two histories. |
| ○ | [`einstein_rosen_everett_godel_synthesis`](LeanBifurcationQuantum/EinsteinRosenBridge.lean#L351) | Particles are bridges. |

</details>

<a id="commutativetorus"></a>

### 🩷 The Torus in Everything — [`CommutativeTorus.lean`](LeanBifurcationQuantum/CommutativeTorus.lean)

> *It was there all along.*

The torus Tⁿ = (S¹)ⁿ appears in EVERY theorem file. It was there all along.

$$T^n = (S^1)^n$$

<details>
<summary>Definitions</summary>

- **`Circle`** — S¹: complex numbers with |z| = 1.
- **`Torus`** — Tⁿ = (S¹)ⁿ: product of n circles. T¹ = circle. T² = donut. Tⁿ = n-fold product.

</details>

<details>
<summary>○ 19 interpretive theorems (conclude <code>True</code>)</summary>

| | Theorem | Meaning |
|:-:|---|---|
| ○ | [`torus_in_bifurcation_boundary`](LeanBifurcationQuantum/CommutativeTorus.lean#L76) | The spectral ball boundary {‖M‖ = 1} contains Tⁿ via diagonal unitaries diag(e^{iθ₁}...e^{iθₙ}). |
| ○ | [`torus_bifurcation_projection`](LeanBifurcationQuantum/CommutativeTorus.lean#L87) | When `projB` scales M, result lands on boundary = torus. |
| ○ | [`torus_bifurcation_threshold_is_torus`](LeanBifurcationQuantum/CommutativeTorus.lean#L99) | At η*, state is on boundary = torus. |
| ○ | [`torus_godel_self_reference_is_circle`](LeanBifurcationQuantum/CommutativeTorus.lean#L123) | "I am not provable" loops back on itself. |
| ○ | [`torus_godel_tower_is_infinite_torus`](LeanBifurcationQuantum/CommutativeTorus.lean#L132) | F₀, F₁ = F₀+G₀, F₂ = F₁+G₁... |
| ○ | [`torus_godel_consistency_is_torus_point`](LeanBifurcationQuantum/CommutativeTorus.lean#L141) | Con(F) is a point on the statement-torus, unprovable from inside the torus. |
| ○ | [`torus_everett_branch_phase`](LeanBifurcationQuantum/CommutativeTorus.lean#L165) | Amplitude = \|a\|·e^{iθ}. |
| ○ | [`torus_everett_multiverse_is_infinite_torus`](LeanBifurcationQuantum/CommutativeTorus.lean#L175) | Infinite branches, each with phase in S¹. |
| ○ | [`torus_everett_branching_splits_torus`](LeanBifurcationQuantum/CommutativeTorus.lean#L183) | Branching: T¹ → T^N. |
| ○ | [`torus_everett_interference_is_torus_geometry`](LeanBifurcationQuantum/CommutativeTorus.lean#L193) | Constructive = phases align (same point on S¹). |
| ○ | [`torus_er_throat_phase_is_torus`](LeanBifurcationQuantum/CommutativeTorus.lean#L214) | Throat is S², phase space is T² = S¹ × S¹. |
| ○ | [`torus_er_bridge_is_torus_map`](LeanBifurcationQuantum/CommutativeTorus.lean#L222) | Bridge = T²(sheet1) → T²(sheet2). |
| ○ | [`torus_er_epr_on_torus`](LeanBifurcationQuantum/CommutativeTorus.lean#L231) | Entanglement lives on T². |
| ○ | [`torus_shadow_eigenvalues_on_torus`](LeanBifurcationQuantum/CommutativeTorus.lean#L254) | PSD matrix eigenvalues in [0,1], eigenvectors have phases in S¹. |
| ○ | [`torus_shadow_boundary_is_torus`](LeanBifurcationQuantum/CommutativeTorus.lean#L264) | Shadow ball boundary contains T⁴ (diagonal unitaries). |
| ○ | [`torus_ledger_chain_is_torus_path`](LeanBifurcationQuantum/CommutativeTorus.lean#L289) | Hash chain = path on Tⁿ. |
| ○ | [`torus_ledger_periodic_is_torus`](LeanBifurcationQuantum/CommutativeTorus.lean#L297) | Periodic ledger = torus. |
| ○ | [`commutative_torus_universal`](LeanBifurcationQuantum/CommutativeTorus.lean#L337) | ALL theorems live on Tⁿ. |
| ○ | [`noncommutative_deformation_quantum`](LeanBifurcationQuantum/CommutativeTorus.lean#L346) | C(Tⁿ) → A_θ (Connes). |

</details>

### The synthesis (all modules)

- **Bifurcation** is where a system splits. The threshold is the torus.
- **Gödel** says the system cannot prove itself from inside. The bifurcation is undecidable from inside.
- **Everett** says the wavefunction never collapses. Branching IS bifurcation.
- **Einstein-Rosen** says particles are bridges. Bridges ARE bifurcations.
- **The torus** is the universal structure: phase space, self-reference, interference, all live on Tⁿ.

The universe is deterministic (Everett), branching (Bifurcation), incomplete (Gödel), geometric (Einstein-Rosen). Sovereignty is building within these limits, anchored in mathematics.

## Proof status

- **`sorry` count: 0.** `rg -w 'sorry|admit' -g '*.lean'` finds nothing.
- **Declared axioms:** `godel_first_incompleteness` and `godel_second_incompleteness` (`GodelBifurcation.lean`). They are the standard theorems, stated as axioms over the abstract `FormalSystem` structure; they are not proved here.
- **`#print axioms`:** the formerly-`sorry` theorems (`bifurcation_preserves_psd`, `bifurcation_is_godel_sentence`, `godel_density_purity_undecidable`, `mwi_measurement_is_bifurcation`, `mwi_branch_is_shadow`, `frobenius_mul_le`) depend only on `propext`, `Classical.choice`, `Quot.sound`. `godel_bifurcation_incomplete` also depends on the declared axiom `godel_first_incompleteness`.
- **Scope:** 39 of the 81 theorems have conclusion `True`. For those, the content is the interpretation in the docstring, not something the kernel checks.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.9.0`); Mathlib is pinned to `v4.9.0` in `lakefile.lean`.

```bash
lake exe cache get   # download prebuilt Mathlib .olean files
lake build
```

Expect no `sorry` warnings; some linter warnings (unused variables and similar) remain. The five modules each define their own `ShadowState`, so they build as separate library roots and cannot all be imported into a single file.

## Repository layout

```text
.
├── LeanBifurcationQuantum/
│   ├── BifurcationLemmas.lean
│   ├── GodelBifurcation.lean
│   ├── EverettManyWorlds.lean
│   ├── EinsteinRosenBridge.lean
│   └── CommutativeTorus.lean
├── assets/
│   └── agent-branching.png
├── lakefile.lean
├── lake-manifest.json
├── lean-toolchain
├── LICENSE
└── README.md
```

## License

SNAPKITTY OPAQUE SOURCE LICENSE v1.0 — see `LICENSE`.
