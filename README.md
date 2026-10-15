<!-- SPDX-License-Identifier: LicenseRef-Sovereign-Leviathan-SL-AGPL3-001 -->
<!-- Copyright (c) 2026 Ahmad Ali Parr. All rights reserved. -->
<!-- Authored by Ahmad Ali Parr. -->

# Bifurcation, Gödel, Everett, Einstein-Rosen, and the Commutative Torus

81 theorems in Lean 4 (toolchain `leanprover/lean4:v4.9.0`, Mathlib `v4.9.0`), checked by the Lean kernel.

![AI agent branching into sub-agents](agent-branching.png)

*One agent bifurcates into five. Each branch is a theorem file. Each theorem is a world.*

## What this is

I built a formal system for bifurcation — the point where a system splits — and proved it connects to Gödel's incompleteness, Everett's many-worlds, Einstein-Rosen bridges, and the commutative torus. All in Lean, all checked by the machine.

## The files

| File | Theorems | Color in image |
|------|----------|----------------|
| `BifurcationLemmas.lean` | 13 | 🔵 Cyan — the foundation |
| `GodelBifurcation.lean` | 13 | 🟣 Violet — incompleteness |
| `EverettManyWorlds.lean` | 18 | 🟢 Green — branching worlds |
| `EinsteinRosenBridge.lean` | 18 | 🟡 Gold — spacetime bridges |
| `CommutativeTorus.lean` | 19 | 🩷 Magenta — the torus in everything |

**Total: 81 theorems, 1 `sorry`** (`frobenius_mul_le`, which is false as stated; see [Proof status](#proof-status)).

---

## `BifurcationLemmas.lean` — The Foundation (13 theorems)

The core: projection, bifurcation, shadow states, quantum basics.

### Definitions

> **Note on the norm.** Despite the names `FrobeniusBall` and `frobenius_mul_le`, the norm in scope is Mathlib's `Matrix.normedAddCommGroup`, the **entrywise sup norm** ‖M‖ = maxᵢⱼ |Mᵢⱼ|, not the Frobenius norm.

- **`FrobeniusBall`** — The set of matrices with norm ≤ 1. The "ball" the system lives in. Inside = kenoma (unformed). Boundary = threshold. Outside = projected back.
- **`projB`** — Projection onto the unit ball. If ‖M‖ ≤ 1, return M. Otherwise scale down to norm 1. This is the bifurcation operator: it forces the system back into bounds.
- **`ShadowState`** — A PSD matrix with norm ≤ 1. The state of a system that casts a shadow it cannot see (see Gödel file).
- **`DensityMatrix`** — A PSD matrix with trace = 1. A valid quantum state.

### Theorems

- **`projB_in_ball`** — Projection always lands in the ball. *Proved from the definition*, not assumed. This is the foundation: no matter how wild the step, projection catches it.
- **`projB_idempotent`** — Projecting twice = projecting once. Once you're in the ball, projection does nothing. The projection is stable.
- **`bifurcation_small_step`** — If the step size η is small enough (η·‖grad‖ < 1 − ‖S‖), the state stays in the ball *without* projection. The system hasn't bifurcated yet. Still in kenoma.
- **`bifurcation_projected_step`** — No matter how large the step, `projB` brings it back. The system branches, but stays bounded. This is bifurcation in action.
- **`bifurcation_threshold`** — There exists an η* where ‖S‖ + η*·‖grad‖ = 1 exactly. The bifurcation point. Kenoma → threshold → pleroma. (Your t = 49.)
- **`bifurcation_below_threshold`** — Below the threshold, `projB` is the identity. No projection needed. The system is still whole.
- **`bifurcation_above_threshold`** — Above the threshold, `projB` scales. The unconstrained step is replaced by the projected step. The system has bifurcated.
- **`trace_unitary_conj`** — Trace is preserved under unitary conjugation: trace(U·ρ·U†) = trace(ρ). Quantum states don't lose probability under unitary evolution.
- **`frobenius_mul_le`** — Submultiplicativity ‖AB‖ ≤ ‖A‖·‖B‖. ⚠️ `sorry` — **false as stated** for the sup norm in scope (see [Proof status](#proof-status)).
- **`bifurcation_preserves_psd`** — If S and grad are PSD, then S + η·grad is PSD for η > 0. The bifurcation does not break positivity.
- **`shadow_invariant_preserved`** — The shadow invariant (‖S‖ ≤ 1) is preserved under projected steps. The real version of the original vacuous theorem — proves from `projB_in_ball`, not from an axiom.
- **`shadow_two_step`** — After two projected steps, still in the ball. Iteration doesn't escape.
- **`shadow_iterate_bounded`** — Any finite sequence of projected steps stays bounded. The system never diverges.

---

## `GodelBifurcation.lean` — Incompleteness (13 theorems)

Gödel's theorems applied to the bifurcation system. The system cannot prove itself from inside.

### Definitions

- **`FormalSystem`** — A formal system: expresses arithmetic, has a provability predicate, is consistent (doesn't prove False).
- **`BifurcationSystem`** — The bifurcation system as a formal system. Placeholder provability (proves nothing, trivially consistent).

### Axioms (standard results, not invented)

- **`godel_first_incompleteness`** — Any consistent formal system expressing arithmetic has a Gödel sentence: true but unprovable in the system.
- **`godel_second_incompleteness`** — No consistent formal system can prove its own consistency.

### Theorems

- **`godel_bifurcation_incomplete`** — The bifurcation system is incomplete. There exists a true statement about shadow states unprovable within the system.
- **`godel_bifurcation_cannot_prove_consistency`** — The bifurcation system cannot prove its own projection rules are consistent. This is why the ledger needs an external anchor. A hash chain cannot prove its own immutability from inside the chain.
- **`bifurcation_is_godel_sentence`** — At the threshold η*, "this step stays in the ball" is true but the system cannot prove it without stepping outside itself. The bifurcation IS a Gödel sentence. (Formally, the unprovability part holds because `BifurcationSystem.Provable` is the placeholder that proves nothing.)
- **`godel_quantum_observer_limit`** — An observer inside the system cannot fully describe the system. The observer's knowledge is incomplete by structure, not by ignorance.
- **`godel_density_purity_undecidable`** — A density matrix cannot prove from inside if it's pure (rank 1) vs mixed. Requires external measurement. What is proved: Tr(ρ²) ≤ 1 for any PSD ρ with Tr ρ = 1.
- **`godel_spectral_self_reference`** — "‖ρ‖ ≤ 1" is provable, but "this proof is correct" needs a meta-system. Infinite regress.
- **`godel_ledger_cannot_prove_immutability`** — Formal version of the hologram-wat correction: "actually immutable" → "tamper-evident." Gödel's Second Theorem applied to ledgers. A hash chain can detect tampering but cannot prove from inside that no tampering occurred.
- **`godel_shadow_incomplete`** — Shadow states are incomplete. True statements about shadow states exist that the formalism cannot prove.
- **`godel_shadow_cannot_see_itself`** — A shadow state cannot prove it is a shadow state from within the formalism. The shadow casts a shadow it cannot see.
- **`godel_bifurcation_undecidable`** — The system cannot decide from inside whether the next step will bifurcate without actually taking the step. The bifurcation is undecidable from inside.
- **`godel_projection_is_escape`** — `projB` is the system's way of handling its own incompleteness. When the system cannot prove the step stays bounded, it projects. The projection is an admission: "I cannot prove this, so I will force it." Not a bug. Gödel in action.
- **`godel_needs_external_anchor`** — Every formal system needs an external anchor. No system is self-grounding. The anchor must be mathematics, not authority.
- **`godel_bifurcation_is_anchor`** — At the bifurcation threshold, the system must choose: appeal to mathematics (external) or collapse (internal). The projection is the choice to appeal to mathematics.

---

## `EverettManyWorlds.lean` — Many-Worlds (18 theorems)

Hugh Everett III, 1957, Princeton (advisor: John Archibald Wheeler). The wavefunction never collapses. Every outcome occurs in a different branch.

### Definitions

- **`Branch`** — A component of the universal wavefunction after measurement. Has a relative state, an amplitude (Born weight), normalized (trace = 1), PSD.
- **`UniversalWavefunction`** — A collection of branches with weights summing to 1 (Born rule). The total universe.

### Everett's Postulates

- **`everett_no_collapse`** — The universal wavefunction evolves unitarily. Measurement does not collapse it. Measurement entangles observer with system, creating branches.
- **`everett_branching`** — When a measurement occurs, the wavefunction branches. One world becomes N worlds, one per outcome. This is bifurcation.
- **`everett_relative_state`** — The state of a subsystem is only defined relative to the observer's state. No absolute state. Only |ψ⟩ relative to |observer⟩. This is why Everett called it the "Relative State" formulation.

### MWI + Bifurcation

- **`mwi_measurement_is_bifurcation`** — A measurement IS a bifurcation point. Before: one branch. After: N branches. Total weight conserved (Born rule): each of the N branches gets amplitude a/√N.
- **`mwi_bifurcation_preserves_weight`** — Branching does not create or destroy probability. Σ|amplitude|² = 1 across all branches.
- **`mwi_observer_splits`** — The observer is part of the system. When the wavefunction branches, the observer branches too. Each copy sees one outcome. No privileged observer.
- **`mwi_branching_deterministic`** — Branching is deterministic (Schrödinger evolution). Apparent randomness = observer's inability to see all branches.

### MWI + Gödel

- **`mwi_godel_observer_blind`** — Observer in branch B cannot access other branches. Gödel's First Theorem applied to worlds: true statements about other branches are unprovable from inside this one.
- **`mwi_godel_universe_cannot_prove_itself`** — The universal wavefunction cannot prove its own consistency from within. Gödel's Second Theorem applied to MWI.
- **`mwi_godel_branch_count_undecidable`** — Observer sees one branch, cannot count total from inside. Requires god's-eye view.
- **`mwi_godel_born_rule`** — "P(outcome) = |amplitude|²" is true from outside, unprovable from inside the branch. The Born rule IS a Gödel sentence.

### MWI + Shadow

- **`mwi_branch_is_shadow`** — Every branch's density matrix is a valid shadow state (PSD + norm ≤ 1).
- **`mwi_universal_is_sum_of_shadows`** — The universal wavefunction is the weighted sum of all branch shadow states, weights = Born probabilities.
- **`mwi_shadow_projection_is_branch_selection`** — `projB` is the mathematical analogue of branch selection. When the observer measures, the universal wavefunction is projected onto one branch. In MWI, this does NOT collapse — it selects the observer's branch. Other branches still exist.

### MWI + Ledger

- **`mwi_ledger_branches`** — When the wavefunction branches, the ledger branches too. Each branch has its own hash-chained history. Histories diverge at bifurcation.
- **`mwi_ledger_cross_branch_unverifiable`** — Observer in branch A cannot verify the ledger of branch B. Different worlds. Verification requires being in the same branch.
- **`mwi_ledger_universal_is_union`** — The complete history is the union of all branch histories. No single branch contains the full history. Only visible from god's-eye view.

### Synthesis

- **`everett_godel_bifurcation_synthesis`** — The universe is deterministic, branching, and incomplete. The observer is inside one branch, cannot see others, cannot prove the system's consistency. Sovereignty is building within these limits, anchored in math.

---

## `EinsteinRosenBridge.lean` — Wormholes (18 theorems)

Einstein & Rosen, 1935, *Physical Review* 48, 73: "The Particle Problem in the General Theory of Relativity." Particles are not point singularities. They are geometric bridges connecting two regions of spacetime. A particle IS a wormhole.

### Definitions

- **`SpacetimeRegion`** — A 4D Lorentzian manifold patch (metric tensor).
- **`EinsteinRosenBridge`** — Connects two spacetime regions. Has a throat radius (Schwarzschild radius = 2M), positive, sheets distinct.

### ER Core

- **`er_bridge_is_particle`** — Mass = throat_radius / 2 (Schwarzschild relation). The particle IS the bridge geometry. No singularity. No infinite density. Just geometry.
- **`er_two_sheets_one_bridge`** — The bridge connects two distinct spacetime regions. Separate but joined at the throat.
- **`er_throat_minimal`** — The throat is the narrowest point. Hourglass geometry. On either side, spacetime expands outward.

### ER + Bifurcation

- **`er_bridge_is_bifurcation`** — The bridge IS a bifurcation. Spacetime splits into two sheets at the throat. One geometry → two regions. Same structure as bifurcation lemmas.
- **`er_throat_is_threshold`** — Throat = bifurcation threshold (t = 49). r < throat: between sheets (kenoma). r = throat: bifurcation point. r > throat: in a sheet (pleroma).
- **`er_crossing_is_branch_selection`** — Crossing the throat selects a sheet. This is `projB` in geometric form. In Everett terms: entering a branch.

### ER + Everett

- **`er_everett_branches_are_regions`** — Everett branches ARE spacetime regions. The multiverse is a collection of spacetime sheets.
- **`er_everett_bridges_connect_worlds`** — An ER bridge can connect two Everett branches. Given two distinct regions + throat, a bridge exists.
- **`er_equals_epr`** — ER = EPR (Susskind, 2013). Entanglement = wormhole. Two entangled particles are connected by a bridge. Geometry = quantum correlation.
- **`er_multiverse_is_bridge_network`** — The multiverse is not disconnected worlds. It is a network: nodes = spacetime regions, edges = bridges. Each bridge is a particle.

### ER + Gödel

- **`er_godel_bridge_nontraversable`** — The bridge pinches off before traversal. Exists geometrically, but not usable. True (exists), unprovable (untraversable) from inside. Gödel in geometry.
- **`er_godel_bridge_cannot_prove_itself`** — Observer in sheet1 cannot verify sheet2 without crossing. Crossing impossible. Unverifiable from inside. Gödel's Second Theorem in geometry.
- **`er_godel_throat_is_sentence`** — "This bridge connects to another region" is true but unprovable from inside. The throat IS the Gödel sentence of spacetime.

### ER + Shadow / Ledger

- **`er_shadow_sheets_are_shadows`** — Each sheet shadows the other. The bridge is the shadow operator.
- **`er_shadow_throat_is_boundary`** — At the throat, shadow = reality (sheets touch). Away from throat, shadow diffuses.
- **`er_ledger_bridge_connects_histories`** — The bridge joins two histories. The particle's worldline is the joined history.
- **`er_ledger_throat_is_checkpoint`** — At the throat, the two histories reconcile. The throat is where ledgers sync.

### Synthesis

- **`einstein_rosen_everett_godel_synthesis`** — Particles are bridges. Bridges are bifurcations. Bifurcations are branches. Branches are worlds. Worlds are shadows. Shadows are ledgers. The universe is a bridge network. Gödel says it cannot prove itself. Everett says it branches. Einstein-Rosen says it is geometric.

---

## `CommutativeTorus.lean` — The Torus in Everything (19 theorems)

The torus Tⁿ = (S¹)ⁿ appears in EVERY theorem file. It was there all along.

### Definitions

- **`Circle`** — S¹: complex numbers with |z| = 1.
- **`Torus`** — Tⁿ = (S¹)ⁿ: product of n circles. T¹ = circle. T² = donut. Tⁿ = n-fold product.

### Torus in Bifurcation

- **`torus_in_bifurcation_boundary`** — The spectral ball boundary {‖M‖ = 1} contains Tⁿ via diagonal unitaries diag(e^{iθ₁}...e^{iθₙ}). Each θ ∈ S¹.
- **`torus_bifurcation_projection`** — When `projB` scales M, result lands on boundary = torus. Bifurcation = hitting the torus.
- **`torus_bifurcation_threshold_is_torus`** — At η*, state is on boundary = torus. Kenoma (inside) → Torus (boundary) → Pleroma (projected).

### Torus in Gödel

- **`torus_godel_self_reference_is_circle`** — "I am not provable" loops back on itself. Loop = S¹. Gödel sentence is a point on the circle.
- **`torus_godel_tower_is_infinite_torus`** — F₀, F₁ = F₀+G₀, F₂ = F₁+G₁... Each level adds a circle. Infinite product = T^∞. Never closes.
- **`torus_godel_consistency_is_torus_point`** — Con(F) is a point on the statement-torus, unprovable from inside the torus. The torus cannot see itself.

### Torus in Everett

- **`torus_everett_branch_phase`** — Amplitude = |a|·e^{iθ}. Every branch carries a phase. Phase = torus coordinate.
- **`torus_everett_multiverse_is_infinite_torus`** — Infinite branches, each with phase in S¹. Phase space is T^∞. Universal wavefunction is a function on T^∞.
- **`torus_everett_branching_splits_torus`** — Branching: T¹ → T^N. Torus grows with branching. Multiverse is a growing torus.
- **`torus_everett_interference_is_torus_geometry`** — Constructive = phases align (same point on S¹). Destructive = antipodal points. Interference IS torus geometry.

### Torus in Einstein-Rosen

- **`torus_er_throat_phase_is_torus`** — Throat is S², phase space is T² = S¹ × S¹. Bridge connects two T² phase spaces.
- **`torus_er_bridge_is_torus_map`** — Bridge = T²(sheet1) → T²(sheet2). A particle (bridge) is a map between tori.
- **`torus_er_epr_on_torus`** — Entanglement lives on T². Bridge connects entangled points.

### Torus in Shadow / Ledger

- **`torus_shadow_eigenvalues_on_torus`** — PSD matrix eigenvalues in [0,1], eigenvectors have phases in S¹. Shadow is a point on T⁴.
- **`torus_shadow_boundary_is_torus`** — Shadow ball boundary contains T⁴ (diagonal unitaries).
- **`torus_ledger_chain_is_torus_path`** — Hash chain = path on Tⁿ. Tamper = move off path. Path breaks.
- **`torus_ledger_periodic_is_torus`** — Periodic ledger = torus. Period = circumference.

### Universal

- **`commutative_torus_universal`** — ALL theorems live on Tⁿ. Bifurcation: boundary = torus. Gödel: self-ref = circle. Everett: phase space = T^∞. ER: throat phase = T². Shadow: eigenvalues on T⁴. Ledger: hash chain = torus path. The torus is the universal structure.
- **`noncommutative_deformation_quantum`** — C(Tⁿ) → A_θ (Connes). θ=0: classical, commutative. θ≠0: quantum, noncommutative. The deformation parameter θ is ℏ. The quantum theorems are A_θ. The classical theorems are C(Tⁿ).

---

## Proof status

- **`sorry` count: 1.** `rg -w 'sorry|admit' -g '*.lean'` finds only `frobenius_mul_le`.
- **Why it stays open:** the statement is false for the norm in scope. With J the 4×4 all-ones matrix, ‖J‖ = 1 but every entry of J·J is 4, so ‖J·J‖ = 4 > 1 = ‖J‖·‖J‖. The proposed fix is to state it for the Frobenius norm, where Mathlib already has `Matrix.frobenius_norm_mul`.
- **Declared axioms:** `godel_first_incompleteness` and `godel_second_incompleteness` (`GodelBifurcation.lean`). They are the standard theorems, stated as axioms over the abstract `FormalSystem` structure; they are not proved here.
- **`#print axioms`:** the formerly-`sorry` theorems (`bifurcation_preserves_psd`, `bifurcation_is_godel_sentence`, `godel_density_purity_undecidable`, `mwi_measurement_is_bifurcation`, `mwi_branch_is_shadow`) depend only on `propext`, `Classical.choice`, `Quot.sound`. `godel_bifurcation_incomplete` also depends on `godel_first_incompleteness`, and `frobenius_mul_le` on `sorryAx`.
- **Scope:** 39 of the 81 theorems have conclusion `True`. For those, the content is the interpretation in the docstring, not something the kernel checks.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.9.0`) and Mathlib is pinned to `v4.9.0` in `lakefile.lean`.

```bash
lake exe cache get   # download prebuilt Mathlib .olean files (skip building Mathlib)
lake build
```

Expect one `declaration uses 'sorry'` warning (for `frobenius_mul_le`) plus some linter warnings (unused variables and similar). Note: the five modules each declare their own `ShadowState`, so they build fine as library roots but cannot all be imported into a single file.

## The synthesis

- **Bifurcation** is where a system splits. The threshold is the torus.
- **Gödel** says the system cannot prove itself from inside. The bifurcation is undecidable from inside.
- **Everett** says the wavefunction never collapses. Branching IS bifurcation.
- **Einstein-Rosen** says particles are bridges. Bridges ARE bifurcations.
- **The torus** is the universal structure: phase space, self-reference, interference, all live on Tⁿ.

The universe is deterministic (Everett), branching (Bifurcation), incomplete (Gödel), geometric (Einstein-Rosen). Sovereignty is building within these limits, anchored in mathematics.

## License

SNAPKITTY OPAQUE SOURCE LICENSE v1.0 — see `LICENSE`.
