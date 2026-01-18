# Erdos (Lean 4)

Lean 4 (mathlib) formalization of the *scaffold* of the argument in
[mainr(1).tex](mainr(1).tex) for Erdős Problem #257 (generalized version).

The repository is organized around a clean separation:

- **Analytic / density layer** (Euler products, tail isolation, density domination, etc.):
  This layer is not fully formalized here yet; it is recorded as well-typed hypotheses.
- **Combinatorial kernel** (exhaustion / not eventually periodic): this part *is* formalized.

## Build

- Requirements: `elan` + the toolchain pinned in [lean-toolchain](lean-toolchain), and `lake`.
- Build: `lake build`

If you use VS Code, install the **Lean 4** extension and open the project folder.

## Repository map

### Root files

- [Erdos.lean](Erdos.lean): project entrypoint; imports modules and exposes declarations under
  `namespace Erdos` / `Erdos257`.
  - Includes an explicit “shells by levels” formulation `P(n)=p_k` and the specialization
    `P(n)=largestPrimeFactor n`.
- [README.md](README.md): this document.
- [mainr(1).tex](mainr(1).tex): the TeX manuscript with the mathematical argument.
- Diophantine Stability and Adelic Obstructions in Reciprocal Sums of Arbitrary Subsets: A Generalized Solution to Erdős Problem #257 -1.pdf:
  associated PDF (reading reference).
- [lakefile.toml](lakefile.toml), [lake-manifest.json](lake-manifest.json): Lake configuration and lockfile.
- [lean-toolchain](lean-toolchain): Lean version pinned for `elan`.
- `benedie`: auxiliary file (not part of the Lean pipeline; safe to ignore if unused).

### Lean modules (folder [Erdos/](Erdos/))

File names correspond to import paths `Erdos.<Name>`.

- [Erdos/Basic.lean](Erdos/Basic.lean)
  - Goal: the main scaffold and the combinatorial kernel.
  - Contents: definition of `erdosSeries`; period arithmetic (`lcm`, growth of `b^L-1`);
    a “carry-span proxy” via `Nat.log`; finite witness selection; integer block/carry model;
    and the kernel `EventuallyPeriodic` + “unbounded range ⇒ not eventually periodic”.
  - Packages the analytic boundary as `KernelPackage` / `DensityPackage`.

- [Erdos/ShellIrrationality.lean](Erdos/ShellIrrationality.lean)
  - Goal: interface “shell log-moment ⇒ irrationality”.
  - Defines `Shell := ℕ → Finset ℕ` and the functional `shellLogMoment`.
  - Defines analytic hypotheses `DifferentialShellLogBound` and `DifferentialShellLogSmall`.
  - Introduces bridge typeclasses:
    - `ShellToKernel`: build a `KernelPackage` from a per-shell bound.
    - `ShellToStageFamily`: intermediate bridge to a stage family with “surplus”.

- [Erdos/ShellDensity.lean](Erdos/ShellDensity.lean)
  - Goal: a finitary **density bridge** connecting hazardous-token counts with sums of the form
    `∑ log(n)/n` on a shell.
  - Main result: `hazardTokensOn_density_le_two_mul_shellLogMoment` (normalized bound
    `card/μ ≤ 2 * shellLogMoment`).

- [Erdos/HazardMaps.lean](Erdos/HazardMaps.lean)
  - Defines the “local” hazardous-token universe:
    - `blockIndices μ = {1,…,μ}`
    - `isHazard L M n q` and `hazardTokens μ L M active`
    - projection `Gamma`.

- [Erdos/HazardCounting.lean](Erdos/HazardCounting.lean)
  - Goal: counting lemmas in `ZMod n` / value intervals, to bound how many `q` produce a remainder
    in an interval `[1,m]`.
  - Provides tools later used to bound `hazardTokens` cardinalities.

- [Erdos/HazardTokenCard.lean](Erdos/HazardTokenCard.lean)
  - Goal: turn the definition of `hazardTokens` into “per-`n`” sums and derive global bounds of
    the form `card ≤ ∑ (μ/n + 1) * M(n)`.
  - Includes a sigma presentation (`hazardSigma`) and auxiliary injectivity lemmas.

- [Erdos/ShellStage.lean](Erdos/ShellStage.lean)
  - Defines `ShellStage`: a finitary stage (a “shell step”) with `μ`, `L`, `active`, `M`, a set of
    allowed block indices `B`, a `witness`, and a block-value function `val` assumed injective on
    `B`.
  - Defines `hazardTokensOn` (tokens restricted to `B`) and the adapter `toBlockStage`.

- [Erdos/TokenBijection.lean](Erdos/TokenBijection.lean)
  - Formalizes the “reverse pigeonhole”: if `card U < card B`, then some block is not hit by the
    projection `Γ : U → B`.

- [Erdos/BlockWitness.lean](Erdos/BlockWitness.lean)
  - Builds the step “there exists a safe block with a fresh value”.
  - Defines `BlockStage` (blocks, tokens, projection, and an injective value map).
  - Key lemma: `exists_safeBlock_avoiding` (avoid both hazards and a finset of forbidden values).
  - Utility: `unbounded_of_strictMono_nat`.

- [Erdos/TokenKernelBridge.lean](Erdos/TokenKernelBridge.lean)
  - Defines `StageFamily`: a family of `BlockStage`s indexed by `k`.
  - Hypothesis `HasSurplus`: eventually there are more blocks than (hazards + forbidden values).
  - Builds a strictly increasing sequence `blocks : ℕ → ℕ` from `HasSurplus`.

- [Erdos/FullClaim.lean](Erdos/FullClaim.lean)
  - States the final goal as a proposition (`erdos257_claim`) and proves the “conditional” version
    assuming a `DensityPackage`.

## What is still missing for a fully unconditional proof

The combinatorial implication `KernelPackage → Irrational` is proved.
What is still missing (in general) is the analytic bridge that produces a `KernelPackage`
(or at least a `ShellToKernel` instance) from per-shell bounds.
# Erdos (Lean 4)

Lean 4 (mathlib) formalization of the *scaffold* of the argument in
[mainr(1).tex](mainr(1).tex) for Erdős Problem #257 (generalized version).

The repo is organized around a clean separation:

- **Analytic / density layer** (Euler products, tail isolation, density domination, etc.):
-   this is not fully formalized here yet; it is recorded as well-typed hypotheses.
- **Combinatorial kernel** (exhaustion / not eventually periodic): this part *is* formalized.

## Build

- Requirements: `elan` + the toolchain pinned in [lean-toolchain](lean-toolchain), and `lake`.
- Build:
  - `lake build`

If you use VS Code, install the **Lean 4** extension and open the project folder.

## Repository map

### Root files

- [Erdos.lean](Erdos.lean): project entrypoint; imports modules and exposes declarations under
  `namespace Erdos` / `Erdos257`.
  - Includes an explicit “shells by levels” formulation `P(n)=p_k` and the specialization
    `P(n)=largestPrimeFactor n`.
- [README.md](README.md): this document.
- [mainr(1).tex](mainr(1).tex): the TeX manuscript with the mathematical argument.
- Diophantine Stability and Adelic Obstructions in Reciprocal Sums of Arbitrary Subsets_ A Generalized Solution to Erdös Problem #257 -1.pdf: associated PDF (reading reference).
- [lakefile.toml](lakefile.toml), [lake-manifest.json](lake-manifest.json): Lake configuration and lockfile.
- [lean-toolchain](lean-toolchain): Lean version pinned for `elan`.
- `benedie`: auxiliary file (not part of the Lean pipeline; safe to ignore if unused).

### Lean modules (folder [Erdos/](Erdos/))

File names correspond to import paths `Erdos.<Name>`.

- [Erdos/Basic.lean](Erdos/Basic.lean)
  - Goal: the main scaffold and the combinatorial kernel.
  - Contents: definition of `erdosSeries`; period arithmetic (`lcm`, growth of `b^L-1`);
    a “carry-span proxy” via `Nat.log`; finite witness selection; integer block/carry model;
    and the kernel `EventuallyPeriodic` + “unbounded range ⇒ not eventually periodic”.
  - Packages the analytic boundary as `KernelPackage` / `DensityPackage`.

- [Erdos/ShellIrrationality.lean](Erdos/ShellIrrationality.lean)
  - Goal: interface “shell log-moment ⇒ irrationality”.
  - Defines `Shell := ℕ → Finset ℕ` and the functional `shellLogMoment`.
  - Defines analytic hypotheses `DifferentialShellLogBound` and `DifferentialShellLogSmall`.
  - Introduces bridge typeclasses:
    - `ShellToKernel`: build a `KernelPackage` from a per-shell bound.
    - `ShellToStageFamily`: intermediate bridge to a stage family with “surplus”.

- [Erdos/ShellDensity.lean](Erdos/ShellDensity.lean)
  - Goal: a finitary **density bridge** connecting hazardous-token counts with
    sums of the form `∑ log(n)/n` on a shell.
  - Main result: `hazardTokensOn_density_le_two_mul_shellLogMoment` (normalized bound
    `card/μ ≤ 2 * shellLogMoment`).

- [Erdos/HazardMaps.lean](Erdos/HazardMaps.lean)
  - Defines the “local” hazardous-token universe:
    - `blockIndices μ = {1,…,μ}`
    - `isHazard L M n q` and `hazardTokens μ L M active`
    - projection `Gamma`.

- [Erdos/HazardCounting.lean](Erdos/HazardCounting.lean)
  - Goal: counting lemmas in `ZMod n` / value intervals, to bound how many `q` produce a
    remainder in an interval `[1,m]`.
  - Provides tools later used to bound `hazardTokens` cardinalities.

- [Erdos/HazardTokenCard.lean](Erdos/HazardTokenCard.lean)
  - Goal: turn the definition of `hazardTokens` into “per-`n`” sums and derive global bounds of
    the form `card ≤ ∑ (μ/n + 1) * M(n)`.
  - Includes a sigma presentation (`hazardSigma`) and auxiliary injectivity lemmas.

- [Erdos/ShellStage.lean](Erdos/ShellStage.lean)
  - Defines `ShellStage`: a finitary stage (a “shell step”) with:
    `μ`, `L`, `active`, `M`, a set of allowed block indices `B`, a `witness`,
    and a block-value function `val` assumed injective on `B`.
  - Defines `hazardTokensOn` (tokens restricted to `B`) and the adapter `toBlockStage`.

- [Erdos/TokenBijection.lean](Erdos/TokenBijection.lean)
  - Formalizes the “reverse pigeonhole”: if `card U < card B`, then some block is not hit by the
    projection `Γ : U → B`.

- [Erdos/BlockWitness.lean](Erdos/BlockWitness.lean)
  - Builds the step “there exists a safe block with a fresh value”.
  - Defines `BlockStage` (blocks, tokens, projection, and an injective value map).
  - Key lemma: `exists_safeBlock_avoiding` (avoid both hazards and a finset of forbidden values).
  - Utility: `unbounded_of_strictMono_nat`.

- [Erdos/TokenKernelBridge.lean](Erdos/TokenKernelBridge.lean)
  - Defines `StageFamily`: a family of `BlockStage`s indexed by `k`.
  - Hypothesis `HasSurplus`: eventually there are more blocks than (hazards + forbidden values).
  - Builds a strictly increasing sequence `blocks : ℕ → ℕ` from `HasSurplus`.

- [Erdos/FullClaim.lean](Erdos/FullClaim.lean)
  - States the final goal as a proposition (`erdos257_claim`) and proves the “conditional”
    version assuming a `DensityPackage`.

## What is still missing for a fully unconditional proof

The combinatorial implication `KernelPackage → Irrational` is proved.
What is still missing (in general) is the analytic bridge that produces a `KernelPackage`
(or at least a `ShellToKernel` instance) from per-shell bounds.

