# Zero-free region for the Riemann zeta-function: computer check and Lean formalization

This repository accompanies the paper
"A larger explicit zero-free region for the Riemann zeta-function" by Arseniy Varlamov (`paper.pdf`).
The paper proves that ζ(σ + it) ≠ 0 whenever |t| ≥ 2 and σ ≥ 1 − 1/(R log |t|), with R = 4.81406.

It contains two independent checks:

- a Python program that checks the finite inequalities of the paper (top level);
- a Lean 4 formalization of the whole proof, with eight published results as explicit hypotheses (`lean/`).

## Computer check of the finite inequalities

```
bash verify.sh
```

The script needs Python 3. It installs python-flint 0.8.0 into a local `.venv` and prints a JSON record with `"status": "PASS"`.
On one core of an Apple M3 Pro the check takes about 19 seconds.

Files:

- `verify.sh`: sets up the environment and runs the check.
- `verify.py`: checks that the seven height bands cover all heights, then checks each band.
- `verify_band.py`: the inequalities for one band, in FLINT/Arb ball arithmetic (160 bits) and exact rationals.
- `polynomial_kernel.py`: exact rational construction of the smoothing kernel.
- `parameters.json`: all parameters of the proof.

The program does not check the analytic arguments of the paper or the published results it cites.
Section 9 of the paper lists exactly what the program checks.

## Lean formalization

`lean/` contains a formalization of the whole argument in Lean 4, written on top of
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (PNT+).
It covers both the analytic arguments and the finite inequalities; it does not use the Python program.

The main theorem is `Varlamov.c8a_nonvanishing` in `lean/FinalRegion.lean`:

```lean
theorem c8a_nonvanishing
    (hK : KadiriInput) (hPT : PlattTrudgianInput) (hY : YangInput)
    (hK2 : KadiriExplicitInput) (hK3 : KadiriDigammaInput)
    (hL1 : LehmanMonotoneInput) (hL2 : LehmanSquareTailInput)
    (hS : RealDigammaStirlingInput) {σ t : ℝ}
    (ht : 2 ≤ |t|) (hσ : 1 - 1 / ((4.81406 : ℝ) * Real.log |t|) ≤ σ) :
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0
```

The eight hypotheses are published results. They are hypotheses of the theorem, not axioms:

| Hypothesis | Defined in | Source |
|---|---|---|
| `KadiriInput` | `Definitions.lean` | Kadiri, Acta Arith. 117 (2005), Theorem 1.1: the region with R = 5.69693, t ≥ 2 |
| `PlattTrudgianInput` | `Definitions.lean` | Platt and Trudgian, Bull. LMS 53 (2021), Theorem 1: RH up to height 3·10¹² |
| `YangInput` | `Definitions.lean` | Yang, J. Math. Anal. Appl. 534 (2024), Corollary 1.2 (arXiv:2301.03165v2): the region with constant 21.233, t ≥ 3 |
| `KadiriExplicitInput` | `KadiriInput.lean` | Kadiri (2005), Proposition 2.1, equation (7): the smoothed explicit formula, for Re s > 1/2 |
| `KadiriDigammaInput` | `GammaBounds.lean` | Kadiri (2005), equation (28), p. 323: a digamma approximation |
| `LehmanMonotoneInput` | `LehmanDensity.lean` | Lehman, Acta Arith. 11 (1966), Lemma 1, p. 400 |
| `LehmanSquareTailInput` | `RealZeroTail.lean` | Lehman (1966), Lemma 2, p. 400, with n = 2 |
| `RealDigammaStirlingInput` | `DigammaNumerical.lean` | Nemes, Proc. R. Soc. A 473 (2017), (4.1)–(4.2) and (1.8) with N = 4: Stirling series for the digamma function with remainder |

The formalization contains no `sorry`, and `#print axioms` on the main theorems gives only
`propext`, `Classical.choice` and `Quot.sound`. `lean/Audit.lean` checks this for every declaration
in the `Varlamov` namespace and fails the build on any other axiom.

### Building

Versions: PNT+ commit `127b50e33f6033e2147921167a117af96d9ba4ea`, Lean v4.35.0,
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; the other dependencies are pinned by PNT+'s `lake-manifest.json`.

```
git clone https://github.com/AlexKontorovich/PrimeNumberTheoremAnd pnt
cd pnt
git checkout 127b50e33f6033e2147921167a117af96d9ba4ea
mkdir -p PrimeNumberTheoremAnd/IEANTN/Varlamov
cp ../zeta-zero-free-region/lean/*.lean PrimeNumberTheoremAnd/IEANTN/Varlamov/
lake exe cache get
lake build PrimeNumberTheoremAnd.IEANTN.Varlamov.Audit
```

The last command should end with `AXIOM AUDIT PASSED`. On 9 November 2026 we ran these commands in a clean
copy of this PNT+ commit, except that the Mathlib cache was already on disk rather than downloaded by
`lake exe cache get`. The build compiled 373 modules (none from Mathlib) in 58 minutes on an Apple M3 Pro,
with peak memory 8.5 GB, and ended with `AXIOM AUDIT PASSED: 7971 declarations`. It prints about 3,200
linter warnings for our files, mostly unused tactics and `simpa` where `simp` would do; there are no errors.

AI tools (Codex, Claude) were used in preparing this work.

## License

The code (Python and Lean) is under the Apache License 2.0, see `LICENSE`. The paper (`paper.pdf`) is not covered by this license.
