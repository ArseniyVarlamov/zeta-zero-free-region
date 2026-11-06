# Zero-free region for the Riemann zeta-function: computer check

This program checks the finite inequalities in the paper
"A larger explicit zero-free region for the Riemann zeta-function" by Arseniy Varlamov.
The paper proves that ζ(σ + it) ≠ 0 whenever |t| ≥ 2 and σ ≥ 1 − 1/(R log |t|), with R = 4.81406.

## Run

```
bash verify.sh
```

The script needs Python 3. It installs python-flint 0.8.0 into a local `.venv` and prints a JSON record with `"status": "PASS"`.
On one core of an Apple M3 Pro the check takes about 19 seconds.

## Files

- `verify.sh`: sets up the environment and runs the check.
- `verify.py`: checks that the seven height bands cover all heights, then checks each band.
- `verify_band.py`: the inequalities for one band, in FLINT/Arb ball arithmetic (160 bits) and exact rationals.
- `polynomial_kernel.py`: exact rational construction of the smoothing kernel.
- `parameters.json`: all parameters of the proof.

## What is not checked

The program does not check the analytic arguments of the paper or the published results it cites.
Section 9 of the paper lists exactly what the program checks.
