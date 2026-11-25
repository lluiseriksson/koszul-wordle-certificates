# Machine-Checked Exact-Rational Koszul Complex Exactness, Max-Degree Filtration, and Multicolor Permutation Wordle Dimension-Count Certificates

**Author:** Lluis Eriksson (with transparent AI assistance via Google Antigravity)  
**License:** MIT (code, Lean 4 proofs, certificates) / CC-BY-4.0 (manuscript)

Zero-dependency Lean 4 formalization and pure-stdlib exact-$\mathbb{Q}$ certificate verifier (`KOSZUL-WORDLE-CERT-1.0`) for the filtered Koszul complex, Euler-characteristic dimension counts, Appendix A Remark A.1 gap-free strictness counterexamples, and zero-set evaluation ranks of Lawren Smithline (*The Max-Degree Filtration, Koszul Complexes, and Dimension Counts for Multicolor Permutation Wordle*, `arXiv:2611.33113`, November 24, 2026).

## Verification Summary
- **Lean 4 Kernel (`lean/KoszulWordle.lean`, Lean 4.35.0):** 18/18 constructive theorems, 0 warnings, 0 `sorry`, 0 `Classical.choice`, formalizing grade-2/3 Koszul $\delta^2=0$, filtration preservation, inductive Euler-characteristic telescoping on arbitrary finite exact chains, exact Eulerian number tables, both Smithline p. 19 dimension examples (`n=3, s=(1,1,1)` and `n=2, s=(3,2)`), inductive saturation degree $\sum s_k - 1$, uniform $|V(J_n)| = n!\,s^n$, and both Appendix A Remark A.1 non-gap-free counterexample identities & parity obstruction.
- **Exact-$\mathbb{Q}$ Certificate Atlas (`results/certificates/*.cert.json`):** 16 canonical certificates across 4 modes (exact rational Koszul differential matrices verifying $\delta^2=0$ & exactness at every grade $h \ge 1$; Theorem 6.1 generating-function vs. alternating Koszul dimension matches; Remark A.1 Farkas dual certificates $w^T \delta_1 = 0, w^T Z \neq 0$ proving strictness failure at non-gap-free multidegrees; exact rational evaluation-matrix ranks on $V(J_n) \subset \mathbb{Q}^n$ up to 48 points).
- **Cross-Checks & Red-Team Suite (`tests/test_suite.py`):** Exhaustive 16-point multidegree grid strictness-defect check on $N=M=2$, full $d=0..4$ exact $V(J_3)$ evaluation-rank sweep for $s=(2,1,2)$ (24 points), 16/16 certificate replays, and **57/57** live adversarial attacks rejected.

## One-Command Reproducibility
```bash
python scripts/verify_all.py
```
To regenerate all certificates, experiment JSONs, and 300-DPI figures from scratch:
```bash
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```
