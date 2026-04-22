# Chapter 6 LaTeX / Lean Crosswalk

This file is the chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and
  planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch6_excerpt.txt)

## Crosswalk

| Textbook result | LaTeX | Lean theorem |
| --- | --- | --- |
| Theorem 6.1 Weak Law of Large Numbers | If $Y_i \in \mathbb{R}^k$ are i.i.d. and $\mathbb{E}\|Y\| < \infty$, then $\bar{Y} = \frac{1}{n} \sum_{i=1}^n Y_i \xrightarrow{p} \mathbb{E}[Y]$ |  |
| Theorem 6.2 transformed WLLN | If $Y_i \in \mathbb{R}^k$ are i.i.d., $h : \mathbb{R}^k \to \mathbb{R}^q$, and $\mathbb{E}\|h(Y)\| < \infty$, then $\hat{\mu} = \frac{1}{n} \sum_{i=1}^n h(Y_i) \xrightarrow{p} \mu = \mathbb{E}[h(Y)]$ |  |
| Definition 6.3 consistency | $\hat{\theta}$ is consistent for $\theta$ if $\hat{\theta} \xrightarrow{p} \theta$ |  |
| Theorem 6.3 multivariate Lindeberg-Lévy CLT | If $Y_i \in \mathbb{R}^k$ are i.i.d. and $\mathbb{E}\|Y\|^2 < \infty$, then $\sqrt{n}(\bar{Y} - \mu) \xrightarrow{d} N(0,V)$ where $\mu = \mathbb{E}[Y]$ and $V = \mathbb{E}[(Y-\mu)(Y-\mu)']$ |  |
| Theorem 6.4 multivariate Lindeberg CLT | If $Y_{ni}$ are independent with $\mathbb{E}[Y_{ni}] = 0$, variance matrices $V_{ni}$, $\nu_n^2 = \lambda_{\min}(V_n) > 0$, and the Lindeberg condition $\nu_n^{-2} \sum_i \mathbb{E}[\|Y_{ni}\|^2 1\{\|Y_{ni}\|^2 \ge \epsilon \nu_n^2\}] \to 0$, then $V_n^{-1/2} \sum_i Y_{ni} \xrightarrow{d} N(0,I_k)$ |  |
| Theorem 6.5 heterogeneous-array CLT | If $Y_{ni}$ are independent with $\mathbb{E}[Y_{ni}] = 0$, $n^{-1}\sum_i V_{ni} \to V > 0$, and $\sup_{n,i} \mathbb{E}\|Y_{ni}\|^{2+\delta} < \infty$ for some $\delta > 0$, then $\sqrt{n}\,\bar{Y} \xrightarrow{d} N(0,V)$ |  |
| Theorem 6.6 Continuous Mapping Theorem in probability | If $Z_n \xrightarrow{p} c$ and $g$ is continuous at $c$, then $g(Z_n) \xrightarrow{p} g(c)$ |  |
| Theorem 6.7 Continuous Mapping Theorem in distribution | If $Z_n \xrightarrow{d} Z$ and $g$ is continuous $Z$-a.s., then $g(Z_n) \xrightarrow{d} g(Z)$ |  |
| Theorem 6.8 Delta Method | If $p_n(\hat{\mu} - \mu) \xrightarrow{d} \xi$ and $g$ is continuously differentiable near $\mu$, then $p_n(g(\hat{\mu}) - g(\mu)) \xrightarrow{d} G' \xi$ where $G = \partial g(\mu)'/\partial u$ |  |
| Theorem 6.9 smooth-function consistency | If $Y_i \in \mathbb{R}^m$ are i.i.d., $h : \mathbb{R}^m \to \mathbb{R}^k$, $\mathbb{E}\|h(Y)\| < \infty$, and $g : \mathbb{R}^k \to \mathbb{R}^q$ is continuous at $\mu$, then $\hat{\theta} \xrightarrow{p} \theta$ |  |
| Theorem 6.10 smooth-function asymptotic normality | If $Y_i \in \mathbb{R}^m$ are i.i.d., $\mathbb{E}\|h(Y)\|^2 < \infty$, and $g$ is continuously differentiable near $\mu$, then $\sqrt{n}(\hat{\theta} - \theta) \xrightarrow{d} N(0,V_\theta)$ where $V_\theta = G' V G$ |  |
| Theorem 6.11 best unbiased estimation of the mean | If $\tilde{\mu}$ is unbiased for $\mu = \mathbb{E}[h(Y)]$ and $\mathbb{E}\|h(Y)\|^2 < \infty$, then $\operatorname{Var}(\tilde{\mu}) \ge n^{-1} V$ where $V = \mathbb{E}[(h(Y)-\mu)(h(Y)-\mu)']$ |  |
| Theorem 6.12 moment bound implies stochastic boundedness | If $\mathbb{E}\|Z_n\|^\delta = O(a_n)$ for some $\delta > 0$, then $Z_n = O_p(a_n^{1/\delta})$; if $\mathbb{E}\|Z_n\|^\delta = o(a_n)$, then $Z_n = o_p(a_n^{1/\delta})$ |  |
| Theorem 6.13 bounded first moments pass to the limit | If $Z_n \xrightarrow{d} Z$ and $\mathbb{E}\|Z_n\| \le C$, then $\mathbb{E}\|Z\| \le C$ |  |
| Definition 6.4 uniform integrability | $Z_n$ is uniformly integrable if $\lim_{M \to \infty} \limsup_{n \to \infty} \mathbb{E}[\|Z_n\| 1\{\|Z_n\| > M\}] = 0$ |  |
| Theorem 6.14 primitive condition for uniform integrability | If for some $\delta > 0$, $\mathbb{E}\|Z_n\|^{1+\delta} \le C < \infty$, then $Z_n$ is uniformly integrable |  |
| Theorem 6.15 convergence of moments under uniform integrability | If $Z_n \xrightarrow{d} Z$ and $Z_n$ is uniformly integrable, then $\mathbb{E}[Z_n] \to \mathbb{E}[Z]$ |  |
| Theorem 6.16 uniform stochastic bounds for maxima | If $|Y_i|^r$ is uniformly integrable, then $n^{-1/r} \max_{1 \le i \le n} |Y_i| \xrightarrow{p} 0$ |  |

## Notes

- Chapter 6 is not yet formalized in Lean in this repo, so this crosswalk is intentionally textbook-
  side only for now.
