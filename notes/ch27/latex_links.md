# Chapter 27 LaTeX / Lean Crosswalk

This file is the chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- This chapter does not appear to package its main results as chapter-numbered theorems in the excerpt,
  so the middle column records the main theorem-level targets instead.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and
  planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch27_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Main target: censored conditional mean | For a censored normal regression model, derive the observed conditional mean as a function of the latent index and the inverse Mills ratio. |  |
| Main target: truncated conditional mean | For a truncated normal regression model, derive the conditional mean of the observed outcome as a selection-corrected function of covariates. |  |
| Main target: Tobit identification / estimation | Formalize the Tobit likelihood and the identifying conditional moments under the latent normal specification. |  |
| Main target: sample-selection bias | Express the conditional mean under sample selection in terms of a correction term driven by selection on latent normals. |  |
| Main target: Heckman correction | Package the two-step or control-function correction as the chapter-facing theorem target for selection models. |  |
| Main target: semiparametric selection | Track the chapter’s nonparametric / semiparametric selection results as future theorem targets even if they are not theorem-numbered in the excerpt. |  |

## Notes

- Chapter 27 is more topic-driven than theorem-labeled in the excerpt, so this file records the main
  theorem targets rather than a list of numbered theorem labels.
