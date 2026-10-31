# Errata for the two papers of Basu, Sidoravicius and Sly

These are two checked lists of the errors and proof gaps found in:

- [BSS23] R. Basu, V. Sidoravicius and A. Sly, *Rotationally invariant first passage percolation: Concentration and scaling relations*, [arXiv:2312.14143v1](https://arxiv.org/abs/2312.14143v1): [`bss23-errors.md`](bss23-errors.md), 73 items;
- [BSS26] R. Basu, V. Sidoravicius and A. Sly, *Rotationally invariant first passage percolation: Breaking the $n/\log n$ variance barrier*, [arXiv:2604.01214v1](https://arxiv.org/abs/2604.01214v1): [`bss26-errors.md`](bss26-errors.md), 78 items.

Neither list refutes a main theorem. Many items have local corrections, but no corrected proof of either paper's main theorems has been obtained. Neither list claims to be exhaustive; each states its scope at the top.

**How they were found.** The errors came to light in a project to formalize the two papers in the Lean 4 proof assistant with the help of AI agents, as Section 1.5 of the continuum paper in [`papers/`](../../papers/) describes. The lists come from written review, not from Lean:
- each list was written by a GPT-6.1 Sol agent;
- each was then checked independently by another GPT-6.1 Sol agent:
  - the check of the BSS23 list confirmed all 73 items;
  - the check of the BSS26 list confirmed 77 items, found one to be a notational omission, and judged the list "correct after minor repairs". Those repairs are applied here.

**Relation to this repository.** The two papers formalized here follow the framework of Basu, Sidoravicius and Sly, which is central to them, but neither uses a result of [BSS23] or [BSS26] as an input. Nothing in these lists is formalized in Lean, and nothing in the Lean depends on them.
