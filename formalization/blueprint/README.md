# Blueprint

One node per numbered statement of *A graphical construction of free Markov
categories* (`paper/free-markov.tex`), plus the definitions of the
Introduction and the syntactic category `Syn_s(G)` of design decision D4
(`formalization/PLAN.md`). `\uses` records the mathematical dependencies,
`\lean` the Lean declarations, `\leanok` what is formalized. The stage that
formalizes a node is given in its section title.

`python3 scripts/verify.py` checks the blueprint: unique labels, every
`\uses` resolves, the dependency graph is acyclic, and every `\lean` name is a
declaration of the library.

Rendering has not been done: it needs `leanblueprint` (pinned in
`requirements.txt`) and Graphviz, which are not installed here, and
`leanblueprint` expects the folder at `blueprint/` in the repository root, so a
rendering job would copy or link this folder there first. `print.tex` builds a
PDF with plain LaTeX.
