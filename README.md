# Automatic Refinements and Polynomial-Time Reductions in Isabelle/HOL
This repository sets out to formalize some classic results about NP-completeness in Isabelle/HOL.

## Preliminaries

The theories in this repository are developed with the development versions of [Isabelle](https://isabelle.in.tum.de)
and the [AFP](https://www.isa-afp.org/download/), and should work with the upcoming Isabelle2025/AFP2025 release.
Tested revisions:

- Isabelle/2ea9efde917c
- AFP/7454e207574a
- ML-Typeclasses/75d3399

## Setup:
Needs [Mercurial](https://www.mercurial-scm.org/) and [Git](https://git-scm.com/) installed.
In the following, replace `<revision>` with the corresponding SHA value listed above.

1. Navigate to a working directory and clone the repositories:
  - This repo: `git clone https://github.com/rosskopfs/poly-reductions`
  - Isabelle: `hg clone https://isabelle-dev.sketis.net/source/isabelle -r <revision>`
  - AFP: `hg clone https://foss.heptapod.net/isa-afp/afp-devel -r <revision>`
  - ML-Typeclasses: 
    - `git clone https://github.com/kappelmann/ml-typeclasses-isabelle.git`
    - `cd ml-typeclasses-isabelle`
    - `git checkout <revision>`
    - `cd ..`

2. Setup up Isabelle from the terminal (on Windows, run `isabelle/Admin/Cygwin/Cygwin-Terminal.bat` to start a terminal):
  - initialize Installation: `isabelle/Admin/init`
  - add AFP: `isabelle/bin/isabelle components -u afp-devel/thys`
  - make ML-Typeclasses globally available with `isabelle components -u ml-typeclasses-isabelle`
  - download additional components: `isabelle/bin/isabelle components -a`

When you run Isabelle, include this repository with `-d <workdir>/poly-reductions`.
E.g., to view the main theory, start Isabelle/jEdit with:
```
isabelle/bin/isabelle jedit -d poly-reductions -R paper poly-reductions/Paper/Paper.thy
```
