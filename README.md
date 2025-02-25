# Automatic Refinements and Polynomial-Time Reductions in Isabelle/HOL
This repository sets out to formalize some classic results about NP-completeness in Isabelle/HOL.

## Preliminaries

The theories in this repository are developed with the development versions of [Isabelle](https://isabelle.in.tum.de)
and the [AFP](https://www.isa-afp.org/download/), and work with the revisions specified below.
They should also work with any reasonably current Isabelle+AFP devel installation.

- Isabelle/2ea9efde917c
- AFP/7454e207574a

## Isabelle/AFP Setup:
Needs [Mercurial](https://www.mercurial-scm.org/) installed.
In the following, replace `<revision>` with the corresponding SHA value listed above.

1. Navigate to a working directory and clone the repositories:
   - Isabelle: `hg clone https://isabelle-dev.sketis.net/source/isabelle -r <revision>`
   - AFP: `hg clone https://foss.heptapod.net/isa-afp/afp-devel -r <revision>`

2. Set up Isabelle from the terminal (on Windows, run `isabelle/Admin/Cygwin/Cygwin-Terminal.bat` to start a terminal):
   - initialize Installation: `isabelle/Admin/init`
   - add AFP: `isabelle/bin/isabelle components -u afp-devel/thys`
   - download additional components: `isabelle/bin/isabelle components -a`

## Using this project
Clone the repository with `git clone https://github.com/rosskopfs/poly-reductions`
(needs [git](https://git-scm.com/) installed),
then include the directory in Isabelle with `-d <workdir>/poly-reductions`.
If you have cloned this project and Isabelle + AFP in the same work dir,
you can view the alignment theory of the Paper with:
```
isabelle/bin/isabelle jedit -d poly-reductions -R paper poly-reductions/Paper/Paper.thy
```
To load up the whole formalization interactively, omit the `-R paper` option.