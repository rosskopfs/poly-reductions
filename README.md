# Automatic Refinements and Polynomial-Time Reductions in Isabelle/HOL

## Preliminaries

This work is based on [Isabelle2025](https://isabelle.in.tum.de) with [AFP-2025](https://www.isa-afp.org/download/).

## Isabelle/AFP Setup:
Installation instructions can be found on the [Isabelle](https://isabelle.in.tum.de/installation.html) and [AFP webpage](https://www.isa-afp.org/help/).
In short:

1. Download and extract Isabelle (for your platform) and AFP (platform-independent) in a common working directory, e.g.
   ```
   workdir/Isabelle2025
   workdir/afp-2025-05-23
   ```

2. Install AFP for Isabelle from the terminal
   (on Windows, run `Isabelle2025/Admin/Cygwin/Cygwin-Terminal.bat` to start a terminal):
   ```
   Isabelle2025/bin/isabelle components -u afp-2025-05-23/thys
   ```

## Using this project
Download this project, then include the directory in Isabelle with `-d <workdir>/poly-reductions`.
E.g., if you have this project in `workdir/poly-reductions`,
you can view the alignment theory of the Paper with:
```
Isabelle2025/bin/isabelle jedit -d poly-reductions -R Paper poly-reductions/Paper/Paper.thy
```
To load up the whole formalization interactively, omit the `-R paper` option.