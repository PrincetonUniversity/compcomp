# Compositional CompCert 

## Overview

Compositional CompCert is a respecification and proof of CompCert 2.1
(http://compcert.inria.fr/) to support compositional separate compilation.

The files are distributed as a modification of standard CompCert 2.1: The
compiler files are the same but there are two sets of proofs, one for standard
CompCert and the second for Compositional CompCert.  Both sets of proofs are
buildable.

In general, files suffixed `*_coop`, `*_eff`, or `*EFF` are the compositional
variants of the standard CompCert proofs. The compositional proofs can typically
be found in the same directory as their standard CompCert counterparts.

## Build

Compositional CompCert builds under: 

* Coq 8.4pl4 (http://coq.inria.fr/),
* Ssreflect 1.5 (http://ssr.msr-inria.inria.fr/), and
* MathComp 1.5 (http://ssr.msr-inria.inria.fr/). 

If you do not have Ssreflect+MathComp, you will be able to build everything but
the files in the linking/ subdirectory (horizontal composition/proofs).

To build, clone the repository, go to the root directory, and type:

```
  ./configure ia32-linux
  make depend
  make
```

### Virtual Machine Image 

As a convenience, we've built a VirtualBox virtual machine image that comes
preinstalled with the required dependencies.

* VirtualBox is available for free here: https://www.virtualbox.org/.
* The CompComp Debian virtual machine image is here: 
  http://www.cs.princeton.edu/~jsseven/papers/compcomp/compcomp-debian.tgz.

When you download the virtual machine, you'll find the Compositional CompCert
`compcomp` repository precloned in directory /home/popl15/Repos/compcomp.

Credentials for the virtual machine:

----------------------------
| User          | `popl15` |
----------------------------
| Password      | `popl15` |
----------------------------
| Root password | `popl15` |
----------------------------

### Using Custom Ssreflect Installation

If your Ssreflect or MathComp are installed in a nonstandard place (e.g., in
your home directory rather than system-wide), edit variables `SSREFLECT` and
`MATHCOMP` in the Makefile to point to appropriate installation directories.
Otherwise, leave both `SSREFLECT` and `MATHCOMP` equal the empty string "".

## The Paper

A draft version of the paper accompanying this work is available here:

> http://www.cs.princeton.edu/~jsseven/papers/compcomp/paper.pdf. 

(Note to AEC members: this is the accepted version.)

## Files

An HTML rendering of the code is browsable at 

> http://www.cs.princeton.edu/~jsseven/papers/compcomp/html. 

Below is a description of the main files and their relation to the POPL results.

### cfrontend/ 

C frontend compiler phases and proofs: 

  * SimplLocals 
  * Cshmgen
  * Cminorgen 

Files suffixed `*_eff.v` and `*_coop.v` give language definitions. Files
suffixed `*EFF.v` are the compositional compiler phase proofs.

### backend/ 

Backend compiler phases and proofs: 

  * Selection 
  * RTLgen 
  * Tailcall 
  * Renumbering
  * Allocation 
  * Tunneling 
  * Linearize 
  * CleanupLabels 
  * Stacking
  * Asmgen

Files suffixed `*_eff.v` and `*_coop.v` give language definitions. Files
suffixed `*EFF.v` are the compositional compiler phase proofs.

### core/

  * core_semantics.v 

    > Defines interaction semantics (Section 2).

  * StructuredInjections.v 
  
    > Defines Structured Injections (Section 4).

  * effect_simulations.v 
   
    > Defines structured simulations (Section 4). Concordance for this file: 
    > - [replace_locals] is the function named "export" in the paper.
    > - [replace_externs] is the function named "import" in the paper.

  * effect_simulations_trans.v 

    > Proves Theorem 1 (Section 5), that simulations compose vertically.
  
### linking/

  * compcert_linking.v

    > Defines linking semantics (Section 3).  The linking semantics
    > (\mathcal{L}) is defined twice: First as a function (to Prop), and then as
    > an inductive relation. The two versions are proved to coincide.

  * linking_spec.v

    > States Theorem 2 (Section 5).

  * linking_proof.v 

    > Proves Theorem 2 (Section 5).  The two main subproofs (for the call and
    > return cases, respectively) are:
    > - linking/call_lemmas.v
    > - linking/ret_lemmas.v

  * linking_inv.v 

    > states the main linking simulation invariant.

  * rc_semantics.v 

    > Defines reach-closed semantics (Section 5). The definition has been 
    > weakened slightly since the POPL submission, to facilitate the proof,
    > in linking/safe_clight_rc.v, that all safe Clight programs are RC. 

  * safe_clight_rc.v 

    > Proves that all safe Clight programs are RC (a new theorem not in the
    > paper). This is a slightly counterintuitive result that relies on the fact
    > that safe Clight programs cannot fabricate pointers (recall that even in
    > C, casting integers to pointers is only implementation-defined).

  * context_equiv.v 
  
    > Defines reach-closed contextual equivalence and proves Corollary 1
    > (Section 5).

### driver/

  * CompositionalCompiler.v 

    > Proves Theorem 3 (Section 6).

  * CompositionalComplements.v 
  
    > Proves Corollary 2 (Section 6).

### scripts/

  Contains the shell scripts used to calculate the line counts in Section 6. In
  general, we calculate lines of spec. vs. proof by first classifying whole
  files as either spec. or proof, and then just use wc. The coqwc tool is an
  alternative, but it often seems to undercount proof lines and overcount
  spec. lines.

  For some specification files (e.g., `backend/RTL.v`), we do not count in our
  "new" line counts those parts of the file, such as definitions of operational
  semantics, that are duplicated in our own files (e.g., `backend/RTL_coop.v`).

  To run the script we used to generate the line counts in the paper, from 
  the root directory of the repository, do: 


  ```
  cd scripts
  ./paperLineCount.sh
  ```

  The current line counts are slightly lower than those listed in the paper. We
  added the line counts to the paper a few days before the deadline and have
  since removed some dead comments, definitions, and lemmas.

