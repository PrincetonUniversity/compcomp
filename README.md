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
the files in the `linking/` subdirectory (horizontal composition/proofs).

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

  > http://www.cs.princeton.edu/~jsseven/papers/compcomp/compcomp-debian.tgz.

Credentials for the virtual machine:

| User          | Password |
| ------------: | :------: |
| popl15        | popl15   |
| root          | popl15   |

When you download the virtual machine, you'll find the Compositional CompCert
`compcomp` repository precloned in directory `/home/popl15/Repos/compcomp`.

### Using Custom Ssreflect Installation

If your Ssreflect or MathComp are installed in a nonstandard place (e.g., in
your home directory rather than system-wide), edit variables `SSREFLECT` and
`MATHCOMP` in the Makefile to point to appropriate installation directories.
Otherwise, leave both `SSREFLECT` and `MATHCOMP` equal the empty string `""`.

## The Paper

A draft version of the paper accompanying Compositional CompCert is available here:

> http://www.cs.princeton.edu/~jsseven/papers/compcomp/paper.pdf. 

(Note to AEC members: this is the accepted version.)

## Special Instructions for AEC Members

The evaluation branch of `compcomp` is `popl15aec`. This branch should already 
be checked out in the `compcomp` repository installed on the virtual 
machine. If it isn't for some reason, or you would like to clone the repository
yourself, you can switch to the `popl15aec` branch as follows:

```
git clone https://github.com/PrincetonUniversity/compcomp.git <compcomp-dir>
cd <compcomp-dir>
git checkout popl15aec
```

## Files

An HTML rendering of the code is browsable at:

> http://www.cs.princeton.edu/~jsseven/papers/compcomp/html. 

Below is a description, with HTML links, of the main files and their relation to
the POPL results.

In the `cfrontend/` and `backend/` directories, source and target language
definitions used in each phase are generally suffixed `*_eff.v` (often importing
files suffixed `*_coop.v`).  The compositional compiler correctness proofs are
suffixed `*EFF.v`, to distinguish from the standard CompCert proofs.

### cfrontend/ 

C frontend compiler phases and proofs: 

  * SimplLocals 
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/SimplLocals.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/SimplLocalsproofEFF.html)
  * Cshmgen
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Cshmgen.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CshmgenproofEFF.html)
  * Cminorgen 
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Cminorgen.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CminorgenproofEFF.html)

### backend/ 

Backend compiler phases and proofs: 

  * Selection 
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Selection.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/SelectionproofEFF.html)
  * RTLgen 
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/RTLgen.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/RTLgenproofEFF.html)
  * Tailcall 
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Tailcall.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/TailcallproofEFF.html)
  * Renumbering
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Renumber.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/RenumberproofEFF.html)
  * Allocation 
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Allocation.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/AllocproofEFF.html)
  * Tunneling 
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Tunneling.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/TunnelingproofEFF.html)
  * Linearize 
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Linearize.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/LinearizeproofEFF.html)
  * CleanupLabels 
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CleanupLabels.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CleanupLabelsproofEFF.html)
  * Stacking
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Stacking.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/StackingproofEFF.html)
  * Asmgen
    - [Compiler phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Asmgen.html)
    - [Compositional correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/AsmgenproofEFF.html)

### core/

  * [core_semantics.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/core_semantics.html)

    > Defines _Interaction Semantics (Section 2)_.

  * [StructuredInjections.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/StructuredInjections.html)
  
    > Defines _Structured Injections (Section 4)_.

  * [effect_simulations.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/effect_simulations.html) 
   
    > Defines _Structured Simulations (Section 4)_. Concordance for this file: 
    > - `replace_locals` is the function named `export` in the paper.
    > - `replace_externs` is the function named `import` in the paper.

  * [effect_simulations_trans.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/effect_simulations_trans.html)  

    > Proves _Theorem 1 (Section 5)_, that simulations compose vertically.
  
### linking/

  * [compcert_linking.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/compcert_linking.html) 

    > Defines _Linking Semantics (Section 3)_.  The linking semantics
    > (\mathcal{L}) is defined twice: First as a function (to Prop), and then as
    > an inductive relation. The two versions are proved to coincide.

  * [linking_spec.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/linking_spec.html) 

    > States _Theorem 2 (Section 5)_.

  * [linking_proof.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/linking_proof.html)  

    > Proves _Theorem 2 (Section 5)_.  The two main subproofs (for the call and
    > return cases, respectively) are:
    > - [linking/call_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/call_lemmas.html)  
    > - [linking/ret_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/ret_lemmas.html)  

  * [linking_inv.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/linking_inv.html)  

    > States the main linking simulation invariant, used to prove Theorem 2.

  * [rc_semantics.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/rc_semantics.html)   

    > Defines _Reach-Closed Semantics (Section 5)_. The definition has been 
    > weakened slightly since the POPL submission, to facilitate the proof,
    > in `linking/safe_clight_rc.v`, that all safe Clight programs are RC. 

  * [safe_clight_rc.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/safe_clight_rc.html)    

    > Proves that all safe Clight programs are RC (a new theorem not in the
    > paper). This is a slightly counterintuitive result that relies on the fact
    > that safe Clight programs cannot fabricate pointers (recall that even in
    > C, casting integers to pointers is only implementation-defined).

  * [context_equiv.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/context_equiv.html)     
  
    > Defines _Reach-Closed Contextual Equivalence_ and proves _Corollary 1_
    > _(Section 5)_.

  * [CompositionalComplements.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CompositionalComplements.html)       
  
    > Proves _Corollary 2 (Section 6)_.

### driver/

  * [CompositionalCompiler.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CompositionalCompiler.html)      

    > Proves _Theorem 3 (Section 6)_.

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

