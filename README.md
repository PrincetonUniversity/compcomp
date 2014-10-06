# Compositional CompCert 

## Overview

Compositional CompCert is a respecification and proof of CompCert 2.1
(http://compcert.inria.fr/) to support compositional separate compilation.

The files are distributed as a modification of standard CompCert 2.1: The
compiler files are the same but there are two sets of proofs, one for standard
CompCert and the second for Compositional CompCert.  Both sets of proofs are
buildable.

In general, files suffixed `*_coop.v` and `*_eff.v` are the compositional
variants of standard CompCert intermediate language semantics (`*_coop.v` is the
base interaction semantics of a given IL; `*_eff.v` is the effectful version).
Files suffixed `*_comp.v`, for "compositional," are the compositional variants of the standard
CompCert proofs. The compositional proofs can typically be found in the same
directory as their standard CompCert counterparts.

## Build

Compositional CompCert builds under: 

* Coq 8.4pl4 (http://coq.inria.fr/),
* Ssreflect 1.5 (http://ssr.msr-inria.inria.fr/), and
* MathComp 1.5 (http://ssr.msr-inria.inria.fr/). 

If you do not have Ssreflect+MathComp, you should be able to build everything
but the files in the `linking/` subdirectory (horizontal composition/proofs)
but we make no guarantees.

To build, clone the repository, go to the root directory, and type:

```
  ./configure ia32-linux
  make
```

### Using Custom Ssreflect Installation

If your Ssreflect or MathComp are installed in a nonstandard place (e.g., in
your home directory rather than system-wide), edit variables `SSREFLECT` and
`MATHCOMP` in the Makefile to point to the appropriate installation directories.
Otherwise, leave both `SSREFLECT` and `MATHCOMP` equal the empty string `""`.

## Special Instructions for AEC Members

### Virtual Machine Image 

To assist the AEC members, we've built a VirtualBox virtual machine image that
comes preinstalled with the required dependencies.

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

**WARNING:** On the virtual machine, the repository could take up to **2 hours**
to build. Make sure to configure the virtual machine to use at least **2GB of
memory.**

### The Paper

The accepted version of the paper (but now with author names) is available here:

> http://www.cs.princeton.edu/~jsseven/papers/compcomp/paper.pdf. 

### `popl15aec` Branch

The evaluation branch of `compcomp` is `popl15aec`. This branch should already 
be checked out in the `compcomp` repository installed on the virtual 
machine. If it isn't for some reason, or you would like to clone the repository
yourself, you can switch to the `popl15aec` branch as follows:

```
git clone https://github.com/PrincetonUniversity/compcomp.git <compcomp-dir>
cd <compcomp-dir>
git checkout popl15aec
```

The `compcomp` developers try to make sure that `master` always builds and
contains no admits (incomplete proofs are developed in separate branches and
only merged into `master` when complete). However, further development on
`compcomp` after the AEC begins its work could result in transitory build issues
on `master`.

## Files

An HTML rendering of the code is browsable at:

> http://www.cs.princeton.edu/~jsseven/papers/compcomp/html. 

Below is a description, with HTML links, of the main files and their relation to
the POPL results.

In the `cfrontend/` and `backend/` directories, source and target language
definitions used in each phase are generally suffixed `*_eff.v` (often importing
files suffixed `*_coop.v`).  The compositional compiler correctness proofs are
suffixed `*_comp.v`, to distinguish from the standard CompCert proofs.

### Toplevel Files

  * [driver/CompositionalCompiler.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CompositionalCompiler.html)      

    > Proves _Theorem 3 (Section 6)_.

  * [linking/CompositionalComplements.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CompositionalComplements.html)     
  
    > Proves _Corollary 2 (Section 6)_.

### cfrontend/ 

C frontend compiler phases and proofs: 

  * SimplLocals 
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/SimplLocals.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/SimplLocalsproof_comp.html)
  * Cshmgen
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Cshmgen.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Cshmgenproof_comp.html)
  * Cminorgen 
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Cminorgen.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Cminorgenproof_comp.html)

### backend/ 

Backend compiler phases and proofs: 

  * Selection 
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Selection.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Selectionproof_comp.html)
  * RTLgen 
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/RTLgen.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/RTLgenproof_comp.html)
  * Tailcall 
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Tailcall.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Tailcallproof_comp.html)
  * Renumbering
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Renumber.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Renumberproof_comp.html)
  * Allocation 
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Allocation.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Allocproof_comp.html)
  * Tunneling 
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Tunneling.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Tunnelingproof_comp.html)
  * Linearize 
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Linearize.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Linearizeproof_comp.html)
  * CleanupLabels 
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CleanupLabels.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CleanupLabelsproof_comp.html)
  * Stacking
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Stacking.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Stackingproof_comp.html)
  * Asmgen
    - [Compiler Phase](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Asmgen.html)
    - [Compositional Correctness](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Asmgenproof_comp.html)

Proof that CompCert IA32 Asm is a "nucular" semantics:

  * [Asm_nucular.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Asm_nucular.html)

### Intermediate Language Semantics 

_Interaction Semantics_ of the intermediate languages used in Compositional CompCert. 

  * Clight
    - [Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Clight_coop.html)
    - [Effectful Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Clight_eff.html)
  * Csharpminor
    - [Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Csharpminor_coop.html)
    - [Effectful Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Csharpminor_eff.html)
  * Cminor
    - [Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Cminor_coop.html)
    - [Effectful Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Cminor_eff.html)
  * CminorSel
    - [Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CminorSel_coop.html)
    - [Effectful Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/CminorSel_eff.html)
  * RTL
    - [Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/RTL_coop.html)
    - [Effectful Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/RTL_eff.html)
  * LTL
    - [Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/LTL_coop.html)
    - [Effectful Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/LTL_eff.html)
  * Linear
    - [Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Linear_coop.html)
    - [Effectful Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Linear_eff.html)
  * Mach
    - [Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Mach_coop.html)
    - [Effectful Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Mach_eff.html)
  * IA32 Asm
    - [Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Asm_coop.html)
    - [Effectful Interaction Semantics](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/Asm_eff.html)

### core/

  * [semantics.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/semantics.html)

    > Defines _Interaction Semantics (Section 2)_.

  * [structured_injections.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/structured_injections.html)
  
    > Defines _Structured Injections (Section 4)_.

  * [simulations.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/simulations.html) 
   
    > Defines _Structured Simulations (Section 4)_. Concordance for this file: 
    > - `replace_locals` is the function named `export` in the paper.
    > - `replace_externs` is the function named `import` in the paper.

  * [simulations_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/simulations_lemmas.html) 
   
    > Various derived structured simulations, specialized for particular use cases.

  * [simulations_trans.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/simulations_trans.html)  

    > Proves _Theorem 1 (Section 5)_, that simulations compose vertically.
    > The main subproofs are:
    > - [internal_diagram_trans.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/internal_diagram_trans.html) 
        proves transitivity of the internal step diagram. 
    > - [interpolation_II.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/interpolation_II.html) 
        proves the interpolation lemma required to prove transitivity of the external step diagram.

  * [closed_simulations.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/closed_simulations.html)  

    > Defines a variant of _simulations_ suitable for closed programs.

  * [closed_simulations_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/closed_simulations_lemmas.html)  

    > Corollaries of closed program simulation.

  * [reach.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/reach.html)  

    > Defines the reach-closure operation used in _Structured Simulations_ and
    > _Reach-Closed Semantics_.

  * [relyguarantee_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/relyguarantee_lemmas.html)  

    > Proves a number of rely-guarantee compatibility lemmas used in the linking proof.

  * [nucular_semantics.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/nucular_semantics.html)  

    > A notion of _Interaction Semantics_ that never store invalid pointers in memory. 
    > Why "nucular"? We call the memory invariant that is preserved by such semantics the "WMD" condition, 
    > as defined in file [mem_welldefined.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/mem_welldefined.html).  

### linking/

  * [compcert_linking.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/compcert_linking.html) 

    > Defines _Linking Semantics (Section 3)_.  The linking semantics
    > (\mathcal{L}) is defined twice: First as a function (to Prop), and then as
    > an inductive relation. The two versions are proved to coincide.

  * [compcert_linking_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/compcert_linking_lemmas.html) 

    > A few lemmas on linking semantics.

  * [linking_spec.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/linking_spec.html) 

    > States _Theorem 2 (Section 5)_.

  * [linking_inv.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/linking_inv.html)  

    > States the main linking simulation invariant, used to prove Theorem 2.
    > Subsidiary files include:
    > [linking/disjointness.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/disjointness.html).

  * [linking_proof.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/linking_proof.html)  

    > Proves _Theorem 2 (Section 5)_.  The two main subproofs (for the call and
    > return cases, respectively) are:
    > - [linking/call_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/call_lemmas.html)  
    > - [linking/ret_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/ret_lemmas.html)  

  * [rc_semantics.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/rc_semantics.html)   

    > Defines _Reach-Closed Semantics (Section 5)_. The definition has been 
    > weakened slightly since the POPL submission, to facilitate the proof,
    > in `linking/safe_clight_rc.v`, that all safe Clight programs are RC. 

  * [rc_semantics_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/rc_semantics_lemmas.html)   

    > Lemmas on _Reach-Closed Semantics_.

  * [safe_clight_rc.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/safe_clight_rc.html)    

    > Proves that all safe Clight programs are RC (a new theorem not in the
    > paper). This is a slightly counterintuitive result that relies on the fact
    > that safe Clight programs cannot fabricate pointers (recall that even in
    > C, casting integers to pointers is only implementation-defined).

  * [context_equiv.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/context_equiv.html)     
  
    > Defines _Reach-Closed Contextual Equivalence_ and proves _Corollary 1_
    > _(Section 5)_.

  * [gallina_coresem.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/gallina_coresem.html)       

    > Demonstrates one way in which to construct an interaction semantics that is just 
    > a mathematical relation in Gallina.

  * [reach_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/reach_lemmas.html)       

    > Lemmas concerning reachability.

  * [wf_lemmas.v](http://www.cs.princeton.edu/~jsseven/papers/compcomp/html/wf_lemmas.html)       

    > Lemmas about well-founded orders.

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

