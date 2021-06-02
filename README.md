Ramics Archimedean
===========

Implementation of the hypersequent calculii HR and HMR introduced in the article "Free Modal Riesz Spaces are Archimedean: a Syntactic Proof".

Working with `Coq 8.12.0`

If you have any trouble or question, please contact `christophe.lucas@ens-lyon.fr` or `matteo.mio@ens-lyon.fr`.

### How to compile
To compile all the coq files and generate the documentation, type the following instruction in a terminal at the root of the project (where the file hr\_main\_results.v is).

	$ ./configure
	$ make gallinahtml

This command generates a .html file for each Coq file, that only have definitions, statements and comments useful for the reader. It also generates a file "toc.html" where all the sections in the files are gathered together as well as a quick explanation of what the reader will find in the files.


### The structure of the repository
There are five folders in the repository:

* QArithSternBrocot - contains the file sqrt2.v from the library [QArithSternBrocot](https://coq.inria.fr/distrib/8.2/contribs/QArithSternBrocot.html) used to prove the irrationality of sqrt 2.
* OLlibs - contains a subset of the library [OLlibs](https://github.com/olaure01/ollibs), a collection of add-ons for the Coq Standard Library.
* Coquelicot - contains the library [Coquelicot](http://coquelicot.saclay.inria.fr/), a Coq library for real analysis.
* Utilities - contains files not connected to Riesz Logic (e.g. a file defining positive real numbers and lemmas about them).
* hr - contains all the files related to the system HR.
* hmr - contains all the files related to the system HMR.
* hr_archimedean - contains all the files related to the proof of the Archimedean property for Free Riesz spaces.
* hmr_archimedean - contains all the files related to the proof of the Archimedean property for Free  modal Riesz spaces.

Following is a quick summary of the purpose of each file in the different folders.

#### H(M)R
The files in hr and hmr are quite similar, here are the files that are in those folders.

##### Terms
* `term.v` : Definitions  ad notations regarding terms of Riesz spaces (with positive real scalars as weights). The type corresponding to those terms is `term`.

##### Semantics
* `semantic.v` : Definition of equational reasoning over the terms defined in `term.v`. The type corresponding to the equality between two `terms` is `eqMALG` and we note `A === B` for `eqMALG A B`. The equalities and properties regarding Riesz spaces are in these files (ex Lemma 2.14 in subsection 2.1 of the article).
* `interpretation.v` : Translation of a hypersequent into a `term` as well as properties regarding this translation.

##### Proof system
* `hseq.v` : Definitions of sequents and hypersequents and some properties (like atomicity and complexity), as well as technical lemmas required to manipulate them in Coq.
* `h(m)r.v` : Definitions of the H(M)R system and some basic lemmas.
* `tech_lemmas.v` : Implementation of some technical lemmas of the system H(M)R.
* `soundness.v` : Proof of soundness.
* `completeness.v` : Proof of completeness.
* `invertibility.v` : Proof of the CAN-free invertibility of the logical rules.
* `prederivation.v` (for HMR only): Definition of prederivations (unfinished derivations).
* `M_elim.v` : Proof of the M elimination.
* `can_elim.v` : Proof of the CAN elimination.
* `p_hseq.v` : Definitions of parametrized sequents and parametrized hypersequents and some properties (like atomicity and complexity), as well as technical lemmas required to manipulate them in Coq.
* `apply_logical_rule.v` : functions reorganizing a hypersequent to put a non-basic term on the active position (i.e. the first one in the hypersequent) and lemmas assuring the correctness of those functions.

#### H(M)R\_archimedean
The files in hr\_archimedean and hmr\_archimedean are quite similar, here are the files that are in those folders.
* `lambda_prop_one.v` : adaptation of the lambda property to have coefficient in [0,1] instean of just R_{\geq 0}.
* `archimedean.v` : proofs that the derivability of H(M)R is continuous, and that free (modal) Riesz spaces are Archimedean.

##### Aux
* `tactics.v` : Some tactics used in the other files, for instance a tactic that apply every possible logical rules to get an atomic hypersequent.
* `h(m)r_perm_lemmas.v` : Technical construction and lemmas used to help manipulate lists of lists (instead of multisets of multisets like in the article). For instance, they help deal with the exchange rule cases in the proofs by induction.
* `lambda_prop_tools.v` : some tools to make the proofs of Lemmas 3.32, 3.42, 4.26 and 4.44 easier to implement.

#### Utilities
* `Rpos.v` : definition of positive real numbers and some lemmas used to manipulate them.
* `riesz_logic_List_more.v` : additionnal lemmas for lists.
* `polynomials.v` : definition of polynomial expressions and their evaluations on real numbers.
* `riesz_logic_Nat_more.v` : definition of tetration (tower of exponentials) and well-founded orders on N², N³ and N⁴, used to ensure terminations (notably to prove decidability).
* `R_complements.v` : contains the additional axioms (IPP and Sequential compactness) as well as some alternative definitions and additional results for limits.
* `Lim_seq_US.v` : adaptation of the file `Lim_seq.v` from the Coquelicot library, except we define limits on Uniform spaces insteand of only real numbers.
* `pol_continuous.v` : proof that the evaluation of polynomial expressions is continuous.

---

Many thanks to Olivier Laurent, the main contributor of [OLlibs](https://github.com/olaure01/ollibs) that was very helpful for this project.
