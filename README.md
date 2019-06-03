# tableaux - This is an incomplete work in progress.

## Tableaux Theorem Prover / Proof Assistant for First-Order Logic
This is an implementation, written in Clojure, of a tableaux based automated theorem prover / proof assistant for first-order logic.  It is based on methods described in the book [First-Order Logic and Automated Theorem Proving by Melvin Fitting](https://www.amazon.com/First-Order-Automated-Theorem-Proving-Computer/dp/0387945938).

This is a console based application.  First-order logic formulas are encoded and manipulated as lists of symbols, such as:

'(not ((exists w (forall x (R x w (f x w)))) imp (exists w (forall x (exists y (R x w y))))))

In the tableaux proof tree, they are printed in a more traditional fashion, such as:

¬((∃w)(∀x)R(x,w,f(x,w)) ⊃ (∃w)(∀x)(∃y)R(x,w,y))

## The Tableaux Proof Method, as implemented

The tableaux method proves a formula through refutation of the formula's negation.  Refutation is by deriving a contradiction.  See [Wikipedia on First-order tableau with unification](https://en.wikipedia.org/wiki/Method_of_analytic_tableaux#First-order_tableau_with_unification) for details.

The guts of the implementation consists of:
* a data structure which we'll call a tableau
* a function called `single-step` which takes a tablea and returns a tableau

`single-step` applies one of several possible rules to a tableau data structure to generate a new tableau data structure. Briefly, the rules are:
* alpha - a conjunctive formula on a branch is split into its conjuncts and they are added to the branch
* beta - a disjuntive formula on a branch is split into its disjuncts and they are placed on two new sub-branches
* gamma - a universally quantified formula has the quantified variable replaced with a new free variable
* delta - an existentially quantified formula has the quantified variable replaced with a new constant, or more generally a new skolem function of any free variables in the formula
* atomic closure - an atomic formula is unified with occurrences of its negation on the same branch, producing unifying substitutions, which are propagated toward the root of the tree

The gamma rule is the only rule that may need to be applied multiple times for a given formula.  This is because a universally quantified formula is true for a multiplicity of objects, and multiple of these may need to be considered in demonstrating a contradiction exists.

The beta rule is the only rule that increases the number of branches on a tableau.

Indefinitely increasing branching of a tableau occurs when repeated applications of the gamma rule expose new instances of beta formulas.

Successful application of the atomic closure rule demonstrates a contradiction on a branch of the tableau, in that there is a substitution of values for free variables which make an atomic formula and it's negation identical.  These substitutions are found by a unification algorith.  However, a tableau is essentially a disjunction of all its branches, and to refute a disjunction, each of the disjuncts must be refuted. An atomic closure must occur on each branch.  Moreover, the substitutions generated in finding these atomic closures must themselves all be unifiable to a single substitution.  Much of the code deals with operations on substitutions and sets of substitutions (maintaining sets of substitutions as antichains under a "more general" partial ordering, computing cartesian sums of sets of substitions that close two beta branches, etc).

At the heart of a tableau structure is a binary tree. This is represented as a map from integer node indexes to node structures.  The root node has index 0.  A node with index `n` has a left sub-node with index `2n+1` and a right sub-node with index `2n+2`.

A branch of a tableau consists of the nodes from a leaf node up to the root.

The tableau data structure contains:
* the binary tree of nodes, each of which which contains:
  * a collection of annotated formula structures
  * a collection of annotated substitution structures
* a queue of branch structures, each of which contains:
  * index of the leaf node for the branch
  * a priority queue of formulas on the branch that rules may be applied to
  * a list of atomic formulas that are on the branch

An annotated formula structure contains:
* a first-order formula (as a list structure)
* a unique integer id
* a type (alpha, beta, gamma, delta, double-negative or atomic)
* the formula's derivation (axiom, negated goal, or derived by rule application from prior formula)
* list of free variables in the formula

An annotated substitution structure which contains:
* a substitution (which is a map from variables to terms)
* a type (was it generated from atomic formulas, or by unification of substitutions from two beta branches)
* two atomic formula structures (if generated from closure on two atomic formulas)
* two substition structures (if generated by unification of substitutions from two beta sibling branches)

When atomic closure happens, substitutions are propagated toward the root of the tree by unification with substitutions from sibling branches.  When a substitution reached the root of the tree, a proof has been found, and the substitution structure contains all the information relevant to deriving that substitution.  This information can be used to prune the tree of unnecessary speculative rule applications and possibly branches.  The substitution can be applied to all formulas in the resulting pruned tree, and the tree printed, to make the proof clear.

