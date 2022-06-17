Etog
====

_See also:_ [LCF-style-ND](https://github.com/cpressey/LCF-style-ND/#readme)
∘ [Philomath](https://github.com/catseye/Philomath#readme)
∘ [Maxixe](https://github.com/catseye/Maxixe#readme)

- - - -

**Etog** is an LCF-style theorem prover in Simple Haskell for the
**equational theory of groups**.
Not recommended for actual use; I wrote it out of curiosity.

The "trusted kernel" is in [Etog.hs](src/Etog.hs) and is less than 100
lines of code.  It does not contain any fancy types, monads, infinite
lists, or anything like that.

Some example proofs can be found in [EtogDemo.hs](src/EtogDemo.hs),
including a proof of the elementary "socks and shoes" theorem:

    (a * b)^-1 = b^-1 * a^-1

...first in a very verbose form, and then with variations.

## Notes on Equational Logic

It took me a relatively long time to wrap my head around equational logic,
so I will provide some notes on it here, and links to resources.

I would put it like this: _Equational logic is the deductive aspect of universal algebra._
It provides the "syntax" where the algebraic structure provides the "semantics".

By itself, it captures only the idea of _equating things_:

*   Equation is a relation which is _reflexive_, _symmetric_, and _transitive_;
*   In the manner of elementary algebra, "equals may always be replaced by equals".

But by itself, it cannot prove many theorems of interest.   To do that, it needs to be
supplemented by extra axioms stipulating exactly which things _should_, for the sake of
argument, be considered equal.  These axioms describe an _algebraic structure_.
When the extra axioms are put together with equational logic, this is said to be the
_equational theory_ of the structure.

For example, the axioms for a group are:

*   _Associativity_: **(x * y) * z = x * (y * z)** 
*   _Existence of an Identity Element_: **x * e = e * x = e**
*   _Existence of Inverse Elements_: **x * x^-1 = x^-1 * x = e**

In the statement of each of these axioms, the variables are implicitly universally quantified.
This is standard practice.

The following sections list some of the resources that I banged my head against repeatedly
while trying to grasp these concepts.

### 📝 Wikipedia

As of this writing, [Equational logic (Wikipedia)](https://en.wikipedia.org/wiki/Equational_logic)
does not contain a very clear explanation.  This is because it
focuses on a particular equational logic, **E**, from the
book "A Logical Approach to Discrete Math"
by David Gries and Fred Schneider.  While it is a very interesting book
([the 1st edition is borrowable from archive.org)](https://archive.org/details/logicalapproacht0000grie),
its presentation of equational logic is somewhat unorthodox:

*   The axiom they call **Leibniz** most other sources call **Congruence**,
    and some sources describe it in a different fashion.  (The book
    explains how these two descriptions are equivalent.)
*   The axiom they call **Equanimity** is not a part of the
    equational logic proper, rather, it exists to support the
    _equational theory of equality_ that **E** is undergirding,
    and to bridge it _to_ the equational logic.  (If you have
    an equational logic supporting a different equational theory,
    for example the equational theory of groups, you don't need
    Equanimity.)
*   They don't have **Reflexivity** and **Symmetry** as axioms, but
    most other sources do.  (These are instead axioms of their
    equational theory of equality, which they can "lift up" to
    the equational level using Equanimity.)

### 📝 Wolfram MathWorld

As of this writing, [Equational Logic (Wolfram MathWorld)](https://mathworld.wolfram.com/EquationalLogic.html)
provides a more orthodox, but rather terse, exposition of equational logic.

Its Axiom 4 is often called **Congruence** elsewhere in the
literature, and is equivalent to Gries and Schneider's **Leibniz**
rule; and its Axiom 5 is often called **Substitution** or
**Replacement** elsewhere.

### 📝 Papers by George F. McNulty

Professor George F. McNulty of USC has written two excellent resources on equational logic:

*   [Field Guide to Equational Logic (1992)](https://www.sciencedirect.com/science/article/pii/074771719290013T)
*   [Equational Logic course notes (Spring 2017)](https://people.math.sc.edu/mcnulty/alglatvar/equationallogic.pdf)

These are both somewhat denser than the encyclopedic entries above, and cover
the connection between equational logic and universal algebra in more depth,
as well as results about equational logic as an object of study in itself.

The course notes have a few highlights definitely worth mentioning here:

*   p.13: A stepwise equational proof of a theorem of ring theory
*   p.21: Birkhoff's axioms for equational logic (basically the same as those on Wolfram MathWorld)
*   also p.21: Tarski's axioms (a more minimal set of axioms; I'm not sure how they work yet)

The field guide lists many results in equational logic, but the most interesting
to me is section 6, which describes Tarski's relation algebra and how formulae of
first-order logic of up to 3 variables (but no more!) may be translated to it.
