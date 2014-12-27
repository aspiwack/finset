Finite sets of countable types in Coq
=====================================

Finite objects on countable types can often be represented in a extensional way in Coq
(that is, such that the native equality of Coq validates the appropriate extensionality
principles). This library is an attempt at implementing such objects. The resulting
data types are quite inefficient and are not appropriate in an implementation, but can
be very helpful as implementation tools.

For now the only implemented structure are finite subsets. Potential extensions are finite
multisets and functions with finite support.

### Licence ###

Cosa and all of its files are distributed under the CeCILL v2.1 licence. It is a licence in
the spirit of Gnu's GPL maintained by three French academic institutes. See the `LICENCE`
file for details.


Principles
----------

The main ingredient is that quotients of countable types by decidable equivalence relations
can be defined extensionally in Coq. This concept has been described and exploited in
[Cyril Cohen's PhD thesis](http://perso.crans.org/cohen/phd/) (see in particular Chapter 6).

This rests on two pillars. One is a consequence of Hedberg's theorem that types with
decidable equality have uniqueness of identity proofs: `{ x:A | P x }` is extensionally
a subset of `A` when `P` is decidable. The second is that countable types support
indefinite description, _i.e._ `(∃x,P x) → {x | P x}`, for `P` decidable.

Finite sets, then, are expressed as such a quotient of the type of lists (lists of
countable types are themselves countable).


Design
------

### Decidable propositions ###

This library uses a type of strongly decidable propositions rather than booleans.
The type is as follows
```
Record DProp := {
  Holds :> Prop;
  Denies : Prop;
  dec :> { Holds } + { Denies };
  contradictory : Holds -> Denies -> False
}.
```
The reason to prefer this type to booleans is essentially what Bob Harper explains
in his blog post [Boolean blindness](https://existentialtype.wordpress.com/2011/03/15/boolean-blindness/).

### Countable types ###

Since the encodings as natural numbers, that the countable types in this library enjoy,
are not particularly efficient. It was found preferable to use a type class to define
countability, so that instances can be inferred automatically.

### Finite sets ###

One advantage of the definition of finite set given in this library is that they are
defined simultaneously on all the countable types. As a result, syntax for defining
sets by comprehension can be given. Because finite sets of countable types are
themselves countable, comprehension primitives form, conveniently, a monad.


Documentation
-------------

A `coqdoc` generated documentation is [available](http://aspiwack.github.io/finset/toc.html).

The sources are organised as follows:

* `FinSet` is the file containing the interface for finite sets
* The `Lib` directory contains general purpose libraries: `DProp` defines the decidable
  propositions, `CEExt` contains extension to the `Coq.Logic.ConstructiveEpsilon` library
  from Coq's standard library, `LibSet` contains extension to Coq's list library mostly
  pertaining to lists viewed as sets.
* The `Quotients` directory contains libraries used to define quotients: `Retract` contains
  a theory of retraction, `Countable` defines countable types and `Quotient` define
  extensional quotients of countable types by decidable equivalence relations.


Installation
------------

The library needs a recent version of Coq development version to compile. When
version 8.5 is released, it will be the reference version.

To compile use the following command:
```
coq_makefile -f _CoqProject -o Makefile && make
```

Then install (probably as root) with:
```
make install
```