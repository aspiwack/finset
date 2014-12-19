(** This file defines the countable types. There is some liberty in
    the notion of countable in a constructive setting. In this file we
    choose countable types to be equipped with a retraction into the
    natural number (which, because of [ConstructiveEpsilon], is
    equivalent to a surjection from natural number and decidable
    equality). Decidability of equality plays an important role in the
    design of concrete quotients of countable types, both to lift
    [ConstructiveEpsilon] and to define quotients.

    A type [A] is called countable if [option A] is a retract of the
    natural numbers. When [A] is inhabited, then it is equivalent to a
    retraction of [A] into the natural numbers, but this definition
    also includes the empty set. *)