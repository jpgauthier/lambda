# λ Interpreter

A substitutional interpreter for untyped λ-calculus that reduces pure λ-calculus expressions to β-normal form written in Scheme R5RS.

λ-expressions are represented as follows:

    e ::= <symbol>             (any symbol except λ is a variable)
    e ::= ( λ <symbol> e )     (function abstraction)
    e ::= ( e e )              (function application)

lambda.scm is divided in three sections:
  * Interpreter: All utility functions for constructing, deconstructing, reducing and interpreting λ-expressions
  * Constructs: All the useful constructs (from church numerals to fibonacci function)
  * Tests: To demonstrate how it can be used and to test all the inner functions
