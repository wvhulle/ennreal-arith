# Tasks


## Comments

Only write comments when they are absolutely necessary. Do not write comments that are obvious from the code itself.

## Compatibility with norm_cast and norm_num

Check whether there is a way to import this library and extend norm_cast norm_num or other existing arithmetic or field simplification tactics. It would be cool if this library was just like an addon or extension that could be easily used. 

You should be careful to do updates in-place, step-by-step, introducing a minimal amount of new errors as possible. 


## Nested expressions

Add more test lemmas. The lemmas should contain more complicated arithmetic expressions. They should contain deeply nested computations. You should extend this project to be able to work with several layers of addition, fractions, inverse and multiplication equalities. 

If you think the complex arithmetic expression is a composite problem, you should first solve the partial problems in the relevant sub-modules of this project. Each module has to compile before you switch to another module.

Add a manual version of each test lemma first where you explicitly try to prove something with tactics. When it works, you add an automatic version that uses the tactic (or one of the sub-tactics) we wrote. 

You should not introduce too many new code syntax / semantic problems when you try to support more complicated arithmetic expressions. Keep everything consistent while adding functionality. 


## Remove duplicated lemmas (less important)

When you are sure some of the sub-modules contain duplicate lemmas (for example they same arithmetic pattern 1 * 2 or 2 * 4 with two different sets but equivalent numbers), you remove the duplication. Do not remove the manual versions of the lemmas for documentation purposes. 


## Performance


Also, dont forget to look at the performance aspect. Try to investigate (after verifying this project works for extended arithmetic expressions) if there are no (or minimal) performance issues that people would run into if they try to apply this library. 

- More precisely, check whether the heuristics in each tactic are optimal. 
- Try to check whether people who call the tactics in this library might encounter infinite loops or recursion and fix if you encounter such situations.

## Research generalization

When you are done writing support for more complicated, deeper nested arithmetic expressions in ENNReal, you can start thinking about how to support more general types of algebraic structures. 

Currently, the ENNReal type is quite specific. There are more generic type classes available in Mathlib that have similar properties as ENNReal. You may want to see how this project can be generalized to type classes such as OrderedCommSemiring or equivalent concepts. Recently, OrderedCommSemiring became deprecated and CanonicallyOrderedAdd and NoZeroDivisors replace the older structure. 

Explore if the current codebase (if there are no other compilation problems) can be generalised to support these more general structures.

