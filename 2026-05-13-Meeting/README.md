This meeting we have:
- A recap of motivation as to why we are interested in SOGATs
	- [ ] It could be interesting to write this up nicely in some way, as our reasoning is quite different/ not covered by the reading notes [#2](../../issues/2)
- Gone through the exercises and some of our implementations in Agda, up to the definition of a dependent monoid

Over the next week we intend to:
- Continue to read Chapter 2, and work through more exercises. 

---
Some notes:
- From Exercise 2:
	- With respect to "Define all the monoids with sort $\{ff, tt\}$", we considered the question on paper of "How many monoids are there with sort $\{ff, tt\}$". This can be done with a Cayley table and we landed on 4.
- Derivable = We only use the data of the theory to define a new operation
- Admissable = if you add a new operation, it doesn't break the assumptions you had before
- When looking at the definition of dependent monoid, we dived into how `subst` works and can be used for defining relations when the types don't normalise to the same value.

