You are given two languages:

1. The language L1 of arithmetic expressions 
on natural numbers n in N is defined by the standard grammar:

U ::=  n | U + U | U * U

2. A toy assembly language L2 constisting of all words Prog
whose grammar is defined by:

Prog  ::= Begin;A
A     ::= Opper;A | End
Opper ::= Set n | Load x | Store x | Add x | Mul x

where x is a value representing 
an address in memory (we can assume x is 
a natural number) and n is a natural number.

The toy assembly language is run on a single accumulator computing machine.
The meaning of the operations Opper are as follows: 

Set n puts the value n into the single accumulator cell.

Load x puts the value stored in the memory under the index x
into the accumulator.

Store x puts the value in the accumulator into the
memory cell indexed by x.

Add x adds the value stored under 
the index x to the accumulator and the result
of the addition is put into the accumulator. In a similar manner, we 
define the meaning of Mul x.

Begin zeroes the indexed memory cells and the accumulator.
End zeroes the indexed memory cells leaving the accumulator intact.

Task. In Agda define:
a) the semantics function s1 : L1 -> N
b) the semantics function s2:  L2 -> M. Here M represents 
a formal model of the set of all states of the above machine 
with memory indexed by natural numbers and a special accumulator
cell.

Moreover, define a compiler c : L1 -> L2 and prove (in Agda)
that t * s1 = s2 * c, where t : N -> M is a map that takes 
a natural number n and assigns to it a state of the machine 
with the accumulator cell occupied
by the value n and the indexed memory cells all set to zeroes. 
