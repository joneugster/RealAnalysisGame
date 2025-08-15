import GameServer

World "NewtonsCalculationOfPi"
Level 1
Title "Newton's Problem: Computing π"

Introduction "
# Cambridge, 1666: The Plague Year

Isaac Newton, age 23, is home from  Cambridge, quarantining to escape an outbreak of the Plague, when he decides to invent calculus. (And what did you manage to accomplish during your COVID quarantine?..) In his mother's farmhouse
in Woolsthorpe, he's about to revolutionize mathematics.

Newton starts to mess around with the Binomial Theorem. He knows Pascal's triangle,
like everybody else, but decides to do something crazy with it.
"

/-- This level has no proof - it's pure exposition. -/
Statement : True := by
  trivial

Conclusion "
Newton's plan:

1. Find a curve whose area under it equals π/6
2. Expand that curve as an infinite series
3. Integrate the series term by term
4. Compute π from the resulting infinite sum

Sounds impossible? Let's see how Newton pulled it off...

**Next:** The geometric setup that makes it all work.
"
