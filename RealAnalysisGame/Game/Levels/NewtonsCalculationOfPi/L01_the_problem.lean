import GameServer

World "NewtonsCalculationOfPi"
Level 1
Title "Newton's Problem: Computing π"

Introduction "
# Cambridge, 1666: The Plague Year

Isaac Newton, age 23, has fled Cambridge due to the plague. In his mother's farmhouse
in Woolsthorpe, he's about to revolutionize mathematics.

The problem: **How do you compute π to arbitrary precision?**

Ancient methods like Archimedes' polygonal approximations are painfully slow.
After inscribing a 96-sided polygon in a circle, Archimedes could only determine
that π lies between 3.1408... and 3.1429...

Newton realizes he needs something completely different: **infinite series**.

But how do you turn the geometric constant π into an infinite sum?

Newton's insight: Connect π to areas under curves, then use infinite series to
compute those areas.
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
