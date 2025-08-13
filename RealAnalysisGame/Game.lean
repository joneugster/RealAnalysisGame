import Game.Levels.RealAnalysisStory


-- Here's what we'll put on the title screen
Title "An Introduction to Formal Real Analysis"
Introduction "
# Welcome to Real Analysis, The Game!

This course takes you through an Introduction to the Real Numbers, rigorous ε-δ Calculus,
and basic Point-Set Topology. To get started, click on
**\"Level 0: The Story of Real Analysis\"**, and good luck!

"

Info "
*An Introduction to Formal Real Analysis - Interactive Edition*

## About this Course

This course follows the historical crises that forced mathematicians to rebuild
mathematics from the ground up in the 19th century. You'll learn why concepts
like ε-δ definitions became necessary and how to use them to do advanced calculus.

## Credits

* **Course Design:** By Alex Kontorovich alex.kontorovich@rutgers.edu
* **Interactive Implementation:** Lean 4 Game Engine
* **Mathematical Content:** Following Rudin, Stein-Shakarchi, etc.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "A First Course in Real Analysis"
CaptionLong "Learn real analysis through the historical crises that forced mathematicians to rebuild calculus from the ground up in the 19th century."

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
