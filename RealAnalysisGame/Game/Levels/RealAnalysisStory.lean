import Game.Levels.RealAnalysisStory.L00_the_problem
import Game.Levels.RealAnalysisStory.L02_rfl
import Game.Levels.RealAnalysisStory.L03_rw
import Game.Levels.RealAnalysisStory.L04_ring_nf
import Game.Levels.RealAnalysisStory.L05_use
import Game.Levels.RealAnalysisStory.L06_intro
import Game.Levels.RealAnalysisStory.L07_specialize
import Game.Levels.RealAnalysisStory.L08_obtain
import Game.Levels.RealAnalysisStory.L09_big_boss

World "RealAnalysisStory"
Title "Level 1: The Story of Real Analysis"

Introduction "
# A First Course in Real Analysis

You may want to pull the left-most slider all the way to the right; what follows is a discussion
between \"Socrates\" and \"Simplicio,\" which hopefully  explains what it is we're trying to do here.

Simplicio: What is \"Real Analysis\"?

Socrates: Oh, it's just Calculus, but done \"right\".

Simplicio: Huh? Why does Calculus need a new name? What's wrong with it?

Socrates: Well, nothing really. Quick: what's a derivative?

Simplicio: Easy! If I have a function $f : \\R \\to \\R$ and it's differentiable at $x$, then the
derivative is $f'(x) := \\lim_{h \\to 0}\\frac{f(x+h) - f(x)}{h}$. This represents the \"instantaneous\" slope
of the graph of the function $y=f(x)$ at the point $(x, f(x))$.

Socrates: Very good! And tell me please, what is an integral?

Simplicio: That's easy, too! If you want to integrate our function $f$ along an
interval, $[a, b]$, say, you pretend that you have infinitely many, infinitely small rectangles, work out their
areas as base times height, and add them up:
$\\int_a^b f(x)dx := \\lim_{N\\to\\infty} \\sum_{j=1}^N \\frac{b-a}{N} f\\left(a + j\\frac{b-a}{N}\\right)$


Socrates: Great. And what are the two Fundamental Theorems of Calculus?

Simplicio: These too are easy! The first one says that if you make a new function by integrating $f$
up to a variable amount, $x$, that is, let
 $F(x) := \\int_a^x f(t)dt$, then the derivative of the new function is just $F'(x) = f(x)$.

Socrates: And the second?

Simplicio:
The second one says that, conversely, if $F$ is an antiderivative of $f$, that is, $F'(x)=f(x)$, then
it's easy to work out the area under the curve, because
 $\\int_a^b f(x)dx = F(b) - F(a)$.
So differentiation and integration are inverse operations!

Socrates: Perfect. Now, here's the problem. You used words like \"limit\", \"infinitely many\", \"infinitely small\", and so on. What do they *actually* mean?

Simplicio: Oh, you know, it's when something  happens \"eventually\". You just have to get used to
the feel of it.

Socrates: Hmm yes, I see. I agree that that's an OK way to think of it, for a while at least, and one that suited Newton (who
was quite uncomfortable with such words), and Leibniz (who was more care-free here), the two 17th century inventors of
calculus (if you don't count people like the ancient Greeks Eudoxus and Archimedes, or the 14th century Indian Madhava... but this isn't a history lesson). Leibniz taught the Bernoulli
brothers (the world's \"first AP Calc students\"!), who taught, among others, the Marquis de l'Hopital, and the great Leonhard Euler (the first \"Calc native\"), who taught the rest of us. All was going quite well... and then came the 19th Century.

Simplicio: Huh? What happened in the 19th Century?

Socrates: Well you see, a guy named Augustin-Louis Cauchy came along (roughly in the 1810s), and started making a fuss that we weren't really doing things perfectly \"rigorously\".
He set out to reprove the theorems of calculus using precise definitions rather than hand-waving.
He was making great progress, including proving statements like: the limit of continuous functions is continuous.

Simplicio: Sure, that sounds perfectly reasonable. A limit is a continuous process, so you do that to
continuous functions, and of course in the end you should get something continuous, too. No?


Socrates: Well, the problem is that around the same time, a guy named Joseph Fourier was going around claiming
 that he could add up a bunch of sines and cosines, and get basically any function he wants, including, say, the discontinuous sawtooth!

Simplicio: What?!

Socrates: Look for yourself: Here's a graph of $\\sum_{n=1}^{100}\\frac1n \\sin(nx)$. As you take 100
out to infinity, Cauchy claims that this will get
closer and closer to a sawtooth function!

Simplicio: Whoa. Wait, I can think of an even easier example: just look at the simplest family of
polynomials, $f_n(x) = x^n$, on the unit interval $[0,1]$. When you take high powers of any point
strictly less than $1$, that goes to $0$ in the limit, but powers of $1$ itself always stay at $1$.
So the limiting function is discontinuous, too! What the heck is going on here?

Socrates: Very good, Simplicio! Exactly right, between Fourier and Cauchy, they \"broke math\".
 You break it, you buy it!

Simplicio: Ok, so what's the right answer, how *do* you do calculus rigorously?

Socrates: Not so fast! Things got even worse, and by the mid-19th century, people realized that
we don't even know what the real numbers *are*!

Simplicio: What? What do you mean, what are they? Here they are right here: There's zero, and one, and $-2$, and $\\frac35$, and
$\\sqrt 2$, and $e$ and $\\pi$. What's the problem?

Socrates: Well, do you remember that you need something called the Intermediate Value Theorem
in calculus?

Simplicio: Sure, if you have a continuous function, and it goes from being negative to being positive,
then it has to cross zero at some point in between.

Socrates: Very good. Tell me about the function $f : x \\mapsto x^2 - 2$. (We say: \"$f$ maps
$x$ to $x^2-2$\". Note that we write $f : \\R \\to \\R$ to mean that $f$ takes real numbers to real numbers, but
replace $\\to$ with $\\mapsto$ (see the tail on the second arrow?) when we want to say what happens to a particular input $x$ under the action of
$f$. Let me remind you that $x$ here is a dummy variable, so it's the same function if we'd said $f : u \\mapsto u ^ 2 - 2$.) In particular, what happens to $f$ on the rational numbers?

Simplicio: Ok, well if $x$ is a rational number, then so is $x^2$, and hence so is $x^2-2$.
So actually, we could say that $f : \\Q \\to \\Q$, that is, $f$ maps rational numbers to rational numbers.
Over the reals, the graph of $y=f(x)$ is a simple parabola.
But you'd asked me about the Intermediate Value Theorem. Hmm. When $x=0$, I know that $f(x)$ will
be $f(0)=0^2-2=-2$ which is negative. And when $x=2$, $f(2)=2^2-2=2$ which is positive.

Socrates: Go on...

Simplicio: So there's a root of $f$ somewhere between $0$ and $2$. But the place where $f$ crosses the $x$-axis is at $x=\\sqrt2\\approx 1.41\\dots$.

Socrates: And what did the Pythagoreans know about this number?

Simplicio: Supposedly one of them, Hippasus, figured out that $\\sqrt2$ is irrational, which ruined
their entire theory of geometry and form (they originally believed that *all* numbers were rational); legend has it
that Hippasus was drowned at sea for his herecy.

Socrates: So...

Simplicio: So wait, if we just restrict to rational inputs, then this parabola is negative, and then
it's positive, and it *never* crosses zero?! But there's tons of rational numbers almost everywhere you look. So what makes the real numbers different from the
rational numbers, so that the Intermediate Value Theorem actually holds?

Socrates: Ah! Now, my friend, we are ready to begin.
"
