# Exactly one two-word licence and the number of probes

These results use the measured instrument and edit relation of the
[complexity boundary](ComplexityBoundary.md). The number of probes counts
the nonconstant spectral coordinates. Rates and the constant coefficient
are present even with no probes.

The [fixed-variable quartic specialization](BoundaryCorollaries.md#1-fixed-counts-from-the-fixed-variable-quartic-problem)
uses a layout of constant size and gives the fixed-count conditional
undecidability corollary.

## 1. Duration one in the hardness construction

In the [constraint-logic construction](SingleAdditiveLicence.md), replace
$LL\sim\{AL,BL\}$ by $L\sim\{A,B\}$. Keep the rate floor, all publications,
all singleton licences, the horizon of three, and both supplied endpoints.
The two right-hand words remain distinct. With the full catalogue held
and the same profile at both endpoints, monotonicity puts every state of
a proposed chain at that profile.

For the duration-two version, the mass equation is the duration-one
mass equation multiplied by $\theta_L$. The equation at probe $j$ is
the duration-one coefficient equation multiplied by
$\theta_L\alpha_{Lj}$. The rate floor gives $\theta_L>0$, and the held
calibration gives $\alpha_{Lj}=k/2>0$ for every probe, including the
reserve. Cancellation therefore gives the same lawful laws at the
held profile, with the same prepared tables. Every chain at that
profile and each tolerance is preserved. The PSPACE lower bound
holds with the unique widened licence of duration one. The same
construction still proves the lower bound with duration two. Both
versions use duration-three singleton selectors and the same
inverse-polynomial tolerance.

## 2. One probe can separate rational and real reachability

Take the binary base with its single nonconstant character, singleton
register, identity mark reversal, and cap $1/2$. Use distinct marks
$L,A,B,H,X,Y,U,V$. Set $a=1/4$, use floor $r=1/9$, and hold $L\sim\{A,B\}$,
four singleton licences, and the two calibrations
$\alpha_L=a/2$, $\alpha_H=a$. The singleton licences are
\[
 UH\sim XX,\qquad AH\sim UU,\qquad VH\sim YY,\qquad BH\sim VV.
\]
The policy holds exactly the full licence set. Use the full-support
profile of grade zero with both publications held.

The mass equation forces $\theta_L=\theta_A+\theta_B$. As the floor
bounds the seven other rates below by $r$, their lower bounds together
with $2r$ for $L$ sum to one. Consequently the rate vector is fixed.
Each singleton licence has equal masses since all of its marks have
rate $r$. At the one probe it enforces its indicated product identity.
Writing $x=\alpha_X,\ y=\alpha_Y$ thus gives
\[
 \alpha_U=x^2/a,\quad \alpha_V=y^2/a,\quad
 \alpha_A=x^4/a^3,\quad \alpha_B=y^4/a^3,\quad
 x^4+y^4=a^4 .
\]
Conversely these formulas give all the laws at the held profile.
Indeed each solution has $|x|,|y|\le a$, whence all responses have
magnitude at most $a$ and the cap holds. The fixed register contributes
no further latitude, and the rate and response equations verify the
measured comparisons by orthogonality.

The lifts of $(a,0)$ and $(0,a)$ are lawful rational endpoints. Over the
reals the arc
\[
  x=a\,(1-t)^{1/4},\qquad y=a t^{1/4},\qquad 0\le t\le1
\]
lifts continuously by the displayed formulas. Over the rationals there
are only four axis points. If $xy\ne0$, clearing a common denominator
in $x^4+y^4=a^4$ and taking absolute values contradicts Fermat's theorem
at exponent four. If one coordinate vanishes, the other is $a$ or $-a$.
At fixed rates the binary prepared law for mark $X$ has entry
$r(1+x)/2$ at a base diagonal. Any chain between the two endpoints
must leave the $x=a$ value, changing that entry by at least $ra/2$.
A mesh of $ra/2$ with the strict inequality in the step definition
therefore rules out the connection. Profile monotonicity keeps all
calibrations and licences held. This supplies the one-probe example
from the referee and shows that a real-component test alone cannot
decide rational fine reachability on that subclass.

## 3. Rational polynomial solvability with one widened licence

**Proposition.** The existence of a rational zero of a sparse binary
integer polynomial reduces in polynomial time to fine reachability with
exactly one widened licence, with a growing number of probes. The widened
licence has duration one, all other licences have duration at most four,
and the endpoints lie at a common fixed profile with singleton register
and cap $1/2$. The same reduction works at a supplied positive
inverse-polynomial tolerance. The result is a reduction from rational
solvability. It uses no undecidability premise.

### Bounded equations and a selector gap

Use the circuit and the bounded selector construction of
[§3 of the complexity note](ComplexityBoundary.md#3-supporting-proposition-on-rational-roots).
For clarity, an input polynomial of bit length $L$ has a gate list of
$O(L+1)$ constant, negation, addition, or multiplication gates by
binary doubling and repeated squaring. Put $p_z\in[-1,1]$ at each source
coordinate or gate, $d,s\in[0,2]$, $w\in[1,3]$, and $u\in[-1,1]$.
Homogenize each gate with $d$ and add the slack equation $w^2=2+d^2u$.
Multiply every residual by $s(2-s)$. All residuals have constant degree,
a constant number of terms, and bounded integer coefficients per gate
before the affine box rescaling. Write every coordinate as an affine
function of a unit-interval variable. In particular $t_s=s/2$. Use
the supplied endpoints with $s=0$ and $s=2$ and every other normalized
coordinate zero.

At a rational point with $0<s<2$, $d=0$ would imply $w^2=2$.
Hence $d>0$ and dividing by $d$ gives a solution of the gate equations
and thus a rational root. Conversely a rational circuit solution
$v_z$ gives $d=(1+\sum_z|v_z|)^{-1}$ and $p_z=dv_z$. Choose rational
$w$ in $(\sqrt{2},\sqrt{2}+d^2/4)$ and put $u=(w^2-2)/d^2$.
Then $1<w<2$, and $0<w^2-2<d^2$ since
$w+\sqrt{2}<4$. Hold those values fixed while $s$ traverses $[0,2]$.
The two endpoint faces are full boxes, so this segment and a
rational segment within each face join the supplied endpoints.
If there is no rational root, every lawful rational point has
$t_s=0$ or $t_s=1$.

To compile the bounded residuals, expand each after the affine rescaling.
Use a variable in $[0,1]$ for each partial monomial product. A multiplication
$z=uv$ on the unit interval can be imposed by affine equations and square
graphs. Set $b=(u+v)/2$, $p=u^2$, $q=v^2$, $h=b^2$ and impose
$2z=4h-p-q$. The identity makes $z=uv$ unique and in the unit interval.
Add one affine equation for each residual's final linear combination of
monomials. Thus the new variables have a unique lift on solutions, by
polynomial functions on the box. There are $O(L+1)$ variables and rows,
each of bounded arity and with coefficients of bounded bit length, because
there is only constant work per original gate. The lifted endpoints are
rational of polynomial bit length and can be computed without a rational
root. This transformation fixes the normalized selector coordinate.

### A measured compiler for affine equations and squares

Supply one probe per master coordinate and an occurrence probe wherever
a row needs multiple terms from the same master. A further probe $*$
serves as the reserve for every budget mark. Use distinct nonzero binary
characters as in the constraint-logic construction. With $m$ marks,
take $r=1/(m+1)$, $k=1/(4|I|)$ and $\kappa=1/2$. Hold just one
widened licence, $L\sim\{A,B\}$, and calibrate $L$ to $k/2$ at every
probe. The mass equation and floor force $2r$ at $L$ and $r$ at
every other mark. The probe equations give $x_j+y_j=k$ for
$x_j=\alpha_{Aj}$ and $y_j=\alpha_{Bj}$. Calibrate $x_*=k$,
which gives $y_*=0$. Define $t_j=x_j/k$ at each nonreserve probe.
Use only marks different from $L$ in the singleton licences, so equal
durations guarantee equal word masses in every singleton comparison.

Build one budget mark $T$ for each row
\[
 \sum_j \lambda_j \big|t_j^{d_j}(1-t_j)^{e_j}\big|\le b
 \quad(\lambda_j\ge0,\ b\ge0,\ d_j+e_j\le 2).
\]
There is at most one term at each probe in a row. Use zero coefficients
at unused nonreserve locations. Include two rows at each nonreserve
probe with bound one, whose only nonzero term is $|t_j|$ or
$|1-t_j|$. These inequalities enforce $0\le t_j\le1$. All powers
in the later rows are then nonnegative, so the absolute values there
can be suppressed.

For every row use
$\gamma=1/[2(1+b+\sum_j\lambda_j)]$.
Calibrate $T$ to $\kappa-\gamma b$ at the reserve. Use a common
mark $K$ calibrated to $k$ at every probe, and a selector $S_j$
calibrated to $k$ at $j$ and zero elsewhere. For every nonreserve
$j$, calibrate an auxiliary mark $C_{Tj}$ to $\gamma\lambda_j$
at $j$ and zero elsewhere. Hold the singleton comparison
\[
 S_j T K^{d_j+e_j}\ \sim\ S_j C_{Tj} A^{d_j}B^{e_j}.
\]
At $j$ cancel the nonzero selector and divide by $k^{d_j+e_j}$.
At the other probes both products vanish. Consequently
$\alpha_{Tj}=\gamma\lambda_j t_j^{d_j}(1-t_j)^{e_j}$ is forced,
including at zeros of the coefficient. Summing the magnitudes gives
exactly the required bound, because $\kappa-\gamma b\ge0$.
The pad, selector and coefficient marks satisfy their own budgets
by construction. So does $L$. The inequalities enforcing the box
guarantee that $A,B$ each spend at most $|I|k$.

The remaining operations only use inequalities of this form.

- For a term occurrence at probe $i$ that represents a master $t_j$,
  use the two inequalities $t_i+(1-t_j)\le1$ and
  $t_j+(1-t_i)\le1$. These use distinct probes, with fresh budget
  marks and no new term locations. They force the copy to agree.
- Rewrite an affine equality as $\sum \lambda_j v_j=b$, where
  $\lambda_j\ge0$ and $v_j$ is either $t_j$ or $1-t_j$. Replacing
  a negative summand by its complemented literal also adjusts the
  right side by the absolute value of its coefficient. Impose one
  upper bound on that sum and one on $\sum \lambda_j(1-v_j)$ with
  bound $\sum\lambda_j-b$. Both bounds are nonnegative because
  the affine system comes with feasible endpoints. Use a copy if
  a probe location is repeated in a row.
- For $z=t^2$ impose $t^2+(1-z)\le1$ and
  $(1-t)+t(1-t)+z\le1$. Read the two terms in $t$ in the second
  inequality from distinct equal copies. The first inequality
  gives $t^2\le z$ and the second gives $z\le t^2$. This is
  equivalent to the referee's use of $(1-t)^2+2t(1-t)$ for the
  complement of $t^2$.

Fix the common profile with all licences and calibrations held, full
support, singleton register and grade zero. Use identity reversal.
The profile policy permits exactly the full licence set. The rate,
register and calibrated data and all determined responses verify
native legality in the forward direction. Conversely every lawful
state at that profile supplies unit-interval master values satisfying
the exact affine and square equations. The construction gives a
canonical rational law from any rational solution. Its numerical
coordinates are polynomial functions of the unit box coordinates.
The prepared tables are affine in the responses here since the rates
and register are fixed.

### Transfer and binary cost

The rational segments for the selector problem lift through the circuit
variables and the measured compiler. These maps are uniformly continuous
on the unit box, since the lifts are polynomial. Equal rational
subdivisions therefore give a lawful mesh at every positive tolerance.
Conversely, any chain between the specified profiles stays at that
profile. If the source polynomial has no rational root, its lifted
selector must change between 0 and 1 at some step, changing the response
$x_j$ at the master selector probe by $k$. At fixed rates,
orthogonality gives a response change strictly less than
$|X|\varepsilon/r$ for a physical step of size strictly less than
$\varepsilon$. Take $\varepsilon_0=rk/(2|X|+1)$. The jump is impossible
at that tolerance or any smaller one. This proves equivalence of
solvability with fine reachability and with chain existence at the
supplied tolerance.

There are $O(L+1)$ master and occurrence probes, inequality rows, and
selectors. Using one singleton licence and coefficient mark for every
row–probe pair gives $O((L+1)^2)$ of each, including zero coefficients.
The at-most-four word length follows from $d_j+e_j\le2$. Explicit
calibrations take $O((L+1)^3)$ entries, including the zeros. The
binary-character table is quadratic up to labels, and $|X|<2(|I|+1)$. All displayed
constants and encoded endpoints have polynomial bit length. In
particular the coefficients of the local inequalities have bounded
bit length, all their arities are bounded, and the endpoint values
in each bounded-depth product or square graph are computed by a
constant number of rational operations on bounded-size normalized
endpoint coordinates. The only input-size denominators added by the
instrument formulas are $m+1$, $4|I|$, and the factor $|X|$ in the
projected tables. Summing explicitly over probes in a table entry
has polynomial bit cost even if a common denominator is formed as
the product of the listed denominators. Explicit register and prepared
tables have $m|X|^2$ entries. The reciprocal tolerance is
$(m+1)4|I|(2|X|+1)$. Thus generation is polynomial in the sparse
binary input and the output tolerance is inverse polynomial.

## 4. Tractable zero-probe restrictions

Assume there are no probes. Let $H$ be the integer matrix of exponent
differences for the singleton licences and ratio publications held
at the source. With the two-word licence held at the source, denote its
words by $w_0,w_1,w_2$ and write $f,g$ for the mark-count vectors of
$w_1,w_2$ minus that of $w_0$. For a positive rate vector put
$t=\mu(w_1)/\mu(w_0)$. Then the widened condition says
$t+\mu(w_2)/\mu(w_0)=1$, and $0<t<1$.

Write $p_A,p_B$ for the profiles of the lawful source $A$ and target
$B$. Every rewrite keeps the profile fixed and every cover advances
it, so any edit chain from $A$ to $B$ requires $p_A\preceq p_B$.

### Widened licence absent at the source

If the widened licence is absent at the source, fine reachability is
equivalent to $p_A\preceq p_B$, regardless of the image rank. The
rate interpolation and profile transfer below use only the held
singleton tests in this case.

### Rank at most one

Suppose the widened licence is held at the source and the image of
$\ker_{\mathbb R}H$ under the two rows $f,g$ has dimension at most
one. Fine reachability is decidable in polynomial time on the supplied
lawful endpoints. It holds exactly when $p_A\preceq p_B$ and
$t_A=t_B$.

For necessity, fix the source rate vector as a reference and use the
coordinatewise logarithmic difference $y$. All initially held
singleton rate equations give $Hy=0$. Their right-hand constants
cancel. If the image has dimension zero, the two ratios are constant.
Otherwise write $(fy,gy)=v(a,b)$ along a line with $(a,b)\ne(0,0)$.
The equation for the reference ratio $t_0$ becomes
\[
 t_0\exp(av)+(1-t_0)\exp(bv)=1 .
\]
The left side is strictly convex, since at least one exponent is
nonzero with a positive coefficient. The level has at most two
solutions. Hence the range of $t$ on the source lawful rate set has
at most two values. Distinct values are separated by a positive gap.
Their ratios are continuous on the compact rate simplex with the
positive floor. The sum of one prepared row recovers each rate, so
a sufficiently small prepared-table step cannot cross the ratio
gap. Every cover preserves rates by its stated law-preservation
condition. Fine reachability therefore requires the same ratio.

For sufficiency when the widened licence is initially held, keep
both ratios fixed to their common endpoint values $t$ and $1-t$.
They are positive homogeneous binomial tests because the durations
agree. At fixed profile, the positive rate-fibre theorem gives fine
rational rate moves under these extra tests. There are no spectral
variables. The profile transfer is as in Theorem 2.1. First shrink the
support to the target support at source rates using admissible
registers. The final register satisfies the initial disclosure
conditions, and the held rate tests are independent of the register.
Move the register within that support by affine interpolation and
the rates under the source tests to their target values. Finally
advance the other profile fields at fixed target law. Use covers in
the widened attained order on $[p_A,p_*]$ and $[p_*,p_B]$,
where $p_*$ has the target support and all other source fields.
The hypothesis $p_A\preceq p_B$ gives $p_A\preceq p_*\preceq p_B$.
The profile $p_*$ is attained by using the target register at source
rates, and policies at intermediate covers come from attainment. When the
widened licence is initially absent, the same construction simply
uses the source binomial tests for the numerical phase. The final
law passes the widened licence whenever it is held in the last
phase.

To test the rank condition, subtract the rational row ranks of $H$
and of the matrix obtained by appending $f,g$. This computes the
dimension by quotienting their row spans over $\mathbb R$, and
rational rank computation is polynomial by exact elimination.
The ratios at the endpoints are positive rational products over
explicit word lists and therefore can be exactly compared in
polynomial bit time. The profile test is the one in the main
theorem. This proof gives a fragment of the zero-probe case, even
with changing profiles. Full image rank two can already occur
with three marks and the licence $L\sim\{A,B\}$ in the absence of
other tests, so the rank condition is a genuine restriction.

### A rank-two case via generalized Fermat finiteness

Suppose the two rows have image rank two. Put
\[
 \Lambda=(f,g)(\ker_{\mathbb Z}H)\subseteq\mathbb Z^2
\]
and let $d_0,d_1,d_\infty$ be the orders in $\mathbb Z^2/\Lambda$
of $(1,0),(0,1),(1,1)$, respectively. These orders are finite.
If
\[
 \frac{1}{d_0}+\frac{1}{d_1}+\frac{1}{d_\infty}<1,
\]
then fine reachability holds exactly when $p_A\preceq p_B$ and
$t_A=t_B$, again in polynomial time. This condition
suffices for finiteness of the rational ratios, even before imposing
the floor and normalization.

To see this, fix the source ratios $t_0,1-t_0$. At each prime $\ell$
let $v_\ell$ be its rational valuation. The valuations of every rate
relative to its value at the source form an integer vector in
$\ker_{\mathbb Z}H$. Thus the valuation pair of
$t/t_0,(1-t)/(1-t_0)$ belongs to $\Lambda$. Outside the finite set
of primes in the numerators or denominators of $t_0,1-t_0$, this
is the pair of valuations of $t,1-t$ themselves.

Write $t=A/C$ and $1-t=B/C$ with $A+B=C$ and positive pairwise
coprime integers $A,B,C$. A prime dividing $A$ contributes the
valuation pair $(v_\ell(A),0)$, one dividing $B$ contributes
$(0,v_\ell(B))$, and one dividing $C$ contributes
$(-v_\ell(C),-v_\ell(C))$. At a prime outside the finite set
those exponents must be multiples of $d_0,d_1,d_\infty$,
respectively. Hence every triple has the form
\[
 A=a x^{d_0},\qquad B=b y^{d_1},\qquad C=c z^{d_\infty}.
\]
Here $a,b,c$ are supported on the finite set, and at each of its
primes we choose the least nonnegative residue modulo the
respective exponent. Only finitely many coefficient triples occur.
The pairwise coprimality of $A,B,C$ gives
$\gcd(x,y,z)=1$. Darmon and Granville's Theorem 2 gives finiteness
of proper integer solutions of
$a x^{d_0}+b y^{d_1}=c z^{d_\infty}$ for each of these coefficient
triples. Therefore only finitely many $t$ occur. The same continuity
and fixed-ratio arguments give the decision criterion. The use of
finiteness needs neither a computed list of ratios nor an effective
separation bound. [Darmon and Granville, Theorem 2](https://www.math.mcgill.ca/darmon/pub/Articles/Research/12.Granville/pub12.pdf)

Computing $\Lambda$ and testing its orders takes polynomial bit time.
For a Smith form $UHV$ with unimodular multipliers, the columns of
$V$ at the zero columns of the Smith form give an integral basis of
$\ker H$. Applying the two rows to that basis gives generators for
$\Lambda$. A second Smith form gives an invertible integer coordinate
change $W$ and invariant factors $s_1,s_2>0$ for its quotient.
The order of a vector $e$ is
$\operatorname{lcm}_{i=1,2}(s_i/\gcd(s_i,(We)_i))$.
The integer input and both multiplier computations have polynomial
bit costs and output sizes by the Smith form algorithm. The arithmetic
test of the resulting three reciprocals also has polynomial bit cost.
The prime set used in the existence proof need never be factored by
the decision procedure. [Kannan and Bachem, polynomial Smith form with multipliers](https://doi.org/10.1137/0208040)

A zero-probe example already distinguishes rational chains from real
paths. Take one base and register state and six marks $L,H,X,Y,U,V$.
Hold the widened licence $L\sim\{U,V\}$, the singleton licences
$UH^3\sim X^4$ and $VH^3\sim Y^4$, and the ordinary rate-ratio
publication $\theta_L/\theta_H=17$. For
$x=\theta_X/\theta_H,\ y=\theta_Y/\theta_H$ the licences give
$\theta_U/\theta_H=x^4$, $\theta_V/\theta_H=y^4$, and
$x^4+y^4=17$. Hold the full catalogue and publication at both
endpoints. The endpoints $(1,2)$ and $(2,1)$ give positive rational
laws under normalization by $35+x+y$. Set the rate floor to $1/40$.
Along the positive real arc with $1\le x,y\le2$ the normalizer is
at most $39$, and all six rate ratios to $H$ are at least one.
Thus the real laws stay above the floor. Clearing denominators sends
every rational point to a proper integer solution of
$a^4+b^4=17c^4$, so there are only finitely many ratios by Darmon and
Granville. The two endpoint values of the licence ratio are $1/17$
and $16/17$. The finite-ratio argument rules out fine rational
reachability, although the real arc gives a continuous path. This
strengthens the distinction of the one-probe example, even with a
duration-one widened licence. [Darmon and Granville, Theorem 2](https://www.math.mcgill.ca/darmon/pub/Articles/Research/12.Granville/pub12.pdf)

### An exact scalar criterion for the remaining rank-two problem

There is a useful formulation with all rate coordinates removed
from the chain problem. Let $\mathcal T$ be the possible ratios $t$
of rational rates obeying the floor and the initially held tests.
When the widened licence is initially held and the image rank is
two, fine reachability from $A$ to $B$ is equivalent to
$p_A\preceq p_B$ and
\[
 [\min(t_A,t_B),\max(t_A,t_B)]\ \subseteq\ \overline{\mathcal T}.
\]
The closure here is only of **feasible rational** ratios.

First consider the source rate problem independently of the register.
Use a reference positive source rate vector $\theta^0$ and fix one
mark $m_0$. Use log ratios $z_m=\log(\theta_m/\theta^0_m)$ modulo
adding a constant, represented by $z_{m_0}=0$. Conversely normalize
$\theta^0_m e^{z_m}$ by their sum. This gives inverse continuous
maps, with $Hz=0$ describing the singleton tests. In this finite
linear space the allowed rate floor cuts out the compact convex set
$K$ given by
\[
 \sum_\ell \frac{\theta^0_\ell}{\theta^0_m}\,e^{z_\ell-z_m}
 \ \le\ \frac{1}{\delta}\quad\text{for every }m .
\]
On the open segment between any distinct points of $K$, every one
of these inequalities is strict. Indeed for each $m$ at least one
difference $z_\ell-z_m$ differs between the two points, since the
representatives agree at $m_0$ and are distinct. That exponential
term is strictly convex along the segment, and the other terms
are convex. If $K$ is a singleton the claim holds immediately.

Write $\pi(z)=(fz,gz)$ and
$\gamma(t)=(\log(t/t_0),\log((1-t)/(1-t_0)))$. In rank two the
linear map $\pi$ is onto, since both rows annihilate constants.
Let $F$ be the closure in $K$ of log representatives of rational
rates satisfying the widened test. Its projection via the ratio
is $\overline{\mathcal T}$ by compactness and continuity. Every
ratio in this closure lies strictly between zero and one, since
all three compared masses are positive with uniform lower
bounds on the compact rate simplex and pass the sum test.

For any $t\in\overline{\mathcal T}$, the fibre of $F$ over $t$ is
the entire real log fibre $K\cap\pi^{-1}(\gamma(t))$. If
$\gamma(t)$ is on the boundary of $\pi(K)$, this fibre contains
at most one point: a midpoint of two distinct points would be
interior to $K$, and a surjective linear map takes it to an
interior point of $\pi(K)$. Nonemptiness follows from the
projection of $F$.

If $\gamma(t)$ is interior to $\pi(K)$, it has a lift in the
interior of $K$. To construct one, start at any interior point of
$K$ and extend the segment from its projection to $\gamma(t)$
slightly beyond $\gamma(t)$ while staying in $\pi(K)$. Take any
lift at the extended endpoint and interpolate back to the desired
projection. The case of equal projections uses the starting
point itself. Interior lifts are therefore dense within the
real fibre by convex interpolation with this lift. For such an
interior lift and a sequence $t_n\in\mathcal T$ tending to $t$,
translate the lift by a fixed linear right inverse applied to
$\gamma(t_n)-\gamma(t)$. For large $n$ these points have the
right projection and stay in the interior of $K$.

For each $t_n$ choose any rational rate vector realizing it.
The corresponding log point is a reference for that fibre.
The translation space of its real log fibre before imposing
the floor is the kernel of the integer equations $H,f,g$ and
$z_{m_0}=0$. Choose an integral basis over $\mathbb R$ of that
kernel by clearing denominators of a rational vector-space
basis. Multiplying the reference rates by rational positive
factors raised to these integer vectors and normalizing gives
rational points dense in the real affine log fibre. This
preserves every prescribed ratio because each exponent row is
homogeneous. Approximating the translated interior points
keeps the strict floor inequalities. Thus the chosen interior
lift, and by closure every real lift of $t$, belongs to $F$.

The resulting fibres of $F$ are convex in log coordinates.
A compact set mapping continuously onto a closed interval
with nonempty connected fibres over the interval has connected
preimage of the interval. A separation of that preimage would
project to a cover by two disjoint closed sets, since no fibre
can meet both sides. Conversely, a connected subset maps to an
interval. Therefore the two endpoint rate points lie in the
same component of $F$ exactly under the displayed scalar
criterion.

Finally, for a subset of a metric space with compact closure,
arbitrarily fine chains within the subset are equivalent to membership
in the same connected component of its closure for endpoints in the
subset. The positive floor and normalization put the rate locus in a
compact subset of a finite-dimensional real space, so its closure is
compact. In that closure, the classes reachable by strict
$\varepsilon$-steps are closed and open. The intersection of the classes for
$\varepsilon=2^{-j}$ is connected: a separation would give two
disjoint compact pieces with positive distance. Disjoint
neighbourhoods of the pieces can be chosen with positive
distance as well. By compactness the nested classes are
eventually contained in their union, and sufficiently fine
chains cannot cross the gap. Conversely a component lies in
each such class. A finite chain in the closure can be
approximated pointwise by the original set at a slightly
larger mesh, keeping the supplied endpoints. This proves the
equivalence for the rate locus. To return to actual native
chains, the necessity uses the prepared row-sum modulus,
with a cover keeping the rates fixed. For sufficiency, carry
out the support and register transfer of §4 and carry the
rate chain at the fixed intermediate profile, then use the
final covers at the target law. The native table is linear in
the rates for the fixed register in this phase.

This gives an exact residual problem for zero probes. The
finite-ratio tests above settle the rank-at-most-one and
hyperbolic rank-two cases. For an initially held licence of
rank two with reciprocal sum at least one, deciding interval
containment in the closure of the feasible rational ratios
remains open here. The reduction in §3 does not bound the probe
count. Neither a no-probe hardness result nor a general
decision bound for fixed probe counts is established here.

## 5. Literature and scope

The duration-one result uses the existing constraint-logic reduction
and cancellation in the diagonal word calculus. The exponent-four
input in the one-probe example is classical. The example applies it
to the rational-point interpretation of the measured instrument.
Real roadmaps such as Canny's concern real configurations and their
components. The transfer of polynomial solvability in §3 uses the ordinary source
problem, the existing rational selector construction, and the referee's
budget idea. Its particular restriction is one
short measured comparison, a growing probe set, and ordinary
singleton constraints throughout the rest of the catalogue. [Canny](https://people.eecs.berkeley.edu/~jfc/papers/88/Castoc88.pdf)

The [status discussion for rational solvability](ComplexityBoundary.md#5-prior-work-and-scope-of-the-contribution)
continues to treat the reported October 2026 undecidability claim as
independently unverified. A PSPACE upper bound on the whole exactly-one
class would put rational polynomial solvability in PSPACE by §3.
The number of probes used by that reduction grows with the input.


Focused Paperclip searches on rational trinomial loci and rational
polynomial solvability in restricted Markov reconfiguration
(`s_e3cc630e`, `s_15cbd8ec`) located generalized Fermat work and
broader computational precedents. They did not locate these measured
instrument reductions or the scalar closure criterion. The
zero-probe finiteness and bit bounds use the specific primary
results of Darmon–Granville and Kannan–Bachem cited above.

## 6. Lean correspondence

- [SingleAdditiveLicence.lean](MovingProjection/SingleAdditiveLicence.lean)
  verifies both lengths. The common tail is empty in the duration-one
  case. The coefficient calculation cancels the nonzero rate and
  response factors for the duration-two case, giving the same equations
  used by the lifting and decoding proofs. The combined
  [complexity theorem](MovingProjection/ComplexityTheorem.lean) checks
  either choice of duration for the hard arm.
- [FermatProbe.lean](MovingProjection/FermatProbe.lean) gives the actual
  one-probe experiment, lawful endpoints, unique widened licence and
  gap in the prepared-table metric. It uses Mathlib's
  `fermatLastTheoremFour` over the rationals. The continuous real
  quartic arc is also checked. Interpreting its real-valued responses
  as a real-valued Markov instrument uses the same kernel formulas
  in the written proof, because the native Lean state type is rational.
- [CalibratedResponses.lean](MovingProjection/CalibratedResponses.lean)
  builds the native catalogue from response budgets, calibrations and
  singleton words and proves both directions of the fixed-profile
  legality correspondence, including the forced rates.
  [ResponseBudgets.lean](MovingProjection/ResponseBudgets.lean) checks the
  actual timed words and calibrations for the dense row compiler.
  `assign_lawful` and `decode_solution` prove forward and reverse
  transfers. `fine_iff_box` proves both mesh directions and
  `no_native_chain_of_selector` proves the obstruction at the stated
  native tolerance. The affine, copy, square and product identities
  are checked in the same file. The choice of occurrence indices and
  conversion of a supplied polynomial's gated residual list to that
  row array, and the binary encoding and running-time bounds, are on
  paper. The rational selector argument for the gate equations is
  also checked in the existing
  [ArithmeticEvents.lean](MovingProjection/ArithmeticEvents.lean).
- [NoProbeRatios.lean](MovingProjection/NoProbeRatios.lean) checks the
  strict convexity argument excluding three solutions of the rank-one
  scalar equation. The full zero-probe log-fibre and profile argument,
  the lattice finiteness application and the bit analysis are written
  proofs. The external generalized Fermat finiteness theorem is used
  on paper.
