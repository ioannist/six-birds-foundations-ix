# Fixed-variable quartics, the algebraic boundary, and real components

These are consequences of the proofs in [Proof.md](Proof.md),
[ComplexityBoundary.md](ComplexityBoundary.md), and
[BoundedProbes.md](BoundedProbes.md). The algebraic formulations carry no
instrument profile. Rational chains use supremum-norm steps, and real
paths use the usual topology.

## 1. Fixed counts from the fixed-variable quartic problem

**Theorem.** For every fixed $N$, there is a polynomial-time many-one
reduction from rational solvability of integer polynomials of total degree at
most four in $N$ variables to each of the following problems in the
instrument class of the [complexity theorem](ComplexityBoundary.md).

1. Fine reachability between two supplied lawful rational states.
2. Existence of a chain between those states at a single prescribed positive
   rational tolerance.

The number of probes, marks, base states, licence names and publication names,
and the tolerance in (2) are fixed as functions of $N$. The instrument has
exactly one widened licence, of duration one, and the two right-hand words
are distinct. All other licences compare singleton words of duration at most
four. The register is a singleton, reversal is the identity, the response
cap is $1/2$, and the only policy set is the full licence catalogue. Both
endpoints have the same full-support grade-zero profile with every audit and
licence held. The calibration values can depend on the input polynomial.

**Conditional corollary.** If Corollary 1.2(3) of Bhargava–Burungale,
[*A Diophantine definition of `ℤ` in `ℚ`*, arXiv:2611.16130v2](https://arxiv.org/html/2611.16130v2)
holds, each problem is undecidable at some fixed probe and mark counts and the
second problem is undecidable at the corresponding fixed positive tolerance.
The cited corollary states undecidability of rational solvability of integer
quartics for some fixed number of variables. The following reduction is
independent of the proof of that external arithmetic statement. We verified
the statement and its locator in v2, and do not independently audit the
arithmetic proof.

### The selector and its two faces

For $f(v)=\sum_{|a|\le4}c_a v^a$, use the dense list of exponent vectors of
total degree at most four, including slots whose coefficient is zero. Put
$$
  F(p,d)=\sum_{|a|\le4}c_a p^a d^{4-|a|}.
$$
Use $p_i\in[-1,1]$, $d\in[0,2]$, $w\in[1,3]$, $u\in[-1,1]$, and
a selector $s\in[0,1]$. The equations are
$$
 s(1-s) F(p,d)=0,\qquad
 s(1-s)(w^2-2-d^2u)=0 .
$$
This uses the normalized selector of the duration-one compiler. In terms of
the selector in [BoundedProbes.md, §3](BoundedProbes.md#3-rational-polynomial-solvability-with-one-widened-licence),
replace that selector by $2s$ and divide both equations by the common factor
four. Affinely normalize each of the remaining coordinates to $[0,1]$.
Take the endpoints with $s=0,1$ and every other normalized coordinate zero.
The equations hold everywhere on both faces.

At a rational point with $0<s<1$, the slack equation excludes $d=0$
because $w^2=2$ has no rational solution. The identity
$F(dv,d)=d^4 f(v)$ gives the root $v=p/d$. Conversely, for a rational root
$v$ take $d=(1+\sum_i|v_i|)^{-1}$ and $p=dv$. Choose rational $w$
strictly between $\sqrt2$ and $\sqrt2+d^2/4$ and put $u=(w^2-2)/d^2$.
Here $1<w<2$ and $0<u<1$, since $w+\sqrt2<4$. These coordinates can be
held constant while $s$ runs from zero to one. One affine segment on each
face connects this middle segment to its corresponding supplied endpoint.
All three segments are lawful and have rational points at rational parameter
values. When $f$ has no rational zero, the only lawful rational selector
values are zero and one.

### A measured compilation with a layout depending only on $N$

After affine normalization the two residuals have degree at most six. Fix
the monomial slots of degrees one through six in all $N+4$ normalized
variables and compute their values by consecutive products in a fixed
order. A zero coefficient uses the same slot. For every binary multiplication
$z=uv$, introduce $z,b,p',q',h$ and require
$$
 b=(u+v)/2,\qquad p'=u^2,\qquad q'=v^2,\qquad h=b^2,\qquad 2z=4h-p'-q'.
$$
They uniquely give the displayed quantities in the unit box, with $z=uv$.
Two final affine equalities set the constant terms plus the weighted sums
of the monomial slots to zero. All new values are fixed polynomial functions
of the normalized inputs.

Convert the affine and square equalities to pairs of inequalities as in
[BoundedProbes.md, §3](BoundedProbes.md#3-rational-polynomial-solvability-with-one-widened-licence).
In detail, a signed affine combination is written as
$\sum_j\lambda_j v_j=b$ with $\lambda_j\ge0$ and each $v_j$ a unit
coordinate or its complement. A term with coefficient $-a<0$ is written as
$a(1-t)-a$. Set $L=\sum_j\lambda_j$ and impose upper bounds $b$ on the
sum and $L-b$ on the sum of complementary literals. The polynomial
assignment at each face corner satisfies every affine equality in the
unit box before it is translated into rows. This gives $0\le b\le L$
for every affine row pair.

For a square $z=t^2$, use the two inequalities in
[`ResponseBudgets.square_rows`](MovingProjection/ResponseBudgets.lean#L571),
$$
t^2+(1-z)\le1,\qquad (1-t)+t(1-t)+z\le1.
$$
The first gives $t^2\le z$ and the second gives $z\le t^2$ because
$(1-t)+t(1-t)=1-t^2$. Both rows are tight at $z=t^2$, including
$(t,z)=(0,0)$ and $(1,1)$. Use a distinct occurrence coordinate for
every term slot, even when its coefficient is zero. In the second
square row the linear complement $1-t$ and the mixed term $t(1-t)$
use two distinct copies of $t$. The mixed term uses one slot with
exponents $(d_j,e_j)=(1,1)$ at its copy. Enforce equality of each
occurrence $v$ with its master $t$ by $v+(1-t)\le1$ and
$t+(1-v)\le1$. The compiler's built-in box rows enforce that all these
coordinates are in $[0,1]$.

Let $U$ be the number of binary multiplications in the fixed layout,
$H$ the number of nonconstant monomial slots and $C$ the number of
term occurrences before adding copy rows. Each multiplication has two
affine equalities with three and four slots per row, and three square
equalities with two and three slots in their respective rows. The two
final affine equalities have $H$ slots in each of their four rows.
Keeping all slots gives $C=29U+4H$. With this scheme
$|J|=N+4+5U+C$ is the number of nonreserve probe coordinates and
$|T|=2(5U+2)+2C$ is the number of rows other than the built-in box rows.
Both depend only on $N$. Read back the original $N+4$ master
coordinates from a solution of those rows. The copy, square, affine and
product identities prove in order that it is a solution of the two gated
equations. Conversely the polynomial assignment just given lifts every
source solution, keeps the original master coordinates, and in particular
fixes $s$ under readback. On a normalized affine segment each original
coordinate varies by at most the difference of the parameters. A product
of $e$ unit factors varies by at most $e$ times that difference by
telescoping. Thus the graph lift has a positive rational common slope bound
on all such segments: copies have their master's bound, and for sums with
fixed coefficients one adds the absolute coefficients times the factors'
bounds. This proves the segment estimate for all intermediate coordinates.

Use [ResponseBudgets.lean](MovingProjection/ResponseBudgets.lean) on these
rows. There are $|J|+1$ probes including the reserve and
$m=3+|\mathrm{Aux}(J,T)|$ marks, where $\mathrm{Aux}(J,T)$ and the
catalogues are fixed finite sums and products of $J,T$. The base is the
binary parity base for $|J|+1$ probes. Set $k=1/(4(|J|+1))$ and
$r=1/(m+1)$. The unique widened comparison $L\sim\{A,B\}$ and the floor
fix the rates to $2r$ at $L$ and $r$ elsewhere. At each probe the
comparison imposes the sum of the two toggle responses equal to $k$.
The row compiler fixes the reserve and decodes each normalized coordinate
as the corresponding first toggle response divided by $k$. The row
inequalities are exactly the budget tests on the row marks with nonnegative
reserved response. All zero slots occur in the same finite catalogue.
The singleton comparisons have duration $2+e_j+d_j\le4$. Both the
pure square and the mixed term have total degree two and duration four.
The linear slots and copy rows have degree one on their nonzero terms.
Complementing an affine literal changes its exponents between $(1,0)$
and $(0,1)$, preserving duration.
The duration-one comparison, its floor, the row equations and the comparison
duration are those of [BoundedProbes.md, §3](BoundedProbes.md#3-rational-polynomial-solvability-with-one-widened-licence).

Lift the two supplied face corners by the polynomial row assignment, then
by the compiler's measured-law assignment. In particular, the fixed
layout includes the product $s\cdot s$ even if its coefficient is zero.
At the second corner $s=1$, its two squared inputs and squared average
all equal one and its product is one, so every square and affine row of
that gadget holds. Both lifts use only the given coordinates and the
input coefficients. If $f$ has a root, subdivide the three segments
at rational parameters, using the
slope bound for the row lift and the measured lift estimate from
`ResponseBudgets.lift_chain`. This gives a chain at every positive
tolerance. If $f$ has no root, every intermediate law is at the shared
profile by profile monotonicity, and so every step decodes to a row step.
At tolerance
$$
                       \varepsilon_0=\frac{r k}{2|X|+1},
$$
the decoded step changes $s$ by strictly less than one. This is
`ResponseBudgets.nativeMesh J T X 1` with the singleton register. The
row scales and calibration values do not enter this cutoff. Its factors
$r$, $k$ and $|X|$ are fixed by the counts above. In a no-instance the
selector of every lawful rational point is zero or one, so such a chain
cannot go from zero to one. This proves both reductions with the same
endpoints and fixed tolerance.

For fixed $N$ only a constant number of arithmetic operations is used to
form each expanded coefficient from the input integers. Converting to
bounds, forming each row scale
$1/[2(1+b+\sum_j\lambda_j)]$, computing calibrations and lifting the face
corners likewise use a number of rational operations bounded in terms of
$N$. At each stage all rational numerators and denominators have
$O_N(L+1)$ bits for input bit length $L$, by the sum and product bounds
for rational arithmetic. A sparse coefficient list can be completed with
zeros to the fixed dense layout in polynomial time, and the
explicit instrument and law tables have the stated bit bound even if the
constant binary base is large. Ordinary binary arithmetic gives a
polynomial-time transducer. The conditional corollary uses the fixed
$N$ in the cited statement.

**Lean correspondence.** [QuarticSelector.lean](MovingProjection/QuarticSelector.lean)
checks the dense homogeneous identity, the normalized lawful endpoint
faces, the interior root extraction, and the three explicit segments
(`homogeneous_scale`, `interior_hasRoot`, `no_root_selector`,
`root_has_three_segments`). The fields of `RowRealization` are the
coordinate inclusion, polynomial lift and readback laws, and slope estimate
proved in the fixed-layout assembly above. Given those fields,
`RowRealization.native_boundary` checks both endpoint equivalences using
the exact native tolerance and checks that exactly one licence is widened.
`RowRealization.nativeEndpoints_distinct` checks that selector readback
distinguishes the two lawful states.
[ResponseBudgets.lean](MovingProjection/ResponseBudgets.lean) checks
row-to-instrument compilation, elementary copy and square identities,
and the measured transfers. The production of the concrete fixed-layout
row arrays from the dense polynomial coefficients, their counts and bit
complexity, and the undecidability transfer from the external arithmetic
statement are written proofs.

## 2. The algebraic complexity boundary

**Theorem.** An input lists finitely many rational variables and equations
$$
             \prod_i x_i^{a_i}=c\prod_i x_i^{b_i},
             \qquad a_i,b_i\in\mathbb N,\quad c\in\mathbb Q,
$$
and guards $\sum_{i\in H}|x_i|\le B$ for explicitly listed subsets $H$
and rational bounds $B$. A zero exponent gives the constant factor one,
including at a zero coordinate. Exponents, rational data and indices are
explicit binary integers, or signed numerators and positive denominators
as appropriate. Sparse exponent lists are allowed with omitted exponents
zero, and the coordinate list and both endpoint vectors are explicit. The
rational lawful locus is promised bounded and both input rational points
are promised lawful. An instance asks whether, for every positive rational
$\varepsilon$, there is a finite chain of lawful rational points between
the endpoints with every coordinate changing by strictly less than
$\varepsilon$ per step. This problem is P-complete under deterministic
log-space many-one reductions whose outputs meet the promises. The version
allowing additional scalar affine trinomials $x_j+y_j=k$ is PSPACE-hard
under polynomial-time many-one reductions, with the same promises, even
with $k=1$ throughout. The number of affine trinomials may grow.

**Upper bound.** Take the algebraic part of [ComplexityBoundary.md, §1](ComplexityBoundary.md#1-proof-of-the-polynomial-time-arm).
The signed-core theorem in [Proof.md](Proof.md) applies with precisely the
promised rational boundedness. For each endpoint form its initial support
and solve the displayed rational LP on the active exponent-difference rows.
Delete every coordinate that can be positive in a nonnegative kernel
vector and recompute the rows. The maximum of the auxiliary objective
finds their union simultaneously, and the support strictly decreases in
every nonterminal round. On $n>0$ coordinates there are at most $n$
nonempty-support rounds per endpoint, with at most $2n$ variables and
one equation per active row plus $4n$ inequalities per round. The
integer data have bit size polynomial in the explicit input. The existing
determinant bound $(2n)!D_0^{2n}$, with $D_0$ the largest exponent
difference in absolute value or one, controls an optimal basic solution.
Exact rational linear programming and comparison of signs on the final
supports are polynomial time. Empty support needs no LP. Both outcomes
have the existing primal contraction and dual terminal certificates.
This algorithm uses the boundedness promise without needing the bound as
an input.

**P-hardness.** From a topologically listed monotone circuit with constants,
output only the response coordinates, the response binomials, the budget
guards and the two endpoint spectra of the
[monotone circuit construction](SingleWordHardness.md). In particular
output the gate rows, $s^2o=z^2o$ for sentinel $s$, output gate $o$
and anchor $z$, and $z=1/4$. Identity reversal adds only tautologies.
There are $n+2$ spectral coordinates for $n$ gates, $2n+1$ licence
rows, and one calibration. Each guard is $|x_i|\le1/2$. The two endpoints
have all magnitudes $1/4$, with just the sentinel's sign flipped at the
second endpoint. The parameters guarantee lawful endpoints independently
of the circuit value and a bounded locus. The two signed cores coincide
exactly when the sentinel is deleted, which the circuit proof shows
equivalent to the output being true. The algebraic reachability theorem
gives the reduction in both directions. A read-only input scan and
logarithmic-size counters suffice to generate each coordinate, two gate
slots, the output row, and the constant guards and endpoint entries.
Each word has length three, so multiplicities are computed by inspecting
at most three mark identifiers. Dense exponent encodings can also be
emitted by an additional coordinate counter, with at most $O(n^2)$ binary
exponent slots. Hence projection to the algebraic instance preserves the
deterministic log-space bound of the original reduction.

**PSPACE-hardness.** Configuration-to-configuration AND/OR Nondeterministic
Constraint Logic is PSPACE-hard by
[Hearn–Demaine, Corollary 6](https://arxiv.org/abs/cs/0205005).
Use the same weight and capacity convention as
[SingleAdditiveLicence.md](SingleAdditiveLicence.md): each edge $i$ has
positive weight $w_i$, each orientation side $b\in\{0,1\}$ selects
its charged vertex $v(i,b)$, and legality is that every vertex has
total charge at most its capacity $B_v$. The change of convention from
minimum inflow to maximum outgoing charge subtracts from the sum of the
incident weights. Supply two legal orientations.

Here is a direct projection to the algebraic problem, using the same charge
construction without the measured catalogue. Introduce toggles $x_{i0},x_{i1}$
and charges $c_{vi}$. Impose
$$
  x_{i0}+x_{i1}=1,\qquad
  x_{ib}c_{v(i,b),i}=w_i x_{ib},\qquad
  |x_{ib}|\le1,\qquad
  \sum_i |c_{vi}|\le B_v .
$$
The first rows are the only trinomials. A nonzero toggle therefore forces a
full charge at the corresponding vertex. An orientation endpoint uses
the unit toggle for its chosen side, the zero toggle for the other, and
charges exactly the chosen vertices. Its legality is the original
capacity condition. The given guards bound every coordinate.

At each lawful point choose any nonzero side at each edge. Every such
orientation is legal, since its full charges are included in the absolute
sum. All orientations represented at the point join by changing their
choices one edge at a time. At two points a step of mesh one with strict
inequality has a common represented orientation. Indeed disjoint nonzero
choices at an edge would force its first toggle to change between zero and
one. Following a chain therefore gives legal NCL flips. The two orientation
endpoints represent only their respective supplied orientations. Conversely,
a legal NCL flip has a three-segment rational realization. Preload the
post-flip charge before switching the toggles, switch the toggles while
holding the union of the two charge assignments, then unload the old
charge. The union takes the larger of the two corner charges at every
coordinate. At each vertex this union agrees with one of the two legal
assignments: a single edge either joins its load, leaves it, or has no
effect there. On the two charge segments the toggle is fixed and its
required charges stay at full weight. On the middle segment all charges
needed by either nonzero toggle are present. Convexity of the absolute-sum
guards gives legality on each charge segment, and all toggles throughout
lie in $[0,1]$. Rational subdivision and concatenation work for every
positive tolerance. The array has $2|E|+|V||E|$ coordinates,
$2|E|$ binomials, $|E|$ trinomials and $2|E|+|V|$ guards.
It and the lawful endpoints are emitted in polynomial time using only
the given weights, capacities and constants zero and one. This gives the
claimed PSPACE lower bound, and the same reduction works at mesh one.

**Lean correspondence.** [AlgebraicBoundary.lean](MovingProjection/AlgebraicBoundary.lean)
checks the circuit projection, including its lawful endpoints, the bounded
promise and equivalence to output truth
(`MonotoneCircuitMarkov.Circuit.algebraic_fine_iff_value`). It defines the
charge binomials, guards and one scalar trinomial per edge and proves their
exact semantics, legality and boundedness, and both chain transfers
(`AlgebraicConstraintLogic.lawful_iff`, `endpoint_lawful`, `bounded`,
`chain_of_flips`, `flips_of_chain`, `fine_iff_flips`). The Lean positive
transfer clips the toggles of the existing three-segment charge proof to
$[0,1]$, a nonexpansive map preserving the competing sum and all charges.
This clip fixes the three-segment witnesses above. In the polynomial-time
arm, Lean proves the signed-core criterion and certificate soundness
(`CoreCertificate.checkPair_sound`). It also proves certificate existence
(`CoreCertificate.checkPair_complete`) and
the bound `witness.steps.length + (core rows s).card ≤ s.card` on
contraction stages in a checked certificate
([`CoreCertificate.checkCore_complete_short`](MovingProjection/CertificateComplete.lean#L154)).
The LP search and its round and dimension bounds, witness bit lengths,
certificate encoding size and running-time bounds are written proofs.
The machine reductions use the classical P- and PSPACE-hard source
theorems in the written argument.

## 3. Real components without a boundedness assumption

**Theorem.** Use the finite signed-binomial equations and absolute-sum
guards of §2, with the same rational coefficients now interpreted in
$\mathbb R$. No boundedness is required for the real lawful locus
$S_{\mathbb R}$. For any lawful real $x,y$, the following conditions are
equivalent.

1. They belong to the same connected component of $S_{\mathbb R}$.
2. A continuous path in $S_{\mathbb R}$ joins them.
3. Their signed cores, computed on their respective supports with the same
   exponent rows, agree.

If the rational lawful locus is bounded, fine connectivity of lawful
rational endpoints is also equivalent to (1) and (2) for those endpoints
viewed as real points. That additional boundedness assumption concerns
only the rational locus.

**Necessity.** Split $S_{\mathbb R}$ into finitely many sign charts.
Equations and guards are continuous, so the locus is closed. In any one
chart with support $S$, a finite limit is still lawful and its surviving
coordinates keep their signs. The chart-limit proof of [Proof.md](Proof.md)
uses only coordinate convergence along the chart, a fixed linear right
inverse on the vanishing-coordinate image, and rational approximation in
the kernel. In detail the active log equations show that the row matrix
on the vanishing coordinates times their log-magnitude vector stays bounded,
since the surviving logs converge. Subtract the bounded correction given
by that right inverse. The corrected kernel vector still tends to minus
infinity in every vanishing coordinate. Negating, approximating within the
rational kernel and clearing denominators supplies integer weights positive
on every vanishing coordinate and zero on the survivors. This is a
contraction of $S$ to the limit support. It gives the same support core,
and the retained signs give the same signed core. There is no use of a
bound on the whole chart.

Each signed-core class is the union of the closures of all charts of that
class. One inclusion follows from the limit argument, and the other from
each point belonging to its own chart. These are finite unions of closed
sets, and the complementary classes form another such union. A connected
subset therefore lies in a single class.

**Sufficiency.** An allowed support contraction is a real path
$t\mapsto(x_i t^{w_i})_i$, $0\le t\le1$, run from (1) to (0).
On an active row the exponents of the scaling parameter balance. If its
left monomial was zero, the two sides were zero and coordinatewise scaling
keeps both zero, including when the coefficient on the right is zero.
The guards decrease term by term. Iterating gives a path to a representative
of the signed core. For the two representatives with common signs, join
the nonzero magnitudes by
$$
               \exp((1-t)\log |x_i|+t\log |y_i|).
$$
Use the shared signs and keep zero coordinates zero. In the common sign
chart the active equations are affine in the logs, with matching signs
already forced at the endpoints. Inactive rows hold since the vanished
factors stay zero (a zero coefficient again leaves its right-hand side
zero). Convexity of the exponential bounds each magnitude by
$(1-t)|x_i|+t|y_i|$, so every absolute-sum guard holds even at a tight bound.
Reverse the second endpoint's contraction paths to finish.

**Rational endpoints.** The bounded-rational-locus signed-core theorem
identifies the rational fine-chain verdict by the same supports, signs
and rows. Hence the two decisions agree for rational endpoints without
needing density of lawful rational points in the full real locus. The
sets and attained component labels can differ. For instance, $x^2=2$
with $|x|\le2$ gives two real components and no rational points.
For $y^2=2x^2$ with $|x|+|y|\le1$, the closure of the rational locus
is the origin while the real locus contains both real line segments through
it.

**Lean correspondence.** [RealComponents.lean](MovingProjection/RealComponents.lean)
checks the closed-class argument and the real paths, and proves
`real_joinedIn_iff_signedCore`, `real_connectedComponent_iff_signedCore`
and `fineConnected_iff_real_joinedIn`. The limit argument reuses
`signedCore_of_chart_limit` in [Components.lean](MovingProjection/Components.lean),
which also serves the original bounded-chart lemma. The agreement theorem
calls the existing rational classification with its boundedness premise.
The paper's related-work section compares the corollary with classifications
of components in real toric geometry.

## 4. Complexity of real path-component membership

**Theorem.** Encode the finite signed-binomial equations and
absolute-sum guards of §2 explicitly in binary, and supply two feasible
rational endpoints. Ask whether their real embeddings are in the same
path component of the real lawful locus. With no boundedness promise,
this problem is P-complete under deterministic log-space many-one
reductions that output feasible endpoints. If the language also allows
a growing number of scalar equations $x_j+y_j=1$, the real problem is
PSPACE-hard under polynomial-time many-one reductions, already for
bounded real loci and supplied feasible rational endpoints.

**Upper bound and P-hardness.** By §3 the real verdict is equality of
signed cores. The LP in §2 computes these from the initial support and
signs at each rational endpoint and the exponent rows. None of its
operations requires a bound on the lawful locus. The input sizes,
round count, exact LP resource bounds, and certificate bit bounds are
the same as in §2. The C23 circuit-value reduction of §2 outputs the
same binomials, guards, and endpoints in deterministic log space.
Its two signed cores coincide exactly when the circuit output is true,
so its real verdict has the same equivalence. In particular the
supplied endpoints are feasible over the reals, by interpreting their
rational values as real values.

**PSPACE lower bound with trinomials.** Use the same explicit NCL rows
and rational corner endpoints as in §2. The guards $|x_{ib}|\le1$ and
$\sum_i|c_{vi}|\le B_v$ already bound the whole real locus. For each
legal flip the preload, toggle, and unload segments of §2 are also
lawful for real parameters. One way to see this is that the equations
and budget inequalities define a closed real locus. The same affine
segments are lawful at all rational parameters, where their toggles
are in $[0,1]$. By density and continuity they are lawful on the entire
real parameter interval. Concatenating the three pieces per flip
gives a continuous path that admits a piecewise-linear parametrization.

Conversely, take any lawful continuous path between the supplied
endpoints. By uniform continuity on the compact parameter interval,
partition it into finitely many equal subintervals with successive
sample points at supremum distance strictly below one. The
common-orientation argument of §2 works over $\mathbb R$. Each nonzero
toggle still forces its entire charge, so every orientation represented
at a sampled point is legal, and any two represented there are joined
by flips. For an edge to have disjoint nonzero sides at two adjacent
samples, its first toggle would have to change between zero and one
by $x_{i0}+x_{i1}=1$. The strict mesh bound excludes this. Choose a
shared orientation at each adjacent pair, then join these choices
within each sampled state. The corner endpoints each represent just
their supplied orientation. Thus the path gives a legal flip chain.
The reduction emits exactly the arrays and endpoints counted in §2,
so the polynomial-time bound and the cited configuration-to-configuration
NCL hardness apply.

**Lean correspondence.**
[`algebraic_real_path_iff_value`](MovingProjection/RealAlgebraicBoundary.lean)
checks the circuit equivalence using the signed-core results of §3.
The same file defines the real interpretation of the exact tests,
guards and trinomials of §2. Its `real_path_iff_flips` checks the two
directions for these rational corner endpoints. It uses
`Graph.flip_segments_lawful` and the closed locus for the forward
construction, and `flips_of_real_path` checks uniform mesh sampling
and the common-orientation argument over the reals.
`network_real_path_iff_flips` checks the transfer from minimum-inflow-two
networks to their scaled charge arrays. Lean checks the
binomial decision criterion without boundedness. The LP resources,
encodings, reductions as polynomial-time or log-space machines, and
source hardness theorems are on paper.

## Scope of the consequences

The fixed-count corollary is conditional on the specified version of the
quartic theorem. It gives some constant probe count and leaves the
zero-probe one-widened-licence problem and the minimum sufficient positive
probe count open here. The real and rational algebraic PSPACE lower
bounds both use a growing number of scalar trinomials. The complexity
with just one scalar trinomial and a matching complexity upper bound
for the widened language are outside these reductions. General
semialgebraic roadmap algorithms give a decision procedure for its real
problem.

The signed-core classification concerns the binomial language.
Agreement with rational fine reachability is proved under the bounded
rational-locus promise, while the real path-component algorithm needs
no such promise.
