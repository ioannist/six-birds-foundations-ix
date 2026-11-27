# Proof of the exactly-one-licence arm

This is the full reduction for the second arm of the
[complexity boundary theorem](ComplexityBoundary.md#2-hardness-in-the-measured-instrument).
It uses the same measured instrument and edit relation as the polynomial-time
arm.

## 1. Source problem and construction

In configuration-to-configuration Nondeterministic Constraint Logic (NCL), the
input consists of an AND/OR constraint graph and two legal orientations.
A move reverses one edge while preserving legality at every vertex. Hearn and
Demaine prove PSPACE-completeness for this precise variant, with distinct
orientations in their hardness construction. Let $E,V$ be the edge and vertex
sets, $w_i\in\{1,2\}$ the edge weights, $u_i,v_i$ the labelled ends of edge $i$,
and $W_v$ the sum of weights of incident ends at vertex $v$. Then $W_v$ is four
or six. The minimum inflow of two is equivalent to an outflow capacity
$W_v-2$, since each end is either a head or a tail, including for a loop.
[Hearn and Demaine, §2 and Corollary 6](https://arxiv.org/abs/cs/0205005)

Let $I=E\sqcup\{*\}$ be the probe set and take $X=(\mathbb Z/2)^d$ for
$d=\lceil\log_2(|E|+2)\rceil$. Assign distinct nonzero labels $a_j\in X$
and use probes $\chi_j(x)=(-1)^{a_j\cdot x}$. For each nonzero $a$, translating
by a unit vector in a nonzero coordinate of $a$ pairs character values of
opposite sign. Thus every probe is balanced, distinct probes are orthogonal,
and the square of each probe is one. Use a singleton register with weight
one and all table entries one. This gives normalized, reciprocally paired
register rows and full proposal support. Use grade zero and identity reversal.

The marks are $L,A,B$, an edge selector $S_i$ for each $i\in E$, and a vertex
mark $T_v$ for each $v\in V$, all distinct. Put
\[
 m=3+|E|+|V|,\qquad r=\frac{1}{m+1},\qquad
 k=\frac{1}{4|I|},\qquad c=\frac18,\qquad \kappa=\frac12.
\]
The rate floor is $r$. Hold the following ordinary calibrations:
\[
 \alpha_{Lj}=k/2,\qquad
 \alpha_{S_i j}=\begin{cases}c w_i & j=i,\\ 0 & j\ne i,\end{cases}
 \qquad
 \alpha_{T_v,*}=\kappa-c(W_v-2).
\]
The reserve values are in $[0,\kappa]$. Hold these named licences:
\[
 LL\ \sim\ \{AL,BL\},\qquad
 S_i A T_{u_i}\ \sim\ S_i A S_i,\qquad
 S_i B T_{v_i}\ \sim\ S_i B S_i\quad(i\in E).
\]
The horizon is three. The policy permits only the full licence set. Both
endpoints hold every publication and have the same profile, including full
proposal support and the sole register partition. Every intermediate profile
in a chain between them equals this one by monotonicity and antisymmetry of the
profile order. Edits on such a chain are physical-distance rewrites.

Dropping the common final $L$ in the widened comparison preserves the
lawful fibre at this profile, by cancellation of the positive mass
and character factors. The [duration-one proof](BoundedProbes.md#1-duration-one-in-the-hardness-construction)
records the identity. Both lengths are checked by the same Lean
construction.

## 2. The exact lawful equations

The conditional base kernel for mark $m$ is
\[
 Q_m(x,y)=\frac{1+\sum_{j\in I}\alpha_{mj}\chi_j(x)\chi_j(y)}{|X|}.
\]
Products of these matrices multiply the response coefficients, since the
uniform projector and the individual character projectors are pairwise
orthogonal. The joint endpoint table of a word is its conditional kernel
times the product of its mark rates. Applying such tables to the constant
function and to each probe recovers separately the uniform coefficient and
the probe coefficients of a linear combination. Conversely equality of
all these coefficients implies equality of the tables.

Write $\theta_m$ for the rates. The uniform coefficients for the widened
licence give $\theta_L^2=(\theta_A+\theta_B)\theta_L$. Since $\theta_L>0$,
we get $\theta_L=\theta_A+\theta_B$. The floor yields a lower bound of
$2r$ for $\theta_L$ and of $r$ for each of the other $m-1$ rates.
These lower bounds sum to one. Normalization forces equality at every
mark. At probe $j$, cancel $2r^2\alpha_{Lj}>0$ from the equality of
coefficients of the widened licence. Writing $x_j=\alpha_{Aj}$ and
$y_j=\alpha_{Bj}$ yields
\[
 x_j+y_j=k\qquad(j\in I).
\]
For each singleton licence the forced rate products agree, and the selector
kills every probe product except possibly at its edge. With
$z_{vi}=\alpha_{T_v,i}$, cancellation of $cw_i>0$ and the vertex budget give
\[
 x_i(z_{u_i i}-cw_i)=0,\qquad
 y_i(z_{v_i i}-cw_i)=0,\qquad
 \sum_{i\in E}|z_{vi}|\le c(W_v-2).
\]
Conversely these equations, the forced rates, the calibrations, the mark
budgets and the fixed register data imply lawfulness by the same coefficient
computation. The kernel is positive because every response budget is
at most $1/2$. No sign restriction on the toggle responses is used.

## 3. Reachability in both directions

A lawful state allows the choice of tail $u_i$ when $x_i\ne 0$ and tail
$v_i$ when $y_i\ne 0$. The choices are of labelled ends, even for a loop.
Each edge allows at least one, since $x_i+y_i=k>0$. Every independent
selection is NCL-legal. An edge chosen outward at $v$ uses a distinct
coordinate with $|z_{vi}|=cw_i$, so summing over chosen outgoing edges
and dividing by $c>0$ gives the capacity constraint. Any two orientations
represented by one state can be joined by legal flips by changing the
differing choices one at a time within that state's allowed choices.

Lift a legal orientation with the forced rates and calibrated data. At
edge $i$ set $(x_i,y_i)=(k,0)$ or $(0,k)$ as selected, and set $z_{vi}=cw_i$
at the selected tail and zero elsewhere. At the reserve set
$(x_*,y_*)=(k,0)$. The vertex budgets hold by legality. The toggle budgets
each cost at most $|I|k=1/4$, the $L$ budget costs $|I|k/2=1/8$, and every
selector costs at most $1/4$. The lift is lawful and represents only the
given orientation. In particular distinct orientations give distinct lifts.

For an allowed flip, interpolate by three affine segments. First raise
the new tail charge to $cw_i$ while its toggle is zero. Next interpolate
the two toggles with both charges in place. Finally remove the old tail
charge after its toggle reaches zero. A loop has the same charge before
and after, so it stays constant. For each vertex the load with both
charges in place equals the larger of the before and after loads, since
only the flipped edge can change and its double charge at that vertex is
the maximum of the old and new charge. Thus both preloaded states obey
the budgets. Interpolating charges preserves the budgets by convexity and
preserves each active charge because the toggles are fixed on those segments.
Interpolating toggles keeps the required charges fixed and the toggles
in $[0,k]$ with sum $k$. With fixed rates and register, each prepared
marked table entry is affine on each segment. Equal rational subdivisions
with sufficiently large denominator give a lawful chain at every
positive mesh. Concatenate these chains along any legal NCL flip sequence.

For the converse it suffices to use
\[
 \varepsilon_0=\frac{rk}{2|X|+1}.
\]
Multiply a row difference of physical entries for one mark by the probe
at the ending point, sum over the base, and multiply by the probe at the
starting point. Orthogonality gives $\theta_m$ times the response
difference. The rate is fixed and at least $r$. Hence a step of size
strictly less than $\varepsilon_0$ changes each response by strictly less
than $|X|\varepsilon_0/r<k$. If adjacent states had disjoint choices
for one edge, they would each allow only one, and opposite, choices.
The first toggle would have to change between $k$ and zero, a
contradiction. Choose a common represented orientation for each link
of the chain, independently at each edge. Join the orientations at
consecutive links by the within-state flip argument, using the unique
orientations represented by the endpoints to start and finish. An empty
chain has equal endpoints. This proves equivalence of NCL reachability
with chain existence at $\varepsilon_0$, and with fine reachability.

## 4. Output length

There are $O(|E|+|V|+1)$ marks, $1+2|E|$ licences, and
$|I|+|E||I|+|V|$ publications. Each word has constant length. The probe
table has $|I||X|=O((|E|+1)^2)$ signs because
$|E|+2\le |X|<2(|E|+2)$. The full support mask and register arrays have
$m|X|^2$ entries, and the licence policy is a list with one allowed set.
Even if both endpoint marked tables are explicitly listed, the bounds
are polynomial. All response denominators divide $8|I|$ at the lifts,
so each prepared entry has a denominator dividing
$8|I||X|(m+1)$. The rates, floor, calibrations, supplied tolerance,
and endpoint parameters have $O(\log(2+|E|+|V|))$ bits each. The reciprocal
of the tolerance is exactly $(m+1)4|I|(2|X|+1)$. Including labels, the
output length is $O((|E|+|V|+1)(|E|+1)^2\log(2+|E|+|V|))$ bits.
Enumerate the binary points and the first $|I|$ nonzero labels, then
evaluate their dot products in $O(d|I||X|)$ bit operations. To list all
prepared entries, add at most $|I|$ signed numerators per entry over the
common response denominator $8|I|$, incorporate the uniform term, and
multiply by the rate. This uses $O(m|X|^2|I|)$ arithmetic operations on
$O(\log(2+|E|+|V|))$-bit integers. The remaining arrays and word lists
can be generated by scanning their index sets with the displayed
formulas. Thus the output is computable in polynomial bit time.

## 5. Scope and attribution

Hearn and Demaine supply the source hardness theorem. The projection
onto the uniform coefficient and one coefficient per probe is the
instrument's character calculus. The reduction uses a single
measured comparison to impose the family of toggle sums and the
response budgets to enforce the graph's vertex constraints. The
[prior-work comparison and open problems](ComplexityBoundary.md#5-prior-work-and-scope-of-the-contribution)
give the precise scope of the complexity claim.
The converse at $\varepsilon_0$ also applies at smaller positive
tolerances. The fine-reachability implication in the other direction
uses the three-segment realization at every positive tolerance.

## 6. Lean correspondence

- [ConstraintLogic.lean](MovingProjection/ConstraintLogic.lean) proves the
  equivalences for orientation legality and flip-chain existence in
  `Network.legal_iff_scaled` and `Network.flips_iff_scaled`. The
  `Graph` declarations prove that every represented orientation is legal,
  all choices at one state are flip-connected, steps of mesh $k$ share a
  represented orientation, and each flip has the three-segment rational
  realization.
- [BinaryParity.lean](MovingProjection/BinaryParity.lean) constructs the
  binary characters, proves balance and orthogonality by pairing, and proves
  the two bounds on the base size.
- [SingleAdditiveLicence.lean](MovingProjection/SingleAdditiveLicence.lean)
  constructs the actual `EventExperiments` catalogue. It proves the
  coefficient calculation in `joint_words_iff`, then derives rate forcing
  and the selector and reserve constraints. `encode` produces a lawful
  state. On the whole auxiliary rational space it clamps the toggles to $[0,k]$. Clamping preserves the
  toggle sum, cannot turn a zero into a nonzero, and is nonexpansive. Along
  the three segments of the written proof it is the identity. The converse
  works on the actual signed responses, using the existing native spectral
  modulus at $\varepsilon_0$ and propagating the fixed endpoint profile
  through the chain.
- `ncl_exactly_one`, `ncl_licence_duration`, `ncl_endpoints_distinct`,
  `ncl_base_size`, `ncl_chain_iff` and `ncl_fine_iff` give the licence
  count and durations, distinct endpoints, linear bound on the base,
  and both reachability equivalences for the binary-base construction.
  The external NCL hardness theorem and the binary encoding and running-time
  argument in §4 are on paper. The Lean basis uses a finite embedding given by the size bound, while the
  explicit binary enumeration in §1 provides the polynomial-time choice
  of that embedding.

## 7. The one-licence verdict control

**Proposition.** Take the duration-two instrument of §1 and any two of
its supplied lawful rational orientation endpoints at the full held
profile. At the same licence name replace $LL\sim\{AL,BL\}$ by
$LL\sim LL$, leaving all other instrument data and both endpoint laws and
profiles fixed. Both endpoints are lawful in the replacement instrument,
and they are finely reachable there. Thus, whenever the source orientations
are disconnected by legal flips, the widened instrument answers no and
the replacement answers yes.

At the replacement name the test is an identity. Its rate and spectral
constraints hold for every law, and the held licence set, publications,
and all other word comparisons are the same. The two original laws
therefore remain feasible. The replacement can release the rate equation
that forced the rates. In the witness below use the original common
rate vector throughout, along with the original singleton register and
profile. In particular the singleton word mass products still agree.

Let $x,y$ be the supplied spectra. For a rational $t\in[0,1]$, multiply
both summand spectra, for marks $A$ and $B$, by $t$ at every probe,
including the reserve. Hold every other response fixed. Both sides of a
selector comparison contain the same summand once, so its response
equation at every probe is scaled by the same factor. The summand budgets
only decrease and the calibrations concern $L$, selectors, and vertex
reserves. Run this segment from the source to the spectrum with summands
zero. With both summands zero all selector response equations are
$0=0$. Interpolate the vertex-label spectra affinely to the corresponding
damped target. All other coordinates agree, and in particular each
vertex reserve stays fixed. The absolute-sum budgets hold by convexity.
Reverse the target damping to finish. All three segments have constant
rates and register and are affine in the response coordinates. The
prepared tables are affine along them, so sufficiently fine rational
subdivision yields lawful chains at every positive tolerance.

For a concrete disconnected source, take $K_{3,3}$ with a weight-two
perfect matching and weight one on the other six edges. Every vertex is
an AND vertex with required inflow two. Orient the matching towards the
first part and every other edge towards the second part. Each vertex
gets inflow exactly two, and the opposite orientation also gives inflow
two at every vertex. A single edge reversal strictly decreases inflow
at its old head, so neither orientation admits a flip. This is an
instance where the endpoints and the other tests are fixed and the single
replacement changes the verdict.

The all-yes conclusion concerns the reflexive replacement in this
reduction with every other input fixed. The necessity of the rate floor,
calibrations, budgets, selectors, reserve, and other ingredients is a
separate question. The signed-core criterion gives the verdict for
general single-word catalogues in this instrument class.

**Lean correspondence.**
[`controlInstrument` and `control_replacement`](MovingProjection/SingleAdditiveLicence.lean)
retain the original binary parity base and singleton register,
replacing the widened comparison by `LL ∼ LL` at the same name, with
every other comparison fixed. `Control.endpoint` is
the original reduction endpoint's base-protocol state, so its law is
unchanged and `Control.endpoint_profile` checks its profile.
`Control.fine` constructs chains at every positive rational
tolerance, lifting its spectral meshes while keeping the original
rates and register fixed. `Control.verdict_changes` checks the two verdicts
when the original orientations have no flip chain. The small
$K_{3,3}$ illustration above is a written example of that premise.
